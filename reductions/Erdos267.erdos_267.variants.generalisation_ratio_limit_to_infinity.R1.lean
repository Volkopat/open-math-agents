import FormalConjectures.ErdosProblems.«267»
import Mathlib

-- Reduction Erdos267.erdos_267.variants.generalisation_ratio_limit_to_infinity.R1 of Erdős Problem 267: generalisation ratio limit to infinity
-- Credit: @rickmanelius
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
Write `S = ∑ 1/F_(n_k)` and `s_K = n_0 + ... + n_K`. Three regimes cover every strictly
increasing `n`.

* Eventually lacunary sequences, `n_(k+1) ≥ c n_k` for some `c > 1` and all large `k`: this is
  `H1`, Badea's theorem (C. Badea, The irrationality of certain infinite series, Glasgow Math. J.
  29 (1987)), which settles the main statement `erdos_267` of the same file.
* Super-lacunary jumps, `n_(K+1) - 2 s_K` unbounded: proved here. If `S = p/q` and `L_K` is the
  product of the nonzero `F_(n_k)` with `k ≤ K`, then `q L_K (S - S_K)` is a positive integer,
  while `L_K ≤ 2^(s_K)` and `S - S_K ≤ 3 / F_(n_(K+1)) ≤ 3 (2/3)^(n_(K+1) - 2)`.
* What remains is `H2`: `n_(k+1) / n_k` comes arbitrarily close to `1` infinitely often, there are
  no super-lacunary jumps, and `n_k / k → ∞` (the hypothesis of the problem).
-/

open Filter Finset

namespace OMA.R_Erdos267_erdos_267_variants_generalisation_ratio_limit_to_infinity_R1

/-- Badea's theorem, in eventual form: if `n_(k+1) ≥ c n_k` for some `c > 1` and all large `k`,
then `∑ 1/F_(n_k)` is irrational. -/
def H1 : Prop :=
  ∀ n : ℕ → ℕ, StrictMono n → (∃ c : ℝ, 1 < c ∧ ∀ᶠ k in atTop, c * n k ≤ n (k + 1)) →
    Irrational (∑' k, 1 / (Nat.fib (n k) : ℝ))

/-- The open core: slowly growing sequences, whose ratio `n_(k+1) / n_k` comes arbitrarily close
to `1` infinitely often and which have no super-lacunary jumps. -/
def H2 : Prop :=
  ∀ n : ℕ → ℕ, StrictMono n →
    Tendsto (fun k => (n (k + 1) / k.succ : ℝ)) atTop atTop →
    (∀ c : ℝ, 1 < c → ∃ᶠ k in atTop, (n (k + 1) : ℝ) < c * n k) →
    (∃ C : ℕ, ∀ k, n (k + 1) ≤ 2 * ∑ j ∈ range (k + 1), n j + C) →
    Irrational (∑' k, 1 / (Nat.fib (n k) : ℝ))

theorem fib_le_two_pow (m : ℕ) : Nat.fib m ≤ 2 ^ m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases m with _ | _ | m
    · simp
    · simp
    · have h1 := ih (m + 1) (by omega)
      have h2 := ih m (by omega)
      calc Nat.fib (m + 2) = Nat.fib m + Nat.fib (m + 1) := Nat.fib_add_two
        _ ≤ 2 ^ m + 2 ^ (m + 1) := add_le_add h2 h1
        _ ≤ 2 ^ (m + 2) := by rw [pow_succ, pow_succ, pow_succ]; omega

theorem fib_succ_ge {m : ℕ} (hm : 2 ≤ m) : (3 : ℝ) / 2 * Nat.fib m ≤ Nat.fib (m + 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  have h1 : Nat.fib (j + 2) = Nat.fib j + Nat.fib (j + 1) := Nat.fib_add_two
  have h2 : Nat.fib (j + 3) = Nat.fib (j + 1) + Nat.fib (j + 2) := Nat.fib_add_two
  have h3 : Nat.fib j ≤ Nat.fib (j + 1) := Nat.fib_mono (by omega)
  have h4 : 3 * Nat.fib (j + 2) ≤ 2 * Nat.fib (j + 3) := by omega
  have h5 : (3 : ℝ) * Nat.fib (j + 2) ≤ 2 * Nat.fib (j + 3) := by exact_mod_cast h4
  show (3 : ℝ) / 2 * Nat.fib (j + 2) ≤ Nat.fib (j + 3)
  linarith

theorem fib_add_ge {M : ℕ} (hM : 2 ≤ M) (i : ℕ) :
    ((3 : ℝ) / 2) ^ i * Nat.fib M ≤ Nat.fib (M + i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have h := fib_succ_ge (show 2 ≤ M + i by omega)
    calc ((3 : ℝ) / 2) ^ (i + 1) * Nat.fib M = 3 / 2 * (((3 : ℝ) / 2) ^ i * Nat.fib M) := by
          ring
      _ ≤ 3 / 2 * Nat.fib (M + i) := by gcongr
      _ ≤ Nat.fib (M + i + 1) := h
      _ = Nat.fib (M + (i + 1)) := by rw [add_assoc]

theorem fib_ge_pow {m : ℕ} (hm : 2 ≤ m) : ((3 : ℝ) / 2) ^ (m - 2) ≤ Nat.fib m := by
  have h := fib_add_ge (le_refl 2) (m - 2)
  rw [Nat.fib_two, Nat.cast_one, mul_one, show 2 + (m - 2) = m by omega] at h
  exact h

theorem inv_fib_le (n : ℕ → ℕ) (hn : StrictMono n) (k : ℕ) :
    1 / (Nat.fib (n k) : ℝ) ≤ 9 / 4 * ((2 : ℝ) / 3) ^ k := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · have h1 : 1 / (Nat.fib (n k) : ℝ) ≤ 1 := by
      rcases Nat.eq_zero_or_pos (Nat.fib (n k)) with h | h
      · simp [h]
      · rw [div_le_one (by exact_mod_cast h)]
        exact_mod_cast h
    calc 1 / (Nat.fib (n k) : ℝ) ≤ 1 := h1
      _ ≤ 9 / 4 * ((2 : ℝ) / 3) ^ k := by interval_cases k <;> norm_num
  · have hk' : k ≤ n k := hn.id_le k
    have hnk : 2 ≤ n k := le_trans hk hk'
    have hF := fib_ge_pow hnk
    have h1 : ((3 : ℝ) / 2) ^ (k - 2) ≤ ((3 : ℝ) / 2) ^ (n k - 2) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    calc 1 / (Nat.fib (n k) : ℝ) ≤ 1 / ((3 : ℝ) / 2) ^ (k - 2) :=
          one_div_le_one_div_of_le (by positivity) (le_trans h1 hF)
      _ = 9 / 4 * ((2 : ℝ) / 3) ^ k := by
          obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
          rw [Nat.add_sub_cancel, pow_add, div_pow, div_pow, div_pow]
          field_simp
          ring

theorem summable_inv_fib (n : ℕ → ℕ) (hn : StrictMono n) :
    Summable (fun k => 1 / (Nat.fib (n k) : ℝ)) :=
  Summable.of_nonneg_of_le (fun _ => by positivity) (inv_fib_le n hn)
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _)

theorem tail_le (n : ℕ → ℕ) (hn : StrictMono n) (K : ℕ) (hK : 2 ≤ n (K + 1)) :
    ∑' i, 1 / (Nat.fib (n (i + (K + 1))) : ℝ) ≤ 3 / Nat.fib (n (K + 1)) := by
  have hFM : (0 : ℝ) < Nat.fib (n (K + 1)) := by
    have h := fib_ge_pow hK
    have : (0 : ℝ) < ((3 : ℝ) / 2) ^ (n (K + 1) - 2) := by positivity
    linarith
  have hs : Summable (fun i => 1 / (Nat.fib (n (i + (K + 1))) : ℝ)) :=
    (summable_nat_add_iff (K + 1)).mpr (summable_inv_fib n hn)
  have hg : Summable (fun i : ℕ => ((2 : ℝ) / 3) ^ i / Nat.fib (n (K + 1))) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).div_const _
  have hstep : ∀ i, n (K + 1) + i ≤ n (i + (K + 1)) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have := hn (show i + (K + 1) < i + 1 + (K + 1) by omega)
      omega
  calc ∑' i, 1 / (Nat.fib (n (i + (K + 1))) : ℝ)
      ≤ ∑' i : ℕ, ((2 : ℝ) / 3) ^ i / Nat.fib (n (K + 1)) := by
        refine hs.tsum_le_tsum (fun i => ?_) hg
        have h1 := fib_add_ge hK i
        have h2 : (Nat.fib (n (K + 1) + i) : ℝ) ≤ Nat.fib (n (i + (K + 1))) := by
          exact_mod_cast Nat.fib_mono (hstep i)
        have h4 : (0 : ℝ) < ((3 : ℝ) / 2) ^ i * Nat.fib (n (K + 1)) := by positivity
        calc 1 / (Nat.fib (n (i + (K + 1))) : ℝ)
            ≤ 1 / (((3 : ℝ) / 2) ^ i * Nat.fib (n (K + 1))) :=
              one_div_le_one_div_of_le h4 (h1.trans h2)
          _ = ((2 : ℝ) / 3) ^ i / Nat.fib (n (K + 1)) := by
              rw [div_pow, div_pow]
              field_simp
    _ = 3 / Nat.fib (n (K + 1)) := by
        rw [tsum_div_const, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        norm_num

/-- The super-lacunary case: if `n_(K+1)` exceeds twice the sum of the earlier exponents by an
unbounded amount, the reciprocal Fibonacci sum is irrational. -/
theorem super_lacunary (n : ℕ → ℕ) (hn : StrictMono n)
    (hjump : ∀ C : ℕ, ∃ K, 2 * ∑ k ∈ range (K + 1), n k + C < n (K + 1)) :
    Irrational (∑' k, 1 / (Nat.fib (n k) : ℝ)) := by
  rintro ⟨r, hr⟩
  have hden : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (3 * (r.den : ℝ)) (by norm_num : (1 : ℝ) < 3 / 2)
  obtain ⟨K, hK⟩ := hjump (m + 2)
  set s := ∑ k ∈ range (K + 1), n k with hs
  set L : ℕ := ∏ k ∈ range (K + 1), max 1 (Nat.fib (n k)) with hL
  have hL1 : 1 ≤ L := Finset.one_le_prod' (fun k _ => le_max_left _ _)
  have hL2 : (L : ℝ) ≤ 2 ^ s := by
    have : L ≤ 2 ^ s := by
      rw [hL, hs, ← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_le_prod' (fun k _ =>
        max_le (Nat.one_le_two_pow) (fib_le_two_pow _))
    exact_mod_cast this
  -- the partial sum times L is an integer
  obtain ⟨z, hz⟩ : ∃ z : ℕ, (L : ℝ) * ∑ k ∈ range (K + 1), 1 / (Nat.fib (n k) : ℝ) = z := by
    refine ⟨∑ k ∈ range (K + 1), (if Nat.fib (n k) = 0 then 0 else L / Nat.fib (n k)), ?_⟩
    rw [Finset.mul_sum, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    by_cases h0 : Nat.fib (n k) = 0
    · simp [h0]
    · rw [if_neg h0]
      have hdvd : Nat.fib (n k) ∣ L := by
        have : max 1 (Nat.fib (n k)) = Nat.fib (n k) := max_eq_right (Nat.one_le_iff_ne_zero.mpr h0)
        rw [← this]
        exact Finset.dvd_prod_of_mem _ hk
      rw [Nat.cast_div hdvd (by exact_mod_cast h0)]
      ring
  -- split the sum
  have hsum := (summable_inv_fib n hn).sum_add_tsum_nat_add (K + 1)
  set T := ∑' i, 1 / (Nat.fib (n (i + (K + 1))) : ℝ) with hT
  have hnK : 2 ≤ n (K + 1) := by omega
  have hTpos : 0 < T := by
    have hs' := (summable_nat_add_iff (K + 1)).mpr (summable_inv_fib n hn)
    refine hs'.tsum_pos (fun _ => by positivity) 0 ?_
    have h := fib_ge_pow hnK
    have : (0 : ℝ) < ((3 : ℝ) / 2) ^ (n (K + 1) - 2) := by positivity
    simp only [zero_add]
    exact one_div_pos.mpr (by linarith)
  have hTle := tail_le n hn K hnK
  -- the integer den * L * T
  have hint : (r.den : ℝ) * L * T = ((r.num * L - r.den * z : ℤ) : ℝ) := by
    have hr' : (r : ℝ) = r.num / r.den := by exact_mod_cast (Rat.num_div_den r).symm
    have hS : ∑' k, 1 / (Nat.fib (n k) : ℝ) = ∑ k ∈ range (K + 1), 1 / (Nat.fib (n k) : ℝ) + T :=
      hsum.symm
    have hT' : T = r - ∑ k ∈ range (K + 1), 1 / (Nat.fib (n k) : ℝ) := by
      rw [hr, hS]; ring
    push_cast
    rw [hT', mul_sub, ← hz, hr']
    field_simp
  have hwpos : (0 : ℝ) < (r.den : ℝ) * L * T := by positivity
  have hw1 : (1 : ℝ) ≤ (r.den : ℝ) * L * T := by
    rw [hint] at hwpos ⊢
    have : (0 : ℤ) < r.num * L - r.den * z := by exact_mod_cast hwpos
    exact_mod_cast this
  -- the upper bound
  have hF := fib_ge_pow hnK
  have hexp : 2 * s + m + 1 ≤ n (K + 1) - 2 := by omega
  have hpow : (2 : ℝ) ^ s * ((3 : ℝ) / 2) ^ m ≤ ((3 : ℝ) / 2) ^ (n (K + 1) - 2) := by
    calc (2 : ℝ) ^ s * ((3 : ℝ) / 2) ^ m ≤ ((3 : ℝ) / 2) ^ (2 * s) * ((3 : ℝ) / 2) ^ m := by
          gcongr
          rw [pow_mul]
          exact pow_le_pow_left₀ (by norm_num) (by norm_num) s
      _ = ((3 : ℝ) / 2) ^ (2 * s + m) := by rw [pow_add]
      _ ≤ ((3 : ℝ) / 2) ^ (n (K + 1) - 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hFpos : (0 : ℝ) < Nat.fib (n (K + 1)) := by
    have : (0 : ℝ) < ((3 : ℝ) / 2) ^ (n (K + 1) - 2) := by positivity
    linarith
  have hbound : (r.den : ℝ) * L * T ≤ 3 * r.den / ((3 : ℝ) / 2) ^ m := by
    have hm0 : (0 : ℝ) < ((3 : ℝ) / 2) ^ m := by positivity
    have h2s : (0 : ℝ) < 2 ^ s := by positivity
    calc (r.den : ℝ) * L * T ≤ r.den * 2 ^ s * (3 / Nat.fib (n (K + 1))) := by
          gcongr
      _ ≤ r.den * 2 ^ s * (3 / (2 ^ s * ((3 : ℝ) / 2) ^ m)) := by
          gcongr
          exact hpow.trans hF
      _ = 3 * r.den / ((3 : ℝ) / 2) ^ m := by
          field_simp
  have hlt : 3 * (r.den : ℝ) / ((3 : ℝ) / 2) ^ m < 1 := by
    rw [div_lt_one (by positivity)]
    exact hm
  linarith

theorem main : H1 → H2 →
    type_of% @Erdos267.erdos_267.variants.generalisation_ratio_limit_to_infinity := by
  intro h1 h2 n hn hlim
  by_cases hlac : ∃ c : ℝ, 1 < c ∧ ∀ᶠ k in atTop, c * n k ≤ n (k + 1)
  · exact h1 n hn hlac
  · have hslow : ∀ c : ℝ, 1 < c → ∃ᶠ k in atTop, (n (k + 1) : ℝ) < c * n k := by
      intro c hc
      have hne : ¬ ∀ᶠ k in atTop, c * (n k : ℝ) ≤ n (k + 1) := fun h => hlac ⟨c, hc, h⟩
      rw [Filter.not_eventually] at hne
      simpa only [not_le] using hne
    by_cases hjump : ∀ C : ℕ, ∃ K, 2 * ∑ k ∈ range (K + 1), n k + C < n (K + 1)
    · exact super_lacunary n hn hjump
    · push Not at hjump
      exact h2 n hn hlim hslow hjump

end OMA.R_Erdos267_erdos_267_variants_generalisation_ratio_limit_to_infinity_R1
