import FormalConjectures.ErdosProblems.«1100»
import Mathlib.Analysis.Complex.ExponentialBounds

open Finset Real


/-!
# Proof of Erdős Problem 1100 (part i)

Self-contained proof that for every `C : ℝ`, the set `{n : ℕ | (tauPerp n : ℝ) ≤ C * (ω n : ℝ)}`
has natural density `0`.
-/

-- Problem: Erdős Problem 1100 — i
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1100.lean:75 (declaration Erdos1100.erdos_1100.parts.i)
-- Credit: @siraustin (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open scoped ArithmeticFunction.omega ArithmeticFunction.vonMangoldt Classical

namespace Erdos1100Proof

/- ## Section 1: Combinatorics of `tauPerp` and coprime consecutive divisor pairs -/

/-- A pair `(d₁, d₂)` is a coprime consecutive divisor pair of `n` if `d₁ < d₂`,
both divide `n`, `Nat.Coprime d₁ d₂`, and no divisor of `n` lies strictly between them. -/
def IsCoprimeConsecDiv (n d₁ d₂ : ℕ) : Prop :=
  d₁ ∣ n ∧ d₂ ∣ n ∧ d₁ < d₂ ∧ Nat.Coprime d₁ d₂ ∧ ∀ w : ℕ, w ∣ n → d₁ < w → d₂ ≤ w

/-- Every finite set `S` of upper endpoints `d₂` for which there exists a lower endpoint `d₁`
forming a coprime consecutive divisor pair of `n` has cardinality at most `tauPerp n`. -/
lemma card_le_tauPerp_of_exists_consec {n : ℕ} (hn : 0 < n) (S : Finset ℕ)
    (hS : ∀ d₂ ∈ S, ∃ d₁ : ℕ, IsCoprimeConsecDiv n d₁ d₂) :
    S.card ≤ Erdos1100.tauPerp n := by
  have hf : (Set.ofPred (· ∣ n)).Finite :=
    (Set.finite_Iic n).subset fun d hd => Nat.le_of_dvd hn hd
  have hcard : hf.toFinset.card = n.divisors.card := by
    congr 1
    ext d
    simp [hn.ne']
  let T := univ.filter fun i : Fin (n.divisors.card - 1) ↦
    Nat.Coprime (Nat.nth (· ∣ n) i) (Nat.nth (· ∣ n) ((i : ℕ) + 1))
  have hsub : S ⊆ T.image fun i : Fin (n.divisors.card - 1) =>
      Nat.nth (· ∣ n) ((i : ℕ) + 1) := by
    intro d₂ hd₂
    obtain ⟨d₁, hd₁n, hd₂n, hlt₁₂, hcop, hconsec⟩ := hS d₂ hd₂
    set j := Nat.count (· ∣ n) d₂ with hj
    have hj1 : 1 ≤ j := by
      have := Nat.count_strict_mono (p := (· ∣ n)) hd₁n hlt₁₂
      omega
    have hjlt : j < hf.toFinset.card := Nat.count_lt_card hf hd₂n
    have hnth2 : Nat.nth (· ∣ n) (j - 1 + 1) = d₂ := by
      rw [Nat.sub_add_cancel hj1, hj, Nat.nth_count (p := (· ∣ n)) hd₂n]
    have hprev_lt : Nat.nth (· ∣ n) (j - 1) < d₂ := by
      have := Nat.nth_lt_nth_of_lt_card hf (Nat.sub_lt hj1 one_pos) hjlt
      rwa [hj, Nat.nth_count (p := (· ∣ n)) hd₂n, ← hj] at this
    have hprev_dvd : Nat.nth (· ∣ n) (j - 1) ∣ n :=
      Nat.nth_mem_of_lt_card hf (by omega)
    have hprev_eq : Nat.nth (· ∣ n) (j - 1) = d₁ := by
      apply le_antisymm
      · by_contra hgt
        push Not at hgt
        have := hconsec (Nat.nth (· ∣ n) (j - 1)) hprev_dvd hgt
        omega
      · have hc₁ : Nat.count (· ∣ n) d₁ < j := Nat.count_strict_mono (p := (· ∣ n)) hd₁n hlt₁₂
        have hc₁_le : Nat.count (· ∣ n) d₁ ≤ j - 1 := by omega
        rcases eq_or_lt_of_le hc₁_le with heq | hltc
        · rw [← heq, Nat.nth_count (p := (· ∣ n)) hd₁n]
        · have hmono := Nat.nth_lt_nth_of_lt_card hf hltc (by omega)
          rw [Nat.nth_count (p := (· ∣ n)) hd₁n] at hmono
          exact le_of_lt hmono
    refine mem_image.mpr ⟨⟨j - 1, by omega⟩,
      mem_filter.mpr ⟨mem_univ _, ?_⟩, hnth2⟩
    show Nat.Coprime (Nat.nth (· ∣ n) (j - 1)) (Nat.nth (· ∣ n) (j - 1 + 1))
    rw [hprev_eq, hnth2]
    exact hcop
  calc S.card
      ≤ (T.image fun i : Fin (n.divisors.card - 1) => Nat.nth (· ∣ n) ((i : ℕ) + 1)).card :=
        card_le_card hsub
    _ ≤ T.card := card_image_le
    _ = Erdos1100.tauPerp n := rfl

/-- If `n = A * Q * R` (with `A, Q, R` pairwise coprime), every prime dividing `R` is `> B`,
`d` and `d'` are coprime consecutive divisors of `Q` with `d' ≤ B` and `A * d < d'`,
then `(A * d, d')` is a coprime consecutive divisor pair of `n`. -/
lemma isCoprimeConsecDiv_of_block {n A Q R B d d' : ℕ}
    (hn : n = A * Q * R) (hApos : 0 < A)
    (hAQ : Nat.Coprime A Q)
    (hRgt : ∀ p : ℕ, p.Prime → p ∣ R → B < p)
    (hdQ : d ∣ Q) (hd'Q : d' ∣ Q) (hd'B : d' ≤ B)
    (hcop : Nat.Coprime d d') (hgap : A * d < d')
    (hconsecQ : ∀ u : ℕ, u ∣ Q → d < u → d' ≤ u) :
    IsCoprimeConsecDiv n (A * d) d' := by
  refine ⟨?_, ?_, hgap, ?_, ?_⟩
  · rw [hn]; exact dvd_mul_of_dvd_left (mul_dvd_mul_left A hdQ) R
  · rw [hn]; exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd'Q A) R
  · exact (hAQ.coprime_dvd_right hd'Q).mul_left hcop
  · intro w hwn hlt
    by_contra hlt'
    push Not at hlt'
    have hwB : w ≤ B := le_trans (le_of_lt hlt') hd'B
    have hwR : Nat.Coprime w R := by
      rw [Nat.coprime_iff_gcd_eq_one]
      by_contra hne
      obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hne
      have hpw : p ∣ w := dvd_trans hpg (Nat.gcd_dvd_left w R)
      have hpR : p ∣ R := dvd_trans hpg (Nat.gcd_dvd_right w R)
      have hwpos : 0 < w := by omega
      have hple : p ≤ w := Nat.le_of_dvd hwpos hpw
      have := hRgt p hp hpR
      omega
    have hwAQ : w ∣ A * Q := by
      rw [hn] at hwn
      exact hwR.dvd_of_dvd_mul_right hwn
    obtain ⟨a, u, haA, huQ, rfl⟩ := Nat.dvd_mul.mp hwAQ
    have ha_le : a ≤ A := Nat.le_of_dvd hApos haA
    have ha_pos : 0 < a := Nat.pos_of_dvd_of_pos haA hApos
    have hu_gt : d < u := by
      by_contra hule
      push Not at hule
      have : a * u ≤ A * d := Nat.mul_le_mul ha_le hule
      omega
    have hu_ge : d' ≤ u := hconsecQ u huQ hu_gt
    have : d' ≤ a * u := le_trans hu_ge (Nat.le_mul_of_pos_left u ha_pos)
    omega

/- ## Section 2: Mertens' First and Second Theorems and Markov bound on `ω` -/

/-- Auxiliary function `F(k) = k log k - k` for elementary Stirling bounds. -/
private noncomputable def stirF (k : ℕ) : ℝ :=
  (k : ℝ) * log (k : ℝ) - (k : ℝ)

private lemma stirF_step_lower (k : ℕ) (hk : 1 ≤ k) :
    stirF k - stirF (k - 1) ≤ log (k : ℝ) := by
  rcases eq_or_lt_of_le hk with rfl | hk2
  · simp [stirF]
  · have hk1 : (1 : ℝ) ≤ (k - 1 : ℕ) := by exact_mod_cast (show 1 ≤ k - 1 by omega)
    have hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
    have hkm1_pos : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by positivity
    have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    have hlog : log ((k : ℝ) / ((k - 1 : ℕ) : ℝ)) ≤ (k : ℝ) / ((k - 1 : ℕ) : ℝ) - 1 :=
      log_le_sub_one_of_pos (div_pos hk_pos hkm1_pos)
    have hmul : ((k - 1 : ℕ) : ℝ) * log ((k : ℝ) / ((k - 1 : ℕ) : ℝ)) ≤ 1 := by
      have h1 := mul_le_mul_of_nonneg_left hlog hkm1_pos.le
      have h2 : ((k - 1 : ℕ) : ℝ) * ((k : ℝ) / ((k - 1 : ℕ) : ℝ) - 1) = 1 := by
        field_simp [hkm1_pos.ne']
        linarith [hcast]
      linarith
    rw [log_div hk_pos.ne' hkm1_pos.ne'] at hmul
    unfold stirF
    rw [hcast] at hmul ⊢
    linarith

private lemma stirF_step_upper (k : ℕ) (hk : 1 ≤ k) :
    log (k : ℝ) ≤ stirF (k + 1) - stirF k := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
  have hkp1_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hlog : log ((k : ℝ) / ((k + 1 : ℕ) : ℝ)) ≤ (k : ℝ) / ((k + 1 : ℕ) : ℝ) - 1 :=
    log_le_sub_one_of_pos (div_pos hk_pos hkp1_pos)
  have hmul : ((k + 1 : ℕ) : ℝ) * log ((k : ℝ) / ((k + 1 : ℕ) : ℝ)) ≤ -1 := by
    have h1 := mul_le_mul_of_nonneg_left hlog hkp1_pos.le
    have h2 : ((k + 1 : ℕ) : ℝ) * ((k : ℝ) / ((k + 1 : ℕ) : ℝ) - 1) = -1 := by
      field_simp [hkp1_pos.ne']
      push_cast
      ring
    linarith
  rw [log_div hk_pos.ne' hkp1_pos.ne'] at hmul
  unfold stirF
  push_cast at hmul ⊢
  linarith

private lemma sum_log_bounds (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) * log (N : ℝ) - (N : ℝ) ≤ ∑ n ∈ Icc 1 N, log (n : ℝ) ∧
    ∑ n ∈ Icc 1 N, log (n : ℝ) ≤ (N : ℝ) * log (N : ℝ) - (N : ℝ) + log (N : ℝ) + 2 := by
  have hlow : ∑ n ∈ Icc 1 N, (stirF n - stirF (n - 1)) ≤ ∑ n ∈ Icc 1 N, log (n : ℝ) :=
    sum_le_sum fun k hk => stirF_step_lower k (mem_Icc.mp hk).1
  have hhigh : ∑ n ∈ Icc 1 N, log (n : ℝ) ≤ ∑ n ∈ Icc 1 N, (stirF (n + 1) - stirF n) :=
    sum_le_sum fun k hk => stirF_step_upper k (mem_Icc.mp hk).1
  have htel1_all : ∀ M : ℕ, ∑ n ∈ Icc 1 M, (stirF n - stirF (n - 1)) = stirF M - stirF 0 := by
    intro M
    induction M with
    | zero => simp
    | succ m ih =>
      have hIcc : Icc 1 (m + 1) = insert (m + 1) (Icc 1 m) := by
        ext k; simp only [mem_Icc, mem_insert]; omega
      rw [hIcc, sum_insert (by simp only [mem_Icc]; omega), ih]
      simp only [Nat.add_sub_cancel]; ring
  have htel2_all : ∀ M : ℕ, ∑ n ∈ Icc 1 M, (stirF (n + 1) - stirF n) = stirF (M + 1) - stirF 1 := by
    intro M
    induction M with
    | zero => simp
    | succ m ih =>
      have hIcc : Icc 1 (m + 1) = insert (m + 1) (Icc 1 m) := by
        ext k; simp only [mem_Icc, mem_insert]; omega
      rw [hIcc, sum_insert (by simp only [mem_Icc]; omega), ih]
      ring
  have htel1 := htel1_all N
  have htel2 := htel2_all N
  have hF0 : stirF 0 = 0 := by simp [stirF]
  have hF1 : stirF 1 = -1 := by simp [stirF]
  constructor
  · rw [htel1, hF0, sub_zero] at hlow
    exact hlow
  · rw [htel2, hF1] at hhigh
    have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
    have hlog_step : log ((N : ℝ) + 1) - log (N : ℝ) ≤ 1 / (N : ℝ) := by
      rw [← log_div (by positivity) hN_pos.ne']
      have := log_le_sub_one_of_pos (div_pos (by positivity : (0 : ℝ) < (N : ℝ) + 1) hN_pos)
      have hdiv : ((N : ℝ) + 1) / (N : ℝ) - 1 = 1 / (N : ℝ) := by field_simp [hN_pos.ne']; ring
      linarith
    have hN_mul : (N : ℝ) * (log ((N : ℝ) + 1) - log (N : ℝ)) ≤ 1 := by
      have := mul_le_mul_of_nonneg_left hlog_step hN_pos.le
      rwa [mul_one_div_cancel hN_pos.ne'] at this
    have h1N : (1 : ℝ) / (N : ℝ) ≤ 1 := by
      rw [div_le_one hN_pos]; exact_mod_cast hN
    unfold stirF at hhigh
    push_cast at hhigh
    nlinarith

/-- Double-counting identity `∑_{n=1}^N log n = ∑_{d=1}^N Λ(d) * ⌊N/d⌋`. -/
private lemma sum_log_eq_sum_vonMangoldt_mul_div (N : ℕ) :
    ∑ n ∈ Icc 1 N, log (n : ℝ) = ∑ d ∈ Icc 1 N, Λ d * ((N / d : ℕ) : ℝ) := by
  have h1 : ∑ n ∈ Icc 1 N, log (n : ℝ) =
      ∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, if d ∣ n then Λ d else 0 := by
    refine sum_congr rfl fun n hn => ?_
    have hn_pos : 0 < n := (mem_Icc.mp hn).1
    have hn_le : n ≤ N := (mem_Icc.mp hn).2
    rw [← ArithmeticFunction.vonMangoldt_sum, ← sum_filter]
    refine sum_congr ?_ fun _ _ => rfl
    ext d
    simp only [Nat.mem_divisors, mem_filter, mem_Icc]
    constructor
    · rintro ⟨hdn, -⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hdn hn_pos, le_trans (Nat.le_of_dvd hn_pos hdn) hn_le⟩, hdn⟩
    · rintro ⟨-, hdn⟩
      exact ⟨hdn, hn_pos.ne'⟩
  rw [h1, sum_comm]
  refine sum_congr rfl fun d hd => ?_
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  congr 1
  norm_cast
  have hd_pos : 0 < d := (mem_Icc.mp hd).1
  have hcard : ((Icc 1 N).filter (fun n => d ∣ n)).card = N / d := by
    have hbij : ((Icc 1 N).filter (fun n => d ∣ n)) = (Icc 1 (N / d)).image (fun k => d * k) := by
      ext n
      simp only [mem_filter, mem_Icc, mem_image]
      constructor
      · rintro ⟨⟨hn1, hnN⟩, k, rfl⟩
        refine ⟨k, ⟨?_, ?_⟩, rfl⟩
        · by_contra hk0; push Not at hk0; interval_cases k; simp at hn1
        · exact (Nat.le_div_iff_mul_le hd_pos).mpr (by rw [mul_comm]; exact hnN)
      · rintro ⟨k, ⟨hk1, hkdiv⟩, rfl⟩
        exact ⟨⟨Nat.mul_pos hd_pos hk1, by rw [mul_comm]; exact (Nat.le_div_iff_mul_le hd_pos).mp hkdiv⟩,
          dvd_mul_right d k⟩
    rw [hbij, card_image_of_injective _ (mul_right_injective₀ hd_pos.ne'), Nat.card_Icc]
    exact Nat.add_sub_cancel (N / d) 1
  exact hcard

/-- Mertens' first theorem for `Λ`: `|∑_{d=1}^N Λ(d)/d - log N| ≤ 12` for all `N ≥ 1`. -/
private lemma mertens_first_vonMangoldt (N : ℕ) (hN : 1 ≤ N) :
    |∑ d ∈ Icc 1 N, Λ d / (d : ℝ) - log (N : ℝ)| ≤ 12 := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  have hsum := sum_log_eq_sum_vonMangoldt_mul_div N
  have hbounds := sum_log_bounds N hN
  have hpsi : ∑ d ∈ Icc 1 N, Λ d ≤ (log 4 + 4) * (N : ℝ) := by
    have hEq : ∑ d ∈ Icc 1 N, Λ d = Chebyshev.psi (N : ℝ) := by
      rw [Chebyshev.psi, Nat.floor_natCast]
      refine sum_congr ?_ fun _ _ => rfl
      ext d; simp only [mem_Icc, mem_Ioc]; omega
    rw [hEq]
    exact Chebyshev.psi_le_const_mul_self hN_pos.le
  have hlog4 : log 4 ≤ 2 := by
    have h4 : (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
    rw [h4, log_pow]
    push_cast
    have h2 : log 2 ≤ 1 := by
      have := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    linarith
  have hupper : ∑ d ∈ Icc 1 N, Λ d * ((N / d : ℕ) : ℝ) ≤
      (N : ℝ) * ∑ d ∈ Icc 1 N, Λ d / (d : ℝ) := by
    rw [mul_sum]
    refine sum_le_sum fun d hd => ?_
    have hd_pos : (0 : ℝ) < (d : ℝ) := by
      have := (mem_Icc.mp hd).1; positivity
    have hdiv_le : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) := by
      rw [le_div_iff₀ hd_pos]
      exact_mod_cast Nat.div_mul_le_self N d
    have hΛ : 0 ≤ Λ d := ArithmeticFunction.vonMangoldt_nonneg
    calc Λ d * ((N / d : ℕ) : ℝ) ≤ Λ d * ((N : ℝ) / (d : ℝ)) :=
          mul_le_mul_of_nonneg_left hdiv_le hΛ
      _ = (N : ℝ) * (Λ d / (d : ℝ)) := by ring
  have hlower : (N : ℝ) * ∑ d ∈ Icc 1 N, Λ d / (d : ℝ) - ∑ d ∈ Icc 1 N, Λ d ≤
      ∑ d ∈ Icc 1 N, Λ d * ((N / d : ℕ) : ℝ) := by
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_le_sum fun d hd => ?_
    have hd_pos : (0 : ℝ) < (d : ℝ) := by
      have := (mem_Icc.mp hd).1; positivity
    have hdiv_ge : (N : ℝ) / (d : ℝ) - 1 ≤ ((N / d : ℕ) : ℝ) := by
      have h1 : N < (N / d + 1) * d := by
        have := Nat.div_add_mod N d
        have hmod : N % d < d := Nat.mod_lt N (mem_Icc.mp hd).1
        nlinarith
      have h2 : (N : ℝ) < (((N / d : ℕ) : ℝ) + 1) * (d : ℝ) := by exact_mod_cast h1
      have h3 : (N : ℝ) / (d : ℝ) < ((N / d : ℕ) : ℝ) + 1 := (div_lt_iff₀ hd_pos).mpr h2
      linarith
    have hΛ : 0 ≤ Λ d := ArithmeticFunction.vonMangoldt_nonneg
    calc (N : ℝ) * (Λ d / (d : ℝ)) - Λ d = Λ d * ((N : ℝ) / (d : ℝ) - 1) := by ring
      _ ≤ Λ d * ((N / d : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hdiv_ge hΛ
  have hlogN_le : log (N : ℝ) ≤ (N : ℝ) := by
    have := log_le_sub_one_of_pos hN_pos; linarith
  have h1 : (N : ℝ) * log (N : ℝ) - (N : ℝ) ≤ (N : ℝ) * ∑ d ∈ Icc 1 N, Λ d / (d : ℝ) := by
    linarith [hbounds.1, hsum, hupper]
  have h2 : (N : ℝ) * ∑ d ∈ Icc 1 N, Λ d / (d : ℝ) ≤
      (N : ℝ) * log (N : ℝ) + 10 * (N : ℝ) := by
    have h2N : (2 : ℝ) ≤ 2 * (N : ℝ) := by
      have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    nlinarith [hbounds.2, hsum, hlower, hpsi, hlog4, hlogN_le, h2N]
  rw [abs_le]
  constructor
  · have : (N : ℝ) * (-12) ≤ (N : ℝ) * (∑ d ∈ Icc 1 N, Λ d / (d : ℝ) - log (N : ℝ)) := by
      nlinarith
    exact le_of_mul_le_mul_left this hN_pos
  · have : (N : ℝ) * (∑ d ∈ Icc 1 N, Λ d / (d : ℝ) - log (N : ℝ)) ≤ (N : ℝ) * 12 := by
      nlinarith
    exact le_of_mul_le_mul_left this hN_pos

/-- Bound on the non-prime contribution `∑_{d ≤ N, ¬d.Prime} Λ(d)/d ≤ 40`. -/
private lemma sum_vonMangoldt_not_prime_div_le (N : ℕ) :
    ∑ d ∈ (Icc 1 N).filter (fun d => ¬d.Prime), Λ d / (d : ℝ) ≤ 40 := by
  have hcov : (Icc 1 N).filter (fun d => ¬d.Prime) ⊆
      (range (N + 1)).biUnion fun k =>
        (Ico (2 ^ k) (2 ^ (k + 1))).filter (fun d => ¬d.Prime) := by
    intro d hd
    simp only [mem_filter, mem_Icc] at hd
    simp only [mem_biUnion, mem_range, mem_filter, mem_Ico]
    refine ⟨Nat.log 2 d, ?_, ⟨Nat.pow_log_le_self 2 (by omega), Nat.lt_pow_succ_log_self (by norm_num) d⟩, hd.2⟩
    have hlt : Nat.log 2 d < d := Nat.log_lt_self 2 (by omega)
    omega
  have hdisj : Set.PairwiseDisjoint (range (N + 1) : Set ℕ) fun k =>
      (Ico (2 ^ k) (2 ^ (k + 1))).filter (fun d => ¬d.Prime) := by
    intro a _ b _ hab
    change Disjoint _ _
    rw [disjoint_left]
    intro d hda hdb
    simp only [mem_filter, mem_Ico] at hda hdb
    rcases lt_or_gt_of_ne hab with hlt | hlt
    · have : 2 ^ (a + 1) ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hlt
      omega
    · have : 2 ^ (b + 1) ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hlt
      omega
  have h1 : ∑ d ∈ (Icc 1 N).filter (fun d => ¬d.Prime), Λ d / (d : ℝ) ≤
      ∑ k ∈ range (N + 1),
        ∑ d ∈ (Ico (2 ^ k) (2 ^ (k + 1))).filter (fun d => ¬d.Prime), Λ d / (d : ℝ) := by
    rw [← sum_biUnion hdisj]
    exact sum_le_sum_of_subset_of_nonneg hcov fun d _ _ =>
      div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg d)
  have hstep : ∀ k : ℕ,
      ∑ d ∈ (Ico (2 ^ k) (2 ^ (k + 1))).filter (fun d => ¬d.Prime), Λ d / (d : ℝ) ≤
        2 * sqrt 2 * ((k + 1 : ℝ) * (sqrt 2)⁻¹ ^ k) := by
    intro k
    have hpow_pos : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by positivity
    have hle_div : ∑ d ∈ (Ico (2 ^ k) (2 ^ (k + 1))).filter (fun d => ¬d.Prime), Λ d / (d : ℝ) ≤
        (∑ d ∈ (Ico (2 ^ k) (2 ^ (k + 1))).filter (fun d => ¬d.Prime), Λ d) / ((2 ^ k : ℕ) : ℝ) := by
      rw [sum_div]
      refine sum_le_sum fun d hd => ?_
      have hd_ge : 2 ^ k ≤ d := (mem_Ico.mp (mem_filter.mp hd).1).1
      exact div_le_div_of_nonneg_left ArithmeticFunction.vonMangoldt_nonneg hpow_pos (by exact_mod_cast hd_ge)
    have hsub_psi : ∑ d ∈ (Ico (2 ^ k) (2 ^ (k + 1))).filter (fun d => ¬d.Prime), Λ d ≤
        Chebyshev.psi ((2 ^ (k + 1) : ℕ) : ℝ) - Chebyshev.theta ((2 ^ (k + 1) : ℕ) : ℝ) := by
      rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast]
      refine sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg
      intro d hd
      simp only [mem_filter, mem_Ico, mem_Ioc] at hd ⊢
      have h2k : 0 < 2 ^ k := Nat.two_pow_pos k
      exact ⟨⟨by omega, le_of_lt hd.1.2⟩, hd.2⟩
    have hdiff := Chebyshev.psi_sub_theta_le (x := ((2 ^ (k + 1) : ℕ) : ℝ)) (by
      have : 1 ≤ 2 ^ (k + 1) := Nat.one_le_pow _ _ (by norm_num)
      exact_mod_cast this)
    have hlog2 : log 2 ≤ 1 := by
      have := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
    have hsqrt_pow_aux : ∀ j : ℕ, sqrt ((2 : ℝ) ^ j) = (sqrt 2) ^ j := by
      intro j
      induction j with
      | zero => simp
      | succ m ih => rw [pow_succ, sqrt_mul (by positivity), ih, pow_succ]
    have hsqrt_pow : sqrt ((2 ^ (k + 1) : ℕ) : ℝ) = sqrt 2 * (sqrt 2) ^ k := by
      rw [Nat.cast_pow, Nat.cast_ofNat, pow_succ', sqrt_mul (by norm_num), hsqrt_pow_aux]
    have hpow2 : ((2 ^ k : ℕ) : ℝ) = (sqrt 2) ^ k * (sqrt 2) ^ k := by
      rw [← mul_pow, mul_self_sqrt (by norm_num)]; norm_cast
    have hlog_pow : log ((2 ^ (k + 1) : ℕ) : ℝ) ≤ (k + 1 : ℝ) := by
      rw [Nat.cast_pow, Nat.cast_ofNat, log_pow]
      push_cast
      nlinarith
    have hnum : 2 * sqrt ((2 ^ (k + 1) : ℕ) : ℝ) * log ((2 ^ (k + 1) : ℕ) : ℝ) ≤
        2 * sqrt 2 * (sqrt 2) ^ k * (k + 1 : ℝ) := by
      rw [hsqrt_pow]
      have hpos1 : 0 ≤ 2 * (sqrt 2 * (sqrt 2) ^ k) := by positivity
      nlinarith
    calc ∑ d ∈ (Ico (2 ^ k) (2 ^ (k + 1))).filter (fun d => ¬d.Prime), Λ d / (d : ℝ)
        ≤ (2 * sqrt ((2 ^ (k + 1) : ℕ) : ℝ) * log ((2 ^ (k + 1) : ℕ) : ℝ)) /
            ((2 ^ k : ℕ) : ℝ) := by
          exact le_trans hle_div (div_le_div_of_nonneg_right (le_trans hsub_psi hdiff) hpow_pos.le)
      _ ≤ (2 * sqrt 2 * (sqrt 2) ^ k * (k + 1 : ℝ)) / ((2 ^ k : ℕ) : ℝ) :=
          div_le_div_of_nonneg_right hnum hpow_pos.le
      _ = 2 * sqrt 2 * ((k + 1 : ℝ) * (sqrt 2)⁻¹ ^ k) := by
          rw [hpow2, inv_pow]
          have hs_ne : (sqrt 2) ^ k ≠ 0 := by positivity
          field_simp [hs_ne]
  set r : ℝ := (sqrt 2)⁻¹
  have hs2_gt : (7 : ℝ) / 5 < sqrt 2 := (lt_sqrt (by norm_num)).mpr (by norm_num)
  have hs2_lt : sqrt 2 < (3 : ℝ) / 2 := (sqrt_lt' (by norm_num)).mpr (by norm_num)
  have hr_pos : 0 < r := by positivity
  have hr_lt : r < 5 / 7 := by
    rw [show r = (sqrt 2)⁻¹ from rfl, inv_lt_comm₀ (by positivity) (by norm_num)]
    linarith
  have h1mr_ge : (2 : ℝ) / 7 < 1 - r := by linarith
  have h1mr_pos : 0 < 1 - r := by linarith
  have hident : ∀ M : ℕ, (1 - r) * ∑ k ∈ range M, ((k + 1 : ℝ) * r ^ k) =
      (∑ k ∈ range M, r ^ k) - (M : ℝ) * r ^ M := by
    intro M
    induction M with
    | zero => simp
    | succ m ih =>
      rw [sum_range_succ, sum_range_succ, mul_add, ih]
      push_cast
      rw [pow_succ]
      ring
  have hgeom0 : ∀ M : ℕ, (1 - r) * ∑ k ∈ range M, r ^ k = 1 - r ^ M := by
    intro M
    induction M with
    | zero => simp
    | succ m ih =>
      rw [sum_range_succ, mul_add, ih, pow_succ]
      ring
  have hgeom : ∑ k ∈ range (N + 1), ((k + 1 : ℝ) * r ^ k) ≤ 1 / (1 - r) ^ 2 := by
    rw [le_div_iff₀ (pow_pos h1mr_pos 2)]
    have hA : (1 - r) * ∑ k ∈ range (N + 1), ((k + 1 : ℝ) * r ^ k) ≤
        ∑ k ∈ range (N + 1), r ^ k := by
      rw [hident]
      have : (0 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) * r ^ (N + 1) := by positivity
      linarith
    have hB : (1 - r) * ∑ k ∈ range (N + 1), r ^ k ≤ 1 := by
      rw [hgeom0]
      have : (0 : ℝ) ≤ r ^ (N + 1) := by positivity
      linarith
    have hmul := mul_le_mul_of_nonneg_left hA h1mr_pos.le
    calc (∑ k ∈ range (N + 1), ((k + 1 : ℝ) * r ^ k)) * (1 - r) ^ 2
        = (1 - r) * ((1 - r) * ∑ k ∈ range (N + 1), ((k + 1 : ℝ) * r ^ k)) := by ring
      _ ≤ (1 - r) * ∑ k ∈ range (N + 1), r ^ k := hmul
      _ ≤ 1 := hB
  have hsum_step : ∑ k ∈ range (N + 1),
      ∑ d ∈ (Ico (2 ^ k) (2 ^ (k + 1))).filter (fun d => ¬d.Prime), Λ d / (d : ℝ) ≤
      2 * sqrt 2 * (1 / (1 - r) ^ 2) := by
    calc _ ≤ ∑ k ∈ range (N + 1), (2 * sqrt 2 * ((k + 1 : ℝ) * r ^ k)) :=
            sum_le_sum fun k _ => hstep k
      _ = 2 * sqrt 2 * ∑ k ∈ range (N + 1), ((k + 1 : ℝ) * r ^ k) := by
            rw [mul_sum]
      _ ≤ 2 * sqrt 2 * (1 / (1 - r) ^ 2) :=
            mul_le_mul_of_nonneg_left hgeom (by positivity)
  have hfinal : 2 * sqrt 2 * (1 / (1 - r) ^ 2) ≤ 40 := by
    have hsq : (4 : ℝ) / 49 ≤ (1 - r) ^ 2 := by nlinarith
    have hinv : 1 / (1 - r) ^ 2 ≤ 49 / 4 := by
      rw [div_le_iff₀ (pow_pos h1mr_pos 2)]
      nlinarith
    nlinarith
  exact le_trans (le_trans h1 hsum_step) hfinal

/-- Mertens' first theorem for primes: `|∑_{p ≤ N} log p / p - log N| ≤ 52` for all `N ≥ 1`. -/
lemma mertens_first_nat (N : ℕ) (hN : 1 ≤ N) :
    |∑ p ∈ (Icc 1 N).filter Nat.Prime, log (p : ℝ) / (p : ℝ) - log (N : ℝ)| ≤ 52 := by
  have hsplit : ∑ d ∈ Icc 1 N, Λ d / (d : ℝ) =
      (∑ p ∈ (Icc 1 N).filter Nat.Prime, log (p : ℝ) / (p : ℝ)) +
      (∑ d ∈ (Icc 1 N).filter (fun d => ¬d.Prime), Λ d / (d : ℝ)) := by
    rw [← sum_filter_add_sum_filter_not (Icc 1 N) Nat.Prime (fun d => Λ d / (d : ℝ))]
    congr 1
    refine sum_congr rfl fun p hp => ?_
    rw [ArithmeticFunction.vonMangoldt_apply_prime (mem_filter.mp hp).2]
  have h1 := mertens_first_vonMangoldt N hN
  have h2 := sum_vonMangoldt_not_prime_div_le N
  have h3 : 0 ≤ ∑ d ∈ (Icc 1 N).filter (fun d => ¬d.Prime), Λ d / (d : ℝ) :=
    sum_nonneg fun d _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg d)
  rw [hsplit] at h1
  rw [abs_le] at h1 ⊢
  constructor <;> linarith

/-- Mertens' second theorem on an integer interval `(a, b]` (`2 ≤ a ≤ b`):
`|∑_{a < p ≤ b} 1/p - log (log b / log a)| ≤ 160 / log a`. -/
lemma mertens_second_Ioc_nat {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) :
    |∑ p ∈ (Ioc a b).filter Nat.Prime, (1 : ℝ) / (p : ℝ) -
      log (log (b : ℝ) / log (a : ℝ))| ≤ 160 / log (a : ℝ) := by
  have ha_pos : (0 : ℝ) < (a : ℝ) := by positivity
  have hloga_pos : 0 < log (a : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < a))
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp [div_self hloga_pos.ne']
    positivity
  -- Define `A n = ∑_{p ≤ n} log p / p` and `R n = A n - log n`.
  let A : ℕ → ℝ := fun n => ∑ p ∈ (Icc 1 n).filter Nat.Prime, log (p : ℝ) / (p : ℝ)
  let R : ℕ → ℝ := fun n => A n - log (n : ℝ)
  have hR : ∀ n : ℕ, 1 ≤ n → |R n| ≤ 52 := fun n hn => mertens_first_nat n hn
  have hdiff : ∀ n : ℕ, 2 ≤ n →
      (if n.Prime then (1 : ℝ) / (n : ℝ) else 0) = (A n - A (n - 1)) / log (n : ℝ) := by
    intro n hn
    have hlogn_ne : log (n : ℝ) ≠ 0 := (log_pos (by exact_mod_cast (by omega : 1 < n))).ne'
    have hIcc : Icc 1 n = insert n (Icc 1 (n - 1)) := by
      ext k; simp only [mem_Icc, mem_insert]; omega
    have hnotmem : n ∉ Icc 1 (n - 1) := by simp only [mem_Icc]; omega
    have hAdiff : A n - A (n - 1) = if n.Prime then log (n : ℝ) / (n : ℝ) else 0 := by
      simp only [A, hIcc]
      by_cases hp : n.Prime
      · rw [filter_insert, if_pos hp, sum_insert]
        · simp [hp]
        · intro h; exact hnotmem (mem_filter.mp h).1
      · rw [filter_insert, if_neg hp]
        simp [hp]
    rw [hAdiff]
    split_ifs with hp
    · field_simp [hlogn_ne]
    · simp
  have hsum_eq : ∑ p ∈ (Ioc a b).filter Nat.Prime, (1 : ℝ) / (p : ℝ) =
      ∑ n ∈ Icc (a + 1) b, (A n - A (n - 1)) / log (n : ℝ) := by
    rw [sum_filter]
    have hIoc : Ioc a b = Icc (a + 1) b := by ext k; simp only [mem_Ioc, mem_Icc]; omega
    rw [hIoc]
    refine sum_congr rfl fun n hn => ?_
    exact hdiff n (by have := (mem_Icc.mp hn).1; omega)
  -- Abel summation (summation by parts) on `Icc (a+1) b`:
  have habel_all : ∀ m : ℕ,
      ∑ n ∈ Icc (a + 1) (a + 1 + m), (A n - A (n - 1)) / log (n : ℝ) =
      A (a + 1 + m) / log ((a + 1 + m : ℕ) : ℝ) - A a / log ((a + 1 : ℕ) : ℝ) +
      ∑ n ∈ Icc (a + 1) (a + m), A n * (1 / log (n : ℝ) - 1 / log ((n + 1 : ℕ) : ℝ)) := by
    intro m
    induction m with
    | zero =>
      simp only [add_zero, Icc_self, sum_singleton, Nat.add_sub_cancel]
      have hIcc_empty : Icc (a + 1) a = ∅ := by ext k; simp only [mem_Icc, notMem_empty, iff_false]; omega
      rw [hIcc_empty, sum_empty, add_zero]
      ring
    | succ m ih =>
      have h1 : Icc (a + 1) (a + 1 + (m + 1)) = insert (a + 1 + (m + 1)) (Icc (a + 1) (a + 1 + m)) := by
        ext k; simp only [mem_Icc, mem_insert]; omega
      have h2 : Icc (a + 1) (a + (m + 1)) = insert (a + 1 + m) (Icc (a + 1) (a + m)) := by
        ext k; simp only [mem_Icc, mem_insert]; omega
      rw [h1, sum_insert (by simp only [mem_Icc]; omega), ih]
      rw [h2, sum_insert (by simp only [mem_Icc]; omega)]
      have hsub1 : a + 1 + (m + 1) - 1 = a + 1 + m := by omega
      have hadd1 : a + 1 + m + 1 = a + 1 + (m + 1) := by omega
      rw [hsub1, hadd1]
      ring
  have habel : ∑ n ∈ Icc (a + 1) b, (A n - A (n - 1)) / log (n : ℝ) =
      A b / log (b : ℝ) - A a / log ((a + 1 : ℕ) : ℝ) +
      ∑ n ∈ Icc (a + 1) (b - 1), A n * (1 / log (n : ℝ) - 1 / log ((n + 1 : ℕ) : ℝ)) := by
    have hm := habel_all (b - (a + 1))
    have hbm : a + 1 + (b - (a + 1)) = b := by omega
    have hbm1 : a + (b - (a + 1)) = b - 1 := by omega
    rwa [hbm, hbm1] at hm
  -- Substitute `A n = log n + R n` into `habel`:
  have hA_eq : ∀ n, A n = log (n : ℝ) + R n := fun n => by simp [R]
  have hlogb_pos : 0 < log (b : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < b))
  have hlogap1_pos : 0 < log ((a + 1 : ℕ) : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < a + 1))
  have hstep_pos : ∀ n ∈ Icc (a + 1) (b - 1),
      0 ≤ 1 / log (n : ℝ) - 1 / log ((n + 1 : ℕ) : ℝ) := by
    intro n hn
    have hn2 : 2 ≤ n := by have := (mem_Icc.mp hn).1; omega
    have hln : 0 < log (n : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < n))
    have hle : log (n : ℝ) ≤ log ((n + 1 : ℕ) : ℝ) :=
      log_le_log (by positivity) (by exact_mod_cast (by omega : n ≤ n + 1))
    exact sub_nonneg.mpr (one_div_le_one_div_of_le hln hle)
  -- Telescoping of `∑_{n=a+1}^{b-1} (1 / log n - 1 / log (n+1)) = 1 / log(a+1) - 1 / log b`:
  have htel_inv_all : ∀ m : ℕ, ∑ n ∈ Icc (a + 1) (a + m),
      (1 / log (n : ℝ) - 1 / log ((n + 1 : ℕ) : ℝ)) =
      1 / log ((a + 1 : ℕ) : ℝ) - 1 / log ((a + 1 + m : ℕ) : ℝ) := by
    intro m
    induction m with
    | zero =>
      have : Icc (a + 1) (a + 0) = ∅ := by ext k; simp only [mem_Icc, notMem_empty, iff_false]; omega
      rw [this, sum_empty]; simp
    | succ m ih =>
      have h2 : Icc (a + 1) (a + (m + 1)) = insert (a + 1 + m) (Icc (a + 1) (a + m)) := by
        ext k; simp only [mem_Icc, mem_insert]; omega
      rw [h2, sum_insert (by simp only [mem_Icc]; omega), ih]
      have hadd1 : a + 1 + m + 1 = a + 1 + (m + 1) := by omega
      rw [hadd1]; ring
  have htel_inv : ∑ n ∈ Icc (a + 1) (b - 1),
      (1 / log (n : ℝ) - 1 / log ((n + 1 : ℕ) : ℝ)) =
      1 / log ((a + 1 : ℕ) : ℝ) - 1 / log (b : ℝ) := by
    have hm := htel_inv_all (b - (a + 1))
    have hbm : a + 1 + (b - (a + 1)) = b := by omega
    have hbm1 : a + (b - (a + 1)) = b - 1 := by omega
    rwa [hbm, hbm1] at hm
  -- Telescoping of `∑_{n=a+1}^{b-1} (log(log(n+1)) - log(log n)) = log(log b) - log(log(a+1))`:
  have htel_ll_all : ∀ m : ℕ, ∑ n ∈ Icc (a + 1) (a + m),
      (log (log ((n + 1 : ℕ) : ℝ)) - log (log (n : ℝ))) =
      log (log ((a + 1 + m : ℕ) : ℝ)) - log (log ((a + 1 : ℕ) : ℝ)) := by
    intro m
    induction m with
    | zero =>
      have : Icc (a + 1) (a + 0) = ∅ := by ext k; simp only [mem_Icc, notMem_empty, iff_false]; omega
      rw [this, sum_empty]; simp
    | succ m ih =>
      have h2 : Icc (a + 1) (a + (m + 1)) = insert (a + 1 + m) (Icc (a + 1) (a + m)) := by
        ext k; simp only [mem_Icc, mem_insert]; omega
      rw [h2, sum_insert (by simp only [mem_Icc]; omega), ih]
      have hadd1 : a + 1 + m + 1 = a + 1 + (m + 1) := by omega
      rw [hadd1]; ring
  have htel_ll : ∑ n ∈ Icc (a + 1) (b - 1),
      (log (log ((n + 1 : ℕ) : ℝ)) - log (log (n : ℝ))) =
      log (log (b : ℝ)) - log (log ((a + 1 : ℕ) : ℝ)) := by
    have hm := htel_ll_all (b - (a + 1))
    have hbm : a + 1 + (b - (a + 1)) = b := by omega
    have hbm1 : a + (b - (a + 1)) = b - 1 := by omega
    rwa [hbm, hbm1] at hm
  -- Compare each main term `log n * (1/log n - 1/log(n+1))` with `log(log(n+1)) - log(log n)`:
  have hterm_cmp : ∀ n ∈ Icc (a + 1) (b - 1),
      |log (n : ℝ) * (1 / log (n : ℝ) - 1 / log ((n + 1 : ℕ) : ℝ)) -
        (log (log ((n + 1 : ℕ) : ℝ)) - log (log (n : ℝ)))| ≤
      1 / log (n : ℝ) - 1 / log ((n + 1 : ℕ) : ℝ) := by
    intro n hn
    have hn2 : 2 ≤ n := by have := (mem_Icc.mp hn).1; omega
    have hln_pos : 0 < log (n : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < n))
    have hln1_pos : 0 < log ((n + 1 : ℕ) : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < n + 1))
    have hln_le : log (n : ℝ) ≤ log ((n + 1 : ℕ) : ℝ) :=
      log_le_log (by positivity) (by exact_mod_cast (by omega : n ≤ n + 1))
    -- Let `u = log(n+1) / log n ≥ 1`. Then `1 - 1/u ≤ log u ≤ u - 1`.
    have hlow : 1 - log (n : ℝ) / log ((n + 1 : ℕ) : ℝ) ≤
        log (log ((n + 1 : ℕ) : ℝ)) - log (log (n : ℝ)) := by
      rw [← log_div hln1_pos.ne' hln_pos.ne']
      have h1 := log_le_sub_one_of_pos (div_pos hln_pos hln1_pos)
      rw [log_div hln_pos.ne' hln1_pos.ne'] at h1
      rw [log_div hln1_pos.ne' hln_pos.ne']
      linarith
    have hhigh : log (log ((n + 1 : ℕ) : ℝ)) - log (log (n : ℝ)) ≤
        log ((n + 1 : ℕ) : ℝ) / log (n : ℝ) - 1 := by
      rw [← log_div hln1_pos.ne' hln_pos.ne']
      exact log_le_sub_one_of_pos (div_pos hln1_pos hln_pos)
    have hLHS : log (n : ℝ) * (1 / log (n : ℝ) - 1 / log ((n + 1 : ℕ) : ℝ)) =
        1 - log (n : ℝ) / log ((n + 1 : ℕ) : ℝ) := by
      field_simp [hln_pos.ne', hln1_pos.ne']
    have hgap_log : log ((n + 1 : ℕ) : ℝ) - log (n : ℝ) ≤ 1 := by
      rw [← log_div (by positivity : ((n + 1 : ℕ) : ℝ) ≠ 0) (by positivity : (n : ℝ) ≠ 0)]
      have h1 := log_le_sub_one_of_pos (div_pos (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ)) (by positivity : (0 : ℝ) < (n : ℝ)))
      have h2 : ((n + 1 : ℕ) : ℝ) / (n : ℝ) - 1 ≤ 1 := by
        rw [sub_le_iff_le_add, div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ))]
        push_cast; linarith [show (2 : ℝ) ≤ (n : ℝ) by exact_mod_cast hn2]
      linarith
    have hdiff_bound : (log ((n + 1 : ℕ) : ℝ) / log (n : ℝ) - 1) -
        (1 - log (n : ℝ) / log ((n + 1 : ℕ) : ℝ)) ≤
        1 / log (n : ℝ) - 1 / log ((n + 1 : ℕ) : ℝ) := by
      have hid : (log ((n + 1 : ℕ) : ℝ) / log (n : ℝ) - 1) -
          (1 - log (n : ℝ) / log ((n + 1 : ℕ) : ℝ)) =
          (log ((n + 1 : ℕ) : ℝ) - log (n : ℝ)) *
            (1 / log (n : ℝ) - 1 / log ((n + 1 : ℕ) : ℝ)) := by
        field_simp [hln_pos.ne', hln1_pos.ne']
      rw [hid]
      have hnonneg : 0 ≤ 1 / log (n : ℝ) - 1 / log ((n + 1 : ℕ) : ℝ) :=
        sub_nonneg.mpr (one_div_le_one_div_of_le hln_pos hln_le)
      nlinarith
    rw [hLHS, abs_le]
    constructor <;> linarith
  -- Bound `|log(log(a+1)) - log(log a)| ≤ 1 / log a` and `|1 - log a / log(a+1)| ≤ 1 / log a`:
  have hlog_step_a : log ((a + 1 : ℕ) : ℝ) - log (a : ℝ) ≤ 1 := by
    rw [← log_div (by positivity : ((a + 1 : ℕ) : ℝ) ≠ 0) ha_pos.ne']
    have h1 := log_le_sub_one_of_pos (div_pos (by positivity : (0 : ℝ) < ((a + 1 : ℕ) : ℝ)) ha_pos)
    have h2 : ((a + 1 : ℕ) : ℝ) / (a : ℝ) - 1 ≤ 1 := by
      rw [sub_le_iff_le_add, div_le_iff₀ ha_pos]
      push_cast; linarith [show (2 : ℝ) ≤ (a : ℝ) by exact_mod_cast ha]
    linarith
  have hll_a : 0 ≤ log (log ((a + 1 : ℕ) : ℝ)) - log (log (a : ℝ)) ∧
      log (log ((a + 1 : ℕ) : ℝ)) - log (log (a : ℝ)) ≤ 1 / log (a : ℝ) := by
    have hle : log (a : ℝ) ≤ log ((a + 1 : ℕ) : ℝ) :=
      log_le_log ha_pos (by exact_mod_cast (by omega : a ≤ a + 1))
    constructor
    · exact sub_nonneg.mpr (log_le_log hloga_pos hle)
    · rw [← log_div hlogap1_pos.ne' hloga_pos.ne']
      have h1 := log_le_sub_one_of_pos (div_pos hlogap1_pos hloga_pos)
      have h2 : log ((a + 1 : ℕ) : ℝ) / log (a : ℝ) - 1 =
          (log ((a + 1 : ℕ) : ℝ) - log (a : ℝ)) / log (a : ℝ) := by
        field_simp [hloga_pos.ne']
      rw [h2] at h1
      exact le_trans h1 (div_le_div_of_nonneg_right hlog_step_a hloga_pos.le)
  have hbd_a : 0 ≤ 1 - log (a : ℝ) / log ((a + 1 : ℕ) : ℝ) ∧
      1 - log (a : ℝ) / log ((a + 1 : ℕ) : ℝ) ≤ 1 / log (a : ℝ) := by
    have hle : log (a : ℝ) ≤ log ((a + 1 : ℕ) : ℝ) :=
      log_le_log ha_pos (by exact_mod_cast (by omega : a ≤ a + 1))
    constructor
    · rw [sub_nonneg, div_le_one hlogap1_pos]; exact hle
    · have h1 : 1 - log (a : ℝ) / log ((a + 1 : ℕ) : ℝ) =
          (log ((a + 1 : ℕ) : ℝ) - log (a : ℝ)) / log ((a + 1 : ℕ) : ℝ) := by
        field_simp [hlogap1_pos.ne']
      rw [h1]
      calc (log ((a + 1 : ℕ) : ℝ) - log (a : ℝ)) / log ((a + 1 : ℕ) : ℝ)
          ≤ 1 / log ((a + 1 : ℕ) : ℝ) := div_le_div_of_nonneg_right hlog_step_a hlogap1_pos.le
        _ ≤ 1 / log (a : ℝ) := one_div_le_one_div_of_le hloga_pos hle
  -- Combine all terms cleanly!
  have hlog_div : log (log (b : ℝ) / log (a : ℝ)) =
      log (log (b : ℝ)) - log (log (a : ℝ)) :=
    log_div hlogb_pos.ne' hloga_pos.ne'
  rw [hsum_eq, habel, hlog_div]
  have hdecomp :
      A b / log (b : ℝ) - A a / log ((a + 1 : ℕ) : ℝ) +
        (∑ n ∈ Icc (a + 1) (b - 1), A n * (1 / log (n : ℝ) - 1 / log ((n + 1 : ℕ) : ℝ))) -
        (log (log (b : ℝ)) - log (log (a : ℝ))) =
      (R b / log (b : ℝ) - R a / log ((a + 1 : ℕ) : ℝ) +
        ∑ n ∈ Icc (a + 1) (b - 1), R n * (1 / log (n : ℝ) - 1 / log ((n + 1 : ℕ) : ℝ))) +
      ((1 - log (a : ℝ) / log ((a + 1 : ℕ) : ℝ)) -
        (log (log ((a + 1 : ℕ) : ℝ)) - log (log (a : ℝ)))) +
      ∑ n ∈ Icc (a + 1) (b - 1),
        (log (n : ℝ) * (1 / log (n : ℝ) - 1 / log ((n + 1 : ℕ) : ℝ)) -
          (log (log ((n + 1 : ℕ) : ℝ)) - log (log (n : ℝ)))) := by
    have hsplit_sum : ∑ n ∈ Icc (a + 1) (b - 1), A n * (1 / log (n : ℝ) - 1 / log ((n + 1 : ℕ) : ℝ)) =
        (∑ n ∈ Icc (a + 1) (b - 1), log (n : ℝ) * (1 / log (n : ℝ) - 1 / log ((n + 1 : ℕ) : ℝ))) +
        (∑ n ∈ Icc (a + 1) (b - 1), R n * (1 / log (n : ℝ) - 1 / log ((n + 1 : ℕ) : ℝ))) := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun n _ => ?_
      rw [hA_eq n]; ring
    rw [hsplit_sum, sum_sub_distrib, htel_ll, hA_eq b, hA_eq a]
    have hbb : (log (b : ℝ) + R b) / log (b : ℝ) = 1 + R b / log (b : ℝ) := by
      field_simp [hlogb_pos.ne']
    have haa : (log (a : ℝ) + R a) / log ((a + 1 : ℕ) : ℝ) =
        log (a : ℝ) / log ((a + 1 : ℕ) : ℝ) + R a / log ((a + 1 : ℕ) : ℝ) := by
      ring
    rw [hbb, haa]; ring
  rw [hdecomp]
  have hinv_le : 1 / log (b : ℝ) ≤ 1 / log (a : ℝ) :=
    one_div_le_one_div_of_le hloga_pos (log_le_log ha_pos (by exact_mod_cast hab))
  have hinv_ap1_le : 1 / log ((a + 1 : ℕ) : ℝ) ≤ 1 / log (a : ℝ) :=
    one_div_le_one_div_of_le hloga_pos (log_le_log ha_pos (by exact_mod_cast (by omega : a ≤ a + 1)))
  have hR_sum : |∑ n ∈ Icc (a + 1) (b - 1),
      R n * (1 / log (n : ℝ) - 1 / log ((n + 1 : ℕ) : ℝ))| ≤
      52 / log (a : ℝ) := by
    calc _ ≤ ∑ n ∈ Icc (a + 1) (b - 1),
              |R n * (1 / log (n : ℝ) - 1 / log ((n + 1 : ℕ) : ℝ))| :=
            abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Icc (a + 1) (b - 1),
              52 * (1 / log (n : ℝ) - 1 / log ((n + 1 : ℕ) : ℝ)) := by
            refine sum_le_sum fun n hn => ?_
            rw [abs_mul, abs_of_nonneg (hstep_pos n hn)]
            exact mul_le_mul_of_nonneg_right (hR n (by have := (mem_Icc.mp hn).1; omega)) (hstep_pos n hn)
      _ = 52 * (1 / log ((a + 1 : ℕ) : ℝ) - 1 / log (b : ℝ)) := by
            rw [← mul_sum, htel_inv]
      _ ≤ 52 / log (a : ℝ) := by
            have : 0 ≤ 1 / log (b : ℝ) := by positivity
            linarith [show 52 * (1 / log ((a + 1 : ℕ) : ℝ)) ≤ 52 * (1 / log (a : ℝ)) by linarith,
                      show 52 * (1 / log (a : ℝ)) = 52 / log (a : ℝ) by ring]
  have hmain_sum : |∑ n ∈ Icc (a + 1) (b - 1),
      (log (n : ℝ) * (1 / log (n : ℝ) - 1 / log ((n + 1 : ℕ) : ℝ)) -
        (log (log ((n + 1 : ℕ) : ℝ)) - log (log (n : ℝ))))| ≤
      1 / log (a : ℝ) := by
    calc _ ≤ ∑ n ∈ Icc (a + 1) (b - 1),
              |log (n : ℝ) * (1 / log (n : ℝ) - 1 / log ((n + 1 : ℕ) : ℝ)) -
                (log (log ((n + 1 : ℕ) : ℝ)) - log (log (n : ℝ)))| :=
            abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Icc (a + 1) (b - 1),
              (1 / log (n : ℝ) - 1 / log ((n + 1 : ℕ) : ℝ)) :=
            sum_le_sum hterm_cmp
      _ = 1 / log ((a + 1 : ℕ) : ℝ) - 1 / log (b : ℝ) := htel_inv
      _ ≤ 1 / log (a : ℝ) := by
            have : 0 ≤ 1 / log (b : ℝ) := by positivity
            linarith
  have hRb : |R b / log (b : ℝ)| ≤ 52 / log (a : ℝ) := by
    rw [abs_div, abs_of_pos hlogb_pos]
    calc |R b| / log (b : ℝ) ≤ 52 / log (b : ℝ) :=
          div_le_div_of_nonneg_right (hR b (by omega)) hlogb_pos.le
      _ ≤ 52 / log (a : ℝ) := by
          have : 52 / log (b : ℝ) = 52 * (1 / log (b : ℝ)) := by ring
          have : 52 / log (a : ℝ) = 52 * (1 / log (a : ℝ)) := by ring
          linarith
  have hRa : |R a / log ((a + 1 : ℕ) : ℝ)| ≤ 52 / log (a : ℝ) := by
    rw [abs_div, abs_of_pos hlogap1_pos]
    calc |R a| / log ((a + 1 : ℕ) : ℝ) ≤ 52 / log ((a + 1 : ℕ) : ℝ) :=
          div_le_div_of_nonneg_right (hR a (by omega)) hlogap1_pos.le
      _ ≤ 52 / log (a : ℝ) := by
          have : 52 / log ((a + 1 : ℕ) : ℝ) = 52 * (1 / log ((a + 1 : ℕ) : ℝ)) := by ring
          have : 52 / log (a : ℝ) = 52 * (1 / log (a : ℝ)) := by ring
          linarith
  have hmid : |(1 - log (a : ℝ) / log ((a + 1 : ℕ) : ℝ)) -
      (log (log ((a + 1 : ℕ) : ℝ)) - log (log (a : ℝ)))| ≤ 1 / log (a : ℝ) := by
    rw [abs_le]; constructor <;> linarith [hbd_a.1, hbd_a.2, hll_a.1, hll_a.2]
  have htri1 := abs_add_le
    ((R b / log (b : ℝ) - R a / log ((a + 1 : ℕ) : ℝ) +
      ∑ n ∈ Icc (a + 1) (b - 1), R n * (1 / log (n : ℝ) - 1 / log ((n + 1 : ℕ) : ℝ))) +
    ((1 - log (a : ℝ) / log ((a + 1 : ℕ) : ℝ)) -
      (log (log ((a + 1 : ℕ) : ℝ)) - log (log (a : ℝ)))))
    (∑ n ∈ Icc (a + 1) (b - 1),
      (log (n : ℝ) * (1 / log (n : ℝ) - 1 / log ((n + 1 : ℕ) : ℝ)) -
        (log (log ((n + 1 : ℕ) : ℝ)) - log (log (n : ℝ)))))
  have htri2 := abs_add_le
    (R b / log (b : ℝ) - R a / log ((a + 1 : ℕ) : ℝ) +
      ∑ n ∈ Icc (a + 1) (b - 1), R n * (1 / log (n : ℝ) - 1 / log ((n + 1 : ℕ) : ℝ)))
    ((1 - log (a : ℝ) / log ((a + 1 : ℕ) : ℝ)) -
      (log (log ((a + 1 : ℕ) : ℝ)) - log (log (a : ℝ))))
  have htri3 := abs_add_le
    (R b / log (b : ℝ) - R a / log ((a + 1 : ℕ) : ℝ))
    (∑ n ∈ Icc (a + 1) (b - 1), R n * (1 / log (n : ℝ) - 1 / log ((n + 1 : ℕ) : ℝ)))
  have htri4 := abs_sub (R b / log (b : ℝ)) (R a / log ((a + 1 : ℕ) : ℝ))
  have h160 : 52 / log (a : ℝ) + 52 / log (a : ℝ) + 52 / log (a : ℝ) +
      1 / log (a : ℝ) + 1 / log (a : ℝ) ≤ 160 / log (a : ℝ) := by
    have : 0 ≤ (log (a : ℝ))⁻¹ := by positivity
    ring_nf; linarith
  linarith

/-- Upper bound `∑_{p ≤ N} 1/p ≤ log (log N) + 400` for all `N ≥ 3`. -/
lemma sum_inv_primes_le (N : ℕ) (hN : 3 ≤ N) :
    ∑ p ∈ (Icc 1 N).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ≤ log (log (N : ℝ)) + 400 := by
  have hsplit : (Icc 1 N).filter Nat.Prime =
      insert 2 ((Ioc 2 N).filter Nat.Prime) := by
    ext p
    simp only [mem_filter, mem_Icc, mem_insert, mem_Ioc]
    constructor
    · rintro ⟨⟨hp1, hpN⟩, hp⟩
      rcases eq_or_lt_of_le hp.two_le with rfl | hgt
      · left; rfl
      · right; exact ⟨⟨hgt, hpN⟩, hp⟩
    · rintro (rfl | ⟨⟨hgt, hpN⟩, hp⟩)
      · exact ⟨⟨by omega, by omega⟩, Nat.prime_two⟩
      · exact ⟨⟨by omega, hpN⟩, hp⟩
  rw [hsplit, sum_insert (by simp)]
  have hm := mertens_second_Ioc_nat (a := 2) (b := N) le_rfl (by omega)
  rw [abs_le] at hm
  have hlog2_pos : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hlog2_ge : (1 : ℝ) / 2 ≤ log (2 : ℝ) := by
    have h := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < (1 : ℝ) / 2)
    rw [log_div (by norm_num) (by norm_num), log_one, zero_sub] at h
    linarith
  have hlog2_le : log (2 : ℝ) ≤ 1 := by
    have := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  have hlogN_pos : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < N))
  have hll2 : -log (log (2 : ℝ)) ≤ 1 := by
    have := log_le_sub_one_of_pos (div_pos one_pos hlog2_pos)
    rw [log_div one_ne_zero hlog2_pos.ne', log_one, zero_sub] at this
    have hinv : 1 / log (2 : ℝ) ≤ 2 := by rw [div_le_iff₀ hlog2_pos]; linarith
    linarith
  have hdiv160 : 160 / log (2 : ℝ) ≤ 320 := by
    rw [div_le_iff₀ hlog2_pos]; linarith
  have hlog_div : log (log (N : ℝ) / log (2 : ℝ)) =
      log (log (N : ℝ)) - log (log (2 : ℝ)) :=
    log_div hlogN_pos.ne' hlog2_pos.ne'
  push_cast at hm ⊢
  linarith [hm.2, hlog_div, hll2, hdiv160]

/-- Sum of `ω n` over `n < N` is bounded by `N * (log (log N) + 400)` for `N ≥ 3`. -/
lemma sum_omega_le (N : ℕ) (hN : 3 ≤ N) :
    ∑ n ∈ range N, (ω n : ℝ) ≤ (N : ℝ) * (log (log (N : ℝ)) + 400) := by
  have hω_eq : ∀ n ∈ range N, (ω n : ℝ) =
      ∑ p ∈ (Icc 1 N).filter Nat.Prime, if p ∣ n ∧ 0 < n then (1 : ℝ) else 0 := by
    intro n hn
    have hn_lt : n < N := mem_range.mp hn
    rcases Nat.eq_zero_or_pos n with rfl | hn_pos
    · simp
    · rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset]
      change (n.primeFactors.card : ℝ) = _
      rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
      congr 1; congr 1
      ext p
      simp only [Nat.mem_primeFactors, mem_filter, mem_Icc]
      constructor
      · rintro ⟨hp, hpn, -⟩
        exact ⟨⟨⟨hp.pos, le_trans (Nat.le_of_dvd hn_pos hpn) (le_of_lt hn_lt)⟩, hp⟩, hpn, hn_pos⟩
      · rintro ⟨⟨-, hp⟩, hpn, -⟩
        exact ⟨hp, hpn, hn_pos.ne'⟩
  calc ∑ n ∈ range N, (ω n : ℝ)
      = ∑ n ∈ range N, ∑ p ∈ (Icc 1 N).filter Nat.Prime,
          if p ∣ n ∧ 0 < n then (1 : ℝ) else 0 := sum_congr rfl hω_eq
    _ = ∑ p ∈ (Icc 1 N).filter Nat.Prime, ∑ n ∈ range N,
          if p ∣ n ∧ 0 < n then (1 : ℝ) else 0 := sum_comm
    _ ≤ ∑ p ∈ (Icc 1 N).filter Nat.Prime, (N : ℝ) / (p : ℝ) := by
          refine sum_le_sum fun p hp => ?_
          have hp_pos : 0 < p := (mem_filter.mp hp).2.pos
          rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
          have hsub : (range N).filter (fun n => p ∣ n ∧ 0 < n) ⊆
              (Icc 1 (N / p)).image (fun k => p * k) := by
            intro n hn
            simp only [mem_filter, mem_range, mem_image, mem_Icc] at hn ⊢
            obtain ⟨hnN, ⟨k, rfl⟩, hpos⟩ := hn
            refine ⟨k, ⟨?_, ?_⟩, rfl⟩
            · by_contra hk0; push Not at hk0; interval_cases k; simp at hpos
            · exact (Nat.le_div_iff_mul_le hp_pos).mpr (by rw [mul_comm]; omega)
          have hcard : ((range N).filter (fun n => p ∣ n ∧ 0 < n)).card ≤ N / p := by
            calc _ ≤ ((Icc 1 (N / p)).image (fun k => p * k)).card := card_le_card hsub
              _ ≤ (Icc 1 (N / p)).card := card_image_le
              _ = N / p := by rw [Nat.card_Icc]; exact Nat.add_sub_cancel (N / p) 1
          calc (((range N).filter (fun n => p ∣ n ∧ 0 < n)).card : ℝ)
              ≤ ((N / p : ℕ) : ℝ) := by exact_mod_cast hcard
            _ ≤ (N : ℝ) / (p : ℝ) := by
                rw [le_div_iff₀ (by positivity)]
                exact_mod_cast Nat.div_mul_le_self N p
    _ = (N : ℝ) * ∑ p ∈ (Icc 1 N).filter Nat.Prime, (1 : ℝ) / (p : ℝ) := by
          rw [mul_sum]; refine sum_congr rfl fun p _ => by ring
    _ ≤ (N : ℝ) * (log (log (N : ℝ)) + 400) :=
          mul_le_mul_of_nonneg_left (sum_inv_primes_le N hN) (Nat.cast_nonneg N)

/-- Bound on `∑_{p ≤ Y} log p / (p - 1) ≤ 2 * log Y + 120` for `Y ≥ 1`. -/
lemma sum_prime_log_div_sub_one (Y : ℕ) (hY : 1 ≤ Y) :
    ∑ p ∈ (Icc 1 Y).filter Nat.Prime, log (p : ℝ) / ((p : ℝ) - 1) ≤
      2 * log (Y : ℝ) + 120 := by
  have h1 : ∑ p ∈ (Icc 1 Y).filter Nat.Prime, log (p : ℝ) / ((p : ℝ) - 1) ≤
      2 * ∑ p ∈ (Icc 1 Y).filter Nat.Prime, log (p : ℝ) / (p : ℝ) := by
    rw [mul_sum]
    refine sum_le_sum fun p hp => ?_
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (mem_filter.mp hp).2.two_le
    have hlog_nn : 0 ≤ log (p : ℝ) := log_nonneg (by linarith)
    have hsub_pos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
    rw [show 2 * (log (p : ℝ) / (p : ℝ)) = log (p : ℝ) * (2 / (p : ℝ)) by ring,
        show log (p : ℝ) / ((p : ℝ) - 1) = log (p : ℝ) * (1 / ((p : ℝ) - 1)) by ring]
    refine mul_le_mul_of_nonneg_left ?_ hlog_nn
    rw [div_le_div_iff₀ hsub_pos hp_pos]
    linarith
  have hm := mertens_first_nat Y hY
  rw [abs_le] at hm
  linarith [h1, hm.2]

/- ## Section 3: Finite-Degree Bonferroni (Truncated Inclusion-Exclusion) -/

/-- Exact alternating binomial partial sum:
for `r ≥ 1`, `∑_{k=0}^m (-1)^k * C(r, k) = (-1)^m * C(r - 1, m)`. -/
private lemma alt_sum_choose (r m : ℕ) (hr : 1 ≤ r) :
    ∑ k ∈ range (m + 1), ((-1 : ℝ) ^ k * (Nat.choose r k : ℝ)) =
      (-1 : ℝ) ^ m * (Nat.choose (r - 1) m : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih]
    have hpascal : Nat.choose r (m + 1) = Nat.choose (r - 1) m + Nat.choose (r - 1) (m + 1) := by
      have : r = (r - 1) + 1 := by omega
      conv_lhs => rw [this]
      rw [Nat.choose_succ_succ, add_comm]
    rw [hpascal, Nat.cast_add, pow_succ]
    ring

/-- Bonferroni upper and lower bounds for the indicator of `r = 0`:
for any `d₀ : ℕ` and `r : ℕ`,
`∑_{k=0}^{2*d₀+1} (-1)^k C(r, k) ≤ (if r = 0 then 1 else 0) ≤ ∑_{k=0}^{2*d₀} (-1)^k C(r, k)`. -/
lemma bonferroni_indicator (r d₀ : ℕ) :
    ∑ k ∈ range (2 * d₀ + 2), ((-1 : ℝ) ^ k * (Nat.choose r k : ℝ)) ≤
      (if r = 0 then (1 : ℝ) else 0) ∧
    (if r = 0 then (1 : ℝ) else 0) ≤
      ∑ k ∈ range (2 * d₀ + 1), ((-1 : ℝ) ^ k * (Nat.choose r k : ℝ)) := by
  rcases eq_or_ne r 0 with rfl | hr0
  · constructor
    · rw [sum_eq_single 0]
      · simp
      · intro k _ hk; simp [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hk)]
      · simp
    · rw [sum_eq_single 0]
      · simp
      · intro k _ hk; simp [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hk)]
      · simp
  · have hr1 : 1 ≤ r := Nat.pos_of_ne_zero hr0
    simp only [if_neg hr0]
    constructor
    · rw [alt_sum_choose r (2 * d₀ + 1) hr1]
      have hpow : (-1 : ℝ) ^ (2 * d₀ + 1) = -1 := by
        rw [pow_succ, pow_mul]; norm_num
      rw [hpow]
      have : (0 : ℝ) ≤ (Nat.choose (r - 1) (2 * d₀ + 1) : ℝ) := Nat.cast_nonneg _
      linarith
    · rw [alt_sum_choose r (2 * d₀) hr1]
      have hpow : (-1 : ℝ) ^ (2 * d₀) = 1 := by rw [pow_mul]; norm_num
      rw [hpow, one_mul]
      exact Nat.cast_nonneg _

/-- Elementary upper bound on the `k`-th elementary symmetric sum of `f` over a finset `S`:
`∑_{A ∈ powersetCard k S} ∏ p ∈ A, f p ≤ (∑ p ∈ S, f p)^k / k!` for `f ≥ 0`. -/
lemma sum_powersetCard_prod_le {α : Type*} [DecidableEq α] (S : Finset α) (f : α → ℝ)
    (hf : ∀ x ∈ S, 0 ≤ f x) (k : ℕ) :
    ∑ A ∈ S.powersetCard k, (∏ x ∈ A, f x) ≤ (∑ x ∈ S, f x) ^ k / (Nat.factorial k : ℝ) := by
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < (Nat.factorial k : ℝ))]
  -- Prove `k! * ∑_{A ∈ powersetCard k S} ∏ x ∈ A, f x ≤ (∑ x ∈ S, f x)^k` by induction on `k`.
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep : ((k + 1 : ℕ) : ℝ) * ∑ A ∈ S.powersetCard (k + 1), (∏ x ∈ A, f x) ≤
        (∑ x ∈ S, f x) * ∑ B ∈ S.powersetCard k, (∏ x ∈ B, f x) := by
      -- Double count pairs `(x, B)` with `x ∈ S \ B`, `B ∈ powersetCard k S`, forming `A = insert x B`:
      have h1 : ((k + 1 : ℕ) : ℝ) * ∑ A ∈ S.powersetCard (k + 1), (∏ x ∈ A, f x) =
          ∑ A ∈ S.powersetCard (k + 1), ∑ x ∈ A, f x * ∏ y ∈ A.erase x, f y := by
        rw [mul_sum]
        refine sum_congr rfl fun A hA => ?_
        have hcard : A.card = k + 1 := (mem_powersetCard.mp hA).2
        have hterm : ∀ x ∈ A, f x * ∏ y ∈ A.erase x, f y = ∏ y ∈ A, f y := fun x hx =>
          mul_prod_erase A f hx
        rw [sum_congr rfl hterm, sum_const, hcard, nsmul_eq_mul]
      rw [h1, sum_mul]
      have h2 : ∑ A ∈ S.powersetCard (k + 1), ∑ x ∈ A, f x * ∏ y ∈ A.erase x, f y =
          ∑ x ∈ S, f x * ∑ B ∈ (S.erase x).powersetCard k, (∏ y ∈ B, f y) := by
        -- Reindex `(A, x)` with `x ∈ A ⊆ S, |A|=k+1` to `(x, B)` with `x ∈ S, B ⊆ S.erase x, |B|=k`.
        trans ∑ p ∈ (S.powersetCard (k + 1)).sigma (fun A => A), f p.2 * ∏ y ∈ p.1.erase p.2, f y
        · rw [sum_sigma]
        trans ∑ p ∈ S.sigma (fun x => (S.erase x).powersetCard k), f p.1 * ∏ y ∈ p.2, f y
        · refine sum_nbij (fun p => ⟨p.2, p.1.erase p.2⟩) ?_ ?_ ?_ ?_
          · intro ⟨A, x⟩ hp
            simp only [mem_sigma, mem_powersetCard] at hp ⊢
            refine ⟨hp.1.1 hp.2, ?_, ?_⟩
            · intro y hy
              rw [mem_erase] at hy ⊢
              exact ⟨hy.1, hp.1.1 hy.2⟩
            · rw [card_erase_of_mem hp.2, hp.1.2]; omega
          · intro ⟨A₁, x₁⟩ hp₁ ⟨A₂, x₂⟩ hp₂ heq
            simp only [mem_coe, mem_sigma, mem_powersetCard] at hp₁ hp₂
            simp only [Sigma.mk.inj_iff] at heq
            obtain ⟨rfl, hB⟩ := heq
            have hB' : A₁.erase x₁ = A₂.erase x₁ := eq_of_heq hB
            have hA : A₁ = A₂ := by
              rw [← insert_erase hp₁.2, hB', insert_erase hp₂.2]
            subst hA; rfl
          · intro ⟨x, B⟩ hp
            simp only [mem_coe, mem_sigma, mem_powersetCard] at hp
            have hxB : x ∉ B := fun hx => (mem_erase.mp (hp.2.1 hx)).1 rfl
            refine ⟨⟨insert x B, x⟩, ?_, ?_⟩
            · simp only [mem_coe, mem_sigma, mem_powersetCard, mem_insert, true_or, and_true]
              refine ⟨?_, ?_⟩
              · intro y hy
                rcases mem_insert.mp hy with rfl | hyB
                · exact hp.1
                · exact (mem_erase.mp (hp.2.1 hyB)).2
              · rw [card_insert_of_notMem hxB, hp.2.2]
            · simp [erase_insert hxB]
          · intro ⟨A, x⟩ _; rfl
        · rw [sum_sigma]
          refine sum_congr rfl fun x _ => ?_
          rw [mul_sum]
      rw [h2]
      refine sum_le_sum fun x hx => ?_
      refine mul_le_mul_of_nonneg_left ?_ (hf x hx)
      refine sum_le_sum_of_subset_of_nonneg ?_ fun B hB _ =>
        prod_nonneg fun y hy => hf y ((mem_powersetCard.mp hB).1 hy)
      intro B hB
      simp only [mem_powersetCard] at hB ⊢
      exact ⟨Subset.trans hB.1 (erase_subset x S), hB.2⟩
    have hfac : (Nat.factorial (k + 1) : ℝ) = ((k + 1 : ℕ) : ℝ) * (Nat.factorial k : ℝ) := by
      rw [Nat.factorial_succ, Nat.cast_mul]
    rw [hfac, pow_succ']
    calc (∑ A ∈ S.powersetCard (k + 1), (∏ x ∈ A, f x)) * (((k + 1 : ℕ) : ℝ) * (Nat.factorial k : ℝ))
        = (Nat.factorial k : ℝ) * (((k + 1 : ℕ) : ℝ) * ∑ A ∈ S.powersetCard (k + 1), (∏ x ∈ A, f x)) := by ring
      _ ≤ (Nat.factorial k : ℝ) * ((∑ x ∈ S, f x) * ∑ B ∈ S.powersetCard k, (∏ x ∈ B, f x)) :=
            mul_le_mul_of_nonneg_left hstep (Nat.cast_nonneg _)
      _ = (∑ x ∈ S, f x) * ((∑ B ∈ S.powersetCard k, (∏ x ∈ B, f x)) * (Nat.factorial k : ℝ)) := by ring
      _ ≤ (∑ x ∈ S, f x) * (∑ x ∈ S, f x) ^ k :=
            mul_le_mul_of_nonneg_left ih (sum_nonneg hf)

/-- Product expansion `∏_{x ∈ S} (1 - f x) = ∑_{k=0}^{|S|} (-1)^k ∑_{A ∈ powersetCard k S} ∏_{x ∈ A} f x`. -/
lemma prod_one_sub_eq_sum_powersetCard {α : Type*} [DecidableEq α] (S : Finset α) (f : α → ℝ) :
    ∏ x ∈ S, (1 - f x) =
      ∑ k ∈ range (S.card + 1), (-1 : ℝ) ^ k * ∑ A ∈ S.powersetCard k, (∏ x ∈ A, f x) := by
  have h1 : ∏ x ∈ S, (1 - f x) = ∑ A ∈ S.powerset, (-1 : ℝ) ^ A.card * (∏ x ∈ A, f x) := by
    have hsub : ∀ x, (1 - f x) = (-f x) + 1 := fun x => by ring
    simp_rw [hsub, prod_add]
    refine sum_congr rfl fun A _ => ?_
    simp only [prod_const_one, mul_one, prod_neg]
  rw [h1]
  -- Group `S.powerset` by cardinality `k ∈ range (S.card + 1)`.
  have hbi : S.powerset = (range (S.card + 1)).biUnion (fun k => S.powersetCard k) := by
    ext A
    simp only [mem_powerset, mem_biUnion, mem_range, mem_powersetCard]
    constructor
    · intro hA
      exact ⟨A.card, Nat.lt_succ_of_le (card_le_card hA), hA, rfl⟩
    · rintro ⟨_, _, hA, _⟩; exact hA
  have hdisj : Set.PairwiseDisjoint (range (S.card + 1) : Set ℕ) (fun k => S.powersetCard k) := by
    intro a _ b _ hab
    change Disjoint _ _
    rw [disjoint_left]
    intro A hAa hAb
    exact hab ((mem_powersetCard.mp hAa).2.symm.trans (mem_powersetCard.mp hAb).2)
  rw [hbi, sum_biUnion hdisj]
  refine sum_congr rfl fun k _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun A hA => ?_
  rw [(mem_powersetCard.mp hA).2]

/-- Truncated Bonferroni error bound for counting integers `m ∈ Icc 1 M` coprime to all primes in `S`. -/
lemma coprime_count_bonferroni (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (M d₀ : ℕ) :
    let Lsum : ℝ := ∑ p ∈ S, (1 : ℝ) / (p : ℝ)
    |(((Icc 1 M).filter (fun m => ∀ p ∈ S, ¬p ∣ m)).card : ℝ) -
      (M : ℝ) * ∏ p ∈ S, (1 - (1 : ℝ) / (p : ℝ))| ≤
    (M : ℝ) * (∑ k ∈ Icc (2 * d₀ + 1) S.card, Lsum ^ k / (Nat.factorial k : ℝ)) +
      ∑ k ∈ range (2 * d₀ + 2), (S.card : ℝ) ^ k := by
  intro Lsum
  have hdvd_iff : ∀ m : ℕ, ∀ A ∈ S.powerset, (∏ p ∈ A, p) ∣ m ↔ ∀ p ∈ A, p ∣ m := by
    intro m A hA
    have hAp : ∀ p ∈ A, p.Prime := fun p hp => hS p (mem_powerset.mp hA hp)
    induction A using Finset.induction_on with
    | empty => simp
    | insert a B ha ih =>
      rw [prod_insert ha]
      have haP : a.Prime := hAp a (mem_insert_self a B)
      have hBp : ∀ p ∈ B, p.Prime := fun p hp => hAp p (mem_insert_of_mem hp)
      have hcop : Nat.Coprime a (∏ p ∈ B, p) := by
        refine Nat.Coprime.prod_right fun p hp => ?_
        have hne : a ≠ p := fun h => ha (h ▸ hp)
        exact (Nat.coprime_primes haP (hBp p hp)).mpr hne
      have hsubB : B ∈ S.powerset := mem_powerset.mpr
        (Subset.trans (subset_insert a B) (mem_powerset.mp hA))
      constructor
      · intro h
        intro p hp
        rcases mem_insert.mp hp with rfl | hpB
        · exact dvd_trans (dvd_mul_right p _) h
        · exact (ih hsubB hBp).mp (dvd_trans (dvd_mul_left _ a) h) p hpB
      · intro hall
        exact hcop.mul_dvd_of_dvd_of_dvd (hall a (mem_insert_self a B))
          ((ih hsubB hBp).mpr fun p hp => hall p (mem_insert_of_mem hp))
  have hdvd_count : ∀ A ∈ S.powerset,
      (((Icc 1 M).filter (fun m => ∀ p ∈ A, p ∣ m)).card : ℝ) = ((M / ∏ p ∈ A, p : ℕ) : ℝ) := by
    intro A hA
    have hprod_pos : 0 < ∏ p ∈ A, p :=
      prod_pos fun p hp => (hS p (mem_powerset.mp hA hp)).pos
    have hfilt : (Icc 1 M).filter (fun m => ∀ p ∈ A, p ∣ m) =
        (Icc 1 (M / ∏ p ∈ A, p)).image (fun k => (∏ p ∈ A, p) * k) := by
      ext m
      simp only [mem_filter, mem_Icc, mem_image]
      constructor
      · rintro ⟨⟨hm1, hmM⟩, hall⟩
        have hdvd : (∏ p ∈ A, p) ∣ m := (hdvd_iff m A hA).mpr hall
        obtain ⟨k, rfl⟩ := hdvd
        refine ⟨k, ⟨?_, ?_⟩, rfl⟩
        · by_contra hk0; push Not at hk0; interval_cases k; simp at hm1
        · exact (Nat.le_div_iff_mul_le hprod_pos).mpr (by rw [mul_comm]; exact hmM)
      · rintro ⟨k, ⟨hk1, hkdiv⟩, rfl⟩
        refine ⟨⟨Nat.mul_pos hprod_pos hk1, by rw [mul_comm]; exact (Nat.le_div_iff_mul_le hprod_pos).mp hkdiv⟩, ?_⟩
        exact (hdvd_iff _ A hA).mp (dvd_mul_right _ k)
    rw [hfilt, card_image_of_injective _ (mul_right_injective₀ hprod_pos.ne'), Nat.card_Icc,
        Nat.add_sub_cancel]
  -- Exact sum over `m ∈ Icc 1 M` of `∑_{k < K} (-1)^k C(r(m), k)`:
  have hbonf_sum : ∀ K : ℕ,
      ∑ m ∈ Icc 1 M, ∑ k ∈ range K, ((-1 : ℝ) ^ k * (Nat.choose (S.filter (· ∣ m)).card k : ℝ)) =
      ∑ k ∈ range K, (-1 : ℝ) ^ k * ∑ A ∈ S.powersetCard k, ((M / ∏ p ∈ A, p : ℕ) : ℝ) := by
    intro K
    rw [sum_comm]
    refine sum_congr rfl fun k _ => ?_
    rw [← mul_sum]
    congr 1
    have hch : ∀ m ∈ Icc 1 M, (Nat.choose (S.filter (· ∣ m)).card k : ℝ) =
        ∑ A ∈ S.powersetCard k, if ∀ p ∈ A, p ∣ m then (1 : ℝ) else 0 := by
      intro m _
      rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
      congr 1
      rw [← card_powersetCard]
      congr 1
      ext A
      simp only [mem_powersetCard, mem_filter, subset_iff]
      constructor
      · rintro ⟨hA, hcard⟩
        exact ⟨⟨fun p hp => (hA hp).1, hcard⟩, fun p hp => (hA hp).2⟩
      · rintro ⟨⟨hA, hcard⟩, hall⟩
        exact ⟨fun p hp => ⟨hA hp, hall p hp⟩, hcard⟩
    rw [sum_congr rfl hch, sum_comm]
    refine sum_congr rfl fun A hA => ?_
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
    exact hdvd_count A (mem_powerset.mpr (mem_powersetCard.mp hA).1)
  -- Floor vs real difference for any `K ≤ 2 * d₀ + 2`:
  have hfloor_err : ∀ K : ℕ, K ≤ 2 * d₀ + 2 →
      |(∑ k ∈ range K, (-1 : ℝ) ^ k * ∑ A ∈ S.powersetCard k, ((M / ∏ p ∈ A, p : ℕ) : ℝ)) -
        (M : ℝ) * ∑ k ∈ range K, (-1 : ℝ) ^ k * ∑ A ∈ S.powersetCard k, (∏ p ∈ A, (1 : ℝ) / (p : ℝ))| ≤
      ∑ k ∈ range (2 * d₀ + 2), (S.card : ℝ) ^ k := by
    intro K hK
    rw [mul_sum, ← sum_sub_distrib]
    calc _ ≤ ∑ k ∈ range K,
              |(-1 : ℝ) ^ k * ∑ A ∈ S.powersetCard k, ((M / ∏ p ∈ A, p : ℕ) : ℝ) -
                (M : ℝ) * ((-1 : ℝ) ^ k * ∑ A ∈ S.powersetCard k, (∏ p ∈ A, (1 : ℝ) / (p : ℝ)))| :=
            abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ range K, (S.card : ℝ) ^ k := by
            refine sum_le_sum fun k _ => ?_
            have hfac : (-1 : ℝ) ^ k * ∑ A ∈ S.powersetCard k, ((M / ∏ p ∈ A, p : ℕ) : ℝ) -
                (M : ℝ) * ((-1 : ℝ) ^ k * ∑ A ∈ S.powersetCard k, (∏ p ∈ A, (1 : ℝ) / (p : ℝ))) =
                (-1 : ℝ) ^ k * ∑ A ∈ S.powersetCard k,
                  (((M / ∏ p ∈ A, p : ℕ) : ℝ) - (M : ℝ) * (∏ p ∈ A, (1 : ℝ) / (p : ℝ))) := by
              rw [sum_sub_distrib, ← mul_sum]; ring
            rw [hfac, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
            calc _ ≤ ∑ A ∈ S.powersetCard k,
                      |((M / ∏ p ∈ A, p : ℕ) : ℝ) - (M : ℝ) * (∏ p ∈ A, (1 : ℝ) / (p : ℝ))| :=
                    abs_sum_le_sum_abs _ _
              _ ≤ ∑ _A ∈ S.powersetCard k, (1 : ℝ) := by
                    refine sum_le_sum fun A hA => ?_
                    have hprod_pos : 0 < ∏ p ∈ A, p :=
                      prod_pos fun p hp => (hS p ((mem_powersetCard.mp hA).1 hp)).pos
                    have hprod_eq : (∏ p ∈ A, (1 : ℝ) / (p : ℝ)) = 1 / ((∏ p ∈ A, p : ℕ) : ℝ) := by
                      rw [prod_div_distrib, prod_const_one, Nat.cast_prod]
                    rw [hprod_eq, mul_one_div, abs_le]
                    have hposR : (0 : ℝ) < ((∏ p ∈ A, p : ℕ) : ℝ) := by exact_mod_cast hprod_pos
                    constructor
                    · have h1 : M < (M / ∏ p ∈ A, p + 1) * (∏ p ∈ A, p) := by
                        have := Nat.div_add_mod M (∏ p ∈ A, p)
                        have := Nat.mod_lt M hprod_pos
                        nlinarith
                      have h2 : (M : ℝ) < (((M / ∏ p ∈ A, p : ℕ) : ℝ) + 1) * ((∏ p ∈ A, p : ℕ) : ℝ) := by
                        exact_mod_cast h1
                      have h3 : (M : ℝ) / ((∏ p ∈ A, p : ℕ) : ℝ) < ((M / ∏ p ∈ A, p : ℕ) : ℝ) + 1 :=
                        (div_lt_iff₀ hposR).mpr h2
                      linarith
                    · have h1 : ((M / ∏ p ∈ A, p : ℕ) : ℝ) ≤ (M : ℝ) / ((∏ p ∈ A, p : ℕ) : ℝ) := by
                        rw [le_div_iff₀ hposR]
                        exact_mod_cast Nat.div_mul_le_self M (∏ p ∈ A, p)
                      linarith
              _ = ((S.powersetCard k).card : ℝ) := by simp
              _ ≤ (S.card : ℝ) ^ k := by
                    rw [card_powersetCard]
                    have hfac1 : (1 : ℝ) ≤ (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
                    exact le_trans (Nat.choose_le_pow_div k S.card) (div_le_self (by positivity) hfac1)
      _ ≤ ∑ k ∈ range (2 * d₀ + 2), (S.card : ℝ) ^ k :=
            sum_le_sum_of_subset_of_nonneg (range_mono hK) fun _ _ _ => by positivity
  -- Tail error between `∏_{p ∈ S} (1 - 1/p)` and `∑_{k < K} (-1)^k ∑_{A ∈ powersetCard k S} ∏ 1/p`:
  have htail_err : ∀ K : ℕ, 2 * d₀ + 1 ≤ K →
      |(∑ k ∈ range K, (-1 : ℝ) ^ k * ∑ A ∈ S.powersetCard k, (∏ p ∈ A, (1 : ℝ) / (p : ℝ))) -
        ∏ p ∈ S, (1 - (1 : ℝ) / (p : ℝ))| ≤
      ∑ k ∈ Icc (2 * d₀ + 1) S.card, Lsum ^ k / (Nat.factorial k : ℝ) := by
    intro K hK
    rw [prod_one_sub_eq_sum_powersetCard]
    have hzero : ∀ k, S.card < k →
        (-1 : ℝ) ^ k * ∑ A ∈ S.powersetCard k, (∏ p ∈ A, (1 : ℝ) / (p : ℝ)) = 0 := by
      intro k hk
      rw [powersetCard_eq_empty.mpr hk, sum_empty, mul_zero]
    have hdiff_eq :
        (∑ k ∈ range K, (-1 : ℝ) ^ k * ∑ A ∈ S.powersetCard k, (∏ p ∈ A, (1 : ℝ) / (p : ℝ))) -
        (∑ k ∈ range (S.card + 1), (-1 : ℝ) ^ k * ∑ A ∈ S.powersetCard k, (∏ p ∈ A, (1 : ℝ) / (p : ℝ))) =
        - ∑ k ∈ Icc K S.card, (-1 : ℝ) ^ k * ∑ A ∈ S.powersetCard k, (∏ p ∈ A, (1 : ℝ) / (p : ℝ)) := by
      by_cases hKS : K ≤ S.card + 1
      · have hsplit : range (S.card + 1) = range K ∪ Icc K S.card := by
          ext k; simp only [mem_range, mem_union, mem_Icc]; omega
        have hd : Disjoint (range K) (Icc K S.card) := by
          rw [disjoint_left]; intro k hk1 hk2
          simp only [mem_range, mem_Icc] at hk1 hk2; omega
        rw [hsplit, sum_union hd]; ring
      · push Not at hKS
        have hIcc : Icc K S.card = ∅ := by ext k; simp only [mem_Icc, notMem_empty, iff_false]; omega
        rw [hIcc, sum_empty, neg_zero]
        have hsplit : range K = range (S.card + 1) ∪ Icc (S.card + 1) (K - 1) := by
          ext k; simp only [mem_range, mem_union, mem_Icc]; omega
        have hd : Disjoint (range (S.card + 1)) (Icc (S.card + 1) (K - 1)) := by
          rw [disjoint_left]; intro k hk1 hk2
          simp only [mem_range, mem_Icc] at hk1 hk2; omega
        rw [hsplit, sum_union hd]
        have hsum0 : ∑ k ∈ Icc (S.card + 1) (K - 1),
            (-1 : ℝ) ^ k * ∑ A ∈ S.powersetCard k, (∏ p ∈ A, (1 : ℝ) / (p : ℝ)) = 0 :=
          sum_eq_zero fun k hk => hzero k (by have := (mem_Icc.mp hk).1; omega)
        rw [hsum0, add_zero, sub_self]
    rw [hdiff_eq, abs_neg]
    calc _ ≤ ∑ k ∈ Icc K S.card,
              |(-1 : ℝ) ^ k * ∑ A ∈ S.powersetCard k, (∏ p ∈ A, (1 : ℝ) / (p : ℝ))| :=
            abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Icc K S.card, Lsum ^ k / (Nat.factorial k : ℝ) := by
            refine sum_le_sum fun k _ => ?_
            rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
                abs_of_nonneg (sum_nonneg fun A _ => prod_nonneg fun p _ => by positivity)]
            exact sum_powersetCard_prod_le S (fun p => (1 : ℝ) / (p : ℝ)) (fun p _ => by positivity) k
      _ ≤ ∑ k ∈ Icc (2 * d₀ + 1) S.card, Lsum ^ k / (Nat.factorial k : ℝ) := by
            refine sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => ?_
            · intro k hk; simp only [mem_Icc] at hk ⊢; omega
            · have : 0 ≤ Lsum := sum_nonneg fun p _ => by positivity
              positivity
  -- Combine Bonferroni lower bound (`K = 2*d₀+2`) and upper bound (`K = 2*d₀+1`):
  have hcount_eq : (((Icc 1 M).filter (fun m => ∀ p ∈ S, ¬p ∣ m)).card : ℝ) =
      ∑ m ∈ Icc 1 M, if (S.filter (· ∣ m)).card = 0 then (1 : ℝ) else 0 := by
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
    congr 1; congr 1
    ext m
    simp only [mem_filter, card_eq_zero, filter_eq_empty_iff]
  have hlow_bonf : ∑ k ∈ range (2 * d₀ + 2), (-1 : ℝ) ^ k * ∑ A ∈ S.powersetCard k, ((M / ∏ p ∈ A, p : ℕ) : ℝ) ≤
      (((Icc 1 M).filter (fun m => ∀ p ∈ S, ¬p ∣ m)).card : ℝ) := by
    rw [hcount_eq, ← hbonf_sum]
    exact sum_le_sum fun m _ => (bonferroni_indicator (S.filter (· ∣ m)).card d₀).1
  have hhigh_bonf : (((Icc 1 M).filter (fun m => ∀ p ∈ S, ¬p ∣ m)).card : ℝ) ≤
      ∑ k ∈ range (2 * d₀ + 1), (-1 : ℝ) ^ k * ∑ A ∈ S.powersetCard k, ((M / ∏ p ∈ A, p : ℕ) : ℝ) := by
    rw [hcount_eq, ← hbonf_sum]
    exact sum_le_sum fun m _ => (bonferroni_indicator (S.filter (· ∣ m)).card d₀).2
  have hf1 := hfloor_err (2 * d₀ + 2) le_rfl
  have hf2 := hfloor_err (2 * d₀ + 1) (by omega)
  have ht1 := htail_err (2 * d₀ + 2) (by omega)
  have ht2 := htail_err (2 * d₀ + 1) le_rfl
  rw [abs_le] at hf1 hf2 ht1 ht2 ⊢
  have hMnn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  constructor
  · have hm1 := mul_le_mul_of_nonneg_left ht1.1 hMnn
    linarith [hlow_bonf, hf1.1, hm1]
  · have hm2 := mul_le_mul_of_nonneg_left ht2.2 hMnn
    linarith [hhigh_bonf, hf2.2, hm2]

/- ## Section 4: Finite Bernoulli Grid `Fin G → Bool` -/

/-- Independent `Bernoulli(p)` probability weight on `b : Fin G → Bool`. -/
def bernProb {G : ℕ} (p : ℝ) (b : Fin G → Bool) : ℝ :=
  ∏ r : Fin G, if b r then p else (1 - p)

/-- Active set of bins `{r : Fin G | b r = true}`. -/
def activeSet {G : ℕ} (b : Fin G → Bool) : Finset (Fin G) :=
  univ.filter fun r => b r = true

lemma bernProb_nonneg {G : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (b : Fin G → Bool) :
    0 ≤ bernProb p b :=
  prod_nonneg fun r _ => by split_ifs <;> linarith

/-- Master product-expectation identity on `Fin G → Bool`:
`∑ b, ∏ r, g r (b r) = ∏ r, (g r false + g r true)`. -/
lemma sum_prod_bool {G : ℕ} (g : Fin G → Bool → ℝ) :
    ∑ b : Fin G → Bool, (∏ r : Fin G, g r (b r)) =
      ∏ r : Fin G, (g r false + g r true) := by
  have h := Fintype.prod_sum (fun (r : Fin G) (c : Bool) => g r c)
  rw [← h]
  refine prod_congr rfl fun r _ => ?_
  rw [Fintype.sum_bool, add_comm]

/-- Product expectation of `∏ r ∈ activeSet b, f r` under `bernProb p`. -/
lemma sum_bernProb_mul_prod {G : ℕ} (p : ℝ) (f : Fin G → ℝ) :
    ∑ b : Fin G → Bool, bernProb p b * ∏ r ∈ activeSet b, f r =
      ∏ r : Fin G, (1 - p + p * f r) := by
  have hterm : ∀ b : Fin G → Bool,
      bernProb p b * ∏ r ∈ activeSet b, f r =
        ∏ r : Fin G, if b r then p * f r else (1 - p) := by
    intro b
    unfold bernProb
    have hprod : ∏ r ∈ activeSet b, f r = ∏ r : Fin G, if b r then f r else 1 := by
      rw [activeSet, prod_filter]
    rw [hprod, ← prod_mul_distrib]
    refine prod_congr rfl fun r _ => by cases b r <;> simp
  simp_rw [hterm]
  rw [sum_prod_bool (fun r c => if c then p * f r else (1 - p))]
  refine prod_congr rfl fun r _ => by simp

lemma sum_bernProb {G : ℕ} (p : ℝ) :
    ∑ b : Fin G → Bool, bernProb p b = 1 := by
  have h := sum_bernProb_mul_prod (G := G) p (fun _ => 1)
  simpa using h

/-- Expectation of a single coordinate indicator `b r = true`. -/
lemma sum_bernProb_indicator {G : ℕ} (p : ℝ) (r₀ : Fin G) :
    ∑ b : Fin G → Bool, bernProb p b * (if b r₀ then (1 : ℝ) else 0) = p := by
  have hterm : ∀ b : Fin G → Bool,
      bernProb p b * (if b r₀ then (1 : ℝ) else 0) =
        ∏ r : Fin G, if r = r₀ then (if b r then p else 0) else (if b r then p else 1 - p) := by
    intro b
    unfold bernProb
    have hsplit : ∏ r : Fin G, (if b r then p else 1 - p) =
        (if b r₀ then p else 1 - p) * ∏ r ∈ univ.erase r₀, (if b r then p else 1 - p) :=
      (mul_prod_erase univ _ (mem_univ r₀)).symm
    have hsplit2 : ∏ r : Fin G, (if r = r₀ then (if b r then p else 0) else (if b r then p else 1 - p)) =
        (if b r₀ then p else 0) * ∏ r ∈ univ.erase r₀, (if b r then p else 1 - p) := by
      rw [← mul_prod_erase univ _ (mem_univ r₀)]
      simp only [ite_true]
      congr 1
      refine prod_congr rfl fun r hr => ?_
      rw [if_neg (ne_of_mem_erase hr)]
    rw [hsplit, hsplit2]
    cases b r₀ <;> simp
  simp_rw [hterm]
  rw [sum_prod_bool (fun r c => if r = r₀ then (if c then p else 0) else (if c then p else 1 - p))]
  rw [prod_eq_single r₀]
  · simp
  · intro r _ hr; simp [hr]
  · intro h; exact absurd (mem_univ r₀) h

/-- Expectation of a pair of coordinate indicators `b r₁ ∧ b r₂` for `r₁ ≠ r₂`. -/
lemma sum_bernProb_indicator_pair {G : ℕ} (p : ℝ) {r₁ r₂ : Fin G} (hne : r₁ ≠ r₂) :
    ∑ b : Fin G → Bool, bernProb p b * ((if b r₁ then (1 : ℝ) else 0) * (if b r₂ then (1 : ℝ) else 0)) =
      p * p := by
  let g : Fin G → Bool → ℝ := fun r c =>
    if r = r₁ ∨ r = r₂ then (if c then p else 0) else (if c then p else 1 - p)
  have hterm : ∀ b : Fin G → Bool,
      bernProb p b * ((if b r₁ then (1 : ℝ) else 0) * (if b r₂ then (1 : ℝ) else 0)) =
        ∏ r : Fin G, g r (b r) := by
    intro b
    unfold bernProb
    have h1 := mul_prod_erase univ (fun r => if b r then p else 1 - p) (mem_univ r₁)
    have hr₂_mem : r₂ ∈ univ.erase r₁ := mem_erase.mpr ⟨hne.symm, mem_univ r₂⟩
    have h2 := mul_prod_erase (univ.erase r₁) (fun r => if b r then p else 1 - p) hr₂_mem
    have hg1 := mul_prod_erase univ (fun r => g r (b r)) (mem_univ r₁)
    have hg2 := mul_prod_erase (univ.erase r₁) (fun r => g r (b r)) hr₂_mem
    have hrest : ∏ r ∈ (univ.erase r₁).erase r₂, g r (b r) =
        ∏ r ∈ (univ.erase r₁).erase r₂, (if b r then p else 1 - p) := by
      refine prod_congr rfl fun r hr => ?_
      have hne2 : r ≠ r₂ := ne_of_mem_erase hr
      have hne1 : r ≠ r₁ := ne_of_mem_erase (mem_of_mem_erase hr)
      simp [g, hne1, hne2]
    rw [← h1, ← h2, ← hg1, ← hg2, hrest]
    simp only [g, true_or, or_true, ite_true]
    cases b r₁ <;> cases b r₂ <;> simp
  simp_rw [hterm]
  rw [sum_prod_bool g]
  have h1 := mul_prod_erase univ (fun r => g r false + g r true) (mem_univ r₁)
  have hr₂_mem : r₂ ∈ univ.erase r₁ := mem_erase.mpr ⟨hne.symm, mem_univ r₂⟩
  have h2 := mul_prod_erase (univ.erase r₁) (fun r => g r false + g r true) hr₂_mem
  have hrest : ∏ r ∈ (univ.erase r₁).erase r₂, (g r false + g r true) = 1 := by
    refine prod_eq_one fun r hr => ?_
    have hne2 : r ≠ r₂ := ne_of_mem_erase hr
    have hne1 : r ≠ r₁ := ne_of_mem_erase (mem_of_mem_erase hr)
    simp [g, hne1, hne2]
  rw [← h1, ← h2, hrest, mul_one]
  simp [g]

/-- Expectation of a linear sum `∑ r ∈ activeSet b ∩ A, w r`. -/
lemma sum_bernProb_linear {G : ℕ} (p : ℝ) (A : Finset (Fin G)) (w : Fin G → ℝ) :
    ∑ b : Fin G → Bool, bernProb p b * (∑ r ∈ activeSet b ∩ A, w r) =
      p * ∑ r ∈ A, w r := by
  have hrew : ∀ b : Fin G → Bool,
      bernProb p b * (∑ r ∈ activeSet b ∩ A, w r) =
        ∑ r ∈ A, w r * (bernProb p b * (if b r then (1 : ℝ) else 0)) := by
    intro b
    have h1 : ∑ r ∈ activeSet b ∩ A, w r = ∑ r ∈ A, if b r then w r else 0 := by
      have hinter : activeSet b ∩ A = A.filter (fun r => b r = true) := by
        ext r; simp [activeSet, and_comm]
      rw [hinter, sum_filter]
    rw [h1, mul_sum]
    refine sum_congr rfl fun r _ => by cases b r <;> simp [mul_comm, mul_left_comm]
  simp_rw [hrew]
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun r _ => ?_
  rw [← mul_sum, sum_bernProb_indicator, mul_comm]

/-- Mean of `(activeSet b ∩ A).card` under `bernProb p`. -/
lemma sum_bernProb_card_inter {G : ℕ} (p : ℝ) (A : Finset (Fin G)) :
    ∑ b : Fin G → Bool, bernProb p b * ((activeSet b ∩ A).card : ℝ) = p * (A.card : ℝ) := by
  have h := sum_bernProb_linear p A (fun _ => (1 : ℝ))
  simpa using h

/-- Variance of `(activeSet b ∩ A).card` under `bernProb p`. -/
lemma sum_bernProb_card_inter_var {G : ℕ} (p : ℝ) (A : Finset (Fin G)) :
    ∑ b : Fin G → Bool, bernProb p b * (((activeSet b ∩ A).card : ℝ) - p * (A.card : ℝ)) ^ 2 =
      p * (1 - p) * (A.card : ℝ) := by
  have hsq : ∑ b : Fin G → Bool, bernProb p b * ((activeSet b ∩ A).card : ℝ) ^ 2 =
      p * (A.card : ℝ) + p * p * ((A.card : ℝ) * (A.card : ℝ) - (A.card : ℝ)) := by
    have hcard_eq : ∀ b : Fin G → Bool,
        ((activeSet b ∩ A).card : ℝ) = ∑ r ∈ A, if b r then (1 : ℝ) else 0 := by
      intro b
      have hinter : activeSet b ∩ A = A.filter (fun r => b r = true) := by
        ext r; simp [activeSet, and_comm]
      rw [hinter, ← sum_filter, sum_const, nsmul_eq_mul, mul_one]
    have hexp : ∀ b : Fin G → Bool,
        bernProb p b * ((activeSet b ∩ A).card : ℝ) ^ 2 =
          ∑ r₁ ∈ A, ∑ r₂ ∈ A, bernProb p b * ((if b r₁ then (1 : ℝ) else 0) * (if b r₂ then (1 : ℝ) else 0)) := by
      intro b
      rw [hcard_eq b, sq, sum_mul_sum, mul_sum]
      refine sum_congr rfl fun r₁ _ => ?_
      rw [mul_sum]
    simp_rw [hexp]
    rw [sum_comm]
    have hinner : ∀ r₁ ∈ A,
        ∑ b : Fin G → Bool, ∑ r₂ ∈ A,
          bernProb p b * ((if b r₁ then (1 : ℝ) else 0) * (if b r₂ then (1 : ℝ) else 0)) =
        p + p * p * ((A.card : ℝ) - 1) := by
      intro r₁ hr₁
      rw [sum_comm]
      have hsplit : ∑ r₂ ∈ A, ∑ b : Fin G → Bool,
          bernProb p b * ((if b r₁ then (1 : ℝ) else 0) * (if b r₂ then (1 : ℝ) else 0)) =
          ∑ r₂ ∈ A, if r₂ = r₁ then p else p * p := by
        refine sum_congr rfl fun r₂ _ => ?_
        by_cases heq : r₂ = r₁
        · subst heq
          have h1 : ∀ b : Fin G → Bool,
              (if b r₂ then (1 : ℝ) else 0) * (if b r₂ then (1 : ℝ) else 0) = if b r₂ then (1 : ℝ) else 0 := by
            intro b; cases b r₂ <;> simp
          simp_rw [h1, sum_bernProb_indicator, ite_true]
        · rw [if_neg heq, sum_bernProb_indicator_pair p (Ne.symm heq)]
      rw [hsplit, ← add_sum_erase A _ hr₁, if_pos rfl]
      have herase : ∑ r₂ ∈ A.erase r₁, (if r₂ = r₁ then p else p * p) =
          ((A.erase r₁).card : ℝ) * (p * p) := by
        rw [sum_congr rfl fun r₂ hr₂ => if_neg (ne_of_mem_erase hr₂),
            sum_const, nsmul_eq_mul]
      rw [herase, card_erase_of_mem hr₁, Nat.cast_sub (card_pos.mpr ⟨r₁, hr₁⟩), Nat.cast_one]
      ring
    rw [sum_congr rfl hinner, sum_const, nsmul_eq_mul]
    ring
  have hexpand : ∑ b : Fin G → Bool, bernProb p b * (((activeSet b ∩ A).card : ℝ) - p * (A.card : ℝ)) ^ 2 =
      (∑ b : Fin G → Bool, bernProb p b * ((activeSet b ∩ A).card : ℝ) ^ 2) -
      2 * (p * (A.card : ℝ)) * (∑ b : Fin G → Bool, bernProb p b * ((activeSet b ∩ A).card : ℝ)) +
      (p * (A.card : ℝ)) ^ 2 * (∑ b : Fin G → Bool, bernProb p b) := by
    have h1 : ∀ b : Fin G → Bool,
        bernProb p b * (((activeSet b ∩ A).card : ℝ) - p * (A.card : ℝ)) ^ 2 =
          bernProb p b * ((activeSet b ∩ A).card : ℝ) ^ 2 -
          2 * (p * (A.card : ℝ)) * (bernProb p b * ((activeSet b ∩ A).card : ℝ)) +
          (p * (A.card : ℝ)) ^ 2 * bernProb p b := fun b => by ring
    simp_rw [h1, sum_add_distrib, sum_sub_distrib, ← mul_sum]
  rw [hexpand, hsq, sum_bernProb_card_inter, sum_bernProb]
  ring

/-- Key weighted-subset expectation for Section 6 (`W^*(b)`):
for any `K ⊆ T` and any `y : ℝ`,
`∑ b, bernProb p b * (if K ⊆ activeSet b then y ^ (activeSet b ∩ T).card else 0)
  = (p * y) ^ K.card * (1 - p + p * y) ^ (T \ K).card`. -/
lemma sum_bernProb_subset_pow {G : ℕ} (p y : ℝ) {K T : Finset (Fin G)} (hKT : K ⊆ T) :
    ∑ b : Fin G → Bool, bernProb p b *
        (if K ⊆ activeSet b then y ^ (activeSet b ∩ T).card else 0) =
      (p * y) ^ K.card * (1 - p + p * y) ^ (T \ K).card := by
  let g : Fin G → Bool → ℝ := fun r c =>
    if r ∈ K then (if c then p * y else 0)
    else if r ∈ T then (if c then p * y else 1 - p)
    else (if c then p else 1 - p)
  have hterm : ∀ b : Fin G → Bool,
      bernProb p b * (if K ⊆ activeSet b then y ^ (activeSet b ∩ T).card else 0) =
        ∏ r : Fin G, g r (b r) := by
    intro b
    by_cases hK : K ⊆ activeSet b
    · rw [if_pos hK]
      have hpow : y ^ (activeSet b ∩ T).card = ∏ r : Fin G, if r ∈ T ∧ b r = true then y else 1 := by
        rw [← prod_filter, prod_const]
        congr 1; congr 1
        ext r
        simp [activeSet, and_comm]
      unfold bernProb
      rw [hpow, ← prod_mul_distrib]
      refine prod_congr rfl fun r _ => ?_
      by_cases hrK : r ∈ K
      · have hbr : b r = true := (mem_filter.mp (hK hrK)).2
        have hrT : r ∈ T := hKT hrK
        simp [g, hrK, hrT, hbr]
      · by_cases hrT : r ∈ T
        · cases b r <;> simp [g, hrK, hrT]
        · cases b r <;> simp [g, hrK, hrT]
    · rw [if_neg hK, mul_zero]
      have hex : ∃ r ∈ K, b r = false := by
        by_contra hall
        push Not at hall
        apply hK
        intro r hrK
        rw [activeSet, mem_filter]
        refine ⟨mem_univ r, ?_⟩
        cases hbr : b r
        · exact absurd hbr (hall r hrK)
        · rfl
      obtain ⟨r₀, hr₀K, hbr₀⟩ := hex
      symm
      exact prod_eq_zero (mem_univ r₀) (by simp [g, hr₀K, hbr₀])
  simp_rw [hterm]
  rw [sum_prod_bool g]
  have hval : ∀ r : Fin G, g r false + g r true =
      if r ∈ K then p * y else if r ∈ T \ K then (1 - p + p * y) else 1 := by
    intro r
    by_cases hrK : r ∈ K
    · simp [g, hrK]
    · by_cases hrT : r ∈ T
      · have hrTK : r ∈ T \ K := mem_sdiff.mpr ⟨hrT, hrK⟩
        simp [g, hrK, hrT, hrTK]
      · have hrTK : r ∉ T \ K := fun h => hrT (mem_sdiff.mp h).1
        simp [g, hrK, hrT, hrTK]
  simp_rw [hval]
  have hpart : univ = K ∪ (T \ K) ∪ Tᶜ := by
    ext r; simp only [mem_univ, mem_union, mem_sdiff, mem_compl, true_iff]
    by_cases hrT : r ∈ T
    · left; by_cases hrK : r ∈ K <;> [left; right] <;> simp [hrT, hrK]
    · right; exact hrT
  have hd1 : Disjoint K (T \ K) := disjoint_sdiff
  have hd2 : Disjoint (K ∪ (T \ K)) Tᶜ := by
    rw [disjoint_left]
    intro r hr1 hr2
    rw [mem_compl] at hr2
    rcases mem_union.mp hr1 with hrK | hrTK
    · exact hr2 (hKT hrK)
    · exact hr2 (mem_sdiff.mp hrTK).1
  rw [hpart, prod_union hd2, prod_union hd1]
  have hP1 : ∏ r ∈ K, (if r ∈ K then p * y else if r ∈ T \ K then (1 - p + p * y) else 1) =
      (p * y) ^ K.card := by
    rw [prod_congr rfl fun r hr => if_pos hr, prod_const]
  have hP2 : ∏ r ∈ T \ K, (if r ∈ K then p * y else if r ∈ T \ K then (1 - p + p * y) else 1) =
      (1 - p + p * y) ^ (T \ K).card := by
    refine (prod_congr rfl fun r hr => ?_).trans (prod_const _)
    rw [if_neg (mem_sdiff.mp hr).2, if_pos hr]
  have hP3 : ∏ r ∈ Tᶜ, (if r ∈ K then p * y else if r ∈ T \ K then (1 - p + p * y) else 1) = 1 := by
    refine prod_eq_one fun r hr => ?_
    have hrT : r ∉ T := mem_compl.mp hr
    rw [if_neg (fun h => hrT (hKT h)), if_neg (fun h => hrT (mem_sdiff.mp h).1)]
  rw [hP1, hP2, hP3, mul_one]

/-- Independence factorization across a bipartition `S₂ᶜ ⊔ S₂` of `Fin G`. -/
lemma sum_bernProb_indep_split {G : ℕ} (p : ℝ) (S₂ : Finset (Fin G))
    (F H : (Fin G → Bool) → ℝ)
    (hF : ∀ b₁ b₂ : Fin G → Bool, (∀ r ∉ S₂, b₁ r = b₂ r) → F b₁ = F b₂)
    (hH : ∀ b₁ b₂ : Fin G → Bool, (∀ r ∈ S₂, b₁ r = b₂ r) → H b₁ = H b₂) :
    ∑ b : Fin G → Bool, bernProb p b * (F b * H b) =
      (∑ b : Fin G → Bool, bernProb p b * F b) * (∑ b : Fin G → Bool, bernProb p b * H b) := by
  let e : (Fin G → Bool) ≃ ({r : Fin G // r ∉ S₂} → Bool) × ({r : Fin G // r ∈ S₂} → Bool) :=
    { toFun := fun b => (fun r => b r.1, fun r => b r.1)
      invFun := fun fg r => if h : r ∈ S₂ then fg.2 ⟨r, h⟩ else fg.1 ⟨r, h⟩
      left_inv := fun b => by ext r; dsimp; split_ifs <;> rfl
      right_inv := fun ⟨f, g⟩ => by
        ext ⟨r, hr⟩
        · simp [hr]
        · simp [hr] }
  let w₁ : ({r : Fin G // r ∉ S₂} → Bool) → ℝ := fun f =>
    ∏ r : {r : Fin G // r ∉ S₂}, if f r then p else 1 - p
  let w₂ : ({r : Fin G // r ∈ S₂} → Bool) → ℝ := fun g =>
    ∏ r : {r : Fin G // r ∈ S₂}, if g r then p else 1 - p
  let F₁ : ({r : Fin G // r ∉ S₂} → Bool) → ℝ := fun f =>
    F (e.symm (f, fun _ => false))
  let H₂ : ({r : Fin G // r ∈ S₂} → Bool) → ℝ := fun g =>
    H (e.symm (fun _ => false, g))
  have hprob : ∀ fg, bernProb p (e.symm fg) = w₁ fg.1 * w₂ fg.2 := by
    rintro ⟨f, g⟩
    unfold bernProb w₁ w₂
    rw [← prod_filter_mul_prod_filter_not univ (fun r => r ∈ S₂)]
    rw [mul_comm]
    congr 1
    · symm
      refine prod_bij (fun r _ => (r : Fin G)) ?_ ?_ ?_ ?_
      · intro ⟨r, hr⟩ _; simp [hr]
      · intro ⟨r₁, _⟩ _ ⟨r₂, _⟩ _ h; exact Subtype.ext h
      · intro r hr; exact ⟨⟨r, (mem_filter.mp hr).2⟩, mem_univ _, rfl⟩
      · intro ⟨r, hr⟩ _; simp [e, hr]
    · symm
      refine prod_bij (fun r _ => (r : Fin G)) ?_ ?_ ?_ ?_
      · intro ⟨r, hr⟩ _; simp [hr]
      · intro ⟨r₁, _⟩ _ ⟨r₂, _⟩ _ h; exact Subtype.ext h
      · intro r hr; exact ⟨⟨r, (mem_filter.mp hr).2⟩, mem_univ _, rfl⟩
      · intro ⟨r, hr⟩ _; simp [e, hr]
  have hF_eq : ∀ fg, F (e.symm fg) = F₁ fg.1 := by
    rintro ⟨f, g⟩; exact hF _ _ fun r hr => by simp [e, hr]
  have hH_eq : ∀ fg, H (e.symm fg) = H₂ fg.2 := by
    rintro ⟨f, g⟩; exact hH _ _ fun r hr => by simp [e, hr]
  have hw₁_sum : ∑ f, w₁ f = 1 := by
    have := Fintype.prod_sum (fun (_ : {r : Fin G // r ∉ S₂}) (c : Bool) => if c then p else 1 - p)
    rw [← this]
    refine prod_eq_one fun _ _ => by rw [Fintype.sum_bool]; simp
  have hw₂_sum : ∑ g, w₂ g = 1 := by
    have := Fintype.prod_sum (fun (_ : {r : Fin G // r ∈ S₂}) (c : Bool) => if c then p else 1 - p)
    rw [← this]
    refine prod_eq_one fun _ _ => by rw [Fintype.sum_bool]; simp
  have hLHS : ∑ b : Fin G → Bool, bernProb p b * (F b * H b) =
      (∑ f, w₁ f * F₁ f) * (∑ g, w₂ g * H₂ g) := by
    rw [← e.symm.sum_comp, Fintype.sum_prod_type]
    simp_rw [hprob, hF_eq, hH_eq]
    rw [sum_mul_sum]
    refine sum_congr rfl fun f _ => sum_congr rfl fun g _ => by ring
  have hF_sum : ∑ b : Fin G → Bool, bernProb p b * F b = ∑ f, w₁ f * F₁ f := by
    rw [← e.symm.sum_comp, Fintype.sum_prod_type]
    simp_rw [hprob, hF_eq]
    have : ∀ f, ∑ g, w₁ f * w₂ g * F₁ f = (w₁ f * F₁ f) * ∑ g, w₂ g := fun f => by
      rw [mul_sum]; refine sum_congr rfl fun g _ => by ring
    simp_rw [this, hw₂_sum, mul_one]
  have hH_sum : ∑ b : Fin G → Bool, bernProb p b * H b = ∑ g, w₂ g * H₂ g := by
    rw [← e.symm.sum_comp, Fintype.sum_prod_type]
    simp_rw [hprob, hH_eq]
    rw [sum_comm]
    have : ∀ g, ∑ f, w₁ f * w₂ g * H₂ g = (w₂ g * H₂ g) * ∑ f, w₁ f := fun g => by
      rw [mul_sum]; refine sum_congr rfl fun f _ => by ring
    simp_rw [this, hw₁_sum, mul_one]
  rw [hLHS, hF_sum, hH_sum]

/- ## Section 5: Geometric Grid and Lower Bound on `E[1_typ * U]` -/

noncomputable def gridDelta (L : ℝ) (G : ℕ) : ℝ := log L / (G : ℝ)

noncomputable def gridP (L : ℝ) (G : ℕ) : ℝ := 1 - exp (-(gridDelta L G))

noncomputable def xLo (L : ℝ) (G : ℕ) (r : Fin G) : ℝ :=
  exp ((r.val : ℝ) * gridDelta L G)

noncomputable def xHi (L : ℝ) (G : ℕ) (r : Fin G) : ℝ :=
  exp (((r.val + 1 : ℕ) : ℝ) * gridDelta L G)

noncomputable def subSum {G : ℕ} (x : Fin G → ℝ) (A : Finset (Fin G)) : ℝ :=
  ∑ r ∈ A, x r

noncomputable def binsLe (L : ℝ) (G : ℕ) (u : ℝ) : Finset (Fin G) :=
  univ.filter fun r => xHi L G r ≤ u

lemma gridDelta_pos {L : ℝ} {G : ℕ} (hL : 1 < L) (hG : 0 < G) :
    0 < gridDelta L G :=
  div_pos (log_pos hL) (by positivity)

lemma gridP_bounds {L : ℝ} {G : ℕ} (hL : 1 < L) (hG : 0 < G) (hΔ : gridDelta L G ≤ 1) :
    gridDelta L G / 2 ≤ gridP L G ∧ gridP L G ≤ gridDelta L G ∧ 0 < gridP L G ∧ gridP L G < 1 := by
  set Δ := gridDelta L G
  have hΔpos : 0 < Δ := gridDelta_pos hL hG
  have h1 : 1 - Δ ≤ exp (-Δ) := by
    have := add_one_le_exp (-Δ); linarith
  have h2 : exp (-Δ) ≤ 1 / (1 + Δ) := by
    rw [exp_neg, one_div]
    exact inv_anti₀ (by positivity) (by linarith [add_one_le_exp Δ])
  have h3 : Δ / 2 ≤ 1 - 1 / (1 + Δ) := by
    have hpos : 0 < 1 + Δ := by linarith
    have hid : 1 - 1 / (1 + Δ) = Δ / (1 + Δ) := by field_simp [hpos.ne']; ring
    rw [hid]
    exact div_le_div_of_nonneg_left hΔpos.le hpos (by linarith)
  have hpos_exp : 0 < exp (-Δ) := exp_pos (-Δ)
  unfold gridP
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

lemma xHi_sub_xLo {L : ℝ} {G : ℕ} (r : Fin G) :
    xHi L G r - xLo L G r = gridP L G * xHi L G r := by
  unfold xHi xLo gridP
  have h1 : exp ((r.val : ℝ) * gridDelta L G) =
      exp (-(gridDelta L G)) * exp (((r.val + 1 : ℕ) : ℝ) * gridDelta L G) := by
    rw [← exp_add]
    congr 1; push_cast; ring
  rw [h1]; ring

lemma xHi_gt_one_and_le {L : ℝ} {G : ℕ} (hL : 1 < L) (hG : 0 < G) (r : Fin G) :
    1 < xHi L G r ∧ xHi L G r ≤ L := by
  have hΔ : 0 < gridDelta L G := gridDelta_pos hL hG
  constructor
  · unfold xHi
    rw [← exp_zero]
    exact exp_lt_exp.mpr (mul_pos (by positivity) hΔ)
  · unfold xHi
    have hle : ((r.val + 1 : ℕ) : ℝ) * gridDelta L G ≤ log L := by
      unfold gridDelta
      have hr : ((r.val + 1 : ℕ) : ℝ) ≤ (G : ℝ) := by exact_mod_cast r.isLt
      have hGpos : (0 : ℝ) < (G : ℝ) := by positivity
      calc ((r.val + 1 : ℕ) : ℝ) * (log L / (G : ℝ))
          ≤ (G : ℝ) * (log L / (G : ℝ)) := mul_le_mul_of_nonneg_right hr (div_nonneg (log_pos hL).le hGpos.le)
        _ = log L := mul_div_cancel₀ _ hGpos.ne'
    calc exp (((r.val + 1 : ℕ) : ℝ) * gridDelta L G)
        ≤ exp (log L) := exp_le_exp.mpr hle
      _ = L := exp_log (by linarith)

lemma xHi_nonneg {L : ℝ} {G : ℕ} (hL : 1 < L) (hG : 0 < G) (r : Fin G) :
    0 ≤ xHi L G r := by
  linarith [(xHi_gt_one_and_le hL hG r).1]

lemma subSum_xHi_nonneg {L : ℝ} {G : ℕ} (hL : 1 < L) (hG : 0 < G) (A : Finset (Fin G)) :
    0 ≤ subSum (xHi L G) A :=
  sum_nonneg fun r _ => xHi_nonneg hL hG r

lemma xLo_ge_one {L : ℝ} {G : ℕ} (hL : 1 < L) (hG : 0 < G) (r : Fin G) :
    1 ≤ xLo L G r := by
  have hΔ : 0 < gridDelta L G := gridDelta_pos hL hG
  unfold xLo
  rw [← exp_zero]
  exact exp_le_exp.mpr (mul_nonneg (Nat.cast_nonneg _) hΔ.le)

lemma xHi_strictMono {L : ℝ} {G : ℕ} (hL : 1 < L) (hG : 0 < G) :
    StrictMono (xHi L G) := by
  intro r₁ r₂ hlt
  have hΔ : 0 < gridDelta L G := gridDelta_pos hL hG
  unfold xHi
  exact exp_lt_exp.mpr (mul_lt_mul_of_pos_right (by exact_mod_cast Nat.succ_lt_succ hlt) hΔ)

lemma binsLe_card_eq {L : ℝ} {G : ℕ} (hL : 1 < L) (hG : 0 < G) {u : ℝ} (hu1 : 1 ≤ u) (huL : u ≤ L) :
    (binsLe L G u).card = ⌊log u / gridDelta L G⌋₊ := by
  have hΔ : 0 < gridDelta L G := gridDelta_pos hL hG
  set k := ⌊log u / gridDelta L G⌋₊
  have hk_le : k ≤ G := by
    have h1 : log u / gridDelta L G ≤ (G : ℝ) := by
      unfold gridDelta
      have hlogL : 0 < log L := log_pos hL
      have hGpos : (0 : ℝ) < (G : ℝ) := by positivity
      rw [div_div_eq_mul_div, div_le_iff₀ hlogL]
      have hlog_le : log u ≤ log L := log_le_log (by linarith) huL
      nlinarith
    exact Nat.floor_le_of_le h1
  have hmem : ∀ r : Fin G, r ∈ binsLe L G u ↔ r.val < k := by
    intro r
    simp only [binsLe, mem_filter, mem_univ, true_and]
    unfold xHi
    rw [← exp_log (by linarith : 0 < u), exp_le_exp, ← le_div_iff₀ hΔ]
    have hnn : 0 ≤ log u / gridDelta L G := div_nonneg (log_nonneg hu1) hΔ.le
    rw [← Nat.le_floor_iff hnn]
    change r.val + 1 ≤ k ↔ r.val < k
    omega
  have hcard : (binsLe L G u).card = (range k).card := by
    refine card_bij (fun r _ => r.val) ?_ ?_ ?_
    · intro r hr; exact mem_range.mpr ((hmem r).mp hr)
    · intro r₁ _ r₂ _ h; exact Fin.ext h
    · intro i hi
      have hik : i < k := mem_range.mp hi
      exact ⟨⟨i, lt_of_lt_of_le hik hk_le⟩, (hmem ⟨i, lt_of_lt_of_le hik hk_le⟩).mpr hik, rfl⟩
  rw [hcard, card_range]

lemma binsLe_card_mul_delta {L : ℝ} {G : ℕ} (hL : 1 < L) (hG : 0 < G) {u : ℝ} (hu1 : 1 ≤ u) (huL : u ≤ L) :
    log u - gridDelta L G < ((binsLe L G u).card : ℝ) * gridDelta L G ∧
    ((binsLe L G u).card : ℝ) * gridDelta L G ≤ log u := by
  have hΔ : 0 < gridDelta L G := gridDelta_pos hL hG
  rw [binsLe_card_eq hL hG hu1 huL]
  have hnn : 0 ≤ log u / gridDelta L G := div_nonneg (log_nonneg hu1) hΔ.le
  constructor
  · have hlt := Nat.lt_floor_add_one (log u / gridDelta L G)
    have hmul := mul_lt_mul_of_pos_right hlt hΔ
    rw [div_mul_cancel₀ _ hΔ.ne', add_mul, one_mul] at hmul
    linarith
  · have hle := Nat.floor_le hnn
    have hmul := mul_le_mul_of_nonneg_right hle hΔ.le
    rwa [div_mul_cancel₀ _ hΔ.ne'] at hmul

lemma binsLe_mono {L : ℝ} {G : ℕ} {u v : ℝ} (huv : u ≤ v) :
    binsLe L G u ⊆ binsLe L G v := by
  intro r hr
  simp only [binsLe, mem_filter, mem_univ, true_and] at hr ⊢
  exact le_trans hr huv

lemma binsLe_top {L : ℝ} {G : ℕ} (hL : 1 < L) (hG : 0 < G) :
    binsLe L G L = univ := by
  ext r
  simp only [binsLe, mem_filter, mem_univ, true_and, iff_true]
  exact (xHi_gt_one_and_le hL hG r).2

/-- Checkpoint scales `u_j = L ^ (j / 1000)` for `j = 0, ..., 1000`. -/
noncomputable def uCk (L : ℝ) (j : ℕ) : ℝ := L ^ ((j : ℝ) / 1000)

/-- Typical event on `b : Fin G → Bool`: every checkpoint `u_j` has at most `(j + 5)/1000 * log L` active bins. -/
def isTyp (L : ℝ) (G : ℕ) (b : Fin G → Bool) : Prop :=
  ∀ j ∈ Icc 0 1000,
    ((activeSet b ∩ binsLe L G (uCk L j)).card : ℝ) ≤
      ((j : ℝ) / 1000 + 5 / 1000) * log L

/-- Every `u ∈ [1, L]` inherits the uniform upper bound on `isTyp`. -/
lemma isTyp_card_binsLe {L : ℝ} {G : ℕ} (hL : 1 < L) (hG : 0 < G) {b : Fin G → Bool}
    (hb : isTyp L G b) {u : ℝ} (hu1 : 1 ≤ u) (huL : u ≤ L) :
    ((activeSet b ∩ binsLe L G u).card : ℝ) ≤ log u + (6 / 1000 : ℝ) * log L := by
  have hlogL : 0 < log L := log_pos hL
  set t : ℝ := 1000 * log u / log L
  have ht_nn : 0 ≤ t := div_nonneg (mul_nonneg (by norm_num) (log_nonneg hu1)) hlogL.le
  have ht_le : t ≤ 1000 := by
    rw [div_le_iff₀ hlogL]
    have := log_le_log (by linarith) huL
    linarith
  set j : ℕ := min 1000 (⌊t⌋₊ + 1)
  have hj_mem : j ∈ Icc 0 1000 := mem_Icc.mpr ⟨Nat.zero_le _, min_le_left _ _⟩
  have hu_le : u ≤ uCk L j := by
    unfold uCk
    rw [rpow_def_of_pos (by linarith : 0 < L), ← exp_log (by linarith : 0 < u)]
    apply exp_le_exp.mpr
    by_cases h1000 : ⌊t⌋₊ + 1 ≤ 1000
    · have hj_eq : j = ⌊t⌋₊ + 1 := min_eq_right h1000
      rw [hj_eq]
      have hlt : t < ((⌊t⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_floor_add_one t
      have hmul := mul_lt_mul_of_pos_right hlt hlogL
      have ht_mul : t * log L = 1000 * log u := by
        unfold t; field_simp [hlogL.ne']
      rw [ht_mul] at hmul
      linarith
    · have hj_eq : j = 1000 := min_eq_left (by omega)
      rw [hj_eq]
      have : log u ≤ log L := log_le_log (by linarith) huL
      linarith
  have hj_bound : (j : ℝ) / 1000 * log L ≤ log u + (1 / 1000 : ℝ) * log L := by
    have hj_le : (j : ℝ) ≤ t + 1 := by
      have h1 : j ≤ ⌊t⌋₊ + 1 := min_le_right _ _
      have h2 : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht_nn
      have h3 : (j : ℝ) ≤ (⌊t⌋₊ : ℝ) + 1 := by exact_mod_cast h1
      linarith
    have ht_mul : t / 1000 * log L = log u := by
      unfold t; field_simp [hlogL.ne']
    have hmul := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hj_le (by norm_num : (0 : ℝ) ≤ 1000)) hlogL.le
    rw [add_div, add_mul, ht_mul] at hmul
    linarith
  have hsub : activeSet b ∩ binsLe L G u ⊆ activeSet b ∩ binsLe L G (uCk L j) :=
    inter_subset_inter_left (binsLe_mono hu_le)
  have hcard : ((activeSet b ∩ binsLe L G u).card : ℝ) ≤
      ((activeSet b ∩ binsLe L G (uCk L j)).card : ℝ) := by
    exact_mod_cast card_le_card hsub
  have htyp := hb j hj_mem
  linarith

/-- On `isTyp`, total cardinality is at most `1.005 * log L`. -/
lemma isTyp_card_total {L : ℝ} {G : ℕ} (hL : 1 < L) (hG : 0 < G) {b : Fin G → Bool}
    (hb : isTyp L G b) :
    ((activeSet b).card : ℝ) ≤ (1005 / 1000 : ℝ) * log L := by
  have h := hb 1000 (mem_Icc.mpr ⟨by omega, le_rfl⟩)
  have hu : uCk L 1000 = L := by unfold uCk; norm_num
  rw [hu, binsLe_top hL hG, inter_univ] at h
  linarith

/-- The `0.1%` reserved bins `S₂ = {r : Fin G | r.val % 1000 = 0}`. -/
def resBins (G : ℕ) : Finset (Fin G) :=
  univ.filter fun r => r.val % 1000 = 0

lemma resBins_card_le (G : ℕ) :
    ((resBins G).card : ℝ) ≤ (G : ℝ) / 1000 + 1 := by
  rcases Nat.eq_zero_or_pos G with rfl | hG
  · simp [resBins]
  have hsub : resBins G ⊆ (range (G / 1000 + 1)).attach.image
      (fun k => ⟨min (G - 1) (1000 * k.1), by omega⟩) := by
    intro r hr
    have hmod : r.val % 1000 = 0 := (mem_filter.mp hr).2
    have hG : 0 < G := Nat.pos_of_ne_zero (by intro h0; subst h0; exact Fin.elim0 r)
    have hdiv : r.val / 1000 < G / 1000 + 1 := by
      have := Nat.div_le_div_right (c := 1000) (le_of_lt r.isLt)
      omega
    refine mem_image.mpr ⟨⟨r.val / 1000, mem_range.mpr hdiv⟩, mem_attach _ _, ?_⟩
    ext
    dsimp
    have heq : 1000 * (r.val / 1000) = r.val := by omega
    rw [heq]
    exact min_eq_right (by omega)
  have hcard : (resBins G).card ≤ G / 1000 + 1 := by
    calc (resBins G).card ≤ _ := card_le_card hsub
      _ ≤ (range (G / 1000 + 1)).attach.card := card_image_le
      _ = G / 1000 + 1 := by rw [card_attach, card_range]
  have hdiv : ((G / 1000 : ℕ) : ℝ) ≤ (G : ℝ) / 1000 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 1000)]
    exact_mod_cast Nat.div_mul_le_self G 1000
  have hcast : ((resBins G).card : ℝ) ≤ ((G / 1000 : ℕ) : ℝ) + 1 := by exact_mod_cast hcard
  linarith

/-- The 3-element spacing lemma: if `A` has an element `r₀` with `x r₀ ≥ 3`,
then for any `η ≤ 1/2`, at least `(1/6) * 3^A.card` disjoint pairs `(I, J)` of subsets of `A`
satisfy `subSum x J - subSum x I ≥ 1 + η`. -/
lemma card_large_diff_disjoint_pairs {G : ℕ} (x : Fin G → ℝ) (A : Finset (Fin G))
    {r₀ : Fin G} (hr₀ : r₀ ∈ A) (hx₀ : 3 ≤ x r₀) {η : ℝ} (hη : η ≤ 1 / 2) :
    (3 : ℝ) ^ A.card / 6 ≤
      ((((A.powerset ×ˢ A.powerset).filter fun IJ =>
          Disjoint IJ.1 IJ.2 ∧ 1 + η ≤ subSum x IJ.2 - subSum x IJ.1).card : ℕ) : ℝ) := by
  set B := A.erase r₀
  set P := (B.powerset ×ˢ B.powerset).filter fun IJ => Disjoint IJ.1 IJ.2
  have hP_card : P.card = 3 ^ B.card := by
    -- Bijection `P ≃ (B → Fin 3)`: `0 ↦ neither, 1 ↦ I, 2 ↦ J`.
    have hbij : P.card = Fintype.card (B → Fin 3) := by
      refine card_bij
        (fun IJ _ (r : B) => if r.1 ∈ IJ.1 then (1 : Fin 3) else if r.1 ∈ IJ.2 then 2 else 0)
        (fun _ _ => mem_univ _) ?_ ?_
      · intro ⟨I₁, J₁⟩ h₁ ⟨I₂, J₂⟩ h₂ hfun
        simp only [P, mem_filter, mem_product, mem_powerset] at h₁ h₂
        have hI : I₁ = I₂ := by
          ext r
          by_cases hrB : r ∈ B
          · have hv := congr_fun hfun ⟨r, hrB⟩
            by_cases h1 : r ∈ I₁ <;> by_cases h2 : r ∈ I₂ <;> simp [h1, h2] at hv ⊢
            · exfalso; split_ifs at hv <;> simp at hv
            · exfalso; split_ifs at hv <;> simp at hv
          · exact ⟨fun h => absurd (h₁.1.1 h) hrB, fun h => absurd (h₂.1.1 h) hrB⟩
        have hJ : J₁ = J₂ := by
          ext r
          by_cases hrB : r ∈ B
          · have hv := congr_fun hfun ⟨r, hrB⟩
            have h1I : r ∈ I₁ → r ∉ J₁ := fun hi hj => disjoint_left.mp h₁.2 hi hj
            have h2I : r ∈ I₂ → r ∉ J₂ := fun hi hj => disjoint_left.mp h₂.2 hi hj
            by_cases h1 : r ∈ J₁ <;> by_cases h2 : r ∈ J₂
            · exact ⟨fun _ => h2, fun _ => h1⟩
            · exfalso
              have hnI1 : r ∉ I₁ := fun hi => h1I hi h1
              have hnI2 : r ∉ I₂ := by rwa [← hI]
              simp [hnI1, hnI2, h1, h2] at hv
            · exfalso
              have hnI2 : r ∉ I₂ := fun hi => h2I hi h2
              have hnI1 : r ∉ I₁ := by rwa [hI]
              simp [hnI1, hnI2, h1, h2] at hv
            · exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩
          · exact ⟨fun h => absurd (h₁.1.2 h) hrB, fun h => absurd (h₂.1.2 h) hrB⟩
        exact Prod.ext hI hJ
      · intro f _
        let I := B.filter fun r => if h : r ∈ B then f ⟨r, h⟩ = 1 else False
        let J := B.filter fun r => if h : r ∈ B then f ⟨r, h⟩ = 2 else False
        refine ⟨(I, J), ?_, ?_⟩
        · simp only [P, mem_filter, mem_product, mem_powerset]
          refine ⟨⟨filter_subset _ _, filter_subset _ _⟩, ?_⟩
          rw [disjoint_left]
          intro r hrI hrJ
          simp only [I, J, mem_filter] at hrI hrJ
          rw [dif_pos hrI.1] at hrI hrJ
          have : (1 : Fin 3) = 2 := hrI.2.symm.trans hrJ.2
          exact absurd this (by decide)
        · ext ⟨r, hrB⟩
          have hrI : r ∈ I ↔ f ⟨r, hrB⟩ = 1 := by simp [I, hrB]
          have hrJ : r ∈ J ↔ f ⟨r, hrB⟩ = 2 := by simp [J, hrB]
          have hval : f ⟨r, hrB⟩ = 0 ∨ f ⟨r, hrB⟩ = 1 ∨ f ⟨r, hrB⟩ = 2 := by
            generalize f ⟨r, hrB⟩ = c; fin_cases c <;> simp
          rcases hval with hfr | hfr | hfr <;> simp [hrI, hrJ, hfr]
    rw [hbij, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
  -- Map each `(I, J) ∈ P` to a disjoint pair `(I', J')` in `A` with `subSum J' - subSum I' ≥ 1 + η`
  -- by choosing between `(I, insert r₀ J)` (if `subSum J - subSum I ≥ 0`) and `(J, insert r₀ I)` (otherwise)!
  -- Notice: BOTH choices map `≤ 2` elements of `P` to the same `(I', J')`? Even better:
  -- The map `(I, J) ↦ if 0 ≤ subSum x J - subSum x I then (I, insert r₀ J) else (J, insert r₀ I)`
  -- has `subSum x J' - subSum x I' = |subSum x J - subSum x I| + x r₀ ≥ 3 ≥ 1 + η`!
  -- Wait: `(I, J)` and `(J, I)` map to the same output ONLY if `subSum J - subSum I ≠ 0` (at most 2-to-1)!
  -- Even simpler: restrict to `P⁺ = P.filter (fun IJ => 0 ≤ subSum x IJ.2 - subSum x IJ.1)`!
  -- On `P⁺`, `(I, J) ↦ (I, insert r₀ J)` is INJECTIVE, AND `P⁺.card + P⁻.card ≥ P.card`,
  -- with `P⁺.card = P⁻.card` by swapping `(I, J) ↦ (J, I)`! So `2 * P⁺.card ≥ P.card = 3 ^ (A.card - 1)`!
  let Ppos := P.filter fun IJ => 0 ≤ subSum x IJ.2 - subSum x IJ.1
  have hPpos_card : P.card ≤ 2 * Ppos.card := by
    have hcov : P ⊆ Ppos ∪ Ppos.image Prod.swap := by
      intro ⟨I, J⟩ hIJ
      rw [mem_union]
      by_cases h0 : 0 ≤ subSum x J - subSum x I
      · left; exact mem_filter.mpr ⟨hIJ, h0⟩
      · right
        refine mem_image.mpr ⟨(J, I), ?_, rfl⟩
        simp only [Ppos, P, mem_filter, mem_product, mem_powerset] at hIJ ⊢
        exact ⟨⟨⟨hIJ.1.2, hIJ.1.1⟩, hIJ.2.symm⟩, by linarith⟩
    calc P.card ≤ (Ppos ∪ Ppos.image Prod.swap).card := card_le_card hcov
      _ ≤ Ppos.card + (Ppos.image Prod.swap).card := card_union_le _ _
      _ ≤ Ppos.card + Ppos.card := Nat.add_le_add_left card_image_le _
      _ = 2 * Ppos.card := by omega
  let T := (A.powerset ×ˢ A.powerset).filter fun IJ =>
    Disjoint IJ.1 IJ.2 ∧ 1 + η ≤ subSum x IJ.2 - subSum x IJ.1
  have hinj : Ppos.card ≤ T.card := by
    refine card_le_card_of_injOn (fun IJ => (IJ.1, insert r₀ IJ.2)) ?_ ?_
    · intro ⟨I, J⟩ hIJ
      simp only [mem_coe, Ppos, P, mem_filter, mem_product, mem_powerset] at hIJ
      simp only [mem_coe, T, mem_filter, mem_product, mem_powerset]
      have hr₀I : r₀ ∉ I := fun h => (mem_erase.mp (hIJ.1.1.1 h)).1 rfl
      have hr₀J : r₀ ∉ J := fun h => (mem_erase.mp (hIJ.1.1.2 h)).1 rfl
      refine ⟨⟨Subset.trans hIJ.1.1.1 (erase_subset r₀ A), ?_⟩, ?_, ?_⟩
      · intro r hr
        rcases mem_insert.mp hr with rfl | hrJ
        · exact hr₀
        · exact erase_subset r₀ A (hIJ.1.1.2 hrJ)
      · exact disjoint_insert_right.mpr ⟨hr₀I, hIJ.1.2⟩
      · unfold subSum
        rw [sum_insert hr₀J]
        have : 0 ≤ subSum x J - subSum x I := hIJ.2
        unfold subSum at this
        linarith
    · intro ⟨I₁, J₁⟩ h₁ ⟨I₂, J₂⟩ h₂ heq
      simp only [Ppos, P, mem_coe, mem_filter, mem_product, mem_powerset] at h₁ h₂
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, hJ⟩ := heq
      have hr₀J₁ : r₀ ∉ J₁ := fun h => (mem_erase.mp (h₁.1.1.2 h)).1 rfl
      have hr₀J₂ : r₀ ∉ J₂ := fun h => (mem_erase.mp (h₂.1.1.2 h)).1 rfl
      have hJeq : J₁ = J₂ := by
        have := congr_arg (fun S => S.erase r₀) hJ
        simpa [erase_insert hr₀J₁, erase_insert hr₀J₂] using this
      subst hJeq; rfl
  have hBcard : B.card + 1 = A.card := by
    rw [card_erase_of_mem hr₀]; have := card_pos.mpr ⟨r₀, hr₀⟩; omega
  have h3pow : (3 : ℝ) ^ A.card = 3 * (3 : ℝ) ^ B.card := by
    rw [← hBcard, pow_succ']
  have hle_real : (3 : ℝ) ^ B.card ≤ 2 * (T.card : ℝ) := by
    have : 3 ^ B.card ≤ 2 * T.card := by
      rw [← hP_card]; exact le_trans hPpos_card (Nat.mul_le_mul_left 2 hinj)
    exact_mod_cast this
  rw [h3pow]
  linarith

/-- Lower bound on the count of reserved bins `r ∈ resBins G` with `xHi L G r ∈ [D - η, D - η/2)`. -/
lemma card_resBins_in_window {L : ℝ} {G : ℕ} (hL : 10 ≤ L) (hG : 0 < G)
    {η D : ℝ} (hηpos : 0 < η) (hη1 : η ≤ 1 / 2) (hD1 : 1 + η ≤ D) (hDL : D ≤ L)
    (hstep : 2000 * L * gridDelta L G ≤ η / 4) :
    η / (16000 * L) ≤
      gridP L G * (((resBins G).filter fun r => D - η ≤ xHi L G r ∧ xHi L G r < D - η / 2).card : ℝ) := by
  have hL1 : 1 < L := by linarith
  have hΔpos : 0 < gridDelta L G := gridDelta_pos hL1 hG
  have hΔle1 : gridDelta L G ≤ 1 := by
    have : 2000 * L * gridDelta L G ≤ 1 / 8 := by linarith
    nlinarith
  have hp := gridP_bounds hL1 hG hΔle1
  -- Look at the bin index range `[k₁, k₂)` where `xHi r ∈ [D - η, D - η/2)`.
  -- Specifically, `k₁ = ⌊log (D - η) / Δ⌋₊` and `k₂ = ⌊log (D - η/2) / Δ⌋₊`.
  -- Every `r : Fin G` with `k₁ ≤ r.val < k₂` satisfies `D - η < xHi L G r ≤ D - η/2`?
  -- Carefully: `xHi L G r = exp ((r.val + 1) * Δ)`.
  -- Let `a = log (D - η) / Δ` and `b = log (D - η/2) / Δ`.
  -- If `a ≤ r.val + 1 < b`, then `D - η ≤ xHi L G r < D - η/2`!
  have hDlo_ge1 : 1 ≤ D - η := by linarith
  have hDhi_leL : D - η / 2 ≤ L := by linarith
  have hDlo_pos : 0 < D - η := by linarith
  have hDhi_pos : 0 < D - η / 2 := by linarith
  set a : ℝ := log (D - η) / gridDelta L G
  set b : ℝ := log (D - η / 2) / gridDelta L G
  have hb_sub_a : η / (2 * L * gridDelta L G) ≤ b - a := by
    have hlog_diff : η / (2 * L) ≤ log (D - η / 2) - log (D - η) := by
      rw [← log_div hDhi_pos.ne' hDlo_pos.ne']
      have hinv := log_le_sub_one_of_pos (div_pos hDlo_pos hDhi_pos)
      rw [log_div hDlo_pos.ne' hDhi_pos.ne'] at hinv
      rw [log_div hDhi_pos.ne' hDlo_pos.ne']
      have hfrac : 1 - (D - η) / (D - η / 2) = (η / 2) / (D - η / 2) := by
        calc 1 - (D - η) / (D - η / 2)
            = (D - η / 2) / (D - η / 2) - (D - η) / (D - η / 2) := by rw [div_self hDhi_pos.ne']
          _ = ((D - η / 2) - (D - η)) / (D - η / 2) := (sub_div _ _ _).symm
          _ = (η / 2) / (D - η / 2) := by ring
      have hge : η / (2 * L) ≤ (η / 2) / (D - η / 2) := by
        rw [div_le_div_iff₀ (by positivity) hDhi_pos]
        nlinarith
      linarith
    have hdiv := div_le_div_of_nonneg_right hlog_diff hΔpos.le
    rw [div_div] at hdiv
    unfold a b
    linarith [show (log (D - η / 2) - log (D - η)) / gridDelta L G =
        log (D - η / 2) / gridDelta L G - log (D - η) / gridDelta L G by ring]
  -- Count multiples `1000 * m` with `a ≤ 1000 * m + 1 < b` and `1000 * m < G`.
  have hb_le_G : b ≤ (G : ℝ) := by
    unfold b gridDelta
    have hlogL : 0 < log L := log_pos hL1
    rw [div_div_eq_mul_div, div_le_iff₀ hlogL]
    have hle : log (D - η / 2) ≤ log L := log_le_log hDhi_pos hDhi_leL
    have hGpos : (0 : ℝ) < (G : ℝ) := by positivity
    nlinarith
  have ha_nn : 0 ≤ a := div_nonneg (log_nonneg hDlo_ge1) hΔpos.le
  -- Let `m₁ = ⌈a / 1000⌉₊` and `m₂ = ⌊(b - 1) / 1000⌋₊`.
  -- Wait: if `1000 * m ∈ [a, b - 1)`, then `a ≤ 1000 * m < 1000 * m + 1 < b`!
  -- And `1000 * m < b - 1 < G`, so `1000 * m < G`!
  have hb_sub_a_ge : 4000 ≤ b - a := by
    have h1 : 4000 ≤ η / (2 * L * gridDelta L G) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    linarith
  set m₁ : ℕ := ⌈a / 1000⌉₊
  set m₂ : ℕ := ⌊(b - 2) / 1000⌋₊
  have hm₁_le : (m₁ : ℝ) < a / 1000 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hm₂_ge : (b - 2) / 1000 - 1 < (m₂ : ℝ) := by
    have := Nat.lt_floor_add_one ((b - 2) / 1000); linarith
  have hm₂_le_b : ((m₂ : ℕ) : ℝ) ≤ (b - 2) / 1000 := Nat.floor_le (by linarith)
  have hm_range : (b - a) / 1000 - 3 ≤ ((m₂ - m₁ : ℕ) : ℝ) := by
    have hle : m₁ ≤ m₂ := by
      have hlt : (m₁ : ℝ) < (m₂ : ℝ) := by linarith
      exact le_of_lt (by exact_mod_cast hlt)
    rw [Nat.cast_sub hle]
    linarith
  have hinj : (Ico m₁ m₂).card ≤
      ((resBins G).filter fun r => D - η ≤ xHi L G r ∧ xHi L G r < D - η / 2).card := by
    refine card_le_card_of_injOn
      (fun m => ⟨min (G - 1) (1000 * m), by omega⟩) ?_ ?_
    · intro m hm
      simp only [mem_coe, mem_Ico] at hm
      have hm_lt_G : 1000 * m < G := by
        have h1 : (1000 * m : ℝ) < b - 2 := by
          have hm2 : (m : ℝ) < (m₂ : ℝ) := by exact_mod_cast hm.2
          linarith
        have h2 : (1000 * m : ℝ) < (G : ℝ) := by linarith
        exact_mod_cast h2
      have hmin : min (G - 1) (1000 * m) = 1000 * m := min_eq_right (by omega)
      simp only [mem_coe, mem_filter, resBins, mem_univ, true_and, hmin]
      refine ⟨by omega, ?_, ?_⟩
      · unfold xHi
        rw [← exp_log hDlo_pos, exp_le_exp]
        have hm1 : a / 1000 ≤ (m : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hm.1)
        have ha_eq : a * gridDelta L G = log (D - η) := div_mul_cancel₀ _ hΔpos.ne'
        have : a ≤ ((1000 * m + 1 : ℕ) : ℝ) := by push_cast; linarith
        have := mul_le_mul_of_nonneg_right this hΔpos.le
        linarith
      · unfold xHi
        rw [← exp_log hDhi_pos, exp_lt_exp]
        have hm2 : (m : ℝ) < (m₂ : ℝ) := by exact_mod_cast hm.2
        have hb_eq : b * gridDelta L G = log (D - η / 2) := div_mul_cancel₀ _ hΔpos.ne'
        have : ((1000 * m + 1 : ℕ) : ℝ) < b := by push_cast; linarith
        have := mul_lt_mul_of_pos_right this hΔpos
        linarith
    · intro m₁' hm₁' m₂' hm₂' heq
      simp only [mem_coe, mem_Ico] at hm₁' hm₂'
      have hlt1 : 1000 * m₁' < G := by
        have : (m₁' : ℝ) < (m₂ : ℝ) := by exact_mod_cast hm₁'.2
        have : (1000 * m₁' : ℝ) < (G : ℝ) := by linarith
        exact_mod_cast this
      have hlt2 : 1000 * m₂' < G := by
        have : (m₂' : ℝ) < (m₂ : ℝ) := by exact_mod_cast hm₂'.2
        have : (1000 * m₂' : ℝ) < (G : ℝ) := by linarith
        exact_mod_cast this
      have hval := congr_arg Fin.val heq
      dsimp at hval
      rw [min_eq_right (by omega), min_eq_right (by omega)] at hval
      omega
  have hcard_ge : (b - a) / 1000 - 3 ≤
      (((resBins G).filter fun r => D - η ≤ xHi L G r ∧ xHi L G r < D - η / 2).card : ℝ) := by
    have h1 : (m₂ - m₁ : ℕ) ≤
        ((resBins G).filter fun r => D - η ≤ xHi L G r ∧ xHi L G r < D - η / 2).card := by
      rwa [Nat.card_Ico] at hinj
    exact le_trans hm_range (by exact_mod_cast h1)
  have hcard_ge2 : (b - a) / 4000 ≤
      (((resBins G).filter fun r => D - η ≤ xHi L G r ∧ xHi L G r < D - η / 2).card : ℝ) := by
    linarith [hb_sub_a_ge]
  have hcard_ge3 : η / (8000 * L * gridDelta L G) ≤
      (((resBins G).filter fun r => D - η ≤ xHi L G r ∧ xHi L G r < D - η / 2).card : ℝ) := by
    have hdiv := div_le_div_of_nonneg_right hb_sub_a (by norm_num : (0 : ℝ) ≤ 4000)
    have hring : η / (2 * L * gridDelta L G) / 4000 = η / (8000 * L * gridDelta L G) := by ring
    linarith
  have hmul : gridDelta L G / 2 * (η / (8000 * L * gridDelta L G)) ≤
      gridP L G * (((resBins G).filter fun r => D - η ≤ xHi L G r ∧ xHi L G r < D - η / 2).card : ℝ) := by
    have hnn : 0 ≤ η / (8000 * L * gridDelta L G) := by positivity
    exact mul_le_mul hp.1 hcard_ge3 hnn hp.2.2.1.le
  have hsimp : gridDelta L G / 2 * (η / (8000 * L * gridDelta L G)) = η / (16000 * L) := by
    field_simp [hΔpos.ne', (show (0 : ℝ) < L by linarith).ne']; ring
  linarith

/-- Definition of good padded consecutive disjoint pairs on `Fin G → Bool`. -/
noncomputable def goodPairs (L : ℝ) (G : ℕ) (η : ℝ) (b : Fin G → Bool) :
    Finset (Finset (Fin G) × Finset (Fin G)) :=
  ((activeSet b).powerset ×ˢ (activeSet b).powerset).filter fun IJ =>
    Disjoint IJ.1 IJ.2 ∧
    subSum (xHi L G) IJ.2 ≤ L ∧
    η / 2 < subSum (xHi L G) IJ.2 - subSum (xHi L G) IJ.1 ∧
    subSum (xHi L G) IJ.2 - subSum (xHi L G) IJ.1 ≤ η ∧
    ∀ H ∈ (activeSet b).powerset, H ≠ IJ.1 → H ≠ IJ.2 →
      subSum (xHi L G) H < subSum (xHi L G) IJ.1 - η / 10 ∨
      subSum (xHi L G) IJ.2 + η / 10 < subSum (xHi L G) H

/-- Good pairs constructed via `S₁` + a single reserved element `r₀ ∈ S₂`. -/
noncomputable def uPairs (L : ℝ) (G : ℕ) (η : ℝ) (b : Fin G → Bool) :
    Finset (Finset (Fin G) × Finset (Fin G)) :=
  ((activeSet b).powerset ×ˢ (activeSet b).powerset).filter fun IJ =>
    Disjoint IJ.1 IJ.2 ∧
    subSum (xHi L G) IJ.2 ≤ L ∧
    η / 2 < subSum (xHi L G) IJ.2 - subSum (xHi L G) IJ.1 ∧
    subSum (xHi L G) IJ.2 - subSum (xHi L G) IJ.1 ≤ η

/-- Bad triples `(I, J, H)` witnessing that `(I, J) ∈ uPairs` fails the `η/10`-padding condition. -/
noncomputable def badTriples (L : ℝ) (G : ℕ) (η : ℝ) (b : Fin G → Bool) :
    Finset ((Finset (Fin G) × Finset (Fin G)) × Finset (Fin G)) :=
  ((uPairs L G η b) ×ˢ (activeSet b).powerset).filter fun IJH =>
    IJH.2 ≠ IJH.1.1 ∧ IJH.2 ≠ IJH.1.2 ∧
    subSum (xHi L G) IJH.1.1 - η / 10 ≤ subSum (xHi L G) IJH.2 ∧
    subSum (xHi L G) IJH.2 ≤ subSum (xHi L G) IJH.1.2 + η / 10

lemma uPairs_le_goodPairs_add_badTriples (L : ℝ) (G : ℕ) (η : ℝ) (b : Fin G → Bool) :
    ((uPairs L G η b).card : ℝ) ≤
      ((goodPairs L G η b).card : ℝ) + ((badTriples L G η b).card : ℝ) := by
  have hsub : uPairs L G η b ⊆ goodPairs L G η b ∪ (badTriples L G η b).image Prod.fst := by
    intro IJ hIJ
    rw [mem_union]
    by_cases hgood : IJ ∈ goodPairs L G η b
    · left; exact hgood
    · right
      simp only [uPairs, mem_filter, mem_product] at hIJ
      simp only [goodPairs, mem_filter, mem_product, hIJ.1, hIJ.2.1, hIJ.2.2.1,
          hIJ.2.2.2.1, hIJ.2.2.2.2, true_and, not_forall, not_or, not_lt] at hgood
      obtain ⟨H, hHpow, hHne1, hHne2, hHlo, hHhi⟩ := hgood
      refine mem_image.mpr ⟨(IJ, H), ?_, rfl⟩
      simp only [badTriples, mem_filter, mem_product, uPairs]
      exact ⟨⟨hIJ, hHpow⟩, hHne1, hHne2, hHlo, hHhi⟩
  have hnat : (uPairs L G η b).card ≤ (goodPairs L G η b).card + (badTriples L G η b).card := by
    calc (uPairs L G η b).card
        ≤ (goodPairs L G η b ∪ (badTriples L G η b).image Prod.fst).card := card_le_card hsub
      _ ≤ (goodPairs L G η b).card + ((badTriples L G η b).image Prod.fst).card := card_union_le _ _
      _ ≤ (goodPairs L G η b).card + (badTriples L G η b).card := Nat.add_le_add_left card_image_le _
  exact_mod_cast hnat

/-- Cell score capped to typical configurations. -/
noncomputable def cellScore (L : ℝ) (G : ℕ) (η : ℝ) (b : Fin G → Bool) : ℕ :=
  open scoped Classical in
  if isTyp L G b then (goodPairs L G η b).card else 0

/-- Good event on the `S₁` coordinates (`r ∉ resBins G`). -/
def isGoodB1 (L : ℝ) (G : ℕ) (b : Fin G → Bool) : Prop :=
  (∀ j ∈ Icc 0 1000,
      ((activeSet b ∩ (binsLe L G (uCk L j) \ resBins G)).card : ℝ) ≤
        ((j : ℝ) / 1000 + 2 / 1000) * log L) ∧
  (997 / 1000 : ℝ) * log L ≤
      ((activeSet b ∩ (binsLe L G (L / 10) \ resBins G)).card : ℝ) ∧
  subSum (xHi L G) (activeSet b ∩ (binsLe L G (L / 10) \ resBins G)) ≤ L ∧
  ∃ r ∈ activeSet b ∩ (binsLe L G (L / 10) \ resBins G), 3 ≤ xHi L G r

/-- `isGoodB1` depends only on coordinates outside `resBins G`. -/
lemma isGoodB1_depends_S1 (L : ℝ) (G : ℕ) (b₁ b₂ : Fin G → Bool)
    (heq : ∀ r ∉ resBins G, b₁ r = b₂ r) :
    isGoodB1 L G b₁ ↔ isGoodB1 L G b₂ := by
  have hinter : ∀ T : Finset (Fin G),
      activeSet b₁ ∩ (T \ resBins G) = activeSet b₂ ∩ (T \ resBins G) := by
    intro T; ext r
    simp only [activeSet, mem_inter, mem_filter, mem_univ, true_and, mem_sdiff]
    constructor <;> rintro ⟨hb, hT, hnr⟩ <;> refine ⟨?_, hT, hnr⟩
    · rwa [← heq r hnr]
    · rwa [heq r hnr]
  unfold isGoodB1
  simp_rw [hinter]

/-- Sum of `xHi L G r` over `binsLe L G u` is bounded by `u / gridP L G`. -/
lemma sum_xHi_binsLe_le {L : ℝ} {G : ℕ} (hL : 1 < L) (hG : 0 < G) (hΔ : gridDelta L G ≤ 1)
    {u : ℝ} (hu1 : 1 ≤ u) (huL : u ≤ L) :
    gridP L G * ∑ r ∈ binsLe L G u, xHi L G r ≤ u := by
  have hp := gridP_bounds hL hG hΔ
  rw [mul_sum]
  simp_rw [← xHi_sub_xLo]
  -- Telescoping sum over `r.val < k`: `∑_{i < k} (exp((i+1)Δ) - exp(iΔ)) = exp(kΔ) - 1 ≤ u - 1 ≤ u`.
  set k := ⌊log u / gridDelta L G⌋₊
  have hk_le : k ≤ G := by
    have h1 := binsLe_card_eq hL hG hu1 huL
    have h2 : (binsLe L G u).card ≤ G := by
      calc (binsLe L G u).card ≤ (univ : Finset (Fin G)).card := card_le_univ _
        _ = G := Fintype.card_fin G
    omega
  have hsum_eq : ∑ r ∈ binsLe L G u, (xHi L G r - xLo L G r) =
      ∑ i ∈ range k, (exp (((i + 1 : ℕ) : ℝ) * gridDelta L G) -
        exp ((i : ℝ) * gridDelta L G)) := by
    refine sum_nbij (fun r => r.val) ?_ ?_ ?_ ?_
    · intro r hr
      simp only [mem_coe, mem_range]
      have hΔpos := gridDelta_pos hL hG
      simp only [mem_coe, binsLe, mem_filter, mem_univ, true_and] at hr
      unfold xHi at hr
      rw [← exp_log (by linarith : 0 < u), exp_le_exp, ← le_div_iff₀ hΔpos] at hr
      have hnn : 0 ≤ log u / gridDelta L G := div_nonneg (log_nonneg hu1) hΔpos.le
      have : r.val + 1 ≤ k := (Nat.le_floor_iff hnn).mpr hr
      omega
    · intro r₁ _ r₂ _ h; exact Fin.ext h
    · intro i hi
      have hik : i < k := mem_range.mp hi
      refine ⟨⟨i, lt_of_lt_of_le hik hk_le⟩, ?_, rfl⟩
      simp only [mem_coe, binsLe, mem_filter, mem_univ, true_and]
      unfold xHi
      have hΔpos := gridDelta_pos hL hG
      rw [← exp_log (by linarith : 0 < u), exp_le_exp, ← le_div_iff₀ hΔpos]
      have hle : ((i + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hik
      exact le_trans hle (Nat.floor_le (div_nonneg (log_nonneg hu1) hΔpos.le))
    · intro r _; rfl
  rw [hsum_eq, sum_range_sub (fun i => exp ((i : ℝ) * gridDelta L G))]
  have hkΔ : (k : ℝ) * gridDelta L G ≤ log u := by
    have hΔpos := gridDelta_pos hL hG
    have hle := Nat.floor_le (div_nonneg (log_nonneg hu1) hΔpos.le)
    have hmul := mul_le_mul_of_nonneg_right hle hΔpos.le
    rwa [div_mul_cancel₀ _ hΔpos.ne'] at hmul
  have hexp : exp ((k : ℝ) * gridDelta L G) ≤ u := by
    calc exp ((k : ℝ) * gridDelta L G) ≤ exp (log u) := exp_le_exp.mpr hkΔ
      _ = u := exp_log (by linarith)
  simp only [Nat.cast_zero, zero_mul, exp_zero]
  linarith

/-- For sufficiently large `L` and fine enough `G`, `Pr[isGoodB1 L G] ≥ 1/2`. -/
lemma prob_isGoodB1_ge_half {L : ℝ} {G : ℕ}
    (hL : exp 10000000000 ≤ L) (hG : 0 < G)
    (hΔ : gridDelta L G ≤ 1 / 1000000) :
    (1 : ℝ) / 2 ≤ ∑ b : Fin G → Bool, if isGoodB1 L G b then bernProb (gridP L G) b else 0 := by
  have hlogL_ge : (10000000000 : ℝ) ≤ log L := by
    have := log_le_log (exp_pos _) hL
    rwa [log_exp] at this
  have hL1 : 1 < L := by
    have h0 : 0 < log L := by linarith
    exact (log_pos_iff (by linarith [exp_pos (10000000000 : ℝ)])).mp h0
  have hL_ge_100 : (100 : ℝ) ≤ L := by
    have : (100 : ℝ) ≤ exp 10000000000 := by
      have h1 := add_one_le_exp (10000000000 : ℝ); linarith
    linarith
  have hΔpos := gridDelta_pos hL1 hG
  have hp := gridP_bounds hL1 hG (by linarith)
  have hprob_nn : ∀ b : Fin G → Bool, 0 ≤ bernProb (gridP L G) b := fun b => bernProb_nonneg hp.2.2.1.le hp.2.2.2.le b
  -- Bound the probability of each of the 4 failure events by union bound (sum ≤ 1/2):
  -- Fail 1: `∃ j ∈ Icc 0 1000`, `card(X(b) ∩ (binsLe(u_j) \ S₂)) > (j/1000 + 2/1000) * log L`
  -- Fail 2: `card(X(b) ∩ (binsLe(L/10) \ S₂)) < 0.997 * log L`
  -- Fail 3: `subSum xHi (X(b) ∩ (binsLe(L/10) \ S₂)) > L`
  -- Fail 4: `∀ r ∈ X(b) ∩ (binsLe(L/10) \ S₂), xHi r < 3`
  let F1 (j : ℕ) (b : Fin G → Bool) : Prop :=
    ((j : ℝ) / 1000 + 2 / 1000) * log L <
      ((activeSet b ∩ (binsLe L G (uCk L j) \ resBins G)).card : ℝ)
  let F2 (b : Fin G → Bool) : Prop :=
    ((activeSet b ∩ (binsLe L G (L / 10) \ resBins G)).card : ℝ) < (997 / 1000 : ℝ) * log L
  let F3 (b : Fin G → Bool) : Prop :=
    L < subSum (xHi L G) (activeSet b ∩ (binsLe L G (L / 10) \ resBins G))
  let F4 (b : Fin G → Bool) : Prop :=
    ∀ r ∈ activeSet b ∩ (binsLe L G (L / 10) \ resBins G), xHi L G r < 3
  -- Bound Pr[F1 j] ≤ 1 / 10000 via Chebyshev:
  have hF1 : ∀ j ∈ Icc 0 1000,
      (∑ b : Fin G → Bool, if F1 j b then bernProb (gridP L G) b else 0) ≤ 1 / 10000 := by
    intro j hj
    set A := binsLe L G (uCk L j) \ resBins G
    have hu1 : 1 ≤ uCk L j := by
      unfold uCk
      exact one_le_rpow hL1.le (by positivity)
    have huL : uCk L j ≤ L := by
      unfold uCk
      have hjle : (j : ℝ) / 1000 ≤ 1 := by
        have : (j : ℝ) ≤ 1000 := by exact_mod_cast (mem_Icc.mp hj).2
        linarith
      calc L ^ ((j : ℝ) / 1000) ≤ L ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le hL1.le hjle
        _ = L := rpow_one L
    have hmean_le : gridP L G * (A.card : ℝ) ≤ ((j : ℝ) / 1000) * log L := by
      have hsub : (A.card : ℝ) ≤ ((binsLe L G (uCk L j)).card : ℝ) := by
        exact_mod_cast card_le_card sdiff_subset
      have hbd := (binsLe_card_mul_delta hL1 hG hu1 huL).2
      have hlog_u : log (uCk L j) = ((j : ℝ) / 1000) * log L := by
        unfold uCk; rw [log_rpow (by linarith)]
      rw [hlog_u] at hbd
      calc gridP L G * (A.card : ℝ) ≤ gridDelta L G * ((binsLe L G (uCk L j)).card : ℝ) :=
            mul_le_mul hp.2.1 hsub (Nat.cast_nonneg _) hΔpos.le
        _ = ((binsLe L G (uCk L j)).card : ℝ) * gridDelta L G := mul_comm _ _
        _ ≤ ((j : ℝ) / 1000) * log L := hbd
    have hgap_pos : (0 : ℝ) < (2 / 1000 : ℝ) * log L := by linarith
    have hcheb : ((2 / 1000 : ℝ) * log L) ^ 2 *
        (∑ b : Fin G → Bool, if F1 j b then bernProb (gridP L G) b else 0) ≤
        gridP L G * (1 - gridP L G) * (A.card : ℝ) := by
      rw [← sum_bernProb_card_inter_var (gridP L G) A, mul_sum]
      refine sum_le_sum fun b _ => ?_
      split_ifs with h
      · have hdiff : (2 / 1000 : ℝ) * log L ≤ ((activeSet b ∩ A).card : ℝ) - gridP L G * (A.card : ℝ) := by
          unfold F1 at h; linarith
        have hsq : ((2 / 1000 : ℝ) * log L) ^ 2 ≤ (((activeSet b ∩ A).card : ℝ) - gridP L G * (A.card : ℝ)) ^ 2 := by
          nlinarith
        calc ((2 / 1000 : ℝ) * log L) ^ 2 * bernProb (gridP L G) b
            = bernProb (gridP L G) b * ((2 / 1000 : ℝ) * log L) ^ 2 := mul_comm _ _
          _ ≤ bernProb (gridP L G) b * (((activeSet b ∩ A).card : ℝ) - gridP L G * (A.card : ℝ)) ^ 2 :=
                mul_le_mul_of_nonneg_left hsq (hprob_nn b)
      · rw [mul_zero]
        exact mul_nonneg (hprob_nn b) (sq_nonneg _)
    have hvar_le : gridP L G * (1 - gridP L G) * (A.card : ℝ) ≤ log L := by
      have h1 : gridP L G * (1 - gridP L G) * (A.card : ℝ) ≤ gridP L G * (A.card : ℝ) := by
        have hnn : 0 ≤ gridP L G * (A.card : ℝ) := mul_nonneg hp.2.2.1.le (Nat.cast_nonneg _)
        nlinarith [hp.2.2.1]
      have h2 : ((j : ℝ) / 1000) * log L ≤ log L := by
        have hjle : (j : ℝ) ≤ 1000 := by exact_mod_cast (mem_Icc.mp hj).2
        nlinarith
      linarith
    have hsq_pos : 0 < ((2 / 1000 : ℝ) * log L) ^ 2 := sq_pos_of_pos hgap_pos
    have hbound : log L ≤ (1 / 10000 : ℝ) * ((2 / 1000 : ℝ) * log L) ^ 2 := by
      have hsq : 10000000000 * log L ≤ (log L) ^ 2 := by nlinarith
      linarith [show (1 / 10000 : ℝ) * ((2 / 1000 : ℝ) * log L) ^ 2 = (4 / 10000000000 : ℝ) * (log L) ^ 2 by ring]
    have hfin : ((2 / 1000 : ℝ) * log L) ^ 2 *
        (∑ b : Fin G → Bool, if F1 j b then bernProb (gridP L G) b else 0) ≤
        ((2 / 1000 : ℝ) * log L) ^ 2 * (1 / 10000) := by linarith
    exact le_of_mul_le_mul_left hfin hsq_pos
  -- Bound Pr[F2] ≤ 1/10 via Chebyshev:
  have hF2 : (∑ b : Fin G → Bool, if F2 b then bernProb (gridP L G) b else 0) ≤ 1 / 10 := by
    set A := binsLe L G (L / 10) \ resBins G
    have hu1 : 1 ≤ L / 10 := by linarith
    have huL : L / 10 ≤ L := by linarith
    have hcard_ge : (log L - 4) / gridDelta L G - (G : ℝ) / 1000 - 2 ≤ (A.card : ℝ) := by
      have h1 := (binsLe_card_mul_delta hL1 hG hu1 huL).1
      have h2 := resBins_card_le G
      have hlog10 : log (L / 10) ≥ log L - 3 := by
        rw [log_div (by linarith) (by norm_num)]
        have h10 : log 10 ≤ 3 := by
          have h10' : (10 : ℝ) ≤ exp 3 := by
            have he1 : (2.7 : ℝ) ≤ exp 1 := by linarith [exp_one_gt_d9]
            have hcube : exp 3 = (exp 1) ^ 3 := by rw [← exp_nat_mul]; norm_num
            have hpow : (2.7 : ℝ) ^ 3 ≤ (exp 1) ^ 3 := pow_le_pow_left₀ (by norm_num) he1 3
            rw [hcube]; linarith [show (2.7 : ℝ) ^ 3 = 19.683 by norm_num]
          have := log_le_log (by norm_num) h10'
          rwa [log_exp] at this
        linarith
      have hcard_bins : (log L - 3 - gridDelta L G) / gridDelta L G ≤ ((binsLe L G (L / 10)).card : ℝ) := by
        rw [div_le_iff₀ hΔpos]; linarith
      have hsdiff : (binsLe L G (L / 10)).card ≤ A.card + (resBins G).card := by
        have hsub : binsLe L G (L / 10) ⊆ A ∪ resBins G := by
          intro r hr
          by_cases hr2 : r ∈ resBins G
          · exact mem_union_right _ hr2
          · exact mem_union_left _ (mem_sdiff.mpr ⟨hr, hr2⟩)
        exact le_trans (card_le_card hsub) (card_union_le _ _)
      have hsdiffR : ((binsLe L G (L / 10)).card : ℝ) ≤ (A.card : ℝ) + ((resBins G).card : ℝ) := by
        exact_mod_cast hsdiff
      have h3 : (log L - 4) / gridDelta L G ≤ (log L - 3 - gridDelta L G) / gridDelta L G :=
        div_le_div_of_nonneg_right (by linarith) hΔpos.le
      linarith
    -- Also `gridP L G ≥ gridDelta L G * (1 - gridDelta L G)`!
    have hp_tight : gridDelta L G * (1 - gridDelta L G) ≤ gridP L G := by
      unfold gridP
      -- `exp(-Δ) ≤ 1 - Δ + Δ^2` for `0 ≤ Δ ≤ 1` (since `exp(Δ) ≥ 1 + Δ` -> wait: use `1 - Δ + Δ^2/2`?
      -- Even easier: `1 / (1 + Δ) ≤ 1 - Δ + Δ^2` since `(1 + Δ)(1 - Δ + Δ^2) = 1 + Δ^3 ≥ 1`!)
      have h1 : exp (-(gridDelta L G)) ≤ 1 / (1 + gridDelta L G) := by
        rw [exp_neg, one_div]
        exact inv_anti₀ (by positivity) (by linarith [add_one_le_exp (gridDelta L G)])
      have h2 : 1 / (1 + gridDelta L G) ≤ 1 - gridDelta L G + (gridDelta L G) ^ 2 := by
        rw [div_le_iff₀ (by positivity : 0 < 1 + gridDelta L G)]
        have : 0 ≤ (gridDelta L G) ^ 3 := by positivity
        nlinarith
      linarith
    have hmean_ge : (998 / 1000 : ℝ) * log L ≤ gridP L G * (A.card : ℝ) := by
      have hGΔ : (G : ℝ) * gridDelta L G = log L := by
        unfold gridDelta; field_simp [(show (G : ℝ) ≠ 0 by positivity)]
      have hA_mul : (999 / 1000 : ℝ) * log L - 4 - 2 * gridDelta L G ≤ gridDelta L G * (A.card : ℝ) := by
        have hmul := mul_le_mul_of_nonneg_left hcard_ge hΔpos.le
        have hsimp : gridDelta L G * ((log L - 4) / gridDelta L G - (G : ℝ) / 1000 - 2) =
            log L - 4 - ((G : ℝ) * gridDelta L G) / 1000 - 2 * gridDelta L G := by
          field_simp [hΔpos.ne']
        rw [hsimp, hGΔ] at hmul
        linarith
      have hnnA : 0 ≤ (A.card : ℝ) := Nat.cast_nonneg _
      have hprod1 : gridDelta L G * (1 - gridDelta L G) * (A.card : ℝ) ≤ gridP L G * (A.card : ℝ) :=
        mul_le_mul_of_nonneg_right hp_tight hnnA
      have hmul2 : (1 - gridDelta L G) * ((999 / 1000 : ℝ) * log L - 4 - 2 * gridDelta L G) ≤
          (1 - gridDelta L G) * (gridDelta L G * (A.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hA_mul (by linarith)
      nlinarith
    have hmean_le : gridP L G * (A.card : ℝ) ≤ log L := by
      have hsub : (A.card : ℝ) ≤ ((binsLe L G (L / 10)).card : ℝ) := by
        exact_mod_cast card_le_card sdiff_subset
      have hbd := (binsLe_card_mul_delta hL1 hG hu1 huL).2
      have hlog_le : log (L / 10) ≤ log L := log_le_log (by linarith) huL
      calc gridP L G * (A.card : ℝ) ≤ gridDelta L G * ((binsLe L G (L / 10)).card : ℝ) :=
            mul_le_mul hp.2.1 hsub (Nat.cast_nonneg _) hΔpos.le
        _ = ((binsLe L G (L / 10)).card : ℝ) * gridDelta L G := mul_comm _ _
        _ ≤ log L := le_trans hbd hlog_le
    have hgap_pos : (0 : ℝ) < (1 / 1000 : ℝ) * log L := by linarith
    have hcheb : ((1 / 1000 : ℝ) * log L) ^ 2 *
        (∑ b : Fin G → Bool, if F2 b then bernProb (gridP L G) b else 0) ≤ log L := by
      have hvar : gridP L G * (1 - gridP L G) * (A.card : ℝ) ≤ log L := by
        have hnn : 0 ≤ gridP L G * (A.card : ℝ) := mul_nonneg hp.2.2.1.le (Nat.cast_nonneg _)
        nlinarith [hp.2.2.1]
      refine le_trans ?_ hvar
      rw [← sum_bernProb_card_inter_var (gridP L G) A, mul_sum]
      refine sum_le_sum fun b _ => ?_
      split_ifs with h
      · have hdiff : (1 / 1000 : ℝ) * log L ≤ gridP L G * (A.card : ℝ) - ((activeSet b ∩ A).card : ℝ) := by
          unfold F2 at h; linarith
        have hsq : ((1 / 1000 : ℝ) * log L) ^ 2 ≤ (((activeSet b ∩ A).card : ℝ) - gridP L G * (A.card : ℝ)) ^ 2 := by
          nlinarith
        calc ((1 / 1000 : ℝ) * log L) ^ 2 * bernProb (gridP L G) b
            = bernProb (gridP L G) b * ((1 / 1000 : ℝ) * log L) ^ 2 := mul_comm _ _
          _ ≤ bernProb (gridP L G) b * (((activeSet b ∩ A).card : ℝ) - gridP L G * (A.card : ℝ)) ^ 2 :=
                mul_le_mul_of_nonneg_left hsq (hprob_nn b)
      · rw [mul_zero]; exact mul_nonneg (hprob_nn b) (sq_nonneg _)
    have hsq_pos : 0 < ((1 / 1000 : ℝ) * log L) ^ 2 := sq_pos_of_pos hgap_pos
    have hfin : ((1 / 1000 : ℝ) * log L) ^ 2 *
        (∑ b : Fin G → Bool, if F2 b then bernProb (gridP L G) b else 0) ≤
        ((1 / 1000 : ℝ) * log L) ^ 2 * (1 / 10) := by nlinarith
    exact le_of_mul_le_mul_left hfin hsq_pos
  -- Bound Pr[F3] ≤ 1/10 via Markov:
  have hF3 : (∑ b : Fin G → Bool, if F3 b then bernProb (gridP L G) b else 0) ≤ 1 / 10 := by
    set A := binsLe L G (L / 10) \ resBins G
    have hmarkov : L * (∑ b : Fin G → Bool, if F3 b then bernProb (gridP L G) b else 0) ≤
        gridP L G * ∑ r ∈ A, xHi L G r := by
      rw [← sum_bernProb_linear (gridP L G) A (xHi L G), mul_sum]
      refine sum_le_sum fun b _ => ?_
      split_ifs with h
      · unfold F3 subSum at h
        calc L * bernProb (gridP L G) b = bernProb (gridP L G) b * L := mul_comm _ _
          _ ≤ bernProb (gridP L G) b * ∑ r ∈ activeSet b ∩ A, xHi L G r :=
                mul_le_mul_of_nonneg_left h.le (hprob_nn b)
      · rw [mul_zero]
        exact mul_nonneg (hprob_nn b) (sum_nonneg fun r _ => (xHi_nonneg hL1 hG r))
    have hsum_le : gridP L G * ∑ r ∈ A, xHi L G r ≤ L / 10 := by
      calc gridP L G * ∑ r ∈ A, xHi L G r
          ≤ gridP L G * ∑ r ∈ binsLe L G (L / 10), xHi L G r :=
            mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg sdiff_subset
              fun r _ _ => (xHi_nonneg hL1 hG r)) hp.2.2.1.le
        _ ≤ L / 10 := sum_xHi_binsLe_le hL1 hG (by linarith) (by linarith) (by linarith)
    have hLpos : 0 < L := by linarith
    have hfin : L * (∑ b : Fin G → Bool, if F3 b then bernProb (gridP L G) b else 0) ≤ L * (1 / 10) := by
      linarith
    exact le_of_mul_le_mul_left hfin hLpos
  -- Bound Pr[F4] ≤ 1/10: if `F4 b` holds then `X(b) ∩ (binsLe(L/10) \ resBins G) ⊆ binsLe(3)`,
  -- whose size is `≤ log 3 / Δ`, wait — even simpler: `F4 b` implies `activeSet b ∩ B = ∅`
  -- where `B = (binsLe L G (L/10) \ binsLe L G 3) \ resBins G`, so `Pr[F4] = (1 - p)^|B| ≤ exp(-p |B|) ≤ 1/10`!
  have hF4 : (∑ b : Fin G → Bool, if F4 b then bernProb (gridP L G) b else 0) ≤ 1 / 10 := by
    set B := (binsLe L G (L / 10) \ resBins G).filter (fun r => 3 ≤ xHi L G r)
    have hsub : ∀ b : Fin G → Bool, F4 b → Disjoint (activeSet b) B := by
      intro b hb
      rw [disjoint_left]
      intro r hrb hrB
      have hr1 := (mem_filter.mp hrB).1
      have hr3 := (mem_filter.mp hrB).2
      have := hb r (mem_inter.mpr ⟨hrb, hr1⟩)
      linarith
    have hle_prod : (∑ b : Fin G → Bool, if F4 b then bernProb (gridP L G) b else 0) ≤
        (1 - gridP L G) ^ B.card := by
      have h1 := sum_bernProb_mul_prod (gridP L G) (fun r : Fin G => if r ∈ B then (0 : ℝ) else 1)
      have hRHS : (∏ r : Fin G, (1 - gridP L G + gridP L G * if r ∈ B then (0 : ℝ) else 1)) =
          (1 - gridP L G) ^ B.card := by
        have hrew : ∀ r : Fin G, 1 - gridP L G + gridP L G * (if r ∈ B then (0 : ℝ) else 1) =
            if r ∈ B then 1 - gridP L G else 1 := fun r => by split_ifs <;> ring
        simp_rw [hrew, ← prod_filter, prod_const]
        congr 1; congr 1; ext r; simp
      rw [← hRHS, ← h1]
      refine sum_le_sum fun b _ => ?_
      split_ifs with h
      · have hprod1 : ∏ r ∈ activeSet b, (if r ∈ B then (0 : ℝ) else 1) = 1 :=
          prod_eq_one fun r hr => if_neg (disjoint_left.mp (hsub b h) hr)
        rw [hprod1, mul_one]
      · exact mul_nonneg (hprob_nn b) (prod_nonneg fun r _ => by split_ifs <;> norm_num)
    -- Lower bound `B.card * gridDelta L G`:
    have hBcard : (10 : ℝ) ≤ (B.card : ℝ) * gridDelta L G := by
      have hcov : binsLe L G (L / 10) ⊆ B ∪ binsLe L G 3 ∪ resBins G := by
        intro r hr
        by_cases hr2 : r ∈ resBins G
        · exact mem_union_right _ hr2
        · apply mem_union_left
          by_cases hr3 : 3 ≤ xHi L G r
          · exact mem_union_left _ (mem_filter.mpr ⟨mem_sdiff.mpr ⟨hr, hr2⟩, hr3⟩)
          · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, le_of_not_ge hr3⟩)
      have hcard_le : (binsLe L G (L / 10)).card ≤ B.card + (binsLe L G 3).card + (resBins G).card := by
        calc (binsLe L G (L / 10)).card
            ≤ (B ∪ binsLe L G 3 ∪ resBins G).card := card_le_card hcov
          _ ≤ (B ∪ binsLe L G 3).card + (resBins G).card := card_union_le _ _
          _ ≤ B.card + (binsLe L G 3).card + (resBins G).card := Nat.add_le_add_right (card_union_le _ _) _
      have hcardR : ((binsLe L G (L / 10)).card : ℝ) ≤
          (B.card : ℝ) + ((binsLe L G 3).card : ℝ) + ((resBins G).card : ℝ) := by exact_mod_cast hcard_le
      have hm1 := (binsLe_card_mul_delta hL1 hG (u := L / 10) (by linarith) (by linarith)).1
      have hm3 := (binsLe_card_mul_delta hL1 hG (u := 3) (by norm_num) (by linarith)).2
      have hres := resBins_card_le G
      have hGΔ : (G : ℝ) * gridDelta L G = log L := by
        unfold gridDelta; field_simp [(show (G : ℝ) ≠ 0 by positivity)]
      have hres_mul : ((resBins G).card : ℝ) * gridDelta L G ≤ log L / 1000 + gridDelta L G := by
        have := mul_le_mul_of_nonneg_right hres hΔpos.le
        rw [add_mul, div_mul_eq_mul_div, hGΔ, one_mul] at this
        exact this
      have hlog3 : log 3 ≤ 2 := by linarith [log_three_lt_d9]
      have hlog10 : log (L / 10) ≥ log L - 3 := by
        rw [log_div (by linarith) (by norm_num)]
        have h10 : log 10 ≤ 3 := by
          have h10' : (10 : ℝ) ≤ exp 3 := by
            have he1 : (2.7 : ℝ) ≤ exp 1 := by linarith [exp_one_gt_d9]
            have hcube : exp 3 = (exp 1) ^ 3 := by rw [← exp_nat_mul]; norm_num
            have hpow : (2.7 : ℝ) ^ 3 ≤ (exp 1) ^ 3 := pow_le_pow_left₀ (by norm_num) he1 3
            rw [hcube]; linarith [show (2.7 : ℝ) ^ 3 = 19.683 by norm_num]
          have := log_le_log (by norm_num) h10'
          rwa [log_exp] at this
        linarith
      have hmul := mul_le_mul_of_nonneg_right hcardR hΔpos.le
      rw [add_mul, add_mul] at hmul
      linarith
    have hpow_le : (1 - gridP L G) ^ B.card ≤ 1 / 10 := by
      have h1mp : 1 - gridP L G = exp (-(gridDelta L G)) := by unfold gridP; ring
      rw [h1mp, ← exp_nat_mul]
      have hexp10 : exp (-10) ≤ 1 / 10 := by
        rw [exp_neg, one_div]
        exact inv_anti₀ (by norm_num) (by linarith [add_one_le_exp (10 : ℝ)])
      have hle : (B.card : ℝ) * (-(gridDelta L G)) ≤ -10 := by linarith
      exact le_trans (exp_le_exp.mpr hle) hexp10
    exact le_trans hle_prod hpow_le
  -- Combine all failure probabilities via union bound:
  have hsum_all := sum_bernProb (G := G) (gridP L G)
  have hfail : ∑ b : Fin G → Bool, (if ¬isGoodB1 L G b then bernProb (gridP L G) b else 0) ≤ 1 / 2 := by
    have hpt : ∀ b : Fin G → Bool,
        (if ¬isGoodB1 L G b then bernProb (gridP L G) b else 0) ≤
        (∑ j ∈ Icc 0 1000, if F1 j b then bernProb (gridP L G) b else 0) +
        (if F2 b then bernProb (gridP L G) b else 0) +
        (if F3 b then bernProb (gridP L G) b else 0) +
        (if F4 b then bernProb (gridP L G) b else 0) := by
      intro b
      by_cases hg : isGoodB1 L G b
      · rw [if_neg (not_not.mpr hg)]
        have h1 : 0 ≤ ∑ j ∈ Icc 0 1000, if F1 j b then bernProb (gridP L G) b else 0 :=
          sum_nonneg fun _ _ => by split_ifs <;> [exact hprob_nn b; exact le_rfl]
        have h2 : 0 ≤ if F2 b then bernProb (gridP L G) b else 0 := by split_ifs <;> [exact hprob_nn b; exact le_rfl]
        have h3 : 0 ≤ if F3 b then bernProb (gridP L G) b else 0 := by split_ifs <;> [exact hprob_nn b; exact le_rfl]
        have h4 : 0 ≤ if F4 b then bernProb (gridP L G) b else 0 := by split_ifs <;> [exact hprob_nn b; exact le_rfl]
        linarith
      · rw [if_pos hg]
        unfold isGoodB1 at hg
        push Not at hg
        have hnn1 : 0 ≤ ∑ j ∈ Icc 0 1000, if F1 j b then bernProb (gridP L G) b else 0 :=
          sum_nonneg fun _ _ => by split_ifs <;> [exact hprob_nn b; exact le_rfl]
        have hnn2 : 0 ≤ if F2 b then bernProb (gridP L G) b else 0 := by split_ifs <;> [exact hprob_nn b; exact le_rfl]
        have hnn3 : 0 ≤ if F3 b then bernProb (gridP L G) b else 0 := by split_ifs <;> [exact hprob_nn b; exact le_rfl]
        have hnn4 : 0 ≤ if F4 b then bernProb (gridP L G) b else 0 := by split_ifs <;> [exact hprob_nn b; exact le_rfl]
        by_cases h1 : ∃ j ∈ Icc 0 1000, F1 j b
        · obtain ⟨j₀, hj₀, hF1j₀⟩ := h1
          have hge : bernProb (gridP L G) b ≤ ∑ j ∈ Icc 0 1000, if F1 j b then bernProb (gridP L G) b else 0 := by
            calc bernProb (gridP L G) b = if F1 j₀ b then bernProb (gridP L G) b else 0 := (if_pos hF1j₀).symm
              _ ≤ _ := single_le_sum (f := fun j => if F1 j b then bernProb (gridP L G) b else 0)
                  (fun j _ => by by_cases hF : F1 j b <;> simp [hF, hprob_nn b]) hj₀
          linarith
        · push Not at h1
          have hc1 : ∀ j ∈ Icc 0 1000, ((activeSet b ∩ (binsLe L G (uCk L j) \ resBins G)).card : ℝ) ≤
              ((j : ℝ) / 1000 + 2 / 1000) * log L := fun j hj => not_lt.mp (h1 j hj)
          have hrem := hg hc1
          by_cases h2 : F2 b
          · rw [if_pos h2]; linarith
          · have hc2 : (997 / 1000 : ℝ) * log L ≤
                ((activeSet b ∩ (binsLe L G (L / 10) \ resBins G)).card : ℝ) := not_lt.mp h2
            have hrem2 := hrem hc2
            by_cases h3 : F3 b
            · rw [if_pos h3]; linarith
            · have hc3 : subSum (xHi L G) (activeSet b ∩ (binsLe L G (L / 10) \ resBins G)) ≤ L := not_lt.mp h3
              have h4 : F4 b := hrem2 hc3
              rw [if_pos h4]; linarith
    calc ∑ b : Fin G → Bool, (if ¬isGoodB1 L G b then bernProb (gridP L G) b else 0)
        ≤ ∑ b : Fin G → Bool, ((∑ j ∈ Icc 0 1000, if F1 j b then bernProb (gridP L G) b else 0) +
            (if F2 b then bernProb (gridP L G) b else 0) +
            (if F3 b then bernProb (gridP L G) b else 0) +
            (if F4 b then bernProb (gridP L G) b else 0)) := sum_le_sum fun b _ => hpt b
      _ = (∑ j ∈ Icc 0 1000, ∑ b : Fin G → Bool, if F1 j b then bernProb (gridP L G) b else 0) +
          (∑ b : Fin G → Bool, if F2 b then bernProb (gridP L G) b else 0) +
          (∑ b : Fin G → Bool, if F3 b then bernProb (gridP L G) b else 0) +
          (∑ b : Fin G → Bool, if F4 b then bernProb (gridP L G) b else 0) := by
            simp only [sum_add_distrib]
            rw [sum_comm]
      _ ≤ (∑ _j ∈ Icc 0 1000, (1 : ℝ) / 10000) + 1 / 10 + 1 / 10 + 1 / 10 := by
            have hsum1 := sum_le_sum hF1
            linarith [hF2, hF3, hF4]
      _ ≤ 1 / 2 := by
            rw [sum_const, Nat.card_Icc]; norm_num
  have hpart : (∑ b : Fin G → Bool, if isGoodB1 L G b then bernProb (gridP L G) b else 0) +
      (∑ b : Fin G → Bool, if ¬isGoodB1 L G b then bernProb (gridP L G) b else 0) = 1 := by
    rw [← sum_add_distrib, ← hsum_all]
    refine sum_congr rfl fun b _ => by split_ifs <;> ring
  linarith

/-- Lower bound on `E[1_typ * uPairs]`:
for large `L` and fine enough `G`, with `η = L ^ (-(1/40))`,
`∑ b, bernProb p b * (if isTyp b then uPairs.card else 0) ≥ L ^ (7/100) / 384000`. -/
lemma expected_uPairs_typ_ge {L : ℝ} {G : ℕ}
    (hL : exp 10000000000 ≤ L) (hG : 0 < G)
    (hstep : 2000 * L * gridDelta L G ≤ L ^ (-(1 / 40 : ℝ)) / 4) :
    L ^ (7 / 100 : ℝ) / 384000 ≤
      ∑ b : Fin G → Bool, bernProb (gridP L G) b *
        (if isTyp L G b then ((uPairs L G (L ^ (-(1 / 40 : ℝ))) b).card : ℝ) else 0) := by
  set η : ℝ := L ^ (-(1 / 40 : ℝ))
  have hlogL_ge : (10000000000 : ℝ) ≤ log L := by
    have := log_le_log (exp_pos _) hL
    rwa [log_exp] at this
  have hLpos : 0 < L := lt_of_lt_of_le (exp_pos _) hL
  have hL1 : 1 < L := (log_pos_iff hLpos.le).mp (by linarith)
  have hL10 : 10 ≤ L := by
    have : (10 : ℝ) ≤ exp 10000000000 := by linarith [add_one_le_exp (10000000000 : ℝ)]
    linarith
  have hηpos : 0 < η := rpow_pos_of_pos hLpos _
  have hηle : η ≤ 1 / 2 := by
    unfold η
    rw [rpow_def_of_pos hLpos]
    have h1 : log L * -(1 / 40 : ℝ) ≤ -2 := by linarith
    have h2 : exp (-2) ≤ 1 / 2 := by
      rw [exp_neg, one_div]
      exact inv_anti₀ (by norm_num) (by linarith [add_one_le_exp (2 : ℝ)])
    exact le_trans (exp_le_exp.mpr h1) h2
  have hΔle : gridDelta L G ≤ 1 / 1000000 := by
    have : 2000 * L * gridDelta L G ≤ 1 / 8 := by linarith
    have : (100000 : ℝ) ≤ L := by linarith [add_one_le_exp (10000000000 : ℝ)]
    nlinarith
  have hΔpos := gridDelta_pos hL1 hG
  have hp := gridP_bounds hL1 hG (by linarith)
  have hprob_nn : ∀ b : Fin G → Bool, 0 ≤ bernProb (gridP L G) b := fun b => bernProb_nonneg hp.2.2.1.le hp.2.2.2.le b
  -- For any `b` with `isGoodB1 L G b` and `(activeSet b ∩ resBins G).card ≤ 0.003 * log L`, `isTyp L G b` holds!
  let isGoodB2 (b : Fin G → Bool) : Prop :=
    ((activeSet b ∩ resBins G).card : ℝ) ≤ (3 / 1000 : ℝ) * log L
  have htyp_of : ∀ b, isGoodB1 L G b → isGoodB2 b → isTyp L G b := by
    intro b h1 h2 j hj
    have hsub : activeSet b ∩ binsLe L G (uCk L j) ⊆
        (activeSet b ∩ (binsLe L G (uCk L j) \ resBins G)) ∪ (activeSet b ∩ resBins G) := by
      intro r hr
      rcases mem_inter.mp hr with ⟨hrb, hru⟩
      by_cases hr2 : r ∈ resBins G
      · exact mem_union_right _ (mem_inter.mpr ⟨hrb, hr2⟩)
      · exact mem_union_left _ (mem_inter.mpr ⟨hrb, mem_sdiff.mpr ⟨hru, hr2⟩⟩)
    have hcard : ((activeSet b ∩ binsLe L G (uCk L j)).card : ℝ) ≤
        ((activeSet b ∩ (binsLe L G (uCk L j) \ resBins G)).card : ℝ) +
        ((activeSet b ∩ resBins G).card : ℝ) := by
      exact_mod_cast le_trans (card_le_card hsub) (card_union_le _ _)
    have hc1 := h1.1 j hj
    unfold isGoodB2 at h2
    linarith
  -- For any fixed `b`, count triples `(I, J, r₀)` where `I, J ⊆ activeSet b ∩ (binsLe(L/10) \ resBins G)` disjoint,
  -- `1 + η ≤ subSum J - subSum I`, `r₀ ∈ activeSet b ∩ resBins G`, and `subSum J - subSum I - η ≤ xHi r₀ < subSum J - subSum I - η/2`.
  -- Each such triple injects into `uPairs L G η b` via `(insert r₀ I, J)`!
  let Aset (b : Fin G → Bool) : Finset (Fin G) := activeSet b ∩ (binsLe L G (L / 10) \ resBins G)
  let basePairs (b : Fin G → Bool) : Finset (Finset (Fin G) × Finset (Fin G)) :=
    ((Aset b).powerset ×ˢ (Aset b).powerset).filter fun IJ =>
      Disjoint IJ.1 IJ.2 ∧ 1 + η ≤ subSum (xHi L G) IJ.2 - subSum (xHi L G) IJ.1
  let winBins (IJ : Finset (Fin G) × Finset (Fin G)) : Finset (Fin G) :=
    (resBins G).filter fun r₀ =>
      subSum (xHi L G) IJ.2 - subSum (xHi L G) IJ.1 - η ≤ xHi L G r₀ ∧
      xHi L G r₀ < subSum (xHi L G) IJ.2 - subSum (xHi L G) IJ.1 - η / 2
  have hpt_uPairs : ∀ b : Fin G → Bool, isGoodB1 L G b → isGoodB2 b →
      (∑ IJ ∈ basePairs b, ∑ r₀ ∈ winBins IJ, if b r₀ then (1 : ℝ) else 0) ≤
        ((uPairs L G η b).card : ℝ) := by
    intro b h1 _h2
    have hsum_eq : (∑ IJ ∈ basePairs b, ∑ r₀ ∈ winBins IJ, if b r₀ then (1 : ℝ) else 0) =
        (((basePairs b).sigma fun IJ => (winBins IJ).filter fun r₀ => b r₀ = true).card : ℝ) := by
      rw [card_sigma, Nat.cast_sum]
      refine sum_congr rfl fun IJ _ => ?_
      rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
    rw [hsum_eq]
    norm_cast
    refine card_le_card_of_injOn (fun p => (insert p.2 p.1.1, p.1.2)) ?_ ?_
    · intro ⟨⟨I, J⟩, r₀⟩ hp
      simp only [mem_coe, mem_sigma, basePairs, winBins, mem_filter,
          mem_product, mem_powerset] at hp
      obtain ⟨⟨⟨hIA, hJA⟩, hdisj, hdiff⟩, ⟨hr₀res, hlo, hhi⟩, hbr₀⟩ := hp
      have hIsub : I ⊆ activeSet b := Subset.trans hIA inter_subset_left
      have hJsub : J ⊆ activeSet b := Subset.trans hJA inter_subset_left
      have hr₀act : r₀ ∈ activeSet b := mem_filter.mpr ⟨mem_univ _, hbr₀⟩
      have hr₀notI : r₀ ∉ I := fun h => (mem_sdiff.mp (mem_inter.mp (hIA h)).2).2 hr₀res
      have hr₀notJ : r₀ ∉ J := fun h => (mem_sdiff.mp (mem_inter.mp (hJA h)).2).2 hr₀res
      simp only [mem_coe, uPairs, mem_filter, mem_product, mem_powerset]
      refine ⟨⟨insert_subset_iff.mpr ⟨hr₀act, hIsub⟩, hJsub⟩,
        disjoint_insert_left.mpr ⟨hr₀notJ, hdisj⟩, ?_, ?_, ?_⟩
      · calc subSum (xHi L G) J ≤ subSum (xHi L G) (Aset b) :=
              sum_le_sum_of_subset_of_nonneg hJA fun r _ _ => (xHi_nonneg hL1 hG r)
          _ ≤ L := h1.2.2.1
      · unfold subSum at hlo hhi ⊢
        rw [sum_insert hr₀notI]
        linarith
      · unfold subSum at hlo hhi ⊢
        rw [sum_insert hr₀notI]
        linarith
    · intro ⟨⟨I₁, J₁⟩, r₁⟩ hp₁ ⟨⟨I₂, J₂⟩, r₂⟩ hp₂ heq
      simp only [mem_coe, mem_sigma, basePairs, winBins, mem_filter,
          mem_product, mem_powerset] at hp₁ hp₂
      simp only [Prod.mk.injEq] at heq
      obtain ⟨hIins, rfl⟩ := heq
      have hr₁res : r₁ ∈ resBins G := hp₁.2.1.1
      have hr₂res : r₂ ∈ resBins G := hp₂.2.1.1
      have hI₁nores : ∀ r ∈ I₁, r ∉ resBins G := fun r hr =>
        (mem_sdiff.mp (mem_inter.mp (hp₁.1.1.1 hr)).2).2
      have hI₂nores : ∀ r ∈ I₂, r ∉ resBins G := fun r hr =>
        (mem_sdiff.mp (mem_inter.mp (hp₂.1.1.1 hr)).2).2
      have hr_eq : r₁ = r₂ := by
        have hmem : r₁ ∈ insert r₂ I₂ := hIins ▸ mem_insert_self r₁ I₁
        rcases mem_insert.mp hmem with rfl | hr1I2
        · rfl
        · exact absurd hr₁res (hI₂nores r₁ hr1I2)
      subst hr_eq
      have hIeq : I₁ = I₂ := by
        have hr1not1 : r₁ ∉ I₁ := fun h => hI₁nores r₁ h hr₁res
        have hr1not2 : r₁ ∉ I₂ := fun h => hI₂nores r₁ h hr₁res
        have := congr_arg (fun S => S.erase r₁) hIins
        simpa [erase_insert hr1not1, erase_insert hr1not2] using this
      subst hIeq; rfl
  -- Now for any single `r₀ ∈ resBins G`, compute `E[1_{b r₀ = true ∧ isGoodB2 b}] ≥ gridP L G / 2`!
  have hB2_single : ∀ r₀ ∈ resBins G,
      gridP L G / 2 ≤ ∑ b : Fin G → Bool, bernProb (gridP L G) b *
        (if b r₀ = true ∧ isGoodB2 b then (1 : ℝ) else 0) := by
    intro r₀ hr₀
    let S_other := (resBins G).erase r₀
    let F_r₀ : (Fin G → Bool) → ℝ := fun b => if b r₀ = true then 1 else 0
    let H_other : (Fin G → Bool) → ℝ := fun b =>
      if ((activeSet b ∩ S_other).card : ℝ) ≤ (3 / 1000 : ℝ) * log L - 1 then 1 else 0
    have hpt_ge : ∀ b : Fin G → Bool,
        F_r₀ b * H_other b ≤ if b r₀ = true ∧ isGoodB2 b then (1 : ℝ) else 0 := by
      intro b
      unfold F_r₀ H_other
      by_cases h1 : b r₀ = true
      · by_cases h2 : ((activeSet b ∩ S_other).card : ℝ) ≤ (3 / 1000 : ℝ) * log L - 1
        · have hg2 : isGoodB2 b := by
            unfold isGoodB2
            have hsub : activeSet b ∩ resBins G ⊆ insert r₀ (activeSet b ∩ S_other) := by
              intro r hr
              rcases mem_inter.mp hr with ⟨hrb, hrres⟩
              by_cases heq : r = r₀
              · subst heq; exact mem_insert_self _ _
              · exact mem_insert_of_mem (mem_inter.mpr ⟨hrb, mem_erase.mpr ⟨heq, hrres⟩⟩)
            have hcard : ((activeSet b ∩ resBins G).card : ℝ) ≤ ((activeSet b ∩ S_other).card : ℝ) + 1 := by
              exact_mod_cast le_trans (card_le_card hsub) (card_insert_le _ _)
            linarith
          simp [h1, h2, hg2]
        · simp only [if_pos h1, if_neg h2, mul_zero]; split_ifs <;> norm_num
      · simp only [if_neg h1, zero_mul]; split_ifs <;> norm_num
    have hsplit := sum_bernProb_indep_split (gridP L G) ({r₀} : Finset (Fin G)) H_other F_r₀
      (fun b₁ b₂ heq => by
        have hinter : activeSet b₁ ∩ S_other = activeSet b₂ ∩ S_other := by
          ext r; simp only [activeSet, S_other, mem_inter, mem_filter, mem_univ,
              true_and, mem_erase]
          constructor <;> rintro ⟨hb, hne, hr⟩ <;> refine ⟨?_, hne, hr⟩
          · rwa [← heq r (by simp [hne])]
          · rwa [heq r (by simp [hne])]
        simp [H_other, hinter])
      (fun b₁ b₂ heq => by simp [F_r₀, heq r₀ (mem_singleton_self r₀)])
    have hF_eval : ∑ b : Fin G → Bool, bernProb (gridP L G) b * F_r₀ b = gridP L G :=
      sum_bernProb_indicator (gridP L G) r₀
    have hH_eval : (1 : ℝ) / 2 ≤ ∑ b : Fin G → Bool, bernProb (gridP L G) b * H_other b := by
      -- By Markov on `|activeSet b ∩ S_other|`: mean `≤ 0.0011 * log L`, threshold `0.003 * log L - 1 ≥ 0.0025 * log L`.
      have hmean : gridP L G * (S_other.card : ℝ) ≤ (11 / 10000 : ℝ) * log L := by
        have hsub : (S_other.card : ℝ) ≤ ((resBins G).card : ℝ) := by
          exact_mod_cast card_le_card (erase_subset r₀ _)
        have hres := resBins_card_le G
        have hGΔ : (G : ℝ) * gridDelta L G = log L := by
          unfold gridDelta; field_simp [(show (G : ℝ) ≠ 0 by positivity)]
        calc gridP L G * (S_other.card : ℝ)
            ≤ gridDelta L G * ((G : ℝ) / 1000 + 1) :=
              mul_le_mul hp.2.1 (le_trans hsub hres) (Nat.cast_nonneg _) hΔpos.le
          _ = ((G : ℝ) * gridDelta L G) / 1000 + gridDelta L G := by ring
          _ = log L / 1000 + gridDelta L G := by rw [hGΔ]
          _ ≤ (11 / 10000 : ℝ) * log L := by linarith
      set Tthr : ℝ := (3 / 1000 : ℝ) * log L - 1
      have hTthr : (25 / 10000 : ℝ) * log L ≤ Tthr := by unfold Tthr; linarith
      have hTpos : 0 < Tthr := by linarith
      have hfail : Tthr * (∑ b : Fin G → Bool, bernProb (gridP L G) b * (1 - H_other b)) ≤
          gridP L G * (S_other.card : ℝ) := by
        rw [← sum_bernProb_card_inter (gridP L G) S_other, mul_sum]
        refine sum_le_sum fun b _ => ?_
        unfold H_other
        split_ifs with h
        · simp; exact mul_nonneg (hprob_nn b) (Nat.cast_nonneg _)
        · push Not at h
          have : Tthr * (bernProb (gridP L G) b * (1 - 0)) = bernProb (gridP L G) b * Tthr := by ring
          rw [this]
          exact mul_le_mul_of_nonneg_left h.le (hprob_nn b)
      have hfail_half : ∑ b : Fin G → Bool, bernProb (gridP L G) b * (1 - H_other b) ≤ 1 / 2 := by
        have h1 : Tthr * (∑ b : Fin G → Bool, bernProb (gridP L G) b * (1 - H_other b)) ≤ Tthr * (1 / 2) := by
          linarith
        exact le_of_mul_le_mul_left h1 hTpos
      have hsum1 : (∑ b : Fin G → Bool, bernProb (gridP L G) b * H_other b) +
          (∑ b : Fin G → Bool, bernProb (gridP L G) b * (1 - H_other b)) = 1 := by
        calc (∑ b : Fin G → Bool, bernProb (gridP L G) b * H_other b) +
              (∑ b : Fin G → Bool, bernProb (gridP L G) b * (1 - H_other b))
            = ∑ b : Fin G → Bool, bernProb (gridP L G) b := by
                rw [← sum_add_distrib]
                refine sum_congr rfl fun b _ => by ring
          _ = 1 := sum_bernProb (G := G) (gridP L G)
      linarith
    calc gridP L G / 2
        = (1 / 2) * gridP L G := by ring
      _ ≤ (∑ b : Fin G → Bool, bernProb (gridP L G) b * H_other b) *
          (∑ b : Fin G → Bool, bernProb (gridP L G) b * F_r₀ b) := by
            rw [hF_eval]; exact mul_le_mul_of_nonneg_right hH_eval hp.2.2.1.le
      _ = ∑ b : Fin G → Bool, bernProb (gridP L G) b * (H_other b * F_r₀ b) := hsplit.symm
      _ ≤ ∑ b : Fin G → Bool, bernProb (gridP L G) b * (if b r₀ = true ∧ isGoodB2 b then (1 : ℝ) else 0) := by
            refine sum_le_sum fun b _ => mul_le_mul_of_nonneg_left ?_ (hprob_nn b)
            rw [mul_comm]; exact hpt_ge b
  -- Now put `S₁` and `S₂` together via `sum_bernProb_indep_split` with `resBins G`!
  -- For each `r₀ ∈ resBins G`, let `F₁(r₀, b) = if isGoodB1 b then #{IJ ∈ basePairs b | r₀ ∈ winBins IJ} else 0`
  -- and `H₂(r₀, b) = if b r₀ = true ∧ isGoodB2 b then 1 else 0`.
  let F₁ (r₀ : Fin G) (b : Fin G → Bool) : ℝ :=
    if isGoodB1 L G b then (((basePairs b).filter fun IJ => r₀ ∈ winBins IJ).card : ℝ) else 0
  let H₂ (r₀ : Fin G) (b : Fin G → Bool) : ℝ :=
    if b r₀ = true ∧ isGoodB2 b then 1 else 0
  have hpt_main : ∀ b : Fin G → Bool,
      (∑ r₀ ∈ resBins G, F₁ r₀ b * H₂ r₀ b) ≤
        if isTyp L G b then ((uPairs L G η b).card : ℝ) else 0 := by
    intro b
    by_cases h1 : isGoodB1 L G b
    · by_cases h2 : isGoodB2 b
      · rw [if_pos (htyp_of b h1 h2)]
        have hrew : ∑ r₀ ∈ resBins G, F₁ r₀ b * H₂ r₀ b =
            ∑ IJ ∈ basePairs b, ∑ r₀ ∈ winBins IJ, if b r₀ then (1 : ℝ) else 0 := by
          have h1' : ∀ r₀ ∈ resBins G, F₁ r₀ b * H₂ r₀ b =
              ∑ IJ ∈ basePairs b, if r₀ ∈ winBins IJ ∧ b r₀ = true then (1 : ℝ) else 0 := by
            intro r₀ _
            simp only [F₁, H₂, if_pos h1, h2, and_true]
            by_cases hbr : b r₀ = true
            · simp [hbr]
            · simp [hbr]
          rw [sum_congr rfl h1', sum_comm]
          refine sum_congr rfl fun IJ _ => ?_
          rw [← sum_filter]
          have hfilt : (resBins G).filter (fun r₀ => r₀ ∈ winBins IJ ∧ b r₀ = true) =
              (winBins IJ).filter (fun r₀ => b r₀ = true) := by
            ext r₀; simp only [mem_filter, winBins]; tauto
          rw [hfilt, sum_filter]
        rw [hrew]
        exact hpt_uPairs b h1 h2
      · have hzero : ∀ r₀ ∈ resBins G, F₁ r₀ b * H₂ r₀ b = 0 := fun r₀ _ => by simp [H₂, h2]
        rw [sum_eq_zero hzero]
        split_ifs <;> positivity
    · have hzero : ∀ r₀ ∈ resBins G, F₁ r₀ b * H₂ r₀ b = 0 := fun r₀ _ => by simp [F₁, h1]
      rw [sum_eq_zero hzero]
      split_ifs <;> positivity
  have hdepF₁ : ∀ r₀ ∈ resBins G, ∀ b₁ b₂ : Fin G → Bool, (∀ r ∉ resBins G, b₁ r = b₂ r) →
      F₁ r₀ b₁ = F₁ r₀ b₂ := by
    intro r₀ _ b₁ b₂ heq
    have hAeq : Aset b₁ = Aset b₂ := by
      ext r; simp only [Aset, activeSet, mem_inter, mem_filter, mem_univ, true_and, mem_sdiff]
      constructor <;> rintro ⟨hb, hL', hnr⟩ <;> refine ⟨?_, hL', hnr⟩
      · rwa [← heq r hnr]
      · rwa [heq r hnr]
    have hbp : basePairs b₁ = basePairs b₂ := by simp only [basePairs, hAeq]
    have hiff := isGoodB1_depends_S1 L G b₁ b₂ heq
    simp only [F₁, hiff, hbp]
  have hdepH₂ : ∀ r₀ ∈ resBins G, ∀ b₁ b₂ : Fin G → Bool, (∀ r ∈ resBins G, b₁ r = b₂ r) →
      H₂ r₀ b₁ = H₂ r₀ b₂ := by
    intro r₀ hr₀ b₁ b₂ heq
    have hinter : activeSet b₁ ∩ resBins G = activeSet b₂ ∩ resBins G := by
      ext r; simp only [activeSet, mem_inter, mem_filter, mem_univ, true_and]
      constructor <;> rintro ⟨hb, hr⟩ <;> refine ⟨?_, hr⟩
      · rwa [← heq r hr]
      · rwa [heq r hr]
    simp only [H₂, isGoodB2, hinter, heq r₀ hr₀]
  have hstep1 : (∑ r₀ ∈ resBins G, (gridP L G / 2) * ∑ b : Fin G → Bool, bernProb (gridP L G) b * F₁ r₀ b) ≤
      ∑ b : Fin G → Bool, bernProb (gridP L G) b *
        (if isTyp L G b then ((uPairs L G η b).card : ℝ) else 0) := by
    calc _ ≤ ∑ r₀ ∈ resBins G, (∑ b : Fin G → Bool, bernProb (gridP L G) b * F₁ r₀ b) *
              (∑ b : Fin G → Bool, bernProb (gridP L G) b * H₂ r₀ b) := by
            refine sum_le_sum fun r₀ hr₀ => ?_
            rw [mul_comm]
            refine mul_le_mul_of_nonneg_left (hB2_single r₀ hr₀) ?_
            exact sum_nonneg fun b _ => mul_nonneg (hprob_nn b) (by unfold F₁; split_ifs <;> positivity)
      _ = ∑ r₀ ∈ resBins G, ∑ b : Fin G → Bool, bernProb (gridP L G) b * (F₁ r₀ b * H₂ r₀ b) := by
            refine sum_congr rfl fun r₀ hr₀ =>
              (sum_bernProb_indep_split (gridP L G) (resBins G) (F₁ r₀) (H₂ r₀)
                (hdepF₁ r₀ hr₀) (hdepH₂ r₀ hr₀)).symm
      _ = ∑ b : Fin G → Bool, bernProb (gridP L G) b * (∑ r₀ ∈ resBins G, F₁ r₀ b * H₂ r₀ b) := by
            rw [sum_comm]
            refine sum_congr rfl fun b _ => by rw [mul_sum]
      _ ≤ _ := sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hpt_main b) (hprob_nn b)
  -- Now evaluate the LHS by swapping `∑ r₀` inside `∑ b`:
  have hLHS_rew : ∑ r₀ ∈ resBins G, (gridP L G / 2) * ∑ b : Fin G → Bool, bernProb (gridP L G) b * F₁ r₀ b =
      ∑ b : Fin G → Bool, if isGoodB1 L G b then
        bernProb (gridP L G) b * ((1 / 2 : ℝ) * ∑ IJ ∈ basePairs b, gridP L G * ((winBins IJ).card : ℝ))
      else 0 := by
    have h1 : ∀ r₀ ∈ resBins G, (gridP L G / 2) * ∑ b : Fin G → Bool, bernProb (gridP L G) b * F₁ r₀ b =
        ∑ b : Fin G → Bool, bernProb (gridP L G) b * ((gridP L G / 2) * F₁ r₀ b) := fun r₀ _ => by
      rw [mul_sum]; refine sum_congr rfl fun b _ => by ring
    rw [sum_congr rfl h1, sum_comm]
    refine sum_congr rfl fun b _ => ?_
    by_cases h1b : isGoodB1 L G b
    · rw [if_pos h1b, ← mul_sum]
      congr 1
      have h2 : ∑ r₀ ∈ resBins G, (gridP L G / 2) * F₁ r₀ b =
          (1 / 2 : ℝ) * (gridP L G * ∑ r₀ ∈ resBins G, (((basePairs b).filter fun IJ => r₀ ∈ winBins IJ).card : ℝ)) := by
        rw [← mul_sum]; simp only [F₁, if_pos h1b]; ring
      rw [h2]
      congr 1
      have hswap : ∑ r₀ ∈ resBins G, (((basePairs b).filter fun IJ => r₀ ∈ winBins IJ).card : ℝ) =
          ∑ IJ ∈ basePairs b, ((winBins IJ).card : ℝ) := by
        have hcast : ∀ r₀ ∈ resBins G, (((basePairs b).filter fun IJ => r₀ ∈ winBins IJ).card : ℝ) =
            ∑ IJ ∈ basePairs b, if r₀ ∈ winBins IJ then (1 : ℝ) else 0 := fun r₀ _ => by
          rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
        rw [sum_congr rfl hcast, sum_comm]
        refine sum_congr rfl fun IJ _ => ?_
        rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
        congr 1; congr 1; ext r₀; simp [winBins]
      rw [hswap, mul_sum]
    · rw [if_neg h1b]
      exact sum_eq_zero fun r₀ _ => by simp [F₁, h1b]
  -- For every `b` with `isGoodB1 L G b`, lower bound `(1/2) * ∑ IJ ∈ basePairs b, gridP * (winBins IJ).card`:
  have hinner_ge : ∀ b : Fin G → Bool, isGoodB1 L G b →
      L ^ (7 / 100 : ℝ) / 192000 ≤ (1 / 2 : ℝ) * ∑ IJ ∈ basePairs b, gridP L G * ((winBins IJ).card : ℝ) := by
    intro b h1b
    have hwin_ge : ∀ IJ ∈ basePairs b, η / (16000 * L) ≤ gridP L G * ((winBins IJ).card : ℝ) := by
      intro IJ hIJ
      simp only [basePairs, mem_filter, mem_product, mem_powerset] at hIJ
      have hDL : subSum (xHi L G) IJ.2 - subSum (xHi L G) IJ.1 ≤ L := by
        have hJle : subSum (xHi L G) IJ.2 ≤ L :=
          le_trans (sum_le_sum_of_subset_of_nonneg hIJ.1.2 fun r _ _ => (xHi_nonneg hL1 hG r))
            h1b.2.2.1
        have hInn : 0 ≤ subSum (xHi L G) IJ.1 :=
          sum_nonneg fun r _ => (xHi_nonneg hL1 hG r)
        linarith
      exact card_resBins_in_window hL10 hG hηpos hηle hIJ.2.2 hDL hstep
    obtain ⟨r₀, hr₀A, hx₀⟩ := h1b.2.2.2
    have hbp_ge : (3 : ℝ) ^ (Aset b).card / 6 ≤ ((basePairs b).card : ℝ) :=
      card_large_diff_disjoint_pairs (xHi L G) (Aset b) hr₀A hx₀ hηle
    have h3pow : L ^ (1095 / 1000 : ℝ) ≤ (3 : ℝ) ^ (Aset b).card := by
      rw [rpow_def_of_pos hLpos, ← rpow_natCast, rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
      apply exp_le_exp.mpr
      have hlog3 : (1.0986 : ℝ) < log 3 := lt_trans (by norm_num) log_three_gt_d9
      have hcard : (997 / 1000 : ℝ) * log L ≤ ((Aset b).card : ℝ) := h1b.2.1
      nlinarith
    have hsum_ge : ((basePairs b).card : ℝ) * (η / (16000 * L)) ≤
        ∑ IJ ∈ basePairs b, gridP L G * ((winBins IJ).card : ℝ) := by
      calc _ = ∑ _IJ ∈ basePairs b, (η / (16000 * L)) := by rw [sum_const, nsmul_eq_mul]
        _ ≤ _ := sum_le_sum hwin_ge
    have hpow_comb : L ^ (7 / 100 : ℝ) ≤ L ^ (1095 / 1000 : ℝ) * η / L := by
      unfold η
      rw [← rpow_add hLpos, ← rpow_sub_one hLpos.ne']
      exact rpow_le_rpow_of_exponent_le hL1.le (by norm_num)
    have h1 : (L ^ (1095 / 1000 : ℝ) / 6) * (η / (16000 * L)) ≤
        ((basePairs b).card : ℝ) * (η / (16000 * L)) :=
      mul_le_mul_of_nonneg_right (le_trans (div_le_div_of_nonneg_right h3pow (by norm_num)) hbp_ge) (by positivity)
    have h2 : (1 / 2 : ℝ) * ((L ^ (1095 / 1000 : ℝ) / 6) * (η / (16000 * L))) =
        (L ^ (1095 / 1000 : ℝ) * η / L) / 192000 := by ring
    linarith [h1, h2, hsum_ge, div_le_div_of_nonneg_right hpow_comb (by norm_num : (0 : ℝ) ≤ 192000)]
  -- Integrate over `b` using `prob_isGoodB1_ge_half`:
  have hprob_half := prob_isGoodB1_ge_half hL hG hΔle
  have hLHS_ge : L ^ (7 / 100 : ℝ) / 384000 ≤
      ∑ b : Fin G → Bool, if isGoodB1 L G b then
        bernProb (gridP L G) b * ((1 / 2 : ℝ) * ∑ IJ ∈ basePairs b, gridP L G * ((winBins IJ).card : ℝ))
      else 0 := by
    calc L ^ (7 / 100 : ℝ) / 384000
        = (L ^ (7 / 100 : ℝ) / 192000) * (1 / 2) := by ring
      _ ≤ (L ^ (7 / 100 : ℝ) / 192000) *
          (∑ b : Fin G → Bool, if isGoodB1 L G b then bernProb (gridP L G) b else 0) :=
            mul_le_mul_of_nonneg_left hprob_half (by positivity)
      _ = ∑ b : Fin G → Bool, if isGoodB1 L G b then
            bernProb (gridP L G) b * (L ^ (7 / 100 : ℝ) / 192000) else 0 := by
            rw [mul_sum]; refine sum_congr rfl fun b _ => by split_ifs <;> ring
      _ ≤ _ := sum_le_sum fun b _ => by
            split_ifs with h
            · exact mul_le_mul_of_nonneg_left (hinner_ge b h) (hprob_nn b)
            · exact le_rfl
  rw [hLHS_rew] at hstep1
  exact le_trans hLHS_ge hstep1

/- ## Section 6: Upper Bound on `E[1_typ * badTriples]` and Grid Existence -/

private lemma sum_union_le_of_nonneg {α : Type*} [DecidableEq α] {s t : Finset α} {f : α → ℝ}
    (hf : ∀ x ∈ s ∪ t, 0 ≤ f x) :
    ∑ x ∈ s ∪ t, f x ≤ (∑ x ∈ s, f x) + (∑ x ∈ t, f x) := by
  have h1 := sum_union_inter (s₁ := s) (s₂ := t) (f := f)
  have hinter : 0 ≤ ∑ x ∈ s ∩ t, f x :=
    sum_nonneg fun x hx => hf x (mem_union_left _ (mem_inter.mp hx).1)
  linarith

private lemma sum_biUnion_le_of_nonneg {ι α : Type*} [DecidableEq α]
    {I : Finset ι} {t : ι → Finset α} {f : α → ℝ}
    (hf : ∀ x ∈ I.biUnion t, 0 ≤ f x) :
    ∑ x ∈ I.biUnion t, f x ≤ ∑ i ∈ I, ∑ x ∈ t i, f x := by
  induction I using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [biUnion_insert, sum_insert hi]
    have h1 : ∑ x ∈ t i ∪ s.biUnion t, f x ≤ (∑ x ∈ t i, f x) + ∑ x ∈ s.biUnion t, f x :=
      sum_union_le_of_nonneg fun x hx => hf x (by rwa [biUnion_insert])
    have h2 : ∑ x ∈ s.biUnion t, f x ≤ ∑ j ∈ s, ∑ x ∈ t j, f x :=
      ih fun x hx => hf x (by rw [biUnion_insert]; exact mem_union_right _ hx)
    linarith

/-- Upper bound `((binsLe L G u).card : ℝ) * Δ ≤ log u` for every `1 ≤ u` (even if `u > L`). -/
lemma binsLe_card_mul_delta_le {L : ℝ} {G : ℕ} (hL : 1 < L) (hG : 0 < G) {u : ℝ} (hu1 : 1 ≤ u) :
    ((binsLe L G u).card : ℝ) * gridDelta L G ≤ log u := by
  by_cases huL : u ≤ L
  · exact (binsLe_card_mul_delta hL hG hu1 huL).2
  · push Not at huL
    have hsub : binsLe L G u ⊆ binsLe L G L := by
      intro r _; rw [binsLe_top hL hG]; exact mem_univ r
    have hcard : ((binsLe L G u).card : ℝ) ≤ ((binsLe L G L).card : ℝ) := by
      exact_mod_cast card_le_card hsub
    have hΔpos := gridDelta_pos hL hG
    calc ((binsLe L G u).card : ℝ) * gridDelta L G
        ≤ ((binsLe L G L).card : ℝ) * gridDelta L G := mul_le_mul_of_nonneg_right hcard hΔpos.le
      _ ≤ log L := (binsLe_card_mul_delta hL hG hL.le le_rfl).2
      _ ≤ log u := log_le_log (by linarith) huL.le

/-- Subset power sum over `binsLe L G u`: `∑_{R ⊆ binsLe L G u} (p / 3)^|R| ≤ u^(1/3)` for `1 ≤ u`. -/
lemma sum_pow_one_third_le {L : ℝ} {G : ℕ} (hL : 1 < L) (hG : 0 < G) (hΔ : gridDelta L G ≤ 1)
    {u : ℝ} (hu1 : 1 ≤ u) :
    ∑ R ∈ (binsLe L G u).powerset, (gridP L G / 3) ^ R.card ≤ u ^ (1 / 3 : ℝ) := by
  have hp := gridP_bounds hL hG hΔ
  have hprod : ∑ R ∈ (binsLe L G u).powerset, (gridP L G / 3) ^ R.card =
      (gridP L G / 3 + 1) ^ (binsLe L G u).card := by
    have h1 := prod_add (fun _ : Fin G => gridP L G / 3) (fun _ : Fin G => (1 : ℝ)) (binsLe L G u)
    rw [prod_const] at h1
    rw [h1]
    refine sum_congr rfl fun R _ => ?_
    rw [prod_const, prod_const_one, mul_one]
  rw [hprod]
  have hstep1 : gridP L G / 3 + 1 ≤ exp (gridDelta L G / 3) := by
    calc gridP L G / 3 + 1
        ≤ gridDelta L G / 3 + 1 := by linarith [hp.2.1]
      _ ≤ exp (gridDelta L G / 3) := add_one_le_exp _
  calc (gridP L G / 3 + 1) ^ (binsLe L G u).card
      ≤ (exp (gridDelta L G / 3)) ^ (binsLe L G u).card :=
          pow_le_pow_left₀ (by linarith [hp.2.2.1]) hstep1 _
    _ = exp (((binsLe L G u).card : ℝ) * (gridDelta L G / 3)) := by
          rw [← exp_nat_mul]
    _ ≤ exp (log u * (1 / 3 : ℝ)) := by
          apply exp_le_exp.mpr
          have hmul := binsLe_card_mul_delta_le hL hG hu1
          linarith
    _ = u ^ (1 / 3 : ℝ) := (rpow_def_of_pos (by linarith) (1 / 3 : ℝ)).symm

/-- Telescoping sum of `xHi r - xLo r` over all bins `r` with `xHi r ∈ [a, b]`:
always bounded by `(b - a) + gridP L G * L` when `a ≤ b`. -/
lemma sum_xHi_sub_xLo_in_interval {L : ℝ} {G : ℕ} (hL : 1 < L) (hG : 0 < G)
    {a b : ℝ} (hab : a ≤ b) :
    ∑ r ∈ univ.filter (fun r : Fin G => a ≤ xHi L G r ∧ xHi L G r ≤ b),
      (xHi L G r - xLo L G r) ≤ (b - a) + gridP L G * L := by
  set S := univ.filter (fun r : Fin G => a ≤ xHi L G r ∧ xHi L G r ≤ b)
  by_cases hne : S.Nonempty
  · set r₁ := S.min' hne
    set r₂ := S.max' hne
    have hr₁S : r₁ ∈ S := min'_mem S hne
    have hr₂S : r₂ ∈ S := max'_mem S hne
    have hle12 : r₁.val ≤ r₂.val := min'_le S r₂ hr₂S
    have hS_eq : S = univ.filter (fun r : Fin G => r₁.val ≤ r.val ∧ r.val ≤ r₂.val) := by
      ext r
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · intro hr
        exact ⟨min'_le S r hr, le_max' S r hr⟩
      · rintro ⟨h1, h2⟩
        have hr₁ab := (mem_filter.mp hr₁S).2
        have hr₂ab := (mem_filter.mp hr₂S).2
        have hm := (xHi_strictMono hL hG).monotone
        exact mem_filter.mpr ⟨mem_univ r,
          le_trans hr₁ab.1 (hm (show r₁ ≤ r from h1)),
          le_trans (hm (show r ≤ r₂ from h2)) hr₂ab.2⟩
    have hsum_eq : ∑ r ∈ S, (xHi L G r - xLo L G r) =
        ∑ k ∈ Icc r₁.val r₂.val, (exp (((k + 1 : ℕ) : ℝ) * gridDelta L G) -
          exp ((k : ℝ) * gridDelta L G)) := by
      rw [hS_eq]
      refine sum_nbij (fun r => r.val) ?_ ?_ ?_ ?_
      · intro r hr
        simp only [mem_coe, mem_filter, mem_univ, true_and] at hr
        exact mem_coe.mpr (mem_Icc.mpr hr)
      · intro r₁' _ r₂' _ h; exact Fin.ext h
      · intro k hk
        have hk' := mem_Icc.mp (mem_coe.mp hk)
        have hkG : k < G := lt_of_le_of_lt hk'.2 r₂.isLt
        refine ⟨⟨k, hkG⟩, ?_, rfl⟩
        simp only [mem_coe, mem_filter, mem_univ, true_and]
        exact hk'
      · intro r _; unfold xHi xLo; rfl
    have htel : ∀ d : ℕ, ∑ k ∈ Icc r₁.val (r₁.val + d),
        (exp (((k + 1 : ℕ) : ℝ) * gridDelta L G) -
          exp ((k : ℝ) * gridDelta L G)) =
        exp (((r₁.val + d + 1 : ℕ) : ℝ) * gridDelta L G) -
          exp ((r₁.val : ℝ) * gridDelta L G) := by
      intro d
      induction d with
      | zero => simp
      | succ d ih =>
        have hIcc : Icc r₁.val (r₁.val + (d + 1)) = insert (r₁.val + d + 1) (Icc r₁.val (r₁.val + d)) := by
          ext k; simp only [mem_Icc, mem_insert]; omega
        rw [hIcc, sum_insert (by simp only [mem_Icc]; omega), ih]
        have heq : r₁.val + (d + 1) + 1 = r₁.val + d + 1 + 1 := by omega
        rw [heq]; ring
    have htel_r2 : ∑ k ∈ Icc r₁.val r₂.val,
        (exp (((k + 1 : ℕ) : ℝ) * gridDelta L G) -
          exp ((k : ℝ) * gridDelta L G)) =
        xHi L G r₂ - xLo L G r₁ := by
      have hm := htel (r₂.val - r₁.val)
      have hadd : r₁.val + (r₂.val - r₁.val) = r₂.val := by omega
      rw [hadd] at hm
      exact hm
    rw [hsum_eq, htel_r2]
    have hr₁ab := (mem_filter.mp hr₁S).2
    have hr₂ab := (mem_filter.mp hr₂S).2
    have hr₁L := (xHi_gt_one_and_le hL hG r₁).2
    have hΔpos := gridDelta_pos hL hG
    have hp_pos : 0 ≤ gridP L G := by
      unfold gridP
      have : exp (-(gridDelta L G)) ≤ 1 := exp_le_one_iff.mpr (by linarith)
      linarith
    have hdiff : xHi L G r₂ - xLo L G r₁ =
        (xHi L G r₂ - xHi L G r₁) + gridP L G * xHi L G r₁ := by
      rw [← xHi_sub_xLo r₁]; ring
    rw [hdiff]
    have hmul : gridP L G * xHi L G r₁ ≤ gridP L G * L :=
      mul_le_mul_of_nonneg_left hr₁L hp_pos
    linarith
  · rw [not_nonempty_iff_eq_empty] at hne
    rw [hne, sum_empty]
    have hΔpos := gridDelta_pos hL hG
    have hp_pos : 0 ≤ gridP L G := by
      unfold gridP
      have : exp (-(gridDelta L G)) ≤ 1 := exp_le_one_iff.mpr (by linarith)
      linarith
    have hLpos : 0 ≤ L := by linarith
    nlinarith

/-- Window sum bound: for `u ≥ 1`, `0 < h ≤ 1/2`, and `gridP L G * L ≤ h`,
`∑_{R : subSum xHi R ∈ [u - h, u + h]} (p / 3)^|R| ≤ 4 * h * u^(-2/3)`. -/
lemma sum_pow_one_third_window {L : ℝ} {G : ℕ} (hL : 1 < L) (hG : 0 < G) (hΔ : gridDelta L G ≤ 1)
    {u h : ℝ} (hu1 : 1 ≤ u) (hhpos : 0 < h) (hhle : h ≤ 1 / 2)
    (hpL : gridP L G * L ≤ h) :
    ∑ R ∈ (univ : Finset (Fin G)).powerset.filter
        (fun R => u - h ≤ subSum (xHi L G) R ∧ subSum (xHi L G) R ≤ u + h),
      (gridP L G / 3) ^ R.card ≤ 4 * h * u ^ (-(2 / 3 : ℝ)) := by
  set p := gridP L G
  have hp := gridP_bounds hL hG hΔ
  set W := (univ : Finset (Fin G)).powerset.filter
    (fun R => u - h ≤ subSum (xHi L G) R ∧ subSum (xHi L G) R ≤ u + h)
  have hupos : 0 < u := by linarith
  have hstep1 : (u / 2) * ∑ R ∈ W, (p / 3) ^ R.card ≤
      ∑ R ∈ W, (p / 3) ^ R.card * subSum (xHi L G) R := by
    rw [mul_sum]
    refine sum_le_sum fun R hR => ?_
    have hlo : u - h ≤ subSum (xHi L G) R := (mem_filter.mp hR).2.1
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg (by linarith [hp.2.2.1]) _)
  -- Reindex `(R, r)` (`R ∈ W, r ∈ R`) to `(R', r)` (`R' ⊆ binsLe (u + h)`, `xHi r ∈ [u - h - subSum R', u + h - subSum R']`).
  have hstep2 : ∑ R ∈ W, (p / 3) ^ R.card * subSum (xHi L G) R ≤
      ∑ R' ∈ (binsLe L G (u + h)).powerset, (1 / 3 : ℝ) * (p / 3) ^ R'.card *
        ∑ r ∈ univ.filter (fun r : Fin G =>
            u - h - subSum (xHi L G) R' ≤ xHi L G r ∧ xHi L G r ≤ u + h - subSum (xHi L G) R'),
          (xHi L G r - xLo L G r) := by
    have hLHS : ∑ R ∈ W, (p / 3) ^ R.card * subSum (xHi L G) R =
        ∑ q ∈ W.sigma (fun R => R), (p / 3) ^ q.1.card * xHi L G q.2 := by
      rw [sum_sigma]
      refine sum_congr rfl fun R _ => by unfold subSum; rw [mul_sum]
    set S_big := (binsLe L G (u + h)).powerset.sigma fun R' =>
      univ.filter (fun r : Fin G =>
        u - h - subSum (xHi L G) R' ≤ xHi L G r ∧ xHi L G r ≤ u + h - subSum (xHi L G) R')
    have hRHS : ∑ R' ∈ (binsLe L G (u + h)).powerset, (1 / 3 : ℝ) * (p / 3) ^ R'.card *
          ∑ r ∈ univ.filter (fun r : Fin G =>
              u - h - subSum (xHi L G) R' ≤ xHi L G r ∧ xHi L G r ≤ u + h - subSum (xHi L G) R'),
            (xHi L G r - xLo L G r) =
        ∑ q ∈ S_big, (1 / 3 : ℝ) * (p / 3) ^ q.1.card * (xHi L G q.2 - xLo L G q.2) := by
      rw [sum_sigma]
      refine sum_congr rfl fun R' _ => by rw [mul_sum]
    rw [hLHS, hRHS]
    -- Injection `f : (R, r) ↦ (R.erase r, r)` from `W.sigma id` into `S_big`:
    let f : Sigma (fun _ : Finset (Fin G) => Fin G) → Sigma (fun _ : Finset (Fin G) => Fin G) :=
      fun q => ⟨q.1.erase q.2, q.2⟩
    have hf_maps : ∀ q ∈ W.sigma (fun R => R), f q ∈ S_big := by
      rintro ⟨R, r⟩ hq
      simp only [mem_sigma] at hq
      have hRW := (mem_filter.mp hq.1).2
      have hsum_er : subSum (xHi L G) (R.erase r) + xHi L G r = subSum (xHi L G) R := by
        unfold subSum; exact sum_erase_add R (xHi L G) hq.2
      simp only [f, S_big, mem_sigma, mem_powerset, mem_filter, mem_univ, true_and]
      refine ⟨?_, by linarith, by linarith⟩
      intro s hs
      have hsR : s ∈ R := mem_of_mem_erase hs
      simp only [binsLe, mem_filter, mem_univ, true_and]
      have hxle : xHi L G s ≤ subSum (xHi L G) R := by
        unfold subSum
        exact single_le_sum (fun t _ => (xHi_nonneg hL hG t)) hsR
      linarith
    have hf_inj : Set.InjOn f (W.sigma (fun R => R)) := by
      rintro ⟨R₁, r₁⟩ h₁ ⟨R₂, r₂⟩ h₂ heq
      simp only [mem_coe, mem_sigma] at h₁ h₂
      simp only [f, Sigma.mk.inj_iff] at heq
      obtain ⟨hR, hr⟩ := heq
      have hr' : r₁ = r₂ := eq_of_heq hr
      subst hr'
      have hReq : R₁ = R₂ := by
        rw [← insert_erase h₁.2, hR, insert_erase h₂.2]
      subst hReq; rfl
    have hf_val : ∀ q ∈ W.sigma (fun R => R),
        (p / 3) ^ q.1.card * xHi L G q.2 =
          (1 / 3 : ℝ) * (p / 3) ^ (f q).1.card * (xHi L G (f q).2 - xLo L G (f q).2) := by
      rintro ⟨R, r⟩ hq
      simp only [mem_sigma] at hq
      have hcard : R.card = (R.erase r).card + 1 := (card_erase_add_one hq.2).symm
      dsimp [f]
      rw [hcard, pow_succ, xHi_sub_xLo r]
      change (p / 3) ^ (R.erase r).card * (p / 3) * xHi L G r =
        1 / 3 * (p / 3) ^ (R.erase r).card * (p * xHi L G r)
      ring
    calc ∑ q ∈ W.sigma (fun R => R), (p / 3) ^ q.1.card * xHi L G q.2
        = ∑ q ∈ W.sigma (fun R => R), (1 / 3 : ℝ) * (p / 3) ^ (f q).1.card * (xHi L G (f q).2 - xLo L G (f q).2) :=
            sum_congr rfl hf_val
      _ = ∑ q ∈ (W.sigma (fun R => R)).image f,
            (1 / 3 : ℝ) * (p / 3) ^ q.1.card * (xHi L G q.2 - xLo L G q.2) :=
            (sum_image (f := fun q : Sigma (fun _ : Finset (Fin G) => Fin G) =>
              (1 / 3 : ℝ) * (p / 3) ^ q.1.card * (xHi L G q.2 - xLo L G q.2)) hf_inj).symm
      _ ≤ ∑ q ∈ S_big, (1 / 3 : ℝ) * (p / 3) ^ q.1.card * (xHi L G q.2 - xLo L G q.2) := by
            refine sum_le_sum_of_subset_of_nonneg ?_ fun q _ _ => ?_
            · intro q hq
              obtain ⟨q₀, hq₀, rfl⟩ := mem_image.mp hq
              exact hf_maps q₀ hq₀
            · rw [xHi_sub_xLo q.2]
              have hxpos := (xHi_gt_one_and_le hL hG q.2).1.le
              have hppos := hp.2.2.1.le
              positivity
  have hstep3 : ∑ R' ∈ (binsLe L G (u + h)).powerset, (1 / 3 : ℝ) * (p / 3) ^ R'.card *
        ∑ r ∈ univ.filter (fun r : Fin G =>
            u - h - subSum (xHi L G) R' ≤ xHi L G r ∧ xHi L G r ≤ u + h - subSum (xHi L G) R'),
          (xHi L G r - xLo L G r) ≤
      h * (u + h) ^ (1 / 3 : ℝ) := by
    calc _ ≤ ∑ R' ∈ (binsLe L G (u + h)).powerset, (1 / 3 : ℝ) * (p / 3) ^ R'.card * (3 * h) := by
            refine sum_le_sum fun R' _ => ?_
            refine mul_le_mul_of_nonneg_left ?_ (by positivity [hp.2.2.1.le])
            have htel := sum_xHi_sub_xLo_in_interval hL hG
              (a := u - h - subSum (xHi L G) R') (b := u + h - subSum (xHi L G) R') (by linarith)
            linarith
      _ = h * ∑ R' ∈ (binsLe L G (u + h)).powerset, (p / 3) ^ R'.card := by
            rw [mul_sum]; refine sum_congr rfl fun R' _ => by ring
      _ ≤ h * (u + h) ^ (1 / 3 : ℝ) :=
            mul_le_mul_of_nonneg_left (sum_pow_one_third_le hL hG hΔ (by linarith)) hhpos.le
  have hstep4 : (u + h) ^ (1 / 3 : ℝ) ≤ 2 * u ^ (1 / 3 : ℝ) := by
    have h1 : (u + h) ^ (1 / 3 : ℝ) ≤ (2 * u) ^ (1 / 3 : ℝ) :=
      rpow_le_rpow (by linarith) (by linarith) (by norm_num)
    rw [mul_rpow (by norm_num) hupos.le] at h1
    have h2 : (2 : ℝ) ^ (1 / 3 : ℝ) ≤ 2 := by
      have : (2 : ℝ) ^ (1 / 3 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
        rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      simpa using this
    exact le_trans h1 (mul_le_mul_of_nonneg_right h2 (rpow_nonneg hupos.le _))
  have hcomb : (u / 2) * ∑ R ∈ W, (p / 3) ^ R.card ≤ 2 * h * u ^ (1 / 3 : ℝ) := by
    have h5 := mul_le_mul_of_nonneg_left hstep4 hhpos.le
    linarith
  have hgoal : (u / 2) * ∑ R ∈ W, (p / 3) ^ R.card ≤ (u / 2) * (4 * h * u ^ (-(2 / 3 : ℝ))) := by
    have heq : (u / 2) * (4 * h * u ^ (-(2 / 3 : ℝ))) = 2 * h * (u * u ^ (-(2 / 3 : ℝ))) := by ring
    rw [heq]
    have hpow : u * u ^ (-(2 / 3 : ℝ)) = u ^ (1 / 3 : ℝ) := by
      conv_lhs => arg 1; rw [← rpow_one u]
      rw [← rpow_add hupos]
      norm_num
    rw [hpow]
    exact hcomb
  exact le_of_mul_le_mul_left hgoal (by positivity)

/-- Dyadic upper bound on the 2-set sum
`∑_{A, B : subSum ≤ 2^(k+1), 1 ≤ subSum A + subSum B} (p/3)^(|A|+|B|) * (subSum A + subSum B)^(-2/3) ≤ 4 * (k + 2)`. -/
private lemma dyadic_pair_sum_le {L : ℝ} {G : ℕ} (hL : 1 < L) (hG : 0 < G) (hΔ : gridDelta L G ≤ 1)
    (k : ℕ) :
    let P_k := (univ : Finset (Fin G)).powerset.filter fun A => subSum (xHi L G) A ≤ (2 : ℝ) ^ (k + 1)
    ∑ AB ∈ (P_k ×ˢ P_k).filter (fun AB => 1 ≤ subSum (xHi L G) AB.1 + subSum (xHi L G) AB.2),
      (gridP L G / 3) ^ AB.1.card * (gridP L G / 3) ^ AB.2.card *
        (subSum (xHi L G) AB.1 + subSum (xHi L G) AB.2) ^ (-(2 / 3 : ℝ)) ≤
      4 * ((k : ℝ) + 2) := by
  intro P_k
  have hp := gridP_bounds hL hG hΔ
  set Q := (P_k ×ˢ P_k).filter (fun AB => 1 ≤ subSum (xHi L G) AB.1 + subSum (xHi L G) AB.2)
  let shell (j : ℕ) : Finset (Finset (Fin G) × Finset (Fin G)) :=
    Q.filter fun AB => (2 : ℝ) ^ j ≤ max (subSum (xHi L G) AB.1) (subSum (xHi L G) AB.2) ∧
      max (subSum (xHi L G) AB.1) (subSum (xHi L G) AB.2) ≤ (2 : ℝ) ^ (j + 1)
  have hcov : Q ⊆ (range (k + 2)).biUnion shell := by
    intro ⟨A, B⟩ hAB_orig
    have hAB := hAB_orig
    simp only [Q, P_k, mem_filter, mem_product, mem_powerset] at hAB
    set m := max (subSum (xHi L G) A) (subSum (xHi L G) B)
    have hm1 : 1 ≤ m := by
      by_cases hA : A.Nonempty
      · obtain ⟨r, hr⟩ := hA
        have hx := (xHi_gt_one_and_le hL hG r).1
        have hle : xHi L G r ≤ subSum (xHi L G) A :=
          single_le_sum (fun t _ => (xHi_nonneg hL hG t)) hr
        exact le_trans hx.le (le_trans hle (le_max_left _ _))
      · rw [not_nonempty_iff_eq_empty] at hA
        subst hA
        have h0 : subSum (xHi L G) (∅ : Finset (Fin G)) = 0 := by simp [subSum]
        have hB1 : 1 ≤ subSum (xHi L G) B := by linarith [hAB.2]
        exact le_trans hB1 (le_max_right _ _)
    have hm_le : m ≤ (2 : ℝ) ^ (k + 1) := max_le hAB.1.1.2 hAB.1.2.2
    -- Pick `j = ⌊log m / log 2⌋₊`; then `2^j ≤ m ≤ 2^(j+1)` and `j ≤ k + 1 < k + 2`.
    have hlog2 : 0 < log 2 := log_pos (by norm_num)
    set j := ⌊log m / log 2⌋₊
    have hj_le : j ≤ k + 1 := by
      have hdiv : log m / log 2 ≤ ((k + 1 : ℕ) : ℝ) := by
        rw [div_le_iff₀ hlog2]
        have hlogm := log_le_log (by linarith) hm_le
        rw [log_pow] at hlogm
        exact hlogm
      exact Nat.floor_le_of_le hdiv
    have h2j_le : (2 : ℝ) ^ j ≤ m := by
      have hnn : 0 ≤ log m / log 2 := div_nonneg (log_nonneg hm1) hlog2.le
      have hfl := Nat.floor_le hnn
      have hmul := mul_le_mul_of_nonneg_right hfl hlog2.le
      rw [div_mul_cancel₀ _ hlog2.ne'] at hmul
      rw [← exp_log (by linarith : 0 < m)]
      have hpow : (2 : ℝ) ^ j = exp ((j : ℝ) * log 2) := by
        rw [← rpow_natCast, rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm]
      rw [hpow]
      exact exp_le_exp.mpr hmul
    have hm_le_2jp1 : m ≤ (2 : ℝ) ^ (j + 1) := by
      have hlt := Nat.lt_floor_add_one (log m / log 2)
      have hmul := mul_lt_mul_of_pos_right hlt hlog2
      rw [div_mul_cancel₀ _ hlog2.ne'] at hmul
      rw [← exp_log (by linarith : 0 < m)]
      have hpow : (2 : ℝ) ^ (j + 1) = exp (((j + 1 : ℕ) : ℝ) * log 2) := by
        rw [← rpow_natCast, rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm]
      rw [hpow]
      exact exp_le_exp.mpr (by push_cast; linarith)
    refine mem_biUnion.mpr ⟨j, mem_range.mpr (by omega), ?_⟩
    exact mem_filter.mpr ⟨hAB_orig, h2j_le, hm_le_2jp1⟩
  have hterm_nn : ∀ AB : Finset (Fin G) × Finset (Fin G),
      0 ≤ (gridP L G / 3) ^ AB.1.card * (gridP L G / 3) ^ AB.2.card *
        (subSum (xHi L G) AB.1 + subSum (xHi L G) AB.2) ^ (-(2 / 3 : ℝ)) := fun AB => by
    have hnn1 : 0 ≤ subSum (xHi L G) AB.1 := sum_nonneg fun r _ => (xHi_nonneg hL hG r)
    have hnn2 : 0 ≤ subSum (xHi L G) AB.2 := sum_nonneg fun r _ => (xHi_nonneg hL hG r)
    have h1 := hp.2.2.1.le
    exact mul_nonneg (mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg (by linarith) _))
      (rpow_nonneg (by linarith) _)
  have hshell_le : ∀ j ∈ range (k + 2),
      ∑ AB ∈ shell j, (gridP L G / 3) ^ AB.1.card * (gridP L G / 3) ^ AB.2.card *
        (subSum (xHi L G) AB.1 + subSum (xHi L G) AB.2) ^ (-(2 / 3 : ℝ)) ≤ 4 := by
    intro j _
    set Bj := (binsLe L G ((2 : ℝ) ^ (j + 1))).powerset
    have hsub : shell j ⊆ Bj ×ˢ Bj := by
      intro ⟨A, B⟩ hAB
      have hmax := (mem_filter.mp hAB).2.2
      simp only [Bj, mem_product, mem_powerset]
      constructor
      · intro r hr
        simp only [binsLe, mem_filter, mem_univ, true_and]
        have hxle : xHi L G r ≤ subSum (xHi L G) A :=
          single_le_sum (fun t _ => (xHi_nonneg hL hG t)) hr
        exact le_trans hxle (le_trans (le_max_left _ _) hmax)
      · intro r hr
        simp only [binsLe, mem_filter, mem_univ, true_and]
        have hxle : xHi L G r ≤ subSum (xHi L G) B :=
          single_le_sum (fun t _ => (xHi_nonneg hL hG t)) hr
        exact le_trans hxle (le_trans (le_max_right _ _) hmax)
    have h2j_pos : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
    have h2jp1_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ (j + 1) := one_le_pow₀ (by norm_num)
    calc ∑ AB ∈ shell j, (gridP L G / 3) ^ AB.1.card * (gridP L G / 3) ^ AB.2.card *
            (subSum (xHi L G) AB.1 + subSum (xHi L G) AB.2) ^ (-(2 / 3 : ℝ))
        ≤ ∑ AB ∈ shell j, (gridP L G / 3) ^ AB.1.card * (gridP L G / 3) ^ AB.2.card *
            ((2 : ℝ) ^ j) ^ (-(2 / 3 : ℝ)) := by
            refine sum_le_sum fun AB hAB => ?_
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (pow_nonneg (by linarith [hp.2.2.1]) _)
              (pow_nonneg (by linarith [hp.2.2.1]) _))
            have hge : (2 : ℝ) ^ j ≤ subSum (xHi L G) AB.1 + subSum (xHi L G) AB.2 := by
              have hm := (mem_filter.mp hAB).2.1
              have hnn1 : 0 ≤ subSum (xHi L G) AB.1 := sum_nonneg fun r _ => (xHi_nonneg hL hG r)
              have hnn2 : 0 ≤ subSum (xHi L G) AB.2 := sum_nonneg fun r _ => (xHi_nonneg hL hG r)
              exact le_trans hm (max_le (by linarith) (by linarith))
            exact rpow_le_rpow_of_nonpos h2j_pos hge (by norm_num)
      _ ≤ ∑ AB ∈ Bj ×ˢ Bj, (gridP L G / 3) ^ AB.1.card * (gridP L G / 3) ^ AB.2.card *
            ((2 : ℝ) ^ j) ^ (-(2 / 3 : ℝ)) := by
            refine sum_le_sum_of_subset_of_nonneg hsub fun AB _ _ => ?_
            exact mul_nonneg (mul_nonneg (pow_nonneg (by linarith [hp.2.2.1]) _)
              (pow_nonneg (by linarith [hp.2.2.1]) _)) (rpow_nonneg h2j_pos.le _)
      _ = ((∑ A ∈ Bj, (gridP L G / 3) ^ A.card) * (∑ B ∈ Bj, (gridP L G / 3) ^ B.card)) *
            ((2 : ℝ) ^ j) ^ (-(2 / 3 : ℝ)) := by
            rw [← sum_mul, sum_product, sum_mul_sum]
      _ ≤ (((2 : ℝ) ^ (j + 1)) ^ (1 / 3 : ℝ) * ((2 : ℝ) ^ (j + 1)) ^ (1 / 3 : ℝ)) *
            ((2 : ℝ) ^ j) ^ (-(2 / 3 : ℝ)) := by
            have hB := sum_pow_one_third_le hL hG hΔ h2jp1_ge1
            have hBnn : 0 ≤ ∑ A ∈ Bj, (gridP L G / 3) ^ A.card :=
              sum_nonneg fun A _ => pow_nonneg (by linarith [hp.2.2.1]) _
            exact mul_le_mul_of_nonneg_right (mul_le_mul hB hB hBnn (rpow_nonneg (by positivity) _))
              (rpow_nonneg h2j_pos.le _)
      _ ≤ 4 := by
            have hpow_eq : ((2 : ℝ) ^ (j + 1)) ^ (1 / 3 : ℝ) * ((2 : ℝ) ^ (j + 1)) ^ (1 / 3 : ℝ) *
                ((2 : ℝ) ^ j) ^ (-(2 / 3 : ℝ)) = (2 : ℝ) ^ (2 / 3 : ℝ) := by
              rw [pow_succ', mul_rpow (by norm_num) h2j_pos.le]
              calc ((2 : ℝ) ^ (1 / 3 : ℝ) * ((2 : ℝ) ^ j) ^ (1 / 3 : ℝ)) *
                    ((2 : ℝ) ^ (1 / 3 : ℝ) * ((2 : ℝ) ^ j) ^ (1 / 3 : ℝ)) *
                    ((2 : ℝ) ^ j) ^ (-(2 / 3 : ℝ))
                  = ((2 : ℝ) ^ (1 / 3 : ℝ) * (2 : ℝ) ^ (1 / 3 : ℝ)) *
                    ((((2 : ℝ) ^ j) ^ (1 / 3 : ℝ) * ((2 : ℝ) ^ j) ^ (1 / 3 : ℝ)) *
                      ((2 : ℝ) ^ j) ^ (-(2 / 3 : ℝ))) := by ring
                _ = (2 : ℝ) ^ (2 / 3 : ℝ) * (1 : ℝ) := by
                    rw [← rpow_add (by norm_num : (0 : ℝ) < 2),
                        ← rpow_add h2j_pos, ← rpow_add h2j_pos]
                    norm_num
                _ = (2 : ℝ) ^ (2 / 3 : ℝ) := mul_one _
            rw [hpow_eq]
            calc (2 : ℝ) ^ (2 / 3 : ℝ) ≤ (2 : ℝ) ^ (2 : ℝ) :=
                  rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
              _ = 4 := by norm_num
  calc ∑ AB ∈ Q, (gridP L G / 3) ^ AB.1.card * (gridP L G / 3) ^ AB.2.card *
          (subSum (xHi L G) AB.1 + subSum (xHi L G) AB.2) ^ (-(2 / 3 : ℝ))
      ≤ ∑ AB ∈ (range (k + 2)).biUnion shell,
          (gridP L G / 3) ^ AB.1.card * (gridP L G / 3) ^ AB.2.card *
            (subSum (xHi L G) AB.1 + subSum (xHi L G) AB.2) ^ (-(2 / 3 : ℝ)) :=
          sum_le_sum_of_subset_of_nonneg hcov fun AB _ _ => hterm_nn AB
    _ ≤ ∑ j ∈ range (k + 2), ∑ AB ∈ shell j,
          (gridP L G / 3) ^ AB.1.card * (gridP L G / 3) ^ AB.2.card *
            (subSum (xHi L G) AB.1 + subSum (xHi L G) AB.2) ^ (-(2 / 3 : ℝ)) :=
          sum_biUnion_le_of_nonneg fun AB _ => hterm_nn AB
    _ ≤ ∑ _j ∈ range (k + 2), (4 : ℝ) := sum_le_sum hshell_le
    _ = 4 * ((k : ℝ) + 2) := by rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring

/-- Localized typical-event subset probability bound:
for `K ⊆ binsLe L G (min U₀ L)` with `K.card ≤ 2 * log L`,
`Pr[isTyp b ∧ K ⊆ activeSet b] ≤ 4 * L^(7/1000) * U₀^(log 3 - 2/3) * (p/3)^K.card`. -/
private lemma bernProb_isTyp_subset_le {L : ℝ} {G : ℕ}
    (hL : exp 10000000000 ≤ L) (hG : 0 < G)
    (hΔle1 : gridDelta L G ≤ 1 / 1000000) (hlogLΔ : log L * gridDelta L G ≤ 1 / 10000)
    {U₀ : ℝ} (hU0 : 1 ≤ U₀) {K : Finset (Fin G)}
    (hKT : K ⊆ binsLe L G (min U₀ L)) (hKcard : (K.card : ℝ) ≤ 2 * log L) :
    (∑ b : Fin G → Bool, bernProb (gridP L G) b *
      (if isTyp L G b ∧ K ⊆ activeSet b then (1 : ℝ) else 0)) ≤
      4 * L ^ (7 / 1000 : ℝ) * U₀ ^ (log 3 - 2 / 3) * (gridP L G / 3) ^ K.card := by
  set p : ℝ := gridP L G
  set Δ : ℝ := gridDelta L G
  have hlogL_ge : (10000000000 : ℝ) ≤ log L := by
    have := log_le_log (exp_pos _) hL; rwa [log_exp] at this
  have hLpos : 0 < L := lt_of_lt_of_le (exp_pos _) hL
  have hL1 : 1 < L := (log_pos_iff hLpos.le).mp (by linarith)
  have hΔpos : 0 < Δ := gridDelta_pos hL1 hG
  have hp := gridP_bounds hL1 hG (by linarith)
  have hprob_nn : ∀ b : Fin G → Bool, 0 ≤ bernProb p b := fun b => bernProb_nonneg hp.2.2.1.le hp.2.2.2.le b
  set u_min : ℝ := min U₀ L
  have humin_ge1 : 1 ≤ u_min := le_min hU0 hL1.le
  have humin_leL : u_min ≤ L := min_le_right _ _
  have humin_pos : 0 < u_min := by linarith
  set T := binsLe L G u_min
  have hpt_wt : ∀ b : Fin G → Bool,
      (if isTyp L G b ∧ K ⊆ activeSet b then (1 : ℝ) else 0) ≤
        u_min ^ (log 3) * L ^ (7 / 1000 : ℝ) *
          (if K ⊆ activeSet b then ((1 / 3 : ℝ) ^ (activeSet b ∩ T).card) else 0) := by
    intro b
    by_cases hcond : isTyp L G b ∧ K ⊆ activeSet b
    · rw [if_pos hcond, if_pos hcond.2]
      have hcard := isTyp_card_binsLe hL1 hG hcond.1 humin_ge1 humin_leL
      have h3pow : (3 : ℝ) ^ (activeSet b ∩ T).card ≤ u_min ^ (log 3) * L ^ (7 / 1000 : ℝ) := by
        rw [← rpow_natCast, rpow_def_of_pos (by norm_num : (0 : ℝ) < 3),
            rpow_def_of_pos humin_pos, rpow_def_of_pos hLpos, ← exp_add]
        apply exp_le_exp.mpr
        have hlog3_pos : 0 < log 3 := log_pos (by norm_num)
        have hlog3_lt : log 3 < 1.1 := lt_trans log_three_lt_d9 (by norm_num)
        have hmul := mul_le_mul_of_nonneg_right hcard hlog3_pos.le
        nlinarith [log_pos hL1]
      have hinv : ((1 / 3 : ℝ) ^ (activeSet b ∩ T).card) * (3 : ℝ) ^ (activeSet b ∩ T).card = 1 := by
        rw [← mul_pow]; norm_num
      calc (1 : ℝ) = (3 : ℝ) ^ (activeSet b ∩ T).card * (1 / 3 : ℝ) ^ (activeSet b ∩ T).card := by linarith
        _ ≤ (u_min ^ (log 3) * L ^ (7 / 1000 : ℝ)) * (1 / 3 : ℝ) ^ (activeSet b ∩ T).card :=
              mul_le_mul_of_nonneg_right h3pow (by positivity)
    · rw [if_neg hcond]
      have : 0 ≤ u_min ^ (log 3) * L ^ (7 / 1000 : ℝ) := by positivity
      split_ifs <;> positivity
  have hexp_eq := sum_bernProb_subset_pow p (1 / 3 : ℝ) (K := K) (T := T) hKT
  have hTK_bound : (1 - p + p * (1 / 3 : ℝ)) ^ (T \ K).card ≤ 4 * u_min ^ (-(2 / 3 : ℝ)) := by
    have hbase_eq : 1 - p + p * (1 / 3 : ℝ) = 1 - 2 * p / 3 := by ring
    rw [hbase_eq]
    have hbase_pos : 0 < 1 - 2 * p / 3 := by linarith [hp.2.2.2]
    have hTcard_eq : (T \ K).card + K.card = T.card := by
      rw [card_sdiff, inter_eq_left.mpr hKT]
      exact Nat.sub_add_cancel (card_le_card hKT)
    have hpow_mul : (1 - 2 * p / 3) ^ (T \ K).card * (1 - 2 * p / 3) ^ K.card =
        (1 - 2 * p / 3) ^ T.card := by
      rw [← pow_add, hTcard_eq]
    have hden_ge : (1 / 2 : ℝ) ≤ (1 - 2 * p / 3) ^ K.card := by
      have hbern : 1 + (K.card : ℝ) * (-(2 * p / 3)) ≤ (1 - 2 * p / 3) ^ K.card := by
        rw [sub_eq_add_neg]
        exact one_add_mul_le_pow (by linarith [hp.2.2.2]) K.card
      have hKmul : (K.card : ℝ) * (2 * p / 3) ≤ 1 / 2 := by
        have h2 : 2 * p / 3 ≤ Δ := by linarith [hp.2.1, hp.2.2.1]
        have h3 : (K.card : ℝ) * (2 * p / 3) ≤ (2 * log L) * Δ :=
          mul_le_mul hKcard h2 (by linarith [hp.2.2.1]) (by linarith)
        linarith
      linarith
    have hnum_le : (1 - 2 * p / 3) ^ T.card ≤ 2 * u_min ^ (-(2 / 3 : ℝ)) := by
      have h1 : (1 - 2 * p / 3) ^ T.card ≤ exp (-((T.card : ℝ) * (2 * p / 3))) := by
        calc (1 - 2 * p / 3) ^ T.card
            ≤ (exp (-(2 * p / 3))) ^ T.card :=
                pow_le_pow_left₀ hbase_pos.le (by linarith [add_one_le_exp (-(2 * p / 3))]) _
          _ = exp ((T.card : ℝ) * -(2 * p / 3)) := (exp_nat_mul _ _).symm
          _ = exp (-((T.card : ℝ) * (2 * p / 3))) := by ring_nf
      have hp_lb : Δ * (1 - Δ) ≤ p := by
        unfold p gridP
        have h1' : exp (-Δ) ≤ 1 / (1 + Δ) := by
          rw [exp_neg, one_div]
          exact inv_anti₀ (by positivity) (by linarith [add_one_le_exp Δ])
        have h2' : Δ * (1 - Δ) ≤ 1 - 1 / (1 + Δ) := by
          have hpos : 0 < 1 + Δ := by linarith
          have hid : 1 - Δ * (1 - Δ) - 1 / (1 + Δ) = Δ ^ 3 / (1 + Δ) := by
            field_simp [hpos.ne']; ring
          have hnn : 0 ≤ 1 - Δ * (1 - Δ) - 1 / (1 + Δ) := by rw [hid]; positivity
          linarith
        linarith
      have hTΔ : log u_min - Δ < (T.card : ℝ) * Δ := (binsLe_card_mul_delta hL1 hG humin_ge1 humin_leL).1
      have hlog_le : log u_min ≤ log L := log_le_log humin_pos humin_leL
      have hexp_arg : -((T.card : ℝ) * (2 * p / 3)) ≤ -(2 / 3 : ℝ) * log u_min + 1 / 2 := by
        have hmul : (T.card : ℝ) * (2 * p / 3) ≥ ((T.card : ℝ) * Δ) * (2 / 3 : ℝ) * (1 - Δ) := by
          have hnn : 0 ≤ (T.card : ℝ) := Nat.cast_nonneg _
          have := mul_le_mul_of_nonneg_left hp_lb hnn
          nlinarith
        have hmul2 : ((T.card : ℝ) * Δ) * (2 / 3 : ℝ) * (1 - Δ) ≥
            (log u_min - Δ) * (2 / 3 : ℝ) * (1 - Δ) := by
          have : 0 ≤ (2 / 3 : ℝ) * (1 - Δ) := by linarith
          nlinarith
        have hlog_nn : 0 ≤ log u_min := log_nonneg humin_ge1
        have hΔlog : Δ * log u_min ≤ 1 / 10000 := by
          calc Δ * log u_min ≤ Δ * log L := mul_le_mul_of_nonneg_left hlog_le hΔpos.le
            _ = log L * Δ := mul_comm _ _
            _ ≤ 1 / 10000 := hlogLΔ
        nlinarith
      calc (1 - 2 * p / 3) ^ T.card
          ≤ exp (-((T.card : ℝ) * (2 * p / 3))) := h1
        _ ≤ exp (-(2 / 3 : ℝ) * log u_min + 1 / 2) := exp_le_exp.mpr hexp_arg
        _ = exp (1 / 2) * u_min ^ (-(2 / 3 : ℝ)) := by
              rw [exp_add, rpow_def_of_pos humin_pos]; ring_nf
        _ ≤ 2 * u_min ^ (-(2 / 3 : ℝ)) := by
              have hehalf : exp (1 / 2 : ℝ) ≤ 2 := by
                have h1' := exp_one_lt_d9
                have hsq : (exp (1 / 2 : ℝ)) ^ 2 = exp 1 := by
                  rw [← exp_nat_mul]; norm_num
                nlinarith [exp_pos (1 / 2 : ℝ)]
              exact mul_le_mul_of_nonneg_right hehalf (rpow_nonneg humin_pos.le _)
    have hmul_le : (1 / 2 : ℝ) * (1 - 2 * p / 3) ^ (T \ K).card ≤ 2 * u_min ^ (-(2 / 3 : ℝ)) := by
      calc (1 / 2 : ℝ) * (1 - 2 * p / 3) ^ (T \ K).card
          ≤ (1 - 2 * p / 3) ^ K.card * (1 - 2 * p / 3) ^ (T \ K).card :=
              mul_le_mul_of_nonneg_right hden_ge (pow_nonneg hbase_pos.le _)
        _ = (1 - 2 * p / 3) ^ T.card := by rw [mul_comm]; exact hpow_mul
        _ ≤ 2 * u_min ^ (-(2 / 3 : ℝ)) := hnum_le
    linarith
  have hpow_comb : u_min ^ (log 3) * u_min ^ (-(2 / 3 : ℝ)) ≤ U₀ ^ (log 3 - 2 / 3) := by
    rw [← rpow_add humin_pos]
    have hexp_pos : 0 ≤ log 3 - 2 / 3 := by have := log_three_gt_d9; linarith
    have hsub_eq : log 3 + -(2 / 3 : ℝ) = log 3 - 2 / 3 := by ring
    rw [hsub_eq]
    exact rpow_le_rpow humin_pos.le (min_le_left _ _) hexp_pos
  calc ∑ b : Fin G → Bool, bernProb p b * (if isTyp L G b ∧ K ⊆ activeSet b then (1 : ℝ) else 0)
      ≤ ∑ b : Fin G → Bool, bernProb p b *
          (u_min ^ (log 3) * L ^ (7 / 1000 : ℝ) *
            (if K ⊆ activeSet b then ((1 / 3 : ℝ) ^ (activeSet b ∩ T).card) else 0)) :=
          sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hpt_wt b) (hprob_nn b)
    _ = u_min ^ (log 3) * L ^ (7 / 1000 : ℝ) *
          ∑ b : Fin G → Bool, bernProb p b *
            (if K ⊆ activeSet b then ((1 / 3 : ℝ) ^ (activeSet b ∩ T).card) else 0) := by
          rw [mul_sum]; refine sum_congr rfl fun b _ => by ring
    _ = u_min ^ (log 3) * L ^ (7 / 1000 : ℝ) *
          ((p * (1 / 3 : ℝ)) ^ K.card * (1 - p + p * (1 / 3 : ℝ)) ^ (T \ K).card) := by
          rw [hexp_eq]
    _ ≤ u_min ^ (log 3) * L ^ (7 / 1000 : ℝ) *
          ((p * (1 / 3 : ℝ)) ^ K.card * (4 * u_min ^ (-(2 / 3 : ℝ)))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hTK_bound
            (pow_nonneg (by linarith [hp.2.2.1]) _)) (by positivity)
    _ = 4 * L ^ (7 / 1000 : ℝ) * (u_min ^ (log 3) * u_min ^ (-(2 / 3 : ℝ))) *
          (p * (1 / 3 : ℝ)) ^ K.card := by ring
    _ ≤ 4 * L ^ (7 / 1000 : ℝ) * U₀ ^ (log 3 - 2 / 3) *
          (p * (1 / 3 : ℝ)) ^ K.card := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow_comb (by positivity))
            (pow_nonneg (by linarith [hp.2.2.1]) _)
    _ = 4 * L ^ (7 / 1000 : ℝ) * U₀ ^ (log 3 - 2 / 3) * (p / 3) ^ K.card := by
          rw [show p * (1 / 3 : ℝ) = p / 3 by ring]

set_option maxHeartbeats 800000 in
/-- Upper bound on `E[1_typ * badTriples]`:
for `L ≥ exp 10000000000` and fine `G`, with `η = L ^ (-(1/40))`,
`∑ b, bernProb p b * (if isTyp b then badTriples.card else 0) ≤ L ^ (7/100) / 768000`. -/
lemma expected_badTriples_typ_le {L : ℝ} {G : ℕ}
    (hL : exp 10000000000 ≤ L) (hG : 0 < G)
    (hstep : 2000 * L * gridDelta L G ≤ L ^ (-(1 / 40 : ℝ)) / 4) :
    ∑ b : Fin G → Bool, bernProb (gridP L G) b *
      (if isTyp L G b then ((badTriples L G (L ^ (-(1 / 40 : ℝ))) b).card : ℝ) else 0) ≤
      L ^ (7 / 100 : ℝ) / 768000 := by
  set η : ℝ := L ^ (-(1 / 40 : ℝ))
  set p : ℝ := gridP L G
  set Δ : ℝ := gridDelta L G
  have hlogL_ge : (10000000000 : ℝ) ≤ log L := by
    have := log_le_log (exp_pos _) hL
    rwa [log_exp] at this
  have hLpos : 0 < L := lt_of_lt_of_le (exp_pos _) hL
  have hL1 : 1 < L := (log_pos_iff hLpos.le).mp (by linarith)
  have hL10 : 10 ≤ L := by
    have : (10 : ℝ) ≤ exp 10000000000 := by linarith [add_one_le_exp (10000000000 : ℝ)]
    linarith
  have hηpos : 0 < η := rpow_pos_of_pos hLpos _
  have hηle : η ≤ 1 / 10 := by
    unfold η
    rw [rpow_def_of_pos hLpos]
    have h1 : log L * -(1 / 40 : ℝ) ≤ -10 := by linarith
    have h2 : exp (-10) ≤ 1 / 10 := by
      rw [exp_neg, one_div]
      exact inv_anti₀ (by norm_num) (by linarith [add_one_le_exp (10 : ℝ)])
    exact le_trans (exp_le_exp.mpr h1) h2
  have hΔpos : 0 < Δ := gridDelta_pos hL1 hG
  have hΔle1 : Δ ≤ 1 / 1000000 := by
    have : 2000 * L * Δ ≤ 1 / 40 := by linarith
    have : (100000 : ℝ) ≤ L := by linarith [add_one_le_exp (10000000000 : ℝ)]
    nlinarith
  have hp := gridP_bounds hL1 hG (by linarith)
  have hprob_nn : ∀ b : Fin G → Bool, 0 ≤ bernProb p b := fun b => bernProb_nonneg hp.2.2.1.le hp.2.2.2.le b
  have hL_ge_logL : log L ≤ L := le_trans (log_le_sub_one_of_pos hLpos) (by linarith)
  -- Key smallness bounds from `hstep`:
  have hLΔ_le : L * Δ ≤ η / 8000 := by linarith
  have hpL_le : p * L ≤ 11 * η / 10 := by
    have : p * L ≤ Δ * L := mul_le_mul_of_nonneg_right hp.2.1 hLpos.le
    linarith
  have hlogLΔ_le : log L * Δ ≤ 1 / 10000 := by
    have : log L * Δ ≤ L * Δ := mul_le_mul_of_nonneg_right hL_ge_logL hΔpos.le
    linarith
  -- Step 1: 5-tuple decomposition of `badTriples L G η b` on `isTyp L G b`.
  set P_all := (univ : Finset (Fin G)).powerset
  set Valid3 := (P_all ×ˢ P_all ×ˢ P_all).filter fun q =>
    subSum (xHi L G) q.1 ≤ L ∧ subSum (xHi L G) q.2.1 ≤ L ∧ subSum (xHi L G) q.2.2 ≤ L + 1 ∧
    1 ≤ subSum (xHi L G) q.1 + subSum (xHi L G) q.2.2 ∧
    1 ≤ subSum (xHi L G) q.2.1 + subSum (xHi L G) q.2.2
  let u₁ (q : Finset (Fin G) × Finset (Fin G) × Finset (Fin G)) : ℝ :=
    subSum (xHi L G) q.1 + subSum (xHi L G) q.2.2
  let u₂ (q : Finset (Fin G) × Finset (Fin G) × Finset (Fin G)) : ℝ :=
    subSum (xHi L G) q.2.1 + subSum (xHi L G) q.2.2
  let U₀ (q : Finset (Fin G) × Finset (Fin G) × Finset (Fin G)) : ℝ :=
    subSum (xHi L G) q.1 + subSum (xHi L G) q.2.1 + subSum (xHi L G) q.2.2 + 1
  let W₁ (q : Finset (Fin G) × Finset (Fin G) × Finset (Fin G)) : Finset (Finset (Fin G)) :=
    P_all.filter fun R₁ => u₂ q - 11 * η / 10 ≤ subSum (xHi L G) R₁ ∧ subSum (xHi L G) R₁ ≤ u₂ q + 11 * η / 10
  let W₂ (q : Finset (Fin G) × Finset (Fin G) × Finset (Fin G)) : Finset (Finset (Fin G)) :=
    P_all.filter fun R₂ => u₁ q - 11 * η / 10 ≤ subSum (xHi L G) R₂ ∧ subSum (xHi L G) R₂ ≤ u₁ q + 11 * η / 10
  let Kset (q : Finset (Fin G) × Finset (Fin G) × Finset (Fin G))
      (R : Finset (Fin G) × Finset (Fin G)) : Finset (Fin G) :=
    q.1 ∪ q.2.1 ∪ q.2.2 ∪ R.1 ∪ R.2
  let Good5 (q : Finset (Fin G) × Finset (Fin G) × Finset (Fin G))
      (R : Finset (Fin G) × Finset (Fin G)) : Prop :=
    Disjoint q.1 q.2.1 ∧ Disjoint q.1 q.2.2 ∧ Disjoint q.2.1 q.2.2 ∧
    Disjoint R.1 (q.1 ∪ q.2.1 ∪ q.2.2) ∧ Disjoint R.2 (q.1 ∪ q.2.1 ∪ q.2.2) ∧
    Disjoint R.1 R.2 ∧ ((Kset q R).card : ℝ) ≤ 2 * log L
  have hpt_decomp : ∀ b : Fin G → Bool,
      (if isTyp L G b then ((badTriples L G η b).card : ℝ) else 0) ≤
        ∑ q ∈ Valid3, ∑ R ∈ (W₁ q ×ˢ W₂ q).filter (Good5 q),
          if isTyp L G b ∧ Kset q R ⊆ activeSet b then (1 : ℝ) else 0 := by
    intro b
    by_cases htyp : isTyp L G b
    · rw [if_pos htyp]
      have hRHS_card : (∑ q ∈ Valid3, ∑ R ∈ (W₁ q ×ˢ W₂ q).filter (Good5 q),
            if isTyp L G b ∧ Kset q R ⊆ activeSet b then (1 : ℝ) else 0) =
          ((Valid3.sigma fun q => ((W₁ q ×ˢ W₂ q).filter (Good5 q)).filter fun R =>
            Kset q R ⊆ activeSet b).card : ℝ) := by
        rw [card_sigma, Nat.cast_sum]
        refine sum_congr rfl fun q _ => ?_
        simp only [htyp, true_and]
        rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
      rw [hRHS_card]
      norm_cast
      refine card_le_card_of_injOn
        (fun IJH => ⟨(IJH.1.1 ∩ IJH.2, IJH.1.2 ∩ IJH.2, IJH.2 \ (IJH.1.1 ∪ IJH.1.2)),
          (IJH.1.1 \ IJH.2, IJH.1.2 \ IJH.2)⟩) ?_ ?_
      · rintro ⟨⟨I, J⟩, H⟩ hmem
        simp only [mem_coe, badTriples, uPairs, mem_filter, mem_product,
          mem_powerset] at hmem
        obtain ⟨⟨⟨⟨hIact, hJact⟩, hdisjIJ, hJL, hdiffLo, hdiffHi⟩, hHact⟩, hHneI, hHneJ, hHlo, hHhi⟩ := hmem
        set M₁ := I ∩ H
        set M₂ := J ∩ H
        set S := H \ (I ∪ J)
        set R₁ := I \ H
        set R₂ := J \ H
        have hI_eq : I = M₁ ∪ R₁ := by
          ext r; simp only [M₁, R₁, mem_union, mem_inter, mem_sdiff]; tauto
        have hJ_eq : J = M₂ ∪ R₂ := by
          ext r; simp only [M₂, R₂, mem_union, mem_inter, mem_sdiff]; tauto
        have hH_eq : H = M₁ ∪ M₂ ∪ S := by
          ext r; simp only [M₁, M₂, S, mem_union, mem_inter, mem_sdiff]; tauto
        have hdM1M2 : Disjoint M₁ M₂ := hdisjIJ.mono inter_subset_left inter_subset_left
        have hdM1S : Disjoint M₁ S := by
          rw [disjoint_left]; intro r hr1 hr2
          exact (mem_sdiff.mp hr2).2 (mem_union_left _ (mem_inter.mp hr1).1)
        have hdM2S : Disjoint M₂ S := by
          rw [disjoint_left]; intro r hr1 hr2
          exact (mem_sdiff.mp hr2).2 (mem_union_right _ (mem_inter.mp hr1).1)
        have hdR1H : Disjoint R₁ (M₁ ∪ M₂ ∪ S) := by
          rw [← hH_eq]; exact sdiff_disjoint
        have hdR2H : Disjoint R₂ (M₁ ∪ M₂ ∪ S) := by
          rw [← hH_eq]; exact sdiff_disjoint
        have hdR1R2 : Disjoint R₁ R₂ := hdisjIJ.mono sdiff_subset sdiff_subset
        have hdM1R1 : Disjoint M₁ R₁ := by
          rw [disjoint_left]; intro r h1 h2
          exact (mem_sdiff.mp h2).2 (mem_inter.mp h1).2
        have hdM2R2 : Disjoint M₂ R₂ := by
          rw [disjoint_left]; intro r h1 h2
          exact (mem_sdiff.mp h2).2 (mem_inter.mp h1).2
        have hsumI : subSum (xHi L G) I = subSum (xHi L G) M₁ + subSum (xHi L G) R₁ := by
          unfold subSum; conv_lhs => rw [hI_eq]
          exact sum_union hdM1R1
        have hsumJ : subSum (xHi L G) J = subSum (xHi L G) M₂ + subSum (xHi L G) R₂ := by
          unfold subSum; conv_lhs => rw [hJ_eq]
          exact sum_union hdM2R2
        have hsumH : subSum (xHi L G) H = subSum (xHi L G) M₁ + subSum (xHi L G) M₂ + subSum (xHi L G) S := by
          unfold subSum; conv_lhs => rw [hH_eq]
          rw [sum_union (disjoint_union_left.mpr ⟨hdM1S, hdM2S⟩), sum_union hdM1M2]
        have hxnn : ∀ A : Finset (Fin G), 0 ≤ subSum (xHi L G) A := fun A =>
          sum_nonneg fun r _ => (xHi_nonneg hL1 hG r)
        have hM1L : subSum (xHi L G) M₁ ≤ L := by linarith [hxnn R₁]
        have hM2L : subSum (xHi L G) M₂ ≤ L := by linarith [hxnn R₂]
        have hSL : subSum (xHi L G) S ≤ L + 1 := by linarith [hxnn M₁, hxnn M₂]
        -- Automatic nonemptiness of `M₁ ∪ S` and `M₂ ∪ S`:
        have hu1_ge1 : 1 ≤ subSum (xHi L G) M₁ + subSum (xHi L G) S := by
          by_contra hlt; push Not at hlt
          have hM1_empty : M₁ = ∅ := by
            by_contra hne
            obtain ⟨r, hr⟩ := nonempty_iff_ne_empty.mpr hne
            have hx := (xHi_gt_one_and_le hL1 hG r).1
            have hle : xHi L G r ≤ subSum (xHi L G) M₁ :=
              single_le_sum (fun t _ => (xHi_nonneg hL1 hG t)) hr
            linarith [hxnn S]
          have hS_empty : S = ∅ := by
            by_contra hne
            obtain ⟨r, hr⟩ := nonempty_iff_ne_empty.mpr hne
            have hx := (xHi_gt_one_and_le hL1 hG r).1
            have hle : xHi L G r ≤ subSum (xHi L G) S :=
              single_le_sum (fun t _ => (xHi_nonneg hL1 hG t)) hr
            linarith [hxnn M₁]
          have hHJ : H = M₂ := by rw [hH_eq, hM1_empty, hS_empty]; simp
          have hR2_ne : R₂.Nonempty := by
            rw [nonempty_iff_ne_empty]; intro hR2e
            apply hHneJ; rw [hJ_eq, hR2e, union_empty, hHJ]
          obtain ⟨r, hr⟩ := hR2_ne
          have hx := (xHi_gt_one_and_le hL1 hG r).1
          have hle : xHi L G r ≤ subSum (xHi L G) R₂ :=
            single_le_sum (fun t _ => (xHi_nonneg hL1 hG t)) hr
          have hH0 : subSum (xHi L G) M₁ = 0 := by rw [hM1_empty]; simp [subSum]
          have hS0 : subSum (xHi L G) S = 0 := by rw [hS_empty]; simp [subSum]
          linarith
        have hu2_ge1 : 1 ≤ subSum (xHi L G) M₂ + subSum (xHi L G) S := by
          by_contra hlt; push Not at hlt
          have hM2_empty : M₂ = ∅ := by
            by_contra hne
            obtain ⟨r, hr⟩ := nonempty_iff_ne_empty.mpr hne
            have hx := (xHi_gt_one_and_le hL1 hG r).1
            have hle : xHi L G r ≤ subSum (xHi L G) M₂ :=
              single_le_sum (fun t _ => (xHi_nonneg hL1 hG t)) hr
            linarith [hxnn S]
          have hS_empty : S = ∅ := by
            by_contra hne
            obtain ⟨r, hr⟩ := nonempty_iff_ne_empty.mpr hne
            have hx := (xHi_gt_one_and_le hL1 hG r).1
            have hle : xHi L G r ≤ subSum (xHi L G) S :=
              single_le_sum (fun t _ => (xHi_nonneg hL1 hG t)) hr
            linarith [hxnn M₂]
          have hHI : H = M₁ := by rw [hH_eq, hM2_empty, hS_empty]; simp
          have hR1_ne : R₁.Nonempty := by
            rw [nonempty_iff_ne_empty]; intro hR1e
            apply hHneI; rw [hI_eq, hR1e, union_empty, hHI]
          obtain ⟨r, hr⟩ := hR1_ne
          have hx := (xHi_gt_one_and_le hL1 hG r).1
          have hle : xHi L G r ≤ subSum (xHi L G) R₁ :=
            single_le_sum (fun t _ => (xHi_nonneg hL1 hG t)) hr
          have hM20 : subSum (xHi L G) M₂ = 0 := by rw [hM2_empty]; simp [subSum]
          have hS0 : subSum (xHi L G) S = 0 := by rw [hS_empty]; simp [subSum]
          linarith
        have hKsub : Kset (M₁, M₂, S) (R₁, R₂) ⊆ activeSet b := by
          intro r hr
          simp only [Kset, M₁, M₂, S, R₁, R₂, mem_union, mem_inter, mem_sdiff] at hr
          rcases hr with ((((h | h) | h) | h) | h)
          · exact hIact h.1
          · exact hJact h.1
          · exact hHact h.1
          · exact hIact h.1
          · exact hJact h.1
        have hKcard : ((Kset (M₁, M₂, S) (R₁, R₂)).card : ℝ) ≤ 2 * log L := by
          have h1 : ((Kset (M₁, M₂, S) (R₁, R₂)).card : ℝ) ≤ ((activeSet b).card : ℝ) := by
            exact_mod_cast card_le_card hKsub
          have h2 := isTyp_card_total hL1 hG htyp
          linarith
        simp only [mem_coe, mem_sigma, Valid3, W₁, W₂, P_all, Good5,
          mem_filter, mem_product, mem_powerset, subset_univ, true_and]
        refine ⟨⟨hM1L, hM2L, hSL, hu1_ge1, hu2_ge1⟩,
          ⟨⟨⟨by unfold u₂; linarith, by unfold u₂; linarith⟩,
            ⟨by unfold u₁; linarith, by unfold u₁; linarith⟩⟩,
            hdM1M2, hdM1S, hdM2S, hdR1H, hdR2H, hdR1R2, hKcard⟩, hKsub⟩
      · rintro ⟨⟨I₁, J₁⟩, H₁⟩ _ ⟨⟨I₂, J₂⟩, H₂⟩ _ heq
        simp only [Sigma.mk.inj_iff, Prod.mk.injEq] at heq
        obtain ⟨⟨hM1, hM2, hS⟩, hR⟩ := heq
        have hR' : (I₁ \ H₁, J₁ \ H₁) = (I₂ \ H₂, J₂ \ H₂) := eq_of_heq hR
        obtain ⟨hR1, hR2⟩ := Prod.mk.inj hR'
        have hI : I₁ = I₂ := by
          have h1 : I₁ = (I₁ ∩ H₁) ∪ (I₁ \ H₁) := by
            ext r; simp only [mem_union, mem_inter, mem_sdiff]; tauto
          have h2 : I₂ = (I₂ ∩ H₂) ∪ (I₂ \ H₂) := by
            ext r; simp only [mem_union, mem_inter, mem_sdiff]; tauto
          rw [h1, h2, hM1, hR1]
        have hJ : J₁ = J₂ := by
          have h1 : J₁ = (J₁ ∩ H₁) ∪ (J₁ \ H₁) := by
            ext r; simp only [mem_union, mem_inter, mem_sdiff]; tauto
          have h2 : J₂ = (J₂ ∩ H₂) ∪ (J₂ \ H₂) := by
            ext r; simp only [mem_union, mem_inter, mem_sdiff]; tauto
          rw [h1, h2, hM2, hR2]
        have hH : H₁ = H₂ := by
          have h1 : H₁ = (I₁ ∩ H₁) ∪ (J₁ ∩ H₁) ∪ (H₁ \ (I₁ ∪ J₁)) := by
            ext r; simp only [mem_union, mem_inter, mem_sdiff]; tauto
          have h2 : H₂ = (I₂ ∩ H₂) ∪ (J₂ ∩ H₂) ∪ (H₂ \ (I₂ ∪ J₂)) := by
            ext r; simp only [mem_union, mem_inter, mem_sdiff]; tauto
          rw [h1, h2, hM1, hM2, hS]
        subst hI hJ hH; rfl
    · rw [if_neg htyp]
      exact sum_nonneg fun q _ => sum_nonneg fun R _ => by split_ifs <;> norm_num
  -- Step 2: Localized `(1/3)^card` expectation bound for each `(q, R)`.
  have hsingle_qR : ∀ q ∈ Valid3, ∀ R ∈ (W₁ q ×ˢ W₂ q).filter (Good5 q),
      (∑ b : Fin G → Bool, bernProb p b * (if isTyp L G b ∧ Kset q R ⊆ activeSet b then (1 : ℝ) else 0)) ≤
        4 * L ^ (7 / 1000 : ℝ) * (U₀ q) ^ (log 3 - 2 / 3) *
          ((p / 3) ^ q.1.card * (p / 3) ^ q.2.1.card * (p / 3) ^ q.2.2.card *
            (p / 3) ^ R.1.card * (p / 3) ^ R.2.card) := by
    intro q hq R hR
    have hR' := mem_filter.mp hR
    have hRW1 := (mem_filter.mp (mem_product.mp hR'.1).1).2
    have hRW2 := (mem_filter.mp (mem_product.mp hR'.1).2).2
    have hG5 := hR'.2
    have hxnn : ∀ A : Finset (Fin G), 0 ≤ subSum (xHi L G) A := fun A =>
      sum_nonneg fun r _ => xHi_nonneg hL1 hG r
    have hU0_ge1 : 1 ≤ U₀ q := by
      unfold U₀; linarith [hxnn q.1, hxnn q.2.1, hxnn q.2.2]
    have hKT : Kset q R ⊆ binsLe L G (min (U₀ q) L) := by
      intro r hr
      simp only [binsLe, mem_filter, mem_univ, true_and]
      refine le_min ?_ (xHi_gt_one_and_le hL1 hG r).2
      simp only [Kset, mem_union] at hr
      unfold U₀
      rcases hr with ((((h | h) | h) | h) | h)
      · have h1 : xHi L G r ≤ subSum (xHi L G) q.1 :=
          single_le_sum (fun t _ => xHi_nonneg hL1 hG t) h
        linarith [hxnn q.2.1, hxnn q.2.2]
      · have h1 : xHi L G r ≤ subSum (xHi L G) q.2.1 :=
          single_le_sum (fun t _ => xHi_nonneg hL1 hG t) h
        linarith [hxnn q.1, hxnn q.2.2]
      · have h1 : xHi L G r ≤ subSum (xHi L G) q.2.2 :=
          single_le_sum (fun t _ => xHi_nonneg hL1 hG t) h
        linarith [hxnn q.1, hxnn q.2.1]
      · have h1 : xHi L G r ≤ subSum (xHi L G) R.1 :=
          single_le_sum (fun t _ => xHi_nonneg hL1 hG t) h
        unfold u₂ at hRW1; linarith [hxnn q.1]
      · have h1 : xHi L G r ≤ subSum (xHi L G) R.2 :=
          single_le_sum (fun t _ => xHi_nonneg hL1 hG t) h
        unfold u₁ at hRW2; linarith [hxnn q.2.1]
    have hKcard_eq : (Kset q R).card = q.1.card + q.2.1.card + q.2.2.card + R.1.card + R.2.card := by
      unfold Kset
      have hd1 := hG5.1
      have hd2 := disjoint_union_left.mpr ⟨hG5.2.1, hG5.2.2.1⟩
      have hd3 := hG5.2.2.2.1.symm
      have hd4 := disjoint_union_left.mpr ⟨hG5.2.2.2.2.1.symm, hG5.2.2.2.2.2.1⟩
      rw [card_union_of_disjoint hd4, card_union_of_disjoint hd3,
          card_union_of_disjoint hd2, card_union_of_disjoint hd1]
    have hmain := bernProb_isTyp_subset_le hL hG hΔle1 hlogLΔ_le hU0_ge1 hKT hG5.2.2.2.2.2.2
    rw [hKcard_eq] at hmain
    simp only [pow_add] at hmain
    exact hmain
  -- Step 3: Swap sums and sum out `R₁ ∈ W₁ q` and `R₂ ∈ W₂ q` via `sum_pow_one_third_window`.
  have hstep3 : (∑ b : Fin G → Bool, bernProb p b *
        (if isTyp L G b then ((badTriples L G η b).card : ℝ) else 0)) ≤
      100 * η ^ 2 * L ^ (7 / 1000 : ℝ) *
        ∑ q ∈ Valid3, (p / 3) ^ q.1.card * (p / 3) ^ q.2.1.card * (p / 3) ^ q.2.2.card *
          (U₀ q) ^ (log 3 - 2 / 3) * (u₁ q) ^ (-(2 / 3 : ℝ)) * (u₂ q) ^ (-(2 / 3 : ℝ)) := by
    have hsw : ∑ b : Fin G → Bool, bernProb p b *
          (∑ q ∈ Valid3, ∑ R ∈ (W₁ q ×ˢ W₂ q).filter (Good5 q),
            if isTyp L G b ∧ Kset q R ⊆ activeSet b then (1 : ℝ) else 0) =
        ∑ q ∈ Valid3, ∑ R ∈ (W₁ q ×ˢ W₂ q).filter (Good5 q),
          ∑ b : Fin G → Bool, bernProb p b * (if isTyp L G b ∧ Kset q R ⊆ activeSet b then (1 : ℝ) else 0) := by
      have h1 : ∀ b : Fin G → Bool, bernProb p b *
            (∑ q ∈ Valid3, ∑ R ∈ (W₁ q ×ˢ W₂ q).filter (Good5 q),
              if isTyp L G b ∧ Kset q R ⊆ activeSet b then (1 : ℝ) else 0) =
          ∑ q ∈ Valid3, ∑ R ∈ (W₁ q ×ˢ W₂ q).filter (Good5 q),
            bernProb p b * (if isTyp L G b ∧ Kset q R ⊆ activeSet b then (1 : ℝ) else 0) := fun b => by
        rw [mul_sum]; refine sum_congr rfl fun q _ => mul_sum _ _ _
      rw [sum_congr rfl fun b _ => h1 b, sum_comm]
      refine sum_congr rfl fun q _ => sum_comm
    calc ∑ b : Fin G → Bool, bernProb p b * (if isTyp L G b then ((badTriples L G η b).card : ℝ) else 0)
        ≤ ∑ b : Fin G → Bool, bernProb p b *
            (∑ q ∈ Valid3, ∑ R ∈ (W₁ q ×ˢ W₂ q).filter (Good5 q),
              if isTyp L G b ∧ Kset q R ⊆ activeSet b then (1 : ℝ) else 0) :=
            sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hpt_decomp b) (hprob_nn b)
      _ = ∑ q ∈ Valid3, ∑ R ∈ (W₁ q ×ˢ W₂ q).filter (Good5 q),
            ∑ b : Fin G → Bool, bernProb p b *
              (if isTyp L G b ∧ Kset q R ⊆ activeSet b then (1 : ℝ) else 0) := hsw
      _ ≤ ∑ q ∈ Valid3, ∑ R ∈ (W₁ q ×ˢ W₂ q).filter (Good5 q),
            4 * L ^ (7 / 1000 : ℝ) * (U₀ q) ^ (log 3 - 2 / 3) *
              ((p / 3) ^ q.1.card * (p / 3) ^ q.2.1.card * (p / 3) ^ q.2.2.card *
                (p / 3) ^ R.1.card * (p / 3) ^ R.2.card) :=
            sum_le_sum fun q hq => sum_le_sum fun R hR => hsingle_qR q hq R hR
      _ ≤ ∑ q ∈ Valid3, ∑ R ∈ W₁ q ×ˢ W₂ q,
            4 * L ^ (7 / 1000 : ℝ) * (U₀ q) ^ (log 3 - 2 / 3) *
              ((p / 3) ^ q.1.card * (p / 3) ^ q.2.1.card * (p / 3) ^ q.2.2.card *
                (p / 3) ^ R.1.card * (p / 3) ^ R.2.card) := by
            refine sum_le_sum fun q hq =>
              sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun R _ _ => ?_
            have hU0_nn : 0 ≤ U₀ q := by
              unfold U₀
              have hnn : ∀ A : Finset (Fin G), 0 ≤ subSum (xHi L G) A := fun A => subSum_xHi_nonneg hL1 hG A
              linarith [hnn q.1, hnn q.2.1, hnn q.2.2]
            have hp_nn : 0 ≤ p / 3 := by linarith [hp.2.2.1]
            exact mul_nonneg (mul_nonneg (by positivity) (rpow_nonneg hU0_nn _)) (by positivity)
      _ ≤ 100 * η ^ 2 * L ^ (7 / 1000 : ℝ) *
            ∑ q ∈ Valid3, (p / 3) ^ q.1.card * (p / 3) ^ q.2.1.card * (p / 3) ^ q.2.2.card *
              (U₀ q) ^ (log 3 - 2 / 3) * (u₁ q) ^ (-(2 / 3 : ℝ)) * (u₂ q) ^ (-(2 / 3 : ℝ)) := by
            rw [mul_sum]
            refine sum_le_sum fun q hq => ?_
            have hq' := (mem_filter.mp hq).2
            have hW1 := sum_pow_one_third_window hL1 hG (by linarith) hq'.2.2.2.2 (by positivity) (by linarith) hpL_le
            have hW2 := sum_pow_one_third_window hL1 hG (by linarith) hq'.2.2.2.1 (by positivity) (by linarith) hpL_le
            have hW1_le : ∑ R₁ ∈ W₁ q, (p / 3) ^ R₁.card ≤ 5 * η * (u₂ q) ^ (-(2 / 3 : ℝ)) := by
              calc _ ≤ 4 * (11 * η / 10) * (u₂ q) ^ (-(2 / 3 : ℝ)) := hW1
                _ ≤ 5 * η * (u₂ q) ^ (-(2 / 3 : ℝ)) :=
                    mul_le_mul_of_nonneg_right (by linarith) (rpow_nonneg (by linarith [hq'.2.2.2.2]) _)
            have hW2_le : ∑ R₂ ∈ W₂ q, (p / 3) ^ R₂.card ≤ 5 * η * (u₁ q) ^ (-(2 / 3 : ℝ)) := by
              calc _ ≤ 4 * (11 * η / 10) * (u₁ q) ^ (-(2 / 3 : ℝ)) := hW2
                _ ≤ 5 * η * (u₁ q) ^ (-(2 / 3 : ℝ)) :=
                    mul_le_mul_of_nonneg_right (by linarith) (rpow_nonneg (by linarith [hq'.2.2.2.1]) _)
            have hfact : (∑ R ∈ W₁ q ×ˢ W₂ q,
                4 * L ^ (7 / 1000 : ℝ) * (U₀ q) ^ (log 3 - 2 / 3) *
                  ((p / 3) ^ q.1.card * (p / 3) ^ q.2.1.card * (p / 3) ^ q.2.2.card *
                    (p / 3) ^ R.1.card * (p / 3) ^ R.2.card)) =
                (4 * L ^ (7 / 1000 : ℝ) * (U₀ q) ^ (log 3 - 2 / 3) *
                  ((p / 3) ^ q.1.card * (p / 3) ^ q.2.1.card * (p / 3) ^ q.2.2.card)) *
                ((∑ R₁ ∈ W₁ q, (p / 3) ^ R₁.card) * (∑ R₂ ∈ W₂ q, (p / 3) ^ R₂.card)) := by
              rw [sum_mul_sum, sum_product, mul_sum]
              refine sum_congr rfl fun R₁ _ => ?_
              rw [mul_sum]
              refine sum_congr rfl fun R₂ _ => by ring
            rw [hfact]
            have hW1_nn : 0 ≤ ∑ R₁ ∈ W₁ q, (p / 3) ^ R₁.card :=
              sum_nonneg fun _ _ => pow_nonneg (by linarith [hp.2.2.1]) _
            have hW2_nn : 0 ≤ 5 * η * (u₁ q) ^ (-(2 / 3 : ℝ)) :=
              mul_nonneg (by linarith) (rpow_nonneg (by linarith [hq'.2.2.2.1]) _)
            have hprod_le : (∑ R₁ ∈ W₁ q, (p / 3) ^ R₁.card) * (∑ R₂ ∈ W₂ q, (p / 3) ^ R₂.card) ≤
                25 * η ^ 2 * (u₁ q) ^ (-(2 / 3 : ℝ)) * (u₂ q) ^ (-(2 / 3 : ℝ)) := by
              have hm := mul_le_mul hW1_le hW2_le
                (sum_nonneg fun _ _ => pow_nonneg (by linarith [hp.2.2.1]) _)
                (mul_nonneg (by linarith) (rpow_nonneg (by linarith [hq'.2.2.2.2]) _))
              linarith [show (5 * η * (u₂ q) ^ (-(2 / 3 : ℝ))) * (5 * η * (u₁ q) ^ (-(2 / 3 : ℝ))) =
                  25 * η ^ 2 * (u₁ q) ^ (-(2 / 3 : ℝ)) * (u₂ q) ^ (-(2 / 3 : ℝ)) by ring]
            have hpref_nn : 0 ≤ 4 * L ^ (7 / 1000 : ℝ) * (U₀ q) ^ (log 3 - 2 / 3) *
                ((p / 3) ^ q.1.card * (p / 3) ^ q.2.1.card * (p / 3) ^ q.2.2.card) := by
              have hU0_nn : 0 ≤ U₀ q := by
                unfold U₀
                have hnn : ∀ A : Finset (Fin G), 0 ≤ subSum (xHi L G) A := fun A => subSum_xHi_nonneg hL1 hG A
                linarith [hnn q.1, hnn q.2.1, hnn q.2.2]
              have hp_nn : 0 ≤ p / 3 := by linarith [hp.2.2.1]
              exact mul_nonneg (mul_nonneg (by positivity) (rpow_nonneg hU0_nn _)) (by positivity)
            have hmul := mul_le_mul_of_nonneg_left hprod_le hpref_nn
            linarith [show (4 * L ^ (7 / 1000 : ℝ) * (U₀ q) ^ (log 3 - 2 / 3) *
                  ((p / 3) ^ q.1.card * (p / 3) ^ q.2.1.card * (p / 3) ^ q.2.2.card)) *
                (25 * η ^ 2 * (u₁ q) ^ (-(2 / 3 : ℝ)) * (u₂ q) ^ (-(2 / 3 : ℝ))) =
                100 * η ^ 2 * L ^ (7 / 1000 : ℝ) *
                  ((p / 3) ^ q.1.card * (p / 3) ^ q.2.1.card * (p / 3) ^ q.2.2.card *
                    (U₀ q) ^ (log 3 - 2 / 3) * (u₁ q) ^ (-(2 / 3 : ℝ)) * (u₂ q) ^ (-(2 / 3 : ℝ))) by ring]
  -- Step 4: Dyadic shell bound on the triple sum over `q ∈ Valid3`.
  have hlog2_pos : 0 < log 2 := log_pos (by norm_num)
  set K_dy : ℕ := ⌊log (2 * L) / log 2⌋₊ + 1
  have h2K_gt : 2 * L < (2 : ℝ) ^ K_dy := by
    have hlt := Nat.lt_floor_add_one (log (2 * L) / log 2)
    have hmul := mul_lt_mul_of_pos_right hlt hlog2_pos
    rw [div_mul_cancel₀ _ hlog2_pos.ne'] at hmul
    have hpow : (2 : ℝ) ^ K_dy = exp ((K_dy : ℝ) * log 2) := by
      rw [← rpow_natCast, rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm]
    rw [hpow, ← exp_log (by positivity : 0 < 2 * L)]
    exact exp_lt_exp.mpr (by push_cast [K_dy]; linarith)
  have h2k_le : ∀ k ∈ range K_dy, (2 : ℝ) ^ k ≤ 2 * L := by
    intro k hk
    have hkle : k ≤ ⌊log (2 * L) / log 2⌋₊ := by
      have := mem_range.mp hk; omega
    have hnn : 0 ≤ log (2 * L) / log 2 := div_nonneg (log_nonneg (by linarith)) hlog2_pos.le
    have hfl : (k : ℝ) ≤ log (2 * L) / log 2 := le_trans (by exact_mod_cast hkle) (Nat.floor_le hnn)
    have hmul := mul_le_mul_of_nonneg_right hfl hlog2_pos.le
    rw [div_mul_cancel₀ _ hlog2_pos.ne'] at hmul
    have hpow : (2 : ℝ) ^ k = exp ((k : ℝ) * log 2) := by
      rw [← rpow_natCast, rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm]
    rw [hpow, ← exp_log (by positivity : 0 < 2 * L)]
    exact exp_le_exp.mpr hmul
  have hKdy_le : (K_dy : ℝ) ≤ 3 * log L := by
    have hlog2_ge : (1 / 2 : ℝ) ≤ log 2 := by
      have h := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
      rw [log_div (by norm_num) (by norm_num), log_one, zero_sub] at h; linarith
    have hfl : (⌊log (2 * L) / log 2⌋₊ : ℝ) ≤ log (2 * L) / log 2 :=
      Nat.floor_le (div_nonneg (log_nonneg (by linarith)) hlog2_pos.le)
    have hlog2L : log (2 * L) ≤ log L + 1 := by
      rw [log_mul (by norm_num) hLpos.ne']
      linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hdiv : log (2 * L) / log 2 ≤ 2 * (log L + 1) := by
      rw [div_le_iff₀ hlog2_pos]; nlinarith
    push_cast [K_dy]; linarith
  -- Partition `Valid3` into 3 families of dyadic shells (`S`, `M₁`, `M₂` largest):
  let f3 (q : Finset (Fin G) × Finset (Fin G) × Finset (Fin G)) : ℝ :=
    (p / 3) ^ q.1.card * (p / 3) ^ q.2.1.card * (p / 3) ^ q.2.2.card *
      (U₀ q) ^ (log 3 - 2 / 3) * (u₁ q) ^ (-(2 / 3 : ℝ)) * (u₂ q) ^ (-(2 / 3 : ℝ))
  have hf3_nn : ∀ q ∈ Valid3, 0 ≤ f3 q := fun q hq => by
    have hq' := (mem_filter.mp hq).2
    have hU0_nn : 0 ≤ U₀ q := by
      unfold U₀
      have hnn : ∀ A : Finset (Fin G), 0 ≤ subSum (xHi L G) A := fun A => subSum_xHi_nonneg hL1 hG A
      linarith [hnn q.1, hnn q.2.1, hnn q.2.2]
    have hp_nn : 0 ≤ p / 3 := by linarith [hp.2.2.1]
    unfold f3
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (rpow_nonneg hU0_nn _))
      (rpow_nonneg (by linarith [hq'.2.2.2.1]) _))
      (rpow_nonneg (by linarith [hq'.2.2.2.2]) _)
  let ShA (k : ℕ) := Valid3.filter fun q =>
    (2 : ℝ) ^ k ≤ subSum (xHi L G) q.2.2 ∧
    subSum (xHi L G) q.1 ≤ (2 : ℝ) ^ (k + 1) ∧
    subSum (xHi L G) q.2.1 ≤ (2 : ℝ) ^ (k + 1) ∧
    subSum (xHi L G) q.2.2 ≤ (2 : ℝ) ^ (k + 1)
  let ShB (k : ℕ) := Valid3.filter fun q =>
    (2 : ℝ) ^ k ≤ subSum (xHi L G) q.1 ∧
    subSum (xHi L G) q.1 ≤ (2 : ℝ) ^ (k + 1) ∧
    subSum (xHi L G) q.2.1 ≤ (2 : ℝ) ^ (k + 1) ∧
    subSum (xHi L G) q.2.2 ≤ (2 : ℝ) ^ (k + 1)
  let ShC (k : ℕ) := Valid3.filter fun q =>
    (2 : ℝ) ^ k ≤ subSum (xHi L G) q.2.1 ∧
    subSum (xHi L G) q.1 ≤ (2 : ℝ) ^ (k + 1) ∧
    subSum (xHi L G) q.2.1 ≤ (2 : ℝ) ^ (k + 1) ∧
    subSum (xHi L G) q.2.2 ≤ (2 : ℝ) ^ (k + 1)
  have hcov3 : Valid3 ⊆ (range K_dy).biUnion (fun k => ShA k ∪ ShB k ∪ ShC k) := by
    intro q hq
    have hq' := (mem_filter.mp hq).2
    set m := max (subSum (xHi L G) q.1) (max (subSum (xHi L G) q.2.1) (subSum (xHi L G) q.2.2))
    have hm1 : 1 ≤ m := by
      by_cases h1 : q.1.Nonempty
      · obtain ⟨r, hr⟩ := h1
        have hx := (xHi_gt_one_and_le hL1 hG r).1
        have hle : xHi L G r ≤ subSum (xHi L G) q.1 :=
          single_le_sum (fun t _ => (xHi_nonneg hL1 hG t)) hr
        exact le_trans hx.le (le_trans hle (le_max_left _ _))
      · rw [not_nonempty_iff_eq_empty] at h1
        have h0 : subSum (xHi L G) q.1 = 0 := by rw [h1]; simp [subSum]
        have hS1 : 1 ≤ subSum (xHi L G) q.2.2 := by linarith [hq'.2.2.2.1]
        exact le_trans hS1 (le_trans (le_max_right _ _) (le_max_right _ _))
    have hm_le : m ≤ 2 * L := max_le (by linarith) (max_le (by linarith) (by linarith))
    set k := ⌊log m / log 2⌋₊
    have hk_lt : k < K_dy := by
      have hle : k ≤ ⌊log (2 * L) / log 2⌋₊ :=
        Nat.floor_mono (div_le_div_of_nonneg_right (log_le_log (by linarith) hm_le) hlog2_pos.le)
      omega
    have h2k : (2 : ℝ) ^ k ≤ m := by
      have hnn : 0 ≤ log m / log 2 := div_nonneg (log_nonneg hm1) hlog2_pos.le
      have hmul := mul_le_mul_of_nonneg_right (Nat.floor_le hnn) hlog2_pos.le
      rw [div_mul_cancel₀ _ hlog2_pos.ne'] at hmul
      have hpow : (2 : ℝ) ^ k = exp ((k : ℝ) * log 2) := by
        rw [← rpow_natCast, rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm]
      rw [hpow, ← exp_log (by linarith : 0 < m)]
      exact exp_le_exp.mpr hmul
    have hm_2kp1 : m ≤ (2 : ℝ) ^ (k + 1) := by
      have hlt := Nat.lt_floor_add_one (log m / log 2)
      have hmul := mul_lt_mul_of_pos_right hlt hlog2_pos
      rw [div_mul_cancel₀ _ hlog2_pos.ne'] at hmul
      have hpow : (2 : ℝ) ^ (k + 1) = exp (((k + 1 : ℕ) : ℝ) * log 2) := by
        rw [← rpow_natCast, rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm]
      rw [hpow, ← exp_log (by linarith : 0 < m)]
      exact exp_le_exp.mpr (by push_cast; linarith)
    have hle1 : subSum (xHi L G) q.1 ≤ (2 : ℝ) ^ (k + 1) := le_trans (le_max_left _ _) hm_2kp1
    have hle2 : subSum (xHi L G) q.2.1 ≤ (2 : ℝ) ^ (k + 1) :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm_2kp1
    have hleS : subSum (xHi L G) q.2.2 ≤ (2 : ℝ) ^ (k + 1) :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm_2kp1
    refine mem_biUnion.mpr ⟨k, mem_range.mpr hk_lt, ?_⟩
    rcases max_choice (subSum (xHi L G) q.1) (max (subSum (xHi L G) q.2.1) (subSum (xHi L G) q.2.2)) with hmEq | hmEq
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hq, hmEq ▸ h2k, hle1, hle2, hleS⟩))
    · rcases max_choice (subSum (xHi L G) q.2.1) (subSum (xHi L G) q.2.2) with hmEq2 | hmEq2
      · exact mem_union_right _ (mem_filter.mpr ⟨hq, (hmEq.trans hmEq2) ▸ h2k, hle1, hle2, hleS⟩)
      · exact mem_union_left _ (mem_union_left _
          (mem_filter.mpr ⟨hq, (hmEq.trans hmEq2) ▸ h2k, hle1, hle2, hleS⟩))
  -- Bound each shell `ShA k`, `ShB k`, `ShC k`:
  have hU0_shell : ∀ (k : ℕ) (q : Finset (Fin G) × Finset (Fin G) × Finset (Fin G)),
      subSum (xHi L G) q.1 ≤ (2 : ℝ) ^ (k + 1) →
      subSum (xHi L G) q.2.1 ≤ (2 : ℝ) ^ (k + 1) →
      subSum (xHi L G) q.2.2 ≤ (2 : ℝ) ^ (k + 1) →
      (U₀ q) ^ (log 3 - 2 / 3) ≤ 8 * ((2 : ℝ) ^ k) ^ (log 3 - 2 / 3) := by
    intro k q h1 h2 hS
    have hU0_nn : 0 ≤ U₀ q := by
      unfold U₀
      have hnn : ∀ A : Finset (Fin G), 0 ≤ subSum (xHi L G) A := fun A => subSum_xHi_nonneg hL1 hG A
      linarith [hnn q.1, hnn q.2.1, hnn q.2.2]
    have h2k_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
    have hU0_le : U₀ q ≤ 8 * (2 : ℝ) ^ k := by
      unfold U₀; rw [pow_succ'] at h1 h2 hS; linarith
    have hexp_pos : 0 ≤ log 3 - 2 / 3 := by have := log_three_gt_d9; linarith
    have hexp_le1 : log 3 - 2 / 3 ≤ 1 := by have := log_three_lt_d9; linarith
    calc (U₀ q) ^ (log 3 - 2 / 3)
        ≤ (8 * (2 : ℝ) ^ k) ^ (log 3 - 2 / 3) := rpow_le_rpow hU0_nn hU0_le hexp_pos
      _ = (8 : ℝ) ^ (log 3 - 2 / 3) * ((2 : ℝ) ^ k) ^ (log 3 - 2 / 3) :=
            mul_rpow (by norm_num) (by positivity)
      _ ≤ 8 * ((2 : ℝ) ^ k) ^ (log 3 - 2 / 3) := by
            have h8 : (8 : ℝ) ^ (log 3 - 2 / 3) ≤ (8 : ℝ) ^ (1 : ℝ) :=
              rpow_le_rpow_of_exponent_le (by norm_num) hexp_le1
            rw [rpow_one] at h8
            exact mul_le_mul_of_nonneg_right h8 (rpow_nonneg (by positivity) _)
  have hBk_sum : ∀ k : ℕ,
      ∑ A ∈ (binsLe L G ((2 : ℝ) ^ (k + 1))).powerset, (p / 3) ^ A.card ≤ 2 * ((2 : ℝ) ^ k) ^ (1 / 3 : ℝ) := by
    intro k
    have h2 : (2 : ℝ) ^ (1 / 3 : ℝ) ≤ 2 := by
      have : (2 : ℝ) ^ (1 / 3 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      simpa using this
    calc ∑ A ∈ (binsLe L G ((2 : ℝ) ^ (k + 1))).powerset, (p / 3) ^ A.card
        ≤ ((2 : ℝ) ^ (k + 1)) ^ (1 / 3 : ℝ) :=
            sum_pow_one_third_le hL1 hG (by linarith) (u := (2 : ℝ) ^ (k + 1)) (one_le_pow₀ (by norm_num))
      _ = (2 * (2 : ℝ) ^ k) ^ (1 / 3 : ℝ) := by rw [pow_succ']
      _ = (2 : ℝ) ^ (1 / 3 : ℝ) * ((2 : ℝ) ^ k) ^ (1 / 3 : ℝ) := mul_rpow (by norm_num) (by positivity)
      _ ≤ 2 * ((2 : ℝ) ^ k) ^ (1 / 3 : ℝ) := mul_le_mul_of_nonneg_right h2 (rpow_nonneg (by positivity) _)
  have hShA_le : ∀ k : ℕ, ∑ q ∈ ShA k, f3 q ≤ 64 * ((2 : ℝ) ^ k) ^ (log 3 - 1) := by
    intro k
    set Bk := (binsLe L G ((2 : ℝ) ^ (k + 1))).powerset
    have hsub : ShA k ⊆ Bk ×ˢ Bk ×ˢ Bk := by
      intro q hq
      have hq' := (mem_filter.mp hq).2
      simp only [Bk, mem_product, mem_powerset]
      refine ⟨?_, ?_, ?_⟩ <;> intro r hr <;> simp only [binsLe, mem_filter, mem_univ, true_and]
      · exact le_trans (single_le_sum (fun t _ => (xHi_nonneg hL1 hG t)) hr) hq'.2.1
      · exact le_trans (single_le_sum (fun t _ => (xHi_nonneg hL1 hG t)) hr) hq'.2.2.1
      · exact le_trans (single_le_sum (fun t _ => (xHi_nonneg hL1 hG t)) hr) hq'.2.2.2
    have h2k_pos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    calc ∑ q ∈ ShA k, f3 q
        ≤ ∑ q ∈ ShA k, (p / 3) ^ q.1.card * (p / 3) ^ q.2.1.card * (p / 3) ^ q.2.2.card *
            (8 * ((2 : ℝ) ^ k) ^ (log 3 - 2 / 3)) * ((2 : ℝ) ^ k) ^ (-(2 / 3 : ℝ)) *
            ((2 : ℝ) ^ k) ^ (-(2 / 3 : ℝ)) := by
            refine sum_le_sum fun q hq => ?_
            have hq' := (mem_filter.mp hq).2
            have hnn : ∀ A : Finset (Fin G), 0 ≤ subSum (xHi L G) A := fun A => subSum_xHi_nonneg hL1 hG A
            have hu1_ge : (2 : ℝ) ^ k ≤ u₁ q := by unfold u₁; linarith [hnn q.1]
            have hu2_ge : (2 : ℝ) ^ k ≤ u₂ q := by unfold u₂; linarith [hnn q.2.1]
            have hU := hU0_shell k q hq'.2.1 hq'.2.2.1 hq'.2.2.2
            have hr1 := rpow_le_rpow_of_nonpos h2k_pos hu1_ge (by norm_num : (-(2 / 3 : ℝ)) ≤ 0)
            have hr2 := rpow_le_rpow_of_nonpos h2k_pos hu2_ge (by norm_num : (-(2 / 3 : ℝ)) ≤ 0)
            have hp_nn : 0 ≤ (p / 3) ^ q.1.card * (p / 3) ^ q.2.1.card * (p / 3) ^ q.2.2.card := by
              have := hp.2.2.1.le; positivity
            unfold f3
            have hU0_nn : 0 ≤ (U₀ q) ^ (log 3 - 2 / 3) := by
              apply rpow_nonneg; unfold U₀; linarith [hnn q.1, hnn q.2.1, hnn q.2.2]
            have hmul1 : (U₀ q) ^ (log 3 - 2 / 3) * (u₁ q) ^ (-(2 / 3 : ℝ)) ≤
                (8 * ((2 : ℝ) ^ k) ^ (log 3 - 2 / 3)) * ((2 : ℝ) ^ k) ^ (-(2 / 3 : ℝ)) :=
              mul_le_mul hU hr1 (rpow_nonneg (by linarith) _) (by positivity)
            have hmul2 := mul_le_mul hmul1 hr2 (rpow_nonneg (by linarith) _) (by positivity)
            have := mul_le_mul_of_nonneg_left hmul2 hp_nn
            linarith
      _ ≤ ∑ q ∈ Bk ×ˢ Bk ×ˢ Bk, (p / 3) ^ q.1.card * (p / 3) ^ q.2.1.card * (p / 3) ^ q.2.2.card *
            (8 * ((2 : ℝ) ^ k) ^ (log 3 - 2 / 3)) * ((2 : ℝ) ^ k) ^ (-(2 / 3 : ℝ)) *
            ((2 : ℝ) ^ k) ^ (-(2 / 3 : ℝ)) := by
            refine sum_le_sum_of_subset_of_nonneg hsub fun q _ _ => ?_
            have := hp.2.2.1.le; positivity
      _ = (∑ A ∈ Bk, (p / 3) ^ A.card) ^ 3 *
            (8 * ((2 : ℝ) ^ k) ^ (log 3 - 2 / 3) * ((2 : ℝ) ^ k) ^ (-(2 / 3 : ℝ)) *
              ((2 : ℝ) ^ k) ^ (-(2 / 3 : ℝ))) := by
            have h1 : ∀ q : Finset (Fin G) × Finset (Fin G) × Finset (Fin G),
                (p / 3) ^ q.1.card * (p / 3) ^ q.2.1.card * (p / 3) ^ q.2.2.card *
                  (8 * ((2 : ℝ) ^ k) ^ (log 3 - 2 / 3)) * ((2 : ℝ) ^ k) ^ (-(2 / 3 : ℝ)) *
                  ((2 : ℝ) ^ k) ^ (-(2 / 3 : ℝ)) =
                ((p / 3) ^ q.1.card * ((p / 3) ^ q.2.1.card * (p / 3) ^ q.2.2.card)) *
                  (8 * ((2 : ℝ) ^ k) ^ (log 3 - 2 / 3) * ((2 : ℝ) ^ k) ^ (-(2 / 3 : ℝ)) *
                    ((2 : ℝ) ^ k) ^ (-(2 / 3 : ℝ))) := fun _ => by ring
            simp_rw [h1, ← sum_mul]
            congr 1
            rw [sum_product, pow_three]
            have hinner : ∀ a ∈ Bk, ∑ bc ∈ Bk ×ˢ Bk, (p / 3) ^ a.card * ((p / 3) ^ bc.1.card * (p / 3) ^ bc.2.card) =
                (p / 3) ^ a.card * ((∑ b ∈ Bk, (p / 3) ^ b.card) * (∑ c ∈ Bk, (p / 3) ^ c.card)) := fun a _ => by
              rw [← mul_sum, sum_product, sum_mul_sum]
            rw [sum_congr rfl hinner, ← sum_mul]
      _ ≤ (2 * ((2 : ℝ) ^ k) ^ (1 / 3 : ℝ)) ^ 3 *
            (8 * ((2 : ℝ) ^ k) ^ (log 3 - 2 / 3) * ((2 : ℝ) ^ k) ^ (-(2 / 3 : ℝ)) *
              ((2 : ℝ) ^ k) ^ (-(2 / 3 : ℝ))) := by
            refine mul_le_mul_of_nonneg_right
              (pow_le_pow_left₀ (sum_nonneg fun _ _ => pow_nonneg (by linarith [hp.2.2.1]) _) (hBk_sum k) 3)
              (by positivity)
      _ = 64 * ((2 : ℝ) ^ k) ^ (log 3 - 1) := by
            have hcube : (2 * ((2 : ℝ) ^ k) ^ (1 / 3 : ℝ)) ^ 3 = 8 * (2 : ℝ) ^ k := by
              rw [mul_pow, ← rpow_natCast (((2 : ℝ) ^ k) ^ (1 / 3 : ℝ)), ← rpow_mul h2k_pos.le]
              norm_num
            rw [hcube]
            have hpow_comb : (2 : ℝ) ^ k * (((2 : ℝ) ^ k) ^ (log 3 - 2 / 3) *
                ((2 : ℝ) ^ k) ^ (-(2 / 3 : ℝ)) * ((2 : ℝ) ^ k) ^ (-(2 / 3 : ℝ))) =
                ((2 : ℝ) ^ k) ^ (log 3 - 1) := by
              conv_lhs => arg 1; rw [← rpow_one ((2 : ℝ) ^ k)]
              rw [← mul_assoc, ← mul_assoc, ← rpow_add h2k_pos, ← rpow_add h2k_pos, ← rpow_add h2k_pos]
              congr 1; ring
            calc 8 * (2 : ℝ) ^ k *
                  (8 * ((2 : ℝ) ^ k) ^ (log 3 - 2 / 3) * ((2 : ℝ) ^ k) ^ (-(2 / 3 : ℝ)) *
                    ((2 : ℝ) ^ k) ^ (-(2 / 3 : ℝ)))
                = 64 * ((2 : ℝ) ^ k * (((2 : ℝ) ^ k) ^ (log 3 - 2 / 3) *
                    ((2 : ℝ) ^ k) ^ (-(2 / 3 : ℝ)) * ((2 : ℝ) ^ k) ^ (-(2 / 3 : ℝ)))) := by ring
              _ = 64 * ((2 : ℝ) ^ k) ^ (log 3 - 1) := by rw [hpow_comb]
  have hShB_le : ∀ k : ℕ, ∑ q ∈ ShB k, f3 q ≤ 64 * ((k : ℝ) + 2) * ((2 : ℝ) ^ k) ^ (log 3 - 1) := by
    intro k
    set Bk := (binsLe L G ((2 : ℝ) ^ (k + 1))).powerset
    set Pk := P_all.filter fun A => subSum (xHi L G) A ≤ (2 : ℝ) ^ (k + 1)
    set Qk := (Pk ×ˢ Pk).filter fun AB => 1 ≤ subSum (xHi L G) AB.1 + subSum (xHi L G) AB.2
    have hsub : ShB k ⊆ Bk ×ˢ Qk := by
      intro ⟨M₁, M₂, S⟩ hq
      have hq1 := (mem_filter.mp hq).1
      have hq2 := (mem_filter.mp hq).2
      have hv := (mem_filter.mp hq1).2
      simp only [Bk, Qk, Pk, P_all, mem_product, mem_filter, mem_powerset,
        subset_univ, true_and]
      refine ⟨?_, ⟨hq2.2.2.1, hq2.2.2.2⟩, hv.2.2.2.2⟩
      intro r hr
      simp only [binsLe, mem_filter, mem_univ, true_and]
      exact le_trans (single_le_sum (fun t _ => (xHi_nonneg hL1 hG t)) hr) hq2.2.1
    have h2k_pos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    calc ∑ q ∈ ShB k, f3 q
        ≤ ∑ q ∈ ShB k, (p / 3) ^ q.1.card * (p / 3) ^ q.2.1.card * (p / 3) ^ q.2.2.card *
            (8 * ((2 : ℝ) ^ k) ^ (log 3 - 2 / 3)) * ((2 : ℝ) ^ k) ^ (-(2 / 3 : ℝ)) *
            (u₂ q) ^ (-(2 / 3 : ℝ)) := by
            refine sum_le_sum fun q hq => ?_
            have hq1 := (mem_filter.mp hq).1
            have hq2 := (mem_filter.mp hq).2
            have hv := (mem_filter.mp hq1).2
            have hnn : ∀ A : Finset (Fin G), 0 ≤ subSum (xHi L G) A := fun A => subSum_xHi_nonneg hL1 hG A
            have hu1_ge : (2 : ℝ) ^ k ≤ u₁ q := by unfold u₁; linarith [hnn q.2.2]
            have hU := hU0_shell k q hq2.2.1 hq2.2.2.1 hq2.2.2.2
            have hr1 := rpow_le_rpow_of_nonpos h2k_pos hu1_ge (by norm_num : (-(2 / 3 : ℝ)) ≤ 0)
            have hp_nn : 0 ≤ (p / 3) ^ q.1.card * (p / 3) ^ q.2.1.card * (p / 3) ^ q.2.2.card := by
              have := hp.2.2.1.le; positivity
            have hu2_nn : 0 ≤ (u₂ q) ^ (-(2 / 3 : ℝ)) := rpow_nonneg (by linarith [hv.2.2.2.2]) _
            have hmul1 : (U₀ q) ^ (log 3 - 2 / 3) * (u₁ q) ^ (-(2 / 3 : ℝ)) ≤
                (8 * ((2 : ℝ) ^ k) ^ (log 3 - 2 / 3)) * ((2 : ℝ) ^ k) ^ (-(2 / 3 : ℝ)) :=
              mul_le_mul hU hr1 (rpow_nonneg (by linarith) _) (by positivity)
            unfold f3
            have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmul1 hp_nn) hu2_nn
            linarith
      _ ≤ ∑ q ∈ Bk ×ˢ Qk, (p / 3) ^ q.1.card * (p / 3) ^ q.2.1.card * (p / 3) ^ q.2.2.card *
            (8 * ((2 : ℝ) ^ k) ^ (log 3 - 2 / 3)) * ((2 : ℝ) ^ k) ^ (-(2 / 3 : ℝ)) *
            (u₂ q) ^ (-(2 / 3 : ℝ)) := by
            refine sum_le_sum_of_subset_of_nonneg hsub fun q hq _ => ?_
            have hq2 := (mem_filter.mp (mem_product.mp hq).2).2
            have hp_nn : 0 ≤ p / 3 := by linarith [hp.2.2.1]
            exact mul_nonneg (by positivity) (rpow_nonneg (by unfold u₂; linarith) _)
      _ = (8 * ((2 : ℝ) ^ k) ^ (log 3 - 2 / 3) * ((2 : ℝ) ^ k) ^ (-(2 / 3 : ℝ))) *
            (∑ M₁ ∈ Bk, (p / 3) ^ M₁.card) *
            (∑ AB ∈ Qk, (p / 3) ^ AB.1.card * (p / 3) ^ AB.2.card *
              (subSum (xHi L G) AB.1 + subSum (xHi L G) AB.2) ^ (-(2 / 3 : ℝ))) := by
            rw [sum_product, mul_assoc, sum_mul, mul_sum]
            refine sum_congr rfl fun M₁ _ => ?_
            rw [mul_sum, mul_sum]
            refine sum_congr rfl fun AB _ => by unfold u₂; ring
      _ ≤ (8 * ((2 : ℝ) ^ k) ^ (log 3 - 2 / 3) * ((2 : ℝ) ^ k) ^ (-(2 / 3 : ℝ))) *
            (2 * ((2 : ℝ) ^ k) ^ (1 / 3 : ℝ)) * (4 * ((k : ℝ) + 2)) := by
            have hB := hBk_sum k
            have hD := dyadic_pair_sum_le hL1 hG (by linarith) k
            have hBnn : 0 ≤ ∑ M₁ ∈ Bk, (p / 3) ^ M₁.card :=
              sum_nonneg fun _ _ => pow_nonneg (by linarith [hp.2.2.1]) _
            have hDnn : 0 ≤ ∑ AB ∈ Qk, (p / 3) ^ AB.1.card * (p / 3) ^ AB.2.card *
                (subSum (xHi L G) AB.1 + subSum (xHi L G) AB.2) ^ (-(2 / 3 : ℝ)) :=
              sum_nonneg fun AB hAB => by
                have hge := (mem_filter.mp hAB).2
                have := hp.2.2.1.le
                exact mul_nonneg (by positivity) (rpow_nonneg (by linarith) _)
            have h1 := mul_le_mul_of_nonneg_left hB (by positivity : 0 ≤ 8 * ((2 : ℝ) ^ k) ^ (log 3 - 2 / 3) * ((2 : ℝ) ^ k) ^ (-(2 / 3 : ℝ)))
            exact mul_le_mul h1 hD hDnn (by positivity)
      _ = 64 * ((k : ℝ) + 2) * ((2 : ℝ) ^ k) ^ (log 3 - 1) := by
            have hpow : ((2 : ℝ) ^ k) ^ (log 3 - 2 / 3) * ((2 : ℝ) ^ k) ^ (-(2 / 3 : ℝ)) *
                ((2 : ℝ) ^ k) ^ (1 / 3 : ℝ) = ((2 : ℝ) ^ k) ^ (log 3 - 1) := by
              rw [← rpow_add h2k_pos, ← rpow_add h2k_pos]; congr 1; ring
            calc (8 * ((2 : ℝ) ^ k) ^ (log 3 - 2 / 3) * ((2 : ℝ) ^ k) ^ (-(2 / 3 : ℝ))) *
                  (2 * ((2 : ℝ) ^ k) ^ (1 / 3 : ℝ)) * (4 * ((k : ℝ) + 2))
                = 64 * ((k : ℝ) + 2) * (((2 : ℝ) ^ k) ^ (log 3 - 2 / 3) *
                    ((2 : ℝ) ^ k) ^ (-(2 / 3 : ℝ)) * ((2 : ℝ) ^ k) ^ (1 / 3 : ℝ)) := by ring
              _ = 64 * ((k : ℝ) + 2) * ((2 : ℝ) ^ k) ^ (log 3 - 1) := by rw [hpow]
  have hShC_le : ∀ k : ℕ, ∑ q ∈ ShC k, f3 q ≤ 64 * ((k : ℝ) + 2) * ((2 : ℝ) ^ k) ^ (log 3 - 1) := by
    intro k
    -- Exact symmetry with `ShB k` via `(M₁, M₂, S) ↦ (M₂, M₁, S)`:
    have hsym : ∑ q ∈ ShC k, f3 q = ∑ q ∈ ShB k, f3 q := by
      refine sum_nbij (fun q => (q.2.1, q.1, q.2.2)) ?_ ?_ ?_ ?_
      · intro ⟨M₁, M₂, S⟩ hq
        simp only [mem_coe, ShC, ShB, Valid3, P_all, mem_filter, mem_product,
          mem_powerset, subset_univ, true_and] at hq ⊢
        tauto
      · intro ⟨a₁, b₁, c₁⟩ _ ⟨a₂, b₂, c₂⟩ _ h
        simp only [Prod.mk.injEq] at h; rcases h with ⟨rfl, rfl, rfl⟩; rfl
      · intro ⟨M₁, M₂, S⟩ hq
        refine ⟨(M₂, M₁, S), ?_, rfl⟩
        simp only [mem_coe, ShC, ShB, Valid3, P_all, mem_filter, mem_product,
          mem_powerset, subset_univ, true_and] at hq ⊢
        tauto
      · intro ⟨M₁, M₂, S⟩ _
        unfold f3 U₀ u₁ u₂; dsimp; ring_nf
    rw [hsym]
    exact hShB_le k
  -- Sum over `k ∈ range K_dy`:
  have hValid3_le : ∑ q ∈ Valid3, f3 q ≤ 400 * ((K_dy : ℝ) + 2) * (K_dy : ℝ) * L ^ (log 3 - 1) := by
    have hexp_pos : 0 < log 3 - 1 := by have := log_three_gt_d9; linarith
    have hexp_le1 : log 3 - 1 ≤ 1 := by have := log_three_lt_d9; linarith
    have h2L_pow : ∀ k ∈ range K_dy, ((2 : ℝ) ^ k) ^ (log 3 - 1) ≤ 2 * L ^ (log 3 - 1) := by
      intro k hk
      calc ((2 : ℝ) ^ k) ^ (log 3 - 1)
          ≤ (2 * L) ^ (log 3 - 1) := rpow_le_rpow (by positivity) (h2k_le k hk) hexp_pos.le
        _ = (2 : ℝ) ^ (log 3 - 1) * L ^ (log 3 - 1) := mul_rpow (by norm_num) hLpos.le
        _ ≤ 2 * L ^ (log 3 - 1) := by
              have h2 : (2 : ℝ) ^ (log 3 - 1) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                rpow_le_rpow_of_exponent_le (by norm_num) hexp_le1
              rw [rpow_one] at h2
              exact mul_le_mul_of_nonneg_right h2 (rpow_nonneg hLpos.le _)
    have hterm_k : ∀ k ∈ range K_dy,
        ∑ q ∈ ShA k ∪ ShB k ∪ ShC k, f3 q ≤ 400 * ((K_dy : ℝ) + 2) * L ^ (log 3 - 1) := by
      intro k hk
      have hkle : (k : ℝ) ≤ (K_dy : ℝ) := by exact_mod_cast le_of_lt (mem_range.mp hk)
      have hnnA : ∀ q ∈ ShA k ∪ ShB k, 0 ≤ f3 q := fun q hq => by
        rcases mem_union.mp hq with h | h <;> exact hf3_nn q (mem_filter.mp h).1
      have hnnC : ∀ q ∈ ShC k, 0 ≤ f3 q := fun q hq => hf3_nn q (mem_filter.mp hq).1
      have hnnB : ∀ q ∈ ShB k, 0 ≤ f3 q := fun q hq => hf3_nn q (mem_filter.mp hq).1
      have hnnA0 : ∀ q ∈ ShA k, 0 ≤ f3 q := fun q hq => hf3_nn q (mem_filter.mp hq).1
      have h1 : ∑ q ∈ ShA k ∪ ShB k ∪ ShC k, f3 q ≤
          (∑ q ∈ ShA k, f3 q) + (∑ q ∈ ShB k, f3 q) + (∑ q ∈ ShC k, f3 q) := by
        have hAB : ∑ q ∈ ShA k ∪ ShB k, f3 q ≤ (∑ q ∈ ShA k, f3 q) + (∑ q ∈ ShB k, f3 q) :=
          sum_union_le_of_nonneg (fun q hq => by rcases mem_union.mp hq with h | h <;> [exact hnnA0 q h; exact hnnB q h])
        have hABC : ∑ q ∈ (ShA k ∪ ShB k) ∪ ShC k, f3 q ≤
            (∑ q ∈ ShA k ∪ ShB k, f3 q) + (∑ q ∈ ShC k, f3 q) :=
          sum_union_le_of_nonneg (fun q hq => by rcases mem_union.mp hq with h | h <;> [exact hnnA q h; exact hnnC q h])
        linarith
      have h2 := hShA_le k
      have h3 := hShB_le k
      have h4 := hShC_le k
      have h5 := h2L_pow k hk
      have hpow_nn : 0 ≤ ((2 : ℝ) ^ k) ^ (log 3 - 1) := rpow_nonneg (by positivity) _
      have h6 : 64 + 64 * ((k : ℝ) + 2) + 64 * ((k : ℝ) + 2) ≤ 200 * ((K_dy : ℝ) + 2) := by linarith
      calc ∑ q ∈ ShA k ∪ ShB k ∪ ShC k, f3 q
          ≤ (64 + 64 * ((k : ℝ) + 2) + 64 * ((k : ℝ) + 2)) * ((2 : ℝ) ^ k) ^ (log 3 - 1) := by linarith
        _ ≤ (200 * ((K_dy : ℝ) + 2)) * (2 * L ^ (log 3 - 1)) :=
              mul_le_mul h6 h5 hpow_nn (by positivity)
        _ = 400 * ((K_dy : ℝ) + 2) * L ^ (log 3 - 1) := by ring
    have hbi_nn : ∀ q ∈ (range K_dy).biUnion (fun k => ShA k ∪ ShB k ∪ ShC k), 0 ≤ f3 q := by
      intro q hq
      obtain ⟨k, _, hk⟩ := mem_biUnion.mp hq
      rcases mem_union.mp hk with h | h
      · rcases mem_union.mp h with h' | h'
        · exact hf3_nn q (mem_filter.mp h').1
        · exact hf3_nn q (mem_filter.mp h').1
      · exact hf3_nn q (mem_filter.mp h).1
    calc ∑ q ∈ Valid3, f3 q
        ≤ ∑ q ∈ (range K_dy).biUnion (fun k => ShA k ∪ ShB k ∪ ShC k), f3 q :=
            sum_le_sum_of_subset_of_nonneg hcov3 fun q hq _ => hbi_nn q hq
      _ ≤ ∑ k ∈ range K_dy, ∑ q ∈ ShA k ∪ ShB k ∪ ShC k, f3 q :=
            sum_biUnion_le_of_nonneg hbi_nn
      _ ≤ ∑ _k ∈ range K_dy, 400 * ((K_dy : ℝ) + 2) * L ^ (log 3 - 1) := sum_le_sum hterm_k
      _ = 400 * ((K_dy : ℝ) + 2) * (K_dy : ℝ) * L ^ (log 3 - 1) := by
            rw [sum_const, card_range, nsmul_eq_mul]; ring
  -- Step 5: Numeric domination `40000 * (K_dy + 2) * K_dy * η^2 * L^(7/1000 + log 3 - 1) ≤ L^(7/100) / 768000`.
  have hfinal_num : 100 * η ^ 2 * L ^ (7 / 1000 : ℝ) *
      (400 * ((K_dy : ℝ) + 2) * (K_dy : ℝ) * L ^ (log 3 - 1)) ≤ L ^ (7 / 100 : ℝ) / 768000 := by
    have hKprod : 40000 * ((K_dy : ℝ) + 2) * (K_dy : ℝ) ≤ 500000 * (log L) ^ 2 := by
      have h1 : (K_dy : ℝ) + 2 ≤ 4 * log L := by linarith
      have h2 : (K_dy : ℝ) ≤ 3 * log L := hKdy_le
      have hKnn : 0 ≤ (K_dy : ℝ) := Nat.cast_nonneg _
      nlinarith
    have hpow_comb : η ^ 2 * L ^ (7 / 1000 : ℝ) * L ^ (log 3 - 1) ≤ L ^ (56 / 1000 : ℝ) := by
      have hη2 : η ^ 2 = L ^ (-(1 / 20 : ℝ)) := by
        unfold η
        rw [← rpow_natCast, ← rpow_mul hLpos.le]
        norm_num
      rw [hη2, ← rpow_add hLpos, ← rpow_add hLpos]
      apply rpow_le_rpow_of_exponent_le hL1.le
      have := log_three_lt_d9
      linarith
    -- Need `500000 * 768000 * (log L)^2 ≤ L^(14/1000)`:
    have hdom : 500000 * (log L) ^ 2 ≤ L ^ (14 / 1000 : ℝ) / 768000 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 768000)]
      set x := log L
      have hx : (10000000000 : ℝ) ≤ x := hlogL_ge
      set t := (14 / 1000 : ℝ) * x
      have ht_pos : 0 < t := by positivity
      have hexp_ge : (t / 5) ^ 5 ≤ L ^ (14 / 1000 : ℝ) := by
        rw [rpow_def_of_pos hLpos]
        have heq : exp (x * (14 / 1000 : ℝ)) = (exp (t / 5)) ^ 5 := by
          rw [← exp_nat_mul]; congr 1; unfold t; ring
        rw [heq]
        exact pow_le_pow_left₀ (by positivity) (by linarith [add_one_le_exp (t / 5)]) 5
      -- `(t/5)^5 = (14/5000)^5 * x^5 ≥ 10^(-13) * x^3 * x^2 ≥ 10^14 * x^2 ≥ 500000 * 768000 * x^2`!
      have ht5 : (500000 * x ^ 2) * 768000 ≤ (t / 5) ^ 5 := by
        have hx3 : (10 : ℝ) ^ 27 ≤ x ^ 3 := by
          have : ((10000000000 : ℝ)) ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) hx 3
          linarith [show (10 : ℝ) ^ 27 ≤ ((10000000000 : ℝ)) ^ 3 by norm_num]
        have hcoef : (14 / 5000 : ℝ) ^ 5 * (10 : ℝ) ^ 27 ≥ 500000 * 768000 := by norm_num
        have hrew : (t / 5) ^ 5 = ((14 / 5000 : ℝ) ^ 5 * x ^ 3) * x ^ 2 := by unfold t; ring
        rw [hrew]
        have h1 : (500000 * 768000 : ℝ) ≤ (14 / 5000 : ℝ) ^ 5 * x ^ 3 := by nlinarith
        nlinarith [sq_nonneg x]
      linarith
    have hsplit : L ^ (56 / 1000 : ℝ) * (L ^ (14 / 1000 : ℝ) / 768000) = L ^ (7 / 100 : ℝ) / 768000 := by
      rw [mul_div_assoc', ← rpow_add hLpos]
      norm_num
    calc 100 * η ^ 2 * L ^ (7 / 1000 : ℝ) * (400 * ((K_dy : ℝ) + 2) * (K_dy : ℝ) * L ^ (log 3 - 1))
        = (40000 * ((K_dy : ℝ) + 2) * (K_dy : ℝ)) * (η ^ 2 * L ^ (7 / 1000 : ℝ) * L ^ (log 3 - 1)) := by ring
      _ ≤ (500000 * (log L) ^ 2) * L ^ (56 / 1000 : ℝ) :=
            mul_le_mul hKprod hpow_comb (by positivity) (by positivity)
      _ ≤ (L ^ (14 / 1000 : ℝ) / 768000) * L ^ (56 / 1000 : ℝ) :=
            mul_le_mul_of_nonneg_right hdom (rpow_nonneg hLpos.le _)
      _ = L ^ (7 / 100 : ℝ) / 768000 := by rw [mul_comm]; exact hsplit
  have hcomb := mul_le_mul_of_nonneg_left hValid3_le (by positivity : 0 ≤ 100 * η ^ 2 * L ^ (7 / 1000 : ℝ))
  linarith [hstep3, hcomb, hfinal_num]

/-- Combined grid score lower bound: `E[cellScore] ≥ L^(7/100) / 768000`. -/
lemma expected_cellScore_ge {L : ℝ} {G : ℕ}
    (hL : exp 10000000000 ≤ L) (hG : 0 < G)
    (hstep : 2000 * L * gridDelta L G ≤ L ^ (-(1 / 40 : ℝ)) / 4) :
    L ^ (7 / 100 : ℝ) / 768000 ≤
      ∑ b : Fin G → Bool, bernProb (gridP L G) b * (cellScore L G (L ^ (-(1 / 40 : ℝ))) b : ℝ) := by
  set η : ℝ := L ^ (-(1 / 40 : ℝ))
  have hLpos : 0 < L := lt_of_lt_of_le (exp_pos _) hL
  have hL1 : 1 < L := (log_pos_iff hLpos.le).mp (by
    have := log_le_log (exp_pos _) hL; rw [log_exp] at this; linarith)
  have hηle : η ≤ 1 / 2 := by
    unfold η
    rw [rpow_def_of_pos hLpos]
    have hlogL : (10000000000 : ℝ) ≤ log L := by
      have := log_le_log (exp_pos _) hL; rwa [log_exp] at this
    have h2 : exp (-2) ≤ 1 / 2 := by
      rw [exp_neg, one_div]
      exact inv_anti₀ (by norm_num) (by linarith [add_one_le_exp (2 : ℝ)])
    exact le_trans (exp_le_exp.mpr (by linarith)) h2
  have hΔle : gridDelta L G ≤ 1 := by
    have : (100000 : ℝ) ≤ L := by linarith [add_one_le_exp (10000000000 : ℝ)]
    have : 2000 * L * gridDelta L G ≤ 1 / 8 := by linarith
    nlinarith
  have hp := gridP_bounds hL1 hG hΔle
  have hprob_nn : ∀ b : Fin G → Bool, 0 ≤ bernProb (gridP L G) b := fun b => bernProb_nonneg hp.2.2.1.le hp.2.2.2.le b
  have hU := expected_uPairs_typ_ge hL hG hstep
  have hB := expected_badTriples_typ_le hL hG hstep
  have hsum : (∑ b : Fin G → Bool, bernProb (gridP L G) b *
        (if isTyp L G b then ((uPairs L G η b).card : ℝ) else 0)) ≤
      (∑ b : Fin G → Bool, bernProb (gridP L G) b * (cellScore L G η b : ℝ)) +
      (∑ b : Fin G → Bool, bernProb (gridP L G) b *
        (if isTyp L G b then ((badTriples L G η b).card : ℝ) else 0)) := by
    rw [← sum_add_distrib]
    refine sum_le_sum fun b _ => ?_
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (hprob_nn b)
    unfold cellScore
    by_cases ht : isTyp L G b
    · simp only [if_pos ht]; exact uPairs_le_goodPairs_add_badTriples L G η b
    · simp [ht]
  linarith

/-- Existence of a grid `(L, G)` achieving arbitrarily large normalized score `γ * E[cellScore] / log (2*L/γ)`
and satisfying all fineness conditions required for the integer transfer. -/
lemma exists_good_grid {ε M_target : ℝ} (hε : 0 < ε) (hM : 1 ≤ M_target) :
    ∃ (L : ℝ) (G : ℕ),
      exp 10000000000 ≤ L ∧
      10000000 / ε ≤ L ∧
      0 < G ∧
      40 * log L * L * gridDelta L G ≤ L ^ (-(1 / 40 : ℝ)) ∧
      M_target * log (2 * L / ((ε / 400) * L ^ (-(1 / 40 : ℝ)))) ≤
        ((ε / 400) * L ^ (-(1 / 40 : ℝ))) *
          ∑ b : Fin G → Bool, bernProb (gridP L G) b * (cellScore L G (L ^ (-(1 / 40 : ℝ))) b : ℝ) := by
  set X : ℝ := max 10000000000 (max (log (800 / ε)) (2000000000000 * M_target / ε))
  have hX1 : (10000000000 : ℝ) ≤ X := le_max_left _ _
  have hX2 : log (800 / ε) ≤ X := le_trans (le_max_left _ _) (le_max_right _ _)
  have hX3 : 2000000000000 * M_target / ε ≤ X := le_trans (le_max_right _ _) (le_max_right _ _)
  set L : ℝ := exp X
  have hL : exp 10000000000 ≤ L := exp_le_exp.mpr hX1
  have hLpos : 0 < L := exp_pos X
  have hlogL : log L = X := log_exp X
  set η : ℝ := L ^ (-(1 / 40 : ℝ))
  have hηpos : 0 < η := rpow_pos_of_pos hLpos _
  set G : ℕ := ⌈40 * X * X * L / η⌉₊ + 1
  have hG : 0 < G := Nat.succ_pos _
  have hfine : 40 * log L * L * gridDelta L G ≤ η := by
    rw [hlogL]
    unfold gridDelta
    rw [hlogL]
    have hG_ge : 40 * X * X * L / η ≤ (G : ℝ) := by
      have := Nat.le_ceil (40 * X * X * L / η)
      push_cast [G]; linarith
    have hGpos : (0 : ℝ) < (G : ℝ) := by positivity
    calc 40 * X * L * (X / (G : ℝ))
        = (40 * X * X * L) / (G : ℝ) := by ring
      _ ≤ (40 * X * X * L) / (40 * X * X * L / η) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hG_ge
      _ = η := by field_simp [hηpos.ne', (show (0 : ℝ) < 40 * X * X * L by positivity).ne']
  have hstep : 2000 * L * gridDelta L G ≤ η / 4 := by
    have hΔnn : 0 ≤ gridDelta L G := div_nonneg (by rw [hlogL]; linarith) (by positivity)
    have hLΔnn : 0 ≤ L * gridDelta L G := mul_nonneg hLpos.le hΔnn
    have : 8000 * L * gridDelta L G ≤ 40 * log L * L * gridDelta L G := by
      rw [hlogL]; nlinarith
    linarith
  have hscore := expected_cellScore_ge hL hG hstep
  have hQ_log : log (2 * L / ((ε / 400) * η)) ≤ 3 * X := by
    have hrew : 2 * L / ((ε / 400) * η) = (800 / ε) * L ^ (41 / 40 : ℝ) := by
      unfold η
      have hL1 : L / L ^ (-(1 / 40 : ℝ)) = L ^ (41 / 40 : ℝ) := by
        conv_lhs => arg 1; rw [← rpow_one L]
        rw [← rpow_sub hLpos]; norm_num
      calc 2 * L / ((ε / 400) * L ^ (-(1 / 40 : ℝ)))
          = (800 / ε) * (L / L ^ (-(1 / 40 : ℝ))) := by field_simp [hε.ne', (rpow_pos_of_pos hLpos _).ne']; ring
        _ = (800 / ε) * L ^ (41 / 40 : ℝ) := by rw [hL1]
    rw [hrew, log_mul (by positivity) (rpow_pos_of_pos hLpos _).ne', log_rpow hLpos, hlogL]
    linarith
  have hprod_ge : M_target * (3 * X) ≤ ((ε / 400) * η) * (L ^ (7 / 100 : ℝ) / 768000) := by
    have hpow : η * L ^ (7 / 100 : ℝ) = exp ((9 / 200 : ℝ) * X) := by
      unfold η
      rw [← rpow_add hLpos, rpow_def_of_pos hLpos, hlogL]
      congr 1; ring
    have hexp_ge : (9 / 400 : ℝ) ^ 2 * X ^ 2 ≤ exp ((9 / 200 : ℝ) * X) := by
      have h1 : exp ((9 / 200 : ℝ) * X) = (exp ((9 / 400 : ℝ) * X)) ^ 2 := by
        rw [← exp_nat_mul]; congr 1; ring
      rw [h1, ← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith [add_one_le_exp ((9 / 400 : ℝ) * X)]) 2
    have hX_dom : 921600000 * M_target / ε ≤ (9 / 400 : ℝ) ^ 2 * X := by
      have h1 : (9 / 400 : ℝ) ^ 2 * (2000000000000 * M_target / ε) = 1012500000 * (M_target / ε) := by ring
      have h2 : (9 / 400 : ℝ) ^ 2 * (2000000000000 * M_target / ε) ≤ (9 / 400 : ℝ) ^ 2 * X :=
        mul_le_mul_of_nonneg_left hX3 (by positivity)
      have h3 : 921600000 * M_target / ε = 921600000 * (M_target / ε) := by ring
      have hpos_me : 0 < M_target / ε := by positivity
      linarith
    have h1 : (921600000 * M_target / ε) * X ≤ exp ((9 / 200 : ℝ) * X) := by
      have := mul_le_mul_of_nonneg_right hX_dom (by linarith : 0 ≤ X)
      linarith [show ((9 / 400 : ℝ) ^ 2 * X) * X = (9 / 400 : ℝ) ^ 2 * X ^ 2 by ring]
    have h2 : M_target * (3 * X) = ((ε / 400) / 768000) * ((921600000 * M_target / ε) * X) := by
      field_simp [hε.ne']; ring
    have h3 : ((ε / 400) * η) * (L ^ (7 / 100 : ℝ) / 768000) =
        ((ε / 400) / 768000) * exp ((9 / 200 : ℝ) * X) := by
      rw [← hpow]; ring
    rw [h2, h3]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have hLε : 10000000 / ε ≤ L := by
    have h1 : 10000000 / ε ≤ 2000000000000 * M_target / ε := by
      rw [div_le_div_iff_of_pos_right hε]; linarith
    have h2 : X ≤ L := by linarith [add_one_le_exp X]
    linarith
  refine ⟨L, G, hL, hLε, hG, hfine, ?_⟩
  have h1 : M_target * log (2 * L / ((ε / 400) * η)) ≤ M_target * (3 * X) :=
    mul_le_mul_of_nonneg_left hQ_log (by linarith)
  have h2 := mul_le_mul_of_nonneg_left hscore (by positivity : 0 ≤ (ε / 400) * η)
  linarith

/- ## Section 7: Transfer to Integers, `A_j`-Trimming, Second Moment, and Main Theorem -/

/- ### Part 7A: Smooth/Rough Factorization -/

/-- The `K`-smooth part of `n`: product of prime powers `p^{v_p(n)}` with `p ≤ K`. -/
noncomputable def smoothPart (K n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (· ≤ K), p ^ (n.factorization p)

/-- The `K`-rough part of `n`: product of prime powers `p^{v_p(n)}` with `K < p`. -/
noncomputable def roughPart (K n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p => K < p), p ^ (n.factorization p)

lemma smoothPart_pos (K n : ℕ) : 0 < smoothPart K n :=
  prod_pos fun p hp => pow_pos (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).pos _

lemma roughPart_pos (K n : ℕ) : 0 < roughPart K n :=
  prod_pos fun p hp => pow_pos (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).pos _

lemma smoothPart_mul_roughPart {K n : ℕ} (hn : 0 < n) :
    smoothPart K n * roughPart K n = n := by
  unfold smoothPart roughPart
  have hnot : n.primeFactors.filter (fun p => K < p) = n.primeFactors.filter (fun p => ¬(p ≤ K)) := by
    ext p; simp only [mem_filter, not_le]
  rw [hnot, prod_filter_mul_prod_filter_not]
  exact Nat.prod_factorization_pow_eq_self hn.ne'

lemma prime_dvd_smoothPart_le {K n p : ℕ} (hp : p.Prime) (hdvd : p ∣ smoothPart K n) :
    p ≤ K := by
  unfold smoothPart at hdvd
  obtain ⟨q, hq, hpq⟩ := hp.prime.exists_mem_finset_dvd hdvd
  have hq' := mem_filter.mp hq
  have hqP := Nat.prime_of_mem_primeFactors hq'.1
  have hpeq : p = q := (Nat.prime_dvd_prime_iff_eq hp hqP).mp (hp.dvd_of_dvd_pow hpq)
  subst hpeq; exact hq'.2

lemma prime_dvd_roughPart_gt {K n p : ℕ} (hp : p.Prime) (hdvd : p ∣ roughPart K n) :
    K < p := by
  unfold roughPart at hdvd
  obtain ⟨q, hq, hpq⟩ := hp.prime.exists_mem_finset_dvd hdvd
  have hq' := mem_filter.mp hq
  have hqP := Nat.prime_of_mem_primeFactors hq'.1
  have hpeq : p = q := (Nat.prime_dvd_prime_iff_eq hp hqP).mp (hp.dvd_of_dvd_pow hpq)
  subst hpeq; exact hq'.2

lemma coprime_smoothPart_roughPart (K n : ℕ) :
    Nat.Coprime (smoothPart K n) (roughPart K n) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hne
  have h1 := prime_dvd_smoothPart_le hp (dvd_trans hpg (Nat.gcd_dvd_left _ _))
  have h2 := prime_dvd_roughPart_gt hp (dvd_trans hpg (Nat.gcd_dvd_right _ _))
  omega

lemma smoothPart_mul_of_gt {K D m : ℕ} (hD : 0 < D) (hm : 0 < m)
    (hDgt : ∀ p : ℕ, p.Prime → p ∣ D → K < p) :
    smoothPart K (D * m) = smoothPart K m := by
  unfold smoothPart
  have hfilt : (D * m).primeFactors.filter (· ≤ K) = m.primeFactors.filter (· ≤ K) := by
    ext p
    simp only [mem_filter, Nat.mem_primeFactors, ne_eq, mul_eq_zero, not_or]
    constructor
    · rintro ⟨⟨hp, hpdm, hD0, hm0⟩, hpK⟩
      refine ⟨⟨hp, ?_, hm0⟩, hpK⟩
      rcases hp.dvd_mul.mp hpdm with hD' | hm'
      · exfalso; have := hDgt p hp hD'; omega
      · exact hm'
    · rintro ⟨⟨hp, hpm, hm0⟩, hpK⟩
      exact ⟨⟨hp, dvd_mul_of_dvd_right hpm D, hD.ne', hm0⟩, hpK⟩
  rw [hfilt]
  refine prod_congr rfl fun p hp => ?_
  have hp' := mem_filter.mp hp
  have hpP := Nat.prime_of_mem_primeFactors hp'.1
  rw [Nat.factorization_mul hD.ne' hm.ne', Finsupp.add_apply]
  have hD0 : D.factorization p = 0 := by
    by_contra hne
    have hdvd : p ∣ D := (hpP.dvd_iff_one_le_factorization hD.ne').mpr (Nat.pos_of_ne_zero hne)
    have := hDgt p hpP hdvd; omega
  rw [hD0, zero_add]

lemma log_smoothPart_eq_sum_dvd {K n N : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    log (smoothPart K n : ℝ) =
      ∑ p ∈ (Icc 1 K).filter Nat.Prime,
        ∑ a ∈ Icc 1 (Nat.log 2 N + 1), if p ^ a ∣ n then log (p : ℝ) else 0 := by
  have h1 : log (smoothPart K n : ℝ) =
      ∑ p ∈ n.primeFactors.filter (· ≤ K), (n.factorization p : ℝ) * log (p : ℝ) := by
    unfold smoothPart
    rw [Nat.cast_prod, log_prod]
    · refine sum_congr rfl fun p _ => by rw [Nat.cast_pow, log_pow]
    · intro p hp
      have hpP := Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1
      positivity [hpP.pos]
  rw [h1]
  have hinner : ∀ p ∈ (Icc 1 K).filter Nat.Prime,
      (∑ a ∈ Icc 1 (Nat.log 2 N + 1), if p ^ a ∣ n then log (p : ℝ) else 0) =
      (n.factorization p : ℝ) * log (p : ℝ) := by
    intro p hp
    have hpP : p.Prime := (mem_filter.mp hp).2
    have hval_le : n.factorization p ≤ Nat.log 2 N := by
      have hpow_le : 2 ^ n.factorization p ≤ N := by
        calc 2 ^ n.factorization p ≤ p ^ n.factorization p := Nat.pow_le_pow_left hpP.two_le _
          _ ≤ n := Nat.le_of_dvd hn (Nat.ordProj_dvd n p)
          _ ≤ N := hnN
      exact Nat.le_log_of_pow_le (by norm_num) hpow_le
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    congr 1
    have hfilt : (Icc 1 (Nat.log 2 N + 1)).filter (fun a => p ^ a ∣ n) = Icc 1 (n.factorization p) := by
      ext a
      simp only [mem_filter, mem_Icc, hpP.pow_dvd_iff_le_factorization hn.ne']
      omega
    rw [hfilt, Nat.card_Icc]
    have : n.factorization p + 1 - 1 = n.factorization p := by omega
    rw [this]
  rw [sum_congr rfl hinner]
  refine sum_subset ?_ ?_
  · intro p hp
    have hp' := mem_filter.mp hp
    have hpP := Nat.prime_of_mem_primeFactors hp'.1
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hpP.pos, hp'.2⟩, hpP⟩
  · intro p hp hpnot
    have hp' := mem_filter.mp hp
    have hnotmem : p ∉ n.primeFactors := fun h => hpnot (mem_filter.mpr ⟨h, (mem_Icc.mp hp'.1).2⟩)
    have hzero : n.factorization p = 0 := by
      by_contra hne
      exact hnotmem (Nat.mem_primeFactors.mpr ⟨hp'.2, (hp'.2.dvd_iff_one_le_factorization hn.ne').mpr (Nat.pos_of_ne_zero hne), hn.ne'⟩)
    simp [hzero]

/- ### Part 7B: Factorial Tail & Product-Exponential Bounds -/

/-- Geometric tail bound on `∑_{k=K}^M x^k / k!` when `2 * ⌈x⌉₊ ≤ K`. -/
lemma factorial_tail_sum_le {x : ℝ} (hx : 0 ≤ x) {K M : ℕ} (hKm : 2 * ⌈x⌉₊ ≤ K) :
    ∑ k ∈ Icc K M, x ^ k / (Nat.factorial k : ℝ) ≤
      2 * (1 / 2 : ℝ) ^ (K - 2 * ⌈x⌉₊) * exp x := by
  set m := 2 * ⌈x⌉₊
  have h2x_le_m : 2 * x ≤ (m : ℝ) := by
    have h := Nat.le_ceil x
    push_cast [m]; linarith
  have hstep : ∀ j : ℕ, x ^ (m + j) / (Nat.factorial (m + j) : ℝ) ≤
      (1 / 2 : ℝ) ^ j * (x ^ m / (Nat.factorial m : ℝ)) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hm1 : 0 < (m + j + 1 : ℕ) := Nat.succ_pos _
      have hfac : (Nat.factorial (m + (j + 1)) : ℝ) = ((m + j + 1 : ℕ) : ℝ) * (Nat.factorial (m + j) : ℝ) := by
        have : m + (j + 1) = (m + j) + 1 := by omega
        rw [this, Nat.factorial_succ, Nat.cast_mul]
      have hrew : x ^ (m + (j + 1)) / (Nat.factorial (m + (j + 1)) : ℝ) =
          (x / ((m + j + 1 : ℕ) : ℝ)) * (x ^ (m + j) / (Nat.factorial (m + j) : ℝ)) := by
        rw [hfac, show m + (j + 1) = (m + j) + 1 by omega, pow_succ]; ring
      have hratio : x / ((m + j + 1 : ℕ) : ℝ) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        push_cast; linarith
      rw [hrew, pow_succ']
      calc (x / ((m + j + 1 : ℕ) : ℝ)) * (x ^ (m + j) / (Nat.factorial (m + j) : ℝ))
          ≤ (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ j * (x ^ m / (Nat.factorial m : ℝ))) :=
            mul_le_mul hratio ih (by positivity) (by norm_num)
        _ = (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ j * (x ^ m / (Nat.factorial m : ℝ)) := by ring
  have hbase : x ^ m / (Nat.factorial m : ℝ) ≤ exp x :=
    pow_div_factorial_le_exp x hx m
  have hterm : ∀ k ∈ Icc K M, x ^ k / (Nat.factorial k : ℝ) ≤
      (1 / 2 : ℝ) ^ (k - m) * exp x := by
    intro k hk
    have hmk : m ≤ k := le_trans hKm (mem_Icc.mp hk).1
    have h1 := hstep (k - m)
    have hadd : m + (k - m) = k := by omega
    rw [hadd] at h1
    exact le_trans h1 (mul_le_mul_of_nonneg_left hbase (by positivity))
  -- Bound `∑_{k ∈ Icc K M} (1/2)^(k - m) ≤ 2 * (1/2)^(K - m)`:
  have hgeom : ∀ r : ℕ, ∑ i ∈ range r, (1 / 2 : ℝ) ^ i ≤ 2 := by
    intro r
    have h1 := mul_geom_sum (1 / 2 : ℝ) r
    have hnn : 0 ≤ (1 / 2 : ℝ) ^ r := by positivity
    linarith
  calc ∑ k ∈ Icc K M, x ^ k / (Nat.factorial k : ℝ)
      ≤ ∑ k ∈ Icc K M, (1 / 2 : ℝ) ^ (k - m) * exp x := sum_le_sum hterm
    _ = (∑ k ∈ Icc K M, (1 / 2 : ℝ) ^ (k - m)) * exp x := (sum_mul _ _ _).symm
    _ ≤ (2 * (1 / 2 : ℝ) ^ (K - m)) * exp x := by
          refine mul_le_mul_of_nonneg_right ?_ (exp_pos x).le
          by_cases hKM : K ≤ M
          · have hrew : ∑ k ∈ Icc K M, (1 / 2 : ℝ) ^ (k - m) =
                (1 / 2 : ℝ) ^ (K - m) * ∑ i ∈ range (M - K + 1), (1 / 2 : ℝ) ^ i := by
              rw [mul_sum]
              refine sum_nbij (fun k => k - K) ?_ ?_ ?_ ?_
              · intro k hk; simp only [mem_coe, mem_Icc, mem_range] at hk ⊢; omega
              · intro k₁ hk₁ k₂ hk₂ heq
                dsimp at heq
                simp only [mem_coe, mem_Icc] at hk₁ hk₂; omega
              · intro i hi
                have hi' := mem_range.mp (mem_coe.mp hi)
                refine ⟨K + i, ?_, by dsimp; omega⟩
                simp only [mem_coe, mem_Icc]; omega
              · intro k hk
                have hk' := mem_Icc.mp hk
                rw [← pow_add]
                congr 1; omega
            rw [hrew]
            have := hgeom (M - K + 1)
            have hnn : 0 ≤ (1 / 2 : ℝ) ^ (K - m) := by positivity
            nlinarith
          · push Not at hKM
            have : Icc K M = ∅ := by ext k; simp only [mem_Icc, notMem_empty, iff_false]; omega
            rw [this, sum_empty]; positivity
    _ = 2 * (1 / 2 : ℝ) ^ (K - m) * exp x := by ring

/-- Two-sided exponential bounds on `∏_{p ∈ S} (1 - 1/p)` when every `p ∈ S` satisfies `p ≥ Pmin ≥ 4`. -/
lemma prod_one_sub_inv_bounds (S : Finset ℕ) {Pmin : ℝ} (hPmin : 4 ≤ Pmin)
    (hge : ∀ p ∈ S, Pmin ≤ (p : ℝ)) :
    exp (-(∑ p ∈ S, (1 : ℝ) / (p : ℝ)) - (2 / Pmin) * (∑ p ∈ S, (1 : ℝ) / (p : ℝ))) ≤
      ∏ p ∈ S, (1 - (1 : ℝ) / (p : ℝ)) ∧
    ∏ p ∈ S, (1 - (1 : ℝ) / (p : ℝ)) ≤ exp (-(∑ p ∈ S, (1 : ℝ) / (p : ℝ))) := by
  have hPpos : 0 < Pmin := by linarith
  constructor
  · have hrew : -(∑ p ∈ S, (1 : ℝ) / (p : ℝ)) - (2 / Pmin) * (∑ p ∈ S, (1 : ℝ) / (p : ℝ)) =
        ∑ p ∈ S, (-(1 / (p : ℝ)) - (2 / Pmin) * (1 / (p : ℝ))) := by
      rw [mul_sum, ← sum_neg_distrib, ← sum_sub_distrib]
    rw [hrew, exp_sum]
    refine prod_le_prod (fun p _ => (exp_pos _).le) fun p hp => ?_
    have hp_ge : Pmin ≤ (p : ℝ) := hge p hp
    have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
    set t : ℝ := 1 / (p : ℝ)
    have ht_pos : 0 < t := by positivity
    have ht_le : t ≤ 1 / Pmin := one_div_le_one_div_of_le hPpos hp_ge
    have ht_half : t ≤ 1 / 2 := le_trans ht_le (by rw [one_div_le_one_div hPpos (by norm_num)]; linarith)
    have hmul_ge1 : 1 ≤ (1 - t) * exp (t + 2 * t ^ 2) := by
      have hexp : 1 + (t + 2 * t ^ 2) ≤ exp (t + 2 * t ^ 2) := by linarith [add_one_le_exp (t + 2 * t ^ 2)]
      have h1mt : 0 ≤ 1 - t := by linarith
      have hprod := mul_le_mul_of_nonneg_left hexp h1mt
      have hpoly : 1 ≤ (1 - t) * (1 + (t + 2 * t ^ 2)) := by
        have hid : (1 - t) * (1 + (t + 2 * t ^ 2)) = 1 + t ^ 2 * (1 - 2 * t) := by ring
        rw [hid]
        have : 0 ≤ t ^ 2 * (1 - 2 * t) := mul_nonneg (sq_nonneg t) (by linarith)
        linarith
      linarith
    have hle_exp : exp (-(t + 2 * t ^ 2)) ≤ 1 - t := by
      rw [exp_neg]
      have hexp_pos : 0 < exp (t + 2 * t ^ 2) := exp_pos _
      rw [inv_le_comm₀ hexp_pos (by linarith)]
      rw [inv_le_iff_one_le_mul₀ (by linarith : 0 < 1 - t), mul_comm]
      exact hmul_ge1
    have harg : -t - (2 / Pmin) * t ≤ -(t + 2 * t ^ 2) := by
      have : 2 * t ^ 2 ≤ (2 / Pmin) * t := by
        have := mul_le_mul_of_nonneg_right ht_le ht_pos.le
        linarith [show (1 / Pmin) * t = t / Pmin by ring, show (2 / Pmin) * t = 2 * (t / Pmin) by ring,
                  show t * t = t ^ 2 by ring]
      linarith
    exact le_trans (exp_le_exp.mpr harg) hle_exp
  · rw [← sum_neg_distrib, exp_sum]
    refine prod_le_prod (fun p hp => ?_) fun p _ => ?_
    · have hp_ge : Pmin ≤ (p : ℝ) := hge p hp
      have : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      linarith
    · linarith [add_one_le_exp (-(1 / (p : ℝ)))]

/- ### Part 7C: Prime-Block Geometry & Mertens Estimates -/

/-- Mertens' second theorem for exponential endpoints `a = ⌊exp a_exp⌋₊`, `b = ⌊exp b_exp⌋₊` (`4 ≤ a_exp ≤ b_exp`). -/
lemma mertens_Ioc_exp {a_exp b_exp : ℝ} (ha : 4 ≤ a_exp) (hab : a_exp ≤ b_exp) :
    |∑ p ∈ (Ioc ⌊exp a_exp⌋₊ ⌊exp b_exp⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ) -
      log (b_exp / a_exp)| ≤ 330 / a_exp := by
  set a := ⌊exp a_exp⌋₊
  set b := ⌊exp b_exp⌋₊
  have ha_ge2 : 2 ≤ a := by
    have h1 : (2 : ℝ) ≤ exp a_exp := by linarith [add_one_le_exp a_exp]
    exact Nat.le_floor h1
  have hab_nat : a ≤ b := Nat.floor_mono (exp_le_exp.mpr hab)
  have hlog_bd : ∀ y : ℝ, 4 ≤ y → y - 1 ≤ log ((⌊exp y⌋₊ : ℕ) : ℝ) ∧
      log ((⌊exp y⌋₊ : ℕ) : ℝ) ≤ y := by
    intro y hy
    have hexp_pos : 0 < exp y := exp_pos y
    have hfl_le : ((⌊exp y⌋₊ : ℕ) : ℝ) ≤ exp y := Nat.floor_le hexp_pos.le
    have hfl_gt : exp (y - 1) ≤ ((⌊exp y⌋₊ : ℕ) : ℝ) := by
      have h1 : exp y - 1 < ((⌊exp y⌋₊ : ℕ) : ℝ) := by
        have := Nat.lt_floor_add_one (exp y); linarith
      have h2 : exp (y - 1) + 1 ≤ exp y := by
        have hrew : exp y = exp 1 * exp (y - 1) := by rw [← exp_add]; congr 1; ring
        have he1 : (2 : ℝ) ≤ exp 1 := by linarith [add_one_le_exp (1 : ℝ)]
        have hey : (1 : ℝ) ≤ exp (y - 1) := one_le_exp (by linarith)
        nlinarith
      linarith
    constructor
    · have := log_le_log (exp_pos _) hfl_gt
      rwa [log_exp] at this
    · have hfl_pos : (0 : ℝ) < ((⌊exp y⌋₊ : ℕ) : ℝ) := lt_of_lt_of_le (exp_pos _) hfl_gt
      have := log_le_log hfl_pos hfl_le
      rwa [log_exp] at this
  have hloga := hlog_bd a_exp ha
  have hlogb := hlog_bd b_exp (le_trans ha hab)
  have hlog_err : ∀ y : ℝ, 4 ≤ y → |log (log ((⌊exp y⌋₊ : ℕ) : ℝ) / y)| ≤ 2 / y := by
    intro y hy
    have hbd := hlog_bd y hy
    have hypos : 0 < y := by linarith
    have hlog_pos : 0 < log ((⌊exp y⌋₊ : ℕ) : ℝ) := by linarith
    have hrat_le : log ((⌊exp y⌋₊ : ℕ) : ℝ) / y ≤ 1 := (div_le_one hypos).mpr hbd.2
    have hrat_ge : 1 - 1 / y ≤ log ((⌊exp y⌋₊ : ℕ) : ℝ) / y := by
      rw [sub_div' hypos.ne', div_le_div_iff_of_pos_right hypos]; linarith
    have hrat_pos : 0 < log ((⌊exp y⌋₊ : ℕ) : ℝ) / y := div_pos hlog_pos hypos
    rw [abs_le]
    constructor
    · have hinv := log_le_sub_one_of_pos (inv_pos.mpr hrat_pos)
      rw [log_inv] at hinv
      have hinv_le : (log ((⌊exp y⌋₊ : ℕ) : ℝ) / y)⁻¹ - 1 ≤ 2 / y := by
        have h1 : 1 / (1 - 1 / y) ≤ 1 + 2 / y := by
          have hpos : 0 < 1 - 1 / y := by
            have : 1 / y ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hy; linarith
          rw [div_le_iff₀ hpos]
          have hid : (1 + 2 / y) * (1 - 1 / y) = 1 + (1 / y) * (1 - 2 / y) := by ring
          rw [hid]
          have : 2 / y ≤ 1 := by rw [div_le_one hypos]; linarith
          have : 0 ≤ (1 / y) * (1 - 2 / y) := mul_nonneg (by positivity) (by linarith)
          linarith
        have h2 : (log ((⌊exp y⌋₊ : ℕ) : ℝ) / y)⁻¹ ≤ 1 / (1 - 1 / y) := by
          rw [one_div]; exact inv_anti₀ (by
            have : 1 / y ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hy; linarith) hrat_ge
        linarith
      linarith
    · exact le_trans (log_nonpos hrat_pos.le hrat_le) (by positivity)
  have hm := mertens_second_Ioc_nat ha_ge2 hab_nat
  have hlog_diff : log (log (b : ℝ) / log (a : ℝ)) - log (b_exp / a_exp) =
      log (log (b : ℝ) / b_exp) - log (log (a : ℝ) / a_exp) := by
    have ha_pos : 0 < a_exp := by linarith
    have hb_pos : 0 < b_exp := by linarith
    have hla_pos : 0 < log (a : ℝ) := by linarith
    have hlb_pos : 0 < log (b : ℝ) := by linarith
    rw [log_div hlb_pos.ne' hla_pos.ne', log_div hb_pos.ne' ha_pos.ne',
        log_div hlb_pos.ne' hb_pos.ne', log_div hla_pos.ne' ha_pos.ne']
    ring
  have h160 : 160 / log (a : ℝ) ≤ 320 / a_exp := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    linarith
  have h2b : 2 / b_exp ≤ 2 / a_exp := div_le_div_of_nonneg_left (by norm_num) (by linarith) hab
  have he1 : |log (log (a : ℝ) / a_exp)| ≤ 2 / a_exp := hlog_err a_exp ha
  have he2 : |log (log (b : ℝ) / b_exp)| ≤ 2 / b_exp := hlog_err b_exp (le_trans ha hab)
  have h324 : 320 / a_exp + 2 / a_exp + 2 / a_exp ≤ 330 / a_exp := by
    rw [← add_div, ← add_div]
    exact div_le_div_of_nonneg_right (by norm_num) (by linarith)
  rw [abs_le] at hm he1 he2 ⊢
  constructor <;> linarith

noncomputable def loBlock (γ Q_step : ℝ) (j : ℕ) : ℕ := ⌊exp (γ * Q_step ^ j)⌋₊
noncomputable def hiBlock (L Q_step : ℝ) (j : ℕ) : ℕ := ⌊exp (L * Q_step ^ j)⌋₊
noncomputable def loBin (L Q_step : ℝ) (G j : ℕ) (r : Fin G) : ℕ := ⌊exp (xLo L G r * Q_step ^ j)⌋₊
noncomputable def hiBin (L Q_step : ℝ) (G j : ℕ) (r : Fin G) : ℕ := ⌊exp (xHi L G r * Q_step ^ j)⌋₊

noncomputable def Sblock (L γ Q_step : ℝ) (j : ℕ) : Finset ℕ :=
  (Ioc (loBlock γ Q_step j) (hiBlock L Q_step j)).filter Nat.Prime

noncomputable def Pbin (L Q_step : ℝ) (G j : ℕ) (r : Fin G) : Finset ℕ :=
  (Ioc (loBin L Q_step G j r) (hiBin L Q_step G j r)).filter Nat.Prime

lemma Pbin_subset_Sblock {L γ Q_step : ℝ} {G j : ℕ}
    (hL : 1 < L) (hG : 0 < G) (hγ : γ ≤ 1) (hQ : 0 < Q_step) (r : Fin G) :
    Pbin L Q_step G j r ⊆ Sblock L γ Q_step j := by
  intro p hp
  simp only [Pbin, Sblock, mem_filter, mem_Ioc] at hp ⊢
  refine ⟨⟨?_, ?_⟩, hp.2⟩
  · have hlo : loBlock γ Q_step j ≤ loBin L Q_step G j r := by
      apply Nat.floor_mono; apply exp_le_exp.mpr
      have := xLo_ge_one hL hG r
      exact mul_le_mul_of_nonneg_right (le_trans hγ this) (pow_nonneg hQ.le j)
    omega
  · have hhi : hiBin L Q_step G j r ≤ hiBlock L Q_step j := by
      apply Nat.floor_mono; apply exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right (xHi_gt_one_and_le hL hG r).2 (pow_nonneg hQ.le j)
    omega

lemma Pbin_disjoint {L Q_step : ℝ} {G j : ℕ} (hL : 1 < L) (hG : 0 < G) (hQ : 0 < Q_step)
    {r₁ r₂ : Fin G} (hne : r₁ ≠ r₂) :
    Disjoint (Pbin L Q_step G j r₁) (Pbin L Q_step G j r₂) := by
  have hord : ∀ a b : Fin G, a.val < b.val → hiBin L Q_step G j a ≤ loBin L Q_step G j b := by
    intro a b hlt
    apply Nat.floor_mono; apply exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hQ.le j)
    unfold xHi xLo
    apply exp_le_exp.mpr
    have hΔ := gridDelta_pos hL hG
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hlt) hΔ.le
  rw [disjoint_left]
  intro p hp1 hp2
  simp only [Pbin, mem_filter, mem_Ioc] at hp1 hp2
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
  · have := hord r₁ r₂ hlt; omega
  · have := hord r₂ r₁ hgt; omega

lemma Sblock_disjoint {L γ Q_step : ℝ} {j₁ j₂ : ℕ}
    (hγ : 0 < γ) (hQ : Q_step = 2 * L / γ) (hL : 1 < L) (hγ1 : γ ≤ 1) (hne : j₁ ≠ j₂) :
    Disjoint (Sblock L γ Q_step j₁) (Sblock L γ Q_step j₂) := by
  have hQ1 : 1 ≤ Q_step := by
    rw [hQ, one_le_div hγ]; linarith
  have hord : ∀ a b : ℕ, a < b → hiBlock L Q_step a ≤ loBlock γ Q_step b := by
    intro a b hlt
    apply Nat.floor_mono; apply exp_le_exp.mpr
    have hpow : Q_step ^ (a + 1) ≤ Q_step ^ b := pow_le_pow_right₀ hQ1 hlt
    have heq : L * Q_step ^ a = (γ / 2) * Q_step ^ (a + 1) := by
      rw [pow_succ, hQ]; field_simp [hγ.ne']
    have hnn : 0 ≤ Q_step ^ b := by positivity
    rw [heq]
    nlinarith [mul_le_mul_of_nonneg_left hpow (show 0 ≤ γ / 2 by linarith)]
  rw [disjoint_left]
  intro p hp1 hp2
  simp only [Sblock, mem_filter, mem_Ioc] at hp1 hp2
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have := hord j₁ j₂ hlt; omega
  · have := hord j₂ j₁ hgt; omega

/- ### Part 7D: Subcells, Uniqueness, and Deterministic `tauPerp` Lower Bound -/

/-- Prime tuples selecting one prime `f r ∈ Pbin L Q_step G j r` for each `r ∈ activeSet b`. -/
noncomputable def tupleSet (L Q_step : ℝ) (G j : ℕ) (b : Fin G → Bool) : Finset (activeSet b → ℕ) :=
  Fintype.piFinset fun r : activeSet b => Pbin L Q_step G j r.1

/-- Product of all primes in a tuple `f`. -/
def prodD {G : ℕ} {b : Fin G → Bool} (f : activeSet b → ℕ) : ℕ :=
  ∏ r : activeSet b, f r

/-- Product of primes in `f` indexed by a subset `H : Finset (Fin G)`. -/
def prodSub {G : ℕ} {b : Fin G → Bool} (f : activeSet b → ℕ) (H : Finset (Fin G)) : ℕ :=
  ∏ r : activeSet b, if r.1 ∈ H then f r else 1

/-- Integer `n` lies in subcell `(j, b, f)` iff `prodD f ∣ n` and no prime of `Sblock j` divides `n / prodD f`. -/
def inSubCell (L γ Q_step : ℝ) (G j : ℕ) (b : Fin G → Bool) (f : activeSet b → ℕ) (n : ℕ) : Prop :=
  prodD f ∣ n ∧ ∀ p ∈ Sblock L γ Q_step j, ¬p ∣ (n / prodD f)

/-- Block-`j` score `Y_j(n)`. -/
noncomputable def Y_val (L γ Q_step η : ℝ) (G j n : ℕ) : ℝ :=
  ∑ b : Fin G → Bool, ∑ f ∈ tupleSet L Q_step G j b,
    if inSubCell L γ Q_step G j b f n then (cellScore L G η b : ℝ) else 0

/-- Trimmed block-`j` score `Z_j(n)` requiring the smooth part `A_j(n) ≤ exp(β * Q_step^j)`. -/
noncomputable def Z_val (L γ β Q_step η : ℝ) (G j n : ℕ) : ℝ :=
  if (smoothPart (loBlock γ Q_step j) n : ℝ) ≤ exp (β * Q_step ^ j) then
    Y_val L γ Q_step η G j n
  else 0

/-- Basic properties of a prime tuple `f ∈ tupleSet L Q_step G j b`. -/
lemma tupleSet_props {L γ Q_step : ℝ} {G j : ℕ} {b : Fin G → Bool}
    (hL : 1 < L) (hG : 0 < G) (hγ1 : γ ≤ 1) (hQ : 0 < Q_step)
    {f : activeSet b → ℕ} (hf : f ∈ tupleSet L Q_step G j b) :
    (∀ r : activeSet b, (f r).Prime) ∧
    (∀ r : activeSet b, f r ∈ Sblock L γ Q_step j) ∧
    Function.Injective f ∧
    0 < prodD f := by
  have hmem : ∀ r : activeSet b, f r ∈ Pbin L Q_step G j r.1 := fun r =>
    Fintype.mem_piFinset.mp hf r
  have hprime : ∀ r : activeSet b, (f r).Prime := fun r => (mem_filter.mp (hmem r)).2
  have hS : ∀ r : activeSet b, f r ∈ Sblock L γ Q_step j := fun r =>
    Pbin_subset_Sblock hL hG hγ1 hQ r.1 (hmem r)
  have hinj : Function.Injective f := by
    intro r₁ r₂ heq
    by_contra hne
    have hne' : r₁.1 ≠ r₂.1 := fun h => hne (Subtype.ext h)
    have hdisj := Pbin_disjoint hL hG hQ (j := j) hne'
    exact disjoint_left.mp hdisj (hmem r₁) (heq ▸ hmem r₂)
  have hpos : 0 < prodD f := prod_pos fun r _ => (hprime r).pos
  exact ⟨hprime, hS, hinj, hpos⟩

/-- Every prime divisor of `prodSub f H` is `f r` for a unique `r : activeSet b` with `r.1 ∈ H`. -/
lemma prime_dvd_prodSub_iff {L γ Q_step : ℝ} {G j : ℕ} {b : Fin G → Bool}
    (hL : 1 < L) (hG : 0 < G) (hγ1 : γ ≤ 1) (hQ : 0 < Q_step)
    {f : activeSet b → ℕ} (hf : f ∈ tupleSet L Q_step G j b) (H : Finset (Fin G))
    {p : ℕ} (hp : p.Prime) :
    p ∣ prodSub f H ↔ ∃ r : activeSet b, r.1 ∈ H ∧ f r = p := by
  obtain ⟨hprime, _, _, _⟩ := tupleSet_props hL hG hγ1 hQ hf
  constructor
  · intro hdvd
    unfold prodSub at hdvd
    obtain ⟨r, _, hpr⟩ := hp.prime.exists_mem_finset_dvd hdvd
    by_cases hrH : r.1 ∈ H
    · rw [if_pos hrH] at hpr
      exact ⟨r, hrH, ((Nat.prime_dvd_prime_iff_eq hp (hprime r)).mp hpr).symm⟩
    · rw [if_neg hrH] at hpr
      exact absurd hpr hp.not_dvd_one
  · rintro ⟨r, hrH, rfl⟩
    unfold prodSub
    have h1 := dvd_prod_of_mem (fun s : activeSet b => if s.1 ∈ H then f s else 1) (mem_univ r)
    rwa [if_pos hrH] at h1

lemma prodSub_pos {L γ Q_step : ℝ} {G j : ℕ} {b : Fin G → Bool}
    (hL : 1 < L) (hG : 0 < G) (hγ1 : γ ≤ 1) (hQ : 0 < Q_step)
    {f : activeSet b → ℕ} (hf : f ∈ tupleSet L Q_step G j b) (H : Finset (Fin G)) :
    0 < prodSub f H := by
  obtain ⟨hprime, _, _, _⟩ := tupleSet_props hL hG hγ1 hQ hf
  exact prod_pos fun r _ => by split_ifs; exact (hprime r).pos; exact one_pos

lemma prodSub_dvd_prodD {G : ℕ} {b : Fin G → Bool} (f : activeSet b → ℕ) (H : Finset (Fin G)) :
    prodSub f H ∣ prodD f := by
  unfold prodSub prodD
  refine prod_dvd_prod_of_dvd _ _ fun r _ => ?_
  split_ifs
  · exact dvd_rfl
  · exact one_dvd _

lemma prodSub_coprime {L γ Q_step : ℝ} {G j : ℕ} {b : Fin G → Bool}
    (hL : 1 < L) (hG : 0 < G) (hγ1 : γ ≤ 1) (hQ : 0 < Q_step)
    {f : activeSet b → ℕ} (hf : f ∈ tupleSet L Q_step G j b)
    {I J : Finset (Fin G)} (hdisj : Disjoint I J) :
    Nat.Coprime (prodSub f I) (prodSub f J) := by
  obtain ⟨_, _, hinj, _⟩ := tupleSet_props hL hG hγ1 hQ hf
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hne
  obtain ⟨r₁, hr₁I, hr₁eq⟩ := (prime_dvd_prodSub_iff hL hG hγ1 hQ hf I hp).mp
    (dvd_trans hpg (Nat.gcd_dvd_left _ _))
  obtain ⟨r₂, hr₂J, hr₂eq⟩ := (prime_dvd_prodSub_iff hL hG hγ1 hQ hf J hp).mp
    (dvd_trans hpg (Nat.gcd_dvd_right _ _))
  have hr : r₁ = r₂ := hinj (hr₁eq.trans hr₂eq.symm)
  subst hr
  exact disjoint_left.mp hdisj hr₁I hr₂J

lemma prodSub_inj {L γ Q_step : ℝ} {G j : ℕ} {b : Fin G → Bool}
    (hL : 1 < L) (hG : 0 < G) (hγ1 : γ ≤ 1) (hQ : 0 < Q_step)
    {f : activeSet b → ℕ} (hf : f ∈ tupleSet L Q_step G j b)
    {H₁ H₂ : Finset (Fin G)} (hH₁ : H₁ ⊆ activeSet b) (hH₂ : H₂ ⊆ activeSet b)
    (heq : prodSub f H₁ = prodSub f H₂) : H₁ = H₂ := by
  obtain ⟨hprime, _, hinj, _⟩ := tupleSet_props hL hG hγ1 hQ hf
  ext r
  constructor
  · intro hr
    have hrb : r ∈ activeSet b := hH₁ hr
    have hdvd : f ⟨r, hrb⟩ ∣ prodSub f H₂ := by
      rw [← heq]
      exact (prime_dvd_prodSub_iff hL hG hγ1 hQ hf H₁ (hprime ⟨r, hrb⟩)).mpr ⟨⟨r, hrb⟩, hr, rfl⟩
    obtain ⟨s, hsH₂, hseq⟩ := (prime_dvd_prodSub_iff hL hG hγ1 hQ hf H₂ (hprime ⟨r, hrb⟩)).mp hdvd
    have hs : s = ⟨r, hrb⟩ := hinj hseq
    have hsval : s.1 = r := congr_arg Subtype.val hs
    rwa [← hsval]
  · intro hr
    have hrb : r ∈ activeSet b := hH₂ hr
    have hdvd : f ⟨r, hrb⟩ ∣ prodSub f H₁ := by
      rw [heq]
      exact (prime_dvd_prodSub_iff hL hG hγ1 hQ hf H₂ (hprime ⟨r, hrb⟩)).mpr ⟨⟨r, hrb⟩, hr, rfl⟩
    obtain ⟨s, hsH₁, hseq⟩ := (prime_dvd_prodSub_iff hL hG hγ1 hQ hf H₁ (hprime ⟨r, hrb⟩)).mp hdvd
    have hs : s = ⟨r, hrb⟩ := hinj hseq
    have hsval : s.1 = r := congr_arg Subtype.val hs
    rwa [← hsval]

/-- Every divisor `u ∣ prodD f` equals `prodSub f H` for some `H ⊆ activeSet b`. -/
lemma exists_prodSub_of_dvd_prodD {L γ Q_step : ℝ} {G j : ℕ} {b : Fin G → Bool}
    (hL : 1 < L) (hG : 0 < G) (hγ1 : γ ≤ 1) (hQ : 0 < Q_step)
    {f : activeSet b → ℕ} (hf : f ∈ tupleSet L Q_step G j b)
    {u : ℕ} (hu : u ∣ prodD f) :
    ∃ H ⊆ activeSet b, u = prodSub f H := by
  obtain ⟨hprime, _, hinj, hDpos⟩ := tupleSet_props hL hG hγ1 hQ hf
  have hupos : 0 < u := Nat.pos_of_dvd_of_pos hu hDpos
  -- Show `prodD f` is squarefree (every prime divides it at most once):
  have hDfac : ∀ p : ℕ, (prodD f).factorization p ≤ 1 := by
    intro p
    unfold prodD
    rw [Nat.factorization_prod (fun r _ => (hprime r).ne_zero), Finsupp.finsetSum_apply]
    by_cases hex : ∃ r : activeSet b, f r = p
    · obtain ⟨r₀, hr₀⟩ := hex
      rw [sum_eq_single r₀]
      · have hp0 : (f r₀).Prime := hprime r₀
        rw [← hr₀, hp0.factorization_self]
      · intro r _ hne
        have hpne : f r ≠ p := fun h => hne (hinj (h.trans hr₀.symm))
        rw [(hprime r).factorization, Finsupp.single_apply, if_neg hpne]
      · simp
    · push Not at hex
      have h0 : ∑ r : activeSet b, (f r).factorization p = 0 :=
        sum_eq_zero fun r _ => by rw [(hprime r).factorization, Finsupp.single_apply, if_neg (hex r)]
      omega
  let H : Finset (Fin G) := (activeSet b).filter fun r => ∃ h : r ∈ activeSet b, f ⟨r, h⟩ ∣ u
  have hHsub : H ⊆ activeSet b := filter_subset _ _
  refine ⟨H, hHsub, ?_⟩
  have hPpos := prodSub_pos hL hG hγ1 hQ hf H
  have hfac_eq : u.factorization = (prodSub f H).factorization := by
    ext p
    have hu_le : u.factorization p ≤ 1 :=
      le_trans ((Nat.factorization_le_iff_dvd hupos.ne' hDpos.ne').mpr hu p) (hDfac p)
    have hP_le : (prodSub f H).factorization p ≤ 1 :=
      le_trans ((Nat.factorization_le_iff_dvd hPpos.ne' hDpos.ne').mpr (prodSub_dvd_prodD f H) p) (hDfac p)
    by_cases hp : p.Prime
    · have hiff : p ∣ u ↔ p ∣ prodSub f H := by
        constructor
        · intro hpu
          have hpD : p ∣ prodD f := dvd_trans hpu hu
          have hpD' : p ∣ prodSub f (activeSet b) := by
            have heq : prodSub f (activeSet b) = prodD f := by
              unfold prodSub prodD; exact prod_congr rfl fun r _ => if_pos r.2
            rwa [heq]
          obtain ⟨r, _, rfl⟩ := (prime_dvd_prodSub_iff hL hG hγ1 hQ hf (activeSet b) hp).mp hpD'
          exact (prime_dvd_prodSub_iff hL hG hγ1 hQ hf H hp).mpr
            ⟨r, mem_filter.mpr ⟨r.2, ⟨r.2, hpu⟩⟩, rfl⟩
        · intro hpP
          obtain ⟨r, hrH, rfl⟩ := (prime_dvd_prodSub_iff hL hG hγ1 hQ hf H hp).mp hpP
          obtain ⟨_, hdu⟩ := (mem_filter.mp hrH).2
          exact hdu
      have h1 : 1 ≤ u.factorization p ↔ 1 ≤ (prodSub f H).factorization p := by
        rw [← hp.dvd_iff_one_le_factorization hupos.ne', ← hp.dvd_iff_one_le_factorization hPpos.ne']
        exact hiff
      omega
    · rw [Nat.factorization_eq_zero_of_not_prime u hp, Nat.factorization_eq_zero_of_not_prime _ hp]
  exact Nat.eq_of_factorization_eq hupos.ne' hPpos.ne' (fun p => congr_arg (fun g => g p) hfac_eq)

/-- Uniqueness of `(b, f)` for `inSubCell L γ Q_step G j b f n` when `0 < n`. -/
lemma inSubCell_unique {L γ Q_step : ℝ} {G j : ℕ}
    (hL : 1 < L) (hG : 0 < G) (hγ1 : γ ≤ 1) (hQ : 0 < Q_step) {n : ℕ} (hn : 0 < n)
    {b₁ b₂ : Fin G → Bool} {f₁ : activeSet b₁ → ℕ} {f₂ : activeSet b₂ → ℕ}
    (hf₁ : f₁ ∈ tupleSet L Q_step G j b₁) (hf₂ : f₂ ∈ tupleSet L Q_step G j b₂)
    (h1 : inSubCell L γ Q_step G j b₁ f₁ n) (h2 : inSubCell L γ Q_step G j b₂ f₂ n) :
    b₁ = b₂ ∧ HEq f₁ f₂ := by
  have hmem₁ := fun r : activeSet b₁ => Fintype.mem_piFinset.mp hf₁ r
  have hmem₂ := fun r : activeSet b₂ => Fintype.mem_piFinset.mp hf₂ r
  obtain ⟨hp₁, hS₁, _, hpos₁⟩ := tupleSet_props hL hG hγ1 hQ hf₁
  obtain ⟨hp₂, hS₂, _, hpos₂⟩ := tupleSet_props hL hG hγ1 hQ hf₂
  have hdvd_char : ∀ (b : Fin G → Bool) (f : activeSet b → ℕ), f ∈ tupleSet L Q_step G j b →
      inSubCell L γ Q_step G j b f n → ∀ p ∈ Sblock L γ Q_step j,
      p ∣ n ↔ ∃ r : activeSet b, f r = p := by
    intro b f hf hsc p hpS
    have hpP : p.Prime := (mem_filter.mp hpS).2
    constructor
    · intro hpn
      have hmul : prodD f * (n / prodD f) = n := Nat.mul_div_cancel' hsc.1
      rw [← hmul] at hpn
      rcases hpP.dvd_mul.mp hpn with hpD | hpq
      · have hpD' : p ∣ prodSub f (activeSet b) := by
          have heq : prodSub f (activeSet b) = prodD f := by
            unfold prodSub prodD; exact prod_congr rfl fun r _ => if_pos r.2
          rwa [heq]
        obtain ⟨r, _, hreq⟩ := (prime_dvd_prodSub_iff hL hG hγ1 hQ hf (activeSet b) hpP).mp hpD'
        exact ⟨r, hreq⟩
      · exact absurd hpq (hsc.2 p hpS)
    · rintro ⟨r, rfl⟩
      exact dvd_trans (dvd_prod_of_mem f (mem_univ r)) hsc.1
  have hb : b₁ = b₂ := by
    ext r
    have hiff : b₁ r = true ↔ b₂ r = true := by
      constructor
      · intro hr1
        have hrb₁ : r ∈ activeSet b₁ := mem_filter.mpr ⟨mem_univ _, hr1⟩
        have hpdvd : f₁ ⟨r, hrb₁⟩ ∣ n := (hdvd_char b₁ f₁ hf₁ h1 _ (hS₁ ⟨r, hrb₁⟩)).mpr ⟨⟨r, hrb₁⟩, rfl⟩
        obtain ⟨r', hr'eq⟩ := (hdvd_char b₂ f₂ hf₂ h2 _ (hS₁ ⟨r, hrb₁⟩)).mp hpdvd
        have hreq : r' = r := by
          by_contra hne
          have hdisj := Pbin_disjoint hL hG hQ (j := j) hne
          exact disjoint_left.mp hdisj (hmem₂ r') (hr'eq ▸ hmem₁ ⟨r, hrb₁⟩)
        have : r'.1 ∈ activeSet b₂ := r'.2
        rw [hreq] at this
        exact (mem_filter.mp this).2
      · intro hr2
        have hrb₂ : r ∈ activeSet b₂ := mem_filter.mpr ⟨mem_univ _, hr2⟩
        have hpdvd : f₂ ⟨r, hrb₂⟩ ∣ n := (hdvd_char b₂ f₂ hf₂ h2 _ (hS₂ ⟨r, hrb₂⟩)).mpr ⟨⟨r, hrb₂⟩, rfl⟩
        obtain ⟨r', hr'eq⟩ := (hdvd_char b₁ f₁ hf₁ h1 _ (hS₂ ⟨r, hrb₂⟩)).mp hpdvd
        have hreq : r' = r := by
          by_contra hne
          have hdisj := Pbin_disjoint hL hG hQ (j := j) hne
          exact disjoint_left.mp hdisj (hmem₁ r') (hr'eq ▸ hmem₂ ⟨r, hrb₂⟩)
        have : r'.1 ∈ activeSet b₁ := r'.2
        rw [hreq] at this
        exact (mem_filter.mp this).2
    cases h1' : b₁ r <;> cases h2' : b₂ r <;> simp [h1', h2'] at hiff ⊢
  subst hb
  refine ⟨rfl, heq_of_eq ?_⟩
  ext r
  have hpdvd : f₁ r ∣ n := (hdvd_char b₁ f₁ hf₁ h1 _ (hS₁ r)).mpr ⟨r, rfl⟩
  obtain ⟨r', hr'eq⟩ := (hdvd_char b₁ f₂ hf₂ h2 _ (hS₁ r)).mp hpdvd
  have hreq : r' = r := by
    by_contra hne
    have hdisj := Pbin_disjoint hL hG hQ (j := j) (fun h => hne (Subtype.ext h))
    exact disjoint_left.mp hdisj (hmem₂ r') (hr'eq ▸ hmem₁ r)
  subst hreq
  exact hr'eq.symm

/-- Injectivity of `(I, J) ↦ J` on `goodPairs L G η b` when `0 < η`. -/
lemma goodPairs_snd_inj {L : ℝ} {G : ℕ} {η : ℝ} (hη : 0 < η) (b : Fin G → Bool) :
    Set.InjOn Prod.snd (goodPairs L G η b : Set (Finset (Fin G) × Finset (Fin G))) := by
  rintro ⟨I₁, J₁⟩ h₁ ⟨I₂, J₂⟩ h₂ hJeq
  dsimp at hJeq; subst hJeq
  by_contra hne
  have hI : I₁ ≠ I₂ := fun h => hne (by subst h; rfl)
  simp only [mem_coe, goodPairs, mem_filter, mem_product] at h₁ h₂
  have hI1_ne_J : I₁ ≠ J₁ := by
    intro h; subst h; linarith [h₁.2.2.2.1]
  have hI2_ne_J : I₂ ≠ J₁ := by
    intro h; subst h; linarith [h₂.2.2.2.1]
  rcases le_total (subSum (xHi L G) I₁) (subSum (xHi L G) I₂) with hle | hle
  · rcases h₁.2.2.2.2.2 I₂ h₂.1.1 hI.symm hI2_ne_J with hlt | hgt
    · linarith
    · linarith [h₂.2.2.2.1]
  · rcases h₂.2.2.2.2.2 I₁ h₁.1.1 hI hI1_ne_J with hlt | hgt
    · linarith
    · linarith [h₁.2.2.2.1]

/-- Deterministic lower bound: for any `n > 0` and finite set of blocks `J_set`,
`∑ j ∈ J_set, Z_val j n ≤ tauPerp n`. -/
lemma sum_Z_le_tauPerp {L γ β Q_step η : ℝ} {G : ℕ}
    (hL : exp 10000000000 ≤ L) (hG : 0 < G)
    (hηpos : 0 < η) (hγpos : 0 < γ) (hγ1 : γ ≤ 1) (hβ : β = η / 4)
    (hQ : Q_step = 2 * L / γ)
    (hfine : 40 * log L * L * gridDelta L G ≤ η)
    (J_set : Finset ℕ) {n : ℕ} (hn : 0 < n) :
    ∑ j ∈ J_set, Z_val L γ β Q_step η G j n ≤ (Erdos1100.tauPerp n : ℝ) := by
  have hLpos : 0 < L := lt_of_lt_of_le (exp_pos _) hL
  have hL1 : 1 < L := (log_pos_iff hLpos.le).mp (by
    have := log_le_log (exp_pos _) hL; rw [log_exp] at this; linarith)
  have hQpos : 0 < Q_step := by rw [hQ]; positivity
  have hΔpos : 0 < gridDelta L G := gridDelta_pos hL1 hG
  have hp_le_Δ : gridP L G ≤ gridDelta L G := by
    unfold gridP; linarith [add_one_le_exp (-(gridDelta L G))]
  -- For each `j`, build the set `U j` of upper endpoints `prodSub f IJ.2` if `(j, n)` is active:
  have hblock_exists : ∀ j : ℕ, ∃ U : Finset ℕ,
      (U.card : ℝ) = Z_val L γ β Q_step η G j n ∧
      (∀ d' ∈ U, ∃ d₁ : ℕ, IsCoprimeConsecDiv n d₁ d') ∧
      (∀ d' ∈ U, ∃ p ∈ Sblock L γ Q_step j, p ∣ d') ∧
      (∀ d' ∈ U, ∀ p : ℕ, p.Prime → p ∣ d' → p ∈ Sblock L γ Q_step j) := by
    intro j
    by_cases hA : (smoothPart (loBlock γ Q_step j) n : ℝ) ≤ exp (β * Q_step ^ j)
    · by_cases hex : ∃ (b : Fin G → Bool) (f : activeSet b → ℕ),
          f ∈ tupleSet L Q_step G j b ∧ inSubCell L γ Q_step G j b f n ∧ isTyp L G b
      · obtain ⟨b₀, f₀, hf₀, hsc₀, htyp₀⟩ := hex
        obtain ⟨hp₀, hS₀, hinj₀, hDpos₀⟩ := tupleSet_props hL1 hG hγ1 hQpos hf₀
        have hY_eq : Y_val L γ Q_step η G j n = (cellScore L G η b₀ : ℝ) := by
          unfold Y_val
          rw [sum_eq_single b₀]
          · rw [sum_eq_single f₀]
            · rw [if_pos hsc₀]
            · intro f hf hne
              rw [if_neg]; intro hsc
              exact hne (eq_of_heq (inSubCell_unique hL1 hG hγ1 hQpos hn hf hf₀ hsc hsc₀).2)
            · intro h; exact absurd hf₀ h
          · intro b _ hne
            refine sum_eq_zero fun f hf => ?_
            rw [if_neg]; intro hsc
            exact hne (inSubCell_unique hL1 hG hγ1 hQpos hn hf hf₀ hsc hsc₀).1
          · simp
        have hZ_eq : Z_val L γ β Q_step η G j n = ((goodPairs L G η b₀).card : ℝ) := by
          unfold Z_val; rw [if_pos hA, hY_eq]; unfold cellScore; rw [if_pos htyp₀]
        set U := (goodPairs L G η b₀).image (fun IJ => prodSub f₀ IJ.2)
        have hU_card : (U.card : ℝ) = ((goodPairs L G η b₀).card : ℝ) := by
          norm_cast
          refine card_image_of_injOn ?_
          intro IJ₁ h₁ IJ₂ h₂ heq
          have hJ₁ : IJ₁.2 ⊆ activeSet b₀ :=
            mem_powerset.mp (mem_product.mp (mem_filter.mp h₁).1).2
          have hJ₂ : IJ₂.2 ⊆ activeSet b₀ :=
            mem_powerset.mp (mem_product.mp (mem_filter.mp h₂).1).2
          have hJeq := prodSub_inj hL1 hG hγ1 hQpos hf₀ hJ₁ hJ₂ heq
          exact goodPairs_snd_inj hηpos b₀ h₁ h₂ hJeq
        -- Exact log approximation for `prodSub f₀ H` (`H ⊆ activeSet b₀`):
        have hlog_sub : ∀ H : Finset (Fin G), H ⊆ activeSet b₀ →
            (subSum (xHi L G) H - η / 20) * Q_step ^ j ≤ log (prodSub f₀ H : ℝ) ∧
            log (prodSub f₀ H : ℝ) ≤ subSum (xHi L G) H * Q_step ^ j := by
          intro H hH
          have hPeq : log (prodSub f₀ H : ℝ) = ∑ r : activeSet b₀, if r.1 ∈ H then log (f₀ r : ℝ) else 0 := by
            unfold prodSub
            rw [Nat.cast_prod, log_prod]
            · refine sum_congr rfl fun r _ => by split_ifs <;> simp
            · intro r _; split_ifs; exact (Nat.cast_pos.mpr (hp₀ r).pos).ne'; norm_num
          have hSumeq : subSum (xHi L G) H = ∑ r : activeSet b₀, if r.1 ∈ H then xHi L G r.1 else 0 := by
            unfold subSum
            rw [← sum_filter]
            symm
            refine sum_nbij (fun r => r.1) ?_ ?_ ?_ ?_
            · intro r hr; exact (mem_filter.mp (mem_coe.mp hr)).2
            · intro r₁ _ r₂ _ h; exact Subtype.ext h
            · intro r hr; exact ⟨⟨r, hH hr⟩, mem_coe.mpr (mem_filter.mpr ⟨mem_univ _, hr⟩), rfl⟩
            · intro _ _; rfl
          have hbin_log : ∀ r : activeSet b₀,
              xLo L G r.1 * Q_step ^ j < log (f₀ r : ℝ) ∧
              log (f₀ r : ℝ) ≤ xHi L G r.1 * Q_step ^ j := by
            intro r
            have hmem := mem_Ioc.mp (mem_filter.mp (Fintype.mem_piFinset.mp hf₀ r)).1
            have hlo_lt : exp (xLo L G r.1 * Q_step ^ j) < (f₀ r : ℝ) := by
              have h1 : exp (xLo L G r.1 * Q_step ^ j) < ((loBin L Q_step G j r.1 : ℕ) : ℝ) + 1 :=
                Nat.lt_floor_add_one _
              have h2 : ((loBin L Q_step G j r.1 : ℕ) : ℝ) + 1 ≤ (f₀ r : ℝ) := by exact_mod_cast hmem.1
              linarith
            have hhi_le : (f₀ r : ℝ) ≤ exp (xHi L G r.1 * Q_step ^ j) := by
              have h1 : (f₀ r : ℝ) ≤ ((hiBin L Q_step G j r.1 : ℕ) : ℝ) := by exact_mod_cast hmem.2
              have h2 : ((hiBin L Q_step G j r.1 : ℕ) : ℝ) ≤ exp (xHi L G r.1 * Q_step ^ j) :=
                Nat.floor_le (exp_pos _).le
              linarith
            constructor
            · have := log_lt_log (exp_pos _) hlo_lt; rwa [log_exp] at this
            · have := log_le_log (Nat.cast_pos.mpr (hp₀ r).pos) hhi_le; rwa [log_exp] at this
          rw [hPeq, hSumeq]
          constructor
          · have hdiff : (∑ r : activeSet b₀, if r.1 ∈ H then xHi L G r.1 else 0) * Q_step ^ j -
                (∑ r : activeSet b₀, if r.1 ∈ H then log (f₀ r : ℝ) else 0) ≤
                (η / 20) * Q_step ^ j := by
              rw [sum_mul, ← sum_sub_distrib]
              have hterm_le : ∀ r : activeSet b₀,
                  (if r.1 ∈ H then xHi L G r.1 else 0) * Q_step ^ j -
                    (if r.1 ∈ H then log (f₀ r : ℝ) else 0) ≤
                  (if r.1 ∈ H then gridDelta L G * L * Q_step ^ j else 0) := by
                intro r
                by_cases hr : r.1 ∈ H
                · simp only [if_pos hr]
                  have hbl := (hbin_log r).1
                  have hsub : xHi L G r.1 - xLo L G r.1 = gridP L G * xHi L G r.1 := xHi_sub_xLo r.1
                  have hxL := (xHi_gt_one_and_le hL1 hG r.1).2
                  have hp_nn : 0 ≤ gridP L G := by
                    unfold gridP; linarith [exp_le_one_iff.mpr (show -(gridDelta L G) ≤ 0 by linarith)]
                  have hprod : gridP L G * xHi L G r.1 ≤ gridDelta L G * L :=
                    mul_le_mul hp_le_Δ hxL (xHi_nonneg hL1 hG r.1) hΔpos.le
                  have hQnn : 0 ≤ Q_step ^ j := by positivity
                  have h1 : (xHi L G r.1 - xLo L G r.1) * Q_step ^ j ≤ gridDelta L G * L * Q_step ^ j := by
                    rw [hsub]; exact mul_le_mul_of_nonneg_right hprod hQnn
                  linarith
                · simp [hr]
              calc _ ≤ ∑ r : activeSet b₀, if r.1 ∈ H then gridDelta L G * L * Q_step ^ j else 0 :=
                      sum_le_sum fun r _ => hterm_le r
                _ = (H.card : ℝ) * (gridDelta L G * L * Q_step ^ j) := by
                      rw [← sum_filter, sum_const, nsmul_eq_mul]
                      congr 1; congr 1
                      refine card_bij (fun r _ => r.1) ?_ ?_ ?_
                      · intro r hr; exact (mem_filter.mp hr).2
                      · intro r₁ _ r₂ _ h; exact Subtype.ext h
                      · intro r hr; exact ⟨⟨r, hH hr⟩, mem_filter.mpr ⟨mem_univ _, hr⟩, rfl⟩
                _ ≤ (2 * log L) * (gridDelta L G * L * Q_step ^ j) := by
                      have hHcard : (H.card : ℝ) ≤ 2 * log L := by
                        have h1 : (H.card : ℝ) ≤ ((activeSet b₀).card : ℝ) := by exact_mod_cast card_le_card hH
                        have h2 := isTyp_card_total hL1 hG htyp₀
                        have hlog_pos : 0 < log L := log_pos hL1
                        linarith
                      exact mul_le_mul_of_nonneg_right hHcard (by positivity)
                _ ≤ (η / 20) * Q_step ^ j := by
                      have hQnn : 0 ≤ Q_step ^ j := by positivity
                      have : 2 * log L * (gridDelta L G * L) ≤ η / 20 := by linarith
                      nlinarith
            linarith
          · rw [sum_mul]
            refine sum_le_sum fun r _ => ?_
            by_cases hr : r.1 ∈ H
            · simp only [if_pos hr]; exact (hbin_log r).2
            · simp [hr]
        -- Decompose `n = A * Q * R`:
        set A := smoothPart (loBlock γ Q_step j) n
        set Q := prodD f₀
        have hAQ : Nat.Coprime A Q := by
          rw [Nat.coprime_iff_gcd_eq_one]
          by_contra hne
          obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hne
          have h1 := prime_dvd_smoothPart_le hp (dvd_trans hpg (Nat.gcd_dvd_left _ _))
          have hpQ' : p ∣ prodSub f₀ (activeSet b₀) := by
            have heq : prodSub f₀ (activeSet b₀) = Q := by
              unfold prodSub Q prodD; exact prod_congr rfl fun r _ => if_pos r.2
            rw [heq]; exact dvd_trans hpg (Nat.gcd_dvd_right _ _)
          obtain ⟨r, _, rfl⟩ := (prime_dvd_prodSub_iff hL1 hG hγ1 hQpos hf₀ (activeSet b₀) hp).mp hpQ'
          have hgt := (mem_Ioc.mp (mem_filter.mp (hS₀ r)).1).1
          omega
        have hAn : A ∣ n := ⟨roughPart (loBlock γ Q_step j) n, (smoothPart_mul_roughPart hn).symm⟩
        have hAQn : A * Q ∣ n := hAQ.mul_dvd_of_dvd_of_dvd hAn hsc₀.1
        set R := n / (A * Q)
        have hn_eq : n = A * Q * R := (Nat.mul_div_cancel' hAQn).symm
        have hRgt : ∀ p : ℕ, p.Prime → p ∣ R → hiBlock L Q_step j < p := by
          intro p hp hpR
          have hpR_rough : R ∣ roughPart (loBlock γ Q_step j) n := by
            have h1 : A * (Q * R) = A * roughPart (loBlock γ Q_step j) n := by
              rw [← mul_assoc, ← hn_eq, smoothPart_mul_roughPart hn]
            exact ⟨Q, (Nat.eq_of_mul_eq_mul_left (smoothPart_pos _ _) h1).symm.trans (mul_comm Q R)⟩
          have hgt_lo := prime_dvd_roughPart_gt hp (dvd_trans hpR hpR_rough)
          have hpR_q : R ∣ n / Q := by
            have h1 : Q * (A * R) = Q * (n / Q) := by
              rw [Nat.mul_div_cancel' hsc₀.1, show Q * (A * R) = A * Q * R by ring, ← hn_eq]
            exact ⟨A, (Nat.eq_of_mul_eq_mul_left hDpos₀ h1).symm.trans (mul_comm A R)⟩
          by_contra hle; push Not at hle
          have hpS : p ∈ Sblock L γ Q_step j :=
            mem_filter.mpr ⟨mem_Ioc.mpr ⟨hgt_lo, hle⟩, hp⟩
          exact hsc₀.2 p hpS (dvd_trans hpR hpR_q)
        refine ⟨U, by rw [hU_card, hZ_eq], ?_, ?_, ?_⟩
        · intro d' hd'
          obtain ⟨⟨I, J⟩, hIJ, rfl⟩ := mem_image.mp hd'
          have hIJ' := mem_filter.mp hIJ
          have hIsub : I ⊆ activeSet b₀ := mem_powerset.mp (mem_product.mp hIJ'.1).1
          have hJsub : J ⊆ activeSet b₀ := mem_powerset.mp (mem_product.mp hIJ'.1).2
          have hdisj := hIJ'.2.1
          have hJL := hIJ'.2.2.1
          have hdiffLo := hIJ'.2.2.2.1
          have hpad := hIJ'.2.2.2.2.2
          set d := prodSub f₀ I
          set d' := prodSub f₀ J
          have hdpos : 0 < d := prodSub_pos hL1 hG hγ1 hQpos hf₀ I
          have hd'pos : 0 < d' := prodSub_pos hL1 hG hγ1 hQpos hf₀ J
          have hApos : 0 < A := smoothPart_pos _ _
          have hd'B : d' ≤ hiBlock L Q_step j := by
            have hlogJ := (hlog_sub J hJsub).2
            have h1 : log (d' : ℝ) ≤ L * Q_step ^ j :=
              le_trans hlogJ (mul_le_mul_of_nonneg_right hJL (by positivity))
            have h2 : (d' : ℝ) ≤ exp (L * Q_step ^ j) := by
              rw [← exp_log (Nat.cast_pos.mpr hd'pos)]
              exact exp_le_exp.mpr h1
            exact Nat.le_floor h2
          have hgap : A * d < d' := by
            have hlogA : log (A : ℝ) ≤ β * Q_step ^ j := by
              have := log_le_log (Nat.cast_pos.mpr hApos) hA
              rwa [log_exp] at this
            have hlogI := (hlog_sub I hIsub).2
            have hlogJ := (hlog_sub J hJsub).1
            have hlogAd : log ((A * d : ℕ) : ℝ) < log (d' : ℝ) := by
              rw [Nat.cast_mul, log_mul (Nat.cast_pos.mpr hApos).ne' (Nat.cast_pos.mpr hdpos).ne']
              have hQpow_pos : 0 < Q_step ^ j := by positivity
              have hstrict : (β + subSum (xHi L G) I) * Q_step ^ j < (subSum (xHi L G) J - η / 20) * Q_step ^ j := by
                rw [hβ]
                exact mul_lt_mul_of_pos_right (by linarith) hQpow_pos
              linarith
            exact_mod_cast (log_lt_log_iff (by positivity) (by positivity)).mp hlogAd
          have hconsec : ∀ u : ℕ, u ∣ Q → d < u → d' ≤ u := by
            intro u huQ hdu
            obtain ⟨H, hHsub, rfl⟩ := exists_prodSub_of_dvd_prodD hL1 hG hγ1 hQpos hf₀ huQ
            by_cases hHI : H = I
            · subst hHI; omega
            · by_cases hHJ : H = J
              · subst hHJ; exact le_rfl
              · have hQpow_pos : 0 < Q_step ^ j := by positivity
                have hupos : 0 < prodSub f₀ H := prodSub_pos hL1 hG hγ1 hQpos hf₀ H
                rcases hpad H (mem_powerset.mpr hHsub) hHI hHJ with hlt | hgt
                · exfalso
                  have hlogH := (hlog_sub H hHsub).2
                  have hlogI := (hlog_sub I hIsub).1
                  have hlt_log : log (prodSub f₀ H : ℝ) < log (d : ℝ) := by
                    have hstrict : subSum (xHi L G) H * Q_step ^ j < (subSum (xHi L G) I - η / 20) * Q_step ^ j :=
                      mul_lt_mul_of_pos_right (by linarith) hQpow_pos
                    linarith
                  have : prodSub f₀ H < d := by
                    exact_mod_cast (log_lt_log_iff (by positivity) (by positivity)).mp hlt_log
                  omega
                · have hlogH := (hlog_sub H hHsub).1
                  have hlogJ := (hlog_sub J hJsub).2
                  have hlt_log : log (d' : ℝ) < log (prodSub f₀ H : ℝ) := by
                    have hstrict : subSum (xHi L G) J * Q_step ^ j < (subSum (xHi L G) H - η / 20) * Q_step ^ j :=
                      mul_lt_mul_of_pos_right (by linarith) hQpow_pos
                    linarith
                  have : d' < prodSub f₀ H := by
                    exact_mod_cast (log_lt_log_iff (by positivity) (by positivity)).mp hlt_log
                  exact le_of_lt this
          exact ⟨A * d, isCoprimeConsecDiv_of_block hn_eq hApos hAQ hRgt (prodSub_dvd_prodD f₀ I)
            (prodSub_dvd_prodD f₀ J) hd'B (prodSub_coprime hL1 hG hγ1 hQpos hf₀ hdisj) hgap hconsec⟩
        · intro d' hd'
          obtain ⟨⟨I, J⟩, hIJ, rfl⟩ := mem_image.mp hd'
          have hIJ' := mem_filter.mp hIJ
          have hJsub : J ⊆ activeSet b₀ := mem_powerset.mp (mem_product.mp hIJ'.1).2
          have hJne : J.Nonempty := by
            rw [nonempty_iff_ne_empty]; intro hJe
            have h0 : subSum (xHi L G) J = 0 := by rw [hJe]; simp [subSum]
            have hInn := subSum_xHi_nonneg hL1 hG I
            linarith [hIJ'.2.2.2.1]
          obtain ⟨r, hrJ⟩ := hJne
          have hrb : r ∈ activeSet b₀ := hJsub hrJ
          exact ⟨f₀ ⟨r, hrb⟩, hS₀ ⟨r, hrb⟩,
            (prime_dvd_prodSub_iff hL1 hG hγ1 hQpos hf₀ J (hp₀ ⟨r, hrb⟩)).mpr ⟨⟨r, hrb⟩, hrJ, rfl⟩⟩
        · intro d' hd' p hp hpd'
          obtain ⟨⟨I, J⟩, _, rfl⟩ := mem_image.mp hd'
          obtain ⟨r, _, rfl⟩ := (prime_dvd_prodSub_iff hL1 hG hγ1 hQpos hf₀ J hp).mp hpd'
          exact hS₀ r
      · -- No typical active subcell in block `j`, so `Z_val j n = 0`:
        refine ⟨∅, ?_, by simp, by simp, by simp⟩
        simp only [card_empty, Nat.cast_zero]
        symm
        unfold Z_val
        rw [if_pos hA]
        unfold Y_val
        refine sum_eq_zero fun b _ => sum_eq_zero fun f hf => ?_
        by_cases hsc : inSubCell L γ Q_step G j b f n
        · rw [if_pos hsc]
          have hntyp : ¬isTyp L G b := fun ht => hex ⟨b, f, hf, hsc, ht⟩
          unfold cellScore; simp [hntyp]
        · rw [if_neg hsc]
    · refine ⟨∅, ?_, by simp, by simp, by simp⟩
      simp [Z_val, hA]
  choose U hU_card hU_consec hU_hasP hU_allP using hblock_exists
  have hdisj_U : Set.PairwiseDisjoint (J_set : Set ℕ) U := by
    intro j₁ _ j₂ _ hne
    change Disjoint (U j₁) (U j₂)
    rw [disjoint_left]
    intro d' hd₁ hd₂
    obtain ⟨p, hpS₁, hpd'⟩ := hU_hasP j₁ d' hd₁
    have hpP : p.Prime := (mem_filter.mp hpS₁).2
    have hpS₂ : p ∈ Sblock L γ Q_step j₂ := hU_allP j₂ d' hd₂ p hpP hpd'
    exact disjoint_left.mp (Sblock_disjoint hγpos hQ hL1 hγ1 hne) hpS₁ hpS₂
  have hcard_tot : ∑ j ∈ J_set, Z_val L γ β Q_step η G j n = ((J_set.biUnion U).card : ℝ) := by
    rw [card_biUnion hdisj_U, Nat.cast_sum]
    exact sum_congr rfl fun j _ => (hU_card j).symm
  rw [hcard_tot]
  exact_mod_cast card_le_tauPerp_of_exists_consec hn (J_set.biUnion U) fun d' hd' => by
    obtain ⟨j, _, hj⟩ := mem_biUnion.mp hd'
    exact hU_consec j d' hj

/- ### Part 7E: Block Weights, Bonferroni Counting, and `A_j`-Trimming -/

/-- Exact factorization of `bernProb (gridP L G) b` in terms of `L` and `exp(gridDelta L G) - 1`. -/
lemma bernProb_gridP_eq {L : ℝ} {G : ℕ} (hL : 1 < L) (hG : 0 < G) (b : Fin G → Bool) :
    bernProb (gridP L G) b =
      (1 / L) * (exp (gridDelta L G) - 1) ^ (activeSet b).card := by
  set Δ := gridDelta L G
  have h1 : ∀ r : Fin G, (if b r then gridP L G else 1 - gridP L G) =
      exp (-Δ) * (if b r then exp Δ - 1 else 1) := by
    intro r
    unfold gridP
    by_cases hbr : b r = true
    · simp only [hbr, ite_true]
      rw [mul_sub, mul_one, ← exp_add, neg_add_cancel, exp_zero]
    · simp only [hbr, Bool.false_eq_true, ite_false, Δ]; ring
  unfold bernProb
  simp_rw [h1]
  rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin]
  have hfirst : (exp (-Δ)) ^ G = 1 / L := by
    rw [← exp_nat_mul]
    have hGne : (G : ℝ) ≠ 0 := by positivity
    have harg : (G : ℝ) * -Δ = -log L := by
      unfold Δ gridDelta; field_simp [hGne]
    rw [harg, exp_neg, exp_log (by linarith), one_div]
  have hsecond : (∏ r : Fin G, if b r then exp Δ - 1 else 1) =
      (exp Δ - 1) ^ (activeSet b).card := by
    rw [← prod_filter, prod_const]
    rfl
  rw [hfirst, hsecond]

/-- Product factorization of `∑ f ∈ tupleSet j b, 1 / prodD f`. -/
lemma sum_inv_prodD_eq_prod (L Q_step : ℝ) (G j : ℕ) (b : Fin G → Bool) :
    ∑ f ∈ tupleSet L Q_step G j b, (1 : ℝ) / (prodD f : ℝ) =
      ∏ r : activeSet b, ∑ p ∈ Pbin L Q_step G j r.1, (1 : ℝ) / (p : ℝ) := by
  unfold tupleSet
  rw [prod_univ_sum]
  refine sum_congr rfl fun f _ => ?_
  unfold prodD
  rw [Nat.cast_prod, prod_div_distrib, prod_const_one]

/-- Theoretical block-`j` density of configuration `b`. -/
noncomputable def blockWeight (L γ Q_step : ℝ) (G j : ℕ) (b : Fin G → Bool) : ℝ :=
  (∏ q ∈ Sblock L γ Q_step j, (1 - (1 : ℝ) / (q : ℝ))) *
    ∑ f ∈ tupleSet L Q_step G j b, (1 : ℝ) / (prodD f : ℝ)

/-- Comparison of `blockWeight` against `γ * bernProb (gridP L G) b` on typical configurations `b`. -/
lemma blockWeight_approx {L γ Q_step η ε : ℝ} {G j : ℕ}
    (hL : exp 10000000000 ≤ L) (hG : 0 < G)
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    (hη : η = L ^ (-(1 / 40 : ℝ))) (hγ : γ = (ε / 400) * η)
    (hQ : Q_step = 2 * L / γ)
    (hfine : 40 * log L * L * gridDelta L G ≤ η)
    (hLε : 10000000 / ε ≤ L)
    (hj1 : 4 ≤ γ * Q_step ^ j)
    (hj2 : 330 / (γ * Q_step ^ j) ≤ ε / 20000)
    (hj3 : (2 / (loBlock γ Q_step j : ℝ)) * (log (L / γ) + 1) ≤ ε / 20000)
    (hj4 : 330 / Q_step ^ j ≤ (gridDelta L G) ^ 2) :
    ((1 - ε / 1000) * (γ / L) ≤ ∏ q ∈ Sblock L γ Q_step j, (1 - (1 : ℝ) / (q : ℝ)) ∧
      ∏ q ∈ Sblock L γ Q_step j, (1 - (1 : ℝ) / (q : ℝ)) ≤ (1 + ε / 1000) * (γ / L)) ∧
    (∑ q ∈ Sblock L γ Q_step j, (1 : ℝ) / (q : ℝ) ≤ log (L / γ) + 1) ∧
    (∀ b : Fin G → Bool, isTyp L G b →
      (1 - ε / 500) * γ * bernProb (gridP L G) b ≤ blockWeight L γ Q_step G j b ∧
      blockWeight L γ Q_step G j b ≤ (1 + ε / 500) * γ * bernProb (gridP L G) b) := by
  have hlogL_ge : (10000000000 : ℝ) ≤ log L := by
    have := log_le_log (exp_pos _) hL; rwa [log_exp] at this
  have hLpos : 0 < L := lt_of_lt_of_le (exp_pos _) hL
  have hL1 : 1 < L := (log_pos_iff hLpos.le).mp (by linarith)
  have hηpos : 0 < η := by rw [hη]; exact rpow_pos_of_pos hLpos _
  have hηle : η ≤ 1 / 10 := by
    rw [hη, rpow_def_of_pos hLpos]
    have h2 : exp (-10) ≤ 1 / 10 := by
      rw [exp_neg, one_div]; exact inv_anti₀ (by norm_num) (by linarith [add_one_le_exp (10 : ℝ)])
    exact le_trans (exp_le_exp.mpr (by linarith)) h2
  have hγpos : 0 < γ := by rw [hγ]; positivity
  have hγ1 : γ ≤ 1 := by
    rw [hγ]
    have := mul_le_mul_of_nonneg_left hηle (by positivity : 0 ≤ ε / 400)
    linarith
  have hQpos : 0 < Q_step := by rw [hQ]; positivity
  have hQpow_pos : 0 < Q_step ^ j := pow_pos hQpos j
  set Δ := gridDelta L G
  have hΔpos : 0 < Δ := gridDelta_pos hL1 hG
  have hΔle : Δ ≤ 1 / 1000000 := by
    have hLbig : (100000 : ℝ) ≤ L := by linarith [add_one_le_exp (10000000000 : ℝ)]
    have hLL : (10000000000 : ℝ) * 100000 ≤ log L * L :=
      mul_le_mul hlogL_ge hLbig (by norm_num) (by linarith)
    have hmul : 40 * (10000000000 * 100000) * Δ ≤ 40 * (log L * L) * Δ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLL (by norm_num)) hΔpos.le
    linarith [show 40 * (log L * L) * Δ = 40 * log L * L * Δ by ring]
  -- Step 1: Mertens estimate on `Sblock j` and `∏_{q ∈ Sblock j} (1 - 1/q)`.
  have hmS := mertens_Ioc_exp (a_exp := γ * Q_step ^ j) (b_exp := L * Q_step ^ j)
    hj1 (mul_le_mul_of_nonneg_right (by linarith) hQpow_pos.le)
  have hrat_S : (L * Q_step ^ j) / (γ * Q_step ^ j) = L / γ := mul_div_mul_right L γ hQpow_pos.ne'
  rw [hrat_S] at hmS
  change |∑ q ∈ Sblock L γ Q_step j, (1 : ℝ) / (q : ℝ) - log (L / γ)| ≤ 330 / (γ * Q_step ^ j) at hmS
  rw [abs_le] at hmS
  have hSsum_le : ∑ q ∈ Sblock L γ Q_step j, (1 : ℝ) / (q : ℝ) ≤ log (L / γ) + 1 := by linarith
  have hlo_ge4 : (4 : ℝ) ≤ (loBlock γ Q_step j : ℝ) := by
    have h1 : (4 : ℝ) ≤ exp (γ * Q_step ^ j) := by linarith [add_one_le_exp (γ * Q_step ^ j)]
    exact_mod_cast Nat.le_floor h1
  have hprodS := prod_one_sub_inv_bounds (Sblock L γ Q_step j) hlo_ge4 fun q hq => by
    have hgt := (mem_Ioc.mp (mem_filter.mp hq).1).1
    exact_mod_cast le_of_lt hgt
  -- Helper: `1 - t ≤ exp (-t)` and `exp t ≤ 1 + 2 * t` for `0 ≤ t ≤ 1/2`:
  have hexp_ub : ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 2 → exp t ≤ 1 + 2 * t := by
    intro t ht0 ht1
    have h1 : exp t ≤ 1 / (1 - t) := by
      have hpos : 0 < 1 - t := by linarith
      rw [le_div_iff₀ hpos]
      have h2 := add_one_le_exp (-t)
      have h3 : (1 - t) * exp t ≤ exp (-t) * exp t :=
        mul_le_mul_of_nonneg_right (by linarith) (exp_pos t).le
      rw [← exp_add, neg_add_cancel, exp_zero] at h3
      linarith
    have h2 : 1 / (1 - t) ≤ 1 + 2 * t := by
      rw [div_le_iff₀ (by linarith : 0 < 1 - t)]
      have : 0 ≤ t * (1 - 2 * t) := mul_nonneg ht0 (by linarith)
      linarith [show (1 + 2 * t) * (1 - t) - 1 = t * (1 - 2 * t) by ring]
    linarith
  have hW_bounds : (1 - ε / 1000) * (γ / L) ≤ ∏ q ∈ Sblock L γ Q_step j, (1 - (1 : ℝ) / (q : ℝ)) ∧
      ∏ q ∈ Sblock L γ Q_step j, (1 - (1 : ℝ) / (q : ℝ)) ≤ (1 + ε / 1000) * (γ / L) := by
    have hexp_log : exp (-log (L / γ)) = γ / L := by
      rw [exp_neg, exp_log (div_pos hLpos hγpos), inv_div]
    constructor
    · have herr : (2 / (loBlock γ Q_step j : ℝ)) * ∑ q ∈ Sblock L γ Q_step j, (1 : ℝ) / (q : ℝ) ≤ ε / 20000 :=
        le_trans (mul_le_mul_of_nonneg_left hSsum_le (by positivity)) hj3
      have harg : -log (L / γ) - ε / 1000 ≤
          -(∑ q ∈ Sblock L γ Q_step j, (1 : ℝ) / (q : ℝ)) -
            (2 / (loBlock γ Q_step j : ℝ)) * (∑ q ∈ Sblock L γ Q_step j, (1 : ℝ) / (q : ℝ)) := by linarith
      calc (1 - ε / 1000) * (γ / L)
          ≤ exp (-(ε / 1000)) * exp (-log (L / γ)) := by
              rw [hexp_log]; exact mul_le_mul_of_nonneg_right (by linarith [add_one_le_exp (-(ε / 1000))]) (by positivity)
        _ = exp (-log (L / γ) - ε / 1000) := by rw [← exp_add]; congr 1; ring
        _ ≤ _ := le_trans (exp_le_exp.mpr harg) hprodS.1
    · have harg : -(∑ q ∈ Sblock L γ Q_step j, (1 : ℝ) / (q : ℝ)) ≤ -log (L / γ) + ε / 20000 := by linarith
      calc ∏ q ∈ Sblock L γ Q_step j, (1 - (1 : ℝ) / (q : ℝ))
          ≤ exp (-log (L / γ) + ε / 20000) := le_trans hprodS.2 (exp_le_exp.mpr harg)
        _ = exp (ε / 20000) * (γ / L) := by rw [exp_add, hexp_log, mul_comm]
        _ ≤ (1 + ε / 1000) * (γ / L) := by
              have h1 := hexp_ub (ε / 20000) (by positivity) (by linarith)
              exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  -- Step 2: Per-bin Mertens estimate `|∑_{p ∈ Pbin j r} 1/p - Δ| ≤ Δ^2` and ratio vs `exp Δ - 1`.
  have hexpΔ_pos : 0 < exp Δ - 1 := by linarith [add_one_lt_exp hΔpos.ne']
  have hexpΔ_le : exp Δ - 1 ≤ Δ + 2 * Δ ^ 2 := by
    have h1 := hexp_ub Δ hΔpos.le (by linarith)
    -- Wait: `hexp_ub` gives `1 + 2 * Δ`, we want `1 + Δ + 2 * Δ^2` from `exp Δ ≤ 1 / (1 - Δ)`:
    have h2 : exp Δ ≤ 1 / (1 - Δ) := by
      rw [le_div_iff₀ (by linarith : 0 < 1 - Δ)]
      have h3 : (1 - Δ) * exp Δ ≤ exp (-Δ) * exp Δ :=
        mul_le_mul_of_nonneg_right (by linarith [add_one_le_exp (-Δ)]) (exp_pos Δ).le
      rw [← exp_add, neg_add_cancel, exp_zero] at h3; linarith
    have h3 : 1 / (1 - Δ) ≤ 1 + Δ + 2 * Δ ^ 2 := by
      rw [div_le_iff₀ (by linarith : 0 < 1 - Δ)]
      have : 0 ≤ Δ ^ 2 * (1 - 2 * Δ) := mul_nonneg (sq_nonneg Δ) (by linarith)
      linarith [show (1 + Δ + 2 * Δ ^ 2) * (1 - Δ) - 1 = Δ ^ 2 * (1 - 2 * Δ) by ring]
    linarith
  have hbin_ratio : ∀ r : Fin G,
      (1 - 3 * Δ) * (exp Δ - 1) ≤ (∑ p ∈ Pbin L Q_step G j r, (1 : ℝ) / (p : ℝ)) ∧
      (∑ p ∈ Pbin L Q_step G j r, (1 : ℝ) / (p : ℝ)) ≤ (1 + 2 * Δ) * (exp Δ - 1) := by
    intro r
    have hxlo1 := xLo_ge_one hL1 hG r
    have hxlo_lt : xLo L G r ≤ xHi L G r := by
      have hsub := xHi_sub_xLo (L := L) (G := G) r
      have hp_nn : 0 ≤ gridP L G := (gridP_bounds hL1 hG (by linarith)).2.2.1.le
      have hmul : 0 ≤ gridP L G * xHi L G r := mul_nonneg hp_nn (xHi_nonneg hL1 hG r)
      linarith
    have ha_ge4 : 4 ≤ xLo L G r * Q_step ^ j := by
      have h1 : γ * Q_step ^ j ≤ xLo L G r * Q_step ^ j :=
        mul_le_mul_of_nonneg_right (le_trans hγ1 hxlo1) hQpow_pos.le
      linarith
    have hm := mertens_Ioc_exp (a_exp := xLo L G r * Q_step ^ j) (b_exp := xHi L G r * Q_step ^ j)
      ha_ge4 (mul_le_mul_of_nonneg_right hxlo_lt hQpow_pos.le)
    have hrat : log ((xHi L G r * Q_step ^ j) / (xLo L G r * Q_step ^ j)) = Δ := by
      rw [mul_div_mul_right _ _ hQpow_pos.ne']
      unfold xHi xLo
      rw [← exp_sub, log_exp]
      push_cast; ring
    rw [hrat] at hm
    change |∑ p ∈ Pbin L Q_step G j r, (1 : ℝ) / (p : ℝ) - Δ| ≤ 330 / (xLo L G r * Q_step ^ j) at hm
    have h330_le : 330 / (xLo L G r * Q_step ^ j) ≤ Δ ^ 2 := by
      have h1 : 330 / (xLo L G r * Q_step ^ j) ≤ 330 / Q_step ^ j :=
        div_le_div_of_nonneg_left (by norm_num) hQpow_pos (le_mul_of_one_le_left hQpow_pos.le hxlo1)
      linarith
    rw [abs_le] at hm
    constructor
    · have h1 : (1 - 3 * Δ) * (exp Δ - 1) ≤ (1 - 3 * Δ) * (Δ + 2 * Δ ^ 2) :=
        mul_le_mul_of_nonneg_left hexpΔ_le (by linarith)
      have h2 : (1 - 3 * Δ) * (Δ + 2 * Δ ^ 2) ≤ Δ - Δ ^ 2 := by
        have : 0 ≤ 6 * Δ ^ 3 := by positivity
        linarith [show (Δ - Δ ^ 2) - (1 - 3 * Δ) * (Δ + 2 * Δ ^ 2) = 6 * Δ ^ 3 by ring]
      linarith
    · have h1 : Δ ≤ exp Δ - 1 := by linarith [add_one_le_exp Δ]
      have h2 : Δ + Δ ^ 2 ≤ (1 + 2 * Δ) * Δ := by
        linarith [sq_nonneg Δ, show (1 + 2 * Δ) * Δ - (Δ + Δ ^ 2) = Δ ^ 2 by ring]
      have h3 : (1 + 2 * Δ) * Δ ≤ (1 + 2 * Δ) * (exp Δ - 1) :=
        mul_le_mul_of_nonneg_left h1 (by linarith)
      linarith
  -- Step 3: Multiply over `r ∈ activeSet b` for typical `b`:
  refine ⟨hW_bounds, hSsum_le, fun b htyp => ?_⟩
  have hcard_le : ((activeSet b).card : ℝ) ≤ 2 * log L := by
    have := isTyp_card_total hL1 hG htyp
    linarith
  have hlogΔ_le : log L * Δ ≤ ε / 400000000 := by
    have h1 : 40 * log L * L * Δ ≤ 1 := by linarith
    have h2 : 40 * log L * (10000000 / ε) * Δ ≤ 40 * log L * L * Δ := by
      have hnn : 0 ≤ 40 * log L * Δ := by positivity
      have := mul_le_mul_of_nonneg_left hLε hnn
      linarith [show 40 * log L * (10000000 / ε) * Δ = (40 * log L * Δ) * (10000000 / ε) by ring,
                show 40 * log L * L * Δ = (40 * log L * Δ) * L by ring]
    have h3 : 400000000 * (log L * Δ) / ε ≤ 1 := by
      linarith [show 40 * log L * (10000000 / ε) * Δ = 400000000 * (log L * Δ) / ε by ring]
    rw [div_le_iff₀ hε] at h3
    linarith
  have hprod_lo : (1 - ε / 10000) * (exp Δ - 1) ^ (activeSet b).card ≤
      ∏ r : activeSet b, ∑ p ∈ Pbin L Q_step G j r.1, (1 : ℝ) / (p : ℝ) := by
    have h1 : ((1 - 3 * Δ) * (exp Δ - 1)) ^ (activeSet b).card ≤
        ∏ r : activeSet b, ∑ p ∈ Pbin L Q_step G j r.1, (1 : ℝ) / (p : ℝ) := by
      calc ((1 - 3 * Δ) * (exp Δ - 1)) ^ (activeSet b).card
          = ∏ _r : activeSet b, ((1 - 3 * Δ) * (exp Δ - 1)) := by
              rw [prod_const, card_univ, Fintype.card_coe]
        _ ≤ _ := prod_le_prod (fun _ _ => mul_nonneg (by linarith) hexpΔ_pos.le)
              fun r _ => (hbin_ratio r.1).1
    rw [mul_pow] at h1
    have hbern : 1 - ε / 10000 ≤ (1 - 3 * Δ) ^ (activeSet b).card := by
      have hb : 1 + ((activeSet b).card : ℝ) * (-(3 * Δ)) ≤ (1 - 3 * Δ) ^ (activeSet b).card := by
        rw [sub_eq_add_neg]; exact one_add_mul_le_pow (by linarith) _
      have hmul : ((activeSet b).card : ℝ) * (3 * Δ) ≤ 6 * (log L * Δ) := by
        have := mul_le_mul_of_nonneg_right hcard_le (by linarith : 0 ≤ 3 * Δ)
        linarith
      linarith
    exact le_trans (mul_le_mul_of_nonneg_right hbern (pow_nonneg hexpΔ_pos.le _)) h1
  have hprod_hi : (∏ r : activeSet b, ∑ p ∈ Pbin L Q_step G j r.1, (1 : ℝ) / (p : ℝ)) ≤
      (1 + ε / 10000) * (exp Δ - 1) ^ (activeSet b).card := by
    have h1 : (∏ r : activeSet b, ∑ p ∈ Pbin L Q_step G j r.1, (1 : ℝ) / (p : ℝ)) ≤
        ((1 + 2 * Δ) * (exp Δ - 1)) ^ (activeSet b).card := by
      calc _ ≤ ∏ _r : activeSet b, ((1 + 2 * Δ) * (exp Δ - 1)) :=
            prod_le_prod (fun r _ => sum_nonneg fun _ _ => by positivity)
              fun r _ => (hbin_ratio r.1).2
        _ = _ := by rw [prod_const, card_univ, Fintype.card_coe]
    rw [mul_pow] at h1
    have hexp_b : (1 + 2 * Δ) ^ (activeSet b).card ≤ 1 + ε / 10000 := by
      calc (1 + 2 * Δ) ^ (activeSet b).card
          ≤ (exp (2 * Δ)) ^ (activeSet b).card :=
              pow_le_pow_left₀ (by linarith) (by linarith [add_one_le_exp (2 * Δ)]) _
        _ = exp (((activeSet b).card : ℝ) * (2 * Δ)) := (exp_nat_mul _ _).symm
        _ ≤ exp (4 * (log L * Δ)) := by
              apply exp_le_exp.mpr
              have := mul_le_mul_of_nonneg_right hcard_le (by linarith : 0 ≤ 2 * Δ)
              linarith
        _ ≤ 1 + 8 * (log L * Δ) := by
              have h := hexp_ub (4 * (log L * Δ)) (by positivity) (by linarith)
              linarith
        _ ≤ 1 + ε / 10000 := by linarith
    exact le_trans h1 (mul_le_mul_of_nonneg_right hexp_b (pow_nonneg hexpΔ_pos.le _))
  unfold blockWeight
  rw [sum_inv_prodD_eq_prod, bernProb_gridP_eq hL1 hG b]
  have hW_nn : 0 ≤ ∏ q ∈ Sblock L γ Q_step j, (1 - (1 : ℝ) / (q : ℝ)) :=
    prod_nonneg fun q hq => by
      have hq2 := (mem_filter.mp hq).2.two_le
      have : (1 : ℝ) / (q : ℝ) ≤ 1 := by rw [div_le_one (by positivity)]; exact_mod_cast (by omega : 1 ≤ q)
      linarith
  have hP_nn : 0 ≤ ∏ r : activeSet b, ∑ p ∈ Pbin L Q_step G j r.1, (1 : ℝ) / (p : ℝ) :=
    prod_nonneg fun _ _ => sum_nonneg fun _ _ => by positivity
  have hR_nn : 0 ≤ (exp Δ - 1) ^ (activeSet b).card := pow_nonneg hexpΔ_pos.le _
  have hγL_nn : 0 ≤ γ / L := by positivity
  constructor
  · calc (1 - ε / 500) * γ * ((1 / L) * (exp Δ - 1) ^ (activeSet b).card)
        = (1 - ε / 500) * ((γ / L) * (exp Δ - 1) ^ (activeSet b).card) := by ring
      _ ≤ ((1 - ε / 1000) * (1 - ε / 10000)) * ((γ / L) * (exp Δ - 1) ^ (activeSet b).card) := by
            refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hγL_nn hR_nn)
            linarith [sq_nonneg ε, show (1 - ε / 1000) * (1 - ε / 10000) - (1 - ε / 500) =
              (9 / 10000 : ℝ) * ε + ε ^ 2 / 10000000 by ring]
      _ = ((1 - ε / 1000) * (γ / L)) * ((1 - ε / 10000) * (exp Δ - 1) ^ (activeSet b).card) := by ring
      _ ≤ _ := mul_le_mul hW_bounds.1 hprod_lo (mul_nonneg (by linarith) hR_nn) hW_nn
  · calc _ ≤ ((1 + ε / 1000) * (γ / L)) * ((1 + ε / 10000) * (exp Δ - 1) ^ (activeSet b).card) :=
            mul_le_mul hW_bounds.2 hprod_hi hP_nn (mul_nonneg (by linarith) hγL_nn)
      _ = ((1 + ε / 1000) * (1 + ε / 10000)) * ((γ / L) * (exp Δ - 1) ^ (activeSet b).card) := by ring
      _ ≤ (1 + ε / 500) * ((γ / L) * (exp Δ - 1) ^ (activeSet b).card) := by
            refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hγL_nn hR_nn)
            have hnn : 0 ≤ ε * ((9 / 10000 : ℝ) - ε / 10000000) := mul_nonneg hε.le (by linarith)
            linarith [show (1 + ε / 500) - (1 + ε / 1000) * (1 + ε / 10000) =
              ε * ((9 / 10000 : ℝ) - ε / 10000000) by ring]
      _ = (1 + ε / 500) * γ * ((1 / L) * (exp Δ - 1) ^ (activeSet b).card) := by ring

/-- Exact Bonferroni count for a single subcell `(j, b, f)` on `Icc 1 N`. -/
lemma subCell_count_bonferroni {L γ Q_step : ℝ} {G j : ℕ} {b : Fin G → Bool}
    (hL : 1 < L) (hG : 0 < G) (hγ1 : γ ≤ 1) (hQ : 0 < Q_step)
    {f : activeSet b → ℕ} (hf : f ∈ tupleSet L Q_step G j b) (N d₀ : ℕ) :
    let S := Sblock L γ Q_step j
    let Lsum : ℝ := ∑ p ∈ S, (1 : ℝ) / (p : ℝ)
    |(((Icc 1 N).filter (inSubCell L γ Q_step G j b f)).card : ℝ) -
      (N : ℝ) * ((1 : ℝ) / (prodD f : ℝ)) * ∏ p ∈ S, (1 - (1 : ℝ) / (p : ℝ))| ≤
    (N : ℝ) * ((1 : ℝ) / (prodD f : ℝ)) * (∑ k ∈ Icc (2 * d₀ + 1) S.card, Lsum ^ k / (Nat.factorial k : ℝ)) +
      1 + ∑ k ∈ range (2 * d₀ + 2), (S.card : ℝ) ^ k := by
  intro S Lsum
  obtain ⟨_, _, _, hDpos⟩ := tupleSet_props hL hG hγ1 hQ hf
  have hSprime : ∀ p ∈ S, p.Prime := fun p hp => (mem_filter.mp hp).2
  set D := prodD f
  have hbij : ((Icc 1 N).filter (inSubCell L γ Q_step G j b f)).card =
      ((Icc 1 (N / D)).filter (fun m => ∀ p ∈ S, ¬p ∣ m)).card := by
    symm
    refine card_bij (fun m _ => D * m) ?_ ?_ ?_
    · intro m hm
      simp only [mem_filter, mem_Icc] at hm ⊢
      refine ⟨⟨Nat.mul_pos hDpos hm.1.1, by
        rw [mul_comm]; exact (Nat.le_div_iff_mul_le hDpos).mp hm.1.2⟩,
        dvd_mul_right D m, by rw [Nat.mul_div_cancel_left m hDpos]; exact hm.2⟩
    · intro m₁ _ m₂ _ h; exact mul_left_cancel₀ hDpos.ne' h
    · intro n hn
      rcases mem_filter.mp hn with ⟨hnIcc, hdvd, hcop⟩
      rcases mem_Icc.mp hnIcc with ⟨hn1, hnN⟩
      refine ⟨n / D, ?_, Nat.mul_div_cancel' hdvd⟩
      simp only [mem_filter, mem_Icc]
      exact ⟨⟨Nat.div_pos (Nat.le_of_dvd hn1 hdvd) hDpos, Nat.div_le_div_right hnN⟩, hcop⟩
  rw [hbij]
  have hbonf := coprime_count_bonferroni S hSprime (N / D) d₀
  have hDposR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hDpos
  have hdiv_le : ((N / D : ℕ) : ℝ) ≤ (N : ℝ) * ((1 : ℝ) / (D : ℝ)) := by
    rw [mul_one_div, le_div_iff₀ hDposR]; exact_mod_cast Nat.div_mul_le_self N D
  have hdiv_diff : |(N : ℝ) * ((1 : ℝ) / (D : ℝ)) - ((N / D : ℕ) : ℝ)| ≤ 1 := by
    rw [mul_one_div, abs_le]; constructor
    · linarith [show ((N / D : ℕ) : ℝ) ≤ (N : ℝ) / (D : ℝ) by rw [le_div_iff₀ hDposR]; exact_mod_cast Nat.div_mul_le_self N D]
    · have h1 : N < (N / D + 1) * D := by
        have := Nat.div_add_mod N D; have := Nat.mod_lt N hDpos; nlinarith
      have h2 : (N : ℝ) < (((N / D : ℕ) : ℝ) + 1) * (D : ℝ) := by exact_mod_cast h1
      have h3 : (N : ℝ) / (D : ℝ) < ((N / D : ℕ) : ℝ) + 1 := (div_lt_iff₀ hDposR).mpr h2
      linarith
  have hW_bd : 0 ≤ ∏ p ∈ S, (1 - (1 : ℝ) / (p : ℝ)) ∧ ∏ p ∈ S, (1 - (1 : ℝ) / (p : ℝ)) ≤ 1 := by
    constructor
    · refine prod_nonneg fun p hp => ?_
      have hp2 := (hSprime p hp).two_le
      have : (1 : ℝ) / (p : ℝ) ≤ 1 := by rw [div_le_one (by positivity)]; exact_mod_cast (by omega : 1 ≤ p)
      linarith
    · refine prod_le_one (fun p hp => ?_) (fun p _ => by
        have : 0 ≤ (1 : ℝ) / (p : ℝ) := by positivity
        linarith)
      have hp2 := (hSprime p hp).two_le
      have : (1 : ℝ) / (p : ℝ) ≤ 1 := by rw [div_le_one (by positivity)]; exact_mod_cast (by omega : 1 ≤ p)
      linarith
  have htail_nn : 0 ≤ ∑ k ∈ Icc (2 * d₀ + 1) S.card, Lsum ^ k / (Nat.factorial k : ℝ) :=
    sum_nonneg fun k _ => by
      have : 0 ≤ Lsum := sum_nonneg fun _ _ => by positivity
      positivity
  have htri := abs_sub_le
    (((Icc 1 (N / D)).filter (fun m => ∀ p ∈ S, ¬p ∣ m)).card : ℝ)
    (((N / D : ℕ) : ℝ) * ∏ p ∈ S, (1 - (1 : ℝ) / (p : ℝ)))
    ((N : ℝ) * ((1 : ℝ) / (D : ℝ)) * ∏ p ∈ S, (1 - (1 : ℝ) / (p : ℝ)))
  have hdiffW : |((N / D : ℕ) : ℝ) * ∏ p ∈ S, (1 - (1 : ℝ) / (p : ℝ)) -
      (N : ℝ) * ((1 : ℝ) / (D : ℝ)) * ∏ p ∈ S, (1 - (1 : ℝ) / (p : ℝ))| ≤ 1 := by
    rw [← sub_mul, abs_mul, abs_of_nonneg hW_bd.1, abs_sub_comm]
    calc _ ≤ 1 * 1 := mul_le_mul hdiv_diff hW_bd.2 hW_bd.1 (by norm_num)
      _ = 1 := mul_one 1
  have hmul_tail : ((N / D : ℕ) : ℝ) * (∑ k ∈ Icc (2 * d₀ + 1) S.card, Lsum ^ k / (Nat.factorial k : ℝ)) ≤
      (N : ℝ) * ((1 : ℝ) / (D : ℝ)) * (∑ k ∈ Icc (2 * d₀ + 1) S.card, Lsum ^ k / (Nat.factorial k : ℝ)) :=
    mul_le_mul_of_nonneg_right hdiv_le htail_nn
  linarith

/-- Exact Bonferroni upper bound for a pair of subcells in distinct blocks `j₁ ≠ j₂`. -/
lemma subCell_pair_count_bonferroni {L γ Q_step : ℝ} {G j₁ j₂ : ℕ}
    {b₁ b₂ : Fin G → Bool}
    (hL : 1 < L) (hG : 0 < G) (hγpos : 0 < γ) (hγ1 : γ ≤ 1) (hQ : Q_step = 2 * L / γ)
    (hne : j₁ ≠ j₂)
    {f₁ : activeSet b₁ → ℕ} {f₂ : activeSet b₂ → ℕ}
    (hf₁ : f₁ ∈ tupleSet L Q_step G j₁ b₁) (hf₂ : f₂ ∈ tupleSet L Q_step G j₂ b₂)
    (N d₀ : ℕ) :
    let S₁ := Sblock L γ Q_step j₁
    let S₂ := Sblock L γ Q_step j₂
    let S := S₁ ∪ S₂
    let Lsum : ℝ := ∑ p ∈ S, (1 : ℝ) / (p : ℝ)
    (((Icc 1 N).filter (fun n => inSubCell L γ Q_step G j₁ b₁ f₁ n ∧
        inSubCell L γ Q_step G j₂ b₂ f₂ n)).card : ℝ) ≤
      (N : ℝ) * ((1 : ℝ) / (prodD f₁ : ℝ)) * ((1 : ℝ) / (prodD f₂ : ℝ)) *
        ((∏ p ∈ S₁, (1 - (1 : ℝ) / (p : ℝ))) * (∏ p ∈ S₂, (1 - (1 : ℝ) / (p : ℝ))) +
          ∑ k ∈ Icc (2 * d₀ + 1) S.card, Lsum ^ k / (Nat.factorial k : ℝ)) +
      ∑ k ∈ range (2 * d₀ + 2), (S.card : ℝ) ^ k := by
  intro S₁ S₂ S Lsum
  have hQpos : 0 < Q_step := by rw [hQ]; positivity
  obtain ⟨hp₁, hS₁, _, hD₁pos⟩ := tupleSet_props hL hG hγ1 hQpos hf₁
  obtain ⟨hp₂, hS₂, _, hD₂pos⟩ := tupleSet_props hL hG hγ1 hQpos hf₂
  have hdisjS : Disjoint S₁ S₂ := Sblock_disjoint hγpos hQ hL hγ1 hne
  have hSprime : ∀ p ∈ S, p.Prime := fun p hp => by
    rcases mem_union.mp hp with h | h <;> exact (mem_filter.mp h).2
  set D₁ := prodD f₁
  set D₂ := prodD f₂
  have hcopD : Nat.Coprime D₁ D₂ := by
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne'
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hne'
    have h1 : p ∣ prodSub f₁ (activeSet b₁) := by
      have heq : prodSub f₁ (activeSet b₁) = D₁ := by unfold prodSub D₁ prodD; exact prod_congr rfl fun r _ => if_pos r.2
      rw [heq]; exact dvd_trans hpg (Nat.gcd_dvd_left _ _)
    have h2 : p ∣ prodSub f₂ (activeSet b₂) := by
      have heq : prodSub f₂ (activeSet b₂) = D₂ := by unfold prodSub D₂ prodD; exact prod_congr rfl fun r _ => if_pos r.2
      rw [heq]; exact dvd_trans hpg (Nat.gcd_dvd_right _ _)
    obtain ⟨r₁, _, rfl⟩ := (prime_dvd_prodSub_iff hL hG hγ1 hQpos hf₁ (activeSet b₁) hp).mp h1
    obtain ⟨r₂, _, hr₂⟩ := (prime_dvd_prodSub_iff hL hG hγ1 hQpos hf₂ (activeSet b₂) hp).mp h2
    exact disjoint_left.mp hdisjS (hS₁ r₁) (hr₂ ▸ hS₂ r₂)
  have hD₁_not_S₂ : ∀ p ∈ S₂, ¬p ∣ D₁ := fun p hpS₂ hdvd => by
    have hp := (mem_filter.mp hpS₂).2
    have h1 : p ∣ prodSub f₁ (activeSet b₁) := by
      have heq : prodSub f₁ (activeSet b₁) = D₁ := by unfold prodSub D₁ prodD; exact prod_congr rfl fun r _ => if_pos r.2
      rwa [heq]
    obtain ⟨r₁, _, rfl⟩ := (prime_dvd_prodSub_iff hL hG hγ1 hQpos hf₁ (activeSet b₁) hp).mp h1
    exact disjoint_left.mp hdisjS (hS₁ r₁) hpS₂
  have hD₂_not_S₁ : ∀ p ∈ S₁, ¬p ∣ D₂ := fun p hpS₁ hdvd => by
    have hp := (mem_filter.mp hpS₁).2
    have h2 : p ∣ prodSub f₂ (activeSet b₂) := by
      have heq : prodSub f₂ (activeSet b₂) = D₂ := by unfold prodSub D₂ prodD; exact prod_congr rfl fun r _ => if_pos r.2
      rwa [heq]
    obtain ⟨r₂, _, rfl⟩ := (prime_dvd_prodSub_iff hL hG hγ1 hQpos hf₂ (activeSet b₂) hp).mp h2
    exact disjoint_left.mp hdisjS hpS₁ (hS₂ r₂)
  have hDpos : 0 < D₁ * D₂ := Nat.mul_pos hD₁pos hD₂pos
  have hbij : ((Icc 1 N).filter (fun n => inSubCell L γ Q_step G j₁ b₁ f₁ n ∧
      inSubCell L γ Q_step G j₂ b₂ f₂ n)).card =
      ((Icc 1 (N / (D₁ * D₂))).filter (fun m => ∀ p ∈ S, ¬p ∣ m)).card := by
    symm
    refine card_bij (fun m _ => (D₁ * D₂) * m) ?_ ?_ ?_
    · intro m hm
      simp only [mem_filter, mem_Icc] at hm ⊢
      refine ⟨⟨Nat.mul_pos hDpos hm.1.1, by rw [mul_comm]; exact (Nat.le_div_iff_mul_le hDpos).mp hm.1.2⟩,
        ⟨dvd_mul_of_dvd_left (dvd_mul_right D₁ D₂) m, fun p hpS₁ hdvd => ?_⟩,
        ⟨dvd_mul_of_dvd_left (dvd_mul_left D₂ D₁) m, fun p hpS₂ hdvd => ?_⟩⟩
      · have hq : (D₁ * D₂) * m / D₁ = D₂ * m := by
          rw [mul_assoc, Nat.mul_div_cancel_left _ hD₁pos]
        rw [hq] at hdvd
        rcases (mem_filter.mp hpS₁).2.dvd_mul.mp hdvd with h | h
        · exact hD₂_not_S₁ p hpS₁ h
        · exact hm.2 p (mem_union_left _ hpS₁) h
      · have hq : (D₁ * D₂) * m / D₂ = D₁ * m := by
          rw [show (D₁ * D₂) * m = D₂ * (D₁ * m) by ring, Nat.mul_div_cancel_left _ hD₂pos]
        rw [hq] at hdvd
        rcases (mem_filter.mp hpS₂).2.dvd_mul.mp hdvd with h | h
        · exact hD₁_not_S₂ p hpS₂ h
        · exact hm.2 p (mem_union_right _ hpS₂) h
    · intro m₁ _ m₂ _ h; exact mul_left_cancel₀ hDpos.ne' h
    · intro n hn
      rcases mem_filter.mp hn with ⟨hnIcc, hsc1, hsc2⟩
      rcases mem_Icc.mp hnIcc with ⟨hn1, hnN⟩
      have hdvd12 : D₁ * D₂ ∣ n := hcopD.mul_dvd_of_dvd_of_dvd hsc1.1 hsc2.1
      refine ⟨n / (D₁ * D₂), ?_, Nat.mul_div_cancel' hdvd12⟩
      simp only [mem_filter, mem_Icc]
      refine ⟨⟨Nat.div_pos (Nat.le_of_dvd hn1 hdvd12) hDpos, Nat.div_le_div_right hnN⟩, fun p hpS hpm => ?_⟩
      rcases mem_union.mp hpS with hpS₁ | hpS₂
      · have hq : n / D₁ = D₂ * (n / (D₁ * D₂)) := by
          apply Nat.eq_of_mul_eq_mul_left hD₁pos
          rw [Nat.mul_div_cancel' hsc1.1, ← mul_assoc, Nat.mul_div_cancel' hdvd12]
        exact hsc1.2 p hpS₁ (hq ▸ dvd_mul_of_dvd_right hpm D₂)
      · have hq : n / D₂ = D₁ * (n / (D₁ * D₂)) := by
          apply Nat.eq_of_mul_eq_mul_left hD₂pos
          rw [Nat.mul_div_cancel' hsc2.1, show D₂ * (D₁ * (n / (D₁ * D₂))) = (D₁ * D₂) * (n / (D₁ * D₂)) by ring,
              Nat.mul_div_cancel' hdvd12]
        exact hsc2.2 p hpS₂ (hq ▸ dvd_mul_of_dvd_right hpm D₁)
  rw [hbij]
  have hbonf := (abs_le.mp (coprime_count_bonferroni S hSprime (N / (D₁ * D₂)) d₀)).2
  rw [prod_union hdisjS] at hbonf
  have hdiv_le : ((N / (D₁ * D₂) : ℕ) : ℝ) ≤ (N : ℝ) * ((1 : ℝ) / (D₁ : ℝ)) * ((1 : ℝ) / (D₂ : ℝ)) := by
    have hDposR : (0 : ℝ) < (D₁ : ℝ) * (D₂ : ℝ) := by positivity
    have h1 : ((N / (D₁ * D₂) : ℕ) : ℝ) ≤ (N : ℝ) / ((D₁ : ℝ) * (D₂ : ℝ)) := by
      rw [le_div_iff₀ hDposR]; exact_mod_cast Nat.div_mul_le_self N (D₁ * D₂)
    linarith [show (N : ℝ) / ((D₁ : ℝ) * (D₂ : ℝ)) = (N : ℝ) * ((1 : ℝ) / (D₁ : ℝ)) * ((1 : ℝ) / (D₂ : ℝ)) by ring]
  have hW_nn : 0 ≤ (∏ p ∈ S₁, (1 - (1 : ℝ) / (p : ℝ))) * (∏ p ∈ S₂, (1 - (1 : ℝ) / (p : ℝ))) := by
    refine mul_nonneg (prod_nonneg fun p hp => ?_) (prod_nonneg fun p hp => ?_)
    · have hp2 := (mem_filter.mp hp).2.two_le
      have : (1 : ℝ) / (p : ℝ) ≤ 1 := by rw [div_le_one (by positivity)]; exact_mod_cast (by omega : 1 ≤ p)
      linarith
    · have hp2 := (mem_filter.mp hp).2.two_le
      have : (1 : ℝ) / (p : ℝ) ≤ 1 := by rw [div_le_one (by positivity)]; exact_mod_cast (by omega : 1 ≤ p)
      linarith
  have htail_nn : 0 ≤ ∑ k ∈ Icc (2 * d₀ + 1) S.card, Lsum ^ k / (Nat.factorial k : ℝ) :=
    sum_nonneg fun k _ => by
      have : 0 ≤ Lsum := sum_nonneg fun _ _ => by positivity
      positivity
  have hmul := mul_le_mul_of_nonneg_right hdiv_le (add_nonneg hW_nn htail_nn)
  linarith [show ((N / (D₁ * D₂) : ℕ) : ℝ) * ((∏ p ∈ S₁, (1 - (1 : ℝ) / (p : ℝ))) *
        (∏ p ∈ S₂, (1 - (1 : ℝ) / (p : ℝ))) + ∑ k ∈ Icc (2 * d₀ + 1) S.card, Lsum ^ k / (Nat.factorial k : ℝ)) =
      ((N / (D₁ * D₂) : ℕ) : ℝ) * ((∏ p ∈ S₁, (1 - (1 : ℝ) / (p : ℝ))) * (∏ p ∈ S₂, (1 - (1 : ℝ) / (p : ℝ)))) +
      ((N / (D₁ * D₂) : ℕ) : ℝ) * (∑ k ∈ Icc (2 * d₀ + 1) S.card, Lsum ^ k / (Nat.factorial k : ℝ)) by ring]

/-- Smooth-part `A_j`-trimming upper bound for a single subcell `(j, b, f)` via Markov + Bonferroni. -/
lemma subCell_smooth_trim_bound {L γ β Q_step : ℝ} {G j : ℕ} {b : Fin G → Bool}
    (hL : 1 < L) (hG : 0 < G) (hγpos : 0 < γ) (hγ1 : γ ≤ 1) (hβpos : 0 < β) (hQ : 0 < Q_step)
    (hj1 : 1 ≤ loBlock γ Q_step j)
    {f : activeSet b → ℕ} (hf : f ∈ tupleSet L Q_step G j b) (N d₀ : ℕ) :
    let S := Sblock L γ Q_step j
    let K := loBlock γ Q_step j
    let Lsum : ℝ := ∑ p ∈ S, (1 : ℝ) / (p : ℝ)
    let W := ∏ p ∈ S, (1 - (1 : ℝ) / (p : ℝ))
    let tail := ∑ k ∈ Icc (2 * d₀ + 1) S.card, Lsum ^ k / (Nat.factorial k : ℝ)
    let Ebonf := ∑ k ∈ range (2 * d₀ + 2), (S.card : ℝ) ^ k
    (β * Q_step ^ j) *
      (((Icc 1 N).filter (fun n => inSubCell L γ Q_step G j b f n ∧
        exp (β * Q_step ^ j) < (smoothPart K n : ℝ))).card : ℝ) ≤
      (N : ℝ) * ((1 : ℝ) / (prodD f : ℝ)) * (W + tail) * (2 * log (K : ℝ) + 120) +
        (K : ℝ) * log (K : ℝ) * ((Nat.log 2 N + 1 : ℕ) : ℝ) * Ebonf := by
  intro S K Lsum W tail Ebonf
  obtain ⟨_, hS, _, hDpos⟩ := tupleSet_props hL hG hγ1 hQ hf
  have hSprime : ∀ p ∈ S, p.Prime := fun p hp => (mem_filter.mp hp).2
  set D := prodD f
  have hDposR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hDpos
  -- Step 1: Markov inequality on `log (smoothPart K n)`:
  have hmarkov : (β * Q_step ^ j) *
      (((Icc 1 N).filter (fun n => inSubCell L γ Q_step G j b f n ∧
        exp (β * Q_step ^ j) < (smoothPart K n : ℝ))).card : ℝ) ≤
      ∑ n ∈ (Icc 1 N).filter (inSubCell L γ Q_step G j b f), log (smoothPart K n : ℝ) := by
    have hsub : (Icc 1 N).filter (fun n => inSubCell L γ Q_step G j b f n ∧
        exp (β * Q_step ^ j) < (smoothPart K n : ℝ)) ⊆
        (Icc 1 N).filter (inSubCell L γ Q_step G j b f) := fun n hn => by
      simp only [mem_filter] at hn ⊢; exact ⟨hn.1, hn.2.1⟩
    calc (β * Q_step ^ j) * (((Icc 1 N).filter (fun n => inSubCell L γ Q_step G j b f n ∧
            exp (β * Q_step ^ j) < (smoothPart K n : ℝ))).card : ℝ)
        = ∑ _n ∈ (Icc 1 N).filter (fun n => inSubCell L γ Q_step G j b f n ∧
            exp (β * Q_step ^ j) < (smoothPart K n : ℝ)), (β * Q_step ^ j) := by
            rw [sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ n ∈ (Icc 1 N).filter (fun n => inSubCell L γ Q_step G j b f n ∧
            exp (β * Q_step ^ j) < (smoothPart K n : ℝ)), log (smoothPart K n : ℝ) := by
            refine sum_le_sum fun n hn => ?_
            have hlt := (mem_filter.mp hn).2.2
            have := log_lt_log (exp_pos _) hlt
            rw [log_exp] at this; exact this.le
      _ ≤ ∑ n ∈ (Icc 1 N).filter (inSubCell L γ Q_step G j b f), log (smoothPart K n : ℝ) :=
            sum_le_sum_of_subset_of_nonneg hsub fun n _ _ =>
              log_nonneg (by exact_mod_cast smoothPart_pos K n)
  -- Step 2: Expand `log (smoothPart K n)` and swap sums over `p ≤ K` and `a ∈ Icc 1 (Nat.log 2 N + 1)`:
  have hexpand : ∑ n ∈ (Icc 1 N).filter (inSubCell L γ Q_step G j b f), log (smoothPart K n : ℝ) =
      ∑ p ∈ (Icc 1 K).filter Nat.Prime, log (p : ℝ) *
        ∑ a ∈ Icc 1 (Nat.log 2 N + 1),
          (((Icc 1 N).filter (fun n => inSubCell L γ Q_step G j b f n ∧ p ^ a ∣ n)).card : ℝ) := by
    have hpt : ∀ n ∈ (Icc 1 N).filter (inSubCell L γ Q_step G j b f),
        log (smoothPart K n : ℝ) =
          ∑ p ∈ (Icc 1 K).filter Nat.Prime,
            ∑ a ∈ Icc 1 (Nat.log 2 N + 1), if p ^ a ∣ n then log (p : ℝ) else 0 := fun n hn => by
      have hn' := mem_Icc.mp (mem_filter.mp hn).1
      exact log_smoothPart_eq_sum_dvd hn'.1 hn'.2
    rw [sum_congr rfl hpt, sum_comm]
    refine sum_congr rfl fun p _ => ?_
    rw [sum_comm, mul_sum]
    refine sum_congr rfl fun a _ => ?_
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
    congr 1
    exact_mod_cast congrArg card (by ext n; simp only [mem_filter]; tauto)
  -- Step 3: For each `p ∈ (Icc 1 K).filter Nat.Prime` and `a ≥ 1`, count via `coprime_count_bonferroni`:
  have hpa_bound : ∀ p ∈ (Icc 1 K).filter Nat.Prime, ∀ a ∈ Icc 1 (Nat.log 2 N + 1),
      (((Icc 1 N).filter (fun n => inSubCell L γ Q_step G j b f n ∧ p ^ a ∣ n)).card : ℝ) ≤
        (N : ℝ) * ((1 : ℝ) / (D : ℝ)) * (W + tail) * ((1 : ℝ) / (p : ℝ)) ^ a + Ebonf := by
    intro p hp a ha
    have hpP : p.Prime := (mem_filter.mp hp).2
    have hpK : p ≤ K := (mem_Icc.mp (mem_filter.mp hp).1).2
    have hp_not_S : p ∉ S := fun h => by
      have hgt := (mem_Ioc.mp (mem_filter.mp h).1).1; omega
    have hcop_pD : Nat.Coprime (p ^ a) D := by
      refine Nat.Coprime.pow_left a ?_
      rw [hpP.coprime_iff_not_dvd]
      intro hdvd
      have h1 : p ∣ prodSub f (activeSet b) := by
        have heq : prodSub f (activeSet b) = D := by unfold prodSub D prodD; exact prod_congr rfl fun r _ => if_pos r.2
        rwa [heq]
      obtain ⟨r, _, rfl⟩ := (prime_dvd_prodSub_iff hL hG hγ1 hQ hf (activeSet b) hpP).mp h1
      exact hp_not_S (hS r)
    have hpa_pos : 0 < p ^ a := pow_pos hpP.pos a
    have hDpa_pos : 0 < D * p ^ a := Nat.mul_pos hDpos hpa_pos
    have hbij : ((Icc 1 N).filter (fun n => inSubCell L γ Q_step G j b f n ∧ p ^ a ∣ n)).card =
        ((Icc 1 (N / (D * p ^ a))).filter (fun m => ∀ q ∈ S, ¬q ∣ m)).card := by
      symm
      refine card_bij (fun m _ => (D * p ^ a) * m) ?_ ?_ ?_
      · intro m hm
        simp only [mem_filter, mem_Icc] at hm ⊢
        refine ⟨⟨Nat.mul_pos hDpa_pos hm.1.1, by rw [mul_comm]; exact (Nat.le_div_iff_mul_le hDpa_pos).mp hm.1.2⟩,
          ⟨dvd_mul_of_dvd_left (dvd_mul_right D _) m, fun q hqS hdvd => ?_⟩,
          dvd_mul_of_dvd_left (dvd_mul_left (p ^ a) D) m⟩
        have hqdiv : (D * p ^ a) * m / D = p ^ a * m := by
          rw [mul_assoc, Nat.mul_div_cancel_left _ hDpos]
        rw [hqdiv] at hdvd
        have hqP : q.Prime := hSprime q hqS
        rcases hqP.dvd_mul.mp hdvd with hqpa | hqm
        · have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hqP hpP).mp (hqP.dvd_of_dvd_pow hqpa)
          exact hp_not_S (hqp ▸ hqS)
        · exact hm.2 q hqS hqm
      · intro m₁ _ m₂ _ h; exact mul_left_cancel₀ hDpa_pos.ne' h
      · intro n hn
        rcases mem_filter.mp hn with ⟨hnIcc, hsc, hpa⟩
        rcases mem_Icc.mp hnIcc with ⟨hn1, hnN⟩
        have hdvd : D * p ^ a ∣ n := hcop_pD.symm.mul_dvd_of_dvd_of_dvd hsc.1 hpa
        refine ⟨n / (D * p ^ a), ?_, Nat.mul_div_cancel' hdvd⟩
        simp only [mem_filter, mem_Icc]
        refine ⟨⟨Nat.div_pos (Nat.le_of_dvd hn1 hdvd) hDpa_pos, Nat.div_le_div_right hnN⟩, fun q hqS hqm => ?_⟩
        have hqdiv : n / D = p ^ a * (n / (D * p ^ a)) := by
          apply Nat.eq_of_mul_eq_mul_left hDpos
          rw [Nat.mul_div_cancel' hsc.1, ← mul_assoc, Nat.mul_div_cancel' hdvd]
        exact hsc.2 q hqS (hqdiv ▸ dvd_mul_of_dvd_right hqm (p ^ a))
    rw [hbij]
    have hbonf := (abs_le.mp (coprime_count_bonferroni S hSprime (N / (D * p ^ a)) d₀)).2
    have hdiv_le : ((N / (D * p ^ a) : ℕ) : ℝ) ≤ (N : ℝ) * ((1 : ℝ) / (D : ℝ)) * ((1 : ℝ) / (p : ℝ)) ^ a := by
      have hppos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hpP.pos
      have hposR : (0 : ℝ) < (D : ℝ) * (p : ℝ) ^ a := by positivity
      have h1 : ((N / (D * p ^ a) : ℕ) : ℝ) ≤ (N : ℝ) / ((D : ℝ) * (p : ℝ) ^ a) := by
        rw [le_div_iff₀ hposR]; exact_mod_cast Nat.div_mul_le_self N (D * p ^ a)
      have h2 : (N : ℝ) / ((D : ℝ) * (p : ℝ) ^ a) = (N : ℝ) * ((1 : ℝ) / (D : ℝ)) * ((1 : ℝ) / (p : ℝ)) ^ a := by
        rw [one_div_pow]; ring
      linarith
    have hW_nn : 0 ≤ W := prod_nonneg fun q hq => by
      have hq2 := (hSprime q hq).two_le
      have : (1 : ℝ) / (q : ℝ) ≤ 1 := by rw [div_le_one (by positivity)]; exact_mod_cast (by omega : 1 ≤ q)
      linarith
    have htail_nn : 0 ≤ tail := sum_nonneg fun k _ => by
      have : 0 ≤ Lsum := sum_nonneg fun _ _ => by positivity
      positivity
    have hmul := mul_le_mul_of_nonneg_right hdiv_le (add_nonneg hW_nn htail_nn)
    linarith [show (N : ℝ) * ((1 : ℝ) / (D : ℝ)) * ((1 : ℝ) / (p : ℝ)) ^ a * (W + tail) =
        (N : ℝ) * ((1 : ℝ) / (D : ℝ)) * (W + tail) * ((1 : ℝ) / (p : ℝ)) ^ a by ring]
  -- Step 4: Sum `((1 / p)^a)` over `a ∈ Icc 1 (Nat.log 2 N + 1)` (≤ `1 / (p - 1)`), then sum over `p ≤ K`:
  have hgeom_p : ∀ p : ℕ, 2 ≤ p → ∀ M : ℕ,
      ∑ a ∈ Icc 1 M, ((1 : ℝ) / (p : ℝ)) ^ a ≤ 1 / ((p : ℝ) - 1) := by
    intro p hp2 M
    have hppos : (0 : ℝ) < (p : ℝ) := by positivity
    have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
      linarith
    have htel : ((p : ℝ) - 1) * ∑ a ∈ Icc 1 M, ((1 : ℝ) / (p : ℝ)) ^ a ≤ 1 := by
      induction M with
      | zero =>
        have : Icc 1 0 = ∅ := by ext k; simp only [mem_Icc, notMem_empty, iff_false]; omega
        rw [this, sum_empty, mul_zero]; norm_num
      | succ M _ =>
        -- Exact telescoping identity `((p - 1) * ∑_{a=1}^{M+1} p^{-a}) = 1 - p^{-(M+1)} ≤ 1`:
        have hid : ∀ m : ℕ, ((p : ℝ) - 1) * ∑ a ∈ Icc 1 m, ((1 : ℝ) / (p : ℝ)) ^ a =
            1 - ((1 : ℝ) / (p : ℝ)) ^ m := by
          intro m
          induction m with
          | zero =>
            have : Icc 1 0 = ∅ := by ext k; simp only [mem_Icc, notMem_empty, iff_false]; omega
            rw [this, sum_empty, mul_zero, pow_zero, sub_self]
          | succ m ihm =>
            have hIcc : Icc 1 (m + 1) = insert (m + 1) (Icc 1 m) := by
              ext k; simp only [mem_Icc, mem_insert]; omega
            rw [hIcc, sum_insert (by simp only [mem_Icc]; omega), mul_add, ihm, pow_succ]
            have h1 : ((p : ℝ) - 1) * ((1 : ℝ) / (p : ℝ)) = 1 - (1 : ℝ) / (p : ℝ) := by
              field_simp [hppos.ne']
            calc ((p : ℝ) - 1) * (((1 : ℝ) / (p : ℝ)) ^ m * ((1 : ℝ) / (p : ℝ))) + (1 - ((1 : ℝ) / (p : ℝ)) ^ m)
                = (((p : ℝ) - 1) * ((1 : ℝ) / (p : ℝ))) * ((1 : ℝ) / (p : ℝ)) ^ m + (1 - ((1 : ℝ) / (p : ℝ)) ^ m) := by ring
              _ = (1 - (1 : ℝ) / (p : ℝ)) * ((1 : ℝ) / (p : ℝ)) ^ m + (1 - ((1 : ℝ) / (p : ℝ)) ^ m) := by rw [h1]
              _ = 1 - ((1 : ℝ) / (p : ℝ)) ^ m * ((1 : ℝ) / (p : ℝ)) := by ring
        rw [hid (M + 1)]
        have : 0 ≤ ((1 : ℝ) / (p : ℝ)) ^ (M + 1) := by positivity
        linarith
    rw [le_div_iff₀ hpm1, mul_comm]; exact htel
  have hW_nn : 0 ≤ W := prod_nonneg fun q hq => by
    have hq2 := (hSprime q hq).two_le
    have : (1 : ℝ) / (q : ℝ) ≤ 1 := by rw [div_le_one (by positivity)]; exact_mod_cast (by omega : 1 ≤ q)
    linarith
  have htail_nn : 0 ≤ tail := sum_nonneg fun k _ => by
    have : 0 ≤ Lsum := sum_nonneg fun _ _ => by positivity
    positivity
  have hsum_bd : ∑ p ∈ (Icc 1 K).filter Nat.Prime, log (p : ℝ) *
      ∑ a ∈ Icc 1 (Nat.log 2 N + 1),
        (((Icc 1 N).filter (fun n => inSubCell L γ Q_step G j b f n ∧ p ^ a ∣ n)).card : ℝ) ≤
      (N : ℝ) * ((1 : ℝ) / (D : ℝ)) * (W + tail) * (2 * log (K : ℝ) + 120) +
        (K : ℝ) * log (K : ℝ) * ((Nat.log 2 N + 1 : ℕ) : ℝ) * Ebonf := by
    have h1 : ∀ p ∈ (Icc 1 K).filter Nat.Prime,
        log (p : ℝ) * ∑ a ∈ Icc 1 (Nat.log 2 N + 1),
          (((Icc 1 N).filter (fun n => inSubCell L γ Q_step G j b f n ∧ p ^ a ∣ n)).card : ℝ) ≤
        (N : ℝ) * ((1 : ℝ) / (D : ℝ)) * (W + tail) * (log (p : ℝ) / ((p : ℝ) - 1)) +
          log (K : ℝ) * ((Nat.log 2 N + 1 : ℕ) : ℝ) * Ebonf := by
      intro p hp
      have hpP : p.Prime := (mem_filter.mp hp).2
      have hpK : p ≤ K := (mem_Icc.mp (mem_filter.mp hp).1).2
      have hlogp_nn : 0 ≤ log (p : ℝ) := log_nonneg (by exact_mod_cast hpP.one_le)
      have hlogp_le : log (p : ℝ) ≤ log (K : ℝ) :=
        log_le_log (Nat.cast_pos.mpr hpP.pos) (by exact_mod_cast hpK)
      have hinner : ∑ a ∈ Icc 1 (Nat.log 2 N + 1),
            (((Icc 1 N).filter (fun n => inSubCell L γ Q_step G j b f n ∧ p ^ a ∣ n)).card : ℝ) ≤
          (N : ℝ) * ((1 : ℝ) / (D : ℝ)) * (W + tail) * (1 / ((p : ℝ) - 1)) +
            ((Nat.log 2 N + 1 : ℕ) : ℝ) * Ebonf := by
        calc _ ≤ ∑ a ∈ Icc 1 (Nat.log 2 N + 1),
                ((N : ℝ) * ((1 : ℝ) / (D : ℝ)) * (W + tail) * ((1 : ℝ) / (p : ℝ)) ^ a + Ebonf) :=
                sum_le_sum fun a ha => hpa_bound p hp a ha
          _ = (N : ℝ) * ((1 : ℝ) / (D : ℝ)) * (W + tail) * (∑ a ∈ Icc 1 (Nat.log 2 N + 1), ((1 : ℝ) / (p : ℝ)) ^ a) +
                ((Nat.log 2 N + 1 : ℕ) : ℝ) * Ebonf := by
                rw [sum_add_distrib, ← mul_sum, sum_const, Nat.card_Icc, nsmul_eq_mul]
                have : Nat.log 2 N + 1 + 1 - 1 = Nat.log 2 N + 1 := by omega
                rw [this]
          _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hgeom_p p hpP.two_le _)
                (mul_nonneg (by positivity : 0 ≤ (N : ℝ) * ((1 : ℝ) / (D : ℝ))) (add_nonneg hW_nn htail_nn))) le_rfl
      have hEbonf_nn : 0 ≤ Ebonf := sum_nonneg fun _ _ => by positivity
      calc log (p : ℝ) * _
          ≤ log (p : ℝ) * ((N : ℝ) * ((1 : ℝ) / (D : ℝ)) * (W + tail) * (1 / ((p : ℝ) - 1)) +
              ((Nat.log 2 N + 1 : ℕ) : ℝ) * Ebonf) := mul_le_mul_of_nonneg_left hinner hlogp_nn
        _ = (N : ℝ) * ((1 : ℝ) / (D : ℝ)) * (W + tail) * (log (p : ℝ) / ((p : ℝ) - 1)) +
              log (p : ℝ) * (((Nat.log 2 N + 1 : ℕ) : ℝ) * Ebonf) := by ring
        _ ≤ _ := add_le_add le_rfl (by
              have := mul_le_mul_of_nonneg_right hlogp_le (mul_nonneg (Nat.cast_nonneg (Nat.log 2 N + 1)) hEbonf_nn)
              linarith)
    have hcardK : (((Icc 1 K).filter Nat.Prime).card : ℝ) ≤ (K : ℝ) := by
      have hsub : ((Icc 1 K).filter Nat.Prime).card ≤ (Icc 1 K).card := card_filter_le _ _
      rw [Nat.card_Icc, Nat.add_sub_cancel] at hsub
      exact_mod_cast hsub
    have hEbonf_nn : 0 ≤ Ebonf := sum_nonneg fun _ _ => by positivity
    have hlogK_nn : 0 ≤ log (K : ℝ) := log_nonneg (by exact_mod_cast hj1)
    calc _ ≤ ∑ p ∈ (Icc 1 K).filter Nat.Prime,
            ((N : ℝ) * ((1 : ℝ) / (D : ℝ)) * (W + tail) * (log (p : ℝ) / ((p : ℝ) - 1)) +
              log (K : ℝ) * ((Nat.log 2 N + 1 : ℕ) : ℝ) * Ebonf) := sum_le_sum h1
      _ = (N : ℝ) * ((1 : ℝ) / (D : ℝ)) * (W + tail) *
            (∑ p ∈ (Icc 1 K).filter Nat.Prime, log (p : ℝ) / ((p : ℝ) - 1)) +
          (((Icc 1 K).filter Nat.Prime).card : ℝ) * (log (K : ℝ) * ((Nat.log 2 N + 1 : ℕ) : ℝ) * Ebonf) := by
            rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) * ((1 : ℝ) / (D : ℝ)) * (W + tail) * (2 * log (K : ℝ) + 120) +
            (K : ℝ) * log (K : ℝ) * ((Nat.log 2 N + 1 : ℕ) : ℝ) * Ebonf := by
            have ha := mul_le_mul_of_nonneg_left (sum_prime_log_div_sub_one K hj1)
              (mul_nonneg (by positivity : 0 ≤ (N : ℝ) * ((1 : ℝ) / (D : ℝ))) (add_nonneg hW_nn htail_nn))
            have hb := mul_le_mul_of_nonneg_right hcardK
              (mul_nonneg (mul_nonneg hlogK_nn (Nat.cast_nonneg (Nat.log 2 N + 1))) hEbonf_nn)
            linarith [show (K : ℝ) * (log (K : ℝ) * ((Nat.log 2 N + 1 : ℕ) : ℝ) * Ebonf) =
                (K : ℝ) * log (K : ℝ) * ((Nat.log 2 N + 1 : ℕ) : ℝ) * Ebonf by ring]
  linarith

/- ### Part 7F: Asymptotic Domination, Second Moment, and Main Proof -/

/-- Elementary exponential domination: for any `C_err ≥ 0`, `K_exp ≥ 1`, `δ > 0`,
for all sufficiently large `N`, `C_err * (log N + 2) * exp (K_exp * (log N)^(1/10)) ≤ δ * N`. -/
lemma exp_subpoly_dominated {C_err K_exp δ : ℝ} (hC : 0 ≤ C_err) (hK : 1 ≤ K_exp) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 100 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      C_err * (log (N : ℝ) + 2) * exp (K_exp * (log (N : ℝ)) ^ (1 / 10 : ℝ)) ≤
        δ * (N : ℝ) := by
  set X₀ : ℝ := max 100 (max ((4 * K_exp) ^ 2) (2 * log (max 1 (C_err / δ)) + 4))
  refine ⟨⌈exp X₀⌉₊ + 100, by omega, fun N hN => ?_⟩
  have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hX₀_le_N : exp X₀ ≤ (N : ℝ) := by
    have h1 := Nat.le_ceil (exp X₀)
    have h2 : (⌈exp X₀⌉₊ : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : ⌈exp X₀⌉₊ ≤ N)
    linarith
  set x : ℝ := log (N : ℝ)
  have hx_ge : X₀ ≤ x := by
    have := log_le_log (exp_pos X₀) hX₀_le_N
    rwa [log_exp] at this
  have hx100 : (100 : ℝ) ≤ x := le_trans (le_max_left _ _) hx_ge
  have hxK : (4 * K_exp) ^ 2 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx_ge
  have hxC : 2 * log (max 1 (C_err / δ)) + 4 ≤ x :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx_ge
  have hx_pos : 0 < x := by linarith
  have hK_bd : K_exp * x ^ (1 / 10 : ℝ) ≤ x / 4 := by
    have h1 : x ^ (1 / 10 : ℝ) ≤ x ^ (1 / 2 : ℝ) :=
      rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have h2 : 4 * K_exp ≤ x ^ (1 / 2 : ℝ) := by
      have hsq : ((4 * K_exp) ^ 2) ^ (1 / 2 : ℝ) ≤ x ^ (1 / 2 : ℝ) :=
        rpow_le_rpow (by positivity) hxK (by norm_num)
      have hrew : ((4 * K_exp) ^ 2) ^ (1 / 2 : ℝ) = 4 * K_exp := by
        rw [← rpow_natCast, ← rpow_mul (by positivity)]; norm_num
      linarith
    have hprod : (4 * K_exp) * x ^ (1 / 10 : ℝ) ≤ x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) :=
      mul_le_mul h2 h1 (rpow_nonneg hx_pos.le _) (rpow_nonneg hx_pos.le _)
    have hsqx : x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by
      rw [← rpow_add hx_pos]; norm_num
    linarith
  have hlin_bd : x + 2 ≤ exp (x / 4) := by
    have h1 : (1 + x / 8) ^ 2 ≤ (exp (x / 8)) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith [add_one_le_exp (x / 8)]) 2
    have h2 : (exp (x / 8)) ^ 2 = exp (x / 4) := by
      rw [← exp_nat_mul]; congr 1; ring
    nlinarith
  have hC_bd : C_err ≤ δ * exp (x / 2) := by
    have h1 : log (max 1 (C_err / δ)) ≤ x / 2 := by linarith
    have h2 : max 1 (C_err / δ) ≤ exp (x / 2) := by
      rw [← exp_log (lt_of_lt_of_le (by norm_num) (le_max_left 1 (C_err / δ)))]
      exact exp_le_exp.mpr h1
    have h3 : C_err / δ ≤ exp (x / 2) := le_trans (le_max_right _ _) h2
    rwa [div_le_iff₀ hδ, mul_comm] at h3
  have hexp_N : exp x = (N : ℝ) := exp_log hNpos
  calc C_err * (x + 2) * exp (K_exp * x ^ (1 / 10 : ℝ))
      ≤ C_err * exp (x / 4) * exp (x / 4) := by
          have h1 := mul_le_mul hlin_bd (exp_le_exp.mpr hK_bd) (exp_pos _).le (exp_pos _).le
          have := mul_le_mul_of_nonneg_left h1 hC
          linarith
    _ = C_err * exp (x / 2) := by rw [mul_assoc, ← exp_add]; congr 2; ring
    _ ≤ (δ * exp (x / 2)) * exp (x / 2) := mul_le_mul_of_nonneg_right hC_bd (exp_pos _).le
    _ = δ * exp x := by rw [mul_assoc, ← exp_add]; congr 2; ring
    _ = δ * (N : ℝ) := by rw [hexp_N]

/-- Crude upper bound on the Bonferroni error sum `∑_{k < 2 d₀ + 2} m^k`. -/
lemma bonf_range_sum_le {d₀ : ℕ} {R_sub m : ℝ} (hR : 1 ≤ R_sub) (hm0 : 0 ≤ m) (hmR : m ≤ 2 * R_sub) :
    ∑ k ∈ range (2 * d₀ + 2), m ^ k ≤ ((2 * d₀ + 2 : ℕ) : ℝ) * (2 * R_sub) ^ (2 * d₀ + 2) := by
  calc ∑ k ∈ range (2 * d₀ + 2), m ^ k
      ≤ ∑ _k ∈ range (2 * d₀ + 2), (2 * R_sub) ^ (2 * d₀ + 2) := sum_le_sum fun k hk => by
          have hklt := mem_range.mp hk
          calc m ^ k ≤ (2 * R_sub) ^ k := pow_le_pow_left₀ hm0 hmR k
            _ ≤ (2 * R_sub) ^ (2 * d₀ + 2) := pow_le_pow_right₀ (by linarith) (le_of_lt hklt)
    _ = ((2 * d₀ + 2 : ℕ) : ℝ) * (2 * R_sub) ^ (2 * d₀ + 2) := by
          rw [sum_const, card_range, nsmul_eq_mul]

/-- Single-block mean approximation for `Y_val` over `Icc 1 N`. -/
lemma block_Y_mean_approx {L γ Q_step η ε μ₀ S_max C_err1 K_exp1 δ_err R_sub : ℝ}
    {G j d₀ N : ℕ}
    (hL : exp 10000000000 ≤ L) (hG : 0 < G)
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    (hη : η = L ^ (-(1 / 40 : ℝ))) (hγ : γ = (ε / 400) * η) (hQ : Q_step = 2 * L / γ)
    (hfine : 40 * log L * L * gridDelta L G ≤ η) (hLε : 10000000 / ε ≤ L)
    (hμ₀ : μ₀ = γ * ∑ b : Fin G → Bool, bernProb (gridP L G) b * (cellScore L G η b : ℝ))
    (hμ₀_ge1 : 1 ≤ μ₀)
    (hS_max : S_max = ∑ b : Fin G → Bool, (cellScore L G η b : ℝ) + 1)
    (hCerr : C_err1 = 100 * S_max ^ 2 * ((2 * d₀ + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * d₀ + 2))
    (hKexp : K_exp1 = (2 * G + 2 * d₀ + 6 : ℝ))
    (hδerr : δ_err = (ε / 10000) * (γ / L) ^ 2)
    (hN100 : 100 ≤ N)
    (hR : R_sub = exp ((log (N : ℝ)) ^ (1 / 10 : ℝ)))
    (hj1 : 4 ≤ γ * Q_step ^ j) (hj2 : 330 / (γ * Q_step ^ j) ≤ ε / 20000)
    (hj3 : (2 / (loBlock γ Q_step j : ℝ)) * (log (L / γ) + 1) ≤ ε / 20000)
    (hj4 : 330 / Q_step ^ j ≤ (gridDelta L G) ^ 2)
    (hS_leR : ((Sblock L γ Q_step j).card : ℝ) ≤ R_sub)
    (htup_leR : ∀ b : Fin G → Bool, ((tupleSet L Q_step G j b).card : ℝ) ≤ R_sub ^ G)
    (hd₀_tail : ∀ (x : ℝ) (M : ℕ), 0 ≤ x → x ≤ 2 * (log (L / γ) + 1) →
      ∑ k ∈ Icc (2 * d₀ + 1) M, x ^ k / (Nat.factorial k : ℝ) ≤ δ_err)
    (hdom_N : C_err1 * (log (N : ℝ) + 2) * exp (K_exp1 * (log (N : ℝ)) ^ (1 / 10 : ℝ)) ≤ δ_err * (N : ℝ)) :
    (1 - ε / 200) * (N : ℝ) * μ₀ ≤ (∑ n ∈ Icc 1 N, Y_val L γ Q_step η G j n) ∧
    (∑ n ∈ Icc 1 N, Y_val L γ Q_step η G j n) ≤ (1 + ε / 200) * (N : ℝ) * μ₀ := by
  have hLpos : 0 < L := lt_of_lt_of_le (exp_pos _) hL
  have hlogL_ge : (10000000000 : ℝ) ≤ log L := by
    have := log_le_log (exp_pos _) hL; rwa [log_exp] at this
  have hL1 : 1 < L := (log_pos_iff hLpos.le).mp (by linarith)
  have hηpos : 0 < η := by rw [hη]; exact rpow_pos_of_pos hLpos _
  have hηle : η ≤ 1 / 10 := by
    rw [hη, rpow_def_of_pos hLpos]
    have h2 : exp (-10) ≤ 1 / 10 := by
      rw [exp_neg, one_div]; exact inv_anti₀ (by norm_num) (by linarith [add_one_le_exp (10 : ℝ)])
    exact le_trans (exp_le_exp.mpr (by linarith)) h2
  have hγpos : 0 < γ := by rw [hγ]; positivity
  have hγ1 : γ ≤ 1 := by
    rw [hγ]; have := mul_le_mul_of_nonneg_left hηle (by positivity : 0 ≤ ε / 400); linarith
  have hQpos : 0 < Q_step := by rw [hQ]; positivity
  have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hlogN_pos : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < N))
  have hR_ge1 : 1 ≤ R_sub := by rw [hR]; exact one_le_exp (rpow_nonneg hlogN_pos.le _)
  have hS1 : 1 ≤ S_max := by
    rw [hS_max]; linarith [sum_nonneg fun b (_ : b ∈ univ) => (Nat.cast_nonneg (cellScore L G η b) : (0 : ℝ) ≤ _)]
  have hbw := blockWeight_approx hL hG hε hεhalf hη hγ hQ hfine hLε hj1 hj2 hj3 hj4
  have hsum_eq : ∑ n ∈ Icc 1 N, Y_val L γ Q_step η G j n =
      ∑ b : Fin G → Bool, (cellScore L G η b : ℝ) *
        ∑ f ∈ tupleSet L Q_step G j b, (((Icc 1 N).filter (inSubCell L γ Q_step G j b f)).card : ℝ) := by
    unfold Y_val
    rw [sum_comm]
    refine sum_congr rfl fun b _ => ?_
    rw [sum_comm, mul_sum]
    refine sum_congr rfl fun f _ => ?_
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  set S := Sblock L γ Q_step j
  set Lsum : ℝ := ∑ p ∈ S, (1 : ℝ) / (p : ℝ)
  set W : ℝ := ∏ p ∈ S, (1 - (1 : ℝ) / (p : ℝ))
  have hlogLγ_nn : 0 ≤ log (L / γ) := log_nonneg (by rw [one_le_div hγpos]; linarith)
  have htail_le : ∑ k ∈ Icc (2 * d₀ + 1) S.card, Lsum ^ k / (Nat.factorial k : ℝ) ≤ δ_err :=
    hd₀_tail Lsum S.card (sum_nonneg fun _ _ => by positivity) (by linarith [hbw.2.1])
  have hγL_le1 : γ / L ≤ 1 := by rw [div_le_one hLpos]; linarith
  have htail_rel : ∑ k ∈ Icc (2 * d₀ + 1) S.card, Lsum ^ k / (Nat.factorial k : ℝ) ≤ (ε / 4000) * W := by
    have hsq : (γ / L) ^ 2 ≤ γ / L := by rw [sq]; exact mul_le_of_le_one_left (div_pos hγpos hLpos).le hγL_le1
    have hW_lo : (1 / 2 : ℝ) * (γ / L) ≤ W :=
      le_trans (mul_le_mul_of_nonneg_right (by linarith) (div_pos hγpos hLpos).le) hbw.1.1
    calc ∑ k ∈ Icc (2 * d₀ + 1) S.card, Lsum ^ k / (Nat.factorial k : ℝ)
        ≤ (ε / 10000) * (γ / L) ^ 2 := by rwa [← hδerr]
      _ ≤ (ε / 10000) * (γ / L) := mul_le_mul_of_nonneg_left hsq (by positivity)
      _ ≤ (ε / 8000) * (γ / L) := mul_le_mul_of_nonneg_right (by linarith) (div_pos hγpos hLpos).le
      _ = (ε / 4000) * ((1 / 2 : ℝ) * (γ / L)) := by ring
      _ ≤ (ε / 4000) * W := mul_le_mul_of_nonneg_left hW_lo (by positivity)
  have hdiff_le : |(∑ n ∈ Icc 1 N, Y_val L γ Q_step η G j n) -
      (N : ℝ) * ∑ b : Fin G → Bool, (cellScore L G η b : ℝ) * blockWeight L γ Q_step G j b| ≤
      (ε / 4000) * ((N : ℝ) * ∑ b : Fin G → Bool, (cellScore L G η b : ℝ) * blockWeight L γ Q_step G j b) +
      (ε / 10000) * (N : ℝ) * μ₀ := by
    rw [hsum_eq, mul_sum, ← sum_sub_distrib]
    have hE := bonf_range_sum_le (d₀ := d₀) hR_ge1 (Nat.cast_nonneg S.card) (by linarith)
    have hper_b : ∀ b : Fin G → Bool,
        |(cellScore L G η b : ℝ) * (∑ f ∈ tupleSet L Q_step G j b,
            (((Icc 1 N).filter (inSubCell L γ Q_step G j b f)).card : ℝ)) -
          (N : ℝ) * ((cellScore L G η b : ℝ) * blockWeight L γ Q_step G j b)| ≤
        (ε / 4000) * ((N : ℝ) * ((cellScore L G η b : ℝ) * blockWeight L γ Q_step G j b)) +
        (cellScore L G η b : ℝ) * R_sub ^ G * (1 + ((2 * d₀ + 2 : ℕ) : ℝ) * (2 * R_sub) ^ (2 * d₀ + 2)) := by
      intro b
      unfold blockWeight
      have hrew : (cellScore L G η b : ℝ) * (∑ f ∈ tupleSet L Q_step G j b,
            (((Icc 1 N).filter (inSubCell L γ Q_step G j b f)).card : ℝ)) -
          (N : ℝ) * ((cellScore L G η b : ℝ) * (W * ∑ f ∈ tupleSet L Q_step G j b, (1 : ℝ) / (prodD f : ℝ))) =
          (cellScore L G η b : ℝ) * ∑ f ∈ tupleSet L Q_step G j b,
            ((((Icc 1 N).filter (inSubCell L γ Q_step G j b f)).card : ℝ) -
              (N : ℝ) * ((1 : ℝ) / (prodD f : ℝ)) * W) := by
        rw [sum_sub_distrib, mul_sub]; congr 1
        simp_rw [mul_sum]
        refine sum_congr rfl fun f _ => by ring
      rw [hrew, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      have hsum_f : |∑ f ∈ tupleSet L Q_step G j b,
            ((((Icc 1 N).filter (inSubCell L γ Q_step G j b f)).card : ℝ) -
              (N : ℝ) * ((1 : ℝ) / (prodD f : ℝ)) * W)| ≤
          (ε / 4000) * ((N : ℝ) * (W * ∑ f ∈ tupleSet L Q_step G j b, (1 : ℝ) / (prodD f : ℝ))) +
            R_sub ^ G * (1 + ((2 * d₀ + 2 : ℕ) : ℝ) * (2 * R_sub) ^ (2 * d₀ + 2)) := by
        calc _ ≤ ∑ f ∈ tupleSet L Q_step G j b,
              |(((Icc 1 N).filter (inSubCell L γ Q_step G j b f)).card : ℝ) -
                (N : ℝ) * ((1 : ℝ) / (prodD f : ℝ)) * W| := abs_sum_le_sum_abs _ _
          _ ≤ ∑ f ∈ tupleSet L Q_step G j b,
              ((N : ℝ) * ((1 : ℝ) / (prodD f : ℝ)) * ((ε / 4000) * W) +
                (1 + ((2 * d₀ + 2 : ℕ) : ℝ) * (2 * R_sub) ^ (2 * d₀ + 2))) := by
                refine sum_le_sum fun f hf => ?_
                have hb1 := subCell_count_bonferroni hL1 hG hγ1 hQpos hf N d₀
                have h1 := mul_le_mul_of_nonneg_left htail_rel (by positivity : 0 ≤ (N : ℝ) * ((1 : ℝ) / (prodD f : ℝ)))
                linarith
          _ = (ε / 4000) * ((N : ℝ) * (W * ∑ f ∈ tupleSet L Q_step G j b, (1 : ℝ) / (prodD f : ℝ))) +
              ((tupleSet L Q_step G j b).card : ℝ) * (1 + ((2 * d₀ + 2 : ℕ) : ℝ) * (2 * R_sub) ^ (2 * d₀ + 2)) := by
                rw [sum_add_distrib, sum_const, nsmul_eq_mul]
                simp_rw [mul_sum]
                congr 1; refine sum_congr rfl fun f _ => by ring
          _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_right (htup_leR b)
                (by positivity : 0 ≤ 1 + ((2 * d₀ + 2 : ℕ) : ℝ) * (2 * R_sub) ^ (2 * d₀ + 2)))
      have hmul := mul_le_mul_of_nonneg_left hsum_f (Nat.cast_nonneg (cellScore L G η b))
      linarith
    have herr_dom : (∑ b : Fin G → Bool, (cellScore L G η b : ℝ) * R_sub ^ G *
          (1 + ((2 * d₀ + 2 : ℕ) : ℝ) * (2 * R_sub) ^ (2 * d₀ + 2))) ≤ (ε / 10000) * (N : ℝ) * μ₀ := by
      have h1 : (∑ b : Fin G → Bool, (cellScore L G η b : ℝ) * R_sub ^ G *
          (1 + ((2 * d₀ + 2 : ℕ) : ℝ) * (2 * R_sub) ^ (2 * d₀ + 2))) ≤
          C_err1 * (log (N : ℝ) + 2) * exp (K_exp1 * (log (N : ℝ)) ^ (1 / 10 : ℝ)) := by
        rw [← sum_mul, ← sum_mul]
        have hS_le : ∑ b : Fin G → Bool, (cellScore L G η b : ℝ) ≤ S_max := by rw [hS_max]; linarith
        have h12 : 1 + ((2 * d₀ + 2 : ℕ) : ℝ) * (2 * R_sub) ^ (2 * d₀ + 2) ≤
            2 * ((2 * d₀ + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * d₀ + 2) * R_sub ^ (2 * d₀ + 2) := by
          rw [mul_pow]
          have hA : (1 : ℝ) ≤ ((2 * d₀ + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * d₀ + 2)
          have hB : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * d₀ + 2) := one_le_pow₀ (by norm_num)
          have hC : (1 : ℝ) ≤ R_sub ^ (2 * d₀ + 2) := one_le_pow₀ hR_ge1
          have hge1 : (1 : ℝ) ≤ ((2 * d₀ + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * d₀ + 2) * R_sub ^ (2 * d₀ + 2) :=
            one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hA hB) hC
          linarith
        have hR_exp : R_sub ^ G * R_sub ^ (2 * d₀ + 2) ≤ exp (K_exp1 * (log (N : ℝ)) ^ (1 / 10 : ℝ)) := by
          rw [← pow_add, hR, ← exp_nat_mul]
          apply exp_le_exp.mpr
          refine mul_le_mul_of_nonneg_right ?_ (rpow_nonneg hlogN_pos.le _)
          rw [hKexp]; push_cast; linarith
        have hlog2 : (1 : ℝ) ≤ log (N : ℝ) + 2 := by linarith
        have hS2 : S_max ≤ S_max ^ 2 := by rw [sq]; exact le_mul_of_one_le_left (by linarith) hS1
        calc _ ≤ S_max * R_sub ^ G * (2 * ((2 * d₀ + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * d₀ + 2) * R_sub ^ (2 * d₀ + 2)) :=
              mul_le_mul (mul_le_mul_of_nonneg_right hS_le (by positivity)) h12 (by positivity) (by positivity)
          _ = (2 * S_max * ((2 * d₀ + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * d₀ + 2)) * (R_sub ^ G * R_sub ^ (2 * d₀ + 2)) := by ring
          _ ≤ (C_err1 * (log (N : ℝ) + 2)) * exp (K_exp1 * (log (N : ℝ)) ^ (1 / 10 : ℝ)) := by
              refine mul_le_mul ?_ hR_exp (by positivity) (by rw [hCerr]; positivity)
              have hnn : 0 ≤ ((2 * d₀ + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * d₀ + 2) := by positivity
              have hA : 2 * S_max * ((2 * d₀ + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * d₀ + 2) ≤ C_err1 := by
                rw [hCerr]
                have h2s := mul_le_mul_of_nonneg_right (show 2 * S_max ≤ 100 * S_max ^ 2 by linarith) hnn
                linarith [show 2 * S_max * ((2 * d₀ + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * d₀ + 2) =
                    2 * S_max * (((2 * d₀ + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * d₀ + 2)) by ring,
                  show 100 * S_max ^ 2 * ((2 * d₀ + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * d₀ + 2) =
                    100 * S_max ^ 2 * (((2 * d₀ + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * d₀ + 2)) by ring]
              exact le_trans hA (le_mul_of_one_le_right (by rw [hCerr]; positivity) hlog2)
          _ = _ := by ring
      have hγL_sq_le : (γ / L) ^ 2 ≤ μ₀ := by
        have : (γ / L) ^ 2 ≤ 1 := by rw [sq]; exact mul_le_one₀ hγL_le1 (div_pos hγpos hLpos).le hγL_le1
        linarith
      have h2 : δ_err * (N : ℝ) ≤ (ε / 10000) * (N : ℝ) * μ₀ := by
        rw [hδerr]
        have := mul_le_mul_of_nonneg_left hγL_sq_le (by positivity : 0 ≤ (ε / 10000) * (N : ℝ))
        linarith
      linarith
    calc _ ≤ ∑ b : Fin G → Bool,
          |(cellScore L G η b : ℝ) * (∑ f ∈ tupleSet L Q_step G j b,
              (((Icc 1 N).filter (inSubCell L γ Q_step G j b f)).card : ℝ)) -
            (N : ℝ) * ((cellScore L G η b : ℝ) * blockWeight L γ Q_step G j b)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ b : Fin G → Bool,
          ((ε / 4000) * ((N : ℝ) * ((cellScore L G η b : ℝ) * blockWeight L γ Q_step G j b)) +
            (cellScore L G η b : ℝ) * R_sub ^ G * (1 + ((2 * d₀ + 2 : ℕ) : ℝ) * (2 * R_sub) ^ (2 * d₀ + 2))) :=
          sum_le_sum fun b _ => hper_b b
      _ = (ε / 4000) * ((N : ℝ) * ∑ b : Fin G → Bool, (cellScore L G η b : ℝ) * blockWeight L γ Q_step G j b) +
          ∑ b : Fin G → Bool, (cellScore L G η b : ℝ) * R_sub ^ G *
            (1 + ((2 * d₀ + 2 : ℕ) : ℝ) * (2 * R_sub) ^ (2 * d₀ + 2)) := by
          rw [sum_add_distrib, ← mul_sum, ← mul_sum]
      _ ≤ (ε / 4000) * ((N : ℝ) * ∑ b : Fin G → Bool, (cellScore L G η b : ℝ) * blockWeight L γ Q_step G j b) +
          (ε / 10000) * (N : ℝ) * μ₀ := add_le_add le_rfl herr_dom
      _ = _ := by rw [mul_sum]
  have hbw_sum : (1 - ε / 500) * μ₀ ≤ ∑ b : Fin G → Bool, (cellScore L G η b : ℝ) * blockWeight L γ Q_step G j b ∧
      ∑ b : Fin G → Bool, (cellScore L G η b : ℝ) * blockWeight L γ Q_step G j b ≤ (1 + ε / 500) * μ₀ := by
    have hrew : μ₀ = ∑ b : Fin G → Bool, (cellScore L G η b : ℝ) * (γ * bernProb (gridP L G) b) := by
      rw [hμ₀, mul_sum]; refine sum_congr rfl fun b _ => by ring
    rw [hrew, mul_sum, mul_sum]
    constructor <;> refine sum_le_sum fun b _ => ?_
    · by_cases ht : isTyp L G b
      · have := mul_le_mul_of_nonneg_left (hbw.2.2 b ht).1 (Nat.cast_nonneg (cellScore L G η b)); linarith
      · unfold cellScore; simp [ht]
    · by_cases ht : isTyp L G b
      · have := mul_le_mul_of_nonneg_left (hbw.2.2 b ht).2 (Nat.cast_nonneg (cellScore L G η b)); linarith
      · unfold cellScore; simp [ht]
  rw [abs_le] at hdiff_le
  have hNμ_nn : 0 ≤ (N : ℝ) * μ₀ := mul_nonneg hNpos.le (by linarith)
  have hNB_lo := mul_le_mul_of_nonneg_left hbw_sum.1 hNpos.le
  have hNB_hi := mul_le_mul_of_nonneg_left hbw_sum.2 hNpos.le
  have hε2 : ε ^ 2 ≤ ε := by rw [sq]; exact mul_le_of_le_one_left hε.le (by linarith)
  constructor
  · have hm1 := mul_le_mul_of_nonneg_left hNB_hi (by positivity : 0 ≤ ε / 4000)
    have hc : 1 - ε / 200 ≤ (1 - ε / 500) - (ε / 4000) * (1 + ε / 500) - ε / 10000 := by
      linarith [show (1 - ε / 500) - (ε / 4000) * (1 + ε / 500) - ε / 10000 =
        1 - (47 / 20000 : ℝ) * ε - ε ^ 2 / 2000000 by ring]
    have hcm := mul_le_mul_of_nonneg_right hc hNμ_nn
    linarith [show ((1 - ε / 500) - (ε / 4000) * (1 + ε / 500) - ε / 10000) * ((N : ℝ) * μ₀) =
        (N : ℝ) * ((1 - ε / 500) * μ₀) - (ε / 4000) * ((N : ℝ) * ((1 + ε / 500) * μ₀)) - (ε / 10000) * (N : ℝ) * μ₀ by ring]
  · have hm1 := mul_le_mul_of_nonneg_left hNB_hi (by positivity : 0 ≤ ε / 4000)
    have hc : (1 + ε / 500) + (ε / 4000) * (1 + ε / 500) + ε / 10000 ≤ 1 + ε / 200 := by
      linarith [show (1 + ε / 500) + (ε / 4000) * (1 + ε / 500) + ε / 10000 =
        1 + (47 / 20000 : ℝ) * ε + ε ^ 2 / 2000000 by ring]
    have hcm := mul_le_mul_of_nonneg_right hc hNμ_nn
    linarith [show ((1 + ε / 500) + (ε / 4000) * (1 + ε / 500) + ε / 10000) * ((N : ℝ) * μ₀) =
        (N : ℝ) * ((1 + ε / 500) * μ₀) + (ε / 4000) * ((N : ℝ) * ((1 + ε / 500) * μ₀)) + (ε / 10000) * (N : ℝ) * μ₀ by ring]

set_option maxHeartbeats 400000 in
/-- Single-block trimmed mean lower bound for `Z_val` over `Icc 1 N`. -/
lemma block_Z_mean_lower {L γ β Q_step η ε μ₀ S_max C_err1 K_exp1 δ_err R_sub : ℝ}
    {G j d₀ N : ℕ}
    (hL : exp 10000000000 ≤ L) (hG : 0 < G)
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    (hη : η = L ^ (-(1 / 40 : ℝ))) (hγ : γ = (ε / 400) * η) (hβ : β = η / 4) (hQ : Q_step = 2 * L / γ)
    (hfine : 40 * log L * L * gridDelta L G ≤ η) (hLε : 10000000 / ε ≤ L)
    (hμ₀ : μ₀ = γ * ∑ b : Fin G → Bool, bernProb (gridP L G) b * (cellScore L G η b : ℝ))
    (hμ₀_ge1 : 1 ≤ μ₀)
    (hS_max : S_max = ∑ b : Fin G → Bool, (cellScore L G η b : ℝ) + 1)
    (hCerr : C_err1 = 100 * S_max ^ 2 * ((2 * d₀ + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * d₀ + 2))
    (hKexp : K_exp1 = (2 * G + 2 * d₀ + 6 : ℝ))
    (hδerr : δ_err = (ε / 10000) * (γ / L) ^ 2)
    (hN100 : 100 ≤ N)
    (hR : R_sub = exp ((log (N : ℝ)) ^ (1 / 10 : ℝ)))
    (hj1 : 4 ≤ γ * Q_step ^ j) (hj2 : 330 / (γ * Q_step ^ j) ≤ ε / 20000)
    (hj3 : (2 / (loBlock γ Q_step j : ℝ)) * (log (L / γ) + 1) ≤ ε / 20000)
    (hj4 : 330 / Q_step ^ j ≤ (gridDelta L G) ^ 2)
    (hj5 : 120 / (β * Q_step ^ j) ≤ ε / 200) (hj6 : 1 ≤ loBlock γ Q_step j)
    (hS_leR : ((Sblock L γ Q_step j).card : ℝ) ≤ R_sub)
    (hlo_leR : (loBlock γ Q_step j : ℝ) ≤ R_sub)
    (htup_leR : ∀ b : Fin G → Bool, ((tupleSet L Q_step G j b).card : ℝ) ≤ R_sub ^ G)
    (hd₀_tail : ∀ (x : ℝ) (M : ℕ), 0 ≤ x → x ≤ 2 * (log (L / γ) + 1) →
      ∑ k ∈ Icc (2 * d₀ + 1) M, x ^ k / (Nat.factorial k : ℝ) ≤ δ_err)
    (hdom_N : C_err1 * (log (N : ℝ) + 2) * exp (K_exp1 * (log (N : ℝ)) ^ (1 / 10 : ℝ)) ≤ δ_err * (N : ℝ))
    (hY_lo : (1 - ε / 200) * (N : ℝ) * μ₀ ≤ ∑ n ∈ Icc 1 N, Y_val L γ Q_step η G j n) :
    (1 - (4 / 100 : ℝ) * ε) * (N : ℝ) * μ₀ ≤ ∑ n ∈ Icc 1 N, Z_val L γ β Q_step η G j n := by
  have hLpos : 0 < L := lt_of_lt_of_le (exp_pos _) hL
  have hlogL_ge : (10000000000 : ℝ) ≤ log L := by
    have := log_le_log (exp_pos _) hL; rwa [log_exp] at this
  have hL1 : 1 < L := (log_pos_iff hLpos.le).mp (by linarith)
  have hηpos : 0 < η := by rw [hη]; exact rpow_pos_of_pos hLpos _
  have hηle : η ≤ 1 / 10 := by
    rw [hη, rpow_def_of_pos hLpos]
    have h2 : exp (-10) ≤ 1 / 10 := by
      rw [exp_neg, one_div]; exact inv_anti₀ (by norm_num) (by linarith [add_one_le_exp (10 : ℝ)])
    exact le_trans (exp_le_exp.mpr (by linarith)) h2
  have hγpos : 0 < γ := by rw [hγ]; positivity
  have hγ1 : γ ≤ 1 := by
    rw [hγ]; have := mul_le_mul_of_nonneg_left hηle (by positivity : 0 ≤ ε / 400); linarith
  have hβpos : 0 < β := by rw [hβ]; positivity
  have hQpos : 0 < Q_step := by rw [hQ]; positivity
  have hQpow_pos : 0 < Q_step ^ j := pow_pos hQpos j
  have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hlogN_pos : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < N))
  have hR_ge1 : 1 ≤ R_sub := by rw [hR]; exact one_le_exp (rpow_nonneg hlogN_pos.le _)
  have hS1 : 1 ≤ S_max := by
    rw [hS_max]; linarith [sum_nonneg fun b (_ : b ∈ univ) => (Nat.cast_nonneg (cellScore L G η b) : (0 : ℝ) ≤ _)]
  have hbw := blockWeight_approx hL hG hε hεhalf hη hγ hQ hfine hLε hj1 hj2 hj3 hj4
  set S := Sblock L γ Q_step j
  set K := loBlock γ Q_step j
  set Lsum : ℝ := ∑ p ∈ S, (1 : ℝ) / (p : ℝ)
  set W := ∏ p ∈ S, (1 - (1 : ℝ) / (p : ℝ))
  set tail := ∑ k ∈ Icc (2 * d₀ + 1) S.card, Lsum ^ k / (Nat.factorial k : ℝ)
  have hγL_le1 : γ / L ≤ 1 := by rw [div_le_one hLpos]; linarith
  have hW_lo : (1 / 2 : ℝ) * (γ / L) ≤ W :=
    le_trans (mul_le_mul_of_nonneg_right (by linarith) (div_pos hγpos hLpos).le) hbw.1.1
  have hWnn : 0 ≤ W := le_trans (by positivity) hW_lo
  have hlogLγ_nn : 0 ≤ log (L / γ) := log_nonneg (by rw [one_le_div hγpos]; linarith)
  have htail_rel : tail ≤ (ε / 4000) * W := by
    have ht := hd₀_tail Lsum S.card (sum_nonneg fun _ _ => by positivity) (by linarith [hbw.2.1])
    have hsq : (γ / L) ^ 2 ≤ γ / L := by rw [sq]; exact mul_le_of_le_one_left (div_pos hγpos hLpos).le hγL_le1
    calc tail ≤ (ε / 10000) * (γ / L) ^ 2 := by rwa [← hδerr]
      _ ≤ (ε / 10000) * (γ / L) := mul_le_mul_of_nonneg_left hsq (by positivity)
      _ ≤ (ε / 8000) * (γ / L) := mul_le_mul_of_nonneg_right (by linarith) (div_pos hγpos hLpos).le
      _ = (ε / 4000) * ((1 / 2 : ℝ) * (γ / L)) := by ring
      _ ≤ (ε / 4000) * W := mul_le_mul_of_nonneg_left hW_lo (by positivity)
  have hβQ_ge1 : 1 ≤ β * Q_step ^ j := by
    have hγleβ : γ ≤ β := by
      rw [hγ, hβ]
      have := mul_le_mul_of_nonneg_right (by linarith : ε / 400 ≤ 1 / 4) hηpos.le
      linarith
    have := mul_le_mul_of_nonneg_right hγleβ hQpow_pos.le
    linarith
  have hKpos : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hj6)
  have hlogK_le : log (K : ℝ) ≤ γ * Q_step ^ j := by
    have h1 : (K : ℝ) ≤ exp (γ * Q_step ^ j) := Nat.floor_le (exp_pos _).le
    have := log_le_log hKpos h1
    rwa [log_exp] at this
  have hlogK_le_R : log (K : ℝ) ≤ R_sub := by
    have h1 : log (K : ℝ) ≤ (log (N : ℝ)) ^ (1 / 10 : ℝ) := by
      have hlo_exp : (K : ℝ) ≤ exp ((log (N : ℝ)) ^ (1 / 10 : ℝ)) := by rwa [← hR]
      have h2 := log_le_log hKpos hlo_exp
      rwa [log_exp] at h2
    rw [hR]; linarith [add_one_le_exp ((log (N : ℝ)) ^ (1 / 10 : ℝ))]
  have hlog2N : ((Nat.log 2 N + 1 : ℕ) : ℝ) ≤ 2 * log (N : ℝ) + 2 := by
    have h1 : (2 : ℝ) ^ Nat.log 2 N ≤ (N : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega : N ≠ 0)
    have h2 := log_le_log (by positivity) h1
    rw [log_pow] at h2
    have hlog2_ge : (1 / 2 : ℝ) ≤ log 2 := by
      have h := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
      rw [log_div (by norm_num) (by norm_num), log_one, zero_sub] at h; linarith
    have h3 : (1 / 2 : ℝ) * (Nat.log 2 N : ℝ) ≤ (Nat.log 2 N : ℝ) * log 2 := by
      have := mul_le_mul_of_nonneg_left hlog2_ge (Nat.cast_nonneg (Nat.log 2 N)); linarith
    push_cast; linarith
  have hratio : (2 * log (K : ℝ) + 120) / (β * Q_step ^ j) ≤ ε / 40 := by
    rw [add_div]
    have h1 : 2 * log (K : ℝ) / (β * Q_step ^ j) ≤ ε / 50 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have h2 : 100 * γ = ε * β := by rw [hγ, hβ]; ring
      have h3 := mul_le_mul_of_nonneg_left hlogK_le (by norm_num : (0 : ℝ) ≤ 100)
      linarith [show 100 * (γ * Q_step ^ j) = ε * (β * Q_step ^ j) by rw [← mul_assoc, h2, mul_assoc]]
    linarith
  have hdiff_eq : ∑ n ∈ Icc 1 N, (Y_val L γ Q_step η G j n - Z_val L γ β Q_step η G j n) =
      ∑ b : Fin G → Bool, (cellScore L G η b : ℝ) *
        ∑ f ∈ tupleSet L Q_step G j b,
          (((Icc 1 N).filter (fun n => inSubCell L γ Q_step G j b f n ∧
            exp (β * Q_step ^ j) < (smoothPart K n : ℝ))).card : ℝ) := by
    have hpt : ∀ n ∈ Icc 1 N, Y_val L γ Q_step η G j n - Z_val L γ β Q_step η G j n =
        ∑ b : Fin G → Bool, ∑ f ∈ tupleSet L Q_step G j b,
          if inSubCell L γ Q_step G j b f n ∧ exp (β * Q_step ^ j) < (smoothPart K n : ℝ) then
            (cellScore L G η b : ℝ) else 0 := fun n _ => by
      unfold Z_val Y_val
      by_cases hA : (smoothPart K n : ℝ) ≤ exp (β * Q_step ^ j)
      · rw [if_pos hA, sub_self]
        symm; refine sum_eq_zero fun b _ => sum_eq_zero fun f _ => if_neg (by intro h; linarith [h.2])
      · rw [if_neg hA, sub_zero]
        push Not at hA
        refine sum_congr rfl fun b _ => sum_congr rfl fun f _ => by
          by_cases hsc : inSubCell L γ Q_step G j b f n <;> simp [hsc, hA]
    rw [sum_congr rfl hpt, sum_comm]
    refine sum_congr rfl fun b _ => ?_
    rw [sum_comm, mul_sum]
    refine sum_congr rfl fun f _ => ?_
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  have hdiff_bd : ∑ n ∈ Icc 1 N, (Y_val L γ Q_step η G j n - Z_val L γ β Q_step η G j n) ≤
      (3 / 100 : ℝ) * ε * (N : ℝ) * μ₀ := by
    rw [hdiff_eq]
    have hE := bonf_range_sum_le (d₀ := d₀) hR_ge1 (Nat.cast_nonneg S.card) (by linarith)
    have hper_b : ∀ b : Fin G → Bool,
        (cellScore L G η b : ℝ) * (∑ f ∈ tupleSet L Q_step G j b,
          (((Icc 1 N).filter (fun n => inSubCell L γ Q_step G j b f n ∧
            exp (β * Q_step ^ j) < (smoothPart K n : ℝ))).card : ℝ)) ≤
        (ε / 35) * (N : ℝ) * ((cellScore L G η b : ℝ) * blockWeight L γ Q_step G j b) +
        (cellScore L G η b : ℝ) * R_sub ^ G *
          (R_sub * R_sub * (2 * log (N : ℝ) + 2) *
            (((2 * d₀ + 2 : ℕ) : ℝ) * (2 * R_sub) ^ (2 * d₀ + 2))) := by
      intro b
      have hsum_f : (∑ f ∈ tupleSet L Q_step G j b,
          (((Icc 1 N).filter (fun n => inSubCell L γ Q_step G j b f n ∧
            exp (β * Q_step ^ j) < (smoothPart K n : ℝ))).card : ℝ)) ≤
          (ε / 35) * (N : ℝ) * blockWeight L γ Q_step G j b +
          R_sub ^ G * (R_sub * R_sub * (2 * log (N : ℝ) + 2) *
            (((2 * d₀ + 2 : ℕ) : ℝ) * (2 * R_sub) ^ (2 * d₀ + 2))) := by
        have h1 : ∀ f ∈ tupleSet L Q_step G j b,
            (((Icc 1 N).filter (fun n => inSubCell L γ Q_step G j b f n ∧
              exp (β * Q_step ^ j) < (smoothPart K n : ℝ))).card : ℝ) ≤
            (ε / 35) * (N : ℝ) * ((1 : ℝ) / (prodD f : ℝ)) * W +
              R_sub * R_sub * (2 * log (N : ℝ) + 2) *
                (((2 * d₀ + 2 : ℕ) : ℝ) * (2 * R_sub) ^ (2 * d₀ + 2)) := by
          intro f hf
          have htr := subCell_smooth_trim_bound hL1 hG hγpos hγ1 hβpos hQpos hj6 hf N d₀
          have hdiv := div_le_div_of_nonneg_right htr (mul_pos hβpos hQpow_pos).le
          rw [mul_div_cancel_left₀ _ (mul_pos hβpos hQpow_pos).ne', add_div] at hdiv
          have hterm1 : (N : ℝ) * ((1 : ℝ) / (prodD f : ℝ)) * (W + tail) * (2 * log (K : ℝ) + 120) /
              (β * Q_step ^ j) ≤ (ε / 35) * (N : ℝ) * ((1 : ℝ) / (prodD f : ℝ)) * W := by
            rw [mul_div_assoc]
            have hWt : W + tail ≤ (1 + 1 / 8) * W := by
              have := mul_le_mul_of_nonneg_right (by linarith : ε / 4000 ≤ 1 / 8) hWnn; linarith
            have hm1 := mul_le_mul hWt hratio (by positivity) (by positivity)
            have hm2 := mul_le_mul_of_nonneg_left hm1 (by positivity : 0 ≤ (N : ℝ) * ((1 : ℝ) / (prodD f : ℝ)))
            have hm3 := mul_le_mul_of_nonneg_right (by norm_num : (9 / 320 : ℝ) ≤ 1 / 35) (mul_nonneg hε.le hWnn)
            have hm4 := mul_le_mul_of_nonneg_left hm3 (by positivity : 0 ≤ (N : ℝ) * ((1 : ℝ) / (prodD f : ℝ)))
            linarith [show (1 + 1 / 8 : ℝ) * W * (ε / 40) = (9 / 320 : ℝ) * (ε * W) by ring,
                      show (ε / 35) * (N : ℝ) * ((1 : ℝ) / (prodD f : ℝ)) * W =
                          (N : ℝ) * ((1 : ℝ) / (prodD f : ℝ)) * ((1 / 35 : ℝ) * (ε * W)) by ring]
          have hterm2 : (K : ℝ) * log (K : ℝ) * ((Nat.log 2 N + 1 : ℕ) : ℝ) *
              (∑ k ∈ range (2 * d₀ + 2), (S.card : ℝ) ^ k) / (β * Q_step ^ j) ≤
              R_sub * R_sub * (2 * log (N : ℝ) + 2) *
                (((2 * d₀ + 2 : ℕ) : ℝ) * (2 * R_sub) ^ (2 * d₀ + 2)) := by
            have hlogK_nn : 0 ≤ log (K : ℝ) := log_nonneg (by exact_mod_cast hj6)
            have hSsum_nn : 0 ≤ ∑ k ∈ range (2 * d₀ + 2), (S.card : ℝ) ^ k :=
              sum_nonneg fun _ _ => by positivity
            have hnum_nn : 0 ≤ (K : ℝ) * log (K : ℝ) * ((Nat.log 2 N + 1 : ℕ) : ℝ) *
                (∑ k ∈ range (2 * d₀ + 2), (S.card : ℝ) ^ k) :=
              mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hlogK_nn) (Nat.cast_nonneg _)) hSsum_nn
            have hnum : (K : ℝ) * log (K : ℝ) * ((Nat.log 2 N + 1 : ℕ) : ℝ) *
                (∑ k ∈ range (2 * d₀ + 2), (S.card : ℝ) ^ k) ≤
                R_sub * R_sub * (2 * log (N : ℝ) + 2) *
                  (((2 * d₀ + 2 : ℕ) : ℝ) * (2 * R_sub) ^ (2 * d₀ + 2)) := by
              have ha := mul_le_mul hlo_leR hlogK_le_R hlogK_nn (by linarith)
              have hb := mul_le_mul ha hlog2N (Nat.cast_nonneg _) (by positivity)
              exact mul_le_mul hb hE hSsum_nn (by positivity)
            exact le_trans (div_le_self hnum_nn hβQ_ge1) hnum
          linarith
        calc _ ≤ ∑ f ∈ tupleSet L Q_step G j b,
              ((ε / 35) * (N : ℝ) * ((1 : ℝ) / (prodD f : ℝ)) * W +
                R_sub * R_sub * (2 * log (N : ℝ) + 2) *
                  (((2 * d₀ + 2 : ℕ) : ℝ) * (2 * R_sub) ^ (2 * d₀ + 2))) := sum_le_sum h1
          _ = (ε / 35) * (N : ℝ) * blockWeight L γ Q_step G j b +
              ((tupleSet L Q_step G j b).card : ℝ) *
                (R_sub * R_sub * (2 * log (N : ℝ) + 2) *
                  (((2 * d₀ + 2 : ℕ) : ℝ) * (2 * R_sub) ^ (2 * d₀ + 2))) := by
              rw [sum_add_distrib, sum_const, nsmul_eq_mul]
              unfold blockWeight; simp_rw [mul_sum]
              congr 1; refine sum_congr rfl fun f _ => by ring
          _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_right (htup_leR b)
                (by positivity : 0 ≤ R_sub * R_sub * (2 * log (N : ℝ) + 2) *
                  (((2 * d₀ + 2 : ℕ) : ℝ) * (2 * R_sub) ^ (2 * d₀ + 2))))
      have := mul_le_mul_of_nonneg_left hsum_f (Nat.cast_nonneg (cellScore L G η b))
      linarith
    have hbw_sum_hi : ∑ b : Fin G → Bool, (cellScore L G η b : ℝ) * blockWeight L γ Q_step G j b ≤
        (1 + ε / 500) * μ₀ := by
      have hrew : μ₀ = ∑ b : Fin G → Bool, (cellScore L G η b : ℝ) * (γ * bernProb (gridP L G) b) := by
        rw [hμ₀, mul_sum]; refine sum_congr rfl fun b _ => by ring
      rw [hrew, mul_sum]
      refine sum_le_sum fun b _ => ?_
      by_cases ht : isTyp L G b
      · have := mul_le_mul_of_nonneg_left (hbw.2.2 b ht).2 (Nat.cast_nonneg (cellScore L G η b)); linarith
      · unfold cellScore; simp [ht]
    have herr_dom2 : (∑ b : Fin G → Bool, (cellScore L G η b : ℝ) * R_sub ^ G *
          (R_sub * R_sub * (2 * log (N : ℝ) + 2) *
            (((2 * d₀ + 2 : ℕ) : ℝ) * (2 * R_sub) ^ (2 * d₀ + 2)))) ≤ (ε / 10000) * (N : ℝ) * μ₀ := by
      have hrew : (∑ b : Fin G → Bool, (cellScore L G η b : ℝ) * R_sub ^ G *
          (R_sub * R_sub * (2 * log (N : ℝ) + 2) *
            (((2 * d₀ + 2 : ℕ) : ℝ) * (2 * R_sub) ^ (2 * d₀ + 2)))) =
          (∑ b : Fin G → Bool, (cellScore L G η b : ℝ)) *
            (((2 * d₀ + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * d₀ + 2)) *
            (2 * log (N : ℝ) + 2) * (R_sub ^ (G + 2 * d₀ + 4)) := by
        have h1 : ∀ b : Fin G → Bool,
            (cellScore L G η b : ℝ) * R_sub ^ G *
              (R_sub * R_sub * (2 * log (N : ℝ) + 2) *
                (((2 * d₀ + 2 : ℕ) : ℝ) * (2 * R_sub) ^ (2 * d₀ + 2))) =
            (cellScore L G η b : ℝ) *
              ((((2 * d₀ + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * d₀ + 2)) *
                (2 * log (N : ℝ) + 2) * (R_sub ^ (G + 2 * d₀ + 4))) := fun b => by
          rw [mul_pow, show G + 2 * d₀ + 4 = G + (2 * d₀ + 2) + 2 by omega, pow_add, pow_add, sq]; ring
        simp_rw [h1, ← sum_mul]; ring
      rw [hrew]
      have hS_le : ∑ b : Fin G → Bool, (cellScore L G η b : ℝ) ≤ S_max ^ 2 := by
        have hS0 : ∑ b : Fin G → Bool, (cellScore L G η b : ℝ) ≤ S_max := by rw [hS_max]; linarith
        have hS2 : S_max ≤ S_max ^ 2 := by rw [sq]; exact le_mul_of_one_le_left (by linarith) hS1
        linarith
      have hR_exp : R_sub ^ (G + 2 * d₀ + 4) ≤ exp (K_exp1 * (log (N : ℝ)) ^ (1 / 10 : ℝ)) := by
        rw [hR, ← exp_nat_mul]
        apply exp_le_exp.mpr
        refine mul_le_mul_of_nonneg_right ?_ (rpow_nonneg hlogN_pos.le _)
        rw [hKexp]; push_cast; linarith
      have h1 : (∑ b : Fin G → Bool, (cellScore L G η b : ℝ)) *
            (((2 * d₀ + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * d₀ + 2)) *
            (2 * log (N : ℝ) + 2) * R_sub ^ (G + 2 * d₀ + 4) ≤
          C_err1 * (log (N : ℝ) + 2) * exp (K_exp1 * (log (N : ℝ)) ^ (1 / 10 : ℝ)) := by
        have hcoef : (∑ b : Fin G → Bool, (cellScore L G η b : ℝ)) *
              (((2 * d₀ + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * d₀ + 2)) * (2 * log (N : ℝ) + 2) ≤
            C_err1 * (log (N : ℝ) + 2) := by
          rw [hCerr]
          have ha := mul_le_mul_of_nonneg_right hS_le (by positivity : 0 ≤ ((2 * d₀ + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * d₀ + 2))
          have hb : 2 * log (N : ℝ) + 2 ≤ 2 * (log (N : ℝ) + 2) := by linarith
          have hc := mul_le_mul ha hb (by positivity) (by positivity)
          have hpos_t : 0 ≤ S_max ^ 2 * ((2 * d₀ + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * d₀ + 2) * (log (N : ℝ) + 2) := by positivity
          linarith [show S_max ^ 2 * (((2 * d₀ + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * d₀ + 2)) * (2 * (log (N : ℝ) + 2)) =
            2 * (S_max ^ 2 * ((2 * d₀ + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * d₀ + 2) * (log (N : ℝ) + 2)) by ring,
            show 100 * S_max ^ 2 * ((2 * d₀ + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * d₀ + 2) * (log (N : ℝ) + 2) =
            100 * (S_max ^ 2 * ((2 * d₀ + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * d₀ + 2) * (log (N : ℝ) + 2)) by ring]
        exact mul_le_mul hcoef hR_exp (by positivity) (by rw [hCerr]; positivity)
      have hγL_sq_le : (γ / L) ^ 2 ≤ μ₀ := by
        have : (γ / L) ^ 2 ≤ 1 := by rw [sq]; exact mul_le_one₀ hγL_le1 (div_pos hγpos hLpos).le hγL_le1
        linarith
      have h2 : δ_err * (N : ℝ) ≤ (ε / 10000) * (N : ℝ) * μ₀ := by
        rw [hδerr]
        have := mul_le_mul_of_nonneg_left hγL_sq_le (by positivity : 0 ≤ (ε / 10000) * (N : ℝ))
        linarith
      linarith
    have hsum_tot := sum_le_sum fun b (_ : b ∈ univ) => hper_b b
    rw [sum_add_distrib, ← mul_sum] at hsum_tot
    have hm1 := mul_le_mul_of_nonneg_left hbw_sum_hi (by positivity : 0 ≤ (ε / 35) * (N : ℝ))
    have hε2 : ε ^ 2 ≤ ε := by rw [sq]; exact mul_le_of_le_one_left hε.le (by linarith)
    have hc : (ε / 35) * (1 + ε / 500) + ε / 10000 ≤ (3 / 100 : ℝ) * ε := by
      linarith [show (ε / 35) * (1 + ε / 500) + ε / 10000 =
        (2007 / 70000 : ℝ) * ε + (4 / 70000 : ℝ) * ε ^ 2 by ring]
    have hcm := mul_le_mul_of_nonneg_right hc (mul_nonneg hNpos.le (by linarith : 0 ≤ μ₀))
    linarith [show ((ε / 35) * (1 + ε / 500) + ε / 10000) * ((N : ℝ) * μ₀) =
        (ε / 35) * (N : ℝ) * ((1 + ε / 500) * μ₀) + (ε / 10000) * (N : ℝ) * μ₀ by ring,
      show ((3 / 100 : ℝ) * ε) * ((N : ℝ) * μ₀) = (3 / 100 : ℝ) * ε * (N : ℝ) * μ₀ by ring]
  rw [sum_sub_distrib] at hdiff_bd
  have hεNμ : 0 ≤ ε * (N : ℝ) * μ₀ := mul_nonneg (mul_nonneg hε.le hNpos.le) (by linarith)
  linarith [show (1 - ε / 200) * (N : ℝ) * μ₀ - (3 / 100 : ℝ) * ε * (N : ℝ) * μ₀ -
      (1 - (4 / 100 : ℝ) * ε) * (N : ℝ) * μ₀ = (1 / 200 : ℝ) * (ε * (N : ℝ) * μ₀) by ring]

/-- Off-diagonal two-block upper bound for `Y_val j₁ * Y_val j₂` (`j₁ ≠ j₂`) over `Icc 1 N`. -/
lemma block_Y_pair_upper {L γ Q_step η ε μ₀ S_max C_err1 K_exp1 δ_err R_sub : ℝ}
    {G j₁ j₂ d₀ N : ℕ}
    (hL : exp 10000000000 ≤ L) (hG : 0 < G)
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    (hη : η = L ^ (-(1 / 40 : ℝ))) (hγ : γ = (ε / 400) * η) (hQ : Q_step = 2 * L / γ)
    (hfine : 40 * log L * L * gridDelta L G ≤ η) (hLε : 10000000 / ε ≤ L)
    (hμ₀ : μ₀ = γ * ∑ b : Fin G → Bool, bernProb (gridP L G) b * (cellScore L G η b : ℝ))
    (hμ₀_ge1 : 1 ≤ μ₀)
    (hS_max : S_max = ∑ b : Fin G → Bool, (cellScore L G η b : ℝ) + 1)
    (hCerr : C_err1 = 100 * S_max ^ 2 * ((2 * d₀ + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * d₀ + 2))
    (hKexp : K_exp1 = (2 * G + 2 * d₀ + 6 : ℝ))
    (hδerr : δ_err = (ε / 10000) * (γ / L) ^ 2)
    (hN100 : 100 ≤ N)
    (hR : R_sub = exp ((log (N : ℝ)) ^ (1 / 10 : ℝ)))
    (hne : j₁ ≠ j₂)
    (hj₁1 : 4 ≤ γ * Q_step ^ j₁) (hj₁2 : 330 / (γ * Q_step ^ j₁) ≤ ε / 20000)
    (hj₁3 : (2 / (loBlock γ Q_step j₁ : ℝ)) * (log (L / γ) + 1) ≤ ε / 20000)
    (hj₁4 : 330 / Q_step ^ j₁ ≤ (gridDelta L G) ^ 2)
    (hj₂1 : 4 ≤ γ * Q_step ^ j₂) (hj₂2 : 330 / (γ * Q_step ^ j₂) ≤ ε / 20000)
    (hj₂3 : (2 / (loBlock γ Q_step j₂ : ℝ)) * (log (L / γ) + 1) ≤ ε / 20000)
    (hj₂4 : 330 / Q_step ^ j₂ ≤ (gridDelta L G) ^ 2)
    (hS₁_leR : ((Sblock L γ Q_step j₁).card : ℝ) ≤ R_sub)
    (hS₂_leR : ((Sblock L γ Q_step j₂).card : ℝ) ≤ R_sub)
    (htup₁_leR : ∀ b : Fin G → Bool, ((tupleSet L Q_step G j₁ b).card : ℝ) ≤ R_sub ^ G)
    (htup₂_leR : ∀ b : Fin G → Bool, ((tupleSet L Q_step G j₂ b).card : ℝ) ≤ R_sub ^ G)
    (hd₀_tail : ∀ (x : ℝ) (M : ℕ), 0 ≤ x → x ≤ 2 * (log (L / γ) + 1) →
      ∑ k ∈ Icc (2 * d₀ + 1) M, x ^ k / (Nat.factorial k : ℝ) ≤ δ_err)
    (hdom_N : C_err1 * (log (N : ℝ) + 2) * exp (K_exp1 * (log (N : ℝ)) ^ (1 / 10 : ℝ)) ≤ δ_err * (N : ℝ)) :
    ∑ n ∈ Icc 1 N, Y_val L γ Q_step η G j₁ n * Y_val L γ Q_step η G j₂ n ≤
      (1 + (1 / 100 : ℝ) * ε) * (N : ℝ) * μ₀ ^ 2 := by
  have hLpos : 0 < L := lt_of_lt_of_le (exp_pos _) hL
  have hlogL_ge : (10000000000 : ℝ) ≤ log L := by
    have := log_le_log (exp_pos _) hL; rwa [log_exp] at this
  have hL1 : 1 < L := (log_pos_iff hLpos.le).mp (by linarith)
  have hηpos : 0 < η := by rw [hη]; exact rpow_pos_of_pos hLpos _
  have hηle : η ≤ 1 / 10 := by
    rw [hη, rpow_def_of_pos hLpos]
    have h2 : exp (-10) ≤ 1 / 10 := by
      rw [exp_neg, one_div]; exact inv_anti₀ (by norm_num) (by linarith [add_one_le_exp (10 : ℝ)])
    exact le_trans (exp_le_exp.mpr (by linarith)) h2
  have hγpos : 0 < γ := by rw [hγ]; positivity
  have hγ1 : γ ≤ 1 := by
    rw [hγ]; have := mul_le_mul_of_nonneg_left hηle (by positivity : 0 ≤ ε / 400); linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hlogN_pos : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < N))
  have hR_ge1 : 1 ≤ R_sub := by rw [hR]; exact one_le_exp (rpow_nonneg hlogN_pos.le _)
  have hbw₁ := blockWeight_approx hL hG hε hεhalf hη hγ hQ hfine hLε hj₁1 hj₁2 hj₁3 hj₁4
  have hbw₂ := blockWeight_approx hL hG hε hεhalf hη hγ hQ hfine hLε hj₂1 hj₂2 hj₂3 hj₂4
  set S₁ := Sblock L γ Q_step j₁
  set S₂ := Sblock L γ Q_step j₂
  set S := S₁ ∪ S₂
  set W₁ := ∏ p ∈ S₁, (1 - (1 : ℝ) / (p : ℝ))
  set W₂ := ∏ p ∈ S₂, (1 - (1 : ℝ) / (p : ℝ))
  set Lsum : ℝ := ∑ p ∈ S, (1 : ℝ) / (p : ℝ)
  have hLsum_le : Lsum ≤ 2 * (log (L / γ) + 1) := by
    unfold Lsum S
    rw [sum_union (Sblock_disjoint hγpos hQ hL1 hγ1 hne)]
    linarith [hbw₁.2.1, hbw₂.2.1]
  have hW₁_lo : (1 / 2 : ℝ) * (γ / L) ≤ W₁ :=
    le_trans (mul_le_mul_of_nonneg_right (by linarith) (div_pos hγpos hLpos).le) hbw₁.1.1
  have hW₂_lo : (1 / 2 : ℝ) * (γ / L) ≤ W₂ :=
    le_trans (mul_le_mul_of_nonneg_right (by linarith) (div_pos hγpos hLpos).le) hbw₂.1.1
  have htail_rel : ∑ k ∈ Icc (2 * d₀ + 1) S.card, Lsum ^ k / (Nat.factorial k : ℝ) ≤
      (ε / 2000) * (W₁ * W₂) := by
    have ht := hd₀_tail Lsum S.card (sum_nonneg fun _ _ => by positivity) hLsum_le
    have hprod : (1 / 4 : ℝ) * (γ / L) ^ 2 ≤ W₁ * W₂ := by
      have hm := mul_le_mul hW₁_lo hW₂_lo (by positivity) (le_trans (by positivity) hW₁_lo)
      linarith [show (1 / 2 : ℝ) * (γ / L) * ((1 / 2 : ℝ) * (γ / L)) = (1 / 4 : ℝ) * (γ / L) ^ 2 by ring]
    calc ∑ k ∈ Icc (2 * d₀ + 1) S.card, Lsum ^ k / (Nat.factorial k : ℝ)
        ≤ (ε / 10000) * (γ / L) ^ 2 := by rwa [← hδerr]
      _ ≤ (ε / 8000) * (γ / L) ^ 2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
      _ = (ε / 2000) * ((1 / 4 : ℝ) * (γ / L) ^ 2) := by ring
      _ ≤ (ε / 2000) * (W₁ * W₂) := mul_le_mul_of_nonneg_left hprod (by positivity)
  have hS_card : (S.card : ℝ) ≤ 2 * R_sub := by
    have : (S.card : ℝ) ≤ (S₁.card : ℝ) + (S₂.card : ℝ) := by exact_mod_cast card_union_le S₁ S₂
    linarith
  have hE := bonf_range_sum_le (d₀ := d₀) hR_ge1 (Nat.cast_nonneg S.card) hS_card
  have hsum_eq : ∑ n ∈ Icc 1 N, Y_val L γ Q_step η G j₁ n * Y_val L γ Q_step η G j₂ n =
      ∑ b₁ : Fin G → Bool, ∑ b₂ : Fin G → Bool, (cellScore L G η b₁ : ℝ) * (cellScore L G η b₂ : ℝ) *
        ∑ f₁ ∈ tupleSet L Q_step G j₁ b₁, ∑ f₂ ∈ tupleSet L Q_step G j₂ b₂,
          (((Icc 1 N).filter (fun n => inSubCell L γ Q_step G j₁ b₁ f₁ n ∧
            inSubCell L γ Q_step G j₂ b₂ f₂ n)).card : ℝ) := by
    unfold Y_val
    have hpt : ∀ n ∈ Icc 1 N,
        (∑ b₁ : Fin G → Bool, ∑ f₁ ∈ tupleSet L Q_step G j₁ b₁,
            if inSubCell L γ Q_step G j₁ b₁ f₁ n then (cellScore L G η b₁ : ℝ) else 0) *
        (∑ b₂ : Fin G → Bool, ∑ f₂ ∈ tupleSet L Q_step G j₂ b₂,
            if inSubCell L γ Q_step G j₂ b₂ f₂ n then (cellScore L G η b₂ : ℝ) else 0) =
        ∑ b₁ : Fin G → Bool, ∑ b₂ : Fin G → Bool,
          ∑ f₁ ∈ tupleSet L Q_step G j₁ b₁, ∑ f₂ ∈ tupleSet L Q_step G j₂ b₂,
            if inSubCell L γ Q_step G j₁ b₁ f₁ n ∧ inSubCell L γ Q_step G j₂ b₂ f₂ n then
              (cellScore L G η b₁ : ℝ) * (cellScore L G η b₂ : ℝ) else 0 := fun n _ => by
      rw [sum_mul_sum]
      refine sum_congr rfl fun b₁ _ => sum_congr rfl fun b₂ _ => ?_
      rw [sum_mul_sum]
      refine sum_congr rfl fun f₁ _ => sum_congr rfl fun f₂ _ => by
        by_cases h1 : inSubCell L γ Q_step G j₁ b₁ f₁ n <;>
        by_cases h2 : inSubCell L γ Q_step G j₂ b₂ f₂ n <;> simp [h1, h2]
    rw [sum_congr rfl hpt, sum_comm]
    refine sum_congr rfl fun b₁ _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun b₂ _ => ?_
    rw [sum_comm, mul_sum]
    refine sum_congr rfl fun f₁ _ => ?_
    rw [sum_comm, mul_sum]
    refine sum_congr rfl fun f₂ _ => ?_
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  rw [hsum_eq]
  have hbw₁_hi : ∑ b₁ : Fin G → Bool, (cellScore L G η b₁ : ℝ) * blockWeight L γ Q_step G j₁ b₁ ≤ (1 + ε / 500) * μ₀ := by
    have hrew : μ₀ = ∑ b : Fin G → Bool, (cellScore L G η b : ℝ) * (γ * bernProb (gridP L G) b) := by
      rw [hμ₀, mul_sum]; refine sum_congr rfl fun b _ => by ring
    rw [hrew, mul_sum]
    refine sum_le_sum fun b _ => ?_
    by_cases ht : isTyp L G b
    · have := mul_le_mul_of_nonneg_left (hbw₁.2.2 b ht).2 (Nat.cast_nonneg (cellScore L G η b)); linarith
    · unfold cellScore; simp [ht]
  have hbw₂_hi : ∑ b₂ : Fin G → Bool, (cellScore L G η b₂ : ℝ) * blockWeight L γ Q_step G j₂ b₂ ≤ (1 + ε / 500) * μ₀ := by
    have hrew : μ₀ = ∑ b : Fin G → Bool, (cellScore L G η b : ℝ) * (γ * bernProb (gridP L G) b) := by
      rw [hμ₀, mul_sum]; refine sum_congr rfl fun b _ => by ring
    rw [hrew, mul_sum]
    refine sum_le_sum fun b _ => ?_
    by_cases ht : isTyp L G b
    · have := mul_le_mul_of_nonneg_left (hbw₂.2.2 b ht).2 (Nat.cast_nonneg (cellScore L G η b)); linarith
    · unfold cellScore; simp [ht]
  have hper_b12 : ∀ b₁ b₂ : Fin G → Bool,
      (cellScore L G η b₁ : ℝ) * (cellScore L G η b₂ : ℝ) *
        (∑ f₁ ∈ tupleSet L Q_step G j₁ b₁, ∑ f₂ ∈ tupleSet L Q_step G j₂ b₂,
          (((Icc 1 N).filter (fun n => inSubCell L γ Q_step G j₁ b₁ f₁ n ∧
            inSubCell L γ Q_step G j₂ b₂ f₂ n)).card : ℝ)) ≤
      (1 + ε / 2000) * (N : ℝ) *
        (((cellScore L G η b₁ : ℝ) * blockWeight L γ Q_step G j₁ b₁) *
          ((cellScore L G η b₂ : ℝ) * blockWeight L γ Q_step G j₂ b₂)) +
      (cellScore L G η b₁ : ℝ) * (cellScore L G η b₂ : ℝ) * R_sub ^ (2 * G) *
        (((2 * d₀ + 2 : ℕ) : ℝ) * (2 * R_sub) ^ (2 * d₀ + 2)) := by
    intro b₁ b₂
    have hsum_f : (∑ f₁ ∈ tupleSet L Q_step G j₁ b₁, ∑ f₂ ∈ tupleSet L Q_step G j₂ b₂,
          (((Icc 1 N).filter (fun n => inSubCell L γ Q_step G j₁ b₁ f₁ n ∧
            inSubCell L γ Q_step G j₂ b₂ f₂ n)).card : ℝ)) ≤
        (1 + ε / 2000) * (N : ℝ) * (blockWeight L γ Q_step G j₁ b₁ * blockWeight L γ Q_step G j₂ b₂) +
        R_sub ^ (2 * G) * (((2 * d₀ + 2 : ℕ) : ℝ) * (2 * R_sub) ^ (2 * d₀ + 2)) := by
      calc _ ≤ ∑ f₁ ∈ tupleSet L Q_step G j₁ b₁, ∑ f₂ ∈ tupleSet L Q_step G j₂ b₂,
            ((1 + ε / 2000) * (N : ℝ) * ((1 : ℝ) / (prodD f₁ : ℝ)) * ((1 : ℝ) / (prodD f₂ : ℝ)) * (W₁ * W₂) +
              (((2 * d₀ + 2 : ℕ) : ℝ) * (2 * R_sub) ^ (2 * d₀ + 2))) := by
              refine sum_le_sum fun f₁ hf₁ => sum_le_sum fun f₂ hf₂ => ?_
              have hp := subCell_pair_count_bonferroni hL1 hG hγpos hγ1 hQ hne hf₁ hf₂ N d₀
              have h1 := mul_le_mul_of_nonneg_left (show W₁ * W₂ + ∑ k ∈ Icc (2 * d₀ + 1) S.card, Lsum ^ k / (Nat.factorial k : ℝ) ≤
                  (1 + ε / 2000) * (W₁ * W₂) by linarith)
                (by positivity : 0 ≤ (N : ℝ) * ((1 : ℝ) / (prodD f₁ : ℝ)) * ((1 : ℝ) / (prodD f₂ : ℝ)))
              linarith
        _ = (1 + ε / 2000) * (N : ℝ) * (blockWeight L γ Q_step G j₁ b₁ * blockWeight L γ Q_step G j₂ b₂) +
            ((tupleSet L Q_step G j₁ b₁).card : ℝ) * ((tupleSet L Q_step G j₂ b₂).card : ℝ) *
              (((2 * d₀ + 2 : ℕ) : ℝ) * (2 * R_sub) ^ (2 * d₀ + 2)) := by
              simp_rw [sum_add_distrib, sum_const, nsmul_eq_mul]
              rw [← mul_assoc]
              congr 1
              unfold blockWeight
              have hprod_eq : (1 + ε / 2000) * (N : ℝ) *
                  ((W₁ * ∑ f₁ ∈ tupleSet L Q_step G j₁ b₁, (1 : ℝ) / (prodD f₁ : ℝ)) *
                    (W₂ * ∑ f₂ ∈ tupleSet L Q_step G j₂ b₂, (1 : ℝ) / (prodD f₂ : ℝ))) =
                  ((1 + ε / 2000) * (N : ℝ) * (W₁ * W₂)) *
                    ((∑ f₁ ∈ tupleSet L Q_step G j₁ b₁, (1 : ℝ) / (prodD f₁ : ℝ)) *
                      (∑ f₂ ∈ tupleSet L Q_step G j₂ b₂, (1 : ℝ) / (prodD f₂ : ℝ))) := by ring
              rw [hprod_eq, sum_mul_sum, mul_sum]
              refine sum_congr rfl fun f₁ _ => ?_
              rw [mul_sum]
              refine sum_congr rfl fun f₂ _ => by ring
        _ ≤ _ := by
              refine add_le_add le_rfl (mul_le_mul_of_nonneg_right ?_ (by positivity))
              have hprod := mul_le_mul (htup₁_leR b₁) (htup₂_leR b₂) (Nat.cast_nonneg _) (by positivity)
              rw [← pow_add, show G + G = 2 * G by omega] at hprod
              exact hprod
    have hmul := mul_le_mul_of_nonneg_left hsum_f
      (mul_nonneg (Nat.cast_nonneg (cellScore L G η b₁)) (Nat.cast_nonneg (cellScore L G η b₂)))
    linarith [show (cellScore L G η b₁ : ℝ) * (cellScore L G η b₂ : ℝ) *
        ((1 + ε / 2000) * (N : ℝ) * (blockWeight L γ Q_step G j₁ b₁ * blockWeight L γ Q_step G j₂ b₂) +
          R_sub ^ (2 * G) * (((2 * d₀ + 2 : ℕ) : ℝ) * (2 * R_sub) ^ (2 * d₀ + 2))) =
        (1 + ε / 2000) * (N : ℝ) *
          (((cellScore L G η b₁ : ℝ) * blockWeight L γ Q_step G j₁ b₁) *
            ((cellScore L G η b₂ : ℝ) * blockWeight L γ Q_step G j₂ b₂)) +
        (cellScore L G η b₁ : ℝ) * (cellScore L G η b₂ : ℝ) * R_sub ^ (2 * G) *
          (((2 * d₀ + 2 : ℕ) : ℝ) * (2 * R_sub) ^ (2 * d₀ + 2)) by ring]
  have herr_dom3 : (∑ b₁ : Fin G → Bool, ∑ b₂ : Fin G → Bool,
        (cellScore L G η b₁ : ℝ) * (cellScore L G η b₂ : ℝ) * R_sub ^ (2 * G) *
          (((2 * d₀ + 2 : ℕ) : ℝ) * (2 * R_sub) ^ (2 * d₀ + 2))) ≤ (ε / 10000) * (N : ℝ) * μ₀ ^ 2 := by
    have hrew : (∑ b₁ : Fin G → Bool, ∑ b₂ : Fin G → Bool,
          (cellScore L G η b₁ : ℝ) * (cellScore L G η b₂ : ℝ) * R_sub ^ (2 * G) *
            (((2 * d₀ + 2 : ℕ) : ℝ) * (2 * R_sub) ^ (2 * d₀ + 2))) =
        (∑ b : Fin G → Bool, (cellScore L G η b : ℝ)) ^ 2 *
          (((2 * d₀ + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * d₀ + 2)) * (R_sub ^ (2 * G) * R_sub ^ (2 * d₀ + 2)) := by
      have h1 : ∀ b₁ b₂ : Fin G → Bool,
          (cellScore L G η b₁ : ℝ) * (cellScore L G η b₂ : ℝ) * R_sub ^ (2 * G) *
            (((2 * d₀ + 2 : ℕ) : ℝ) * (2 * R_sub) ^ (2 * d₀ + 2)) =
          ((cellScore L G η b₁ : ℝ) * (cellScore L G η b₂ : ℝ)) *
            ((((2 * d₀ + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * d₀ + 2)) * (R_sub ^ (2 * G) * R_sub ^ (2 * d₀ + 2))) := fun _ _ => by
        rw [mul_pow]; ring
      simp_rw [h1, ← sum_mul]
      rw [← sum_mul_sum, ← sq]; ring
    rw [hrew]
    have hS_le : (∑ b : Fin G → Bool, (cellScore L G η b : ℝ)) ^ 2 ≤ S_max ^ 2 :=
      pow_le_pow_left₀ (sum_nonneg fun _ _ => Nat.cast_nonneg _) (by rw [hS_max]; linarith) 2
    have hR_exp : R_sub ^ (2 * G) * R_sub ^ (2 * d₀ + 2) ≤
        exp (K_exp1 * (log (N : ℝ)) ^ (1 / 10 : ℝ)) := by
      rw [← pow_add, hR, ← exp_nat_mul]
      apply exp_le_exp.mpr
      refine mul_le_mul_of_nonneg_right ?_ (rpow_nonneg hlogN_pos.le _)
      rw [hKexp]; push_cast; linarith
    have h1 : (∑ b : Fin G → Bool, (cellScore L G η b : ℝ)) ^ 2 *
          (((2 * d₀ + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * d₀ + 2)) * (R_sub ^ (2 * G) * R_sub ^ (2 * d₀ + 2)) ≤
        C_err1 * (log (N : ℝ) + 2) * exp (K_exp1 * (log (N : ℝ)) ^ (1 / 10 : ℝ)) := by
      have hcoef : (∑ b : Fin G → Bool, (cellScore L G η b : ℝ)) ^ 2 *
            (((2 * d₀ + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * d₀ + 2)) ≤ C_err1 * (log (N : ℝ) + 2) := by
        have hlog1 : (1 : ℝ) ≤ log (N : ℝ) + 2 := by linarith
        have ha := mul_le_mul_of_nonneg_right hS_le (by positivity : 0 ≤ ((2 * d₀ + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * d₀ + 2))
        have hA : (∑ b : Fin G → Bool, (cellScore L G η b : ℝ)) ^ 2 *
              (((2 * d₀ + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * d₀ + 2)) ≤ C_err1 := by
          rw [hCerr]
          have hpos_t : 0 ≤ S_max ^ 2 * (((2 * d₀ + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * d₀ + 2)) := by positivity
          linarith [show 100 * S_max ^ 2 * ((2 * d₀ + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * d₀ + 2) =
            100 * (S_max ^ 2 * (((2 * d₀ + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * d₀ + 2))) by ring]
        exact le_trans hA (le_mul_of_one_le_right (by rw [hCerr]; positivity) hlog1)
      exact mul_le_mul hcoef hR_exp (by positivity) (by rw [hCerr]; positivity)
    have hγL_le : (γ / L) ^ 2 ≤ μ₀ ^ 2 :=
      pow_le_pow_left₀ (by positivity) (le_trans (by rw [div_le_one hLpos]; linarith) hμ₀_ge1) 2
    have h2 : δ_err * (N : ℝ) ≤ (ε / 10000) * (N : ℝ) * μ₀ ^ 2 := by
      rw [hδerr]
      have := mul_le_mul_of_nonneg_left hγL_le (by positivity : 0 ≤ (ε / 10000) * (N : ℝ))
      linarith
    linarith
  calc _ ≤ ∑ b₁ : Fin G → Bool, ∑ b₂ : Fin G → Bool,
        ((1 + ε / 2000) * (N : ℝ) *
            (((cellScore L G η b₁ : ℝ) * blockWeight L γ Q_step G j₁ b₁) *
              ((cellScore L G η b₂ : ℝ) * blockWeight L γ Q_step G j₂ b₂)) +
          (cellScore L G η b₁ : ℝ) * (cellScore L G η b₂ : ℝ) * R_sub ^ (2 * G) *
            (((2 * d₀ + 2 : ℕ) : ℝ) * (2 * R_sub) ^ (2 * d₀ + 2))) :=
        sum_le_sum fun b₁ _ => sum_le_sum fun b₂ _ => hper_b12 b₁ b₂
    _ = (1 + ε / 2000) * (N : ℝ) *
          ((∑ b₁ : Fin G → Bool, (cellScore L G η b₁ : ℝ) * blockWeight L γ Q_step G j₁ b₁) *
            (∑ b₂ : Fin G → Bool, (cellScore L G η b₂ : ℝ) * blockWeight L γ Q_step G j₂ b₂)) +
        ∑ b₁ : Fin G → Bool, ∑ b₂ : Fin G → Bool,
          (cellScore L G η b₁ : ℝ) * (cellScore L G η b₂ : ℝ) * R_sub ^ (2 * G) *
            (((2 * d₀ + 2 : ℕ) : ℝ) * (2 * R_sub) ^ (2 * d₀ + 2)) := by
        simp_rw [sum_add_distrib]
        congr 1
        rw [sum_mul_sum, mul_sum]
        refine sum_congr rfl fun b₁ _ => by rw [mul_sum]
    _ ≤ (1 + ε / 2000) * (N : ℝ) * (((1 + ε / 500) * μ₀) * ((1 + ε / 500) * μ₀)) +
          (ε / 10000) * (N : ℝ) * μ₀ ^ 2 := by
        refine add_le_add ?_ herr_dom3
        refine mul_le_mul_of_nonneg_left (mul_le_mul hbw₁_hi hbw₂_hi ?_ (by positivity)) (by positivity)
        exact sum_nonneg fun b _ => mul_nonneg (Nat.cast_nonneg _)
          (mul_nonneg (le_trans (by positivity) hW₂_lo) (sum_nonneg fun _ _ => by positivity))
    _ ≤ (1 + (1 / 100 : ℝ) * ε) * (N : ℝ) * μ₀ ^ 2 := by
        have hε2 : ε ^ 2 ≤ ε := by rw [sq]; exact mul_le_of_le_one_left hε.le (by linarith)
        have hε3 : ε ^ 3 ≤ ε := by
          have : ε ^ 3 = ε * ε ^ 2 := by ring
          rw [this]; exact le_trans (mul_le_of_le_one_left (sq_nonneg ε) (by linarith)) hε2
        have hcoef : (1 + ε / 2000) * (1 + ε / 500) * (1 + ε / 500) + ε / 10000 ≤ 1 + (1 / 100 : ℝ) * ε := by
          linarith [show (1 + ε / 2000) * (1 + ε / 500) * (1 + ε / 500) + ε / 10000 =
            1 + (46 / 10000 : ℝ) * ε + (6 / 1000000 : ℝ) * ε ^ 2 + (1 / 500000000 : ℝ) * ε ^ 3 by ring]
        have := mul_le_mul_of_nonneg_right hcoef (by positivity : 0 ≤ (N : ℝ) * μ₀ ^ 2)
        linarith [show ((1 + ε / 2000) * (1 + ε / 500) * (1 + ε / 500) + ε / 10000) * ((N : ℝ) * μ₀ ^ 2) =
          (1 + ε / 2000) * (N : ℝ) * (((1 + ε / 500) * μ₀) * ((1 + ε / 500) * μ₀)) + (ε / 10000) * (N : ℝ) * μ₀ ^ 2 by ring]

set_option maxHeartbeats 600000 in
/-- Main density-zero theorem: for every `C : ℝ`, `{n | tauPerp n ≤ C * ω n}` has natural density `0`. -/
theorem erdos_1100_part_i (C : ℝ) :
    {n : ℕ | (Erdos1100.tauPerp n : ℝ) ≤ C * (ω n : ℝ)}.HasDensity 0 := by
  set S_bad : Set ℕ := {n : ℕ | (Erdos1100.tauPerp n : ℝ) ≤ C * (ω n : ℝ)}
  simp only [Set.HasDensity, Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio]
  rw [Metric.tendsto_atTop]
  intro ε_raw hε_raw
  set ε : ℝ := min ε_raw (1 / 2)
  have hε : 0 < ε := lt_min hε_raw (by norm_num)
  have hεhalf : ε ≤ 1 / 2 := min_le_right _ _
  have hεle : ε ≤ ε_raw := min_le_left _ _
  set C₁ : ℝ := max C 1
  have hC₁1 : 1 ≤ C₁ := le_max_right C 1
  have hCC₁ : C ≤ C₁ := le_max_left C 1
  set M_target : ℝ := 400 * C₁ / ε
  have hM_ge1 : 1 ≤ M_target := by
    unfold M_target; rw [one_le_div hε]; linarith
  -- Choose the grid `(L, G)` once and for all (depending only on `C` and `ε`):
  obtain ⟨L, G, hL, hLε, hG, hfine, hgrid_score⟩ := exists_good_grid hε hM_ge1
  set η : ℝ := L ^ (-(1 / 40 : ℝ))
  set γ : ℝ := (ε / 400) * η
  set β : ℝ := η / 4
  set Q_step : ℝ := 2 * L / γ
  set μ_grid : ℝ := ∑ b : Fin G → Bool, bernProb (gridP L G) b * (cellScore L G η b : ℝ)
  set μ₀ : ℝ := γ * μ_grid
  have hLpos : 0 < L := lt_of_lt_of_le (exp_pos _) hL
  have hlogL_ge : (10000000000 : ℝ) ≤ log L := by
    have := log_le_log (exp_pos _) hL; rwa [log_exp] at this
  have hL1 : 1 < L := (log_pos_iff hLpos.le).mp (by linarith)
  have hηpos : 0 < η := rpow_pos_of_pos hLpos _
  have hηle : η ≤ 1 / 10 := by
    unfold η; rw [rpow_def_of_pos hLpos]
    have h2 : exp (-10) ≤ 1 / 10 := by
      rw [exp_neg, one_div]; exact inv_anti₀ (by norm_num) (by linarith [add_one_le_exp (10 : ℝ)])
    exact le_trans (exp_le_exp.mpr (by linarith)) h2
  have hγpos : 0 < γ := by unfold γ; positivity
  have hγ1 : γ ≤ 1 := by unfold γ; nlinarith
  have hβpos : 0 < β := by unfold β; positivity
  have hQ_gt10 : 10 < Q_step := by unfold Q_step; rw [lt_div_iff₀ hγpos]; linarith [add_one_le_exp (10000000000 : ℝ)]
  have hQpos : 0 < Q_step := by linarith
  have hlogQ_pos : 0 < log Q_step := log_pos (by linarith)
  have hlogQ_ge1 : 1 ≤ log Q_step := by
    have h1 : exp 1 ≤ Q_step := by linarith [exp_one_lt_d9]
    have := log_le_log (exp_pos 1) h1; rwa [log_exp] at this
  have hμ₀_ge : M_target * log Q_step ≤ μ₀ := hgrid_score
  have hμ₀_pos : 0 < μ₀ := lt_of_lt_of_le (by positivity) hμ₀_ge
  have hμ₀_ge1 : 1 ≤ μ₀ := le_trans (by nlinarith) hμ₀_ge
  -- Fixed constants depending ONLY on `(L, G, ε)`:
  set Δ : ℝ := gridDelta L G
  have hΔpos : 0 < Δ := gridDelta_pos hL1 hG
  set L_sieve : ℝ := 2 * (log (L / γ) + 1)
  have hLsieve_pos : 0 < L_sieve := by
    have : 1 < L / γ := by rw [one_lt_div hγpos]; linarith
    have := log_pos this; unfold L_sieve; linarith
  -- Choose fixed `d₀ : ℕ` so that the Bonferroni tail `≤ (ε / 10000) * (γ / L)^2`:
  set m_bonf : ℕ := 2 * ⌈L_sieve⌉₊
  set t_bonf : ℕ := ⌈(L_sieve + log (20000 * (L / γ) ^ 2 / ε)) / log 2⌉₊ + 2
  set d₀ : ℕ := m_bonf + t_bonf
  have hd₀_tail : ∀ (x : ℝ) (M : ℕ), 0 ≤ x → x ≤ L_sieve →
      ∑ k ∈ Icc (2 * d₀ + 1) M, x ^ k / (Nat.factorial k : ℝ) ≤ (ε / 10000) * (γ / L) ^ 2 := by
    intro x M hx0 hxL
    have hK_ge : 2 * ⌈x⌉₊ ≤ 2 * d₀ + 1 := by
      have : ⌈x⌉₊ ≤ ⌈L_sieve⌉₊ := Nat.ceil_mono hxL
      omega
    have h1 := factorial_tail_sum_le hx0 (M := M) hK_ge
    have hsub_ge : t_bonf ≤ 2 * d₀ + 1 - 2 * ⌈x⌉₊ := by
      have : ⌈x⌉₊ ≤ ⌈L_sieve⌉₊ := Nat.ceil_mono hxL
      omega
    have hpow_le : (1 / 2 : ℝ) ^ (2 * d₀ + 1 - 2 * ⌈x⌉₊) ≤ (1 / 2 : ℝ) ^ t_bonf :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hsub_ge
    have hlog2 : 0 < log 2 := log_pos (by norm_num)
    have ht_ge : (L_sieve + log (20000 * (L / γ) ^ 2 / ε)) / log 2 ≤ (t_bonf : ℝ) := by
      have := Nat.le_ceil ((L_sieve + log (20000 * (L / γ) ^ 2 / ε)) / log 2)
      push_cast [t_bonf]; linarith
    have h2t : 2 * exp L_sieve * (1 / 2 : ℝ) ^ t_bonf ≤ (ε / 10000) * (γ / L) ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_right ht_ge hlog2.le
      rw [div_mul_cancel₀ _ hlog2.ne'] at hmul
      have hpow2 : (1 / 2 : ℝ) ^ t_bonf = exp (-(t_bonf : ℝ) * log 2) := by
        rw [one_div, inv_pow, ← rpow_natCast, rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
            ← exp_neg]; congr 1; ring
      rw [hpow2, mul_assoc, ← exp_add]
      have harg : L_sieve + -(t_bonf : ℝ) * log 2 ≤ -log (20000 * (L / γ) ^ 2 / ε) := by linarith
      calc 2 * exp (L_sieve + -(t_bonf : ℝ) * log 2)
          ≤ 2 * exp (-log (20000 * (L / γ) ^ 2 / ε)) :=
              mul_le_mul_of_nonneg_left (exp_le_exp.mpr harg) (by norm_num)
        _ = 2 * (ε / (20000 * (L / γ) ^ 2)) := by
              rw [exp_neg, exp_log (by positivity), inv_div]
        _ = (ε / 10000) * (γ / L) ^ 2 := by field_simp [hLpos.ne', hγpos.ne']; ring
    have hexpx : exp x ≤ exp L_sieve := exp_le_exp.mpr hxL
    calc ∑ k ∈ Icc (2 * d₀ + 1) M, x ^ k / (Nat.factorial k : ℝ)
        ≤ 2 * (1 / 2 : ℝ) ^ (2 * d₀ + 1 - 2 * ⌈x⌉₊) * exp x := h1
      _ ≤ 2 * (1 / 2 : ℝ) ^ t_bonf * exp L_sieve :=
            mul_le_mul (mul_le_mul_of_nonneg_left hpow_le (by norm_num)) hexpx (exp_pos x).le (by positivity)
      _ = 2 * exp L_sieve * (1 / 2 : ℝ) ^ t_bonf := by ring
      _ ≤ (ε / 10000) * (γ / L) ^ 2 := h2t
  -- Choose fixed starting block index `j₀ : ℕ` so all Mertens/trimming hypotheses hold for all `j ≥ j₀`:
  set A_j0 : ℝ := max (4 / γ) (max (6600000 / (γ * ε))
    (max (330 / Δ ^ 2) (max (24000 / (β * ε))
      ((log (max 1 (40000 * (log (L / γ) + 1) / ε)) + 2) / γ))))
  set j₀ : ℕ := ⌈log (max 1 A_j0) / log Q_step⌉₊ + 2
  have hj₀_ge1 : 1 ≤ j₀ := by omega
  have hj_props : ∀ j : ℕ, j₀ ≤ j →
      4 ≤ γ * Q_step ^ j ∧
      330 / (γ * Q_step ^ j) ≤ ε / 20000 ∧
      (2 / (loBlock γ Q_step j : ℝ)) * (log (L / γ) + 1) ≤ ε / 20000 ∧
      330 / Q_step ^ j ≤ Δ ^ 2 ∧
      120 / (β * Q_step ^ j) ≤ ε / 200 ∧
      1 ≤ loBlock γ Q_step j := by
    intro j hj
    have hQj_ge : A_j0 ≤ Q_step ^ j := by
      have h1 : log (max 1 A_j0) / log Q_step ≤ (j : ℝ) := by
        have hfl := Nat.le_ceil (log (max 1 A_j0) / log Q_step)
        have hj' : (j₀ : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
        push_cast [j₀] at hj'; linarith
      have h2 := mul_le_mul_of_nonneg_right h1 hlogQ_pos.le
      rw [div_mul_cancel₀ _ hlogQ_pos.ne'] at h2
      have h3 : max 1 A_j0 ≤ Q_step ^ j := by
        rw [← exp_log (lt_of_lt_of_le (by norm_num) (le_max_left 1 A_j0)),
            ← rpow_natCast, rpow_def_of_pos hQpos]
        exact exp_le_exp.mpr (by linarith)
      exact le_trans (le_max_right 1 A_j0) h3
    have hQpow_pos : 0 < Q_step ^ j := pow_pos hQpos j
    have h1 : 4 ≤ γ * Q_step ^ j := by
      have := le_trans (le_max_left _ _) hQj_ge
      rwa [div_le_iff₀ hγpos, mul_comm] at this
    have h2 : 330 / (γ * Q_step ^ j) ≤ ε / 20000 := by
      have h := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hQj_ge
      rw [div_le_iff₀ (by positivity)] at h
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    have h3 : (2 / (loBlock γ Q_step j : ℝ)) * (log (L / γ) + 1) ≤ ε / 20000 := by
      have h := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) (le_max_right _ _)))) hQj_ge
      rw [div_le_iff₀ hγpos] at h
      have hexp_ge : 40000 * (log (L / γ) + 1) / ε + 2 ≤ exp (γ * Q_step ^ j) := by
        have hpos_m : 0 < max 1 (40000 * (log (L / γ) + 1) / ε) :=
          lt_of_lt_of_le (by norm_num) (le_max_left _ _)
        have h_exp : max 1 (40000 * (log (L / γ) + 1) / ε) * exp 2 ≤ exp (γ * Q_step ^ j) := by
          rw [← exp_log hpos_m, ← exp_add]
          exact exp_le_exp.mpr (by linarith)
        have he2 : (3 : ℝ) ≤ exp 2 := by linarith [add_one_le_exp (2 : ℝ)]
        have hm1 : (1 : ℝ) ≤ max 1 (40000 * (log (L / γ) + 1) / ε) := le_max_left _ _
        have hm2 : 40000 * (log (L / γ) + 1) / ε ≤ max 1 (40000 * (log (L / γ) + 1) / ε) := le_max_right _ _
        nlinarith
      have hlo_ge : 40000 * (log (L / γ) + 1) / ε ≤ (loBlock γ Q_step j : ℝ) := by
        unfold loBlock
        have := Nat.lt_floor_add_one (exp (γ * Q_step ^ j)); linarith
      have hlo_pos : (0 : ℝ) < (loBlock γ Q_step j : ℝ) := by
        have : 0 < log (L / γ) + 1 := by
          have : 1 < L / γ := by rw [one_lt_div hγpos]; linarith
          linarith [log_pos this]
        have : 0 < 40000 * (log (L / γ) + 1) / ε := by positivity
        linarith
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hlo_pos (by norm_num)]
      have := mul_le_mul_of_nonneg_left hlo_ge hε.le
      rw [mul_div_cancel₀ _ hε.ne'] at this
      linarith
    have h4 : 330 / Q_step ^ j ≤ Δ ^ 2 := by
      have h := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hQj_ge
      rw [div_le_iff₀ (sq_pos_of_pos hΔpos)] at h
      rw [div_le_iff₀ hQpow_pos]; linarith
    have h5 : 120 / (β * Q_step ^ j) ≤ ε / 200 := by
      have h := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) (le_max_right _ _)))) hQj_ge
      rw [div_le_iff₀ (by positivity)] at h
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    have h6 : 1 ≤ loBlock γ Q_step j := Nat.le_floor (by push_cast; linarith [add_one_le_exp (γ * Q_step ^ j)])
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  -- Crude finite upper bound `S_max` on `∑ b, cellScore b` (hence on `Y_val j n`):
  set S_max : ℝ := ∑ b : Fin G → Bool, (cellScore L G η b : ℝ) + 1
  have hS_max_pos : 0 < S_max := by
    unfold S_max; linarith [sum_nonneg fun b (_ : b ∈ univ) => (Nat.cast_nonneg (cellScore L G η b) : (0 : ℝ) ≤ _)]
  have hY_le_Smax : ∀ (j n : ℕ), 0 < n → Y_val L γ Q_step η G j n ≤ S_max := by
    intro j n hn
    unfold Y_val
    have hle : ∀ b : Fin G → Bool, (∑ f ∈ tupleSet L Q_step G j b,
        if inSubCell L γ Q_step G j b f n then (cellScore L G η b : ℝ) else 0) ≤ (cellScore L G η b : ℝ) := by
      intro b
      by_cases hex : ∃ f ∈ tupleSet L Q_step G j b, inSubCell L γ Q_step G j b f n
      · obtain ⟨f₀, hf₀, hsc₀⟩ := hex
        rw [sum_eq_single f₀]
        · rw [if_pos hsc₀]
        · intro f hf hne
          rw [if_neg]; intro hsc
          exact hne (eq_of_heq (inSubCell_unique hL1 hG hγ1 hQpos hn hf hf₀ hsc hsc₀).2)
        · intro h; exact absurd hf₀ h
      · push Not at hex
        rw [sum_eq_zero fun f hf => if_neg (hex f hf)]
        exact Nat.cast_nonneg _
    have hsum := sum_le_sum fun b (_ : b ∈ univ) => hle b
    unfold S_max; linarith
  -- Choose large `N₀` so that all Bonferroni/subpoly errors are tiny AND `M_blocks ≥ log log N / (20 log Q_step)`:
  set C_err1 : ℝ := 100 * S_max ^ 2 * ((2 * d₀ + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * d₀ + 2)
  set K_exp1 : ℝ := (2 * G + 2 * d₀ + 6 : ℝ)
  set δ_err : ℝ := (ε / 10000) * (γ / L) ^ 2
  obtain ⟨N_dom, hNdom_100, hNdom⟩ := exp_subpoly_dominated (C_err := C_err1) (K_exp := K_exp1) (δ := δ_err)
    (by positivity) (by unfold K_exp1; have : (0 : ℝ) ≤ (G : ℝ) := Nat.cast_nonneg _; have : (0 : ℝ) ≤ (d₀ : ℝ) := Nat.cast_nonneg _; linarith) (by positivity)
  set LL_thr : ℝ := max 1000 (max (20 * ((j₀ + 2 : ℕ) : ℝ) * log Q_step + 20 * log L)
    (4000 * S_max * log Q_step / (ε * μ₀)))
  set N₀ : ℕ := max N_dom (max (⌈exp (exp LL_thr)⌉₊ + 10) (⌈10 / ε⌉₊ + 10))
  refine ⟨N₀, fun N hN => ?_⟩
  have hN_ge_dom : N_dom ≤ N := le_trans (le_max_left _ _) hN
  have hN_ge_100 : 100 ≤ N := le_trans hNdom_100 hN_ge_dom
  have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hN_ge_ee : exp (exp LL_thr) ≤ (N : ℝ) := by
    have h1 := Nat.le_ceil (exp (exp LL_thr))
    have h2 : (⌈exp (exp LL_thr)⌉₊ : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast le_trans (by omega : ⌈exp (exp LL_thr)⌉₊ ≤ ⌈exp (exp LL_thr)⌉₊ + 10)
        (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hN))
    linarith
  have hN_ge_10ε : 10 / ε ≤ (N : ℝ) := by
    have h1 := Nat.le_ceil (10 / ε)
    have h2 : (⌈10 / ε⌉₊ : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast le_trans (by omega : ⌈10 / ε⌉₊ ≤ ⌈10 / ε⌉₊ + 10)
        (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hN))
    linarith
  have hlogN_ge : exp LL_thr ≤ log (N : ℝ) := by
    have := log_le_log (exp_pos _) hN_ge_ee; rwa [log_exp] at this
  have hlogN_pos : 0 < log (N : ℝ) := lt_of_lt_of_le (exp_pos _) hlogN_ge
  have hllN_ge : LL_thr ≤ log (log (N : ℝ)) := by
    have := log_le_log (exp_pos _) hlogN_ge; rwa [log_exp] at this
  have hllN_ge1000 : (1000 : ℝ) ≤ log (log (N : ℝ)) := le_trans (le_max_left _ _) hllN_ge
  have hllN_pos : 0 < log (log (N : ℝ)) := by linarith
  -- Define upper block index `B`:
  set B : ℕ := ⌊log ((log (N : ℝ)) ^ (1 / 10 : ℝ) / L) / log Q_step⌋₊
  have hQ_B_le : L * Q_step ^ B ≤ (log (N : ℝ)) ^ (1 / 10 : ℝ) := by
    have harg_ge1 : 1 ≤ (log (N : ℝ)) ^ (1 / 10 : ℝ) / L := by
      rw [one_le_div hLpos, ← exp_log hLpos, rpow_def_of_pos hlogN_pos]
      apply exp_le_exp.mpr
      have h1 : 20 * log L ≤ log (log (N : ℝ)) := by
        have := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hllN_ge
        have : 0 ≤ 20 * ((j₀ + 2 : ℕ) : ℝ) * log Q_step := by positivity
        linarith
      linarith
    have hfl := Nat.floor_le (div_nonneg (log_nonneg harg_ge1) hlogQ_pos.le)
    have hmul := mul_le_mul_of_nonneg_right hfl hlogQ_pos.le
    rw [div_mul_cancel₀ _ hlogQ_pos.ne'] at hmul
    have hpow : Q_step ^ B ≤ (log (N : ℝ)) ^ (1 / 10 : ℝ) / L := by
      rw [← rpow_natCast, rpow_def_of_pos hQpos,
          ← exp_log (lt_of_lt_of_le (by norm_num) harg_ge1)]
      exact exp_le_exp.mpr (by linarith)
    rwa [le_div_iff₀ hLpos, mul_comm] at hpow
  set J_set : Finset ℕ := Icc j₀ B
  set M_blk : ℝ := (J_set.card : ℝ)
  have hMblk_ge : log (log (N : ℝ)) / (20 * log Q_step) ≤ M_blk := by
    have hlt := Nat.lt_floor_add_one (log ((log (N : ℝ)) ^ (1 / 10 : ℝ) / L) / log Q_step)
    have hmul := mul_lt_mul_of_pos_right hlt hlogQ_pos
    rw [div_mul_cancel₀ _ hlogQ_pos.ne'] at hmul
    change log ((log (N : ℝ)) ^ (1 / 10 : ℝ) / L) < ((B : ℝ) + 1) * log Q_step at hmul
    have hlog_eq : log ((log (N : ℝ)) ^ (1 / 10 : ℝ) / L) =
        (1 / 10 : ℝ) * log (log (N : ℝ)) - log L := by
      rw [log_div (rpow_pos_of_pos hlogN_pos _).ne' hLpos.ne', log_rpow hlogN_pos]
    have h1 : 20 * ((j₀ : ℝ) + 2) * log Q_step + 20 * log L ≤ log (log (N : ℝ)) := by
      have := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hllN_ge
      push_cast at this; exact this
    have hB_ge : j₀ ≤ B := by
      have hj0Q : 0 ≤ (j₀ : ℝ) * log Q_step := by positivity
      have h2 : ((j₀ + 1 : ℕ) : ℝ) * log Q_step < ((B + 1 : ℕ) : ℝ) * log Q_step := by
        push_cast; linarith
      have h3 : ((j₀ + 1 : ℕ) : ℝ) < ((B + 1 : ℕ) : ℝ) := lt_of_mul_lt_mul_right h2 hlogQ_pos.le
      have h4 : j₀ + 1 < B + 1 := by exact_mod_cast h3
      omega
    have hcard_eq : M_blk = (B : ℝ) - (j₀ : ℝ) + 1 := by
      unfold M_blk J_set; rw [Nat.card_Icc, Nat.cast_sub (by omega : j₀ ≤ B + 1)]; push_cast; ring
    rw [div_le_iff₀ (by positivity), hcard_eq]
    linarith [show ((B : ℝ) - (j₀ : ℝ) + 1) * (20 * log Q_step) =
      20 * (((B : ℝ) + 1) * log Q_step) - 20 * (j₀ : ℝ) * log Q_step by ring]
  have hMblk_pos : 0 < M_blk := lt_of_lt_of_le (by positivity) hMblk_ge
  have hMblk_big : 200 * S_max / (ε * μ₀) ≤ M_blk := by
    have h1 : 4000 * S_max * log Q_step / (ε * μ₀) ≤ log (log (N : ℝ)) :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hllN_ge
    have h2 : 200 * S_max / (ε * μ₀) ≤ log (log (N : ℝ)) / (20 * log Q_step) := by
      rw [le_div_iff₀ (by positivity)]
      have hrew : 200 * S_max / (ε * μ₀) * (20 * log Q_step) =
          4000 * S_max * log Q_step / (ε * μ₀) := by ring
      linarith
    linarith
  -- Uniform bound on `hiBlock j`, `Sblock.card`, `tupleSet.card`, and Bonferroni error for any `j ∈ J_set`:
  set R_sub : ℝ := exp ((log (N : ℝ)) ^ (1 / 10 : ℝ))
  have hR_ge1 : 1 ≤ R_sub := one_le_exp (rpow_nonneg hlogN_pos.le _)
  have hj_sizes : ∀ j ∈ J_set,
      (hiBlock L Q_step j : ℝ) ≤ R_sub ∧
      ((Sblock L γ Q_step j).card : ℝ) ≤ R_sub ∧
      (loBlock γ Q_step j : ℝ) ≤ R_sub ∧
      (∀ b : Fin G → Bool, ((tupleSet L Q_step G j b).card : ℝ) ≤ R_sub ^ G) := by
    intro j hj
    have hjB : j ≤ B := (mem_Icc.mp hj).2
    have hLQj : L * Q_step ^ j ≤ (log (N : ℝ)) ^ (1 / 10 : ℝ) :=
      le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith) hjB) hLpos.le) hQ_B_le
    have hhi : (hiBlock L Q_step j : ℝ) ≤ R_sub :=
      le_trans (Nat.floor_le (exp_pos _).le) (exp_le_exp.mpr hLQj)
    have hS : ((Sblock L γ Q_step j).card : ℝ) ≤ R_sub := by
      have h1 : (Sblock L γ Q_step j).card ≤ hiBlock L Q_step j := by
        calc (Sblock L γ Q_step j).card ≤ (Ioc (loBlock γ Q_step j) (hiBlock L Q_step j)).card := card_filter_le _ _
          _ ≤ (Icc 1 (hiBlock L Q_step j)).card := card_le_card (fun p hp => by
              simp only [mem_Ioc, mem_Icc] at hp ⊢; omega)
          _ = hiBlock L Q_step j := by rw [Nat.card_Icc, Nat.add_sub_cancel]
      exact le_trans (by exact_mod_cast h1) hhi
    have hlo : (loBlock γ Q_step j : ℝ) ≤ R_sub := by
      have h1 : loBlock γ Q_step j ≤ hiBlock L Q_step j :=
        Nat.floor_mono (exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hQpos.le j)))
      exact le_trans (by exact_mod_cast h1) hhi
    refine ⟨hhi, hS, hlo, fun b => ?_⟩
    have hcard_pi : (tupleSet L Q_step G j b).card = ∏ r : activeSet b, (Pbin L Q_step G j r.1).card := by
      unfold tupleSet; exact Fintype.card_piFinset _
    have hprod_le : ((tupleSet L Q_step G j b).card : ℝ) ≤ R_sub ^ (activeSet b).card := by
      rw [hcard_pi, Nat.cast_prod]
      calc ∏ r : activeSet b, ((Pbin L Q_step G j r.1).card : ℝ)
          ≤ ∏ _r : activeSet b, R_sub := prod_le_prod (fun _ _ => Nat.cast_nonneg _) fun r _ => by
              have hsub := Pbin_subset_Sblock hL1 hG hγ1 hQpos r.1 (j := j)
              exact le_trans (by exact_mod_cast card_le_card hsub) hS
        _ = R_sub ^ (activeSet b).card := by rw [prod_const, card_univ, Fintype.card_coe]
    have hact_le : (activeSet b).card ≤ G := by
      calc (activeSet b).card ≤ (univ : Finset (Fin G)).card := card_le_univ _
        _ = G := Fintype.card_fin G
    exact le_trans hprod_le (pow_le_pow_right₀ hR_ge1 hact_le)
  have hdom_N := hNdom N hN_ge_dom
  -- Single-block mean, trimmed mean, and off-diagonal pair bounds for `j ∈ J_set`:
  have hY_mean : ∀ j ∈ J_set,
      (1 - ε / 200) * (N : ℝ) * μ₀ ≤ (∑ n ∈ Icc 1 N, Y_val L γ Q_step η G j n) ∧
      (∑ n ∈ Icc 1 N, Y_val L γ Q_step η G j n) ≤ (1 + ε / 200) * (N : ℝ) * μ₀ := fun j hj => by
    have hj' := hj_props j (mem_Icc.mp hj).1
    have hsz := hj_sizes j hj
    exact block_Y_mean_approx hL hG hε hεhalf rfl rfl rfl hfine hLε rfl hμ₀_ge1 rfl rfl rfl rfl hN_ge_100 rfl
      hj'.1 hj'.2.1 hj'.2.2.1 hj'.2.2.2.1 hsz.2.1 hsz.2.2.2 hd₀_tail hdom_N
  have hZ_mean : ∀ j ∈ J_set,
      (1 - (4 / 100 : ℝ) * ε) * (N : ℝ) * μ₀ ≤ ∑ n ∈ Icc 1 N, Z_val L γ β Q_step η G j n := fun j hj => by
    have hj' := hj_props j (mem_Icc.mp hj).1
    have hsz := hj_sizes j hj
    exact block_Z_mean_lower hL hG hε hεhalf rfl rfl rfl rfl hfine hLε rfl hμ₀_ge1 rfl rfl rfl rfl hN_ge_100 rfl
      hj'.1 hj'.2.1 hj'.2.2.1 hj'.2.2.2.1 hj'.2.2.2.2.1 hj'.2.2.2.2.2
      hsz.2.1 hsz.2.2.1 hsz.2.2.2 hd₀_tail hdom_N (hY_mean j hj).1
  have hY_pair : ∀ j₁ ∈ J_set, ∀ j₂ ∈ J_set, j₁ ≠ j₂ →
      ∑ n ∈ Icc 1 N, Y_val L γ Q_step η G j₁ n * Y_val L γ Q_step η G j₂ n ≤
        (1 + (1 / 100 : ℝ) * ε) * (N : ℝ) * μ₀ ^ 2 := fun j₁ hj₁ j₂ hj₂ hne => by
    have hj₁' := hj_props j₁ (mem_Icc.mp hj₁).1
    have hj₂' := hj_props j₂ (mem_Icc.mp hj₂).1
    have hsz₁ := hj_sizes j₁ hj₁
    have hsz₂ := hj_sizes j₂ hj₂
    exact block_Y_pair_upper hL hG hε hεhalf rfl rfl rfl hfine hLε rfl hμ₀_ge1 rfl rfl rfl rfl hN_ge_100 rfl hne
      hj₁'.1 hj₁'.2.1 hj₁'.2.2.1 hj₁'.2.2.2.1 hj₂'.1 hj₂'.2.1 hj₂'.2.2.1 hj₂'.2.2.2.1
      hsz₁.2.1 hsz₂.2.1 hsz₁.2.2.2 hsz₂.2.2.2 hd₀_tail hdom_N
  -- Second moment and Chebyshev concentration for `S_tot n = ∑ j ∈ J_set, Z_val j n`:
  let S_tot (n : ℕ) : ℝ := ∑ j ∈ J_set, Z_val L γ β Q_step η G j n
  let S_Y (n : ℕ) : ℝ := ∑ j ∈ J_set, Y_val L γ Q_step η G j n
  set μ_tot : ℝ := M_blk * μ₀
  have hμtot_pos : 0 < μ_tot := mul_pos hMblk_pos hμ₀_pos
  have hmean_Stot : (1 - (4 / 100 : ℝ) * ε) * (N : ℝ) * μ_tot ≤ ∑ n ∈ Icc 1 N, S_tot n := by
    unfold S_tot
    rw [sum_comm]
    calc (1 - (4 / 100 : ℝ) * ε) * (N : ℝ) * μ_tot
        = ∑ _j ∈ J_set, (1 - (4 / 100 : ℝ) * ε) * (N : ℝ) * μ₀ := by
            rw [sum_const, nsmul_eq_mul]; unfold μ_tot M_blk; ring
      _ ≤ ∑ j ∈ J_set, ∑ n ∈ Icc 1 N, Z_val L γ β Q_step η G j n := sum_le_sum hZ_mean
  have hsq_Stot : ∑ n ∈ Icc 1 N, (S_tot n) ^ 2 ≤ (1 + (2 / 100 : ℝ) * ε) * (N : ℝ) * μ_tot ^ 2 := by
    have hpt_le : ∀ n ∈ Icc 1 N, (S_tot n) ^ 2 ≤ (S_Y n) ^ 2 := fun n _ => by
      have h0 : 0 ≤ S_tot n := sum_nonneg fun j _ => by
        unfold Z_val Y_val
        split_ifs
        · exact sum_nonneg fun b _ => sum_nonneg fun f _ => by split_ifs <;> positivity
        · exact le_rfl
      have hle : S_tot n ≤ S_Y n := sum_le_sum fun j _ => by
        unfold Z_val
        split_ifs
        · exact le_rfl
        · exact sum_nonneg fun b _ => sum_nonneg fun f _ => by split_ifs <;> positivity
      exact pow_le_pow_left₀ h0 hle 2
    have hexpand_sq : ∑ n ∈ Icc 1 N, (S_Y n) ^ 2 =
        ∑ j₁ ∈ J_set, ∑ j₂ ∈ J_set, ∑ n ∈ Icc 1 N, Y_val L γ Q_step η G j₁ n * Y_val L γ Q_step η G j₂ n := by
      have h1 : ∀ n ∈ Icc 1 N, (S_Y n) ^ 2 =
          ∑ j₁ ∈ J_set, ∑ j₂ ∈ J_set, Y_val L γ Q_step η G j₁ n * Y_val L γ Q_step η G j₂ n := fun n _ => by
        unfold S_Y; rw [sq, sum_mul_sum]
      rw [sum_congr rfl h1, sum_comm]
      refine sum_congr rfl fun j₁ _ => sum_comm
    have hdiag : ∀ j ∈ J_set, ∑ n ∈ Icc 1 N, Y_val L γ Q_step η G j n * Y_val L γ Q_step η G j n ≤
        2 * S_max * (N : ℝ) * μ₀ := by
      intro j hj
      calc _ ≤ ∑ n ∈ Icc 1 N, S_max * Y_val L γ Q_step η G j n := by
              refine sum_le_sum fun n hn => ?_
              have hn1 : 0 < n := (mem_Icc.mp hn).1
              have hYnn : 0 ≤ Y_val L γ Q_step η G j n :=
                sum_nonneg fun _ _ => sum_nonneg fun _ _ => by split_ifs <;> positivity
              exact mul_le_mul_of_nonneg_right (hY_le_Smax j n hn1) hYnn
        _ = S_max * ∑ n ∈ Icc 1 N, Y_val L γ Q_step η G j n := (mul_sum _ _ _).symm
        _ ≤ S_max * ((1 + ε / 200) * (N : ℝ) * μ₀) := mul_le_mul_of_nonneg_left (hY_mean j hj).2 hS_max_pos.le
        _ ≤ 2 * S_max * (N : ℝ) * μ₀ := by
              have h1 : (1 + ε / 200) * ((N : ℝ) * μ₀) ≤ 2 * ((N : ℝ) * μ₀) :=
                mul_le_mul_of_nonneg_right (by linarith) (mul_pos hNpos hμ₀_pos).le
              have h2 := mul_le_mul_of_nonneg_left h1 hS_max_pos.le
              linarith [show S_max * ((1 + ε / 200) * (N : ℝ) * μ₀) = S_max * ((1 + ε / 200) * ((N : ℝ) * μ₀)) by ring,
                        show 2 * S_max * (N : ℝ) * μ₀ = S_max * (2 * ((N : ℝ) * μ₀)) by ring]
    have htot_Y : ∑ n ∈ Icc 1 N, (S_Y n) ^ 2 ≤ (1 + (2 / 100 : ℝ) * ε) * (N : ℝ) * μ_tot ^ 2 := by
      rw [hexpand_sq]
      calc _ ≤ ∑ j₁ ∈ J_set, ∑ j₂ ∈ J_set,
            ((if j₁ = j₂ then 2 * S_max * (N : ℝ) * μ₀ else 0) +
              (1 + (1 / 100 : ℝ) * ε) * (N : ℝ) * μ₀ ^ 2) := by
              refine sum_le_sum fun j₁ hj₁ => sum_le_sum fun j₂ hj₂ => ?_
              by_cases heq : j₁ = j₂
              · subst heq; rw [if_pos rfl]
                have := hdiag j₁ hj₁
                have : 0 ≤ (1 + (1 / 100 : ℝ) * ε) * (N : ℝ) * μ₀ ^ 2 := by positivity
                linarith
              · rw [if_neg heq, zero_add]; exact hY_pair j₁ hj₁ j₂ hj₂ heq
        _ = M_blk * (2 * S_max * (N : ℝ) * μ₀) + M_blk ^ 2 * ((1 + (1 / 100 : ℝ) * ε) * (N : ℝ) * μ₀ ^ 2) := by
              have h1 : ∀ j₁ ∈ J_set, ∑ j₂ ∈ J_set,
                  ((if j₁ = j₂ then 2 * S_max * (N : ℝ) * μ₀ else 0) +
                    (1 + (1 / 100 : ℝ) * ε) * (N : ℝ) * μ₀ ^ 2) =
                  2 * S_max * (N : ℝ) * μ₀ + M_blk * ((1 + (1 / 100 : ℝ) * ε) * (N : ℝ) * μ₀ ^ 2) := fun j₁ hj₁ => by
                rw [sum_add_distrib, sum_ite_eq J_set j₁, if_pos hj₁, sum_const, nsmul_eq_mul]
              rw [sum_congr rfl h1, sum_const, nsmul_eq_mul]
              unfold M_blk; ring
        _ ≤ (1 + (2 / 100 : ℝ) * ε) * (N : ℝ) * μ_tot ^ 2 := by
              have hdiag_sm : 2 * S_max ≤ (1 / 100 : ℝ) * ε * M_blk * μ₀ := by
                have := mul_le_mul_of_nonneg_left hMblk_big (mul_pos hε hμ₀_pos).le
                rw [mul_div_cancel₀ _ (mul_pos hε hμ₀_pos).ne'] at this
                linarith
              have hdiag_tot : M_blk * (2 * S_max * (N : ℝ) * μ₀) ≤ (1 / 100 : ℝ) * ε * (N : ℝ) * μ_tot ^ 2 := by
                have := mul_le_mul_of_nonneg_right hdiag_sm (by positivity : 0 ≤ M_blk * (N : ℝ) * μ₀)
                unfold μ_tot; linarith [show (1 / 100 : ℝ) * ε * M_blk * μ₀ * (M_blk * (N : ℝ) * μ₀) =
                    (1 / 100 : ℝ) * ε * (N : ℝ) * (M_blk * μ₀) ^ 2 by ring]
              unfold μ_tot; linarith [show M_blk ^ 2 * ((1 + (1 / 100 : ℝ) * ε) * (N : ℝ) * μ₀ ^ 2) =
                  (1 + (1 / 100 : ℝ) * ε) * (N : ℝ) * (M_blk * μ₀) ^ 2 by ring]
    exact le_trans (sum_le_sum hpt_le) htot_Y
  -- Chebyshev bound on `B_Z := (Icc 1 N).filter (fun n => S_tot n < (1 / 4) * μ_tot)`:
  set B_Z := (Icc 1 N).filter (fun n => S_tot n < (1 / 4 : ℝ) * μ_tot)
  have hBZ_card : (B_Z.card : ℝ) ≤ (ε / 4) * (N : ℝ) := by
    set avg : ℝ := (∑ n ∈ Icc 1 N, S_tot n) / (N : ℝ)
    have havg_ge : (1 - (4 / 100 : ℝ) * ε) * μ_tot ≤ avg := by
      unfold avg; rw [le_div_iff₀ hNpos]; linarith
    have hvar : ∑ n ∈ Icc 1 N, (S_tot n - avg) ^ 2 ≤ (ε / 10) * (N : ℝ) * μ_tot ^ 2 := by
      have hid : ∑ n ∈ Icc 1 N, (S_tot n - avg) ^ 2 = (∑ n ∈ Icc 1 N, (S_tot n) ^ 2) - (N : ℝ) * avg ^ 2 := by
        have h1 : ∀ n ∈ Icc 1 N, (S_tot n - avg) ^ 2 = (S_tot n) ^ 2 - 2 * avg * S_tot n + avg ^ 2 := fun _ _ => by ring
        rw [sum_congr rfl h1, sum_add_distrib, sum_sub_distrib, ← mul_sum,
            sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        have hsum_avg : ∑ n ∈ Icc 1 N, S_tot n = (N : ℝ) * avg := by unfold avg; field_simp [hNpos.ne']
        rw [hsum_avg]; ring
      rw [hid]
      have hsq_avg : (1 - (8 / 100 : ℝ) * ε) * μ_tot ^ 2 ≤ avg ^ 2 := by
        have h1 : ((1 - (4 / 100 : ℝ) * ε) * μ_tot) ^ 2 ≤ avg ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg (by linarith) hμtot_pos.le) havg_ge 2
        have h2 : (1 - (8 / 100 : ℝ) * ε) * μ_tot ^ 2 ≤ ((1 - (4 / 100 : ℝ) * ε) * μ_tot) ^ 2 := by
          linarith [sq_nonneg ((4 / 100 : ℝ) * ε * μ_tot),
            show ((1 - (4 / 100 : ℝ) * ε) * μ_tot) ^ 2 - (1 - (8 / 100 : ℝ) * ε) * μ_tot ^ 2 =
              ((4 / 100 : ℝ) * ε * μ_tot) ^ 2 by ring]
        linarith
      have hNsq := mul_le_mul_of_nonneg_left hsq_avg hNpos.le
      linarith [hsq_Stot]
    have hcheb : ((7 / 10 : ℝ) * μ_tot) ^ 2 * (B_Z.card : ℝ) ≤ (ε / 10) * (N : ℝ) * μ_tot ^ 2 := by
      refine le_trans ?_ hvar
      calc ((7 / 10 : ℝ) * μ_tot) ^ 2 * (B_Z.card : ℝ)
          = ∑ _n ∈ B_Z, ((7 / 10 : ℝ) * μ_tot) ^ 2 := by rw [sum_const, nsmul_eq_mul, mul_comm]
        _ ≤ ∑ n ∈ B_Z, (S_tot n - avg) ^ 2 := by
              refine sum_le_sum fun n hn => ?_
              have hlt : S_tot n < (1 / 4 : ℝ) * μ_tot := (mem_filter.mp hn).2
              have h95 : (95 / 100 : ℝ) * μ_tot ≤ (1 - (4 / 100 : ℝ) * ε) * μ_tot :=
                mul_le_mul_of_nonneg_right (by linarith) hμtot_pos.le
              have hgap : (7 / 10 : ℝ) * μ_tot ≤ avg - S_tot n := by linarith
              have hsq := pow_le_pow_left₀ (by positivity) hgap 2
              linarith [show (S_tot n - avg) ^ 2 = (avg - S_tot n) ^ 2 by ring]
        _ ≤ ∑ n ∈ Icc 1 N, (S_tot n - avg) ^ 2 :=
              sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => sq_nonneg _
    have hpos_sq : 0 < μ_tot ^ 2 := sq_pos_of_pos hμtot_pos
    have h1 : (49 / 100 : ℝ) * (B_Z.card : ℝ) * μ_tot ^ 2 ≤ (ε / 10) * (N : ℝ) * μ_tot ^ 2 := by
      linarith [show ((7 / 10 : ℝ) * μ_tot) ^ 2 * (B_Z.card : ℝ) = (49 / 100 : ℝ) * (B_Z.card : ℝ) * μ_tot ^ 2 by ring]
    have h2 : (49 / 100 : ℝ) * (B_Z.card : ℝ) ≤ (ε / 10) * (N : ℝ) := le_of_mul_le_mul_right h1 hpos_sq
    linarith [show (0 : ℝ) ≤ ε * (N : ℝ) by positivity]
  -- Markov bound on `B_ω := (range N).filter (fun n => (4 / ε) * log (log N) < ω n)`:
  set B_ω := (range N).filter (fun n => (4 / ε) * log (log (N : ℝ)) < (ω n : ℝ))
  have hBω_card : (B_ω.card : ℝ) ≤ (ε / 2) * (N : ℝ) := by
    have hω := sum_omega_le N (by omega)
    have hω2 : ∑ n ∈ range N, (ω n : ℝ) ≤ 2 * (N : ℝ) * log (log (N : ℝ)) := by
      have hm := mul_le_mul_of_nonneg_left (show log (log (N : ℝ)) + 400 ≤ 2 * log (log (N : ℝ)) by linarith) hNpos.le
      linarith
    have hmarkov : ((4 / ε) * log (log (N : ℝ))) * (B_ω.card : ℝ) ≤
        2 * (N : ℝ) * log (log (N : ℝ)) := by
      refine le_trans ?_ hω2
      calc _ = ∑ _n ∈ B_ω, ((4 / ε) * log (log (N : ℝ))) := by rw [sum_const, nsmul_eq_mul, mul_comm]
        _ ≤ ∑ n ∈ B_ω, (ω n : ℝ) := sum_le_sum fun n hn => (mem_filter.mp hn).2.le
        _ ≤ ∑ n ∈ range N, (ω n : ℝ) :=
            sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => Nat.cast_nonneg _
    have hthr_pos : 0 < (4 / ε) * log (log (N : ℝ)) := by positivity
    have hfin : ((4 / ε) * log (log (N : ℝ))) * (B_ω.card : ℝ) ≤
        ((4 / ε) * log (log (N : ℝ))) * ((ε / 2) * (N : ℝ)) := by
      have hid : ((4 / ε) * log (log (N : ℝ))) * ((ε / 2) * (N : ℝ)) =
          2 * (N : ℝ) * log (log (N : ℝ)) := by field_simp [hε.ne']; ring
      linarith
    exact le_of_mul_le_mul_left hfin hthr_pos
  -- Every `n ∈ (range N).filter (· ∈ S_bad)` lies in `{0} ∪ B_ω ∪ B_Z`:
  have hcov_bad : (range N).filter (fun n => n ∈ S_bad) ⊆ ({0} : Finset ℕ) ∪ B_ω ∪ B_Z := by
    intro n hn
    simp only [mem_filter, mem_range] at hn
    rcases Nat.eq_zero_or_pos n with rfl | hn_pos
    · exact mem_union_left _ (mem_union_left _ (mem_singleton_self 0))
    · by_cases hω : (4 / ε) * log (log (N : ℝ)) < (ω n : ℝ)
      · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨mem_range.mpr hn.1, hω⟩))
      · push Not at hω
        apply mem_union_right
        refine mem_filter.mpr ⟨mem_Icc.mpr ⟨hn_pos, le_of_lt hn.1⟩, ?_⟩
        by_contra hge; push Not at hge
        have htau : S_tot n ≤ (Erdos1100.tauPerp n : ℝ) :=
          sum_Z_le_tauPerp hL hG hηpos hγpos hγ1 rfl rfl hfine J_set hn_pos
        have hbad : (Erdos1100.tauPerp n : ℝ) ≤ C * (ω n : ℝ) := hn.2
        have hCω : C * (ω n : ℝ) ≤ C₁ * ((4 / ε) * log (log (N : ℝ))) := by
          calc C * (ω n : ℝ) ≤ C₁ * (ω n : ℝ) := mul_le_mul_of_nonneg_right hCC₁ (Nat.cast_nonneg _)
            _ ≤ C₁ * ((4 / ε) * log (log (N : ℝ))) := mul_le_mul_of_nonneg_left hω (by linarith)
        have hlower : (5 * C₁ / ε) * log (log (N : ℝ)) ≤ (1 / 4 : ℝ) * μ_tot := by
          have h1 : (log (log (N : ℝ)) / (20 * log Q_step)) * (M_target * log Q_step) ≤ μ_tot :=
            mul_le_mul hMblk_ge hμ₀_ge (by positivity) hMblk_pos.le
          have h2 : (1 / 4 : ℝ) * ((log (log (N : ℝ)) / (20 * log Q_step)) *
              (M_target * log Q_step)) = (5 * C₁ / ε) * log (log (N : ℝ)) := by
            unfold M_target; field_simp [hlogQ_pos.ne', hε.ne']; ring
          linarith
        have hstrict : C₁ * ((4 / ε) * log (log (N : ℝ))) < (5 * C₁ / ε) * log (log (N : ℝ)) := by
          have hpos_t : 0 < (C₁ / ε) * log (log (N : ℝ)) := by positivity
          linarith [show C₁ * ((4 / ε) * log (log (N : ℝ))) = 4 * ((C₁ / ε) * log (log (N : ℝ))) by ring,
                    show (5 * C₁ / ε) * log (log (N : ℝ)) = 5 * ((C₁ / ε) * log (log (N : ℝ))) by ring]
        linarith
  have hncard_eq : (S_bad ∩ Set.Iio N).ncard = ((range N).filter (fun n => n ∈ S_bad)).card := by
    have hset : S_bad ∩ Set.Iio N = ↑((range N).filter (fun n => n ∈ S_bad)) := by
      ext n; simp only [Set.mem_inter_iff, Set.mem_Iio, mem_coe, mem_filter, mem_range]; tauto
    rw [hset, Set.ncard_coe_finset]
  rw [dist_eq, sub_zero, abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)), hncard_eq]
  rw [div_lt_iff₀ hNpos]
  have hcard_le : (((range N).filter (fun n => n ∈ S_bad)).card : ℝ) ≤
      1 + (B_ω.card : ℝ) + (B_Z.card : ℝ) := by
    have hnat : ((range N).filter (fun n => n ∈ S_bad)).card ≤ 1 + B_ω.card + B_Z.card := by
      calc _ ≤ (({0} : Finset ℕ) ∪ B_ω ∪ B_Z).card := card_le_card hcov_bad
        _ ≤ (({0} : Finset ℕ) ∪ B_ω).card + B_Z.card := card_union_le _ _
        _ ≤ ({0} : Finset ℕ).card + B_ω.card + B_Z.card := Nat.add_le_add_right (card_union_le _ _) _
        _ = 1 + B_ω.card + B_Z.card := by simp
    exact_mod_cast hnat
  have h1_le : (1 : ℝ) ≤ (ε / 10) * (N : ℝ) := by
    have := mul_le_mul_of_nonneg_left hN_ge_10ε hε.le
    rw [mul_div_cancel₀ _ hε.ne'] at this; linarith
  have htot_lt : 1 + (B_ω.card : ℝ) + (B_Z.card : ℝ) < ε * (N : ℝ) := by
    linarith [mul_pos hε hNpos]
  have hle_raw : ε * (N : ℝ) ≤ ε_raw * (N : ℝ) := mul_le_mul_of_nonneg_right hεle hNpos.le
  linarith

end Erdos1100Proof

theorem OMA.solution : type_of% @Erdos1100.erdos_1100.parts.i :=
  Erdos1100Proof.erdos_1100_part_i

