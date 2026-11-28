import FormalConjectures.OEIS.«7918»

-- Reduction OeisA7918.conjecture2.R1 of Least prime ≥ n — conjecture2
-- Credit: @mbilenko03

/-!
# Ordowski's bound `a(n) < n^(n^(1/n))` from Cramér's strict gap bound

For `x ≥ 1`, `x^(1/x) = exp(log x / x) ≥ 1 + log x / x`, so
`x^(x^(1/x)) ≥ exp(log x + (log x)^2 / x) = x * exp((log x)^2 / x) ≥ x + (log x)^2`.
So the conjecture follows from `a(n) < n + (log n)^2`, i.e. from Cramér's strict gap bound
`p' - p < (log p)^2` for consecutive primes `p ≥ 11`: apply it to the largest prime `p ≤ n`.
The cases `n ≤ 10` are checked by hand. This analytic part and the assembly are proved in `main`.

* `H1` (open core): Cramér's strict gap bound for primes `p ≥ 4 * 10^18`. Since
  `n^(n^(1/n)) = n + (log n)^2 + O((log n)^4 / n)`, the conjecture itself is essentially this
  bound, so a core of this strength is unavoidable. (Granville's heuristic predicts gaps up to
  about `1.12 (log p)^2`, so both may fail for some huge `p`.)
* `H2` (verified numerically, not formalized): the same bound for primes `11 ≤ p < 4 * 10^18`.
  Oliveira e Silva, Herzog and Pardi (2014) list every maximal prime gap below `4 * 10^18`;
  the largest ratio `gap / (log p)^2` among them is about `0.92` (gap 1132 after
  `1693182318746371`).
-/

namespace OMA.R_OeisA7918_conjecture2_R1

open OeisA7918

/-- Open core: Cramér's strict gap bound above `4 * 10^18`: every prime `p ≥ 4 * 10^18` is
followed by a prime `q < p + (log p)^2`. -/
def H1 : Prop :=
  ∀ p : ℕ, p.Prime → 4 * 10 ^ 18 ≤ p → ∃ q : ℕ, q.Prime ∧ p < q ∧ (q : ℝ) < p + Real.log p ^ 2

/-- Numerically verified range (Oliveira e Silva–Herzog–Pardi 2014): every prime
`11 ≤ p < 4 * 10^18` is followed by a prime `q < p + (log p)^2`. -/
def H2 : Prop :=
  ∀ p : ℕ, p.Prime → 11 ≤ p → p < 4 * 10 ^ 18 →
    ∃ q : ℕ, q.Prime ∧ p < q ∧ (q : ℝ) < p + Real.log p ^ 2

/-- `x + (log x)^2 ≤ x^(x^(1/x))` for `x ≥ 1`. -/
lemma add_log_sq_le {x : ℝ} (hx : 1 ≤ x) : x + Real.log x ^ 2 ≤ x ^ (x ^ (1 / x)) := by
  have hx0 : 0 < x := by linarith
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  have h1 : 1 + Real.log x / x ≤ x ^ (1 / x) := by
    rw [Real.rpow_def_of_pos hx0, mul_one_div]
    have := Real.add_one_le_exp (Real.log x / x)
    linarith
  rw [Real.rpow_def_of_pos hx0]
  have h2 : Real.log x * (1 + Real.log x / x) ≤ Real.log x * x ^ (1 / x) :=
    mul_le_mul_of_nonneg_left h1 hl
  have h3 : Real.exp (Real.log x * (1 + Real.log x / x)) = x * Real.exp (Real.log x ^ 2 / x) := by
    rw [mul_add, mul_one, Real.exp_add, Real.exp_log hx0]; congr 2; ring
  have h4 : 1 + Real.log x ^ 2 / x ≤ Real.exp (Real.log x ^ 2 / x) := by
    have := Real.add_one_le_exp (Real.log x ^ 2 / x); linarith
  calc x + Real.log x ^ 2 = x * (1 + Real.log x ^ 2 / x) := by field_simp
    _ ≤ x * Real.exp (Real.log x ^ 2 / x) := mul_le_mul_of_nonneg_left h4 hx0.le
    _ = Real.exp (Real.log x * (1 + Real.log x / x)) := h3.symm
    _ ≤ Real.exp (Real.log x * x ^ (1 / x)) := Real.exp_le_exp.mpr h2

lemma a_le {n q : ℕ} (hq : q.Prime) (hnq : n ≤ q) : a n ≤ q := Nat.sInf_le ⟨hq, hnq⟩

lemma log_two_gt : (693 / 1000 : ℝ) < Real.log 2 := by
  have := Real.log_two_gt_d9; linarith

/-- `a n < n + (log n)^2` for every `n ≥ 2`. -/
lemma a_lt (h1 : H1) (h2 : H2) (n : ℕ) (hn : 2 ≤ n) : (a n : ℝ) < n + Real.log n ^ 2 := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  have hlpos : 0 < Real.log n := Real.log_pos hn1
  by_cases hp : n.Prime
  · have : a n ≤ n := a_le hp le_rfl
    have : (a n : ℝ) ≤ n := by exact_mod_cast this
    nlinarith
  by_cases hbig : 11 ≤ n
  · set p := Nat.findGreatest Nat.Prime n with hpdef
    have hp11 : 11 ≤ p := Nat.le_findGreatest hbig (by norm_num)
    have hpp : p.Prime := Nat.findGreatest_spec (P := Nat.Prime) hbig (by norm_num)
    have hpn : p ≤ n := Nat.findGreatest_le n
    obtain ⟨q, hq, hpq, hqlt⟩ : ∃ q : ℕ, q.Prime ∧ p < q ∧ (q : ℝ) < p + Real.log p ^ 2 := by
      rcases lt_or_ge p (4 * 10 ^ 18) with h | h
      · exact h2 p hpp hp11 h
      · exact h1 p hpp h
    have hnq : n ≤ q := by
      by_contra hc
      exact Nat.findGreatest_is_greatest hpq (by omega) hq
    have haq : (a n : ℝ) ≤ q := by exact_mod_cast a_le hq hnq
    have hpnr : (p : ℝ) ≤ n := by exact_mod_cast hpn
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
    have hlog : Real.log p ≤ Real.log n := Real.log_le_log hp0 hpnr
    have hlp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast (show 1 ≤ p by omega))
    nlinarith
  · have l2 := log_two_gt
    have hl4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have hl8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    interval_cases n
    all_goals try (norm_num at hp; done)
    · have := a_le (n := 4) (q := 5) (by norm_num) (by norm_num)
      have h : (a 4 : ℝ) ≤ 5 := by exact_mod_cast this
      push_cast; rw [hl4]; nlinarith
    · have := a_le (n := 6) (q := 7) (by norm_num) (by norm_num)
      have h : (a 6 : ℝ) ≤ 7 := by exact_mod_cast this
      have : Real.log 4 ≤ Real.log 6 := Real.log_le_log (by norm_num) (by norm_num)
      push_cast; nlinarith
    · have := a_le (n := 8) (q := 11) (by norm_num) (by norm_num)
      have h : (a 8 : ℝ) ≤ 11 := by exact_mod_cast this
      push_cast; rw [hl8]; nlinarith
    · have := a_le (n := 9) (q := 11) (by norm_num) (by norm_num)
      have h : (a 9 : ℝ) ≤ 11 := by exact_mod_cast this
      have : Real.log 8 ≤ Real.log 9 := Real.log_le_log (by norm_num) (by norm_num)
      push_cast; nlinarith
    · have := a_le (n := 10) (q := 11) (by norm_num) (by norm_num)
      have h : (a 10 : ℝ) ≤ 11 := by exact_mod_cast this
      have : Real.log 8 ≤ Real.log 10 := Real.log_le_log (by norm_num) (by norm_num)
      push_cast; nlinarith

theorem main : H1 → H2 → type_of% @OeisA7918.conjecture2 := by
  intro h1 h2 n hn
  have h := a_lt h1 h2 n hn
  have hx : (1 : ℝ) ≤ n := by exact_mod_cast hn.le
  exact lt_of_lt_of_le h (add_log_sq_le hx)

end OMA.R_OeisA7918_conjecture2_R1
