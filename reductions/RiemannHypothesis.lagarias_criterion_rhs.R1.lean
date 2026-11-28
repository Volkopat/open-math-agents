import FormalConjectures.Paper.RiemannHypothesisEquivalents

-- Reduction RiemannHypothesis.lagarias_criterion_rhs.R1 of Lagarias' inequality
-- Credit: @pyaf
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Lagarias' inequality from Robin's theorem

J. C. Lagarias, An elementary problem equivalent to the Riemann hypothesis, Amer. Math. Monthly
109 (2002), 534–543, deduces his inequality from Robin's.

* `H1`: the Riemann Hypothesis (as in the merged reduction `Erdos462.erdos_462.R1`).
* `H2`: Robin's theorem (G. Robin, Grandes valeurs de la fonction somme des diviseurs et hypothèse
  de Riemann, J. Math. Pures Appl. 63 (1984), 187–213): under the Riemann Hypothesis,
  `σ(n) < e^γ n log log n` for every `n > 5040`.
* `H3`: Lagarias' inequality for `1 < n ≤ 5040`, a finite computation.

Proved here: for `n > 5040`, `H_n > log n + γ` gives `e^{H_n} > e^γ n` and
`log H_n > log log n > 0`, so Robin's bound is below `H_n + e^{H_n} log H_n`.
-/

namespace OMA.R_RiemannHypothesis_lagarias_criterion_rhs_R1

open Real
open scoped ArithmeticFunction.sigma

/-- The Riemann Hypothesis. -/
def H1 : Prop := RiemannHypothesis

/-- Robin's theorem: the Riemann Hypothesis implies Robin's inequality for `n > 5040`. -/
def H2 : Prop :=
  RiemannHypothesis → ∀ n : ℕ, n > 5040 →
    σ 1 n < exp eulerMascheroniConstant * n * log (log n)

/-- Lagarias' inequality in the finite range `1 < n ≤ 5040`. -/
def H3 : Prop :=
  ∀ n : ℕ, 1 < n → n ≤ 5040 → σ 1 n < harmonic n + exp (harmonic n) * log (harmonic n)

lemma robin_le_lagarias {n : ℕ} (hn : 5040 < n) :
    exp eulerMascheroniConstant * n * log (log n) <
      harmonic n + exp (harmonic n) * log (harmonic n) := by
  have hn0 : n ≠ 0 := by omega
  have hγ := eulerMascheroniConstant_lt_eulerMascheroniSeq' n
  rw [eulerMascheroniSeq', if_neg hn0] at hγ
  have hγ0 : 0 < eulerMascheroniConstant := one_half_lt_eulerMascheroniConstant.trans' (by norm_num)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hlog1 : 1 < log n := by
    rw [lt_log_iff_exp_lt hnpos]
    have : exp 1 < 3 := exp_one_lt_d9.trans (by norm_num)
    have : (3 : ℝ) < n := by exact_mod_cast (by omega : 3 < n)
    linarith
  have hll : 0 < log (log n) := log_pos hlog1
  have hH : log n + eulerMascheroniConstant < harmonic n := by linarith
  have hHpos : (0 : ℝ) < harmonic n := by linarith
  have hexp : exp eulerMascheroniConstant * n < exp (harmonic n) := by
    calc exp eulerMascheroniConstant * n = exp (log n + eulerMascheroniConstant) := by
          rw [exp_add, exp_log hnpos, mul_comm]
      _ < exp (harmonic n) := exp_lt_exp.mpr hH
  have hlogH : log (log n) < log (harmonic n) := log_lt_log (by linarith) (by linarith)
  calc exp eulerMascheroniConstant * n * log (log n)
      < exp (harmonic n) * log (harmonic n) :=
        mul_lt_mul hexp hlogH.le hll (exp_pos _).le
    _ < harmonic n + exp (harmonic n) * log (harmonic n) := by linarith

theorem main : H1 → H2 → H3 → type_of% @RiemannHypothesis.lagarias_criterion_rhs := by
  intro h1 h2 h3 n hn
  by_cases hs : n ≤ 5040
  · exact h3 n hn hs
  · exact (h2 h1 n (by omega)).trans (robin_le_lagarias (by omega))

end OMA.R_RiemannHypothesis_lagarias_criterion_rhs_R1
