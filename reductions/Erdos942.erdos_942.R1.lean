import FormalConjectures.ErdosProblems.«942»
import Mathlib

namespace OMA.R_Erdos942_erdos_942_R1

open Filter Asymptotics Set Erdos942

-- Upper half of the two-sided exponent problem: existence of a constant and a
-- little-o error giving an exponent c + o1(n) above which h(n) eventually lies.
def H1 : Prop :=
  ∃ c > 0, ∃ o1 : ℕ → ℝ, o1 =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ᶠ n : ℕ in atTop, erdos_942.h n < (Real.log n) ^ (c + o1 n)

-- Lower half at the *same* constant: every admissible upper exponent estimate
-- forces infinitely many n where h(n) exceeds (log n)^(c - o2(n)). This is the
-- genuine extremal/lower-bound problem for powerful integers in short intervals;
-- it quantifies over all admissible (c, o1) and produces its own error term o2.
def H2 : Prop :=
  ∀ c > 0, ∀ o1 : ℕ → ℝ, o1 =o[atTop] (1 : ℕ → ℝ) →
    (∀ᶠ n : ℕ in atTop, erdos_942.h n < (Real.log n) ^ (c + o1 n)) →
    ∃ o2 : ℕ → ℝ, o2 =o[atTop] (1 : ℕ → ℝ) ∧
      {n | erdos_942.h n > (Real.log n) ^ (c - o2 n)}.Infinite

theorem main : H1 → H2 → type_of% @Erdos942.erdos_942 := by
  intro h1 h2
  rcases h1 with ⟨c, hc, o1, ho1, hup⟩
  rcases h2 c hc o1 ho1 hup with ⟨o2, ho2, hinf⟩
  let o : ℕ → ℝ := fun n => |o1 n| + |o2 n|
  have hz1 : ∀ x : ℕ, ((1 : ℕ → ℝ) x) = 0 → o1 x = 0 := by
    intro x hx
    norm_num at hx
  have hz2 : ∀ x : ℕ, ((1 : ℕ → ℝ) x) = 0 → o2 x = 0 := by
    intro x hx
    norm_num at hx
  have ht1 : Tendsto o1 atTop (nhds 0) := by
    have h := (Asymptotics.isLittleO_iff_tendsto hz1).mp ho1
    simpa using h
  have ht2 : Tendsto o2 atTop (nhds 0) := by
    have h := (Asymptotics.isLittleO_iff_tendsto hz2).mp ho2
    simpa using h
  have hotend : Tendsto o atTop (nhds 0) := by
    simpa [o] using ht1.abs.add ht2.abs
  have ho : o =o[atTop] (1 : ℕ → ℝ) := by
    rw [Asymptotics.isLittleO_iff_tendsto]
    · simpa using hotend
    · intro x hx
      norm_num at hx
  have hlog_tend : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hlog_ev : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ Real.log (n : ℝ) :=
    hlog_tend.eventually (Filter.eventually_ge_atTop (1 : ℝ))
  rcases (Filter.eventually_atTop.1 hlog_ev) with ⟨N, hN⟩
  have hupper : ∀ᶠ n : ℕ in atTop, erdos_942.h n < (Real.log n) ^ (c + o n) := by
    filter_upwards [hup, hlog_ev] with n hhn hbase
    have hoe1 : o1 n ≤ o n := by
      dsimp [o]
      have ha : o1 n ≤ |o1 n| := le_abs_self _
      have hb : 0 ≤ |o2 n| := abs_nonneg _
      linarith
    have hpow : (Real.log n) ^ (c + o1 n) ≤ (Real.log n) ^ (c + o n) :=
      Real.rpow_le_rpow_of_exponent_le hbase (by linarith : c + o1 n ≤ c + o n)
    exact lt_of_lt_of_le hhn hpow
  have hlower : {n | erdos_942.h n > (Real.log n) ^ (c - o n)}.Infinite := by
    let S2 : Set ℕ := {n | erdos_942.h n > (Real.log n) ^ (c - o2 n)}
    let S : Set ℕ := {n | erdos_942.h n > (Real.log n) ^ (c - o n)}
    have hsub : S2 \ {n : ℕ | n < N} ⊆ S := by
      intro n hn
      rcases hn with ⟨hn2, hnN⟩
      have hbase : (1 : ℝ) ≤ Real.log (n : ℝ) := hN n (not_lt.mp hnN)
      have hoe2 : o2 n ≤ o n := by
        dsimp [o]
        have ha : o2 n ≤ |o2 n| := le_abs_self _
        have hb : 0 ≤ |o1 n| := abs_nonneg _
        linarith
      have hexp : c - o n ≤ c - o2 n := by linarith
      have hpow : (Real.log n) ^ (c - o n) ≤ (Real.log n) ^ (c - o2 n) :=
        Real.rpow_le_rpow_of_exponent_le hbase hexp
      exact lt_of_le_of_lt hpow hn2
    have hinf' : (S2 \ {n : ℕ | n < N}).Infinite := by
      have hfin : ({n : ℕ | n < N} : Set ℕ).Finite := Set.finite_lt_nat N
      have hinfS2 : S2.Infinite := by simpa [S2] using hinf
      exact hinfS2.sdiff hfin
    have hsinf : S.Infinite := Set.Infinite.mono hsub hinf'
    simpa [S] using hsinf
  exact ⟨c, hc, o, ho, hupper, hlower⟩

end OMA.R_Erdos942_erdos_942_R1
