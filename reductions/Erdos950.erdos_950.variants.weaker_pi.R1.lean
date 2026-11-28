import FormalConjectures.ErdosProblems.«950»

/-!
# The weaker conjecture on π follows from f(n) = o(log log n)

Suppose that x violates the conjecture for ε: every y < x has π(x) ≥ π(y) + ε π(x - y). Then each
window (x - k, x] with 1 ≤ k ≤ x holds at least ε π(k) primes. Partial summation against the
decreasing weights 1 / j turns this into f(x + 1) ≥ ε ∑_{p ≤ x} 1 / p. By Mertens the right side
is at least ε (log log x - C), which contradicts f(x + 1) ≤ (ε / 2) log log (x + 1) for large x.

H1 is part (iii) of Erdős Problem 950 (open). H2 is the lower half of the second theorem of
Mertens (1874), a known elementary estimate that Mathlib does not have.

Source: Erdős, Problems and results on combinatorial number theory III, Number theory day
(Proc. Conf., Rockefeller Univ., New York, 1976), 43-72, and erdosproblems.com/950.
-/
-- Reduction Erdos950.erdos_950.variants.weaker_pi.R1 of Erdős Problem 950
-- Credit: @LordMike

open Filter Finset
open scoped Asymptotics Nat.Prime

namespace OMA.R_Erdos950_erdos_950_variants_weaker_pi_R1

/-- Part (iii) of Erdős Problem 950: f(n) = o(log log n). -/
def H1 : Prop := Erdos950.f =o[atTop] (fun n : ℕ ↦ Real.log (Real.log n))

/-- Mertens: the sum of 1 / p over the primes p ≤ x is at least log log x - C. -/
def H2 : Prop := ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x →
    Real.log (Real.log x) - C ≤ ∑ p ∈ (range (x + 1)).filter Nat.Prime, (1 : ℝ) / p

/-- Partial summation: nonnegative partial sums stay nonnegative under the weights 1 / j. -/
lemma abel (d : ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N)
    (h : ∀ k, 1 ≤ k → k ≤ N → 0 ≤ ∑ j ∈ Icc 1 k, d j) :
    (∑ j ∈ Icc 1 N, d j) / N ≤ ∑ j ∈ Icc 1 N, d j / j := by
  induction N with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have ih' := ih hn (fun k hk hkn ↦ h k hk (by omega))
      have hD := h n hn (by omega)
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      rw [sum_Icc_succ_top (by omega), sum_Icc_succ_top (by omega)]
      have h1 : (∑ j ∈ Icc 1 n, d j) / ((n : ℝ) + 1) ≤ (∑ j ∈ Icc 1 n, d j) / n :=
        div_le_div_of_nonneg_left hD hn' (by linarith)
      push_cast
      rw [add_div]
      linarith

lemma pi_succ (m : ℕ) : π (m + 1) = π m + if (m + 1).Prime then 1 else 0 := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_succ]
  rfl

lemma sum_prime_ind (k : ℕ) :
    (∑ j ∈ Icc 1 k, (if j.Prime then (1 : ℝ) else 0)) = π k := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega), ih, pi_succ]
    push_cast
    rfl

lemma sum_window (x k : ℕ) (hk : k ≤ x) :
    (∑ j ∈ Icc 1 k, (if (x + 1 - j).Prime then (1 : ℝ) else 0)) = (π x : ℝ) - π (x - k) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega), ih (by omega)]
    have h := pi_succ (x - (n + 1))
    rw [show x - (n + 1) + 1 = x - n by omega] at h
    rw [show x + 1 - (n + 1) = x - n by omega, h]
    push_cast
    ring

lemma f_succ (x : ℕ) :
    Erdos950.f (x + 1) = ∑ j ∈ Icc 1 x, (if (x + 1 - j).Prime then (1 : ℝ) else 0) / j := by
  unfold Erdos950.f
  have hite : ∀ j ∈ Icc 1 x, (if (x + 1 - j).Prime then (1 : ℝ) else 0) / j =
      if (x + 1 - j).Prime then (1 : ℝ) / j else 0 := by
    intro j _
    split_ifs <;> simp
  rw [sum_congr rfl hite, ← sum_filter]
  refine sum_nbij' (fun p ↦ x + 1 - p) (fun j ↦ x + 1 - j) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [mem_filter, mem_range, mem_Icc] at hp ⊢
    have h2 := hp.2.nat_prime.two_le
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [show x + 1 - (x + 1 - p) = p by omega]
    exact hp.2.nat_prime
  · intro j hj
    simp only [mem_filter, mem_range, mem_Icc] at hj ⊢
    exact ⟨by omega, hj.2.prime⟩
  · intro p hp
    simp only [mem_filter, mem_range] at hp
    omega
  · intro j hj
    simp only [mem_filter, mem_Icc] at hj
    omega
  · intro p hp
    simp only [mem_filter, mem_range] at hp
    rw [Nat.cast_sub (by omega)]

lemma sum_inv_primes (x : ℕ) :
    (∑ j ∈ Icc 1 x, (if j.Prime then (1 : ℝ) else 0) / j) =
      ∑ p ∈ (range (x + 1)).filter Nat.Prime, (1 : ℝ) / p := by
  have hite : ∀ j ∈ Icc 1 x, (if j.Prime then (1 : ℝ) else 0) / j =
      if j.Prime then (1 : ℝ) / j else 0 := by
    intro j _
    split_ifs <;> simp
  rw [sum_congr rfl hite, ← sum_filter]
  congr 1
  ext p
  simp only [mem_filter, mem_Icc, mem_range]
  constructor
  · rintro ⟨⟨_, h⟩, hp⟩
    exact ⟨by omega, hp⟩
  · rintro ⟨h, hp⟩
    exact ⟨⟨hp.one_lt.le, by omega⟩, hp⟩

/-- A violation at x forces f(x + 1) to dominate the sum of the prime reciprocals up to x. -/
lemma key (ε : ℝ) (x : ℕ) (hx : 1 ≤ x)
    (h : ∀ y < x, (π y : ℝ) + ε * (π (x - y) : ℝ) ≤ (π x : ℝ)) :
    ε * ∑ p ∈ (range (x + 1)).filter Nat.Prime, (1 : ℝ) / p ≤ Erdos950.f (x + 1) := by
  have hD : ∀ k, 1 ≤ k → k ≤ x → 0 ≤ ∑ j ∈ Icc 1 k,
      ((if (x + 1 - j).Prime then (1 : ℝ) else 0) - ε * (if j.Prime then (1 : ℝ) else 0)) := by
    intro k hk1 hkx
    rw [sum_sub_distrib, ← mul_sum, sum_window x k hkx, sum_prime_ind]
    have := h (x - k) (by omega)
    rw [show x - (x - k) = k by omega] at this
    linarith
  have h1 := abel _ x hx hD
  have h0 := div_nonneg (hD x hx le_rfl) (Nat.cast_nonneg (α := ℝ) x)
  have h2 : ∑ j ∈ Icc 1 x,
      ((if (x + 1 - j).Prime then (1 : ℝ) else 0) - ε * (if j.Prime then (1 : ℝ) else 0)) / j =
      Erdos950.f (x + 1) - ε * ∑ p ∈ (range (x + 1)).filter Nat.Prime, (1 : ℝ) / p := by
    rw [f_succ, ← sum_inv_primes, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun j _ ↦ ?_
    ring
  linarith

theorem main : H1 → H2 → type_of% @Erdos950.erdos_950.variants.weaker_pi := by
  intro h1 h2 ε hε
  obtain ⟨C, hC⟩ := h2
  have hll : Tendsto (fun x : ℕ ↦ Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have e1 : ∀ᶠ x : ℕ in atTop, ‖Erdos950.f (x + 1)‖ ≤
      ε / 2 * ‖Real.log (Real.log ((x + 1 : ℕ) : ℝ))‖ :=
    (tendsto_add_atTop_nat 1).eventually (Asymptotics.IsLittleO.def h1 (half_pos hε))
  have e3 : ∀ᶠ x : ℕ in atTop, 2 * C + 1 < Real.log (Real.log x) :=
    hll.eventually (eventually_gt_atTop _)
  have e4 : ∀ᶠ x : ℕ in atTop, 0 ≤ Real.log (Real.log ((x + 1 : ℕ) : ℝ)) :=
    (tendsto_add_atTop_nat 1).eventually (hll.eventually (eventually_ge_atTop 0))
  filter_upwards [e1, e3, e4, eventually_ge_atTop 2] with x hx1 hx3 hx4 hx2
  by_contra hne
  push Not at hne
  have hk := key ε x (by omega) hne
  have hm := hC x hx2
  have hx' : (2 : ℝ) ≤ x := by exact_mod_cast hx2
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hpos : 0 < Real.log ((x + 1 : ℕ) : ℝ) := Real.log_pos (by push_cast; linarith)
  have hle : Real.log ((x + 1 : ℕ) : ℝ) ≤ 2 * Real.log x := by
    have h := Real.log_le_log (show (0 : ℝ) < ((x + 1 : ℕ) : ℝ) by positivity)
      (show ((x + 1 : ℕ) : ℝ) ≤ (x : ℝ) ^ 2 by push_cast; nlinarith)
    rw [Real.log_pow] at h
    exact_mod_cast h
  have hup : Real.log (Real.log ((x + 1 : ℕ) : ℝ)) ≤ Real.log (Real.log x) + 1 := by
    calc Real.log (Real.log ((x + 1 : ℕ) : ℝ)) ≤ Real.log (2 * Real.log x) :=
          Real.log_le_log hpos hle
      _ = Real.log 2 + Real.log (Real.log x) := Real.log_mul (by norm_num) hlogx.ne'
      _ ≤ Real.log (Real.log x) + 1 := by
          have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
          linarith
  rw [Real.norm_of_nonneg hx4] at hx1
  have hf := Real.le_norm_self (Erdos950.f (x + 1))
  have ha := mul_le_mul_of_nonneg_left hm hε.le
  have hb := mul_le_mul_of_nonneg_left hup (half_pos hε).le
  nlinarith [mul_pos hε (sub_pos.mpr hx3)]

end OMA.R_Erdos950_erdos_950_variants_weaker_pi_R1
