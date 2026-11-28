import FormalConjectures.ErdosProblems.«1095»
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Choose.Lucas

/-! The moderate-range obstruction and the two counting estimates in
Konyagin's proof. We derive the rational-approximation condition from
Lucas's theorem, and use Vandermonde's identity to give an admissible
index for the Erdős–Selfridge function. -/

namespace OMA.R_Erdos1095_erdos_1095_variants_lower_solved_R1

open Filter Asymptotics
open scoped BigOperators

private theorem admissible_nonempty (k : ℕ) (hk : 0 < k) :
    {m : ℕ | k + 1 < m ∧ k < (m.choose k).minFac}.Nonempty := by
  classical
  let F := (k + 2).factorial
  let L := F * F
  have hF : 2 ≤ F := Nat.le_of_dvd (Nat.factorial_pos _) (Nat.dvd_factorial (by decide) (by omega))
  have hL : 1 < L := by dsimp [L]; nlinarith
  have hchoose : 1 < (L + k).choose k := by
    have hmon := Nat.choose_le_choose k (show k + 1 ≤ L + k by omega)
    rw [Nat.choose_succ_self_right] at hmon
    omega
  refine ⟨L + k, by omega, ?_⟩
  by_contra! hmin
  let p := ((L + k).choose k).minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpk : p ≤ k := hmin
  have hpF : p ∣ F := Nat.dvd_factorial hp.pos (by omega)
  have hterm (j : ℕ) (hj : j < k) : p ∣ L.choose (j + 1) := by
    have hjF : j + 1 ∣ F := Nat.dvd_factorial (Nat.succ_pos _) (by omega)
    have hjp : (j + 1) * p ∣ L := Nat.mul_dvd_mul hjF hpF
    have hL' : L - 1 + 1 = L := by omega
    have hidentity := Nat.add_one_mul_choose_eq (L - 1) j
    rw [hL', mul_comm (L.choose (j + 1))] at hidentity
    apply Nat.dvd_of_mul_dvd_mul_left (Nat.succ_pos j)
    rw [← hidentity]
    exact dvd_mul_of_dvd_left hjp _
  have hexpand :
      (L + k).choose k = (∑ j ∈ Finset.range k, L.choose (j + 1) * k.choose (k - (j + 1))) + 1 := by
    rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ']
    simp
  have hsum : p ∣ ∑ j ∈ Finset.range k, L.choose (j + 1) * k.choose (k - (j + 1)) := by
    apply Finset.dvd_sum
    intro j hj
    exact dvd_mul_of_dvd_left (hterm j (Finset.mem_range.mp hj)) _
  have hdvd : p ∣ (L + k).choose k := Nat.minFac_dvd _
  rw [hexpand] at hdvd
  have hdvd1 : p ∣ 1 := (Nat.dvd_add_iff_right hsum).2 hdvd
  exact hp.not_dvd_one hdvd1

private theorem rational_approximation {k n p u w : ℕ} (hp : p.Prime)
    (hndvd : ¬ p ∣ n.choose k) (hu : u = w * p) (hw : k / p + 1 = w) :
    ∃ v : ℕ, n * w < v * u ∧ v * u ≤ n * w + w * (u - k) := by
  have hdigit : k % p ≤ n % p := by
    by_contra! h
    let _ : Fact p.Prime := ⟨hp⟩
    have hmod := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := n) (k := k) (p := p)
    rw [Nat.choose_eq_zero_of_lt h, zero_mul] at hmod
    exact hndvd (Nat.dvd_of_mod_eq_zero (by simpa [Nat.ModEq] using hmod))
  have hk := Nat.mod_add_div k p
  have hn := Nat.mod_add_div n p
  have hlt := Nat.mod_lt n hp.pos
  let v := n / p + 1
  have hv : v * p = n + (p - n % p) := by
    dsimp [v]
    rw [Nat.add_mul, one_mul, mul_comm (n / p)]
    omega
  have hk' : u = k + (p - k % p) := by
    rw [hu, ← hw, Nat.add_mul, one_mul, mul_comm (k / p)]
    have := Nat.mod_lt k hp.pos
    omega
  refine ⟨v, ?_, ?_⟩
  · have hwpos : 0 < w := hw ▸ Nat.succ_pos (k / p)
    have hnv : n < v * p := by omega
    calc
      n * w = w * n := Nat.mul_comm _ _
      _ < w * (v * p) := Nat.mul_lt_mul_of_pos_left hnv hwpos
      _ = v * u := by rw [hu, mul_left_comm]
  · have hnv : v * p ≤ n + (u - k) := by omega
    calc
      v * u = w * (v * p) := by rw [hu, mul_left_comm]
      _ ≤ w * (n + (u - k)) := Nat.mul_le_mul_left w hnv
      _ = n * w + w * (u - k) := by rw [Nat.mul_add, mul_comm w n]

/-- Small-prime divisibility below the cubic threshold. -/
def H1 : Prop :=
  ∀ᶠ k : ℕ in atTop, ∀ n : ℕ, k + 1 < n → n < k ^ 3 →
    ∃ p : ℕ, p.Prime ∧ p ≤ k ∧ p ∣ n.choose k

/-- A short interval contains many multiples of primes with small multipliers. -/
def H2 : Prop :=
  ∃ d : ℝ, 0 < d ∧ ∀ᶠ k : ℕ in atTop, ∃ U : Finset ℕ,
    d * (k : ℝ) ^ (3 / 4 : ℝ) ≤ U.card ∧
    ∀ u ∈ U, k < u ∧ (u : ℝ) ≤ k + (k : ℝ) ^ (3 / 4 : ℝ) ∧
      ∃ p w : ℕ, p.Prime ∧ p ≤ k ∧ 2 ≤ w ∧
        (w : ℝ) ≤ (k : ℝ) ^ (1 / 40 : ℝ) ∧ u = w * p ∧ k / p + 1 = w

/-- For subexponential n in the long range, too few nearby u admit
a rational approximation from above with a small denominator. -/
def H3 : Prop :=
  ∀ d : ℝ, 0 < d → ∃ c : ℝ, 0 < c ∧
    ∀ᶠ k : ℕ in atTop, ∀ n : ℕ, k ^ 3 ≤ n →
      (n : ℝ) < Real.exp (c * Real.log k ^ 2) →
      ∀ U : Finset ℕ, (∀ u ∈ U, k < u ∧ (u : ℝ) ≤ k + (k : ℝ) ^ (3 / 4 : ℝ) ∧
        ∃ v w : ℕ, 2 ≤ w ∧ (w : ℝ) ≤ (k : ℝ) ^ (1 / 40 : ℝ) ∧
          n * w < v * u ∧ v * u ≤ n * w + w * (u - k)) →
        (U.card : ℝ) < d * (k : ℝ) ^ (3 / 4 : ℝ)

theorem main : H1 → H2 → H3 → type_of% @Erdos1095.erdos_1095.variants.lower_solved := by
  intro hmoderate hdense hsparse
  obtain ⟨d, hd, hdense⟩ := hdense
  obtain ⟨c, hc, hsparse⟩ := hsparse d hd
  refine ⟨c, hc, IsBigO.of_bound 1 ?_⟩
  filter_upwards [hmoderate, hdense, hsparse, eventually_ge_atTop (1 : ℕ)] with k hm hdense hsparse hk
  have hmem : Erdos1095.g k ∈ {m : ℕ | k + 1 < m ∧ k < (m.choose k).minFac} :=
    Nat.sInf_mem (admissible_nonempty k hk)
  obtain ⟨hg, hfac⟩ := hmem
  have hbound : Real.exp (c * Real.log k ^ 2) ≤ (Erdos1095.g k : ℝ) := by
    by_contra! hs
    let n := Erdos1095.g k
    have hn (p : ℕ) (hp : p.Prime) (hpk : p ≤ k) : ¬ p ∣ n.choose k := fun hpd ↦
      (not_le_of_gt hfac) ((Nat.minFac_le_of_dvd hp.two_le hpd).trans hpk)
    by_cases hcut : n < k ^ 3
    · obtain ⟨p, hp, hpk, hpd⟩ := hm n hg hcut
      exact hn p hp hpk hpd
    · obtain ⟨U, hcard, hU⟩ := hdense
      apply (not_lt_of_ge hcard)
      apply hsparse n (Nat.le_of_not_gt hcut) hs U
      intro u hu
      obtain ⟨hku, hub, p, w, hp, hpk, hw, hwb, hprod, hquot⟩ := hU u hu
      obtain ⟨v, hv, hv'⟩ := rational_approximation hp (hn p hp hpk) hprod hquot
      exact ⟨hku, hub, v, w, hw, hwb, hv, hv'⟩
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _), one_mul] using hbound

end OMA.R_Erdos1095_erdos_1095_variants_lower_solved_R1
