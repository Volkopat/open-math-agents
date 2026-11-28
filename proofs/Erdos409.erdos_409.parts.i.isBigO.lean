import FormalConjectures.ErdosProblems.«409»
import Mathlib

/-! A square-root upper bound for the prime hitting time of the totient iteration. -/

namespace OMA.Erdos409Bound

open Filter

-- Multiples of a prime factor cannot contribute to Euler's totient.
theorem totient_add_quotient_le (p q : ℕ) (hp : p.Prime) :
    (p * q).totient + q ≤ p * q := by
  let s := Finset.range (p * q)
  let t := s.filter (fun k => (p * q).Coprime k)
  let u := (Finset.range q).image (fun k => p * k)
  have hu : u.card = q := by
    unfold u
    rw [Finset.card_image_of_injective, Finset.card_range]
    exact fun x y h => Nat.eq_of_mul_eq_mul_left hp.pos h
  have huSub : u ⊆ s := by
    intro k hk
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_range.mpr (Nat.mul_lt_mul_of_pos_left (Finset.mem_range.mp hr) hp.pos)
  have hdis : Disjoint t u := by
    apply Finset.disjoint_left.mpr
    intro k hkt hku
    have hc : (p * q).Coprime k := (Finset.mem_filter.mp hkt).2
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hku
    have hd := Nat.dvd_gcd (dvd_mul_right p q) (dvd_mul_right p r)
    rw [hc.gcd_eq_one] at hd
    exact hp.ne_one (Nat.dvd_one.mp hd)
  have h := Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) huSub : t ∪ u ⊆ s)
  rw [Finset.card_union_of_disjoint hdis, hu] at h
  simpa [s, t, Nat.totient] using h

abbrev next (n : ℕ) : ℕ := n.totient + 1

theorem sqrt_decrease (n : ℕ) (hn : 4 ≤ n) (hprime : ¬ n.Prime) :
    Real.sqrt (next n : ℝ) ≤ Real.sqrt (n : ℝ) - 1 / 4 := by
  let p := n.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  obtain ⟨q, hq⟩ : p ∣ n := Nat.minFac_dvd n
  have hpSq : p ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hprime
  have hpq : p ≤ q := by
    rw [hq, pow_two] at hpSq
    exact Nat.le_of_mul_le_mul_left hpSq hp.pos
  have hnSq : n ≤ q ^ 2 := by
    rw [hq, pow_two]
    exact Nat.mul_le_mul_right q hpq
  have hroot : Real.sqrt (n : ℝ) ≤ (q : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity, by exact_mod_cast hnSq⟩
  have hdec : n.totient + q ≤ n := by
    rw [hq]
    exact totient_add_quotient_le p q hp
  have hdecReal : (n.totient : ℝ) + q ≤ (n : ℝ) := by exact_mod_cast hdec
  have h2 : (2 : ℝ) ≤ Real.sqrt (n : ℝ) := Real.le_sqrt_of_sq_le (by exact_mod_cast hn)
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) by positivity)
  apply Real.sqrt_le_iff.mpr
  push_cast
  constructor <;> nlinarith

theorem step_bound (c : ℕ → ℕ)
    (hc : ∀ n > 0, IsLeast {i | (next^[i] n).Prime} (c n))
    (n : ℕ) (hn : 0 < n) : c n ≤ c (next n) + 1 := by
  apply (hc n hn).2
  change (next^[c (next n) + 1] n).Prime
  rw [Function.iterate_succ_apply]
  exact (hc (next n) (by positivity)).1

theorem bound (c : ℕ → ℕ)
    (hc : ∀ n > 0, IsLeast {i | (next^[i] n).Prime} (c n))
    (n : ℕ) (hn : 0 < n) : (c n : ℝ) ≤ 4 * Real.sqrt (n : ℝ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hp : n.Prime
    · have h : c n = 0 := Nat.eq_zero_of_le_zero ((hc n hn).2 (by simpa using hp))
      simp [h]
    by_cases h1 : n = 1
    · subst n
      have h : c 1 ≤ 1 := (hc 1 (by decide)).2 (by decide)
      have h' : (c 1 : ℝ) ≤ 1 := by exact_mod_cast h
      norm_num
      linarith
    have hn4 : 4 ≤ n := by
      by_contra! h
      obtain rfl | rfl | rfl : n = 1 ∨ n = 2 ∨ n = 3 := by omega
      · exact h1 rfl
      · exact hp Nat.prime_two
      · exact hp Nat.prime_three
    have hh := sqrt_decrease n hn4 hp
    have hlt : next n < n := by
      by_contra! hh'
      have hmono := Real.sqrt_le_sqrt (show (n : ℝ) ≤ (next n : ℝ) by exact_mod_cast hh')
      linarith
    have hi := ih (next n) hlt (by positivity)
    have hstep : (c n : ℝ) ≤ (c (next n) : ℝ) + 1 := by exact_mod_cast step_bound c hc n hn
    linarith

end OMA.Erdos409Bound

open Filter Asymptotics

noncomputable def OMA.answer : ℕ → ℝ := fun n => Real.sqrt n

theorem OMA.solution : Erdos409.erdos_409.parts.i.isBigO.answer = OMA.answer →
    type_of% @Erdos409.erdos_409.parts.i.isBigO := by
  intro h
  rw [h]
  intro c hc
  refine Asymptotics.IsBigO.of_bound 4 ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  simp only [OMA.answer, Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ (c n : ℝ) from Nat.cast_nonneg _),
    abs_of_nonneg (Real.sqrt_nonneg (n : ℝ))]
  exact OMA.Erdos409Bound.bound c hc n (by omega)
