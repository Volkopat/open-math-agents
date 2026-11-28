import OMAReductions.R_Mathoverflow339137_mathoverflow_339137_R1
import Mathlib

-- Reduction Mathoverflow339137.mathoverflow_339137.R1.H2.R1 of step Mathoverflow339137.mathoverflow_339137.R1.H2
-- Credit: @rickmanelius
-- Each H becomes its own step once this file is accepted. Proving all of them closes the step.

/-!
# The gap case of the unfair 0-1 polynomial problem: palindromic factors, degrees 5 and 6

The step asks: for normalized monic factors `P`, `Q` (nonnegative coefficients, constant terms
`1`, `5 ≤ deg P < deg Q`) whose product is a `0, 1` polynomial with a zero coefficient below its
degree, `P` is a `0, 1` polynomial.

`main` proves, with no hypothesis:

* a palindromic factor (`x^m P(1/x) = P`) is always a `0, 1` polynomial, whatever the product.
  Let `t` be the first index where `P` or `Q` has a coefficient outside `{0, 1}`; the coefficient
  of `P * Q` at `t` is `P_t + Q_t` plus a natural number, so `P_t + Q_t = 1` and both are
  positive, and `0 < t < m = deg P`. The coefficient of `P * Q` at `m` is at most `1` but
  contains `P_m Q_0 = 1` and `P_(m-t) Q_t = P_t Q_t > 0`. The same holds for `Q`, and a `0, 1`
  factor `Q` forces `P` to be `0, 1` (a lemma of the reduction `R1`). Every factor of a
  polynomial dividing some `x^M - 1` is palindromic, so this covers in particular every product
  whose roots are distinct roots of unity;
* degree `5`: coefficient algebra on the coefficients `1, ..., 5` of `P * Q`, with the reversal
  symmetry, shows that `P_1` and `P_4` are `0` or `1`, and that a coefficient `P_2` (or `P_3`)
  outside `{0, 1}` forces `P = 1 + b x^2 + x^5` (or its reversal `1 + b x^3 + x^5`) with
  `0 < b < 1`. So in degree `5` only the trinomial family is left;
* degree `6`, completely: the coefficients `1, ..., 8` of `P * Q` and the reversal give `P_1`,
  `P_5` in `{0, 1}` (the case `0 < P_1 < 1` splits by which of `Q_2`, `P_2`, `P_3` vanish; two
  branches force an algebraic value of `P_1`, a root of `2a^3 - 4a^2 + 5a - 1` or of
  `2a^3 - 2a^2 + 3a - 2`, and then the coefficient at `7` or `8` exceeds `1`), then `P_2`, `P_4`
  in `{0, 1}`, and `P_3` in `{0, 1}` because `P_3 Q_3` is a term of the middle coefficient `6`.

What is left:

* `H1`: no trinomial `1 + b x^2 + x^5` with `0 < b < 1` has a monic nonnegative cofactor making
  a `0, 1` product with a zero coefficient below its degree (a product without such a gap is an
  interval, the case `H1` of `R1`). Secondary sources credit this family to Ghidelli; not checked
  against the original;
* `H2`: factors of degree at least `7`, both not palindromic (the open core).
-/

open Polynomial Finset

namespace OMA.R_Mathoverflow339137_mathoverflow_339137_R1_H2_R1

open Mathoverflow339137

/-- The trinomial family `1 + b x^2 + x^5`, `0 < b < 1`: with a monic nonnegative cofactor
(constant term `1`, degree above `5`) the product is never a `0, 1` polynomial with a zero
coefficient below its degree. -/
def H1 : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 → ∀ Q : ℝ[X], Q.Monic → (∀ n, 0 ≤ Q.coeff n) → Q.coeff 0 = 1 →
    5 < Q.natDegree → IsZeroOne ((1 + C b * X ^ 2 + X ^ 5) * Q) →
    (∃ k < ((1 + C b * X ^ 2 + X ^ 5) * Q).natDegree,
      ((1 + C b * X ^ 2 + X ^ 5) * Q).coeff k = 0) → False

/-- The step for a non-palindromic pair whose smaller factor has degree at least `7`. -/
def H2 : Prop :=
  ∀ P Q : ℝ[X], P.Monic → Q.Monic → (∀ n, 0 ≤ P.coeff n) → (∀ n, 0 ≤ Q.coeff n) →
    P.coeff 0 = 1 → Q.coeff 0 = 1 → 7 ≤ P.natDegree → P.natDegree < Q.natDegree →
    IsZeroOne (P * Q) → (∃ k < (P * Q).natDegree, (P * Q).coeff k = 0) →
    P.reverse ≠ P → Q.reverse ≠ Q → IsZeroOne P

/-- The coefficient of `P * Q` at `t ≥ 1`: the two end terms plus the inner terms. -/
lemma coeff_split (P Q : ℝ[X]) {t : ℕ} (ht : t ≠ 0) :
    (P * Q).coeff t = P.coeff 0 * Q.coeff t + P.coeff t * Q.coeff 0 +
      ∑ x ∈ ((antidiagonal t).erase (0, t)).erase (t, 0), P.coeff x.1 * Q.coeff x.2 := by
  have ha : ((0 : ℕ), t) ∈ antidiagonal t := mem_antidiagonal.mpr (zero_add t)
  have hb : (t, (0 : ℕ)) ∈ (antidiagonal t).erase (0, t) := by
    refine Finset.mem_erase.mpr ⟨?_, mem_antidiagonal.mpr (add_zero t)⟩
    intro h
    have := congrArg Prod.fst h
    simp only at this
    exact ht this
  rw [coeff_mul, ← Finset.add_sum_erase _ _ ha, ← Finset.add_sum_erase _ _ hb]
  ring

/-- A palindromic normalized factor of a `0, 1` polynomial is a `0, 1` polynomial. -/
lemma zero_one_of_palindromic {P Q : ℝ[X]} (hP : P.Monic) (hQ : Q.Monic)
    (hp : ∀ n, 0 ≤ P.coeff n) (hq : ∀ n, 0 ≤ Q.coeff n) (hp0 : P.coeff 0 = 1)
    (hq0 : Q.coeff 0 = 1) (hR : ∀ n, (P * Q).coeff n = 0 ∨ (P * Q).coeff n = 1)
    (hpal : P.reverse = P) : ∀ n, P.coeff n = 0 ∨ P.coeff n = 1 := by
  have hRQ : ∀ n, (Q * P).coeff n = 0 ∨ (Q * P).coeff n = 1 := by
    rw [mul_comm]
    exact hR
  have hP1 := OMA.R_Mathoverflow339137_mathoverflow_339137_R1.coeff_le_one hQ hp hq hR
  have hQ1 := OMA.R_Mathoverflow339137_mathoverflow_339137_R1.coeff_le_one hP hq hp hRQ
  obtain ⟨-, -, -, hcr⟩ := OMA.R_Mathoverflow339137_mathoverflow_339137_R1.rev_facts hP hp0
  have hsym : ∀ i ≤ P.natDegree, P.coeff i = P.coeff (P.natDegree - i) := by
    intro i hi
    rw [← hcr i hi, hpal]
  by_contra hcon
  have hex : ∃ t, ¬ ((P.coeff t = 0 ∨ P.coeff t = 1) ∧ (Q.coeff t = 0 ∨ Q.coeff t = 1)) := by
    by_contra hall
    push_neg at hall
    exact hcon fun n => (hall n).1
  classical
  set t := Nat.find hex with ht_def
  have ht : ¬ ((P.coeff t = 0 ∨ P.coeff t = 1) ∧ (Q.coeff t = 0 ∨ Q.coeff t = 1)) :=
    Nat.find_spec hex
  have hbelow : ∀ i < t, (P.coeff i = 0 ∨ P.coeff i = 1) ∧ (Q.coeff i = 0 ∨ Q.coeff i = 1) := by
    intro i hi
    exact not_not.mp (Nat.find_min hex hi)
  have ht0 : t ≠ 0 := by
    intro h0
    apply ht
    rw [h0, hp0, hq0]
    exact ⟨Or.inr rfl, Or.inr rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : ℕ,
      ∑ x ∈ ((antidiagonal t).erase (0, t)).erase (t, 0), P.coeff x.1 * Q.coeff x.2 = s := by
    apply OMA.R_Mathoverflow339137_mathoverflow_339137_R1.sum_nat
    intro x hx
    have hx1 := Finset.mem_erase.mp hx
    have hx2 := Finset.mem_erase.mp hx1.2
    have hx3 := mem_antidiagonal.mp hx2.2
    have hne1 : x.1 ≠ 0 := by
      intro h0
      apply hx2.1
      exact Prod.ext h0 (by show x.2 = t; omega)
    have hne2 : x.2 ≠ 0 := by
      intro h0
      apply hx1.1
      exact Prod.ext (by show x.1 = t; omega) h0
    have hlt1 : x.1 < t := by omega
    have hlt2 : x.2 < t := by omega
    rcases (hbelow x.1 hlt1).1 with h1 | h1 <;> rcases (hbelow x.2 hlt2).2 with h2 | h2
    exacts [⟨0, by simp [h1, h2]⟩, ⟨0, by simp [h1, h2]⟩, ⟨0, by simp [h1, h2]⟩,
      ⟨1, by simp [h1, h2]⟩]
  have hrt := hR t
  rw [coeff_split P Q ht0, hs, hp0, hq0] at hrt
  have hpt := hp t
  have hqt := hq t
  have hpt1 := hP1 t
  have hqt1 := hQ1 t
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hsum_pos : 0 < P.coeff t + Q.coeff t := by
    by_contra hle
    push_neg at hle
    have hpz : P.coeff t = 0 := by linarith
    have hqz : Q.coeff t = 0 := by linarith
    exact ht ⟨Or.inl hpz, Or.inl hqz⟩
  have hsum1 : P.coeff t + Q.coeff t = 1 := by
    rcases hrt with h | h
    · linarith
    · rcases Nat.eq_zero_or_pos s with h0 | hpos
      · rw [h0, Nat.cast_zero] at h
        linarith
      · have : (1 : ℝ) ≤ s := by exact_mod_cast hpos
        linarith
  have hpt_pos : 0 < P.coeff t := by
    by_contra hle
    push_neg at hle
    have hpz : P.coeff t = 0 := le_antisymm hle hpt
    have hq1' : Q.coeff t = 1 := by linarith
    exact ht ⟨Or.inl hpz, Or.inr hq1'⟩
  have hqt_pos : 0 < Q.coeff t := by
    by_contra hle
    push_neg at hle
    have hqz : Q.coeff t = 0 := le_antisymm hle hqt
    have hp1' : P.coeff t = 1 := by linarith
    exact ht ⟨Or.inr hp1', Or.inl hqz⟩
  have htm : t < P.natDegree := by
    by_contra hle
    push_neg at hle
    rcases eq_or_lt_of_le hle with heq | hlt'
    · have h1 : P.coeff t = 1 := by
        rw [← heq]
        exact hP.coeff_natDegree
      have hq0' : Q.coeff t = 0 := by linarith
      exact ht ⟨Or.inr h1, Or.inl hq0'⟩
    · have h1 : P.coeff t = 0 := coeff_eq_zero_of_natDegree_lt hlt'
      linarith
  have hPm : P.coeff P.natDegree = 1 := hP.coeff_natDegree
  have hsymt : P.coeff (P.natDegree - t) = P.coeff t := (hsym t htm.le).symm
  have hmem1 : (P.natDegree, (0 : ℕ)) ∈ antidiagonal P.natDegree :=
    mem_antidiagonal.mpr (add_zero _)
  have hmem2 : (P.natDegree - t, t) ∈ antidiagonal P.natDegree :=
    mem_antidiagonal.mpr (by omega)
  have hne : (P.natDegree, (0 : ℕ)) ≠ (P.natDegree - t, t) := by
    intro h
    have := congrArg Prod.snd h
    simp only at this
    omega
  have hsub : ({(P.natDegree, (0 : ℕ)), (P.natDegree - t, t)} : Finset (ℕ × ℕ)) ⊆
      antidiagonal P.natDegree := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hmem1
    · exact hmem2
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun x : ℕ × ℕ => P.coeff x.1 * Q.coeff x.2) (fun x _ _ => mul_nonneg (hp _) (hq _))
  rw [Finset.sum_pair hne, ← coeff_mul] at hle
  simp only at hle
  rw [hPm, hq0, hsymt] at hle
  have hRm : (P * Q).coeff P.natDegree ≤ 1 := by
    rcases hR P.natDegree with h | h <;> linarith
  have hprod : 0 < P.coeff t * Q.coeff t := mul_pos hpt_pos hqt_pos
  linarith

-- Degree 5

lemma c5 (P Q : ℝ[X]) :
    (P * Q).coeff 5 = P.coeff 0 * Q.coeff 5 + P.coeff 1 * Q.coeff 4 + P.coeff 2 * Q.coeff 3 +
      P.coeff 3 * Q.coeff 2 + P.coeff 4 * Q.coeff 1 + P.coeff 5 * Q.coeff 0 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

/-- Degree 5, first coefficient: `P = 1 + p1 x + p2 x^2 + p3 x^3 + p4 x^4 + x^5` forces `p1` to
be `0` or `1`. -/
lemma five_p1 {p1 p2 p3 p4 q1 q2 q3 q4 q5 : ℝ} (hp1 : 0 ≤ p1) (hp1' : p1 ≤ 1) (hp2 : 0 ≤ p2)
    (hp3 : 0 ≤ p3) (hp3' : p3 ≤ 1) (hp4 : 0 ≤ p4) (hq1 : 0 ≤ q1) (hq2 : 0 ≤ q2) (hq3 : 0 ≤ q3)
    (hq3' : q3 ≤ 1) (hq4 : 0 ≤ q4) (hq5 : 0 ≤ q5)
    (r1 : q1 + p1 = 0 ∨ q1 + p1 = 1) (r2 : q2 + p1 * q1 + p2 = 0 ∨ q2 + p1 * q1 + p2 = 1)
    (r3 : q3 + p1 * q2 + p2 * q1 + p3 = 0 ∨ q3 + p1 * q2 + p2 * q1 + p3 = 1)
    (r4 : q4 + p1 * q3 + p2 * q2 + p3 * q1 + p4 = 0 ∨
      q4 + p1 * q3 + p2 * q2 + p3 * q1 + p4 = 1)
    (r5 : q5 + p1 * q4 + p2 * q3 + p3 * q2 + p4 * q1 + 1 = 0 ∨
      q5 + p1 * q4 + p2 * q3 + p3 * q2 + p4 * q1 + 1 = 1) :
    p1 = 0 ∨ p1 = 1 := by
  have e1 := mul_nonneg hp1 hq4
  have e2 := mul_nonneg hp2 hq3
  have e3 := mul_nonneg hp3 hq2
  have e4 := mul_nonneg hp4 hq1
  have h14 : p1 * q4 = 0 := by rcases r5 with h | h <;> linarith
  have h23 : p2 * q3 = 0 := by rcases r5 with h | h <;> linarith
  have h32 : p3 * q2 = 0 := by rcases r5 with h | h <;> linarith
  have h41 : p4 * q1 = 0 := by rcases r5 with h | h <;> linarith
  by_contra hne
  push_neg at hne
  have hapos : 0 < p1 := lt_of_le_of_ne hp1 (Ne.symm hne.1)
  have halt : p1 < 1 := lt_of_le_of_ne hp1' hne.2
  have hq1v : q1 = 1 - p1 := by rcases r1 with h | h <;> linarith
  have hq1pos : 0 < q1 := by linarith
  have hp4z : p4 = 0 := by
    rcases mul_eq_zero.mp h41 with h | h
    · exact h
    · linarith
  have hq4z : q4 = 0 := by
    rcases mul_eq_zero.mp h14 with h | h
    · linarith
    · exact h
  have hpq1 : 0 < p1 * q1 := mul_pos hapos hq1pos
  have hr2 : q2 + p1 * q1 + p2 = 1 := by
    rcases r2 with h | h
    · linarith
    · exact h
  rcases eq_or_lt_of_le hp3 with hp3z | hp3pos
  · rw [← hp3z] at r3 r4
    rcases eq_or_lt_of_le hp2 with hp2z | hp2pos
    · -- the trinomial `1 + p1 x + x^5`
      rw [← hp2z] at hr2 r3 r4
      have hq2v : q2 = 1 - p1 * q1 := by linarith
      have hq2pos : 0 < q2 := by nlinarith
      have hq2lt : q2 < 1 := by linarith
      have hr3 : q3 + p1 * q2 + 0 * q1 + 0 = 1 := by
        rcases r3 with h | h
        · nlinarith [mul_pos hapos hq2pos]
        · exact h
      rw [hq4z, hp4z] at r4
      rcases r4 with h | h
      · have hq3z : q3 = 0 := by
          have : p1 * q3 = 0 := by nlinarith [mul_nonneg hp1 hq3]
          rcases mul_eq_zero.mp this with h' | h'
          · linarith
          · exact h'
        rw [hq3z] at hr3
        nlinarith [mul_le_mul_of_nonneg_right hp1' hq2]
      · nlinarith [mul_le_mul_of_nonneg_left hq3' hp1]
    · have hq3z : q3 = 0 := by
        rcases mul_eq_zero.mp h23 with h | h
        · linarith
        · exact h
      rw [hq3z, hq4z, hp4z] at r4
      rw [hq3z] at r3
      rcases eq_or_lt_of_le hq2 with hq2z | hq2pos
      · rw [← hq2z] at r3 hr2
        have hp2v : p2 = 1 - p1 * q1 := by linarith
        have hp2lt : p2 < 1 := by linarith
        rcases r3 with h | h
        · nlinarith [mul_pos hp2pos hq1pos]
        · nlinarith [mul_le_mul_of_nonneg_right hp2lt.le hq1]
      · have hq2lt : q2 < 1 := by linarith
        rcases r4 with h | h
        · nlinarith [mul_pos hp2pos hq2pos]
        · nlinarith [mul_pos hp2pos (show 0 < 1 - q2 by linarith)]
  · have hq2z : q2 = 0 := by
      rcases mul_eq_zero.mp h32 with h | h
      · linarith
      · exact h
    rw [hq2z] at hr2
    have hp2pos : 0 < p2 := by nlinarith
    have hq3z : q3 = 0 := by
      rcases mul_eq_zero.mp h23 with h | h
      · linarith
      · exact h
    rw [hq3z, hq4z, hp4z, hq2z] at r4
    rcases r4 with h | h
    · nlinarith [mul_pos hp3pos hq1pos]
    · nlinarith [mul_le_mul_of_nonneg_right hp3' hq1]

/-- Degree 5, second coefficient: once `p1` and `p4` are `0` or `1`, a coefficient
`0 < p2 < 1` forces `p1 = p3 = p4 = 0`. -/
lemma five_p2 {p1 p2 p3 p4 q1 q2 q3 q4 q5 : ℝ} (hp1 : p1 = 0 ∨ p1 = 1) (hp4 : p4 = 0 ∨ p4 = 1)
    (hb : 0 < p2) (hb1 : p2 < 1) (hp3 : 0 ≤ p3) (hq1 : 0 ≤ q1) (hq2 : 0 ≤ q2) (hq3 : 0 ≤ q3)
    (hq4 : 0 ≤ q4) (hq5 : 0 ≤ q5)
    (r1 : q1 + p1 = 0 ∨ q1 + p1 = 1) (r2 : q2 + p1 * q1 + p2 = 0 ∨ q2 + p1 * q1 + p2 = 1)
    (r3 : q3 + p1 * q2 + p2 * q1 + p3 = 0 ∨ q3 + p1 * q2 + p2 * q1 + p3 = 1)
    (r4 : q4 + p1 * q3 + p2 * q2 + p3 * q1 + p4 = 0 ∨
      q4 + p1 * q3 + p2 * q2 + p3 * q1 + p4 = 1)
    (r5 : q5 + p1 * q4 + p2 * q3 + p3 * q2 + p4 * q1 + 1 = 0 ∨
      q5 + p1 * q4 + p2 * q3 + p3 * q2 + p4 * q1 + 1 = 1) :
    p1 = 0 ∧ p3 = 0 ∧ p4 = 0 := by
  have hp1n : 0 ≤ p1 := by rcases hp1 with h | h <;> rw [h] <;> norm_num
  have hp4n : 0 ≤ p4 := by rcases hp4 with h | h <;> rw [h] <;> norm_num
  have e1 := mul_nonneg hp1n hq4
  have e2 := mul_nonneg hb.le hq3
  have e3 := mul_nonneg hp3 hq2
  have e4 := mul_nonneg hp4n hq1
  have h23 : p2 * q3 = 0 := by rcases r5 with h | h <;> linarith
  have h32 : p3 * q2 = 0 := by rcases r5 with h | h <;> linarith
  have hq3z : q3 = 0 := by
    rcases mul_eq_zero.mp h23 with h | h
    · linarith
    · exact h
  rcases hp1 with hp1z | hp1o
  · subst hp1z
    have hr2 : q2 + 0 * q1 + p2 = 1 := by
      rcases r2 with h | h
      · nlinarith
      · exact h
    have hq2v : q2 = 1 - p2 := by linarith
    have hp3z : p3 = 0 := by
      rcases mul_eq_zero.mp h32 with h | h
      · exact h
      · linarith
    have hq1z : q1 = 0 := by
      rw [hq3z, hp3z] at r3
      have hq1' : q1 = 0 ∨ q1 = 1 := by simpa using r1
      rcases hq1' with h | h
      · exact h
      · rw [h] at r3
        rcases r3 with h' | h' <;> nlinarith
    refine ⟨rfl, hp3z, ?_⟩
    rw [hq3z, hq2v, hp3z, hq1z] at r4
    rcases hp4 with h | h
    · exact h
    · rw [h] at r4
      rcases r4 with h' | h' <;> nlinarith [mul_pos hb (show 0 < 1 - p2 by linarith)]
  · subst hp1o
    have hq1z : q1 = 0 := by rcases r1 with h | h <;> linarith
    have hr2 : q2 + 1 * q1 + p2 = 1 := by
      rcases r2 with h | h
      · nlinarith
      · exact h
    rw [hq1z] at hr2
    have hp3z : p3 = 0 := by
      rcases mul_eq_zero.mp h32 with h | h
      · exact h
      · linarith
    rw [hq3z, hq1z, hp3z] at r3
    exfalso
    rcases r3 with h | h <;> nlinarith

/-- A monic degree-5 polynomial `1 + b x^2 + x^5` written by coefficients. -/
lemma eq_trinomial {P : ℝ[X]} (hP : P.Monic) (hd : P.natDegree = 5) (h0 : P.coeff 0 = 1)
    (h1 : P.coeff 1 = 0) (h3 : P.coeff 3 = 0) (h4 : P.coeff 4 = 0) :
    P = 1 + C (P.coeff 2) * X ^ 2 + X ^ 5 := by
  have h5 : P.coeff 5 = 1 := by rw [← hd]; exact hP.coeff_natDegree
  ext n
  simp only [coeff_add, coeff_one, coeff_C_mul, coeff_X_pow]
  rcases Nat.lt_or_ge 5 n with hn | hn
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    have a1 : n ≠ 0 := by omega
    have a2 : n ≠ 2 := by omega
    have a3 : n ≠ 5 := by omega
    simp [a1, a2, a3]
  · interval_cases n <;> simp [h0, h1, h3, h4, h5]

/-- The coefficient equations `1, ..., 5` of a normalized pair with `deg P = 5`. -/
lemma five_eqs {P Q : ℝ[X]} (hP : P.Monic) (hp0 : P.coeff 0 = 1) (hq0 : Q.coeff 0 = 1)
    (hd : P.natDegree = 5) (hR : ∀ n, (P * Q).coeff n = 0 ∨ (P * Q).coeff n = 1) :
    (Q.coeff 1 + P.coeff 1 = 0 ∨ Q.coeff 1 + P.coeff 1 = 1) ∧
    (Q.coeff 2 + P.coeff 1 * Q.coeff 1 + P.coeff 2 = 0 ∨
      Q.coeff 2 + P.coeff 1 * Q.coeff 1 + P.coeff 2 = 1) ∧
    (Q.coeff 3 + P.coeff 1 * Q.coeff 2 + P.coeff 2 * Q.coeff 1 + P.coeff 3 = 0 ∨
      Q.coeff 3 + P.coeff 1 * Q.coeff 2 + P.coeff 2 * Q.coeff 1 + P.coeff 3 = 1) ∧
    (Q.coeff 4 + P.coeff 1 * Q.coeff 3 + P.coeff 2 * Q.coeff 2 + P.coeff 3 * Q.coeff 1 +
        P.coeff 4 = 0 ∨
      Q.coeff 4 + P.coeff 1 * Q.coeff 3 + P.coeff 2 * Q.coeff 2 + P.coeff 3 * Q.coeff 1 +
        P.coeff 4 = 1) ∧
    (Q.coeff 5 + P.coeff 1 * Q.coeff 4 + P.coeff 2 * Q.coeff 3 + P.coeff 3 * Q.coeff 2 +
        P.coeff 4 * Q.coeff 1 + 1 = 0 ∨
      Q.coeff 5 + P.coeff 1 * Q.coeff 4 + P.coeff 2 * Q.coeff 3 + P.coeff 3 * Q.coeff 2 +
        P.coeff 4 * Q.coeff 1 + 1 = 1) := by
  have hp5 : P.coeff 5 = 1 := by rw [← hd]; exact hP.coeff_natDegree
  have e1 : (P * Q).coeff 1 = Q.coeff 1 + P.coeff 1 := by
    rw [OMA.R_Mathoverflow339137_mathoverflow_339137_R1.c1, hp0, hq0]; ring
  have e2 : (P * Q).coeff 2 = Q.coeff 2 + P.coeff 1 * Q.coeff 1 + P.coeff 2 := by
    rw [OMA.R_Mathoverflow339137_mathoverflow_339137_R1.c2, hp0, hq0]; ring
  have e3 : (P * Q).coeff 3 =
      Q.coeff 3 + P.coeff 1 * Q.coeff 2 + P.coeff 2 * Q.coeff 1 + P.coeff 3 := by
    rw [OMA.R_Mathoverflow339137_mathoverflow_339137_R1.c3, hp0, hq0]; ring
  have e4 : (P * Q).coeff 4 = Q.coeff 4 + P.coeff 1 * Q.coeff 3 + P.coeff 2 * Q.coeff 2 +
      P.coeff 3 * Q.coeff 1 + P.coeff 4 := by
    rw [OMA.R_Mathoverflow339137_mathoverflow_339137_R1.c4, hp0, hq0]; ring
  have e5 : (P * Q).coeff 5 = Q.coeff 5 + P.coeff 1 * Q.coeff 4 + P.coeff 2 * Q.coeff 3 +
      P.coeff 3 * Q.coeff 2 + P.coeff 4 * Q.coeff 1 + 1 := by
    rw [c5, hp0, hq0, hp5]; ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← e1]; exact hR 1
  · rw [← e2]; exact hR 2
  · rw [← e3]; exact hR 3
  · rw [← e4]; exact hR 4
  · rw [← e5]; exact hR 5

/-- Degree 5 with only the trinomial family assumed away. -/
lemma deg_five (h1 : H1) {P Q : ℝ[X]} (hP : P.Monic) (hQ : Q.Monic) (hp : ∀ n, 0 ≤ P.coeff n)
    (hq : ∀ n, 0 ≤ Q.coeff n) (hp0 : P.coeff 0 = 1) (hq0 : Q.coeff 0 = 1)
    (hR : ∀ n, (P * Q).coeff n = 0 ∨ (P * Q).coeff n = 1) (hd : P.natDegree = 5)
    (hdQ : 5 < Q.natDegree) (hgap : ∃ k < (P * Q).natDegree, (P * Q).coeff k = 0) :
    ∀ n, P.coeff n = 0 ∨ P.coeff n = 1 := by
  have hRQ : ∀ n, (Q * P).coeff n = 0 ∨ (Q * P).coeff n = 1 := by
    rw [mul_comm]
    exact hR
  -- the gap survives the reversal
  have hPQ0 : (P * Q).coeff 0 = 1 := by rw [mul_coeff_zero, hp0, hq0, one_mul]
  obtain ⟨-, -, hdPQ, hcPQ⟩ :=
    OMA.R_Mathoverflow339137_mathoverflow_339137_R1.rev_facts (hP.mul hQ) hPQ0
  have hgapr : ∃ k < (P.reverse * Q.reverse).natDegree,
      (P.reverse * Q.reverse).coeff k = 0 := by
    obtain ⟨k, hk, hk0⟩ := hgap
    have hkpos : k ≠ 0 := by
      intro h
      rw [h, hPQ0] at hk0
      exact one_ne_zero hk0
    refine ⟨(P * Q).natDegree - k, ?_, ?_⟩
    · rw [← reverse_mul_of_domain, hdPQ]
      omega
    · rw [← reverse_mul_of_domain, hcPQ _ (by omega)]
      rw [show (P * Q).natDegree - ((P * Q).natDegree - k) = k by omega]
      exact hk0
  have hP1 := OMA.R_Mathoverflow339137_mathoverflow_339137_R1.coeff_le_one hQ hp hq hR
  have hQ1 := OMA.R_Mathoverflow339137_mathoverflow_339137_R1.coeff_le_one hP hq hp hRQ
  -- the reversed pair
  obtain ⟨hPr, hpr0, hdr, hcr⟩ := OMA.R_Mathoverflow339137_mathoverflow_339137_R1.rev_facts hP hp0
  obtain ⟨hQr, hqr0, hdqr, -⟩ := OMA.R_Mathoverflow339137_mathoverflow_339137_R1.rev_facts hQ hq0
  have hpr : ∀ n, 0 ≤ P.reverse.coeff n := fun n => by rw [coeff_reverse]; exact hp _
  have hqr : ∀ n, 0 ≤ Q.reverse.coeff n := fun n => by rw [coeff_reverse]; exact hq _
  have hRr : ∀ n, (P.reverse * Q.reverse).coeff n = 0 ∨ (P.reverse * Q.reverse).coeff n = 1 := by
    intro n
    rw [← reverse_mul_of_domain, coeff_reverse]
    exact hR _
  have hRrQ : ∀ n, (Q.reverse * P.reverse).coeff n = 0 ∨
      (Q.reverse * P.reverse).coeff n = 1 := by
    rw [mul_comm]
    exact hRr
  have hPr1 := OMA.R_Mathoverflow339137_mathoverflow_339137_R1.coeff_le_one hQr hpr hqr hRr
  have hQr1 := OMA.R_Mathoverflow339137_mathoverflow_339137_R1.coeff_le_one hPr hqr hpr hRrQ
  have hdr5 : P.reverse.natDegree = 5 := by rw [hdr, hd]
  have rc1 : P.reverse.coeff 1 = P.coeff 4 := by rw [hcr 1 (by omega), hd]
  have rc2 : P.reverse.coeff 2 = P.coeff 3 := by rw [hcr 2 (by omega), hd]
  have rc3 : P.reverse.coeff 3 = P.coeff 2 := by rw [hcr 3 (by omega), hd]
  have rc4 : P.reverse.coeff 4 = P.coeff 1 := by rw [hcr 4 (by omega), hd]
  obtain ⟨r1, r2, r3, r4, r5⟩ := five_eqs hP hp0 hq0 hd hR
  obtain ⟨s1, s2, s3, s4, s5⟩ := five_eqs hPr hpr0 hqr0 hdr5 hRr
  have hz1 : P.coeff 1 = 0 ∨ P.coeff 1 = 1 :=
    five_p1 (hp 1) (hP1 1) (hp 2) (hp 3) (hP1 3) (hp 4) (hq 1) (hq 2) (hq 3) (hQ1 3) (hq 4) (hq 5)
      r1 r2 r3 r4 r5
  have hz4 : P.coeff 4 = 0 ∨ P.coeff 4 = 1 := by
    rw [← rc1]
    exact five_p1 (hpr 1) (hPr1 1) (hpr 2) (hpr 3) (hPr1 3) (hpr 4) (hqr 1) (hqr 2) (hqr 3)
      (hQr1 3) (hqr 4) (hqr 5) s1 s2 s3 s4 s5
  have hRzo := (OMA.R_Mathoverflow339137_mathoverflow_339137_R1.isZeroOne_iff (P * Q)).mpr hR
  have hRrzo :=
    (OMA.R_Mathoverflow339137_mathoverflow_339137_R1.isZeroOne_iff (P.reverse * Q.reverse)).mpr hRr
  have hz2 : P.coeff 2 = 0 ∨ P.coeff 2 = 1 := by
    by_contra hne
    push_neg at hne
    have hb : 0 < P.coeff 2 := lt_of_le_of_ne (hp 2) (Ne.symm hne.1)
    have hb1 : P.coeff 2 < 1 := lt_of_le_of_ne (hP1 2) hne.2
    obtain ⟨e1, e3, e4⟩ := five_p2 hz1 hz4 hb hb1 (hp 3) (hq 1) (hq 2) (hq 3) (hq 4) (hq 5)
      r1 r2 r3 r4 r5
    have heq := eq_trinomial hP hd hp0 e1 e3 e4
    apply h1 (P.coeff 2) hb hb1 Q hQ hq hq0 hdQ
    · rw [← heq]
      exact hRzo
    · rw [← heq]
      exact hgap
  have hz3 : P.coeff 3 = 0 ∨ P.coeff 3 = 1 := by
    by_contra hne
    push_neg at hne
    have hb : 0 < P.reverse.coeff 2 := by
      rw [rc2]
      exact lt_of_le_of_ne (hp 3) (Ne.symm hne.1)
    have hb1 : P.reverse.coeff 2 < 1 := by
      rw [rc2]
      exact lt_of_le_of_ne (hP1 3) hne.2
    have hz1r : P.reverse.coeff 1 = 0 ∨ P.reverse.coeff 1 = 1 := by rw [rc1]; exact hz4
    have hz4r : P.reverse.coeff 4 = 0 ∨ P.reverse.coeff 4 = 1 := by rw [rc4]; exact hz1
    obtain ⟨e1, e3, e4⟩ := five_p2 hz1r hz4r hb hb1 (hpr 3) (hqr 1) (hqr 2) (hqr 3) (hqr 4)
      (hqr 5) s1 s2 s3 s4 s5
    have heq := eq_trinomial hPr hdr5 hpr0 e1 e3 e4
    apply h1 (P.reverse.coeff 2) hb hb1 Q.reverse hQr hqr hqr0 (by rw [hdqr]; exact hdQ)
    · rw [← heq]
      exact hRrzo
    · rw [← heq]
      exact hgapr
  intro n
  rcases Nat.lt_or_ge 5 n with hn | hn
  · exact Or.inl (coeff_eq_zero_of_natDegree_lt (by omega))
  · have hp5 : P.coeff 5 = 1 := by rw [← hd]; exact hP.coeff_natDegree
    interval_cases n
    · exact Or.inr hp0
    · exact hz1
    · exact hz2
    · exact hz3
    · exact hz4
    · exact Or.inr hp5

/-- Case A2 of degree 6: the algebra. -/
lemma six_caseA2 {a q3 p4 : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hq3 : q3 = 1 - (1 - a * (1 - a)) * (1 - a)) (hp4 : p4 = 1 - a * q3)
    (h5 : (1 - a * (1 - a)) * q3 + p4 * (1 - a) = 1) :
    1 < p4 * q3 + (1 - a) := by
  subst hp4
  subst hq3
  have hE : (2 - 2 * a + a ^ 2) * (1 - 2 * a + 2 * a ^ 2) = 1 := by
    have h5' : a * ((2 - 2 * a + a ^ 2) * (1 - 2 * a + 2 * a ^ 2) - 1) = 0 := by
      linear_combination h5
    rcases mul_eq_zero.mp h5' with h | h
    · linarith
    · linarith
  have hhalf : a < 1 / 2 := by
    by_contra hge
    push_neg at hge
    nlinarith [mul_nonneg (sub_nonneg.mpr hge) (sub_nonneg.mpr ha1.le),
      mul_nonneg (mul_nonneg (sub_nonneg.mpr hge) (sub_nonneg.mpr ha1.le)) (sub_nonneg.mpr ha1.le)]
  nlinarith [mul_pos ha ha, mul_pos (mul_pos ha ha) ha, mul_pos ha (sub_pos.mpr hhalf)]

/-- Case B1b of degree 6: the algebra. -/
lemma six_caseB1b {a q2 p3 q4 q7 : ℝ} (ha : 0 < a) (ha1 : a < 1) (hq4' : q4 ≤ 1)
    (hq2 : q2 = 1 - a * (1 - a)) (hp3 : p3 = 1 - a * q2) (hq4 : q4 = 1 - p3 * (1 - a))
    (h5 : a * q4 + p3 * q2 = 1) (hq7 : q7 = 1 - p3 * q4 - (1 - a)) :
    1 < a * q7 + q2 := by
  subst hq7
  have hk : a * (2 * a ^ 3 - 2 * a ^ 2 + 3 * a - 2) * (a - 1) = 0 := by
    subst hq4
    subst hp3
    subst hq2
    linear_combination (-1 : ℝ) * h5
  have hk' : 2 * a ^ 3 - 2 * a ^ 2 + 3 * a - 2 = 0 := by
    rcases mul_eq_zero.mp hk with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · linarith
      · exact h'
    · linarith
  have h34 : 3 / 4 < a := by
    nlinarith [sq_nonneg (a - 1 / 8)]
  have hp3v : p3 = 1 - a + a ^ 2 - a ^ 3 := by rw [hp3, hq2]; ring
  have hp3lt : p3 < 1 / 2 := by nlinarith
  have hp3pos : 0 ≤ p3 := by nlinarith
  have hq4pos : 0 ≤ q4 := by rw [hq4]; nlinarith
  have hprod : p3 * q4 < 1 / 2 := by nlinarith
  rw [hq2]
  nlinarith

/-- Degree 6, first coefficient. -/
lemma six_p1 {p1 p2 p3 p4 p5 q1 q2 q3 q4 q5 q6 q7 q8 : ℝ}
    (hp1 : 0 ≤ p1) (hp1' : p1 ≤ 1) (hp2 : 0 ≤ p2) (hp3 : 0 ≤ p3) (hp3' : p3 ≤ 1)
    (hp4 : 0 ≤ p4) (hp4' : p4 ≤ 1) (hp5 : 0 ≤ p5)
    (hq1 : 0 ≤ q1) (hq2 : 0 ≤ q2) (hq2' : q2 ≤ 1) (hq3 : 0 ≤ q3) (hq3' : q3 ≤ 1) (hq4 : 0 ≤ q4)
    (hq4' : q4 ≤ 1) (hq5 : 0 ≤ q5) (hq6 : 0 ≤ q6) (hq7 : 0 ≤ q7) (hq8 : 0 ≤ q8)
    (r1 : q1 + p1 = 0 ∨ q1 + p1 = 1)
    (r2 : q2 + p1 * q1 + p2 = 0 ∨ q2 + p1 * q1 + p2 = 1)
    (r3 : q3 + p1 * q2 + p2 * q1 + p3 = 0 ∨ q3 + p1 * q2 + p2 * q1 + p3 = 1)
    (r4 : q4 + p1 * q3 + p2 * q2 + p3 * q1 + p4 = 0 ∨
      q4 + p1 * q3 + p2 * q2 + p3 * q1 + p4 = 1)
    (r5 : q5 + p1 * q4 + p2 * q3 + p3 * q2 + p4 * q1 + p5 = 0 ∨
      q5 + p1 * q4 + p2 * q3 + p3 * q2 + p4 * q1 + p5 = 1)
    (r6 : q6 + p1 * q5 + p2 * q4 + p3 * q3 + p4 * q2 + p5 * q1 + 1 = 0 ∨
      q6 + p1 * q5 + p2 * q4 + p3 * q3 + p4 * q2 + p5 * q1 + 1 = 1)
    (r7 : q7 + p1 * q6 + p2 * q5 + p3 * q4 + p4 * q3 + p5 * q2 + q1 = 0 ∨
      q7 + p1 * q6 + p2 * q5 + p3 * q4 + p4 * q3 + p5 * q2 + q1 = 1)
    (r8 : q8 + p1 * q7 + p2 * q6 + p3 * q5 + p4 * q4 + p5 * q3 + q2 = 0 ∨
      q8 + p1 * q7 + p2 * q6 + p3 * q5 + p4 * q4 + p5 * q3 + q2 = 1) :
    p1 = 0 ∨ p1 = 1 := by
  have e1 := mul_nonneg hp1 hq5
  have e2 := mul_nonneg hp2 hq4
  have e3 := mul_nonneg hp3 hq3
  have e4 := mul_nonneg hp4 hq2
  have e5 := mul_nonneg hp5 hq1
  have hq6z : q6 = 0 := by rcases r6 with h | h <;> linarith
  have h15 : p1 * q5 = 0 := by rcases r6 with h | h <;> linarith
  have h24 : p2 * q4 = 0 := by rcases r6 with h | h <;> linarith
  have h33 : p3 * q3 = 0 := by rcases r6 with h | h <;> linarith
  have h42 : p4 * q2 = 0 := by rcases r6 with h | h <;> linarith
  have h51 : p5 * q1 = 0 := by rcases r6 with h | h <;> linarith
  by_contra hne
  push_neg at hne
  have ha : 0 < p1 := lt_of_le_of_ne hp1 (Ne.symm hne.1)
  have ha1 : p1 < 1 := lt_of_le_of_ne hp1' hne.2
  have hq1v : q1 = 1 - p1 := by rcases r1 with h | h <;> linarith
  have hq1pos : 0 < q1 := by linarith
  have hp5z : p5 = 0 := by
    rcases mul_eq_zero.mp h51 with h | h
    · exact h
    · linarith
  have hq5z : q5 = 0 := by
    rcases mul_eq_zero.mp h15 with h | h
    · linarith
    · exact h
  have hpq : 0 < p1 * q1 := mul_pos ha hq1pos
  have hpq1 : p1 * q1 < 1 := by have := mul_le_mul_of_nonneg_right hp1' hq1; linarith
  have hr2 : q2 + p1 * q1 + p2 = 1 := by
    rcases r2 with h | h
    · linarith
    · exact h
  rcases eq_or_lt_of_le hq2 with hq2z | hq2pos
  · -- Case A: q2 = 0, so p2 = 1 - p1 q1 > 0 and q4 = 0
    have hp2v : p2 = 1 - p1 * q1 := by
      rw [← hq2z] at hr2
      linarith
    have hp2pos : 0 < p2 := by linarith
    have hq4z : q4 = 0 := by
      rcases mul_eq_zero.mp h24 with h | h
      · linarith
      · exact h
    rcases eq_or_lt_of_le hp3 with hp3z | hp3pos
    · -- A2: p3 = 0
      have hr3 : q3 + p2 * q1 = 1 := by
        rw [← hq2z, ← hp3z] at r3
        rcases r3 with h | h
        · linarith [mul_pos hp2pos hq1pos]
        · linarith
      have hq3v : q3 = 1 - (1 - p1 * (1 - p1)) * (1 - p1) := by
        rw [hp2v, hq1v] at hr3
        linarith
      have hq3pos : 0 < q3 := by
        rw [hq3v]
        linarith [mul_pos ha (show (0:ℝ) < (1 - p1) ^ 2 + 1 by positivity)]
      have hr4 : p1 * q3 + p4 = 1 := by
        rw [hq4z, ← hq2z, ← hp3z] at r4
        rcases r4 with h | h
        · linarith [mul_pos ha hq3pos]
        · linarith
      have hp4v : p4 = 1 - p1 * q3 := by linarith
      have hu : 0 < 1 - p1 * (1 - p1) := by linarith [sq_nonneg (p1 - 1 / 2)]
      have hr5 : (1 - p1 * (1 - p1)) * q3 + p4 * (1 - p1) = 1 := by
        rw [hq5z, hq4z, ← hq2z, ← hp3z, hp5z, hp2v, hq1v] at r5
        rcases r5 with h | h
        · linarith [mul_pos hu hq3pos, mul_nonneg hp4 (sub_pos.mpr ha1).le]
        · linarith
      have key := six_caseA2 ha ha1 hq3v hp4v hr5
      rw [hq6z, hq5z, hq4z, ← hp3z, ← hq2z, hp5z, hq1v] at r7
      rcases r7 with h | h <;> linarith
    · -- A1: p3 > 0, so q3 = 0
      have hq3z : q3 = 0 := by
        rcases mul_eq_zero.mp h33 with h | h
        · linarith
        · exact h
      have hp4z : p4 = 0 := by
        rw [hq5z, hq4z, hq3z, ← hq2z, hp5z] at r5
        have hlt : p4 * q1 < 1 := by linarith [mul_le_mul_of_nonneg_right hp4' hq1]
        rcases r5 with h | h
        · have h0 : p4 * q1 = 0 := by linarith
          rcases mul_eq_zero.mp h0 with h' | h'
          · exact h'
          · linarith
        · linarith
      rw [hq4z, hq3z, ← hq2z, hp4z] at r4
      have hlt : p3 * q1 < 1 := by linarith [mul_le_mul_of_nonneg_right hp3' hq1]
      rcases r4 with h | h <;> linarith [mul_pos hp3pos hq1pos]
  · -- Case B: q2 > 0, so p4 = 0
    have hp4z : p4 = 0 := by
      rcases mul_eq_zero.mp h42 with h | h
      · exact h
      · linarith
    rcases eq_or_lt_of_le hp3 with hp3z | hp3pos
    · -- B2: p3 = 0
      rcases eq_or_lt_of_le hp2 with hp2z | hp2pos
      · -- B2b: p2 = 0, the trinomial 1 + p1 x + x^6
        have hr3 : q3 + p1 * q2 = 1 := by
          rw [← hp2z, ← hp3z] at r3
          rcases r3 with h | h
          · linarith [mul_pos ha hq2pos]
          · linarith
        have hq3pos : 0 < q3 := by linarith [mul_lt_mul_of_pos_right ha1 hq2pos]
        have hr4 : q4 + p1 * q3 = 1 := by
          rw [← hp2z, ← hp3z, hp4z] at r4
          rcases r4 with h | h
          · linarith [mul_pos ha hq3pos]
          · linarith
        rw [hq5z, ← hp2z, ← hp3z, hp4z, hp5z] at r5
        rcases r5 with h | h
        · have hq4z : q4 = 0 := by
            have h0 : p1 * q4 = 0 := by linarith
            rcases mul_eq_zero.mp h0 with h' | h'
            · linarith
            · exact h'
          rw [hq4z] at hr4
          linarith [mul_lt_mul_of_pos_right ha1 hq3pos]
        · linarith [mul_le_mul_of_nonneg_left hq4' hp1]
      · -- B2a: p2 > 0, so q4 = 0
        have hq4z : q4 = 0 := by
          rcases mul_eq_zero.mp h24 with h | h
          · linarith
          · exact h
        have hq2lt : q2 < 1 := by linarith
        have hp2lt : p2 < 1 := by linarith
        rw [hq5z, hq4z, ← hp3z, hp4z, hp5z] at r5
        have hq3z : q3 = 0 := by
          rcases r5 with h | h
          · have h0 : p2 * q3 = 0 := by linarith
            rcases mul_eq_zero.mp h0 with h' | h'
            · linarith
            · exact h'
          · linarith [mul_le_mul_of_nonneg_left hq3' hp2]
        rw [hq4z, hq3z, ← hp3z, hp4z] at r4
        rcases r4 with h | h
        · linarith [mul_pos hp2pos hq2pos]
        · linarith [mul_le_mul_of_nonneg_right hp2lt.le hq2]
    · -- B1: p3 > 0, so q3 = 0
      have hq3z : q3 = 0 := by
        rcases mul_eq_zero.mp h33 with h | h
        · linarith
        · exact h
      rcases eq_or_lt_of_le hp2 with hp2z | hp2pos
      · -- B1b: p2 = 0
        have hq2v : q2 = 1 - p1 * (1 - p1) := by
          rw [← hp2z, hq1v] at hr2
          linarith
        have hr3 : p1 * q2 + p3 = 1 := by
          rw [hq3z, ← hp2z] at r3
          rcases r3 with h | h
          · linarith [mul_pos ha hq2pos]
          · linarith
        have hp3v : p3 = 1 - p1 * q2 := by linarith
        have hr4 : q4 + p3 * (1 - p1) = 1 := by
          rw [hq3z, ← hp2z, hp4z, hq1v] at r4
          rcases r4 with h | h
          · linarith [mul_pos hp3pos (sub_pos.mpr ha1)]
          · linarith
        have hq4v : q4 = 1 - p3 * (1 - p1) := by linarith
        have hr5 : p1 * q4 + p3 * q2 = 1 := by
          rw [hq5z, ← hp2z, hq3z, hp4z, hp5z] at r5
          rcases r5 with h | h
          · linarith [mul_pos hp3pos hq2pos, mul_nonneg hp1 hq4]
          · linarith
        have hr7 : q7 = 1 - p3 * q4 - (1 - p1) := by
          rw [hq6z, hq5z, hq3z, hp4z, hp5z, ← hp2z, hq1v] at r7
          rcases r7 with h | h
          · linarith [mul_nonneg hp3 hq4]
          · linarith
        have key := six_caseB1b ha ha1 hq4' hq2v hp3v hq4v hr5 hr7
        rw [hq6z, hq5z, hp4z, hp5z, ← hp2z] at r8
        rcases r8 with h | h <;> linarith
      · -- B1a: p2 > 0, so q4 = 0 and the coefficient at 5 is p3 q2 < 1
        have hq4z : q4 = 0 := by
          rcases mul_eq_zero.mp h24 with h | h
          · linarith
          · exact h
        have hq2lt : q2 < 1 := by linarith
        rw [hq5z, hq4z, hq3z, hp4z, hp5z] at r5
        rcases r5 with h | h
        · linarith [mul_pos hp3pos hq2pos]
        · linarith [mul_le_mul_of_nonneg_right hp3' hq2]

/-- Degree 6, second coefficient (once `p1` is `0` or `1`). -/
lemma six_p2 {p1 p2 p3 p4 p5 q1 q2 q3 q4 q5 q6 : ℝ} (hp1 : p1 = 0 ∨ p1 = 1)
    (hb : 0 < p2) (hb1 : p2 < 1) (hp3 : 0 ≤ p3) (hp4 : 0 ≤ p4) (hp5 : 0 ≤ p5)
    (hq1 : 0 ≤ q1) (hq2 : 0 ≤ q2) (hq3 : 0 ≤ q3) (hq4 : 0 ≤ q4) (hq5 : 0 ≤ q5) (hq6 : 0 ≤ q6)
    (r1 : q1 + p1 = 0 ∨ q1 + p1 = 1)
    (r2 : q2 + p1 * q1 + p2 = 0 ∨ q2 + p1 * q1 + p2 = 1)
    (r3 : q3 + p1 * q2 + p2 * q1 + p3 = 0 ∨ q3 + p1 * q2 + p2 * q1 + p3 = 1)
    (r4 : q4 + p1 * q3 + p2 * q2 + p3 * q1 + p4 = 0 ∨
      q4 + p1 * q3 + p2 * q2 + p3 * q1 + p4 = 1)
    (r6 : q6 + p1 * q5 + p2 * q4 + p3 * q3 + p4 * q2 + p5 * q1 + 1 = 0 ∨
      q6 + p1 * q5 + p2 * q4 + p3 * q3 + p4 * q2 + p5 * q1 + 1 = 1) : False := by
  have hp1n : 0 ≤ p1 := by rcases hp1 with h | h <;> rw [h] <;> norm_num
  have e1 := mul_nonneg hp1n hq5
  have e2 := mul_nonneg hb.le hq4
  have e3 := mul_nonneg hp3 hq3
  have e4 := mul_nonneg hp4 hq2
  have e5 := mul_nonneg hp5 hq1
  have h24 : p2 * q4 = 0 := by rcases r6 with h | h <;> linarith
  have h33 : p3 * q3 = 0 := by rcases r6 with h | h <;> linarith
  have h42 : p4 * q2 = 0 := by rcases r6 with h | h <;> linarith
  have hq4z : q4 = 0 := by
    rcases mul_eq_zero.mp h24 with h | h
    · linarith
    · exact h
  rcases hp1 with hp1z | hp1o
  · subst hp1z
    have hr2 : q2 + p2 = 1 := by
      rcases r2 with h | h <;> linarith
    have hq2v : q2 = 1 - p2 := by linarith
    have hp4z : p4 = 0 := by
      rcases mul_eq_zero.mp h42 with h | h
      · exact h
      · linarith
    rw [hq4z, hp4z, hq2v] at r4
    have hr4 : p2 * (1 - p2) + p3 * q1 = 1 := by
      rcases r4 with h | h
      · linarith [mul_pos hb (sub_pos.mpr hb1), mul_nonneg hp3 hq1]
      · linarith
    have hq1' : q1 = 0 ∨ q1 = 1 := by
      rcases r1 with h | h
      · left; linarith
      · right; linarith
    rcases hq1' with hq1z | hq1o
    · rw [hq1z] at hr4
      linarith [sq_nonneg (p2 - 1 / 2)]
    · rw [hq1o] at hr4 r3
      have hp3pos : 0 < p3 := by linarith [sq_nonneg (p2 - 1 / 2)]
      have hq3z : q3 = 0 := by
        rcases mul_eq_zero.mp h33 with h | h
        · linarith
        · exact h
      rw [hq3z] at r3
      rcases r3 with h | h <;> linarith [mul_pos hb hb]
  · subst hp1o
    have hq1z : q1 = 0 := by rcases r1 with h | h <;> linarith
    rw [hq1z] at r2 r3 r4
    have hr2 : q2 + p2 = 1 := by
      rcases r2 with h | h <;> linarith
    have hq2v : q2 = 1 - p2 := by linarith
    have hp4z : p4 = 0 := by
      rcases mul_eq_zero.mp h42 with h | h
      · exact h
      · linarith
    have hr3 : q3 + q2 + p3 = 1 := by
      rcases r3 with h | h <;> linarith
    rw [hq4z, hp4z, hq2v] at r4
    rcases r4 with h | h <;>
      linarith [mul_pos hb (sub_pos.mpr hb1), mul_pos (sub_pos.mpr hb1) (sub_pos.mpr hb1)]

/-- Degree 6, third coefficient: `p3` against `q3` in the middle coefficient `r6`. -/
lemma six_p3 {p1 p2 p3 p4 p5 q1 q2 q3 q4 q5 q6 : ℝ} (hp1 : p1 = 0 ∨ p1 = 1)
    (hp2 : p2 = 0 ∨ p2 = 1) (hc : 0 < p3) (hc1 : p3 < 1) (hp4 : 0 ≤ p4) (hp5 : 0 ≤ p5)
    (hq1 : 0 ≤ q1) (hq2 : 0 ≤ q2) (hq3 : 0 ≤ q3) (hq4 : 0 ≤ q4) (hq5 : 0 ≤ q5) (hq6 : 0 ≤ q6)
    (r1 : q1 + p1 = 0 ∨ q1 + p1 = 1)
    (r2 : q2 + p1 * q1 + p2 = 0 ∨ q2 + p1 * q1 + p2 = 1)
    (r3 : q3 + p1 * q2 + p2 * q1 + p3 = 0 ∨ q3 + p1 * q2 + p2 * q1 + p3 = 1)
    (r6 : q6 + p1 * q5 + p2 * q4 + p3 * q3 + p4 * q2 + p5 * q1 + 1 = 0 ∨
      q6 + p1 * q5 + p2 * q4 + p3 * q3 + p4 * q2 + p5 * q1 + 1 = 1) : False := by
  have hp1n : 0 ≤ p1 := by rcases hp1 with h | h <;> rw [h] <;> norm_num
  have hp2n : 0 ≤ p2 := by rcases hp2 with h | h <;> rw [h] <;> norm_num
  have e1 := mul_nonneg hp1n hq5
  have e2 := mul_nonneg hp2n hq4
  have e3 := mul_nonneg hc.le hq3
  have e4 := mul_nonneg hp4 hq2
  have e5 := mul_nonneg hp5 hq1
  have h33 : p3 * q3 = 0 := by rcases r6 with h | h <;> linarith
  have hq3z : q3 = 0 := by
    rcases mul_eq_zero.mp h33 with h | h
    · linarith
    · exact h
  rw [hq3z] at r3
  rcases hp1 with h1 | h1 <;> rcases hp2 with h2 | h2 <;> subst h1 <;> subst h2 <;>
    rcases r1 with s1 | s1 <;> rcases r2 with s2 | s2 <;> rcases r3 with s3 | s3 <;>
    linarith

-- Degree 6

lemma c6 (P Q : ℝ[X]) :
    (P * Q).coeff 6 = P.coeff 0 * Q.coeff 6 + P.coeff 1 * Q.coeff 5 + P.coeff 2 * Q.coeff 4 +
      P.coeff 3 * Q.coeff 3 + P.coeff 4 * Q.coeff 2 + P.coeff 5 * Q.coeff 1 +
      P.coeff 6 * Q.coeff 0 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

lemma c7 (P Q : ℝ[X]) :
    (P * Q).coeff 7 = P.coeff 0 * Q.coeff 7 + P.coeff 1 * Q.coeff 6 + P.coeff 2 * Q.coeff 5 +
      P.coeff 3 * Q.coeff 4 + P.coeff 4 * Q.coeff 3 + P.coeff 5 * Q.coeff 2 +
      P.coeff 6 * Q.coeff 1 + P.coeff 7 * Q.coeff 0 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

lemma c8 (P Q : ℝ[X]) :
    (P * Q).coeff 8 = P.coeff 0 * Q.coeff 8 + P.coeff 1 * Q.coeff 7 + P.coeff 2 * Q.coeff 6 +
      P.coeff 3 * Q.coeff 5 + P.coeff 4 * Q.coeff 4 + P.coeff 5 * Q.coeff 3 +
      P.coeff 6 * Q.coeff 2 + P.coeff 7 * Q.coeff 1 + P.coeff 8 * Q.coeff 0 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

/-- The coefficient equations `1, ..., 8` of a normalized pair with `deg P = 6`. -/
lemma six_eqs {P Q : ℝ[X]} (hP : P.Monic) (hp0 : P.coeff 0 = 1) (hq0 : Q.coeff 0 = 1)
    (hd : P.natDegree = 6) (hR : ∀ n, (P * Q).coeff n = 0 ∨ (P * Q).coeff n = 1) :
    (Q.coeff 1 + P.coeff 1 = 0 ∨ Q.coeff 1 + P.coeff 1 = 1) ∧
    (Q.coeff 2 + P.coeff 1 * Q.coeff 1 + P.coeff 2 = 0 ∨
      Q.coeff 2 + P.coeff 1 * Q.coeff 1 + P.coeff 2 = 1) ∧
    (Q.coeff 3 + P.coeff 1 * Q.coeff 2 + P.coeff 2 * Q.coeff 1 + P.coeff 3 = 0 ∨
      Q.coeff 3 + P.coeff 1 * Q.coeff 2 + P.coeff 2 * Q.coeff 1 + P.coeff 3 = 1) ∧
    (Q.coeff 4 + P.coeff 1 * Q.coeff 3 + P.coeff 2 * Q.coeff 2 + P.coeff 3 * Q.coeff 1 +
        P.coeff 4 = 0 ∨
      Q.coeff 4 + P.coeff 1 * Q.coeff 3 + P.coeff 2 * Q.coeff 2 + P.coeff 3 * Q.coeff 1 +
        P.coeff 4 = 1) ∧
    (Q.coeff 5 + P.coeff 1 * Q.coeff 4 + P.coeff 2 * Q.coeff 3 + P.coeff 3 * Q.coeff 2 +
        P.coeff 4 * Q.coeff 1 + P.coeff 5 = 0 ∨
      Q.coeff 5 + P.coeff 1 * Q.coeff 4 + P.coeff 2 * Q.coeff 3 + P.coeff 3 * Q.coeff 2 +
        P.coeff 4 * Q.coeff 1 + P.coeff 5 = 1) ∧
    (Q.coeff 6 + P.coeff 1 * Q.coeff 5 + P.coeff 2 * Q.coeff 4 + P.coeff 3 * Q.coeff 3 +
        P.coeff 4 * Q.coeff 2 + P.coeff 5 * Q.coeff 1 + 1 = 0 ∨
      Q.coeff 6 + P.coeff 1 * Q.coeff 5 + P.coeff 2 * Q.coeff 4 + P.coeff 3 * Q.coeff 3 +
        P.coeff 4 * Q.coeff 2 + P.coeff 5 * Q.coeff 1 + 1 = 1) ∧
    (Q.coeff 7 + P.coeff 1 * Q.coeff 6 + P.coeff 2 * Q.coeff 5 + P.coeff 3 * Q.coeff 4 +
        P.coeff 4 * Q.coeff 3 + P.coeff 5 * Q.coeff 2 + Q.coeff 1 = 0 ∨
      Q.coeff 7 + P.coeff 1 * Q.coeff 6 + P.coeff 2 * Q.coeff 5 + P.coeff 3 * Q.coeff 4 +
        P.coeff 4 * Q.coeff 3 + P.coeff 5 * Q.coeff 2 + Q.coeff 1 = 1) ∧
    (Q.coeff 8 + P.coeff 1 * Q.coeff 7 + P.coeff 2 * Q.coeff 6 + P.coeff 3 * Q.coeff 5 +
        P.coeff 4 * Q.coeff 4 + P.coeff 5 * Q.coeff 3 + Q.coeff 2 = 0 ∨
      Q.coeff 8 + P.coeff 1 * Q.coeff 7 + P.coeff 2 * Q.coeff 6 + P.coeff 3 * Q.coeff 5 +
        P.coeff 4 * Q.coeff 4 + P.coeff 5 * Q.coeff 3 + Q.coeff 2 = 1) := by
  have hp6 : P.coeff 6 = 1 := by rw [← hd]; exact hP.coeff_natDegree
  have hp7 : P.coeff 7 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have hp8 : P.coeff 8 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have e1 : (P * Q).coeff 1 = Q.coeff 1 + P.coeff 1 := by
    rw [OMA.R_Mathoverflow339137_mathoverflow_339137_R1.c1, hp0, hq0]; ring
  have e2 : (P * Q).coeff 2 = Q.coeff 2 + P.coeff 1 * Q.coeff 1 + P.coeff 2 := by
    rw [OMA.R_Mathoverflow339137_mathoverflow_339137_R1.c2, hp0, hq0]; ring
  have e3 : (P * Q).coeff 3 =
      Q.coeff 3 + P.coeff 1 * Q.coeff 2 + P.coeff 2 * Q.coeff 1 + P.coeff 3 := by
    rw [OMA.R_Mathoverflow339137_mathoverflow_339137_R1.c3, hp0, hq0]; ring
  have e4 : (P * Q).coeff 4 = Q.coeff 4 + P.coeff 1 * Q.coeff 3 + P.coeff 2 * Q.coeff 2 +
      P.coeff 3 * Q.coeff 1 + P.coeff 4 := by
    rw [OMA.R_Mathoverflow339137_mathoverflow_339137_R1.c4, hp0, hq0]; ring
  have e5 : (P * Q).coeff 5 = Q.coeff 5 + P.coeff 1 * Q.coeff 4 + P.coeff 2 * Q.coeff 3 +
      P.coeff 3 * Q.coeff 2 + P.coeff 4 * Q.coeff 1 + P.coeff 5 := by
    rw [c5, hp0, hq0]; ring
  have e6 : (P * Q).coeff 6 = Q.coeff 6 + P.coeff 1 * Q.coeff 5 + P.coeff 2 * Q.coeff 4 +
      P.coeff 3 * Q.coeff 3 + P.coeff 4 * Q.coeff 2 + P.coeff 5 * Q.coeff 1 + 1 := by
    rw [c6, hp0, hq0, hp6]; ring
  have e7 : (P * Q).coeff 7 = Q.coeff 7 + P.coeff 1 * Q.coeff 6 + P.coeff 2 * Q.coeff 5 +
      P.coeff 3 * Q.coeff 4 + P.coeff 4 * Q.coeff 3 + P.coeff 5 * Q.coeff 2 + Q.coeff 1 := by
    rw [c7, hp0, hq0, hp6, hp7]; ring
  have e8 : (P * Q).coeff 8 = Q.coeff 8 + P.coeff 1 * Q.coeff 7 + P.coeff 2 * Q.coeff 6 +
      P.coeff 3 * Q.coeff 5 + P.coeff 4 * Q.coeff 4 + P.coeff 5 * Q.coeff 3 + Q.coeff 2 := by
    rw [c8, hp0, hq0, hp6, hp7, hp8]; ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← e1]; exact hR 1
  · rw [← e2]; exact hR 2
  · rw [← e3]; exact hR 3
  · rw [← e4]; exact hR 4
  · rw [← e5]; exact hR 5
  · rw [← e6]; exact hR 6
  · rw [← e7]; exact hR 7
  · rw [← e8]; exact hR 8

/-- Degree 6: every normalized factor of degree `6` is a `0, 1` polynomial. -/
lemma deg_six {P Q : ℝ[X]} (hP : P.Monic) (hQ : Q.Monic) (hp : ∀ n, 0 ≤ P.coeff n)
    (hq : ∀ n, 0 ≤ Q.coeff n) (hp0 : P.coeff 0 = 1) (hq0 : Q.coeff 0 = 1)
    (hR : ∀ n, (P * Q).coeff n = 0 ∨ (P * Q).coeff n = 1) (hd : P.natDegree = 6) :
    ∀ n, P.coeff n = 0 ∨ P.coeff n = 1 := by
  have hRQ : ∀ n, (Q * P).coeff n = 0 ∨ (Q * P).coeff n = 1 := by
    rw [mul_comm]
    exact hR
  have hP1 := OMA.R_Mathoverflow339137_mathoverflow_339137_R1.coeff_le_one hQ hp hq hR
  have hQ1 := OMA.R_Mathoverflow339137_mathoverflow_339137_R1.coeff_le_one hP hq hp hRQ
  obtain ⟨hPr, hpr0, hdr, hcr⟩ := OMA.R_Mathoverflow339137_mathoverflow_339137_R1.rev_facts hP hp0
  obtain ⟨hQr, hqr0, -, -⟩ := OMA.R_Mathoverflow339137_mathoverflow_339137_R1.rev_facts hQ hq0
  have hpr : ∀ n, 0 ≤ P.reverse.coeff n := fun n => by rw [coeff_reverse]; exact hp _
  have hqr : ∀ n, 0 ≤ Q.reverse.coeff n := fun n => by rw [coeff_reverse]; exact hq _
  have hRr : ∀ n, (P.reverse * Q.reverse).coeff n = 0 ∨ (P.reverse * Q.reverse).coeff n = 1 := by
    intro n
    rw [← reverse_mul_of_domain, coeff_reverse]
    exact hR _
  have hRrQ : ∀ n, (Q.reverse * P.reverse).coeff n = 0 ∨
      (Q.reverse * P.reverse).coeff n = 1 := by
    rw [mul_comm]
    exact hRr
  have hPr1 := OMA.R_Mathoverflow339137_mathoverflow_339137_R1.coeff_le_one hQr hpr hqr hRr
  have hQr1 := OMA.R_Mathoverflow339137_mathoverflow_339137_R1.coeff_le_one hPr hqr hpr hRrQ
  have hdr6 : P.reverse.natDegree = 6 := by rw [hdr, hd]
  have rc1 : P.reverse.coeff 1 = P.coeff 5 := by rw [hcr 1 (by omega), hd]
  have rc2 : P.reverse.coeff 2 = P.coeff 4 := by rw [hcr 2 (by omega), hd]
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8⟩ := six_eqs hP hp0 hq0 hd hR
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩ := six_eqs hPr hpr0 hqr0 hdr6 hRr
  have hz1 : P.coeff 1 = 0 ∨ P.coeff 1 = 1 :=
    six_p1 (hp 1) (hP1 1) (hp 2) (hp 3) (hP1 3) (hp 4) (hP1 4) (hp 5) (hq 1) (hq 2) (hQ1 2)
      (hq 3) (hQ1 3) (hq 4) (hQ1 4) (hq 5) (hq 6) (hq 7) (hq 8) r1 r2 r3 r4 r5 r6 r7 r8
  have hz5 : P.coeff 5 = 0 ∨ P.coeff 5 = 1 := by
    rw [← rc1]
    exact six_p1 (hpr 1) (hPr1 1) (hpr 2) (hpr 3) (hPr1 3) (hpr 4) (hPr1 4) (hpr 5) (hqr 1)
      (hqr 2) (hQr1 2) (hqr 3) (hQr1 3) (hqr 4) (hQr1 4) (hqr 5) (hqr 6) (hqr 7) (hqr 8)
      s1 s2 s3 s4 s5 s6 s7 s8
  have hz2 : P.coeff 2 = 0 ∨ P.coeff 2 = 1 := by
    by_contra hne
    push_neg at hne
    exact six_p2 hz1 (lt_of_le_of_ne (hp 2) (Ne.symm hne.1)) (lt_of_le_of_ne (hP1 2) hne.2)
      (hp 3) (hp 4) (hp 5) (hq 1) (hq 2) (hq 3) (hq 4) (hq 5) (hq 6) r1 r2 r3 r4 r6
  have hz4 : P.coeff 4 = 0 ∨ P.coeff 4 = 1 := by
    by_contra hne
    push_neg at hne
    have hz1r : P.reverse.coeff 1 = 0 ∨ P.reverse.coeff 1 = 1 := by rw [rc1]; exact hz5
    have hb : 0 < P.reverse.coeff 2 := by
      rw [rc2]
      exact lt_of_le_of_ne (hp 4) (Ne.symm hne.1)
    have hb1 : P.reverse.coeff 2 < 1 := by
      rw [rc2]
      exact lt_of_le_of_ne (hP1 4) hne.2
    exact six_p2 hz1r hb hb1 (hpr 3) (hpr 4) (hpr 5) (hqr 1) (hqr 2) (hqr 3) (hqr 4) (hqr 5)
      (hqr 6) s1 s2 s3 s4 s6
  have hz3 : P.coeff 3 = 0 ∨ P.coeff 3 = 1 := by
    by_contra hne
    push_neg at hne
    exact six_p3 hz1 hz2 (lt_of_le_of_ne (hp 3) (Ne.symm hne.1)) (lt_of_le_of_ne (hP1 3) hne.2)
      (hp 4) (hp 5) (hq 1) (hq 2) (hq 3) (hq 4) (hq 5) (hq 6) r1 r2 r3 r6
  intro n
  rcases Nat.lt_or_ge 6 n with hn | hn
  · exact Or.inl (coeff_eq_zero_of_natDegree_lt (by omega))
  · have hp6 : P.coeff 6 = 1 := by rw [← hd]; exact hP.coeff_natDegree
    interval_cases n
    · exact Or.inr hp0
    · exact hz1
    · exact hz2
    · exact hz3
    · exact hz4
    · exact hz5
    · exact Or.inr hp6

theorem main : H1 → H2 → OMA.R_Mathoverflow339137_mathoverflow_339137_R1.H2 := by
  intro h1 h2 P Q hP hQ hp hq hp0 hq0 h5 hlt hR hgap
  have hR' := (OMA.R_Mathoverflow339137_mathoverflow_339137_R1.isZeroOne_iff _).mp hR
  rw [OMA.R_Mathoverflow339137_mathoverflow_339137_R1.isZeroOne_iff]
  rcases Nat.lt_or_ge P.natDegree 6 with h6 | h6
  · exact deg_five h1 hP hQ hp hq hp0 hq0 hR' (by omega) (by omega) hgap
  rcases Nat.lt_or_ge P.natDegree 7 with h7 | h7
  · exact deg_six hP hQ hp hq hp0 hq0 hR' (by omega)
  by_cases hPpal : P.reverse = P
  · exact zero_one_of_palindromic hP hQ hp hq hp0 hq0 hR' hPpal
  by_cases hQpal : Q.reverse = Q
  · have hRQ : ∀ n, (Q * P).coeff n = 0 ∨ (Q * P).coeff n = 1 := by
      rw [mul_comm]
      exact hR'
    have hzQ := zero_one_of_palindromic hQ hP hq hp hq0 hp0 hRQ hQpal
    exact OMA.R_Mathoverflow339137_mathoverflow_339137_R1.zo_of_zo hq0 hzQ hp hRQ
  rw [← OMA.R_Mathoverflow339137_mathoverflow_339137_R1.isZeroOne_iff]
  exact h2 P Q hP hQ hp hq hp0 hq0 h7 hlt hR hgap hPpal hQpal

end OMA.R_Mathoverflow339137_mathoverflow_339137_R1_H2_R1
