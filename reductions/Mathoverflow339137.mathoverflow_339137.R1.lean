import FormalConjectures.Mathoverflow.«339137»
import Mathlib

-- Reduction Mathoverflow339137.mathoverflow_339137.R1 of Mathoverflow 339137
-- Credit: @rickmanelius
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# The unfair 0-1 polynomial problem: small factors, normalization, and the two remaining cases

The target: if `P` and `Q` are monic real polynomials with nonnegative coefficients and `P * Q`
has all its coefficients in `{0, 1}`, then so do `P` and `Q`.

`main` proves, with no hypothesis:

* every coefficient of `P` and of `Q` lies in `[0, 1]` (the coefficient of `P * Q` at
  `i + deg Q` is at least `P_i`);
* normalization: stripping the powers of `X` from both factors loses nothing, and afterwards the
  constant terms are both `1`;
* if one normalized factor is a `0, 1` polynomial then so is the other (by induction on the index,
  the coefficient of `P * Q` at `k` is `Q_k` plus a natural number);
* after normalization the two factors have different degrees (otherwise the coefficient of
  `P * Q` at the common degree would be at least `2`);
* the whole target when the smaller factor has degree at most `4`: direct coefficient algebra on
  the coefficients `1, 2, 3, 4` of `P * Q`, together with the reversal symmetry
  `x^n P(1/x)`, which keeps every hypothesis.

What is left, for normalized factors of degree at least `5` (the smaller factor first):

* `H1`: the interval case `P * Q = 1 + x + ... + x^N` (`X + Y` uniform on an interval, in the
  probabilistic form of Green's Problem 28). Secondary sources attribute this case to Krasner and
  Ranulac (1937); that attribution has not been checked against the original paper.
* `H2`: products with at least one zero coefficient below the degree (the open core).
-/

open Polynomial Finset

namespace OMA.R_Mathoverflow339137_mathoverflow_339137_R1

open Mathoverflow339137

/-- The interval case: a factorization of `1 + x + ... + x^N` into monic polynomials with
nonnegative coefficients, the smaller factor of degree at least `5`, has `0, 1` factors. -/
def H1 : Prop :=
  ∀ (N : ℕ) (P Q : ℝ[X]), P.Monic → Q.Monic → (∀ n, 0 ≤ P.coeff n) → (∀ n, 0 ≤ Q.coeff n) →
    5 ≤ P.natDegree → P.natDegree < Q.natDegree →
    P * Q = ∑ k ∈ range (N + 1), (X : ℝ[X]) ^ k → IsZeroOne P

/-- The gap case: normalized factors (constant terms `1`), the smaller of degree at least `5`,
whose product is a `0, 1` polynomial with a zero coefficient below its degree. -/
def H2 : Prop :=
  ∀ P Q : ℝ[X], P.Monic → Q.Monic → (∀ n, 0 ≤ P.coeff n) → (∀ n, 0 ≤ Q.coeff n) →
    P.coeff 0 = 1 → Q.coeff 0 = 1 → 5 ≤ P.natDegree → P.natDegree < Q.natDegree →
    IsZeroOne (P * Q) → (∃ k < (P * Q).natDegree, (P * Q).coeff k = 0) → IsZeroOne P

-- Coefficient forms of the hypotheses

lemma isZeroOne_iff (F : ℝ[X]) : IsZeroOne F ↔ ∀ n, F.coeff n = 0 ∨ F.coeff n = 1 := by
  unfold IsZeroOne
  constructor
  · intro h n
    by_cases h0 : F.coeff n = 0
    · exact Or.inl h0
    · right
      have hmem : F.coeff n ∈ F.coeffs := mem_coeffs_iff.mpr ⟨n, mem_support_iff.mpr h0, rfl⟩
      simpa using h hmem
  · intro h c hc
    obtain ⟨n, hn, rfl⟩ := mem_coeffs_iff.mp hc
    rcases h n with h0 | h1
    · exact absurd h0 (mem_support_iff.mp hn)
    · simp [h1]

lemma nonneg_iff (F : ℝ[X]) : (∀ c ∈ F.coeffs, 0 ≤ c) ↔ ∀ n, 0 ≤ F.coeff n := by
  constructor
  · intro h n
    by_cases h0 : F.coeff n = 0
    · rw [h0]
    · exact h _ (mem_coeffs_iff.mpr ⟨n, mem_support_iff.mpr h0, rfl⟩)
  · intro h c hc
    obtain ⟨n, -, rfl⟩ := mem_coeffs_iff.mp hc
    exact h n

-- Coefficient bounds, one factor `0, 1` forces the other, degrees differ

/-- Every coefficient of `P` is at most `1`: the coefficient of `P * Q` at `i + deg Q` is at
least `P_i * 1`. -/
lemma coeff_le_one {P Q : ℝ[X]} (hQ : Q.Monic) (hp : ∀ n, 0 ≤ P.coeff n)
    (hq : ∀ n, 0 ≤ Q.coeff n) (hR : ∀ n, (P * Q).coeff n = 0 ∨ (P * Q).coeff n = 1) (i : ℕ) :
    P.coeff i ≤ 1 := by
  have hmem : (i, Q.natDegree) ∈ antidiagonal (i + Q.natDegree) := mem_antidiagonal.mpr rfl
  have hle : P.coeff i * Q.coeff Q.natDegree ≤ (P * Q).coeff (i + Q.natDegree) := by
    rw [coeff_mul]
    exact single_le_sum (f := fun x : ℕ × ℕ => P.coeff x.1 * Q.coeff x.2)
      (fun x _ => mul_nonneg (hp _) (hq _)) hmem
  rw [hQ.coeff_natDegree, mul_one] at hle
  rcases hR (i + Q.natDegree) with h | h <;> linarith

/-- A sum of natural-number values is a natural number. -/
lemma sum_nat {s : Finset (ℕ × ℕ)} {f : ℕ × ℕ → ℝ} (h : ∀ x ∈ s, ∃ m : ℕ, f x = m) :
    ∃ m : ℕ, ∑ x ∈ s, f x = m := by
  apply Finset.sum_induction f (fun y => ∃ m : ℕ, y = m)
  · rintro a b ⟨m, rfl⟩ ⟨k, rfl⟩
    exact ⟨m + k, by push_cast; ring⟩
  · exact ⟨0, by simp⟩
  · exact h

/-- If `P` is a `0, 1` polynomial with constant term `1` and `P * Q` is a `0, 1` polynomial with
`Q` nonnegative, then `Q` is a `0, 1` polynomial: the coefficient of `P * Q` at `k` is `Q_k` plus
a natural number. -/
lemma zo_of_zo {P Q : ℝ[X]} (hp0 : P.coeff 0 = 1) (hpz : ∀ n, P.coeff n = 0 ∨ P.coeff n = 1)
    (hq : ∀ n, 0 ≤ Q.coeff n) (hR : ∀ n, (P * Q).coeff n = 0 ∨ (P * Q).coeff n = 1) :
    ∀ n, Q.coeff n = 0 ∨ Q.coeff n = 1 := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    have hmem : ((0 : ℕ), k) ∈ antidiagonal k := mem_antidiagonal.mpr (zero_add k)
    have hsplit := Finset.add_sum_erase (antidiagonal k)
      (fun x : ℕ × ℕ => P.coeff x.1 * Q.coeff x.2) hmem
    obtain ⟨s, hs⟩ : ∃ s : ℕ,
        ∑ x ∈ (antidiagonal k).erase (0, k), P.coeff x.1 * Q.coeff x.2 = s := by
      apply sum_nat
      intro x hx
      have hx1 := Finset.mem_erase.mp hx
      have hx2 := mem_antidiagonal.mp hx1.2
      have hne : x.1 ≠ 0 := by
        intro h0
        apply hx1.1
        exact Prod.ext h0 (by show x.2 = k; omega)
      have hlt : x.2 < k := by omega
      rcases hpz x.1 with h1 | h1 <;> rcases ih x.2 hlt with h2 | h2
      exacts [⟨0, by simp [h1, h2]⟩, ⟨0, by simp [h1, h2]⟩, ⟨0, by simp [h1, h2]⟩,
        ⟨1, by simp [h1, h2]⟩]
    have hrk := hR k
    rw [coeff_mul, ← hsplit, hs] at hrk
    simp only [hp0, one_mul] at hrk
    have hqk := hq k
    rcases Nat.eq_zero_or_pos s with h0 | hpos
    · subst h0
      simpa using hrk
    · left
      have : (1 : ℝ) ≤ s := by exact_mod_cast hpos
      rcases hrk with h | h <;> linarith

/-- After normalization the two degrees differ: otherwise the coefficient of `P * Q` at the
common degree `m` is at least `P_0 Q_m + P_m Q_0 = 2`. -/
lemma natDegree_ne {P Q : ℝ[X]} (hP : P.Monic) (hQ : Q.Monic) (hp : ∀ n, 0 ≤ P.coeff n)
    (hq : ∀ n, 0 ≤ Q.coeff n) (hp0 : P.coeff 0 = 1) (hq0 : Q.coeff 0 = 1)
    (hR : ∀ n, (P * Q).coeff n = 0 ∨ (P * Q).coeff n = 1) (h1 : 1 ≤ P.natDegree) :
    P.natDegree ≠ Q.natDegree := by
  intro heq
  have hPm : P.coeff P.natDegree = 1 := hP.coeff_natDegree
  have hQm : Q.coeff P.natDegree = 1 := by rw [heq]; exact hQ.coeff_natDegree
  have hsub : ({((0 : ℕ), P.natDegree), (P.natDegree, 0)} : Finset (ℕ × ℕ)) ⊆
      antidiagonal P.natDegree := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [HasAntidiagonal.mem_antidiagonal]
  have hne : ((0 : ℕ), P.natDegree) ≠ (P.natDegree, 0) := by
    intro h
    have := congrArg Prod.fst h
    simp only at this
    omega
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun x : ℕ × ℕ => P.coeff x.1 * Q.coeff x.2) (fun x _ _ => mul_nonneg (hp _) (hq _))
  rw [Finset.sum_pair hne, ← coeff_mul] at hle
  simp only [hp0, hq0, hPm, hQm] at hle
  rcases hR P.natDegree with h | h <;> linarith

-- Small degrees: coefficient algebra

lemma c1 (P Q : ℝ[X]) :
    (P * Q).coeff 1 = P.coeff 0 * Q.coeff 1 + P.coeff 1 * Q.coeff 0 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

lemma c2 (P Q : ℝ[X]) :
    (P * Q).coeff 2 = P.coeff 0 * Q.coeff 2 + P.coeff 1 * Q.coeff 1 + P.coeff 2 * Q.coeff 0 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

lemma c3 (P Q : ℝ[X]) :
    (P * Q).coeff 3 = P.coeff 0 * Q.coeff 3 + P.coeff 1 * Q.coeff 2 + P.coeff 2 * Q.coeff 1 +
      P.coeff 3 * Q.coeff 0 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

lemma c4 (P Q : ℝ[X]) :
    (P * Q).coeff 4 = P.coeff 0 * Q.coeff 4 + P.coeff 1 * Q.coeff 3 + P.coeff 2 * Q.coeff 2 +
      P.coeff 3 * Q.coeff 1 + P.coeff 4 * Q.coeff 0 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

/-- Degree 2: `P = 1 + a x + x^2`. The coefficient at `2` forces `a q_1 = 0`, then the
coefficient at `1` is `a`. -/
lemma bottom_two {a q1 q2 : ℝ} (ha : 0 ≤ a) (hq1 : 0 ≤ q1) (hq2 : 0 ≤ q2)
    (r1 : q1 + a = 0 ∨ q1 + a = 1) (r2 : q2 + a * q1 + 1 = 0 ∨ q2 + a * q1 + 1 = 1) :
    a = 0 ∨ a = 1 := by
  have e := mul_nonneg ha hq1
  have haq : a * q1 = 0 := by rcases r2 with h | h <;> linarith
  rcases eq_or_lt_of_le ha with h0 | hpos
  · exact Or.inl h0.symm
  · have hq10 : q1 = 0 := by
      rcases mul_eq_zero.mp haq with h | h
      · linarith
      · exact h
    rw [hq10, zero_add] at r1
    exact r1

/-- Degree 3: `P = 1 + b x + a x^2 + x^3`, then `b` is `0` or `1`. -/
lemma bottom_three {b a q1 q2 q3 : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1) (ha : 0 ≤ a) (hq1 : 0 ≤ q1)
    (hq2 : 0 ≤ q2) (hq3 : 0 ≤ q3)
    (r1 : q1 + b = 0 ∨ q1 + b = 1) (r2 : q2 + b * q1 + a = 0 ∨ q2 + b * q1 + a = 1)
    (r3 : q3 + b * q2 + a * q1 + 1 = 0 ∨ q3 + b * q2 + a * q1 + 1 = 1) :
    b = 0 ∨ b = 1 := by
  have e1 := mul_nonneg hb hq2
  have e2 := mul_nonneg ha hq1
  have hbq2 : b * q2 = 0 := by rcases r3 with h | h <;> linarith
  have haq1 : a * q1 = 0 := by rcases r3 with h | h <;> linarith
  by_contra hne
  push_neg at hne
  have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hne.1)
  have hblt : b < 1 := lt_of_le_of_ne hb1 hne.2
  have hq2z : q2 = 0 := by
    rcases mul_eq_zero.mp hbq2 with h | h
    · linarith
    · exact h
  have hq1v : q1 = 1 - b := by rcases r1 with h | h <;> linarith
  have haz : a = 0 := by
    rcases mul_eq_zero.mp haq1 with h | h
    · exact h
    · linarith
  rw [hq2z, hq1v, haz] at r2
  rcases r2 with h | h
  · nlinarith [mul_pos hbpos (sub_pos.mpr hblt)]
  · nlinarith [sq_nonneg (b - 1 / 2)]

/-- Degree 4: `P = 1 + c x + b x^2 + a x^3 + x^4`, then `c` is `0` or `1`. -/
lemma bottom_four {c b a q1 q2 q3 q4 : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (ha : 0 ≤ a) (hq1 : 0 ≤ q1) (hq2 : 0 ≤ q2) (hq3 : 0 ≤ q3) (hq4 : 0 ≤ q4)
    (r1 : q1 + c = 0 ∨ q1 + c = 1) (r2 : q2 + c * q1 + b = 0 ∨ q2 + c * q1 + b = 1)
    (r3 : q3 + c * q2 + b * q1 + a = 0 ∨ q3 + c * q2 + b * q1 + a = 1)
    (r4 : q4 + c * q3 + b * q2 + a * q1 + 1 = 0 ∨ q4 + c * q3 + b * q2 + a * q1 + 1 = 1) :
    c = 0 ∨ c = 1 := by
  have e1 := mul_nonneg hc hq3
  have e2 := mul_nonneg hb hq2
  have e3 := mul_nonneg ha hq1
  have hcq3 : c * q3 = 0 := by rcases r4 with h | h <;> linarith
  have hbq2 : b * q2 = 0 := by rcases r4 with h | h <;> linarith
  have haq1 : a * q1 = 0 := by rcases r4 with h | h <;> linarith
  by_contra hne
  push_neg at hne
  have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hne.1)
  have hclt : c < 1 := lt_of_le_of_ne hc1 hne.2
  have hq3z : q3 = 0 := by
    rcases mul_eq_zero.mp hcq3 with h | h
    · linarith
    · exact h
  have hq1v : q1 = 1 - c := by rcases r1 with h | h <;> linarith
  have haz : a = 0 := by
    rcases mul_eq_zero.mp haq1 with h | h
    · exact h
    · linarith
  have hcq1 : 0 < c * q1 := by rw [hq1v]; exact mul_pos hcpos (by linarith)
  have hr2 : q2 + c * q1 + b = 1 := by
    rcases r2 with h | h
    · linarith
    · exact h
  rcases eq_or_lt_of_le hb with hb0 | hbpos
  · rw [← hb0] at hr2 r3
    have hq2v : q2 = 1 - c * (1 - c) := by rw [hq1v] at hr2; linarith
    rw [hq3z, hq2v, haz, hq1v] at r3
    have hpos2 : 0 < 1 - c * (1 - c) := by nlinarith
    rcases r3 with h | h
    · nlinarith [mul_pos hcpos hpos2]
    · nlinarith [mul_pos (sub_pos.mpr hclt) (by positivity : (0 : ℝ) < c ^ 2 + 1)]
  · have hq2z : q2 = 0 := by
      rcases mul_eq_zero.mp hbq2 with h | h
      · linarith
      · exact h
    rw [hq3z, hq2z, haz, hq1v] at r3
    rcases r3 with h | h
    · nlinarith [mul_pos hbpos (sub_pos.mpr hclt)]
    · nlinarith [mul_le_mul_of_nonneg_right hb1 (sub_nonneg.mpr hc1)]

/-- Degree 4, middle coefficient: once `c` is `0` or `1`, so is `b`. -/
lemma middle_four {c b a q1 q2 q3 q4 : ℝ} (hc : c = 0 ∨ c = 1) (hc0 : 0 ≤ c) (hb : 0 ≤ b)
    (ha : 0 ≤ a) (hq1 : 0 ≤ q1) (hq2 : 0 ≤ q2) (hq3 : 0 ≤ q3) (hq4 : 0 ≤ q4)
    (r1 : q1 + c = 0 ∨ q1 + c = 1) (r2 : q2 + c * q1 + b = 0 ∨ q2 + c * q1 + b = 1)
    (r4 : q4 + c * q3 + b * q2 + a * q1 + 1 = 0 ∨ q4 + c * q3 + b * q2 + a * q1 + 1 = 1) :
    b = 0 ∨ b = 1 := by
  have e1 := mul_nonneg hc0 hq3
  have e2 := mul_nonneg hb hq2
  have e3 := mul_nonneg ha hq1
  have hbq2 : b * q2 = 0 := by rcases r4 with h | h <;> linarith
  rcases eq_or_lt_of_le hb with hb0 | hbpos
  · exact Or.inl hb0.symm
  · have hq2z : q2 = 0 := by
      rcases mul_eq_zero.mp hbq2 with h | h
      · linarith
      · exact h
    rcases hc with hc | hc
    · rw [hq2z, hc] at r2
      simpa using r2
    · have hq1z : q1 = 0 := by
        rw [hc] at r1
        rcases r1 with h | h <;> linarith
      rw [hq2z, hc, hq1z] at r2
      simpa using r2

-- Small degrees: polynomial wrappers

lemma deg_two_coeff_one {P Q : ℝ[X]} (hP : P.Monic) (hp : ∀ n, 0 ≤ P.coeff n)
    (hq : ∀ n, 0 ≤ Q.coeff n) (hp0 : P.coeff 0 = 1) (hq0 : Q.coeff 0 = 1)
    (hR : ∀ n, (P * Q).coeff n = 0 ∨ (P * Q).coeff n = 1) (hd : P.natDegree = 2) :
    P.coeff 1 = 0 ∨ P.coeff 1 = 1 := by
  have hp2 : P.coeff 2 = 1 := by rw [← hd]; exact hP.coeff_natDegree
  have e1 : (P * Q).coeff 1 = Q.coeff 1 + P.coeff 1 := by rw [c1, hp0, hq0]; ring
  have e2 : (P * Q).coeff 2 = Q.coeff 2 + P.coeff 1 * Q.coeff 1 + 1 := by
    rw [c2, hp0, hq0, hp2]; ring
  have r1 := hR 1
  have r2 := hR 2
  rw [e1] at r1
  rw [e2] at r2
  exact bottom_two (hp 1) (hq 1) (hq 2) r1 r2

lemma deg_three_coeff_one {P Q : ℝ[X]} (hP : P.Monic) (hQ : Q.Monic) (hp : ∀ n, 0 ≤ P.coeff n)
    (hq : ∀ n, 0 ≤ Q.coeff n) (hp0 : P.coeff 0 = 1) (hq0 : Q.coeff 0 = 1)
    (hR : ∀ n, (P * Q).coeff n = 0 ∨ (P * Q).coeff n = 1) (hd : P.natDegree = 3) :
    P.coeff 1 = 0 ∨ P.coeff 1 = 1 := by
  have hp3 : P.coeff 3 = 1 := by rw [← hd]; exact hP.coeff_natDegree
  have e1 : (P * Q).coeff 1 = Q.coeff 1 + P.coeff 1 := by rw [c1, hp0, hq0]; ring
  have e2 : (P * Q).coeff 2 = Q.coeff 2 + P.coeff 1 * Q.coeff 1 + P.coeff 2 := by
    rw [c2, hp0, hq0]; ring
  have e3 : (P * Q).coeff 3 =
      Q.coeff 3 + P.coeff 1 * Q.coeff 2 + P.coeff 2 * Q.coeff 1 + 1 := by
    rw [c3, hp0, hq0, hp3]; ring
  have r1 := hR 1
  have r2 := hR 2
  have r3 := hR 3
  rw [e1] at r1
  rw [e2] at r2
  rw [e3] at r3
  exact bottom_three (hp 1) (coeff_le_one hQ hp hq hR 1) (hp 2) (hq 1) (hq 2) (hq 3) r1 r2 r3

lemma deg_four_coeffs {P Q : ℝ[X]} (hP : P.Monic) (hQ : Q.Monic) (hp : ∀ n, 0 ≤ P.coeff n)
    (hq : ∀ n, 0 ≤ Q.coeff n) (hp0 : P.coeff 0 = 1) (hq0 : Q.coeff 0 = 1)
    (hR : ∀ n, (P * Q).coeff n = 0 ∨ (P * Q).coeff n = 1) (hd : P.natDegree = 4) :
    (P.coeff 1 = 0 ∨ P.coeff 1 = 1) ∧ (P.coeff 2 = 0 ∨ P.coeff 2 = 1) := by
  have hp4 : P.coeff 4 = 1 := by rw [← hd]; exact hP.coeff_natDegree
  have e1 : (P * Q).coeff 1 = Q.coeff 1 + P.coeff 1 := by rw [c1, hp0, hq0]; ring
  have e2 : (P * Q).coeff 2 = Q.coeff 2 + P.coeff 1 * Q.coeff 1 + P.coeff 2 := by
    rw [c2, hp0, hq0]; ring
  have e3 : (P * Q).coeff 3 =
      Q.coeff 3 + P.coeff 1 * Q.coeff 2 + P.coeff 2 * Q.coeff 1 + P.coeff 3 := by
    rw [c3, hp0, hq0]; ring
  have e4 : (P * Q).coeff 4 = Q.coeff 4 + P.coeff 1 * Q.coeff 3 + P.coeff 2 * Q.coeff 2 +
      P.coeff 3 * Q.coeff 1 + 1 := by
    rw [c4, hp0, hq0, hp4]; ring
  have r1 := hR 1
  have r2 := hR 2
  have r3 := hR 3
  have r4 := hR 4
  rw [e1] at r1
  rw [e2] at r2
  rw [e3] at r3
  rw [e4] at r4
  have h1 := bottom_four (hp 1) (coeff_le_one hQ hp hq hR 1) (hp 2) (coeff_le_one hQ hp hq hR 2)
    (hp 3) (hq 1) (hq 2) (hq 3) (hq 4) r1 r2 r3 r4
  exact ⟨h1, middle_four h1 (hp 1) (hp 2) (hp 3) (hq 1) (hq 2) (hq 3) (hq 4) r1 r2 r4⟩

/-- Reversal `x^n P(1/x)` of a monic polynomial with constant term `1`. -/
lemma rev_facts {P : ℝ[X]} (hP : P.Monic) (hp0 : P.coeff 0 = 1) :
    P.reverse.Monic ∧ P.reverse.coeff 0 = 1 ∧ P.reverse.natDegree = P.natDegree ∧
      ∀ i ≤ P.natDegree, P.reverse.coeff i = P.coeff (P.natDegree - i) := by
  have hnt : P.natTrailingDegree = 0 :=
    natTrailingDegree_eq_zero.mpr (Or.inr (by rw [hp0]; norm_num))
  refine ⟨?_, ?_, ?_, ?_⟩
  · show P.reverse.leadingCoeff = 1
    rw [reverse_leadingCoeff]
    show P.coeff P.natTrailingDegree = 1
    rw [hnt, hp0]
  · rw [coeff_zero_reverse]
    exact hP.leadingCoeff
  · rw [reverse_natDegree, hnt, Nat.sub_zero]
  · intro i hi
    rw [coeff_reverse, revAt_le hi]

/-- The target when the factor `P` has degree at most `4` (after normalization). -/
lemma small_deg {P Q : ℝ[X]} (hP : P.Monic) (hQ : Q.Monic) (hp : ∀ n, 0 ≤ P.coeff n)
    (hq : ∀ n, 0 ≤ Q.coeff n) (hp0 : P.coeff 0 = 1) (hq0 : Q.coeff 0 = 1)
    (hR : ∀ n, (P * Q).coeff n = 0 ∨ (P * Q).coeff n = 1) (hd : P.natDegree ≤ 4) :
    ∀ n, P.coeff n = 0 ∨ P.coeff n = 1 := by
  obtain ⟨hPr, hpr0, hdr, hcr⟩ := rev_facts hP hp0
  obtain ⟨hQr, hqr0, -, -⟩ := rev_facts hQ hq0
  have hpr : ∀ n, 0 ≤ P.reverse.coeff n := fun n => by rw [coeff_reverse]; exact hp _
  have hqr : ∀ n, 0 ≤ Q.reverse.coeff n := fun n => by rw [coeff_reverse]; exact hq _
  have hRr : ∀ n, (P.reverse * Q.reverse).coeff n = 0 ∨ (P.reverse * Q.reverse).coeff n = 1 := by
    intro n
    rw [← reverse_mul_of_domain, coeff_reverse]
    exact hR _
  have htop : P.coeff P.natDegree = 1 := hP.coeff_natDegree
  intro n
  rcases lt_or_ge P.natDegree n with hlt | hle
  · exact Or.inl (coeff_eq_zero_of_natDegree_lt hlt)
  obtain ⟨m, hm⟩ : ∃ m, P.natDegree = m := ⟨_, rfl⟩
  rw [hm] at hd hle htop hdr hcr
  interval_cases m
  · interval_cases n
    exact Or.inr hp0
  · interval_cases n
    · exact Or.inr hp0
    · exact Or.inr htop
  · interval_cases n
    · exact Or.inr hp0
    · exact deg_two_coeff_one hP hp hq hp0 hq0 hR hm
    · exact Or.inr htop
  · interval_cases n
    · exact Or.inr hp0
    · exact deg_three_coeff_one hP hQ hp hq hp0 hq0 hR hm
    · have h := deg_three_coeff_one hPr hQr hpr hqr hpr0 hqr0 hRr hdr
      rwa [hcr 1 (by norm_num)] at h
    · exact Or.inr htop
  · interval_cases n
    · exact Or.inr hp0
    · exact (deg_four_coeffs hP hQ hp hq hp0 hq0 hR hm).1
    · exact (deg_four_coeffs hP hQ hp hq hp0 hq0 hR hm).2
    · have h := (deg_four_coeffs hPr hQr hpr hqr hpr0 hqr0 hRr hdr).1
      rwa [hcr 1 (by norm_num)] at h
    · exact Or.inr htop

-- Assembly

/-- Normalization: strip the powers of `X`. -/
lemma strip {P : ℝ[X]} (hP : P.Monic) :
    ∃ (k : ℕ) (P1 : ℝ[X]), P = X ^ k * P1 ∧ P1.Monic ∧ P1.coeff 0 ≠ 0 := by
  obtain ⟨P1, h1, h2⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd P hP.ne_zero 0
  simp only [map_zero, sub_zero] at h1 h2
  refine ⟨_, P1, h1, ?_, ?_⟩
  · rw [h1] at hP
    exact Monic.of_mul_monic_left (monic_X_pow _) hP
  · rwa [X_dvd_iff] at h2

/-- A product with no zero coefficient below its degree is `1 + x + ... + x^N`. -/
lemma interval_of_no_gap {R : ℝ[X]} (hRm : R.Monic)
    (hR : ∀ n, R.coeff n = 0 ∨ R.coeff n = 1) (hng : ¬ ∃ k < R.natDegree, R.coeff k = 0) :
    R = ∑ k ∈ range (R.natDegree + 1), (X : ℝ[X]) ^ k := by
  ext n
  rw [finsetSum_coeff]
  simp only [coeff_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rw [mem_range] at h
    rcases Nat.lt_or_ge n R.natDegree with hlt | hge
    · rcases hR n with h0 | h1
      · exact absurd ⟨n, hlt, h0⟩ hng
      · exact h1
    · have : n = R.natDegree := by omega
      rw [this]
      exact hRm.coeff_natDegree
  · rw [mem_range] at h
    exact coeff_eq_zero_of_natDegree_lt (by omega)

/-- The normalized case with the smaller factor first and of degree at least `5`. -/
lemma ordered (h1 : H1) (h2 : H2) {P Q : ℝ[X]} (hP : P.Monic) (hQ : Q.Monic)
    (hp : ∀ n, 0 ≤ P.coeff n) (hq : ∀ n, 0 ≤ Q.coeff n) (hp0 : P.coeff 0 = 1)
    (hq0 : Q.coeff 0 = 1) (hR : ∀ n, (P * Q).coeff n = 0 ∨ (P * Q).coeff n = 1)
    (h5 : 5 ≤ P.natDegree) (hlt : P.natDegree < Q.natDegree) :
    ∀ n, P.coeff n = 0 ∨ P.coeff n = 1 := by
  rw [← isZeroOne_iff]
  by_cases hgap : ∃ k < (P * Q).natDegree, (P * Q).coeff k = 0
  · exact h2 P Q hP hQ hp hq hp0 hq0 h5 hlt ((isZeroOne_iff _).mpr hR) hgap
  · exact h1 _ P Q hP hQ hp hq h5 hlt (interval_of_no_gap (hP.mul hQ) hR hgap)

/-- The target for factors with nonzero constant terms. -/
lemma core (h1 : H1) (h2 : H2) {P Q : ℝ[X]} (hP : P.Monic) (hQ : Q.Monic)
    (hp : ∀ n, 0 ≤ P.coeff n) (hq : ∀ n, 0 ≤ Q.coeff n) (hp0 : P.coeff 0 ≠ 0)
    (hq0 : Q.coeff 0 ≠ 0) (hR : ∀ n, (P * Q).coeff n = 0 ∨ (P * Q).coeff n = 1) :
    (∀ n, P.coeff n = 0 ∨ P.coeff n = 1) ∧ (∀ n, Q.coeff n = 0 ∨ Q.coeff n = 1) := by
  have hRQ : ∀ n, (Q * P).coeff n = 0 ∨ (Q * P).coeff n = 1 := by
    rw [mul_comm]
    exact hR
  have hP1 := coeff_le_one hQ hp hq hR 0
  have hQ1 := coeff_le_one hP hq hp hRQ 0
  have h00 : (P * Q).coeff 0 = P.coeff 0 * Q.coeff 0 := mul_coeff_zero P Q
  have hc : P.coeff 0 * Q.coeff 0 = 1 := by
    rcases hR 0 with h | h
    · rw [h00] at h
      exact absurd h (mul_ne_zero hp0 hq0)
    · rw [h00] at h
      exact h
  have hpp := hp 0
  have hqq := hq 0
  have hp01 : P.coeff 0 = 1 := le_antisymm hP1 (by nlinarith)
  have hq01 : Q.coeff 0 = 1 := le_antisymm hQ1 (by nlinarith)
  by_cases hsP : P.natDegree ≤ 4
  · have hz := small_deg hP hQ hp hq hp01 hq01 hR hsP
    exact ⟨hz, zo_of_zo hp01 hz hq hR⟩
  by_cases hsQ : Q.natDegree ≤ 4
  · have hz := small_deg hQ hP hq hp hq01 hp01 hRQ hsQ
    exact ⟨zo_of_zo hq01 hz hp hRQ, hz⟩
  push_neg at hsP hsQ
  have hne := natDegree_ne hP hQ hp hq hp01 hq01 hR (by omega)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hz := ordered h1 h2 hP hQ hp hq hp01 hq01 hR (by omega) hlt
    exact ⟨hz, zo_of_zo hp01 hz hq hR⟩
  · have hz := ordered h1 h2 hQ hP hq hp hq01 hp01 hRQ (by omega) hgt
    exact ⟨zo_of_zo hq01 hz hp hRQ, hz⟩

theorem main : H1 → H2 → type_of% @Mathoverflow339137.mathoverflow_339137 := by
  intro h1 h2 P Q R hP hQ hp hq h hR
  subst h
  rw [nonneg_iff] at hp hq
  rw [isZeroOne_iff] at hR
  rw [isZeroOne_iff, isZeroOne_iff]
  obtain ⟨k, P1, rfl, hP1, hP10⟩ := strip hP
  obtain ⟨l, Q1, rfl, hQ1, hQ10⟩ := strip hQ
  have hp1 : ∀ n, 0 ≤ P1.coeff n := fun n => by
    have := hp (n + k)
    rwa [coeff_X_pow_mul] at this
  have hq1 : ∀ n, 0 ≤ Q1.coeff n := fun n => by
    have := hq (n + l)
    rwa [coeff_X_pow_mul] at this
  have hR1 : ∀ n, (P1 * Q1).coeff n = 0 ∨ (P1 * Q1).coeff n = 1 := by
    intro n
    have := hR (n + (k + l))
    have e : X ^ k * P1 * (X ^ l * Q1) = X ^ (k + l) * (P1 * Q1) := by ring
    rwa [e, coeff_X_pow_mul] at this
  obtain ⟨hzP, hzQ⟩ := core h1 h2 hP1 hQ1 hp1 hq1 hP10 hQ10 hR1
  constructor
  · intro n
    rw [coeff_X_pow_mul']
    split_ifs
    exacts [hzP _, Or.inl rfl]
  · intro n
    rw [coeff_X_pow_mul']
    split_ifs
    exacts [hzQ _, Or.inl rfl]

end OMA.R_Mathoverflow339137_mathoverflow_339137_R1
