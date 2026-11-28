import OMAReductions.R_LebesgueNagell_lebesgue_nagell_R1
import Mathlib

-- Reduction LebesgueNagell.lebesgue_nagell.R1.H1.R1 of step LebesgueNagell.lebesgue_nagell.R1.H1
-- Credit: @rickmanelius

/-! Classical descent in Z[r], r = sqrt 2, for the forward direction of x^2 - 2 = y^p.

Let p be an odd prime and x^2 - 2 = y^p. Then x is odd, so the factors x + r and x - r of y^p
are coprime (explicit Bezout witnesses). Z[r] (`Zsqrtd 2`) is a principal ideal ring: a nonzero
element of least absolute norm generates an ideal, because rounding the quotient gives a
remainder of absolute norm at most half. So x + r is a unit times a p-th power. A descent on the
r-coefficient shows that every unit is plus or minus (1 + r)^n or (r - 1)^n, and p-th powers
absorb all of it except (1 + r)^j with 0 <= j < p:

  x + r = (1 + r)^j (a + b r)^p.

Conjugating and multiplying by -1 turns a solution x with exponent j into the solution -x with
exponent p - j, so only 0 <= j < p/2 needs an argument. Comparing r-coefficients gives one
binary form equation of degree p in (a, b) for each j. For j = 0 the coefficient is b times a
sum of nonnegative terms whose last term is 2^((p-1)/2) >= 2, so it is never 1; this file
proves it. The other cases are the two Thue statements below. H1 is the case j = 1: its only
solution (a, b) = (1, 0) gives x = 1 (and x = -1 through the exponent p - 1). H2 is the case
1 < j < p/2, with no solutions at all. Both follow from the Lebesgue-Nagell theorem itself
(then x = 1 or -1 and the unit exponent is forced). A brute-force search for p up to 13 and
|a|, |b| <= 60 finds no other solutions. Finally y^p = -1 gives y = -1. -/

namespace OMA.R_LebesgueNagell_lebesgue_nagell_R1_H1_R1

/-- Case j = 1. The r-coefficient of (1 + r) (a + b r)^p, with r = sqrt 2, is
the sum over k of C(p,k) a^(p-k) b^k 2^(k/2) (floor). It is 1 only for (a, b) = (1, 0). -/
def H1 : Prop :=
  ∀ (p : ℕ), p.Prime → Odd p → ∀ (a b : ℤ),
    ∑ k ∈ Finset.range (p + 1), (p.choose k : ℤ) * a ^ (p - k) * b ^ k * 2 ^ (k / 2) = 1 →
      a = 1 ∧ b = 0

/-- Cases 1 < j < p/2. Write (1 + r)^j = u + v r and (a + b r)^p = A + B r, with r = sqrt 2,
each part as its binomial sum. Then u B + v A = 1 has no integer solution. (The cases
p/2 < j < p turn into p - j under conjugation, and `main` handles them.) -/
def H2 : Prop :=
  ∀ (p : ℕ), p.Prime → Odd p → ∀ (j : ℕ), 1 < j → 2 * j < p → ∀ (a b : ℤ),
    (∑ l ∈ Finset.range (j + 1), if l % 2 = 0 then (j.choose l : ℤ) * 2 ^ (l / 2) else 0) *
        (∑ k ∈ Finset.range (p + 1),
          if k % 2 = 1 then (p.choose k : ℤ) * a ^ (p - k) * b ^ k * 2 ^ (k / 2) else 0) +
      (∑ l ∈ Finset.range (j + 1), if l % 2 = 1 then (j.choose l : ℤ) * 2 ^ (l / 2) else 0) *
        (∑ k ∈ Finset.range (p + 1),
          if k % 2 = 0 then (p.choose k : ℤ) * a ^ (p - k) * b ^ k * 2 ^ (k / 2) else 0) = 1 →
      False

open Finset

/-- Powers of r = sqrt 2. -/
lemma sqrtd_pow (k : ℕ) : (Zsqrtd.sqrtd ^ k : Zsqrtd 2) =
    ⟨if k % 2 = 0 then 2 ^ (k / 2) else 0, if k % 2 = 1 then 2 ^ (k / 2) else 0⟩ := by
  induction k with
  | zero => ext <;> simp
  | succ k ih =>
    rw [pow_succ, ih]
    rcases Nat.mod_two_eq_zero_or_one k with h | h
    · have h' : (k + 1) % 2 = 1 := by omega
      have h'' : (k + 1) / 2 = k / 2 := by omega
      ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul, h, h', h'']
    · have h' : (k + 1) % 2 = 0 := by omega
      have h'' : (k + 1) / 2 = k / 2 + 1 := by omega
      ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul, h, h', h'', pow_succ]
      ring

lemma re_sum (s : Finset ℕ) (f : ℕ → Zsqrtd 2) : (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re := by
  refine Finset.induction_on s (by simp) ?_
  intro i s hi ih
  rw [sum_insert hi, sum_insert hi, Zsqrtd.re_add, ih]

lemma im_sum (s : Finset ℕ) (f : ℕ → Zsqrtd 2) : (∑ i ∈ s, f i).im = ∑ i ∈ s, (f i).im := by
  refine Finset.induction_on s (by simp) ?_
  intro i s hi ih
  rw [sum_insert hi, sum_insert hi, Zsqrtd.im_add, ih]

/-- Binomial expansion of (a + b r)^n. -/
lemma pow_expand (a b : ℤ) (n : ℕ) : ((⟨a, b⟩ : Zsqrtd 2) ^ n) =
    ∑ k ∈ range (n + 1), (((n.choose k : ℤ) * a ^ (n - k) * b ^ k : ℤ) : Zsqrtd 2) *
      (Zsqrtd.sqrtd ^ k : Zsqrtd 2) := by
  have h : (⟨a, b⟩ : Zsqrtd 2) = Zsqrtd.sqrtd * (b : Zsqrtd 2) + (a : Zsqrtd 2) := by
    rw [Zsqrtd.decompose]; ring
  rw [h, add_pow]
  refine sum_congr rfl fun k _ => ?_
  push_cast
  ring

lemma pow_re (a b : ℤ) (n : ℕ) : ((⟨a, b⟩ : Zsqrtd 2) ^ n).re =
    ∑ k ∈ range (n + 1),
      if k % 2 = 0 then (n.choose k : ℤ) * a ^ (n - k) * b ^ k * 2 ^ (k / 2) else 0 := by
  rw [pow_expand, re_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [Zsqrtd.re_smul, sqrtd_pow]
  split_ifs <;> simp

lemma pow_im (a b : ℤ) (n : ℕ) : ((⟨a, b⟩ : Zsqrtd 2) ^ n).im =
    ∑ k ∈ range (n + 1),
      if k % 2 = 1 then (n.choose k : ℤ) * a ^ (n - k) * b ^ k * 2 ^ (k / 2) else 0 := by
  rw [pow_expand, im_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [Zsqrtd.im_smul, sqrtd_pow]
  split_ifs <;> simp

/-- The case j = 0: the r-coefficient of (a + b r)^p is never 1. -/
lemma no_untwisted (p : ℕ) (hodd : Odd p) (h3 : 3 ≤ p) (a b : ℤ) :
    (∑ k ∈ range (p + 1),
      if k % 2 = 1 then (p.choose k : ℤ) * a ^ (p - k) * b ^ k * 2 ^ (k / 2) else 0) ≠ 1 := by
  intro hS
  have hdvd : b ∣ ∑ k ∈ range (p + 1),
      (if k % 2 = 1 then (p.choose k : ℤ) * a ^ (p - k) * b ^ k * 2 ^ (k / 2) else 0) := by
    apply Finset.dvd_sum
    intro k _
    split_ifs with h
    · exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_pow_self b (by omega)) _) _
    · exact dvd_zero b
  rw [hS] at hdvd
  have hb : b = 1 ∨ b = -1 := Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd)
  have hb2 : ∀ k, k % 2 = 1 → b * b ^ k = 1 := by
    intro k hk
    rcases hb with rfl | rfl
    · simp
    · rw [← pow_succ']; exact Even.neg_one_pow ⟨(k + 1) / 2, by omega⟩
  have hpos : ∀ k ∈ range (p + 1), 0 ≤ b * (if k % 2 = 1 then
      (p.choose k : ℤ) * a ^ (p - k) * b ^ k * 2 ^ (k / 2) else 0) := by
    intro k hk
    split_ifs with h
    · have hk' : k ≤ p := Nat.lt_succ_iff.mp (mem_range.mp hk)
      have heven : Even (p - k) := by
        obtain ⟨m, hm⟩ := hodd
        exact ⟨(p - k) / 2, by omega⟩
      have e : b * ((p.choose k : ℤ) * a ^ (p - k) * b ^ k * 2 ^ (k / 2)) =
          (p.choose k : ℤ) * a ^ (p - k) * 2 ^ (k / 2) * (b * b ^ k) := by ring
      rw [e, hb2 k h, mul_one]
      exact mul_nonneg (mul_nonneg (by positivity) (Even.pow_nonneg heven a)) (by positivity)
    · simp
  have hp1 : p % 2 = 1 := Nat.odd_iff.mp hodd
  have hlast : 2 ≤ b * (if p % 2 = 1 then
      (p.choose p : ℤ) * a ^ (p - p) * b ^ p * 2 ^ (p / 2) else 0) := by
    rw [if_pos hp1, Nat.choose_self, Nat.sub_self, pow_zero]
    have e : b * (((1 : ℕ) : ℤ) * 1 * b ^ p * 2 ^ (p / 2)) = 2 ^ (p / 2) * (b * b ^ p) := by
      push_cast; ring
    rw [e, hb2 p hp1, mul_one]
    calc (2 : ℤ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (p / 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hsum := Finset.single_le_sum hpos (Finset.self_mem_range_succ p)
  rw [← Finset.mul_sum, hS, mul_one] at hsum
  rcases hb with rfl | rfl <;> linarith

lemma nonsq : ∀ n : ℤ, (2 : ℤ) ≠ n * n := by
  intro n h
  have h1 : n ≤ 1 := by nlinarith
  have h2 : -1 ≤ n := by nlinarith
  interval_cases n <;> omega

lemma norm_ne_zero' (z : Zsqrtd 2) (hz : z ≠ 0) : z.norm ≠ 0 :=
  fun h => hz ((Zsqrtd.norm_eq_zero nonsq z).mp h)

/-- Rounding: some multiple of n lies within |n|/2 of z. -/
lemma exists_near (z n : ℤ) (hn : n ≠ 0) : ∃ q : ℤ, 4 * (z - n * q) ^ 2 ≤ n ^ 2 := by
  refine ⟨round ((z : ℚ) / n), ?_⟩
  have h := abs_sub_round ((z : ℚ) / n)
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  have e : (z : ℚ) - n * round ((z : ℚ) / n) = n * ((z : ℚ) / n - round ((z : ℚ) / n)) := by
    field_simp
  have h2 : |(z : ℚ) - n * round ((z : ℚ) / n)| ≤ |(n : ℚ)| / 2 := by
    rw [e, abs_mul]
    nlinarith [abs_nonneg (n : ℚ)]
  have h3 : ((z : ℚ) - n * round ((z : ℚ) / n)) ^ 2 ≤ (|(n : ℚ)| / 2) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  have h4 : 4 * ((z : ℚ) - n * round ((z : ℚ) / n)) ^ 2 ≤ (n : ℚ) ^ 2 := by
    have : (|(n : ℚ)| / 2) ^ 2 = (n : ℚ) ^ 2 / 4 := by rw [div_pow, sq_abs]; norm_num
    rw [this] at h3
    linarith
  exact_mod_cast h4

/-- Division with small remainder in Z[r]: |N(x - y q)| <= |N(y)|/2 < |N(y)|. -/
lemma div_small (x y : Zsqrtd 2) (hy : y ≠ 0) :
    ∃ q : Zsqrtd 2, (x - y * q).norm.natAbs < y.norm.natAbs := by
  have hn0 : y.norm ≠ 0 := norm_ne_zero' y hy
  obtain ⟨q1, hq1⟩ := exists_near (x * star y).re y.norm hn0
  obtain ⟨q2, hq2⟩ := exists_near (x * star y).im y.norm hn0
  refine ⟨⟨q1, q2⟩, ?_⟩
  have h1 : (x - y * ⟨q1, q2⟩) * star y =
      x * star y - ((y.norm : ℤ) : Zsqrtd 2) * ⟨q1, q2⟩ := by
    rw [Zsqrtd.norm_eq_mul_conj]; ring
  have h2 := congrArg Zsqrtd.norm h1
  rw [Zsqrtd.norm_mul, Zsqrtd.norm_conj] at h2
  have key : (x - y * ⟨q1, q2⟩).norm * y.norm =
      ((x * star y).re - y.norm * q1) ^ 2 - 2 * ((x * star y).im - y.norm * q2) ^ 2 := by
    rw [h2, Zsqrtd.norm_def]
    simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_smul, Zsqrtd.im_smul]
    ring
  set M := (x - y * ⟨q1, q2⟩).norm
  set n := y.norm
  have hlo : -2 * n ^ 2 ≤ 4 * (M * n) := by
    rw [key]; nlinarith [sq_nonneg ((x * star y).re - n * q1)]
  have hhi : 4 * (M * n) ≤ n ^ 2 := by
    rw [key]; nlinarith [sq_nonneg ((x * star y).im - n * q2)]
  rcases lt_or_gt_of_ne hn0 with hneg | hpos
  · have a1 : n ≤ 4 * M := by nlinarith
    have a2 : 4 * M ≤ -2 * n := by nlinarith
    omega
  · have a1 : 4 * M ≤ n := by nlinarith
    have a2 : -2 * n ≤ 4 * M := by nlinarith
    omega

/-- Z[r] is a principal ideal ring (no instance is declared; it is used locally). -/
lemma isPID : IsPrincipalIdealRing (Zsqrtd 2) := by
  classical
  refine ⟨fun I => ?_⟩
  by_cases hI : I = ⊥
  · rw [hI]; exact bot_isPrincipal
  · have hex : ∃ N : ℕ, ∃ g ∈ I, g ≠ 0 ∧ g.norm.natAbs = N := by
      obtain ⟨g, hg, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
      exact ⟨_, g, hg, hg0, rfl⟩
    obtain ⟨g, hgI, hg0, hgN⟩ := Nat.find_spec hex
    refine ⟨⟨g, ?_⟩⟩
    ext x
    rw [Ideal.submodule_span_eq, Ideal.mem_span_singleton']
    constructor
    · intro hx
      obtain ⟨q, hq⟩ := div_small x g hg0
      have hr : x - g * q ∈ I := I.sub_mem hx (I.mul_mem_right q hgI)
      by_cases h0 : x - g * q = 0
      · exact ⟨q, by rw [mul_comm]; exact (sub_eq_zero.mp h0).symm⟩
      · have := Nat.find_min' hex ⟨x - g * q, hr, h0, rfl⟩
        omega
    · rintro ⟨a, rfl⟩
      exact I.mul_mem_left a hgI

lemma isDomain : IsDomain (Zsqrtd 2) := by
  have : NoZeroDivisors (Zsqrtd 2) := ⟨fun {x y} h => by
    have := congrArg Zsqrtd.norm h
    rw [Zsqrtd.norm_mul, Zsqrtd.norm_zero] at this
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl ((Zsqrtd.norm_eq_zero nonsq x).mp h)
    · exact Or.inr ((Zsqrtd.norm_eq_zero nonsq y).mp h)⟩
  exact NoZeroDivisors.to_isDomain _

/-- Multiplying a unit a + b r (a b > 0) by r - 1 shrinks its r-coefficient. -/
lemma unit_ineq (a b : ℤ) (hb : b ≠ 0) (hab : 0 < a * b)
    (hn : a * a - 2 * b * b = 1 ∨ a * a - 2 * b * b = -1) : (a - b).natAbs < b.natAbs := by
  rw [Int.natAbs_lt_iff_sq_lt]
  rcases lt_or_gt_of_ne hb with hb' | hb'
  · have ha : a < 0 := by
      by_contra h
      nlinarith [not_lt.mp h]
    have h1 : 2 * b < a := by rcases hn with hn | hn <;> nlinarith
    have h2 : a ≤ b := by rcases hn with hn | hn <;> nlinarith
    nlinarith
  · have ha : 0 < a := by
      by_contra h
      nlinarith [not_lt.mp h]
    have h1 : a < 2 * b := by rcases hn with hn | hn <;> nlinarith
    have h2 : b ≤ a := by rcases hn with hn | hn <;> nlinarith
    nlinarith

/-- Units of norm 1 or -1 are plus or minus (1 + r)^n or (r - 1)^n (descent on |b|). -/
lemma unit_desc (N : ℕ) : ∀ e : Zsqrtd 2, e.im.natAbs = N → (e.norm = 1 ∨ e.norm = -1) →
    ∃ n : ℕ, ∃ s : Zsqrtd 2, (s = 1 ∨ s = -1) ∧
      (e = s * (⟨1, 1⟩ : Zsqrtd 2) ^ n ∨ e = s * (⟨-1, 1⟩ : Zsqrtd 2) ^ n) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro e hN he
  have huw : (⟨1, 1⟩ : Zsqrtd 2) * ⟨-1, 1⟩ = 1 := by
    ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul]
  simp only [Zsqrtd.norm_def] at he
  by_cases hb : e.im = 0
  · have ha : e.re = 1 ∨ e.re = -1 := by
      rw [hb] at he
      rcases he with he | he
      · have h0 : (e.re - 1) * (e.re + 1) = 0 := by linarith
        rcases mul_eq_zero.mp h0 with h | h
        · left; linarith
        · right; linarith
      · nlinarith [mul_self_nonneg e.re]
    refine ⟨0, e, ?_, Or.inl (by simp)⟩
    rcases ha with ha | ha
    · left; ext <;> simp [ha, hb]
    · right; ext <;> simp [ha, hb]
  · rcases lt_trichotomy (e.re * e.im) 0 with hab | hab | hab
    · -- opposite signs: multiply by 1 + r
      have hlt : (e * (⟨1, 1⟩ : Zsqrtd 2)).im.natAbs < N := by
        have h1 : (e * (⟨1, 1⟩ : Zsqrtd 2)).im = e.re + e.im := by
          simp [Zsqrtd.im_mul]
        rw [h1, ← hN]
        have := unit_ineq (-e.re) e.im hb (by linarith)
          (by rcases he with h | h
              · left; linarith
              · right; linarith)
        rwa [show -e.re - e.im = -(e.re + e.im) by ring, Int.natAbs_neg] at this
      have hnorm : (e * (⟨1, 1⟩ : Zsqrtd 2)).norm = 1 ∨
          (e * (⟨1, 1⟩ : Zsqrtd 2)).norm = -1 := by
        have h1 : (e * (⟨1, 1⟩ : Zsqrtd 2)).norm = -(e.re * e.re - 2 * e.im * e.im) := by
          rw [Zsqrtd.norm_mul, Zsqrtd.norm_def, Zsqrtd.norm_def]; simp
        rcases he with h | h
        · right; linarith
        · left; linarith
      obtain ⟨n, s, hs, hrep⟩ := ih _ hlt _ rfl hnorm
      have hee : e = e * (⟨1, 1⟩ : Zsqrtd 2) * ⟨-1, 1⟩ := by rw [mul_assoc, huw, mul_one]
      rcases hrep with h | h
      · cases n with
        | zero => exact ⟨1, s, hs, Or.inr (by rw [hee, h]; ring)⟩
        | succ m => exact ⟨m, s, hs, Or.inl (by
            rw [hee, h]; linear_combination (s * (⟨1, 1⟩ : Zsqrtd 2) ^ m) * huw)⟩
      · exact ⟨n + 1, s, hs, Or.inr (by rw [hee, h]; ring)⟩
    · exfalso
      have hre : e.re = 0 := by
        rcases mul_eq_zero.mp hab with h | h
        · exact h
        · exact absurd h hb
      rw [hre] at he
      have : 2 * (e.im * e.im) = 1 ∨ 2 * (e.im * e.im) = -1 := by
        rcases he with h | h
        · right; linarith
        · left; linarith
      generalize e.im * e.im = t at this
      omega
    · -- same signs: multiply by r - 1
      have hlt : (e * (⟨-1, 1⟩ : Zsqrtd 2)).im.natAbs < N := by
        have h1 : (e * (⟨-1, 1⟩ : Zsqrtd 2)).im = e.re - e.im := by
          simp [Zsqrtd.im_mul]; ring
        rw [h1, ← hN]
        exact unit_ineq e.re e.im hb hab he
      have hnorm : (e * (⟨-1, 1⟩ : Zsqrtd 2)).norm = 1 ∨
          (e * (⟨-1, 1⟩ : Zsqrtd 2)).norm = -1 := by
        have h1 : (e * (⟨-1, 1⟩ : Zsqrtd 2)).norm = -(e.re * e.re - 2 * e.im * e.im) := by
          rw [Zsqrtd.norm_mul, Zsqrtd.norm_def, Zsqrtd.norm_def]; simp
        rcases he with h | h
        · right; linarith
        · left; linarith
      obtain ⟨n, s, hs, hrep⟩ := ih _ hlt _ rfl hnorm
      have hee : e = e * (⟨-1, 1⟩ : Zsqrtd 2) * ⟨1, 1⟩ := by
        rw [mul_assoc, mul_comm (⟨-1, 1⟩ : Zsqrtd 2), huw, mul_one]
      rcases hrep with h | h
      · exact ⟨n + 1, s, hs, Or.inl (by rw [hee, h]; ring)⟩
      · cases n with
        | zero => exact ⟨1, s, hs, Or.inl (by rw [hee, h]; ring)⟩
        | succ m => exact ⟨m, s, hs, Or.inr (by
            rw [hee, h]; linear_combination (s * (⟨-1, 1⟩ : Zsqrtd 2) ^ m) * huw)⟩

lemma units_form (e : Zsqrtd 2) (he : IsUnit e) : ∃ n : ℕ, ∃ s : Zsqrtd 2, (s = 1 ∨ s = -1) ∧
    (e = s * (⟨1, 1⟩ : Zsqrtd 2) ^ n ∨ e = s * (⟨-1, 1⟩ : Zsqrtd 2) ^ n) := by
  have h := Zsqrtd.norm_eq_one_iff.mpr he
  exact unit_desc _ e rfl (by omega)

/-- p-th powers absorb the unit up to (1 + r)^j with j < p (p odd, so the sign is a p-th power). -/
lemma absorb (p : ℕ) (hp : 0 < p) (hodd : Odd p) (X d s : Zsqrtd 2) (hs : s = 1 ∨ s = -1)
    (n : ℕ) (hX : X = d ^ p * (s * (⟨1, 1⟩ : Zsqrtd 2) ^ n) ∨
      X = d ^ p * (s * (⟨-1, 1⟩ : Zsqrtd 2) ^ n)) :
    ∃ j < p, ∃ α : Zsqrtd 2, X = (⟨1, 1⟩ : Zsqrtd 2) ^ j * α ^ p := by
  have hsp : s ^ p = s := by
    rcases hs with rfl | rfl
    · simp
    · exact hodd.neg_one_pow
  have huw : (⟨1, 1⟩ : Zsqrtd 2) * ⟨-1, 1⟩ = 1 := by
    ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul]
  have hn := Nat.div_add_mod n p
  have hlt := Nat.mod_lt n hp
  rcases hX with hX | hX
  · refine ⟨n % p, hlt, s * d * (⟨1, 1⟩ : Zsqrtd 2) ^ (n / p), ?_⟩
    have e1 : (⟨1, 1⟩ : Zsqrtd 2) ^ n =
        (⟨1, 1⟩ : Zsqrtd 2) ^ (p * (n / p)) * (⟨1, 1⟩ : Zsqrtd 2) ^ (n % p) := by
      rw [← pow_add, hn]
    rw [hX, e1, mul_pow, mul_pow, hsp, ← pow_mul, mul_comm (n / p) p]
    ring
  · by_cases h0 : n % p = 0
    · refine ⟨0, hp, s * d * (⟨-1, 1⟩ : Zsqrtd 2) ^ (n / p), ?_⟩
      have e1 : (⟨-1, 1⟩ : Zsqrtd 2) ^ n = (⟨-1, 1⟩ : Zsqrtd 2) ^ (p * (n / p)) := by
        congr 1; omega
      rw [hX, e1, mul_pow, mul_pow, hsp, ← pow_mul, mul_comm (n / p) p]
      ring
    · refine ⟨p - n % p, by omega, s * d * (⟨-1, 1⟩ : Zsqrtd 2) ^ (n / p + 1), ?_⟩
      have e1 : (⟨-1, 1⟩ : Zsqrtd 2) ^ (p * (n / p + 1)) =
          (⟨-1, 1⟩ : Zsqrtd 2) ^ n * (⟨-1, 1⟩ : Zsqrtd 2) ^ (p - n % p) := by
        rw [← pow_add]; congr 1; rw [mul_add, mul_one]; omega
      have e2 : (⟨1, 1⟩ : Zsqrtd 2) ^ (p - n % p) * (⟨-1, 1⟩ : Zsqrtd 2) ^ (p - n % p) = 1 := by
        rw [← mul_pow, huw, one_pow]
      rw [hX, mul_pow, mul_pow, hsp, ← pow_mul, mul_comm (n / p + 1) p, e1]
      linear_combination (-(d ^ p * s * (⟨-1, 1⟩ : Zsqrtd 2) ^ n)) * e2

/-- x is odd: an even x gives x^2 - 2 = 2 mod 4, while an even y gives 4 | y^p. -/
lemma x_odd (p : ℕ) (hp : p.Prime) (x y : ℤ) (h : x ^ 2 - 2 = y ^ p) : Odd x := by
  by_contra hx
  rw [Int.not_odd_iff_even] at hx
  obtain ⟨t, rfl⟩ := hx
  have hev : Even (y ^ p) := by rw [← h]; exact ⟨2 * t ^ 2 - 1, by ring⟩
  obtain ⟨s, rfl⟩ := (Int.even_pow.mp hev).1
  have h4 : (4 : ℤ) ∣ (s + s) ^ p := by
    have e : (s + s) ^ p = 2 ^ p * s ^ p := by rw [← mul_pow]; ring
    rw [e]
    exact Dvd.dvd.mul_right (by
      have := pow_dvd_pow (2 : ℤ) hp.two_le
      norm_num at this
      exact this) _
  rw [← h] at h4
  have e : (t + t) ^ 2 - 2 = 4 * t ^ 2 - 2 := by ring
  rw [e] at h4
  obtain ⟨c, hc⟩ := h4
  omega

/-- The descent: x + r = (1 + r)^j (a + b r)^p with j < p. -/
lemma descent (p : ℕ) (hp : p.Prime) (hodd : Odd p) (x y : ℤ) (h : x ^ 2 - 2 = y ^ p) :
    ∃ j < p, ∃ a b : ℤ, (⟨1, 1⟩ : Zsqrtd 2) ^ j * (⟨a, b⟩ : Zsqrtd 2) ^ p = ⟨x, 1⟩ := by
  obtain ⟨m, hm⟩ := x_odd p hp x y h
  have hprod : (⟨x, 1⟩ : Zsqrtd 2) * ⟨x, -1⟩ = (y : Zsqrtd 2) ^ p := by
    rw [← Int.cast_pow, ← h]
    ext <;> simp only [Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast] <;> ring
  have hcop : IsCoprime (⟨x, 1⟩ : Zsqrtd 2) ⟨x, -1⟩ := by
    refine ⟨⟨-x, m ^ 2 + m + 1⟩, ⟨0, -(m ^ 2 + m)⟩, ?_⟩
    subst hm
    ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul] <;> ring
  have := isDomain
  have := isPID
  obtain ⟨d, ε, hε⟩ := exists_associated_pow_of_mul_eq_pow' hcop hprod
  obtain ⟨n, s, hs, he⟩ := units_form (ε : Zsqrtd 2) ε.isUnit
  obtain ⟨j, hj, α, hα⟩ := absorb p hp.pos hodd ⟨x, 1⟩ d s hs n (by
    rcases he with he | he
    · left; rw [← hε, he]
    · right; rw [← hε, he])
  exact ⟨j, hj, α.re, α.im, by rw [hα]⟩

/-- Conjugation: x + r = (1 + r)^j (a + b r)^p gives -x + r = (1 + r)^(p - j) (c + d r)^p. -/
lemma flip (p j : ℕ) (hodd : Odd p) (hj : j ≤ p) (x : ℤ) (α : Zsqrtd 2)
    (h : (⟨1, 1⟩ : Zsqrtd 2) ^ j * α ^ p = ⟨x, 1⟩) :
    ∃ β : Zsqrtd 2, (⟨1, 1⟩ : Zsqrtd 2) ^ (p - j) * β ^ p = ⟨-x, 1⟩ := by
  have hs := congrArg star h
  rw [star_mul', star_pow, star_pow, Zsqrtd.star_mk 1 1, Zsqrtd.star_mk x 1] at hs
  have huw : (⟨1, 1⟩ : Zsqrtd 2) * ⟨-1, 1⟩ = 1 := by
    ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul]
  have hc : (⟨1, -1⟩ : Zsqrtd 2) = -⟨-1, 1⟩ := by ext <;> simp
  have hneg : (⟨-x, 1⟩ : Zsqrtd 2) = -⟨x, -1⟩ := by ext <;> simp
  have hsp : ((-1 : Zsqrtd 2) ^ (j + 1)) ^ p = (-1) ^ (j + 1) := by
    rw [← pow_mul, mul_comm, pow_mul, hodd.neg_one_pow]
  have hw : (⟨-1, 1⟩ : Zsqrtd 2) ^ p =
      (⟨-1, 1⟩ : Zsqrtd 2) ^ j * (⟨-1, 1⟩ : Zsqrtd 2) ^ (p - j) := by
    rw [← pow_add, Nat.add_sub_cancel' hj]
  have huwp : (⟨1, 1⟩ : Zsqrtd 2) ^ (p - j) * (⟨-1, 1⟩ : Zsqrtd 2) ^ (p - j) = 1 := by
    rw [← mul_pow, huw, one_pow]
  refine ⟨(-1) ^ (j + 1) * ⟨-1, 1⟩ * star α, ?_⟩
  rw [hneg, ← hs, hc, mul_pow, mul_pow, hsp, hw, neg_pow (⟨-1, 1⟩ : Zsqrtd 2) j]
  linear_combination ((-1) ^ (j + 1) * (⟨-1, 1⟩ : Zsqrtd 2) ^ j * star α ^ p) * huwp

/-- The cases 2 j < p: j = 0 is impossible, j = 1 is H1, and 1 < j is H2. -/
lemma half_case (h1 : H1) (h2 : H2) (p : ℕ) (hp : p.Prime) (hodd : Odd p) (h3 : 3 ≤ p)
    (j : ℕ) (hj : 2 * j < p) (a b x : ℤ)
    (hX : (⟨1, 1⟩ : Zsqrtd 2) ^ j * (⟨a, b⟩ : Zsqrtd 2) ^ p = ⟨x, 1⟩) : x = 1 := by
  have hre : ((⟨1, 1⟩ : Zsqrtd 2) ^ j * (⟨a, b⟩ : Zsqrtd 2) ^ p).re = x := by rw [hX]
  have him : ((⟨1, 1⟩ : Zsqrtd 2) ^ j * (⟨a, b⟩ : Zsqrtd 2) ^ p).im = 1 := by rw [hX]
  rw [Zsqrtd.im_mul] at him
  rcases Nat.lt_or_ge j 2 with hj2 | hj2
  · interval_cases j
    · -- j = 0 is impossible
      simp only [pow_zero, Zsqrtd.re_one, Zsqrtd.im_one, one_mul, zero_mul, add_zero] at him
      rw [pow_im] at him
      exact absurd him (no_untwisted p hodd h3 a b)
    · -- j = 1: H1
      simp only [pow_one, one_mul] at him
      have hsum : ∑ k ∈ range (p + 1),
          (p.choose k : ℤ) * a ^ (p - k) * b ^ k * 2 ^ (k / 2) = 1 := by
        rw [← him, pow_re, pow_im, ← sum_add_distrib]
        refine sum_congr rfl fun k _ => ?_
        rcases Nat.mod_two_eq_zero_or_one k with hk | hk
        · simp [hk]
        · simp [hk]
      obtain ⟨rfl, rfl⟩ := h1 p hp hodd a b hsum
      rw [← hre]
      have : (⟨1, 0⟩ : Zsqrtd 2) = 1 := rfl
      rw [this, one_pow, pow_one, mul_one]
  · -- 1 < j < p/2: H2
    exfalso
    have key := him
    rw [pow_re, pow_im, pow_re, pow_im] at key
    simp only [one_pow, mul_one] at key
    exact h2 p hp hodd j hj2 hj a b key

theorem main : H1 → H2 → OMA.R_LebesgueNagell_lebesgue_nagell_R1.H1 := by
  intro h1 h2 p hp hodd x y hxy
  have h3 : 3 ≤ p := by
    have := hp.two_le
    obtain ⟨m, hm⟩ := hodd
    omega
  have hp1 : p % 2 = 1 := Nat.odd_iff.mp hodd
  obtain ⟨j, hj, a, b, hX⟩ := descent p hp hodd x y hxy
  have hx : x = 1 ∨ x = -1 := by
    by_cases hjp : 2 * j < p
    · exact Or.inl (half_case h1 h2 p hp hodd h3 j hjp a b x hX)
    · obtain ⟨β, hβ⟩ := flip p j hodd hj.le x _ hX
      have := half_case h1 h2 p hp hodd h3 (p - j) (by omega) β.re β.im (-x) (by rw [← hβ])
      right
      linarith
  have hy : y ^ p = -1 := by
    rcases hx with rfl | rfl <;> linarith
  refine ⟨hx, ?_⟩
  have hdvd : y ∣ 1 := by
    have : y ∣ y ^ p := dvd_pow_self y (by omega)
    rw [hy] at this
    exact (dvd_neg).mp this
  rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd) with h | h
  · subst h; simp at hy
  · exact h

end OMA.R_LebesgueNagell_lebesgue_nagell_R1_H1_R1
