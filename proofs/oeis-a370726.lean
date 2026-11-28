import OMAStatements.S_oeis_a370726
import Mathlib

-- Problem: OEIS A370726, a(n) = denominator of 1/(2-3/(3-4/(4-5/(...(n-1)-n/(n+3))))).
-- Conjecture: the sequence contains only 1's and primes.
-- Statement: statements/oeis-a370726.lean (declaration OMA.S_oeis_a370726.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. Let r(0) = 0, r(1) = 1, r(j+2) = (j+3)(r(j+1) - r(j)). By induction on the number of
-- levels, for y >= j+1,
--   2 - 3/(3 - ... ((j+2) - (j+3)/y)) = ((j+2) y - (j+1)(j+3)) / (r(j+1) y - (j+3) r(j)).
-- With n = j+3 and y = n+3 the continued fraction is A / (4n-3), where
-- A = (j+6) r(j+1) - (j+3) r(j). Let L(j) = 0! + ... + (j-1)!. Then 2 r(j) = (j+1) L(j), and
-- 2 A = (4n-3) L(n-2) + n (n-2)!. Thus a(n) = D = (4n-3)/gcd(4n-3, A), and D divides 2 q if
-- 4n-3 divides q n (n-2)!. D is odd, so D divides q.
-- Lemma key: there is q, equal to 1 or a prime, such that 4n-3 divides q n (n-2)!.
-- * n = 3, 4, 5, 7, 13: q = 3, 13, 17, 5, 7.
-- * 4n-3 has a prime factor p >= n-1: q = p. The cofactor is odd and less than 5, so it is
--   1 or 3, and 3 divides (n-2)!.
-- * All prime factors of 4n-3 are at most n-2: q = 1. For each prime power p^e that divides
--   4n-3, either e = 1, or e p <= n-2 (lemma ep_le: p^e >= 4 e p + 5, or a small case), and
--   p^e divides (e p)!. Thus 4n-3 divides (n-2)!.

namespace OMA.A370726

open OMA.S_oeis_a370726 Nat

/-- The numerators: r(0) = 0, r(1) = 1, r(j+2) = (j+3) (r(j+1) - r(j)). -/
def r : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | j + 2 => ((j : ℤ) + 3) * (r (j + 1) - r j)

/-- The left factorial 0! + 1! + ... + (j-1)!. -/
def lf (j : ℕ) : ℕ := ∑ i ∈ Finset.range j, i !

lemma nest_formula (j : ℕ) : ∀ y : ℚ, (j : ℚ) + 1 ≤ y →
    nest (j + 1) y = (((j : ℚ) + 2) * y - (j + 1) * (j + 3)) / ((r (j + 1) : ℚ) * y - (j + 3) * r j) := by
  induction j with
  | zero =>
    intro y hy
    have hy0 : y ≠ 0 := by
      intro h
      rw [h] at hy
      norm_num at hy
    have e0 : nest (0 + 1) y = 2 - 3 / y := by simp [nest]
    rw [e0]
    simp only [r]
    norm_num
    field_simp
  | succ j ih =>
    intro y hy
    have hjq : (0 : ℚ) ≤ j := Nat.cast_nonneg j
    have hypos : 0 < y := by push_cast at hy; linarith
    have hy0 : y ≠ 0 := hypos.ne'
    have hstep : nest (j + 1 + 1) y = nest (j + 1) (((j : ℚ) + 3) - ((j : ℚ) + 4) / y) := by
      show nest (j + 1) (((j + 1 : ℕ) : ℚ) + 2 - (((j + 1 : ℕ) : ℚ) + 3) / y) = _
      congr 1
      push_cast
      ring
    have hy' : (j : ℚ) + 1 ≤ ((j : ℚ) + 3) - ((j : ℚ) + 4) / y := by
      have h1 : ((j : ℚ) + 4) / y ≤ 2 := by
        rw [div_le_iff₀ hypos]
        push_cast at hy
        nlinarith
      linarith
    rw [hstep, ih _ hy']
    have e1 : ((j : ℚ) + 2) * (((j : ℚ) + 3) - ((j : ℚ) + 4) / y) - (j + 1) * (j + 3)
        = ((((j + 1 : ℕ) : ℚ) + 2) * y - ((j + 1 : ℕ) + 1) * ((j + 1 : ℕ) + 3)) / y := by
      field_simp
      push_cast
      ring
    have e2 : (r (j + 1) : ℚ) * (((j : ℚ) + 3) - ((j : ℚ) + 4) / y) - (j + 3) * r j
        = ((r (j + 1 + 1) : ℚ) * y - ((j + 1 : ℕ) + 3) * r (j + 1)) / y := by
      have hr : r (j + 1 + 1) = ((j : ℤ) + 3) * (r (j + 1) - r j) := rfl
      rw [hr]
      field_simp
      push_cast
      ring
    rw [e1, e2, div_div_div_cancel_right₀ hy0]

lemma lf_succ (j : ℕ) : lf (j + 1) = lf j + j ! := by
  unfold lf
  rw [Finset.sum_range_succ]

lemma two_r (j : ℕ) : 2 * r j = ((j : ℤ) + 1) * lf j ∧ 2 * r (j + 1) = ((j : ℤ) + 2) * lf (j + 1) := by
  induction j with
  | zero => simp [r, lf]
  | succ j ih =>
    refine ⟨by have := ih.2; push_cast at this ⊢; linarith, ?_⟩
    have hr : r (j + 1 + 1) = ((j : ℤ) + 3) * (r (j + 1) - r j) := rfl
    have h1 := ih.1
    have h2 := ih.2
    rw [hr, lf_succ (j + 1), lf_succ j] at *
    rw [Nat.factorial_succ]
    push_cast at *
    linear_combination ((j : ℤ) + 3) * h2 - ((j : ℤ) + 3) * h1

/-- `p ^ e` divides `(e p)!`. -/
lemma pow_dvd_fact (p e : ℕ) (hp : 0 < p) : p ^ e ∣ (e * p)! := by
  induction e with
  | zero => simp
  | succ e ih =>
    have h1 : (e * p)! * p ! ∣ ((e + 1) * p)! := by
      have := Nat.factorial_mul_factorial_dvd_factorial_add (e * p) p
      rwa [show e * p + p = (e + 1) * p by ring] at this
    rw [pow_succ]
    exact dvd_trans (Nat.mul_dvd_mul ih (Nat.dvd_factorial hp le_rfl)) h1

lemma dvd_of_prime_pows (N X : ℕ) (hN : N ≠ 0) (hX : X ≠ 0)
    (h : ∀ p e, p.Prime → p ^ e ∣ N → p ^ e ∣ X) : N ∣ X :=
  (Nat.factorization_prime_le_iff_dvd hN hX).mp
    (fun p hp => (hp.pow_dvd_iff_le_factorization hX).mp (h p _ hp (Nat.ordProj_dvd N p)))

lemma pow_ineq (p : ℕ) (hp : 3 ≤ p) : ∀ e, 4 ≤ e → 4 * e * p + 5 ≤ p ^ e := by
  intro e he
  induction e, he using Nat.le_induction with
  | base =>
    have h2 : 9 ≤ p ^ 2 := by nlinarith
    have h4 : p ^ 4 = p ^ 2 * p ^ 2 := by ring
    nlinarith
  | succ e he ih =>
    rw [pow_succ]
    have h1 : (4 * e * p + 5) * 3 ≤ p ^ e * p := Nat.mul_le_mul ih hp
    nlinarith

/-- The key arithmetic fact. -/
lemma ep_le (p e j : ℕ) (hp : p.Prime) (he : 2 ≤ e) (hd : p ^ e ∣ 4 * j + 9) (hj3 : 3 ≤ j)
    (hj4 : j ≠ 4) (hj10 : j ≠ 10) : e * p ≤ j + 1 := by
  have hle : p ^ e ≤ 4 * j + 9 := Nat.le_of_dvd (by omega) hd
  have hpodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h2 | ho
    · exfalso
      subst h2
      have : 2 ∣ 4 * j + 9 := dvd_trans (dvd_pow_self 2 (by omega)) hd
      omega
    · exact ho
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  rcases Nat.lt_or_ge e 4 with he4 | he4
  · have hcases : e = 2 ∨ e = 3 := by omega
    rcases hcases with rfl | rfl
    · rcases Nat.lt_or_ge p 9 with hp9 | hp9
      · have hc : p = 3 ∨ p = 5 ∨ p = 7 := by omega
        rcases hc with rfl | rfl | rfl
        · obtain ⟨c, hc⟩ := hd
          omega
        · obtain ⟨c, hc⟩ := hd
          omega
        · obtain ⟨c, hc⟩ := hd
          omega
      · have : 8 * p + 5 ≤ p ^ 2 := by nlinarith
        omega
    · rcases Nat.lt_or_ge p 5 with hp5 | hp5
      · have hc : p = 3 := by omega
        subst hc
        obtain ⟨c, hc⟩ := hd
        omega
      · have h2 : 25 ≤ p ^ 2 := by nlinarith
        have h3 : p ^ 3 = p ^ 2 * p := by ring
        have : 12 * p + 5 ≤ p ^ 3 := by nlinarith
        omega
  · have := pow_ineq p hp3 e he4
    have h4 : 4 * (e * p) + 5 ≤ 4 * j + 9 := by
      calc 4 * (e * p) + 5 = 4 * e * p + 5 := by ring
        _ ≤ p ^ e := this
        _ ≤ 4 * j + 9 := hle
    omega

/-- There is `q`, equal to 1 or a prime, such that `4n - 3` divides `q n (n-2)!` (`n = j + 3`). -/
lemma key (j : ℕ) : ∃ q, (q = 1 ∨ q.Prime) ∧ 4 * j + 9 ∣ q * ((j + 3) * (j + 1)!) := by
  rcases Nat.lt_or_ge j 3 with hj | hj3
  · interval_cases j
    · exact ⟨3, Or.inr (by norm_num), by norm_num [Nat.factorial]⟩
    · exact ⟨13, Or.inr (by norm_num), by norm_num [Nat.factorial]⟩
    · exact ⟨17, Or.inr (by norm_num), by norm_num [Nat.factorial]⟩
  by_cases hj4 : j = 4
  · subst hj4
    exact ⟨5, Or.inr (by norm_num), by norm_num [Nat.factorial]⟩
  by_cases hj10 : j = 10
  · subst hj10
    exact ⟨7, Or.inr (by norm_num), by norm_num [Nat.factorial]⟩
  by_cases hbig : ∃ p, p.Prime ∧ p ∣ 4 * j + 9 ∧ j + 2 ≤ p
  · obtain ⟨p, hp, ⟨c, hc⟩, hpj⟩ := hbig
    refine ⟨p, Or.inr hp, ?_⟩
    rw [hc]
    apply Nat.mul_dvd_mul_left
    apply Dvd.dvd.mul_left
    have hc5 : c < 5 := by
      by_contra hcon
      have : (j + 2) * 5 ≤ p * c := Nat.mul_le_mul hpj (by omega)
      omega
    have hcodd : c % 2 = 1 := by
      by_contra hcon
      have : c % 2 = 0 := by omega
      obtain ⟨d, hd⟩ := Nat.dvd_of_mod_eq_zero this
      rw [hd] at hc
      have : 4 * j + 9 = 2 * (p * d) := by rw [hc]; ring
      omega
    have hc13 : c = 1 ∨ c = 3 := by omega
    rcases hc13 with rfl | rfl
    · exact one_dvd _
    · exact Nat.dvd_factorial (by norm_num) (by omega)
  · push Not at hbig
    refine ⟨1, Or.inl rfl, ?_⟩
    rw [one_mul]
    apply Dvd.dvd.mul_left
    apply dvd_of_prime_pows _ _ (by omega) (Nat.factorial_ne_zero _)
    intro p e hp hd
    rcases Nat.lt_or_ge e 2 with he | he
    · have he01 : e = 0 ∨ e = 1 := by omega
      rcases he01 with rfl | rfl
      · simp
      · rw [pow_one] at hd ⊢
        have := hbig p hp hd
        exact Nat.dvd_factorial hp.pos (by omega)
    · have h1 := ep_le p e j hp he hd hj3 hj4 hj10
      exact dvd_trans (pow_dvd_fact p e hp.pos) (Nat.factorial_dvd_factorial h1)

theorem result (n : ℕ) (hn : 3 ≤ n) : a n = 1 ∨ (a n).Prime := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 3 := ⟨n - 3, by omega⟩
  have hjq : (0 : ℚ) ≤ j := Nat.cast_nonneg j
  -- the value of the continued fraction
  have hval : 1 / nest (j + 1) (((j + 3 : ℕ) : ℚ) + 3)
      = ((((j : ℤ) + 6) * r (j + 1) - ((j : ℤ) + 3) * r j : ℤ) : ℚ) / ((4 * j + 9 : ℕ) : ℚ) := by
    rw [nest_formula j _ (by push_cast; linarith), one_div_div]
    congr 1
    · push_cast
      ring
    · push_cast
      ring
  -- the numerator in terms of the left factorial
  obtain ⟨h1, h2⟩ := two_r j
  have hnum : 2 * (((j : ℤ) + 6) * r (j + 1) - ((j : ℤ) + 3) * r j)
      = ((4 * j + 9 : ℕ) : ℤ) * (lf (j + 1) : ℕ) + (((j + 3) * (j + 1)! : ℕ) : ℤ) := by
    have e1 : (lf (j + 1) : ℤ) = lf j + j ! := by rw [lf_succ]; push_cast; ring
    rw [Nat.factorial_succ]
    push_cast
    rw [e1] at h2 ⊢
    linear_combination ((j : ℤ) + 6) * h2 - ((j : ℤ) + 3) * h1
  have hnn : 0 ≤ ((j : ℤ) + 6) * r (j + 1) - ((j : ℤ) + 3) * r j := by
    have : (0 : ℤ) ≤ ((4 * j + 9 : ℕ) : ℤ) * (lf (j + 1) : ℕ) + (((j + 3) * (j + 1)! : ℕ) : ℤ) := by
      positivity
    omega
  obtain ⟨A, hA⟩ := Int.eq_ofNat_of_zero_le hnn
  rw [hA] at hval hnum
  have hnumN : 2 * A = (4 * j + 9) * lf (j + 1) + (j + 3) * (j + 1)! := by exact_mod_cast hnum
  -- reduce the fraction
  have hNpos : 0 < 4 * j + 9 := by omega
  obtain ⟨g, A', D, hg, hcop, hA', hD⟩ := Nat.exists_coprime' (Nat.gcd_pos_of_pos_right A hNpos)
  have hDpos : 0 < D := by
    rcases Nat.eq_zero_or_pos D with h | h
    · rw [h, zero_mul] at hD
      omega
    · exact h
  have hden : a (j + 3) = D := by
    unfold a
    rw [show j + 3 - 2 = j + 1 by omega, hval, hA', hD]
    have hgq : (g : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
    have e : (((A' * g : ℕ) : ℤ) : ℚ) / ((D * g : ℕ) : ℚ) = ((A' : ℤ) : ℚ) / ((D : ℤ) : ℚ) := by
      push_cast
      rw [mul_div_mul_right _ _ hgq]
    rw [e]
    have := Rat.den_div_eq_of_coprime (a := (A' : ℤ)) (b := (D : ℤ)) (by exact_mod_cast hDpos)
      (by simpa using hcop)
    exact_mod_cast this
  rw [hden]
  -- D divides q
  obtain ⟨q, hq, hqdvd⟩ := key j
  have h2q : D * g ∣ 2 * q * A' * g := by
    rw [← hD]
    have : 2 * q * A' * g = q * (2 * A) := by rw [hA']; ring
    rw [this, hnumN, mul_add]
    exact dvd_add ⟨q * lf (j + 1), by ring⟩ hqdvd
  have h3 : D ∣ 2 * q * A' := Nat.dvd_of_mul_dvd_mul_right hg h2q
  have h4 : D ∣ 2 * q := (Nat.Coprime.dvd_of_dvd_mul_right hcop.symm h3)
  have hDodd : Nat.Coprime D 2 := by
    rw [Nat.coprime_two_right]
    have : ¬ 2 ∣ D := by
      intro h
      have : 2 ∣ 4 * j + 9 := by rw [hD]; exact Dvd.dvd.mul_right h g
      omega
    exact Nat.odd_iff.mpr (by omega)
  have h5 : D ∣ q := hDodd.dvd_of_dvd_mul_left h4
  rcases hq with rfl | hq
  · exact Or.inl (Nat.dvd_one.mp h5)
  · rcases (Nat.dvd_prime hq).mp h5 with h | h
    · exact Or.inl h
    · exact Or.inr (h ▸ hq)

end OMA.A370726

theorem OMA.solution : type_of% @OMA.S_oeis_a370726.main :=
  fun n hn => OMA.A370726.result n hn
