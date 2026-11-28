import OMAStatements.S_oeis_a362086
import Mathlib

-- Problem: OEIS A362086, a(n) = denominator of 1/(2-3/(3-4/(4-5/(...(n-1)-n/(-3))))).
-- Conjecture: except for 9, every term is 1 or a prime.
-- Statement: statements/oeis-a362086.lean (declaration OMA.S_oeis_a362086.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. Let r(0) = 0, r(1) = 1, r(j+2) = (j+3)(r(j+1) - r(j)). By induction on the number of
-- levels, for y >= j+1 and also for y < 0,
--   2 - 3/(3 - ... ((j+2) - (j+3)/y)) = ((j+2) y - (j+1)(j+3)) / (r(j+1) y - (j+3) r(j)).
-- With n = j+3 and y = -3 the continued fraction is A / N, where N = n^2 + n - 3 and
-- A = 3 r(j+1) + (j+3) r(j). Let L(j) = 0! + ... + (j-1)!. Then 2 r(j) = (j+1) L(j), and
-- 2 A + n (n-2)! = N L(n-2). Thus a(n) = D = N/gcd(N, A), and D divides 2 q if N divides
-- q n (n-2)!. N is odd, so D divides q.
-- Lemma key: there is q, equal to 1, a prime or 9, such that N divides q n (n-2)!.
-- * n = 3, ..., 22: an explicit q (q = 9 for n = 5, N = 27).
-- * n >= 23 and N has a prime factor p >= n+2: q = p. The cofactor c is less than n+2 because
--   N < (n+2)^2, and c is not n-1, n or n+1 (each of them is coprime to N or too large), so
--   c <= n-2 and c divides (n-2)!.
-- * n >= 23 and all prime factors of N are less than n+2: then they are at most n-2. For a
--   prime power p^e that divides N with e >= 3, e p <= n-2 (lemma ep_le, from N < (n+2)^2),
--   so p^e divides (e p)! and (n-2)!. For e = 2, either 2 p <= n-2, or 2 p >= n-1; at most
--   one prime q is of the second type (lemma uniq), and then q^2 divides q (n-2)!. Take this
--   q, or q = 1 if there is no such prime.

namespace OMA.A362086

open OMA.S_oeis_a362086 Nat

/-- The numerators: r(0) = 0, r(1) = 1, r(j+2) = (j+3) (r(j+1) - r(j)). -/
def r : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | j + 2 => ((j : ℤ) + 3) * (r (j + 1) - r j)

/-- The left factorial 0! + 1! + ... + (j-1)!. -/
def lf (j : ℕ) : ℕ := ∑ i ∈ Finset.range j, i !

lemma nest_zero (y : ℚ) (hy0 : y ≠ 0) :
    nest (0 + 1) y = ((((0 : ℕ) : ℚ) + 2) * y - (((0 : ℕ) : ℚ) + 1) * (((0 : ℕ) : ℚ) + 3)) / ((r (0 + 1) : ℚ) * y - (((0 : ℕ) : ℚ) + 3) * r 0) := by
  have e0 : nest (0 + 1) y = 2 - 3 / y := by simp [nest]
  rw [e0]
  simp only [r]
  norm_num
  field_simp

lemma nest_step (j : ℕ) (y : ℚ) :
    nest (j + 1 + 1) y = nest (j + 1) (((j : ℚ) + 3) - ((j : ℚ) + 4) / y) := by
  show nest (j + 1) (((j + 1 : ℕ) : ℚ) + 2 - (((j + 1 : ℕ) : ℚ) + 3) / y) = _
  congr 1
  push_cast
  ring

lemma step_alg (j : ℕ) (y : ℚ) (hy0 : y ≠ 0) :
    (((j : ℚ) + 2) * (((j : ℚ) + 3) - ((j : ℚ) + 4) / y) - (j + 1) * (j + 3))
        / ((r (j + 1) : ℚ) * (((j : ℚ) + 3) - ((j : ℚ) + 4) / y) - (j + 3) * r j)
      = ((((j + 1 : ℕ) : ℚ) + 2) * y - ((j + 1 : ℕ) + 1) * ((j + 1 : ℕ) + 3))
        / ((r (j + 1 + 1) : ℚ) * y - ((j + 1 : ℕ) + 3) * r (j + 1)) := by
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

lemma nest_formula (j : ℕ) : ∀ y : ℚ, (j : ℚ) + 1 ≤ y →
    nest (j + 1) y = (((j : ℚ) + 2) * y - (j + 1) * (j + 3)) / ((r (j + 1) : ℚ) * y - (j + 3) * r j) := by
  induction j with
  | zero =>
    intro y hy
    have hy0 : y ≠ 0 := by
      intro h
      rw [h] at hy
      norm_num at hy
    exact nest_zero y hy0
  | succ j ih =>
    intro y hy
    have hjq : (0 : ℚ) ≤ j := Nat.cast_nonneg j
    have hypos : 0 < y := by push_cast at hy; linarith
    have hy' : (j : ℚ) + 1 ≤ ((j : ℚ) + 3) - ((j : ℚ) + 4) / y := by
      have h1 : ((j : ℚ) + 4) / y ≤ 2 := by
        rw [div_le_iff₀ hypos]
        push_cast at hy
        nlinarith
      linarith
    rw [nest_step, ih _ hy', step_alg j y hypos.ne']

/-- The formula for a negative innermost value. -/
lemma nest_neg (j : ℕ) (y : ℚ) (hy : y < 0) :
    nest (j + 1) y = (((j : ℚ) + 2) * y - (j + 1) * (j + 3)) / ((r (j + 1) : ℚ) * y - (j + 3) * r j) := by
  cases j with
  | zero => exact nest_zero y hy.ne
  | succ j =>
    have hjq : (0 : ℚ) ≤ j := Nat.cast_nonneg j
    have hy' : (j : ℚ) + 1 ≤ ((j : ℚ) + 3) - ((j : ℚ) + 4) / y := by
      have h1 : ((j : ℚ) + 4) / y ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by linarith) hy.le
      linarith
    rw [nest_step, nest_formula j _ hy', step_alg j y hy.ne]

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

lemma pow_big (p : ℕ) (hp : 3 ≤ p) : ∀ e, 6 ≤ e → (e * p + 3) ^ 2 ≤ p ^ e := by
  intro e he
  induction e, he using Nat.le_induction with
  | base =>
    have h2 : 9 ≤ p * p := Nat.mul_le_mul hp hp
    have h3 : 3 * p ≤ p * p := Nat.mul_le_mul_right p hp
    have h6 : p ^ 6 = (p * p) * (p * p) * (p * p) := by ring
    have h7 : 81 * (p * p) ≤ (p * p) * (p * p) * (p * p) := by
      have := Nat.mul_le_mul (Nat.mul_le_mul h2 h2) (le_refl (p * p))
      linarith
    have h8 : (6 * p + 3) ^ 2 = 36 * (p * p) + 36 * p + 9 := by ring
    rw [h6, h8]
    linarith
  | succ e he ih =>
    have h6 : 6 * p ≤ e * p + 3 := by
      have := Nat.mul_le_mul_right p he
      omega
    have ha : (6 * p) * (e * p + 3) ≤ (e * p + 3) * (e * p + 3) := Nat.mul_le_mul_right _ h6
    have hb : (6 * p) * (6 * p) ≤ (e * p + 3) * (e * p + 3) := Nat.mul_le_mul h6 h6
    have hc : ((e + 1) * p + 3) ^ 2 ≤ 3 * (e * p + 3) ^ 2 := by nlinarith
    have hd : 3 * (e * p + 3) ^ 2 ≤ p ^ e * p := by
      have := Nat.mul_le_mul ih hp
      linarith
    rw [pow_succ]
    exact le_trans hc hd

lemma pow_cases (p e : ℕ) (hp : p.Prime) (hodd : p % 2 = 1) (he : 3 ≤ e) :
    e * p ≤ 21 ∨ (e * p + 3) ^ 2 ≤ p ^ e := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  rcases Nat.lt_or_ge e 6 with he6 | he6
  · have hcases : e = 3 ∨ e = 4 ∨ e = 5 := by omega
    rcases hcases with rfl | rfl | rfl
    · rcases Nat.lt_or_ge p 8 with h | h
      · left; omega
      · right
        have hp11 : 11 ≤ p := by
          by_contra hc
          have h9 : p = 9 := by omega
          rw [h9] at hp
          norm_num at hp
        have h2 : 11 * p ≤ p * p := Nat.mul_le_mul_right p hp11
        have h3 : 11 * (p * p) ≤ p * p * p := by
          have := Nat.mul_le_mul_left (p * p) hp11
          linarith
        have e1 : p ^ 3 = p * p * p := by ring
        have e2 : (3 * p + 3) ^ 2 = 9 * (p * p) + 18 * p + 9 := by ring
        rw [e1, e2]
        linarith
    · rcases Nat.lt_or_ge p 6 with h | h
      · left; omega
      · right
        have hp7 : 7 ≤ p := by omega
        have h2 : 7 * p ≤ p * p := Nat.mul_le_mul_right p hp7
        have h49 : 49 ≤ p * p := Nat.mul_le_mul hp7 hp7
        have h3 : 49 * (p * p) ≤ p * p * (p * p) := Nat.mul_le_mul_right (p * p) h49
        have e1 : p ^ 4 = p * p * (p * p) := by ring
        have e2 : (4 * p + 3) ^ 2 = 16 * (p * p) + 24 * p + 9 := by ring
        rw [e1, e2]
        linarith
    · rcases Nat.lt_or_ge p 4 with h | h
      · left; omega
      · right
        have hp5 : 5 ≤ p := by omega
        have h2 : 5 * p ≤ p * p := Nat.mul_le_mul_right p hp5
        have h25 : 25 ≤ p * p := Nat.mul_le_mul hp5 hp5
        have h3 : 25 * (p * p) ≤ p * p * (p * p) := Nat.mul_le_mul_right (p * p) h25
        have h4 : 5 * (p * p * (p * p)) ≤ p * p * (p * p) * p := by
          have := Nat.mul_le_mul_left (p * p * (p * p)) hp5
          linarith
        have e1 : p ^ 5 = p * p * (p * p) * p := by ring
        have e2 : (5 * p + 3) ^ 2 = 25 * (p * p) + 30 * p + 9 := by ring
        rw [e1, e2]
        linarith
  · exact Or.inr (pow_big p hp3 e he6)

lemma N_lt (j : ℕ) : (j * j + 7 * j + 9) < (j + 5) ^ 2 := by
  have : (j + 5) ^ 2 = j * j + 10 * j + 25 := by ring
  omega

lemma N_odd (j : ℕ) : (j * j + 7 * j + 9) % 2 = 1 := by
  have h : j * j % 2 = j % 2 := by
    rcases Nat.mod_two_eq_zero_or_one j with h | h <;> simp [Nat.mul_mod, h]
  omega

lemma prime_odd (j p : ℕ) (hp : p.Prime) (hd : p ∣ (j * j + 7 * j + 9)) : p % 2 = 1 := by
  rcases hp.eq_two_or_odd with h2 | ho
  · exfalso
    subst h2
    have := N_odd j
    omega
  · exact ho

/-- A prime power `p ^ e` with `e ≥ 3` that divides `N` has `e p ≤ n - 2`. -/
lemma ep_le (p e j : ℕ) (hp : p.Prime) (he : 3 ≤ e) (hd : p ^ e ∣ (j * j + 7 * j + 9)) (hj : 20 ≤ j) :
    e * p ≤ j + 1 := by
  have hodd := prime_odd j p hp (dvd_trans (dvd_pow_self p (by omega)) hd)
  have hle : p ^ e ≤ (j * j + 7 * j + 9) := Nat.le_of_dvd (by positivity) hd
  rcases pow_cases p e hp hodd he with h | h
  · omega
  · have hlt : (e * p + 3) ^ 2 < (j + 5) ^ 2 := lt_of_le_of_lt (le_trans h hle) (N_lt j)
    have : e * p + 3 < j + 5 := lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) hlt
    omega

lemma nd2 (j : ℕ) (hj : 20 ≤ j) : ¬ (j + 2) ∣ (j * j + 7 * j + 9) := by
  intro hd
  have h1 : (j + 2) ∣ (j * j + 7 * j + 9) + 1 := ⟨j + 5, by ring⟩
  have h2 : (j + 2) ∣ 1 := (Nat.dvd_add_right hd).mp h1
  have := Nat.le_of_dvd (by norm_num) h2
  omega

lemma nd3 (j : ℕ) (hj : 20 ≤ j) : ¬ (j + 3) ∣ (j * j + 7 * j + 9) := by
  intro hd
  have h1 : (j + 3) ∣ (j * j + 7 * j + 9) + 3 := ⟨j + 4, by ring⟩
  have h2 : (j + 3) ∣ 3 := (Nat.dvd_add_right hd).mp h1
  have := Nat.le_of_dvd (by norm_num) h2
  omega

lemma nd4 (j : ℕ) (hj : 20 ≤ j) : ¬ (j + 4) ∣ (j * j + 7 * j + 9) := by
  intro hd
  have h1 : (j + 4) ∣ (j * j + 7 * j + 9) + 3 := ⟨j + 3, by ring⟩
  have h2 : (j + 4) ∣ 3 := (Nat.dvd_add_right hd).mp h1
  have := Nat.le_of_dvd (by norm_num) h2
  omega

/-- Two different primes `p`, `q` with `2p, 2q ≥ n - 1` do not both have their squares as
divisors of `N`. -/
lemma uniq (p q j : ℕ) (hp : p.Prime) (hq : q.Prime) (hj : 20 ≤ j) (hdp : p ^ 2 ∣ (j * j + 7 * j + 9))
    (hdq : q ^ 2 ∣ (j * j + 7 * j + 9)) (h2p : j + 2 ≤ 2 * p) (h2q : j + 2 ≤ 2 * q) : p = q := by
  by_contra hne
  have hcop : Nat.Coprime (p ^ 2) (q ^ 2) := Nat.Coprime.pow 2 2 ((Nat.coprime_primes hp hq).mpr hne)
  have hd := hcop.mul_dvd_of_dvd_of_dvd hdp hdq
  have hle : p ^ 2 * q ^ 2 ≤ (j * j + 7 * j + 9) := Nat.le_of_dvd (by positivity) hd
  have hlt : (p * q) ^ 2 < (j + 5) ^ 2 := by
    rw [mul_pow]
    exact lt_of_le_of_lt hle (N_lt j)
  have h1 : p * q < j + 5 := lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) hlt
  have h2 : (j + 2) * (j + 2) ≤ (2 * p) * (2 * q) := Nat.mul_le_mul h2p h2q
  nlinarith

/-- There is `q`, equal to 1, a prime or 9, such that `N` divides `q n (n-2)!`
(`n = j + 3`). -/
lemma key (j : ℕ) : ∃ q, (q = 1 ∨ q.Prime ∨ q = 9) ∧
    (j * j + 7 * j + 9) ∣ q * ((j + 3) * (j + 1)!) := by
  rcases Nat.lt_or_ge j 20 with hj | hj
  · interval_cases j
    · exact ⟨3, by norm_num, by norm_num [Nat.factorial]⟩
    · exact ⟨17, by norm_num, by norm_num [Nat.factorial]⟩
    · exact ⟨9, by norm_num, by norm_num [Nat.factorial]⟩
    · exact ⟨13, by norm_num, by norm_num [Nat.factorial]⟩
    · exact ⟨53, by norm_num, by norm_num [Nat.factorial]⟩
    · exact ⟨23, by norm_num, by norm_num [Nat.factorial]⟩
    · exact ⟨29, by norm_num, by norm_num [Nat.factorial]⟩
    · exact ⟨107, by norm_num, by norm_num [Nat.factorial]⟩
    · exact ⟨43, by norm_num, by norm_num [Nat.factorial]⟩
    · exact ⟨17, by norm_num, by norm_num [Nat.factorial]⟩
    · exact ⟨179, by norm_num, by norm_num [Nat.factorial]⟩
    · exact ⟨23, by norm_num, by norm_num [Nat.factorial]⟩
    · exact ⟨79, by norm_num, by norm_num [Nat.factorial]⟩
    · exact ⟨269, by norm_num, by norm_num [Nat.factorial]⟩
    · exact ⟨101, by norm_num, by norm_num [Nat.factorial]⟩
    · exact ⟨113, by norm_num, by norm_num [Nat.factorial]⟩
    · exact ⟨29, by norm_num, by norm_num [Nat.factorial]⟩
    · exact ⟨139, by norm_num, by norm_num [Nat.factorial]⟩
    · exact ⟨1, by norm_num, by norm_num [Nat.factorial]⟩
    · exact ⟨503, by norm_num, by norm_num [Nat.factorial]⟩
  have hNpos : 0 < (j * j + 7 * j + 9) := by positivity
  by_cases hbig : ∃ p, p.Prime ∧ p ∣ (j * j + 7 * j + 9) ∧ j + 5 ≤ p
  · obtain ⟨p, hp, hpd, hpj⟩ := hbig
    obtain ⟨c, hc⟩ := hpd
    refine ⟨p, Or.inr (Or.inl hp), ?_⟩
    rw [hc]
    apply Nat.mul_dvd_mul_left
    apply Dvd.dvd.mul_left
    have hcd : c ∣ (j * j + 7 * j + 9) := ⟨p, by rw [hc]; ring⟩
    have hc5 : c < j + 5 := by
      by_contra hcon
      have h1 : (j + 5) * (j + 5) ≤ p * c := Nat.mul_le_mul hpj (by omega)
      have h2 := N_lt j
      have h3 : (j + 5) ^ 2 = (j + 5) * (j + 5) := by ring
      omega
    have hc0 : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · rw [h, mul_zero] at hc
        omega
      · exact h
    have hc2 : c ≠ j + 2 := fun h => nd2 j hj (h ▸ hcd)
    have hc3 : c ≠ j + 3 := fun h => nd3 j hj (h ▸ hcd)
    have hc4 : c ≠ j + 4 := fun h => nd4 j hj (h ▸ hcd)
    exact Nat.dvd_factorial hc0 (by omega)
  · push Not at hbig
    have hall : ∀ p, p.Prime → p ∣ (j * j + 7 * j + 9) → p ≤ j + 1 := by
      intro p hp hd
      have h5 := hbig p hp hd
      have hc2 : p ≠ j + 2 := fun h => nd2 j hj (h ▸ hd)
      have hc3 : p ≠ j + 3 := fun h => nd3 j hj (h ▸ hd)
      have hc4 : p ≠ j + 4 := fun h => nd4 j hj (h ▸ hd)
      omega
    by_cases hq : ∃ q, q.Prime ∧ q ^ 2 ∣ (j * j + 7 * j + 9) ∧ j + 2 ≤ 2 * q
    · obtain ⟨q, hqp, hqd, hq2⟩ := hq
      have hqle : q ≤ j + 1 := hall q hqp (dvd_trans (dvd_pow_self q (by norm_num)) hqd)
      refine ⟨q, Or.inr (Or.inl hqp), ?_⟩
      have hmain : (j * j + 7 * j + 9) ∣ q * (j + 1)! := by
        apply dvd_of_prime_pows _ _ hNpos.ne' (Nat.mul_ne_zero hqp.pos.ne' (Nat.factorial_ne_zero _))
        intro p e hp hd
        rcases Nat.lt_or_ge e 3 with he | he
        · have he012 : e = 0 ∨ e = 1 ∨ e = 2 := by omega
          rcases he012 with rfl | rfl | rfl
          · simp
          · rw [pow_one] at hd ⊢
            exact Dvd.dvd.mul_left (Nat.dvd_factorial hp.pos (hall p hp hd)) _
          · by_cases h2p : 2 * p ≤ j + 1
            · exact Dvd.dvd.mul_left
                (dvd_trans (pow_dvd_fact p 2 hp.pos) (Nat.factorial_dvd_factorial h2p)) _
            · have hpq : p = q := uniq p q j hp hqp hj hd hqd (by omega) hq2
              subst hpq
              rw [pow_two]
              exact Nat.mul_dvd_mul_left p (Nat.dvd_factorial hp.pos hqle)
        · exact Dvd.dvd.mul_left
            (dvd_trans (pow_dvd_fact p e hp.pos) (Nat.factorial_dvd_factorial (ep_le p e j hp he hd hj))) _
      have e : q * ((j + 3) * (j + 1)!) = (j + 3) * (q * (j + 1)!) := by ring
      rw [e]
      exact Dvd.dvd.mul_left hmain _
    · push Not at hq
      refine ⟨1, Or.inl rfl, ?_⟩
      rw [one_mul]
      apply Dvd.dvd.mul_left
      apply dvd_of_prime_pows _ _ hNpos.ne' (Nat.factorial_ne_zero _)
      intro p e hp hd
      rcases Nat.lt_or_ge e 3 with he | he
      · have he012 : e = 0 ∨ e = 1 ∨ e = 2 := by omega
        rcases he012 with rfl | rfl | rfl
        · simp
        · rw [pow_one] at hd ⊢
          exact Nat.dvd_factorial hp.pos (hall p hp hd)
        · have h2p : 2 * p ≤ j + 1 := by
            have := hq p hp hd
            omega
          exact dvd_trans (pow_dvd_fact p 2 hp.pos) (Nat.factorial_dvd_factorial h2p)
      · exact dvd_trans (pow_dvd_fact p e hp.pos) (Nat.factorial_dvd_factorial (ep_le p e j hp he hd hj))

theorem result (n : ℕ) (hn : 3 ≤ n) (hne : a n ≠ 9) : a n = 1 ∨ (a n).Prime := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 3 := ⟨n - 3, by omega⟩
  have hjq : (0 : ℚ) ≤ j := Nat.cast_nonneg j
  -- the value of the continued fraction
  have hval : 1 / nest (j + 1) (-3 : ℚ)
      = (((3 : ℤ) * r (j + 1) + ((j : ℤ) + 3) * r j : ℤ) : ℚ) / (((j * j + 7 * j + 9) : ℕ) : ℚ) := by
    rw [nest_neg j _ (by norm_num), one_div_div]
    have e1 : (r (j + 1) : ℚ) * (-3) - (j + 3) * r j
        = -(((3 : ℤ) * r (j + 1) + ((j : ℤ) + 3) * r j : ℤ) : ℚ) := by
      push_cast
      ring
    have e2 : ((j : ℚ) + 2) * (-3) - (j + 1) * (j + 3) = -(((j * j + 7 * j + 9) : ℕ) : ℚ) := by
      push_cast
      ring
    rw [e1, e2, neg_div_neg_eq]
  -- the numerator in terms of the left factorial
  obtain ⟨h1, h2⟩ := two_r j
  have hr0 : 0 ≤ r j := by
    have : (0 : ℤ) ≤ ((j : ℤ) + 1) * lf j := by positivity
    omega
  have hr1 : 0 ≤ r (j + 1) := by
    have : (0 : ℤ) ≤ ((j : ℤ) + 2) * lf (j + 1) := by positivity
    omega
  have hnum : 2 * ((3 : ℤ) * r (j + 1) + ((j : ℤ) + 3) * r j) + (((j + 3) * (j + 1)! : ℕ) : ℤ)
      = (((j * j + 7 * j + 9) : ℕ) : ℤ) * (lf (j + 1) : ℕ) := by
    have e1 : (lf (j + 1) : ℤ) = lf j + j ! := by rw [lf_succ]; push_cast; ring
    rw [Nat.factorial_succ]
    push_cast
    rw [e1] at h2 ⊢
    linear_combination (3 : ℤ) * h2 + ((j : ℤ) + 3) * h1
  have hnn : 0 ≤ (3 : ℤ) * r (j + 1) + ((j : ℤ) + 3) * r j :=
    add_nonneg (mul_nonneg (by norm_num) hr1) (mul_nonneg (by positivity) hr0)
  obtain ⟨A, hA⟩ := Int.eq_ofNat_of_zero_le hnn
  rw [hA] at hval hnum
  have hnumN : 2 * A + (j + 3) * (j + 1)! = (j * j + 7 * j + 9) * lf (j + 1) := by exact_mod_cast hnum
  -- reduce the fraction
  have hNpos : 0 < (j * j + 7 * j + 9) := by positivity
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
  rw [hden] at hne ⊢
  -- D divides q
  obtain ⟨q, hq, hqdvd⟩ := key j
  have h2q : D * g ∣ 2 * q * A' * g := by
    rw [← hD]
    have e1 : 2 * q * A' * g + q * ((j + 3) * (j + 1)!) = (j * j + 7 * j + 9) * (q * lf (j + 1)) := by
      rw [show 2 * q * A' * g = q * (2 * A) by rw [hA']; ring, ← mul_add, hnumN]
      ring
    have h3 : (j * j + 7 * j + 9) ∣ 2 * q * A' * g + q * ((j + 3) * (j + 1)!) := ⟨_, e1⟩
    exact (Nat.dvd_add_left hqdvd).mp h3
  have h3 : D ∣ 2 * q * A' := Nat.dvd_of_mul_dvd_mul_right hg h2q
  have h4 : D ∣ 2 * q := (Nat.Coprime.dvd_of_dvd_mul_right hcop.symm h3)
  have hDodd : Nat.Coprime D 2 := by
    rw [Nat.coprime_two_right]
    have : ¬ 2 ∣ D := by
      intro h
      have h5 : 2 ∣ (j * j + 7 * j + 9) := by rw [hD]; exact Dvd.dvd.mul_right h g
      have := N_odd j
      omega
    exact Nat.odd_iff.mpr (by omega)
  have h5 : D ∣ q := hDodd.dvd_of_dvd_mul_left h4
  rcases hq with rfl | hq | rfl
  · exact Or.inl (Nat.dvd_one.mp h5)
  · rcases (Nat.dvd_prime hq).mp h5 with h | h
    · exact Or.inl h
    · exact Or.inr (h ▸ hq)
  · have h7 : D ∣ 3 ^ 2 := by norm_num; exact h5
    obtain ⟨m, hm, hDm⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp h7
    interval_cases m
    · exact Or.inl (by simpa using hDm)
    · exact Or.inr (by rw [hDm]; norm_num)
    · exact absurd (by rw [hDm]; norm_num) hne

end OMA.A362086

theorem OMA.solution : type_of% @OMA.S_oeis_a362086.main :=
  fun n hn hne => OMA.A362086.result n hn hne
