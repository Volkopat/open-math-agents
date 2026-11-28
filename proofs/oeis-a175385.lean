import OMAStatements.S_oeis_a175385
import Mathlib

-- Problem: OEIS A175385, conjecture of Shevelev and Seidov: for n > 1 the rational number
-- S(n) = Sum_{i=1..n} C(2n-i-1, i-1)/i is not an integer.
-- Statement: statements/oeis-a175385.lean (declaration OMA.S_oeis_a175385.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. Let F be the Fibonacci numbers and L(m) = F(m+1) + F(m-1) the Lucas numbers.
-- Step 1. The identity (2n/i) C(2n-i-1, i-1) = C(2n-i, i) + C(2n-i-1, i-1) and the formula
-- F(m+1) = Sum_i C(m-i, i) give 2n S(n) = L(2n) - 1. So if S(n) is an integer, then 2n divides
-- L(2n) - 1.
-- Step 2. Let Q = [[1,1],[1,0]], so Q^(k+1) = [[F(k+2),F(k+1)],[F(k+1),F(k)]], the trace of Q^m
-- is L(m) and det(Q^(2n)) = 1. Modulo 4 we have Q^6 = 1, thus L(2n) mod 4 is 2 or 3, and it is
-- 2 if 3 divides n. So 4 does not divide L(2n) - 1 (this excludes even n), and L(2n) - 1 is odd
-- if 3 divides n.
-- Step 3. Let n be odd and not divisible by 3, and let p >= 5 be the least prime factor of n.
-- Assume L(2n) == 1 (mod p). Then X = Q^(2n) has trace 1 and determinant 1 modulo p, thus
-- X^2 = X - 1, X^3 = -1 and Q^(12n) = 1.
-- If p = 5: Q^10 = -1 modulo 5, thus Q^(2n) = -1 and L(2n) == -2, a contradiction.
-- If p > 5: M = 2Q - 1 satisfies M^2 = 5. In characteristic p, 2 Q^p - 1 = M^p = e M with
-- e = 5^((p-1)/2) = 1 or -1. If e = 1 then Q^(p-1) = 1. If e = -1 then Q^p = 1 - Q and
-- Q^(2(p+1)) = 1. The numbers p - 1 and 2 (p + 1) are coprime to n, because p is the least
-- prime factor of the odd number n. So the order of Q divides gcd(D, 12n) which divides 12,
-- thus Q^12 = 1 and p divides F(12) = 144, a contradiction.

namespace OMA.A175385

open Finset Matrix

lemma sum_Icc_eq_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ k ∈ Icc 1 n, f k = ∑ j ∈ range n, f (j + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_Icc_succ_top (by omega), ih, sum_range_succ]

/-- The Lucas number L(m), for m ≥ 1. -/
def luc (m : ℕ) : ℕ := Nat.fib (m + 1) + Nat.fib (m - 1)

lemma fib_sum (m : ℕ) : ∑ i ∈ range (m + 1), (m - i).choose i = Nat.fib (m + 1) := by
  rw [Nat.fib_succ_eq_sum_choose, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have h := sum_range_reflect (fun k => k.choose (m - k)) (m + 1)
  rw [← h]
  apply sum_congr rfl
  intro i hi
  have := mem_range.1 hi
  have e1 : m + 1 - 1 - i = m - i := by omega
  have e2 : m - (m - i) = i := by omega
  simp only [e1, e2]

lemma sumA (n : ℕ) : ∑ i ∈ range (n + 1), (2 * n - i).choose i = Nat.fib (2 * n + 1) := by
  rw [← fib_sum (2 * n)]
  apply sum_subset (range_subset_range.2 (by omega))
  intro i hi hni
  have h1 := mem_range.1 hi
  have h2 : ¬ i < n + 1 := fun h => hni (mem_range.2 h)
  exact Nat.choose_eq_zero_of_lt (by omega)

lemma sumB (n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ range n, (2 * n - j - 2).choose j = Nat.fib (2 * n - 1) := by
  have e : 2 * n - 1 = (2 * n - 2) + 1 := by omega
  rw [e, ← fib_sum (2 * n - 2)]
  have h : ∑ j ∈ range n, (2 * n - j - 2).choose j = ∑ j ∈ range n, (2 * n - 2 - j).choose j :=
    sum_congr rfl (fun j _ => by congr 1; omega)
  rw [h]
  apply sum_subset (range_subset_range.2 (by omega))
  intro i hi hni
  have h1 := mem_range.1 hi
  have h2 : ¬ i < n := fun h => hni (mem_range.2 h)
  exact Nat.choose_eq_zero_of_lt (by omega)

lemma key_sum (n : ℕ) (hn : 1 ≤ n) :
    (2 * n : ℚ) * ∑ i ∈ Icc 1 n, ((2 * n - i - 1).choose (i - 1) : ℚ) / (i : ℚ)
      = (luc (2 * n) : ℚ) - 1 := by
  rw [sum_Icc_eq_range, mul_sum]
  have hterm : ∀ j ∈ range n,
      (2 * n : ℚ) * (((2 * n - (j + 1) - 1).choose (j + 1 - 1) : ℚ) / ((j + 1 : ℕ) : ℚ))
        = (((2 * n - (j + 1)).choose (j + 1) : ℕ) : ℚ) + (((2 * n - j - 2).choose j : ℕ) : ℚ) := by
    intro j hj
    have hj' := mem_range.1 hj
    have e1 : 2 * n - (j + 1) - 1 = 2 * n - j - 2 := by omega
    have h := Nat.add_one_mul_choose_eq (2 * n - j - 2) j
    have e2 : 2 * n - j - 2 + 1 = 2 * n - (j + 1) := by omega
    rw [e2] at h
    rw [e1, Nat.add_sub_cancel]
    have hq : ((2 * n - (j + 1) : ℕ) : ℚ) * (((2 * n - j - 2).choose j : ℕ) : ℚ)
        = (((2 * n - (j + 1)).choose (j + 1) : ℕ) : ℚ) * ((j : ℚ) + 1) := by exact_mod_cast h
    have hc : ((2 * n - (j + 1) : ℕ) : ℚ) = 2 * n - (j + 1) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hc] at hq
    have hne : ((j : ℚ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    linear_combination hq
  rw [sum_congr rfl hterm, sum_add_distrib]
  have hA := sumA n
  rw [sum_range_succ'] at hA
  have hB := sumB n hn
  have hA' : (∑ j ∈ range n, (((2 * n - (j + 1)).choose (j + 1) : ℕ) : ℚ))
      = (Nat.fib (2 * n + 1) : ℚ) - 1 := by
    have := congrArg (fun x : ℕ => (x : ℚ)) hA
    simp only [Nat.cast_add, Nat.cast_sum, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one] at this
    linarith
  have hB' : (∑ j ∈ range n, (((2 * n - j - 2).choose j : ℕ) : ℚ)) = (Nat.fib (2 * n - 1) : ℚ) := by
    have := congrArg (fun x : ℕ => (x : ℚ)) hB
    simpa only [Nat.cast_sum] using this
  rw [hA', hB']
  unfold luc
  push_cast
  ring

/-- The Fibonacci matrix. -/
def Q (R : Type*) [CommRing R] : Matrix (Fin 2) (Fin 2) R := !![1, 1; 1, 0]

lemma Q_pow (R : Type*) [CommRing R] (k : ℕ) :
    Q R ^ (k + 1) = !![(Nat.fib (k + 2) : R), (Nat.fib (k + 1) : R);
      (Nat.fib (k + 1) : R), (Nat.fib k : R)] := by
  induction k with
  | zero => simp [Q]
  | succ k ih =>
    rw [pow_succ, ih, Q]
    have h3 : Nat.fib (k + 1 + 2) = Nat.fib (k + 1) + Nat.fib (k + 2) := Nat.fib_add_two
    have h2 : Nat.fib (k + 2) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, h3] <;> rw [h2] <;> push_cast <;> ring

lemma trace_Q_pow (R : Type*) [CommRing R] (m : ℕ) (hm : 1 ≤ m) :
    (Q R ^ m) 0 0 + (Q R ^ m) 1 1 = (luc m : R) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [Q_pow]
  simp [luc]

lemma det_Q_pow (R : Type*) [CommRing R] (n : ℕ) :
    (Q R ^ (2 * n)) 0 0 * (Q R ^ (2 * n)) 1 1 - (Q R ^ (2 * n)) 0 1 * (Q R ^ (2 * n)) 1 0 = 1 := by
  rw [← Matrix.det_fin_two, Matrix.det_pow]
  have : (Q R).det = -1 := by simp [Q, Matrix.det_fin_two_of]
  rw [this, pow_mul]; simp

lemma sq_of_trace_det {R : Type*} [CommRing R] (X : Matrix (Fin 2) (Fin 2) R)
    (ht : X 0 0 + X 1 1 = 1) (hd : X 0 0 * X 1 1 - X 0 1 * X 1 0 = 1) : X * X = X - 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (X 0 0) * ht - hd
  · linear_combination (X 0 1) * ht
  · linear_combination (X 1 0) * ht
  · linear_combination (X 1 1) * ht - hd

/-- If L(2n) = 1 in R, then Q^(12 n) = 1. -/
lemma pow_twelve (R : Type*) [CommRing R] (n : ℕ) (hn : 1 ≤ n) (hL : (luc (2 * n) : R) = 1) :
    Q R ^ (12 * n) = 1 := by
  have hsq := sq_of_trace_det (Q R ^ (2 * n))
    (by rw [trace_Q_pow R (2 * n) (by omega), hL]) (det_Q_pow R n)
  have h3 : (Q R ^ (2 * n)) ^ 3 = -1 := by
    rw [pow_succ, pow_two, hsq, sub_mul, one_mul, hsq]; abel
  have e : 12 * n = 2 * n * 3 * 2 := by ring
  rw [e, pow_mul, pow_mul, h3]; simp

lemma Q_sq (R : Type*) [CommRing R] : Q R * Q R = Q R + 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Q, Matrix.mul_apply, Fin.sum_univ_two]

lemma two_ne (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h2)

lemma five_ne (p : ℕ) [Fact p.Prime] (hp5 : p ≠ 5) : (5 : ZMod p) ≠ 0 := by
  intro h
  have h2 : ((5 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h2
  exact hp5 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_five).1 h2)

/-- The order of Q modulo p divides p - 1 or 2 (p + 1). -/
lemma frob (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    Q (ZMod p) ^ (p - 1) = 1 ∨ Q (ZMod p) ^ (2 * (p + 1)) = 1 := by
  have hp : p.Prime := Fact.out
  have hsq : Q (ZMod p) * Q (ZMod p) = Q (ZMod p) + 1 := Q_sq _
  generalize Q (ZMod p) = q at hsq ⊢
  have hM2 : (q + q - 1) * (q + q - 1) = (5 : ZMod p) • (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
    have e : (q + q - 1) * (q + q - 1) = (q * q + q * q + q * q + q * q) - (q + q + q + q) + 1 := by
      noncomm_ring
    rw [e, hsq]
    have e5 : (5 : ZMod p) • (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) = 1 + 1 + 1 + 1 + 1 := by
      have : (5 : ZMod p) = 1 + 1 + 1 + 1 + 1 := by norm_num
      rw [this, add_smul, add_smul, add_smul, add_smul, one_smul]
    rw [e5]; abel
  have hodd : p = 2 * (p / 2) + 1 := by
    obtain ⟨k, hk⟩ := hp.eq_two_or_odd'.resolve_left hp2
    omega
  have gen : ∀ k : ℕ, (q + q - 1) ^ (2 * k + 1) = ((5 : ZMod p) ^ k) • (q + q - 1) := by
    intro k
    rw [pow_succ, pow_mul, pow_two, hM2, smul_pow, one_pow, smul_mul_assoc, one_mul]
  have hMp : (q + q - 1) ^ p = ((5 : ZMod p) ^ (p / 2)) • (q + q - 1) := by
    have h := gen (p / 2)
    rwa [← hodd] at h
  have hMp' : (q + q - 1) ^ p = q ^ p + q ^ p - 1 := by
    rw [sub_pow_char_of_commute p (Commute.one_right _),
      add_pow_char_of_commute p (Commute.refl q), one_pow]
  have h2 := two_ne p hp2
  have hinv : q * (q - 1) = 1 := by rw [mul_sub, mul_one, hsq]; abel
  have hpp : p - 1 + 1 = p := by have := hp.pos; omega
  rcases ZMod.pow_div_two_eq_neg_one_or_one p (five_ne p hp5) with h | h
  · left
    rw [h, one_smul] at hMp
    have e : q ^ p + q ^ p - 1 = q + q - 1 := hMp'.symm.trans hMp
    have e2 : (2 : ZMod p) • (q ^ p - q) = 0 := by
      rw [two_smul]
      have : q ^ p - q + (q ^ p - q) = (q ^ p + q ^ p - 1) - (q + q - 1) := by abel
      rw [this, e, sub_self]
    have hqp : q ^ p = q := sub_eq_zero.1 ((smul_eq_zero.1 e2).resolve_left h2)
    have h1 : q ^ (p - 1) * q = q := by rw [← pow_succ, hpp, hqp]
    calc q ^ (p - 1) = q ^ (p - 1) * (q * (q - 1)) := by rw [hinv, mul_one]
      _ = (q ^ (p - 1) * q) * (q - 1) := by rw [mul_assoc]
      _ = 1 := by rw [h1, hinv]
  · right
    rw [h, neg_one_smul] at hMp
    have e : q ^ p + q ^ p - 1 = -(q + q - 1) := hMp'.symm.trans hMp
    have e2 : (2 : ZMod p) • (q ^ p - (1 - q)) = 0 := by
      rw [two_smul]
      have : q ^ p - (1 - q) + (q ^ p - (1 - q)) = (q ^ p + q ^ p - 1) - (-(q + q - 1)) := by abel
      rw [this, e, sub_self]
    have hqp : q ^ p = 1 - q := sub_eq_zero.1 ((smul_eq_zero.1 e2).resolve_left h2)
    have h1 : q ^ (p + 1) = -1 := by
      rw [pow_succ, hqp, sub_mul, one_mul, hsq]; abel
    rw [mul_comm, pow_mul, h1]; simp

lemma prime_case (p n : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hn : 1 ≤ n)
    (hD1 : Nat.Coprime (p - 1) n) (hD2 : Nat.Coprime (2 * (p + 1)) n)
    (hL : (luc (2 * n) : ZMod p) = 1) : False := by
  have hp : p.Prime := Fact.out
  have h12n := pow_twelve (ZMod p) n hn hL
  have hD : ∃ D, Nat.Coprime D n ∧ Q (ZMod p) ^ D = 1 := by
    rcases frob p hp2 hp5 with h | h
    · exact ⟨p - 1, hD1, h⟩
    · exact ⟨2 * (p + 1), hD2, h⟩
  obtain ⟨D, hc, hQD⟩ := hD
  have ho1 : orderOf (Q (ZMod p)) ∣ D := orderOf_dvd_of_pow_eq_one hQD
  have ho2 : orderOf (Q (ZMod p)) ∣ 12 * n := orderOf_dvd_of_pow_eq_one h12n
  have ho3 : orderOf (Q (ZMod p)) ∣ 12 :=
    Nat.Coprime.dvd_of_dvd_mul_right (hc.coprime_dvd_left ho1) ho2
  have h12 : Q (ZMod p) ^ 12 = 1 := orderOf_dvd_iff_pow_eq_one.1 ho3
  have h := Q_pow (ZMod p) 11
  rw [h12] at h
  have h01 := congrFun (congrFun h 0) 1
  have hfib : Nat.fib 12 = 144 := by decide
  simp only [hfib] at h01
  simp at h01
  have hd : p ∣ 144 := (ZMod.natCast_eq_zero_iff 144 p).1 (by exact_mod_cast h01.symm)
  have hd' : p ∣ 2 ^ 4 * 3 ^ 2 := by norm_num; exact hd
  rcases hp.dvd_mul.1 hd' with h' | h'
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h'))
  · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h'))

lemma Q6 : Q (ZMod 4) ^ 6 = 1 := by decide

lemma luc_mod_four (n : ℕ) (hn : 1 ≤ n) :
    (luc (2 * n) % 4 = 2 ∨ luc (2 * n) % 4 = 3) ∧ (3 ∣ n → luc (2 * n) % 4 = 2) := by
  have ht := trace_Q_pow (ZMod 4) (2 * n) (by omega)
  have hdm : 2 * n = 6 * (2 * n / 6) + 2 * n % 6 := (Nat.div_add_mod _ _).symm
  have hpow : Q (ZMod 4) ^ (2 * n) = Q (ZMod 4) ^ (2 * n % 6) := by
    conv_lhs => rw [hdm, pow_add, pow_mul, Q6, one_pow, one_mul]
  rw [hpow] at ht
  have conv2 : (luc (2 * n) : ZMod 4) = ((2 : ℕ) : ZMod 4) → luc (2 * n) % 4 = 2 := fun h =>
    (ZMod.natCast_eq_natCast_iff' _ _ _).1 h
  have conv3 : (luc (2 * n) : ZMod 4) = ((3 : ℕ) : ZMod 4) → luc (2 * n) % 4 = 3 := fun h =>
    (ZMod.natCast_eq_natCast_iff' _ _ _).1 h
  have h0 : (Q (ZMod 4) ^ 0) 0 0 + (Q (ZMod 4) ^ 0) 1 1 = ((2 : ℕ) : ZMod 4) := by decide
  have h2 : (Q (ZMod 4) ^ 2) 0 0 + (Q (ZMod 4) ^ 2) 1 1 = ((3 : ℕ) : ZMod 4) := by decide
  have h4 : (Q (ZMod 4) ^ 4) 0 0 + (Q (ZMod 4) ^ 4) 1 1 = ((3 : ℕ) : ZMod 4) := by decide
  have hr : 2 * n % 6 = 0 ∨ 2 * n % 6 = 2 ∨ 2 * n % 6 = 4 := by omega
  constructor
  · rcases hr with hr | hr | hr <;> rw [hr] at ht
    · exact Or.inl (conv2 (ht.symm.trans h0))
    · exact Or.inr (conv3 (ht.symm.trans h2))
    · exact Or.inr (conv3 (ht.symm.trans h4))
  · intro h3
    have hr0 : 2 * n % 6 = 0 := by omega
    rw [hr0] at ht
    exact conv2 (ht.symm.trans h0)

lemma Q10 : Q (ZMod 5) ^ 10 = -1 := by decide

lemma mod_five (n : ℕ) (hodd : Odd n) (h5 : 5 ∣ n) (hL : (luc (2 * n) : ZMod 5) = 1) : False := by
  obtain ⟨t, rfl⟩ := h5
  have ht : Odd t := by
    rcases Nat.even_or_odd t with he | ho
    · exact absurd hodd (Nat.not_odd_iff_even.2 (he.mul_left 5))
    · exact ho
  have htr := trace_Q_pow (ZMod 5) (2 * (5 * t)) (by obtain ⟨k, hk⟩ := ht; omega)
  have e : 2 * (5 * t) = 10 * t := by ring
  rw [e, pow_mul, Q10, ht.neg_one_pow, ← e, hL] at htr
  simp at htr
  revert htr
  decide

lemma cast_eq_one (m L : ℕ) (h : (m : ℤ) ∣ (L : ℤ) - 1) : (L : ZMod m) = 1 := by
  have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd ((L : ℤ) - 1) m).2 h
  push_cast at h0
  linear_combination h0

theorem main' (n : ℕ) (hn : 1 < n) :
    ¬ ∃ z : ℤ, (∑ i ∈ Icc 1 n, ((2 * n - i - 1).choose (i - 1) : ℚ) / (i : ℚ)) = (z : ℚ) := by
  rintro ⟨z, hz⟩
  have hk := key_sum n (by omega)
  rw [hz] at hk
  have hk' : (2 * n : ℤ) * z = (luc (2 * n) : ℤ) - 1 := by exact_mod_cast hk
  have hdvd : ((2 * n : ℕ) : ℤ) ∣ (luc (2 * n) : ℤ) - 1 := ⟨z, by rw [← hk']; push_cast; ring⟩
  obtain ⟨h4, h43⟩ := luc_mod_four n (by omega)
  by_cases he : Even n
  · obtain ⟨t, ht⟩ := he
    have h4d : (4 : ℤ) ∣ (luc (2 * n) : ℤ) - 1 :=
      Dvd.dvd.trans ⟨(t : ℤ), by rw [ht]; push_cast; ring⟩ hdvd
    omega
  · rw [Nat.not_even_iff_odd] at he
    by_cases h3 : 3 ∣ n
    · have h2d : (2 : ℤ) ∣ (luc (2 * n) : ℤ) - 1 :=
        Dvd.dvd.trans ⟨(n : ℤ), by push_cast; ring⟩ hdvd
      have := h43 h3
      omega
    · have hpp : n.minFac.Prime := Nat.minFac_prime (by omega)
      have hpn : n.minFac ∣ n := Nat.minFac_dvd n
      have hp2 : n.minFac ≠ 2 := by
        intro h; rw [h] at hpn
        exact (Nat.not_even_iff_odd.2 he) (even_iff_two_dvd.2 hpn)
      have hp3 : n.minFac ≠ 3 := by
        intro h; rw [h] at hpn; exact h3 hpn
      have hLp : (luc (2 * n) : ZMod n.minFac) = 1 :=
        cast_eq_one _ _ (Dvd.dvd.trans (Int.natCast_dvd_natCast.2 (Dvd.dvd.mul_left hpn 2)) hdvd)
      by_cases hp5 : n.minFac = 5
      · rw [hp5] at hLp hpn
        exact mod_five n he hpn hLp
      · have hfact : Fact n.minFac.Prime := ⟨hpp⟩
        have hodd_p : Odd n.minFac := hpp.eq_two_or_odd'.resolve_left hp2
        have hp_two := hpp.two_le
        have hD1 : Nat.Coprime (n.minFac - 1) n :=
          (Nat.coprime_of_lt_minFac (by omega) (by omega)).symm
        have hhalf : Nat.Coprime n ((n.minFac + 1) / 2) := by
          apply Nat.coprime_of_lt_minFac
          · obtain ⟨k, hk⟩ := hodd_p; omega
          · obtain ⟨k, hk⟩ := hodd_p; omega
        have hn2 : Nat.Coprime n 2 := Nat.coprime_two_right.2 he
        have e : 2 * (n.minFac + 1) = 2 * (2 * ((n.minFac + 1) / 2)) := by
          obtain ⟨k, hk⟩ := hodd_p; omega
        have hD2 : Nat.Coprime (2 * (n.minFac + 1)) n := by
          rw [e]; exact (Nat.Coprime.mul_right hn2 (Nat.Coprime.mul_right hn2 hhalf)).symm
        exact prime_case n.minFac n hp2 hp3 hp5 (by omega) hD1 hD2 hLp

end OMA.A175385

theorem OMA.solution : type_of% @OMA.S_oeis_a175385.main :=
  fun n hn => OMA.A175385.main' n hn
