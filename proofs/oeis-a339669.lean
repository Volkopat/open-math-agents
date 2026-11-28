import OMAStatements.S_oeis_a339669
import Mathlib

-- Problem: OEIS A339669, conjectures of Lagneau: the number a(n) of Fibonacci divisors of
-- Lucas(n)^2 + 1 satisfies a(6n+3) = 1 and a(6n+1) = a(6n+5) = 2.
-- Statement: statements/oeis-a339669.lean (declaration OMA.S_oeis_a339669.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. Let n be odd, F = Fibonacci, L = Lucas, N = L(n)^2 + 1. Cassini's identity
-- F(n)^2 = F(n+1) F(n-1) + 1 gives N + 3 = 5 F(n)^2 and L(2n) = L(n)^2 + 2 = N + 1.
-- Let F(k) divide N.
-- (1) gcd(F(k), F(n)) divides 3 and gcd(F(k), L(n)) = 1. Because F(2n) = F(n) L(n), the number
-- F(gcd(k, 2n)) = gcd(F(k), F(2n)) divides 3, thus gcd(k, 2n) is 1, 2 or 4, and it is not 4
-- because n is odd.
-- (2) Modulo N the matrix X = Q^(2n), Q = [[1,1],[1,0]], has trace L(2n) = 1 and determinant 1,
-- thus X^3 = -1 and N divides F(6n). So F(k) divides F(6n), and k divides 6n if k >= 3.
-- (3) From (1) and (2), k divides 6. The case k = 6 is not possible, because F(6) = 8 and
-- L(n)^2 + 1 is not divisible by 4. So F(k) is 1 or 2.
-- The number 2 divides N if and only if L(n) is odd, that is, if and only if 3 does not divide
-- n. So the set of Fibonacci divisors is {1} for n = 6m+3 and {1, 2} for n = 6m+1, 6m+5.

namespace OMA.A339669

open Finset Matrix OMA.S_oeis_a339669

/-- The Lucas number L(m), for m ≥ 1, in terms of Fibonacci numbers. -/
def luc (m : ℕ) : ℕ := Nat.fib (m + 1) + Nat.fib (m - 1)

lemma lucas_succ_succ (n : ℕ) : lucas (n + 2) = lucas (n + 1) + lucas n := by
  rw [lucas]

lemma lucas_eq_aux : ∀ n : ℕ, lucas (n + 1) = Nat.fib (n + 2) + Nat.fib n ∧
    lucas (n + 2) = Nat.fib (n + 3) + Nat.fib (n + 1) := by
  intro n
  induction n with
  | zero => exact ⟨by decide, by decide⟩
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have h0 : lucas (n + 1 + 2) = lucas (n + 2) + lucas (n + 1) := lucas_succ_succ (n + 1)
    have h1 : Nat.fib (n + 2 + 2) = Nat.fib (n + 2) + Nat.fib (n + 3) := Nat.fib_add_two
    have h3 : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
    have e1 : n + 1 + 3 = n + 2 + 2 := by ring
    have e2 : n + 1 + 1 = n + 2 := by ring
    rw [h0, ih.1, ih.2, e1, e2, h1]
    omega

lemma lucas_eq (n : ℕ) (hn : 1 ≤ n) : lucas n = Nat.fib (n + 1) + Nat.fib (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact (lucas_eq_aux k).1

lemma lucas_par : ∀ m : ℕ,
    lucas (3 * m) % 2 = 0 ∧ lucas (3 * m + 1) % 2 = 1 ∧ lucas (3 * m + 2) % 2 = 1 := by
  intro m
  induction m with
  | zero => exact ⟨by decide, by decide, by decide⟩
  | succ m ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    have a0 : lucas (3 * (m + 1)) = lucas (3 * m + 2) + lucas (3 * m + 1) := lucas_succ_succ _
    have a1 : lucas (3 * (m + 1) + 1) = lucas (3 * (m + 1)) + lucas (3 * m + 2) :=
      lucas_succ_succ _
    have a2 : lucas (3 * (m + 1) + 2) = lucas (3 * (m + 1) + 1) + lucas (3 * (m + 1)) :=
      lucas_succ_succ _
    refine ⟨by omega, by omega, by omega⟩

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

lemma fib6 (R : Type*) [CommRing R] (n : ℕ) (hn : 1 ≤ n) (hL : (luc (2 * n) : R) = 1) :
    (Nat.fib (6 * n) : R) = 0 := by
  have hsq := sq_of_trace_det (Q R ^ (2 * n))
    (by rw [trace_Q_pow R (2 * n) (by omega), hL]) (det_Q_pow R n)
  have h3 : (Q R ^ (2 * n)) ^ 3 = -1 := by
    rw [pow_succ, pow_two, hsq, sub_mul, one_mul, hsq]; abel
  have e : 6 * n = (6 * n - 1) + 1 := by omega
  have h := Q_pow R (6 * n - 1)
  rw [← e] at h
  have e2 : Q R ^ (6 * n) = (Q R ^ (2 * n)) ^ 3 := by rw [← pow_mul]; congr 1; ring
  rw [e2, h3] at h
  have h01 := congrFun (congrFun h 0) 1
  simp at h01
  first
    | exact h01
    | exact h01.symm

lemma cassini (n : ℕ) (hodd : Odd n) :
    Nat.fib n ^ 2 = Nat.fib (n + 1) * Nat.fib (n - 1) + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by obtain ⟨t, ht⟩ := hodd; omega⟩
  have h := congrArg Matrix.det (Q_pow ℤ k)
  rw [Matrix.det_pow, Matrix.det_fin_two_of] at h
  have hd : (Q ℤ).det = -1 := by simp [Q, Matrix.det_fin_two_of]
  rw [hd, hodd.neg_one_pow] at h
  have hz : ((Nat.fib (k + 1) : ℤ)) ^ 2 = Nat.fib (k + 2) * Nat.fib k + 1 := by linarith
  rw [Nat.add_sub_cancel]
  exact_mod_cast hz

/-- For an odd n, a Fibonacci number that divides L(n)^2 + 1 is 1 or 2. -/
lemma fib_div (n k : ℕ) (hodd : Odd n) (hk : Nat.fib k ∣ lucas n ^ 2 + 1) :
    Nat.fib k = 1 ∨ Nat.fib k = 2 := by
  have hn : 1 ≤ n := by obtain ⟨t, ht⟩ := hodd; omega
  have hL := lucas_eq n hn
  have hC := cassini n hodd
  have hrec : Nat.fib (n + 1) = Nat.fib n + Nat.fib (n - 1) := by
    have h : Nat.fib (n - 1 + 2) = Nat.fib (n - 1) + Nat.fib (n - 1 + 1) := Nat.fib_add_two
    have e1 : n - 1 + 2 = n + 1 := by omega
    have e2 : n - 1 + 1 = n := by omega
    rw [e1, e2] at h
    omega
  have h2n : Nat.fib (2 * n) = Nat.fib n * lucas n := by
    rw [Nat.fib_two_mul, hL]
    congr 1
    omega
  have hluc : luc (2 * n) = lucas n ^ 2 + 2 := by
    unfold luc
    have h1 := Nat.fib_two_mul_add_one n
    have h2 := Nat.fib_two_mul_add_one (n - 1)
    have e1 : 2 * (n - 1) + 1 = 2 * n - 1 := by omega
    have e2 : n - 1 + 1 = n := by omega
    rw [e1, e2] at h2
    rw [h1, h2, hL, hrec]
    rw [hrec] at hC
    nlinarith [hC]
  have h5 : lucas n ^ 2 + 1 + 3 = 5 * Nat.fib n ^ 2 := by
    rw [hL, hrec]
    rw [hrec] at hC
    nlinarith [hC]
  generalize hN : lucas n ^ 2 + 1 = N at hk h5
  generalize hF : Nat.fib n = F at h5 h2n
  generalize hLl : lucas n = L at hN h2n hluc
  -- gcd with F
  have g1 : Nat.gcd (Nat.fib k) F ∣ 3 := by
    have hgN : Nat.gcd (Nat.fib k) F ∣ N := Dvd.dvd.trans (Nat.gcd_dvd_left _ _) hk
    have hgF : Nat.gcd (Nat.fib k) F ∣ N + 3 := by
      rw [h5]
      exact Dvd.dvd.mul_left (Dvd.dvd.pow (Nat.gcd_dvd_right _ _) two_ne_zero) 5
    exact (Nat.dvd_add_right hgN).1 hgF
  have g2 : Nat.Coprime L (Nat.fib k) := by
    have ha : Nat.gcd L (Nat.fib k) ∣ L ^ 2 :=
      Dvd.dvd.pow (Nat.gcd_dvd_left _ _) two_ne_zero
    have hb : Nat.gcd L (Nat.fib k) ∣ L ^ 2 + 1 := by
      rw [hN]; exact Dvd.dvd.trans (Nat.gcd_dvd_right _ _) hk
    exact Nat.dvd_one.1 ((Nat.dvd_add_right ha).1 hb)
  have g3 : Nat.gcd (Nat.fib k) (Nat.fib (2 * n)) ∣ 3 := by
    rw [h2n, Nat.Coprime.gcd_mul_right_cancel_right F g2]; exact g1
  rw [← Nat.fib_gcd] at g3
  have g5 : Nat.gcd k (2 * n) ∣ 2 := by
    have hpos : 0 < Nat.gcd k (2 * n) := Nat.gcd_pos_of_pos_right _ (by omega)
    have hd4 : Nat.gcd k (2 * n) ∣ 2 * n := Nat.gcd_dvd_right _ _
    generalize Nat.gcd k (2 * n) = g at g3 hpos hd4
    have hle : g ≤ 4 := by
      by_contra hgt
      have h5' : Nat.fib 5 ≤ Nat.fib g := Nat.fib_mono (by omega)
      have h3' := Nat.le_of_dvd (by norm_num) g3
      have : Nat.fib 5 = 5 := by decide
      omega
    interval_cases g
    · exact one_dvd 2
    · exact dvd_refl 2
    · exact absurd g3 (by decide)
    · obtain ⟨t, ht⟩ := hodd
      omega
  have g6 : Nat.fib k ∣ Nat.fib (6 * n) := by
    have hcast : (luc (2 * n) : ZMod N) = 1 := by
      rw [hluc]
      have : L ^ 2 + 2 = N + 1 := by omega
      rw [this]; push_cast; rw [ZMod.natCast_self]; ring
    have h0 := fib6 (ZMod N) n hn hcast
    exact Dvd.dvd.trans hk ((ZMod.natCast_eq_zero_iff _ _).1 h0)
  have hNpos : 0 < N := by omega
  by_cases hk3 : k < 3
  · interval_cases k
    · rw [Nat.fib_zero] at hk
      have := Nat.eq_zero_of_zero_dvd hk
      omega
    · left; decide
    · left; decide
  · have hk6 : k ∣ 6 * n := by
      have hg : Nat.fib (Nat.gcd k (6 * n)) = Nat.fib k := by
        rw [Nat.fib_gcd]; exact Nat.gcd_eq_left g6
      have hjk : Nat.gcd k (6 * n) ∣ k := Nat.gcd_dvd_left _ _
      have hjle : Nat.gcd k (6 * n) ≤ k := Nat.le_of_dvd (by omega) hjk
      have hjeq : Nat.gcd k (6 * n) = k := by
        by_contra hne
        have hlt : Nat.gcd k (6 * n) ≤ k - 1 := by omega
        have h1 : Nat.fib (Nat.gcd k (6 * n)) ≤ Nat.fib (k - 1) := Nat.fib_mono hlt
        have h2 : Nat.fib (k - 1) < Nat.fib (k - 1 + 1) := Nat.fib_lt_fib_succ (by omega)
        have e : k - 1 + 1 = k := by omega
        rw [e] at h2
        omega
      rw [← hjeq]; exact Nat.gcd_dvd_right _ _
    have hk6' : k ∣ 6 := by
      have e : 6 * n = 3 * (2 * n) := by ring
      rw [e] at hk6
      have hgpos : 0 < Nat.gcd k (2 * n) := Nat.gcd_pos_of_pos_right _ (by omega)
      obtain ⟨k', m', hcop, hk', hm'⟩ := Nat.exists_coprime k (2 * n)
      rw [hm'] at hk6
      have h1 : k' * Nat.gcd k (2 * n) ∣ (3 * m') * Nat.gcd k (2 * n) := by
        rw [← hk', mul_assoc]; exact hk6
      have h2 : k' ∣ 3 * m' := Nat.dvd_of_mul_dvd_mul_right hgpos h1
      have h3 : k' ∣ 3 := Nat.Coprime.dvd_of_dvd_mul_right hcop h2
      rw [hk']
      exact Nat.mul_dvd_mul h3 g5
    have hle : k ≤ 6 := Nat.le_of_dvd (by norm_num) hk6'
    interval_cases k
    · right; decide
    · exact absurd hk6' (by decide)
    · exact absurd hk6' (by decide)
    · exfalso
      have h8 : Nat.fib 6 = 8 := by decide
      rw [h8] at hk
      have h4 : 4 ∣ L ^ 2 + 1 := by rw [hN]; exact Dvd.dvd.trans (by decide) hk
      have hm : (L ^ 2 + 1) % 4 = ((L % 4) ^ 2 + 1) % 4 := by
        simp [Nat.add_mod, Nat.pow_mod]
      have hlt : L % 4 < 4 := Nat.mod_lt _ (by norm_num)
      have h0 : (L ^ 2 + 1) % 4 = 0 := Nat.mod_eq_zero_of_dvd h4
      rw [hm] at h0
      interval_cases (L % 4) <;> omega

lemma count_one (n : ℕ) (hodd : Odd n) (hev : lucas n % 2 = 0) : a n = 1 := by
  unfold a
  have hS : {d : ℕ | d ∣ lucas n ^ 2 + 1 ∧ ∃ k : ℕ, Nat.fib k = d} = {1} := by
    ext d
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hd, k, rfl⟩
      rcases fib_div n k hodd hd with h | h
      · exact h
      · exfalso
        rw [h] at hd
        have h2 : (lucas n ^ 2 + 1) % 2 = 1 := by
          have : (lucas n ^ 2 + 1) % 2 = ((lucas n % 2) ^ 2 + 1) % 2 := by
            simp [Nat.add_mod, Nat.pow_mod]
          rw [this, hev]; norm_num
        omega
    · rintro rfl
      exact ⟨one_dvd _, 1, by decide⟩
  rw [hS, Set.ncard_singleton]

lemma count_two (n : ℕ) (hodd : Odd n) (hod : lucas n % 2 = 1) : a n = 2 := by
  unfold a
  have hS : {d : ℕ | d ∣ lucas n ^ 2 + 1 ∧ ∃ k : ℕ, Nat.fib k = d} = {1, 2} := by
    ext d
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hd, k, rfl⟩
      exact fib_div n k hodd hd
    · rintro (rfl | rfl)
      · exact ⟨one_dvd _, 1, by decide⟩
      · refine ⟨?_, 3, by decide⟩
        have h2 : (lucas n ^ 2 + 1) % 2 = 0 := by
          have : (lucas n ^ 2 + 1) % 2 = ((lucas n % 2) ^ 2 + 1) % 2 := by
            simp [Nat.add_mod, Nat.pow_mod]
          rw [this, hod]; norm_num
        exact Nat.dvd_of_mod_eq_zero h2
  rw [hS, Set.ncard_pair (by norm_num)]

theorem main' (n : ℕ) : a (6 * n + 3) = 1 ∧ a (6 * n + 1) = 2 ∧ a (6 * n + 5) = 2 := by
  have p1 := lucas_par (2 * n + 1)
  have p0 := lucas_par (2 * n)
  have q3 : lucas (6 * n + 3) % 2 = 0 := by
    have h := p1.1
    rwa [show 3 * (2 * n + 1) = 6 * n + 3 by ring] at h
  have q5 : lucas (6 * n + 5) % 2 = 1 := by
    have h := p1.2.2
    rwa [show 3 * (2 * n + 1) + 2 = 6 * n + 5 by ring] at h
  have q1 : lucas (6 * n + 1) % 2 = 1 := by
    have h := p0.2.1
    rwa [show 3 * (2 * n) + 1 = 6 * n + 1 by ring] at h
  exact ⟨count_one _ ⟨3 * n + 1, by ring⟩ q3, count_two _ ⟨3 * n, by ring⟩ q1,
    count_two _ ⟨3 * n + 2, by ring⟩ q5⟩

end OMA.A339669

theorem OMA.solution : type_of% @OMA.S_oeis_a339669.main :=
  fun n => OMA.A339669.main' n
