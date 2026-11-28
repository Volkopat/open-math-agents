import OMAStatements.S_oeis_a132634
import Mathlib

-- Problem: A132634: a(n) = Fibonacci(n) mod n^2.
-- Upstream: formal-conjectures statements/oeis-a132634.lean:0 (declaration OMA.S_oeis_a132634.main)
-- Credit: @npnelson (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- Proof (following Marques, Fibonacci Quart. 50 (2012), Prop. 4.2), self-contained over Mathlib.
-- 1. apparition: an odd prime p other than 5 divides F(p-1) or F(p+1). Shown with 2x2 matrices
--    over ZMod p: for Q = [[1,1],[1,0]] one has (2Q-1)^2 = 5, so Frobenius and Euler's criterion
--    give 2Q^p - 1 = +-(2Q - 1).
-- 2. D5, D3, D2: 5^(e+1) | F(n) forces 5^(e+1) | n; for 4 | n, 3^(e+2) | F(n) forces 3^(e+1) | n;
--    for 12 | n, 2^(e+3) | F(n) forces 2^(e+1) | n. These use the formulas for F(5m), F(3m), F(2m)
--    in terms of F(m) and F(m+1), and gcd(F(a), F(b)) = F(gcd(a, b)) for the base cases.
-- 3. If n > 1 and n^2 | F(n), the least prime factor of n is 2 (not 5, by D5; otherwise it would
--    divide F(1)), hence 12 | n, and 8, 9, 5 do not divide n. Writing n = 12 m, the least prime
--    factor q of m would divide F(d) for some d | 12, so q | 144, which is impossible.

namespace Fib132634Proof
lemma fib_add_int (m n : ℕ) : (Nat.fib (m + n) : ℤ) =
    Nat.fib m * Nat.fib (n + 1) + (Nat.fib (m + 1) - Nat.fib m) * Nat.fib n := by
  cases n with
  | zero => simp
  | succ k =>
    have h1 : Nat.fib (m + (k + 1)) =
        Nat.fib m * Nat.fib k + Nat.fib (m + 1) * Nat.fib (k + 1) := by
      rw [← Nat.add_assoc]; exact Nat.fib_add m k
    have h2 : Nat.fib (k + 1 + 1) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two
    rw [h1, h2]; push_cast; ring

lemma fib_succ_add_int (m n : ℕ) : (Nat.fib (m + n + 1) : ℤ) =
    Nat.fib m * Nat.fib n + Nat.fib (m + 1) * Nat.fib (n + 1) := by
  rw [Nat.fib_add]; push_cast; ring

lemma cassini_sq (m : ℕ) :
    ((Nat.fib (m + 1) : ℤ) ^ 2 - Nat.fib (m + 1) * Nat.fib m - (Nat.fib m : ℤ) ^ 2) ^ 2 = 1 := by
  induction m with
  | zero => simp
  | succ k ih =>
    have h2 : Nat.fib (k + 1 + 1) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two
    rw [h2]; push_cast
    have h : ((Nat.fib k : ℤ) + Nat.fib (k + 1)) ^ 2
        - ((Nat.fib k : ℤ) + Nat.fib (k + 1)) * Nat.fib (k + 1) - (Nat.fib (k + 1) : ℤ) ^ 2
        = -((Nat.fib (k + 1) : ℤ) ^ 2 - Nat.fib (k + 1) * Nat.fib k - (Nat.fib k : ℤ) ^ 2) := by
      ring
    rw [h, neg_sq]; exact ih

lemma fib_two_int (m : ℕ) : (Nat.fib (m + m) : ℤ) =
    Nat.fib m * (2 * Nat.fib (m + 1) - Nat.fib m) := by
  rw [fib_add_int]; ring

lemma fib_two_succ_int (m : ℕ) : (Nat.fib (m + m + 1) : ℤ) =
    (Nat.fib m : ℤ) ^ 2 + (Nat.fib (m + 1) : ℤ) ^ 2 := by
  rw [fib_succ_add_int]; ring

lemma fib_three_int (m : ℕ) : (Nat.fib (m + m + m) : ℤ) =
    Nat.fib m * (3 * (Nat.fib (m + 1) : ℤ) ^ 2 - 3 * Nat.fib m * Nat.fib (m + 1)
      + 2 * (Nat.fib m : ℤ) ^ 2) := by
  rw [fib_add_int (m + m) m, fib_two_int, fib_two_succ_int]; ring

lemma fib_five_int (m : ℕ) : (Nat.fib (m + m + m + (m + m)) : ℤ) =
    Nat.fib m * (5 * (5 * (Nat.fib m : ℤ) ^ 4
      + 5 * ((Nat.fib (m + 1) : ℤ) ^ 2 - Nat.fib (m + 1) * Nat.fib m - (Nat.fib m : ℤ) ^ 2)
          * (Nat.fib m : ℤ) ^ 2
      + ((Nat.fib (m + 1) : ℤ) ^ 2 - Nat.fib (m + 1) * Nat.fib m - (Nat.fib m : ℤ) ^ 2) ^ 2)) := by
  rw [fib_add_int (m + m + m) (m + m), fib_three_int, fib_succ_add_int (m + m) m, fib_two_int,
    fib_two_succ_int]
  ring

lemma five_dvd_fib {n : ℕ} (h : 5 ∣ Nat.fib n) : 5 ∣ n := by
  have hg : 5 ∣ Nat.fib (Nat.gcd n 5) := by
    rw [Nat.fib_gcd]; exact Nat.dvd_gcd h (by norm_num)
  rcases (Nat.dvd_prime Nat.prime_five).mp (Nat.gcd_dvd_right n 5) with h1 | h5
  · rw [h1] at hg; norm_num at hg
  · rw [← h5]; exact Nat.gcd_dvd_left n 5

lemma D5 : ∀ e n : ℕ, 5 ^ (e + 1) ∣ Nat.fib n → 5 ^ (e + 1) ∣ n
  | 0, n, hF => by simpa using five_dvd_fib (by simpa using hF)
  | (e + 1), n, hF => by
    have h1 : 5 ^ (e + 1) ∣ n := D5 e n (dvd_trans (pow_dvd_pow 5 (by omega)) hF)
    have h5 : 5 ∣ n := dvd_trans (dvd_pow_self 5 (by omega)) h1
    obtain ⟨m, rfl⟩ := h5
    have hm : 5 * m = m + m + m + (m + m) := by ring
    have hc := cassini_sq m
    have hfib := fib_five_int m
    rw [← hm, hc] at hfib
    have hZ : (5 : ℤ) ^ (e + 1 + 1) ∣ (Nat.fib (5 * m) : ℤ) := by exact_mod_cast hF
    rw [hfib] at hZ
    have hU : IsCoprime ((5 : ℤ) ^ (e + 1)) (5 * (Nat.fib m : ℤ) ^ 4
        + 5 * ((Nat.fib (m + 1) : ℤ) ^ 2 - Nat.fib (m + 1) * Nat.fib m - (Nat.fib m : ℤ) ^ 2)
          * (Nat.fib m : ℤ) ^ 2 + 1) := by
      apply IsCoprime.pow_left
      exact ⟨-((Nat.fib m : ℤ) ^ 4
        + ((Nat.fib (m + 1) : ℤ) ^ 2 - Nat.fib (m + 1) * Nat.fib m - (Nat.fib m : ℤ) ^ 2)
          * (Nat.fib m : ℤ) ^ 2), 1, by ring⟩
    have h2 : (5 : ℤ) ^ (e + 1) ∣ (Nat.fib m : ℤ) * (5 * (Nat.fib m : ℤ) ^ 4
        + 5 * ((Nat.fib (m + 1) : ℤ) ^ 2 - Nat.fib (m + 1) * Nat.fib m - (Nat.fib m : ℤ) ^ 2)
          * (Nat.fib m : ℤ) ^ 2 + 1) := by
      refine (mul_dvd_mul_iff_left (by norm_num : (5 : ℤ) ≠ 0)).mp ?_
      have e1 : (5 : ℤ) * 5 ^ (e + 1) = 5 ^ (e + 1 + 1) := by ring
      rw [e1]
      refine hZ.trans (dvd_of_eq ?_)
      ring
    have h3 : (5 : ℤ) ^ (e + 1) ∣ (Nat.fib m : ℤ) := hU.dvd_of_dvd_mul_right h2
    have h4 : 5 ^ (e + 1) ∣ Nat.fib m := by exact_mod_cast h3
    have h6 := D5 e m h4
    rw [pow_succ, mul_comm]
    exact Nat.mul_dvd_mul_left 5 h6

lemma nine_dvd_fib {n : ℕ} (h : 9 ∣ Nat.fib n) : 3 ∣ n := by
  have hg : 9 ∣ Nat.fib (Nat.gcd n 12) := by
    rw [Nat.fib_gcd]; exact Nat.dvd_gcd h (by norm_num)
  have hmem : Nat.gcd n 12 ∈ Nat.divisors 12 :=
    Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right n 12, by norm_num⟩
  have key : ∀ d ∈ Nat.divisors 12, 9 ∣ Nat.fib d → d = 12 := by decide
  have h12 := key _ hmem hg
  have h : 12 ∣ n := h12 ▸ Nat.gcd_dvd_left n 12
  exact dvd_trans (by norm_num) h

lemma D3 : ∀ e n : ℕ, 4 ∣ n → 3 ^ (e + 2) ∣ Nat.fib n → 3 ^ (e + 1) ∣ n
  | 0, n, _, hF => by simpa using nine_dvd_fib (by simpa using hF)
  | (e + 1), n, h4, hF => by
    have h1 : 3 ^ (e + 1) ∣ n := D3 e n h4 (dvd_trans (pow_dvd_pow 3 (by omega)) hF)
    have h3 : 3 ∣ n := dvd_trans (dvd_pow_self 3 (by omega)) h1
    have h12 : 4 * 3 ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h4 h3
    obtain ⟨t, rfl⟩ := h12
    have hn : 4 * 3 * t = 4 * t + 4 * t + 4 * t := by ring
    have h3n : 3 ∣ Nat.fib (4 * t) := by
      have h := Nat.fib_dvd 4 (4 * t) (Dvd.intro t rfl)
      have h4' : Nat.fib 4 = 3 := by norm_num
      rwa [h4'] at h
    have hcopN : Nat.Coprime 3 (Nat.fib (4 * t + 1)) :=
      Nat.Coprime.coprime_dvd_left h3n (Nat.fib_coprime_fib_succ (4 * t))
    have hcop : IsCoprime (3 : ℤ) (Nat.fib (4 * t + 1) : ℤ) := by
      exact_mod_cast Nat.isCoprime_iff_coprime.mpr hcopN
    obtain ⟨a', ha'⟩ : (3 : ℤ) ∣ (Nat.fib (4 * t) : ℤ) := by exact_mod_cast h3n
    have hfib := fib_three_int (4 * t)
    rw [← hn] at hfib
    have hZ : (3 : ℤ) ^ (e + 1 + 2) ∣ (Nat.fib (4 * 3 * t) : ℤ) := by exact_mod_cast hF
    rw [hfib] at hZ
    have hV : IsCoprime ((3 : ℤ) ^ (e + 2))
        ((Nat.fib (4 * t + 1) : ℤ) ^ 2 + 3 * (-a' * Nat.fib (4 * t + 1) + 2 * a' ^ 2)) :=
      IsCoprime.pow_left ((hcop.pow_right).add_mul_left_right _)
    have h2 : (3 : ℤ) ^ (e + 2) ∣ (Nat.fib (4 * t) : ℤ)
        * ((Nat.fib (4 * t + 1) : ℤ) ^ 2 + 3 * (-a' * Nat.fib (4 * t + 1) + 2 * a' ^ 2)) := by
      refine (mul_dvd_mul_iff_left (by norm_num : (3 : ℤ) ≠ 0)).mp ?_
      have e1 : (3 : ℤ) * 3 ^ (e + 2) = 3 ^ (e + 1 + 2) := by ring
      rw [e1]
      refine hZ.trans (dvd_of_eq ?_)
      rw [ha']; ring
    have h3' : (3 : ℤ) ^ (e + 2) ∣ (Nat.fib (4 * t) : ℤ) := hV.dvd_of_dvd_mul_right h2
    have h4' : 3 ^ (e + 2) ∣ Nat.fib (4 * t) := by exact_mod_cast h3'
    have h6 := D3 e (4 * t) (Dvd.intro t rfl) h4'
    have hn' : 4 * 3 * t = 3 * (4 * t) := by ring
    rw [hn', pow_succ, mul_comm]
    exact Nat.mul_dvd_mul_left 3 h6

lemma thirtytwo_dvd_fib {n : ℕ} (h : 32 ∣ Nat.fib n) : 8 ∣ n := by
  have hg : 32 ∣ Nat.fib (Nat.gcd n 24) := by
    rw [Nat.fib_gcd]; exact Nat.dvd_gcd h (by norm_num)
  have hmem : Nat.gcd n 24 ∈ Nat.divisors 24 :=
    Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right n 24, by norm_num⟩
  have key : ∀ d ∈ Nat.divisors 24, 32 ∣ Nat.fib d → d = 24 := by decide
  have h24 := key _ hmem hg
  have h : 24 ∣ n := h24 ▸ Nat.gcd_dvd_left n 24
  exact dvd_trans (by norm_num) h

lemma D2 : ∀ e n : ℕ, 12 ∣ n → 2 ^ (e + 3) ∣ Nat.fib n → 2 ^ (e + 1) ∣ n
  | 0, n, h12, _ => dvd_trans (by norm_num) h12
  | 1, n, h12, _ => dvd_trans (by norm_num) h12
  | 2, n, _, hF => by simpa using thirtytwo_dvd_fib (by simpa using hF)
  | (e + 3), n, h12, hF => by
    have h1 : 2 ^ (e + 2 + 1) ∣ n :=
      D2 (e + 2) n h12 (dvd_trans (pow_dvd_pow 2 (by omega)) hF)
    have h8 : 2 ^ 3 ∣ n := dvd_trans (pow_dvd_pow 2 (by omega)) h1
    have h24 : 24 ∣ n := by
      have h := Nat.lcm_dvd h8 h12
      have hl : Nat.lcm (2 ^ 3) 12 = 24 := by norm_num
      rwa [hl] at h
    obtain ⟨t, rfl⟩ := h24
    have hn : 24 * t = 2 * (12 * t) := by ring
    have hfm := Nat.fib_two_mul (12 * t)
    have h144 : 144 ∣ Nat.fib (12 * t) := by
      have h := Nat.fib_dvd 12 (12 * t) (Dvd.intro t rfl)
      have h12' : Nat.fib 12 = 144 := by norm_num
      rwa [h12'] at h
    obtain ⟨a', ha'⟩ : 4 ∣ Nat.fib (12 * t) := dvd_trans (by norm_num) h144
    have hodd : ¬ 2 ∣ Nat.fib (12 * t + 1) := by
      intro h2
      have hc : Nat.gcd (Nat.fib (12 * t)) (Nat.fib (12 * t + 1)) = 1 :=
        Nat.fib_coprime_fib_succ (12 * t)
      have h := Nat.dvd_gcd (dvd_trans (by norm_num : 2 ∣ 144) h144) h2
      rw [hc] at h
      omega
    have hle : Nat.fib (12 * t) ≤ Nat.fib (12 * t + 1) := Nat.fib_le_fib_succ
    have hW : 2 * Nat.fib (12 * t + 1) - Nat.fib (12 * t)
        = 2 * (Nat.fib (12 * t + 1) - 2 * a') := by omega
    have hWodd : ¬ 2 ∣ (Nat.fib (12 * t + 1) - 2 * a') := by omega
    rw [hn, hfm, hW] at hF
    have h2' : 2 ^ (e + 2 + 3) ∣ Nat.fib (12 * t) * (Nat.fib (12 * t + 1) - 2 * a') := by
      refine (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mp ?_
      have e1 : 2 * 2 ^ (e + 2 + 3) = 2 ^ (e + 3 + 3) := by ring
      rw [e1]
      refine hF.trans (dvd_of_eq ?_)
      ring
    have hcop : Nat.Coprime (2 ^ (e + 2 + 3)) (Nat.fib (12 * t + 1) - 2 * a') :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hWodd)
    have h3 : 2 ^ (e + 2 + 3) ∣ Nat.fib (12 * t) := hcop.dvd_of_dvd_mul_right h2'
    have h4 := D2 (e + 2) (12 * t) (Dvd.intro t rfl) h3
    rw [hn, pow_succ, mul_comm]
    exact Nat.mul_dvd_mul_left 2 h4

lemma Qpow (K : Type) [CommRing K] (n : ℕ) :
    (!![(1 : K), 1; 1, 0]) ^ (n + 1) =
      !![(Nat.fib (n + 2) : K), (Nat.fib (n + 1) : K);
         (Nat.fib (n + 1) : K), (Nat.fib n : K)] := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h3 : Nat.fib (k + 1 + 2) = Nat.fib (k + 1) + Nat.fib (k + 2) := Nat.fib_add_two
    have h2 : Nat.fib (k + 2) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two
    have h1 : k + 1 + 1 = k + 2 := rfl
    rw [pow_succ, ih, Matrix.mul_fin_two, h3, h1, h2]
    push_cast
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring

lemma apparition {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h5 : p ≠ 5) :
    p ∣ Nat.fib (p - 1) ∨ p ∣ Nat.fib (p + 1) := by
  have : Fact p.Prime := Fact.mk hp
  have hA : (!![(1 : ZMod p), 2; 2, -1] : Matrix (Fin 2) (Fin 2) (ZMod p))
      = (2 : ZMod p) • (!![(1 : ZMod p), 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) - 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
  have hAA : (!![(1 : ZMod p), 2; 2, -1] : Matrix (Fin 2) (Fin 2) (ZMod p))
      * !![(1 : ZMod p), 2; 2, -1] = (5 : ZMod p) • (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
    rw [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
  obtain ⟨k, hk⟩ : ∃ k, p = 2 * k + 1 := by
    rcases hp.eq_two_or_odd' with h | h
    · exact absurd h h2
    · exact h
  have hApow : (!![(1 : ZMod p), 2; 2, -1] : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ p
      = ((5 : ZMod p) ^ k) • !![(1 : ZMod p), 2; 2, -1] := by
    have hpk : (!![(1 : ZMod p), 2; 2, -1] : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ p
        = (!![(1 : ZMod p), 2; 2, -1] : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ (2 * k + 1) :=
      congrArg (fun n => (!![(1 : ZMod p), 2; 2, -1] : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ n) hk
    rw [hpk, pow_succ, pow_mul, pow_two, hAA, smul_pow, one_pow, smul_mul_assoc, one_mul]
  have hFrob : (!![(1 : ZMod p), 2; 2, -1] : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ p
      = (2 : ZMod p) • (!![(1 : ZMod p), 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ p - 1 := by
    rw [hA, sub_pow_char_of_commute p (Commute.one_right _), one_pow, smul_pow, ZMod.pow_card]
  have h5ne : (5 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((5 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact h5 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h')
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
  have hk' : k = p / 2 := by omega
  have hEuler : (5 : ZMod p) ^ k = 1 ∨ (5 : ZMod p) ^ k = -1 := by
    rw [hk']; exact ZMod.pow_div_two_eq_neg_one_or_one p h5ne
  have hQp : (!![(1 : ZMod p), 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ p
      = !![(Nat.fib (p + 1) : ZMod p), (Nat.fib p : ZMod p);
           (Nat.fib p : ZMod p), (Nat.fib (p - 1) : ZMod p)] := by
    have h := Qpow (ZMod p) (p - 1)
    have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_le
    have hp2 : p - 1 + 2 = p + 1 := by omega
    rw [hp1, hp2] at h
    exact h
  have heq := hFrob.symm.trans hApow
  rw [hQp] at heq
  rcases hEuler with he | he
  · left
    rw [he, one_smul] at heq
    have h11 := congrFun (congrFun heq 1) 1
    simp at h11
    have h0 : (Nat.fib (p - 1) : ZMod p) = 0 := by
      rcases h11 with h | h
      · exact absurd h h2ne
      · exact h
    exact (ZMod.natCast_eq_zero_iff _ _).mp h0
  · right
    rw [he, neg_one_smul] at heq
    have h00 := congrFun (congrFun heq 0) 0
    simp at h00
    have h0 : (Nat.fib (p + 1) : ZMod p) = 0 := by
      rcases h00 with h | h
      · exact absurd h h2ne
      · exact h
    exact (ZMod.natCast_eq_zero_iff _ _).mp h0

lemma key {n m : ℕ} (hm : 1 < m) (hq2 : m.minFac ≠ 2) (hq5 : m.minFac ≠ 5)
    (hF : m.minFac ∣ Nat.fib n) :
    ∃ d, d ∣ n ∧ Nat.Coprime d m ∧ m.minFac ∣ Nat.fib d := by
  have hq : (m.minFac).Prime := Nat.minFac_prime (by omega)
  have hq3 : 3 ≤ m.minFac := by
    have := hq.two_le
    omega
  rcases apparition hq hq2 hq5 with h | h
  · refine ⟨Nat.gcd n (m.minFac - 1), Nat.gcd_dvd_left _ _, ?_, ?_⟩
    · apply Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right n (m.minFac - 1))
      apply Nat.coprime_of_dvd
      intro r hr hr1 hrm
      have h1 : m.minFac ≤ r := Nat.minFac_le_of_dvd hr.two_le hrm
      have h2 : r ≤ m.minFac - 1 := Nat.le_of_dvd (by omega) hr1
      omega
    · rw [Nat.fib_gcd]; exact Nat.dvd_gcd hF h
  · refine ⟨Nat.gcd n (m.minFac + 1), Nat.gcd_dvd_left _ _, ?_, ?_⟩
    · apply Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right n (m.minFac + 1))
      apply Nat.coprime_of_dvd
      intro r hr hr1 hrm
      have h1 : m.minFac ≤ r := Nat.minFac_le_of_dvd hr.two_le hrm
      have h2 : r ≤ m.minFac + 1 := Nat.le_of_dvd (by omega) hr1
      have hqodd : m.minFac % 2 = 1 := by
        rcases hq.eq_two_or_odd with h | h
        · exact absurd h hq2
        · exact h
      rcases (by omega : r = m.minFac ∨ r = m.minFac + 1) with hr' | hr'
      · rw [hr'] at hr1
        have h1' : m.minFac ∣ 1 := (Nat.dvd_add_right (dvd_refl _)).mp hr1
        have := Nat.dvd_one.mp h1'
        omega
      · have h2' : 2 ∣ r := by omega
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hr).mp h2'
        omega
    · rw [Nat.fib_gcd]; exact Nat.dvd_gcd hF h

lemma no_high (p c : ℕ) (hp : p.Prime) (Cond : ℕ → Prop)
    (H : ∀ e n, Cond n → p ^ (e + c + 1) ∣ Nat.fib n → p ^ (e + 1) ∣ n)
    {n : ℕ} (hn : n ≠ 0) (hC : Cond n) (hF : n ^ 2 ∣ Nat.fib n) : ¬ p ^ (c + 1) ∣ n := by
  intro hdiv
  obtain ⟨k, m, hm, hnk⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
  have hk : c + 1 ≤ k := by
    by_contra hlt
    have h1 : p ^ (k + 1) ∣ p ^ k * m := hnk ▸ dvd_trans (pow_dvd_pow p (by omega)) hdiv
    rw [pow_succ] at h1
    exact hm ((Nat.mul_dvd_mul_iff_left (pow_pos hp.pos k)).mp h1)
  have h1 : p ^ (k + c + 1) ∣ Nat.fib n := by
    refine dvd_trans ?_ hF
    rw [hnk, mul_pow, ← pow_mul]
    exact dvd_mul_of_dvd_left (pow_dvd_pow p (by omega)) _
  have h2 : p ^ (k + 1) ∣ p ^ k * m := hnk ▸ H k n hC h1
  rw [pow_succ] at h2
  exact hm ((Nat.mul_dvd_mul_iff_left (pow_pos hp.pos k)).mp h2)

theorem main_dir {n : ℕ} (hn : 1 ≤ n) (hF : n ^ 2 ∣ Nat.fib n) : n = 1 ∨ n = 12 := by
  by_contra hcon
  have hn1 : n ≠ 1 := fun h => hcon (Or.inl h)
  have hn12 : n ≠ 12 := fun h => hcon (Or.inr h)
  have hn2 : 1 < n := by omega
  have hnF : n ∣ Nat.fib n := dvd_trans (dvd_pow_self n two_ne_zero) hF
  have hqF : n.minFac ∣ Nat.fib n := dvd_trans (Nat.minFac_dvd n) hnF
  have h5 : ¬ 5 ∣ n := by
    have h := no_high 5 0 Nat.prime_five (fun _ => True) (fun e n _ h => D5 e n h)
      (by omega) trivial hF
    simpa using h
  have hq : n.minFac = 2 := by
    by_contra hq2
    have hq5 : n.minFac ≠ 5 := fun h => h5 (h ▸ Nat.minFac_dvd n)
    obtain ⟨d, hdn, hcop, hqd⟩ := key hn2 hq2 hq5 hqF
    have hd1 : d = 1 := Nat.Coprime.eq_one_of_dvd hcop hdn
    rw [hd1] at hqd
    have h1 : n.minFac = 1 := Nat.dvd_one.mp (by simpa using hqd)
    exact (Nat.minFac_prime (by omega)).one_lt.ne' h1
  have h2n : 2 ∣ n := hq ▸ Nat.minFac_dvd n
  have h3n : 3 ∣ n := by
    have h2F : 2 ∣ Nat.fib n := dvd_trans h2n hnF
    have hg : 2 ∣ Nat.fib (Nat.gcd n 3) := by
      rw [Nat.fib_gcd]; exact Nat.dvd_gcd h2F (by norm_num)
    rcases (Nat.dvd_prime Nat.prime_three).mp (Nat.gcd_dvd_right n 3) with h1 | h3
    · rw [h1] at hg; norm_num at hg
    · rw [← h3]; exact Nat.gcd_dvd_left n 3
  have h4n : 4 ∣ n := by
    have h3F : 3 ∣ Nat.fib n := dvd_trans h3n hnF
    have hg : 3 ∣ Nat.fib (Nat.gcd n 4) := by
      rw [Nat.fib_gcd]; exact Nat.dvd_gcd h3F (by norm_num)
    have hmem : Nat.gcd n 4 ∈ Nat.divisors 4 :=
      Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right n 4, by norm_num⟩
    have hkey : ∀ d ∈ Nat.divisors 4, 3 ∣ Nat.fib d → d = 4 := by decide
    have h4 := hkey _ hmem hg
    exact h4 ▸ Nat.gcd_dvd_left n 4
  have h12 : 4 * 3 ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h4n h3n
  have h12' : 12 ∣ n := h12
  have h8 : ¬ 8 ∣ n := by
    have h := no_high 2 2 Nat.prime_two (fun n => 12 ∣ n) (fun e n hc h => D2 e n hc h)
      (by omega) h12' hF
    simpa using h
  have h9 : ¬ 9 ∣ n := by
    have h := no_high 3 1 Nat.prime_three (fun n => 4 ∣ n) (fun e n hc h => D3 e n hc h)
      (by omega) h4n hF
    simpa using h
  obtain ⟨m, rfl⟩ := h12'
  have hm1 : 1 < m := by omega
  have hm2 : ¬ 2 ∣ m := fun h => h8 (by omega)
  have hm3 : ¬ 3 ∣ m := fun h => h9 (by omega)
  have hm5 : ¬ 5 ∣ m := fun h => h5 (Dvd.dvd.mul_left h 12)
  have hq2 : m.minFac ≠ 2 := fun h => hm2 (h ▸ Nat.minFac_dvd m)
  have hq5 : m.minFac ≠ 5 := fun h => hm5 (h ▸ Nat.minFac_dvd m)
  have hq3 : m.minFac ≠ 3 := fun h => hm3 (h ▸ Nat.minFac_dvd m)
  have hqF' : m.minFac ∣ Nat.fib (12 * m) :=
    dvd_trans (dvd_trans (Nat.minFac_dvd m) (Dvd.intro_left 12 rfl)) hnF
  obtain ⟨d, hdn, hcop, hqd⟩ := key hm1 hq2 hq5 hqF'
  have hd12 : d ∣ 12 := hcop.dvd_of_dvd_mul_right hdn
  have hf12 : Nat.fib 12 = 2 ^ 4 * 3 ^ 2 := by norm_num
  have h144 : m.minFac ∣ 2 ^ 4 * 3 ^ 2 := hf12 ▸ dvd_trans hqd (Nat.fib_dvd d 12 hd12)
  have hqp : (m.minFac).Prime := Nat.minFac_prime (by omega)
  rcases (Nat.Prime.dvd_mul hqp).mp h144 with h | h
  · exact hq2 ((Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).mp (hqp.dvd_of_dvd_pow h))
  · exact hq3 ((Nat.prime_dvd_prime_iff_eq hqp Nat.prime_three).mp (hqp.dvd_of_dvd_pow h))

end Fib132634Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a132634.main := by
  intro n hn
  constructor
  · intro h
    exact Fib132634Proof.main_dir hn (Nat.dvd_of_mod_eq_zero h)
  · rintro (rfl | rfl) <;> decide
