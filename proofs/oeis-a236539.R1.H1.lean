import OMAReductions.R_oeis_a236539_R1
import Mathlib

/-!
Step oeis-a236539.R1.H1: an integer-area triangle with two equal shorter Fibonacci sides is (5, 5, 8).
Credit: @xor2k
Heron reduces the case to `fib m * L (m+3)` being a square (L the Lucas numbers), so `L (m+3)` is a
square or twice a square. Cohn's elementary argument (the identity `L (c+2b) + L c = L b * L (c+b)`
for even `b` and primes `p = 3 mod 4` dividing `L k`) leaves only `L 6 = 2 * 3^2`, i.e. (5, 5, 8).
-/

namespace OMA.StepCohnLucasSquares

open Real

def luc : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | (n+2) => luc (n+1) + luc n

theorem luc_add_two (n : ℕ) : luc (n+2) = luc (n+1) + luc n := rfl

theorem luc_real : ∀ n : ℕ, (luc n : ℝ) = goldenRatio ^ n + goldenConj ^ n
  | 0 => by norm_num [luc]
  | 1 => by
    have := goldenRatio_add_goldenConj
    simp only [luc, pow_one, Nat.cast_one]
    linarith
  | (n+2) => by
    rw [luc_add_two, Nat.cast_add, luc_real (n+1), luc_real n]
    linear_combination (-goldenRatio ^ n) * goldenRatio_sq - goldenConj ^ n * goldenConj_sq

theorem luc_T1 (c b : ℕ) (hb : b % 2 = 0) : luc (c + 2*b) + luc c = luc b * luc (c + b) := by
  have h : (goldenRatio * goldenConj) ^ b = 1 := by
    rw [goldenRatio_mul_goldenConj]
    obtain ⟨j, rfl⟩ : ∃ j, b = 2 * j := ⟨b / 2, by omega⟩
    rw [pow_mul]
    norm_num
  have : (luc (c + 2*b) : ℝ) + luc c = luc b * luc (c + b) := by
    rw [luc_real, luc_real, luc_real, luc_real]
    generalize goldenRatio = a at h ⊢
    generalize goldenConj = z at h ⊢
    linear_combination (-(a ^ c + z ^ c)) * h
  exact_mod_cast this

theorem luc_fib : ∀ n : ℕ, luc (n+1) = Nat.fib n + Nat.fib (n+2)
  | 0 => by decide
  | 1 => by decide
  | (n+2) => by
    show luc (n+3) = Nat.fib (n+2) + Nat.fib (n+4)
    have a : luc (n+3) = luc (n+2) + luc (n+1) := luc_add_two (n+1)
    have b : luc (n+2) = Nat.fib (n+1) + Nat.fib (n+3) := luc_fib (n+1)
    have c : luc (n+1) = Nat.fib n + Nat.fib (n+2) := luc_fib n
    have f2 : Nat.fib (n+2) = Nat.fib n + Nat.fib (n+1) := Nat.fib_add_two
    have f3 : Nat.fib (n+3) = Nat.fib (n+1) + Nat.fib (n+2) := Nat.fib_add_two
    have f4 : Nat.fib (n+4) = Nat.fib (n+2) + Nat.fib (n+3) := Nat.fib_add_two
    omega

theorem luc_fib_rel (m : ℕ) : luc (m+3) = 3 * Nat.fib m + 4 * Nat.fib (m+1) := by
  have b : luc (m+3) = Nat.fib (m+2) + Nat.fib (m+4) := luc_fib (m+2)
  have f2 : Nat.fib (m+2) = Nat.fib m + Nat.fib (m+1) := Nat.fib_add_two
  have f3 : Nat.fib (m+3) = Nat.fib (m+1) + Nat.fib (m+2) := Nat.fib_add_two
  have f4 : Nat.fib (m+4) = Nat.fib (m+2) + Nat.fib (m+3) := Nat.fib_add_two
  omega

theorem luc_step6 (n : ℕ) : luc (n+6) = 5 * luc n + 8 * luc (n+1) := by
  have h2 : luc (n+2) = luc (n+1) + luc n := luc_add_two n
  have h3 : luc (n+3) = luc (n+2) + luc (n+1) := luc_add_two (n+1)
  have h4 : luc (n+4) = luc (n+3) + luc (n+2) := luc_add_two (n+2)
  have h5 : luc (n+5) = luc (n+4) + luc (n+3) := luc_add_two (n+3)
  have h6 : luc (n+6) = luc (n+5) + luc (n+4) := luc_add_two (n+4)
  omega

theorem luc_step8 (n : ℕ) : luc (n+8) = 13 * luc n + 21 * luc (n+1) := by
  have h6 := luc_step6 n
  have h7 : luc (n+7) = 5 * luc (n+1) + 8 * luc (n+2) := luc_step6 (n+1)
  have h2 : luc (n+2) = luc (n+1) + luc n := luc_add_two n
  have h8 : luc (n+8) = luc (n+7) + luc (n+6) := luc_add_two (n+6)
  omega

theorem luc_step12 (n : ℕ) : luc (n+12) = 89 * luc n + 144 * luc (n+1) := by
  have h6 := luc_step6 n
  have h7 : luc (n+7) = 5 * luc (n+1) + 8 * luc (n+2) := luc_step6 (n+1)
  have h2 : luc (n+2) = luc (n+1) + luc n := luc_add_two n
  have a : luc (n+12) = 5 * luc (n+6) + 8 * luc (n+7) := luc_step6 (n+6)
  omega

theorem luc_mod4 (n : ℕ) : luc n % 4 = luc (n % 6) % 4 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 6
    · rw [Nat.mod_eq_of_lt hn]
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (by omega : 6 ≤ n)
      rw [Nat.add_comm 6 j, luc_step6, show (j + 6) % 6 = j % 6 by omega, ← ih j (by omega)]
      omega

theorem luc_mod3 (n : ℕ) : luc n % 3 = luc (n % 8) % 3 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 8
    · rw [Nat.mod_eq_of_lt hn]
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (by omega : 8 ≤ n)
      rw [Nat.add_comm 8 j, luc_step8, show (j + 8) % 8 = j % 8 by omega, ← ih j (by omega)]
      omega

theorem luc_mod8 (n : ℕ) : luc n % 8 = luc (n % 12) % 8 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 12
    · rw [Nat.mod_eq_of_lt hn]
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (by omega : 12 ≤ n)
      rw [Nat.add_comm 12 j, luc_step12, show (j + 12) % 12 = j % 12 by omega, ← ih j (by omega)]
      omega

theorem luc_k_mod4 (k : ℕ) (h2 : k % 2 = 0) (h3 : k % 3 ≠ 0) : luc k % 4 = 3 := by
  rw [luc_mod4]
  rcases (by omega : k % 6 = 2 ∨ k % 6 = 4) with h | h <;> rw [h] <;> decide

theorem luc_even_mod4 (n : ℕ) (h2 : n % 2 = 0) : luc n % 4 = 2 ∨ luc n % 4 = 3 := by
  rw [luc_mod4]
  rcases (by omega : n % 6 = 0 ∨ n % 6 = 2 ∨ n % 6 = 4) with h | h | h <;> rw [h] <;> decide

theorem luc_even_idx (n : ℕ) (h : luc n % 2 = 0) : n % 6 = 0 ∨ n % 6 = 3 := by
  have h4 := luc_mod4 n
  have : n % 6 < 6 := Nat.mod_lt _ (by norm_num)
  rcases (by omega : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5)
    with e | e | e | e | e | e <;> rw [e] at h4 <;> norm_num [luc] at h4 <;> omega

theorem luc_k_mod3 (k : ℕ) (h : k % 4 = 0) : luc k % 3 ≠ 0 := by
  rw [luc_mod3]
  rcases (by omega : k % 8 = 0 ∨ k % 8 = 4) with e | e <;> rw [e] <;> decide

theorem luc_odd_mod8 (n : ℕ) (h : n % 6 = 3) : luc n % 8 = 4 := by
  rw [luc_mod8]
  rcases (by omega : n % 12 = 3 ∨ n % 12 = 9) with e | e <;> rw [e] <;> decide

theorem prime_three_factor : ∀ a : ℕ, a % 4 = 3 →
    ∃ p, p.Prime ∧ p % 4 = 3 ∧ p ∣ a := by
  apply Nat.recOnMul
  · norm_num
  · norm_num
  · exact fun p hp h => ⟨p, hp, h, dvd_rfl⟩
  · intro a b ha hb hh
    have h : a % 4 = 3 ∨ b % 4 = 3 := by
      rw [Nat.mul_mod] at hh
      have aa := Nat.mod_lt a (by decide : 0 < 4)
      have bb := Nat.mod_lt b (by decide : 0 < 4)
      interval_cases a % 4 <;> interval_cases b % 4 <;> norm_num at *
    rcases h with h | h
    · obtain ⟨p, hp, he, hd⟩ := ha h
      exact ⟨p, hp, he, dvd_mul_of_dvd_left hd _⟩
    · obtain ⟨p, hp, he, hd⟩ := hb h
      exact ⟨p, hp, he, dvd_mul_of_dvd_right hd _⟩

theorem final_contra (M : ℕ) (hM : M % 4 = 3) (x : ℤ) (u : ℕ) (hu : Nat.Coprime u M)
    (h : (M : ℤ) ∣ x ^ 2 + (u : ℤ) ^ 2) : False := by
  obtain ⟨p, hp, hp4, hpM⟩ := prime_three_factor M hM
  have : Fact p.Prime := ⟨hp⟩
  have hpu : ¬ p ∣ u := by
    intro hd
    have hc : Nat.Coprime p u := (Nat.Coprime.coprime_dvd_right hpM hu).symm
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hc hd)
  have h0 : ((x ^ 2 + (u : ℤ) ^ 2 : ℤ) : ZMod p) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact (Int.natCast_dvd_natCast.mpr hpM).trans h
  push_cast at h0
  have hu0 : (u : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact hpu
  have hxy : (x : ZMod p) ^ 2 = -(u : ZMod p) ^ 2 := by linear_combination h0
  exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq' hu0 hxy hp4

theorem decomp (d : ℕ) (hd : 0 < d) (h4 : 4 ∣ d) :
    ∃ k t, d = 2*k + 4*k*t ∧ 0 < k ∧ k % 2 = 0 ∧ k % 3 ≠ 0 ∧ (8 ∣ d → k % 4 = 0) := by
  obtain ⟨e, d', h3, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd.ne' 3 (by norm_num)
  have hodd : Odd (3 ^ e) := Odd.pow (by decide)
  obtain ⟨t, ht⟩ := hodd
  have hcop : ∀ q, Nat.Coprime q 3 → q ∣ 3 ^ e * d' → q ∣ d' :=
    fun q hq hqd => (Nat.Coprime.pow_right e hq).dvd_of_dvd_mul_left hqd
  obtain ⟨j, rfl⟩ := hcop 4 (by decide) h4
  have hj : 0 < j := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0; simp at hd
    · exact h0
  refine ⟨2 * j, t, ?_, by omega, by omega, by omega, ?_⟩
  · rw [ht]; ring
  · intro h8
    have := hcop 8 (by decide) h8
    omega

theorem cong_step (c k : ℕ) (hk : k % 2 = 0) : (luc k : ℤ) ∣ luc (c + 2*k) + luc c :=
  ⟨luc (c + k), by exact_mod_cast luc_T1 c k hk⟩

theorem cong_period (c k t : ℕ) (hk : k % 2 = 0) :
    (luc k : ℤ) ∣ (luc (c + 4*k*t) : ℤ) - luc c := by
  induction t with
  | zero => simp
  | succ t ih =>
    have h1 := cong_step (c + 4*k*t) k hk
    have h2 := cong_step (c + 4*k*t + 2*k) k hk
    have e1 : c + 4*k*(t+1) = c + 4*k*t + 2*k + 2*k := by ring
    rw [e1]
    have key := dvd_add (dvd_sub h2 h1) ih
    rwa [show ∀ a b c d : ℤ, a + b - (b + c) + (c - d) = a - d from
      fun a b c d => by ring] at key

theorem cong_odd (r k t : ℕ) (hk : k % 2 = 0) :
    (luc k : ℤ) ∣ (luc (r + 2*k + 4*k*t) : ℤ) + luc r := by
  have key := dvd_add (cong_period (r + 2*k) k t hk) (cong_step r k hk)
  rwa [show ∀ a b c : ℤ, a - b + (b + c) = a + c from
    fun a b c => by ring] at key

theorem sq_mod4 (x : ℕ) : x ^ 2 % 4 = 0 ∨ x ^ 2 % 4 = 1 := by
  rw [Nat.pow_mod]
  have : x % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases x % 4 <;> simp

theorem two_sq_mod8 (y : ℕ) : (2 * y ^ 2) % 8 = 0 ∨ (2 * y ^ 2) % 8 = 2 := by
  rw [Nat.mul_mod, Nat.pow_mod]
  have : y % 8 < 8 := Nat.mod_lt _ (by norm_num)
  interval_cases y % 8 <;> simp

theorem coprime_two (M : ℕ) (h : M % 4 = 3) : Nat.Coprime 2 M :=
  (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega)

theorem coprime_six (M : ℕ) (h : M % 4 = 3) (h3 : M % 3 ≠ 0) : Nat.Coprime 6 M := by
  have a := coprime_two M h
  have b : Nat.Coprime 3 M := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega)
  exact Nat.Coprime.mul_left a b

theorem luc_sq (n x : ℕ) (h : luc n = x ^ 2) : n = 1 ∨ n = 3 := by
  by_contra hne
  have hx : (luc n : ℤ) = (x : ℤ) ^ 2 := by exact_mod_cast h
  rcases (by omega : n % 2 = 0 ∨ n % 4 = 1 ∨ n % 4 = 3) with h2 | h2 | h2
  · have h1 := luc_even_mod4 n h2
    have h3 := sq_mod4 x
    omega
  · obtain ⟨k, t, hd, hk0, hk2, hk3, -⟩ := decomp (n - 1) (by omega) (by omega)
    have hn : 1 + 2*k + 4*k*t = n := by omega
    have hc := cong_odd 1 k t hk2
    rw [hn, hx] at hc
    have e1 : (luc 1 : ℤ) = ((1 : ℕ) : ℤ) ^ 2 := by norm_num [luc]
    rw [e1] at hc
    exact final_contra (luc k) (luc_k_mod4 k hk2 hk3) x 1 (Nat.coprime_one_left _) hc
  · obtain ⟨k, t, hd, hk0, hk2, hk3, -⟩ := decomp (n - 3) (by omega) (by omega)
    have hn : 3 + 2*k + 4*k*t = n := by omega
    have hc := cong_odd 3 k t hk2
    rw [hn, hx] at hc
    have e1 : (luc 3 : ℤ) = ((2 : ℕ) : ℤ) ^ 2 := by norm_num [luc]
    rw [e1] at hc
    have hk := luc_k_mod4 k hk2 hk3
    exact final_contra (luc k) hk x 2 (coprime_two _ hk) hc

theorem luc_two_sq (n y : ℕ) (h : luc n = 2 * y ^ 2) : n = 0 ∨ n = 6 := by
  by_contra hne
  have hy : 2 * (luc n : ℤ) = ((2 * y : ℕ) : ℤ) ^ 2 := by
    rw [show (luc n : ℤ) = 2 * (y : ℤ) ^ 2 by exact_mod_cast h]
    push_cast
    ring
  rcases luc_even_idx n (by omega) with h6 | h6
  · rcases (by omega : n % 4 = 0 ∨ n % 8 = 6 ∨ n % 8 = 2) with h4 | h4 | h4
    · obtain ⟨k, t, hd, hk0, hk2, hk3, -⟩ := decomp n (by omega) (by omega)
      have hc := cong_odd 0 k t hk2
      rw [show 0 + 2*k + 4*k*t = n by omega] at hc
      have hk := luc_k_mod4 k hk2 hk3
      apply final_contra (luc k) hk ((2 * y : ℕ) : ℤ) 2 (coprime_two _ hk)
      rw [← hy]
      have e0 : (luc 0 : ℤ) = 2 := by norm_num [luc]
      rw [e0] at hc
      have := dvd_mul_of_dvd_right hc 2
      rwa [show (2 : ℤ) * (luc n + 2) = 2 * luc n + ((2 : ℕ) : ℤ) ^ 2 by push_cast; ring] at this
    · obtain ⟨k, t, hd, hk0, hk2, hk3, hk8⟩ := decomp (n - 6) (by omega) (by omega)
      have hk4 := hk8 (by omega)
      have hc := cong_odd 6 k t hk2
      rw [show 6 + 2*k + 4*k*t = n by omega] at hc
      have hk := luc_k_mod4 k hk2 hk3
      apply final_contra (luc k) hk ((2 * y : ℕ) : ℤ) 6 (coprime_six _ hk (luc_k_mod3 k hk4))
      rw [← hy]
      have e0 : (luc 6 : ℤ) = 18 := by norm_num [luc]
      rw [e0] at hc
      have := dvd_mul_of_dvd_right hc 2
      rwa [show (2 : ℤ) * (luc n + 18) = 2 * luc n + ((6 : ℕ) : ℤ) ^ 2 by push_cast; ring] at this
    · obtain ⟨k, t, hd, hk0, hk2, hk3, hk8⟩ := decomp (n + 6) (by omega) (by omega)
      have hk4 := hk8 (by omega)
      have hper := cong_period (2*k - 6) k t hk2
      rw [show 2*k - 6 + 4*k*t = n by omega] at hper
      have hbase : (luc k : ℤ) ∣ (luc (2*k - 6) : ℤ) + 18 := by
        rcases (by omega : k = 4 ∨ 8 ≤ k) with e | e
        · subst e
          norm_num [luc]
        · have h1 := luc_T1 6 (k - 6) (by omega)
          rw [show 6 + 2*(k-6) = 2*k - 6 by omega, show 6 + (k-6) = k by omega,
            show luc 6 = 18 by decide] at h1
          exact Dvd.intro_left (luc (k - 6) : ℤ) (by exact_mod_cast h1.symm)
      have hc := dvd_add hper hbase
      rw [show ∀ a b : ℤ, a - b + (b + 18) = a + 18 from fun a b => by ring] at hc
      have hk := luc_k_mod4 k hk2 hk3
      apply final_contra (luc k) hk ((2 * y : ℕ) : ℤ) 6 (coprime_six _ hk (luc_k_mod3 k hk4))
      rw [← hy]
      have := dvd_mul_of_dvd_right hc 2
      rwa [show (2 : ℤ) * (luc n + 18) = 2 * luc n + ((6 : ℕ) : ℤ) ^ 2 by push_cast; ring] at this
  · have h8 := luc_odd_mod8 n h6
    have := two_sq_mod8 y
    omega

theorem coprime_sq (a b s : ℕ) (hab : Nat.Coprime a b) (h : a * b = s ^ 2) : ∃ y, b = y ^ 2 := by
  have h' : b * a = s ^ 2 := by rw [Nat.mul_comm]; exact h
  exact exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr hab.symm) h'

theorem dvd_four (g : ℕ) (h : g ∣ 4) : g = 1 ∨ g = 2 ∨ g = 4 := by
  have := Nat.le_of_dvd (by norm_num) h
  interval_cases g <;> omega

theorem fib_luc_sq (m s : ℕ) (hm : 0 < m) (h : Nat.fib m * luc (m+3) = s ^ 2) :
    ∃ y, luc (m+3) = y ^ 2 ∨ luc (m+3) = 2 * y ^ 2 := by
  have hF : 0 < Nat.fib m := Nat.fib_pos.mpr hm
  obtain ⟨g, hg⟩ : ∃ g, g = Nat.gcd (Nat.fib m) (luc (m+3)) := ⟨_, rfl⟩
  have hgF : g ∣ Nat.fib m := hg ▸ Nat.gcd_dvd_left _ _
  have hgL : g ∣ luc (m+3) := hg ▸ Nat.gcd_dvd_right _ _
  have hg0 : 0 < g := hg ▸ Nat.gcd_pos_of_pos_left _ hF
  have hg4 : g ∣ 4 := by
    have h1 : g ∣ 3 * Nat.fib m + 4 * Nat.fib (m+1) := by rw [← luc_fib_rel]; exact hgL
    have h2 : g ∣ 4 * Nat.fib (m+1) := (Nat.dvd_add_right (dvd_mul_of_dvd_right hgF 3)).mp h1
    have cop : Nat.Coprime g (Nat.fib (m+1)) :=
      Nat.Coprime.coprime_dvd_left hgF (Nat.fib_coprime_fib_succ m)
    exact cop.dvd_of_dvd_mul_right h2
  obtain ⟨F', hF'⟩ := hgF
  obtain ⟨L', hL'⟩ := hgL
  have cop : Nat.Coprime F' L' := by
    have e : g * Nat.gcd F' L' = g * 1 := by
      rw [← Nat.gcd_mul_left, ← hF', ← hL', ← hg, Nat.mul_one]
    exact Nat.eq_of_mul_eq_mul_left hg0 e
  rw [hF', hL'] at h
  have hgs : g ∣ s := (Nat.pow_dvd_pow_iff two_ne_zero).mp ⟨F' * L', by rw [← h]; ring⟩
  obtain ⟨s', hs'⟩ := hgs
  have e2 : F' * L' = s' ^ 2 := by
    have : g ^ 2 * (F' * L') = g ^ 2 * s' ^ 2 := by
      calc g ^ 2 * (F' * L') = g * F' * (g * L') := by ring
        _ = s ^ 2 := h
        _ = g ^ 2 * s' ^ 2 := by rw [hs']; ring
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hg0 2) this
  obtain ⟨y, hy⟩ := coprime_sq F' L' s' cop e2
  rcases dvd_four g hg4 with e | e | e
  · exact ⟨y, Or.inl (by rw [hL', hy, e]; ring)⟩
  · exact ⟨y, Or.inr (by rw [hL', hy, e])⟩
  · exact ⟨2 * y, Or.inl (by rw [hL', hy, e]; ring)⟩

theorem key (m s : ℕ) (hm : 0 < m) (h : Nat.fib m * luc (m+3) = s ^ 2) : m = 3 := by
  obtain ⟨y, hy | hy⟩ := fib_luc_sq m s hm h
  · rcases luc_sq _ _ hy with h1 | h1 <;> omega
  · rcases luc_two_sq _ _ hy with h1 | h1 <;> omega

theorem no_three_sq (x y : ℕ) (hy : 0 < y) (h : x ^ 2 = 3 * y ^ 2) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx : x ≠ 0 := by
    rintro rfl
    have : 0 < 3 * y ^ 2 := by positivity
    omega
  have h3 := congrArg (padicValNat 3) h
  rw [padicValNat.pow, padicValNat.mul (by norm_num) (pow_ne_zero 2 hy.ne'), padicValNat.pow,
    padicValNat_self] at h3
  omega

theorem h1_proof : OMA.R_oeis_a236539_R1.H1 := by
  intro i k A ha hle hlt hA h
  rw [show Nat.fib i + Nat.fib k - Nat.fib i = Nat.fib k by omega] at h
  rcases hle.eq_or_lt with heq | hlt'
  · exfalso
    rw [← heq, show Nat.fib i + Nat.fib i - Nat.fib i = Nat.fib i by omega] at h
    apply no_three_sq (4 * A) (Nat.fib i ^ 2) (pow_pos ha 2)
    calc (4 * A) ^ 2 = 16 * A ^ 2 := by ring
      _ = _ := h
      _ = _ := by ring
  · have hik : i < k := by
      by_contra hc
      have := Nat.fib_mono (show k ≤ i by omega)
      omega
    have hk : k = i + 1 := by
      by_contra hc
      have h1 : Nat.fib (i+2) ≤ Nat.fib k := Nat.fib_mono (by omega)
      have h2 : Nat.fib (i+2) = Nat.fib i + Nat.fib (i+1) := Nat.fib_add_two
      have h3 : Nat.fib i ≤ Nat.fib (i+1) := Nat.fib_le_fib_succ
      omega
    subst hk
    have hi2 : 2 ≤ i := by
      rcases (by omega : i = 0 ∨ i = 1 ∨ 2 ≤ i) with e | e | e
      · subst e; simp at ha
      · subst e; exact absurd hlt' (by decide)
      · exact e
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 2 := ⟨i - 2, by omega⟩
    have hm : 0 < m := by
      rcases Nat.eq_zero_or_pos m with e | e
      · subst e; exact absurd hlt (by decide)
      · exact e
    have f2 : Nat.fib (m+2) = Nat.fib m + Nat.fib (m+1) := Nat.fib_add_two
    have f3 : Nat.fib (m+2+1) = Nat.fib (m+1) + Nat.fib (m+2) := Nat.fib_add_two
    have f4 : Nat.fib (m+4) = Nat.fib (m+2) + Nat.fib (m+2+1) := Nat.fib_add_two
    have hL : luc (m+3) = Nat.fib (m+2) + Nat.fib (m+4) := luc_fib (m+2)
    have e1 : Nat.fib (m+2) + Nat.fib (m+2) + Nat.fib (m+2+1) = luc (m+3) := by omega
    have e2 : Nat.fib (m+2) + Nat.fib (m+2) - Nat.fib (m+2+1) = Nat.fib m := by omega
    rw [e1, e2] at h
    have hc : 0 < Nat.fib (m+2+1) := Nat.fib_pos.mpr (by omega)
    obtain ⟨c, hc'⟩ : ∃ c, Nat.fib (m+2+1) = c := ⟨_, rfl⟩
    rw [hc'] at h hc
    have hsq : (4 * A) ^ 2 = c ^ 2 * (Nat.fib m * luc (m+3)) := by
      calc (4 * A) ^ 2 = 16 * A ^ 2 := by ring
        _ = _ := h
        _ = _ := by ring
    obtain ⟨s, hs⟩ : c ∣ 4 * A := (Nat.pow_dvd_pow_iff two_ne_zero).mp ⟨_, hsq⟩
    have hs2 : Nat.fib m * luc (m+3) = s ^ 2 := by
      have : c ^ 2 * (Nat.fib m * luc (m+3)) = c ^ 2 * s ^ 2 := by rw [← hsq, hs]; ring
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hc 2) this
    have hm3 := key m s hm hs2
    subst hm3
    have hc8 : c = 8 := by rw [← hc']; decide
    subst hc8
    have hl6 : luc (3+3) = 18 := by decide
    have hf3 : Nat.fib 3 = 2 := by decide
    rw [hl6, hf3] at h
    have hA2 : A ^ 2 = 12 ^ 2 := by omega
    refine ⟨by decide, rfl, ?_⟩
    exact Nat.pow_left_injective two_ne_zero hA2

end OMA.StepCohnLucasSquares

theorem OMA.solution : OMA.R_oeis_a236539_R1.H1 :=
  OMA.StepCohnLucasSquares.h1_proof
