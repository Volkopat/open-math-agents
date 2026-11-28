import OMAReductions.R_oeis_a105403_R1

-- Step oeis-a105403.R1.H1: hypothesis H1 of reduction oeis-a105403.R1
-- Credit: @sobrien032
-- H1 := ({2, 30, 53, 217} : Set ℕ) ⊆ {n : ℕ | 1 ≤ n ∧ gpf (prime n - 1) = gpf (prime (n + 1) - 1)}

/-!
The four known terms 2, 30, 53 and 217 of OEIS A105403 (conjecture of Jon E. Schoenfield) have
the property. The primes involved are prime(2) = 3, prime(3) = 5, prime(30) = 113,
prime(31) = 127, prime(53) = 241, prime(54) = 251, prime(217) = 1327 and prime(218) = 1361.
The largest prime factors agree: 2 for 2 and 4, 7 for 112 and 126, 5 for 240 and 250, and
17 for 1326 and 1360.

Each prime is located with `Nat.nth_count`. The number of primes below it is computed by the
kernel (`decide +kernel`) with an exact trial-division test that stops at the square root.
The largest prime factors are computed by `simp` with Mathlib's `Nat.primeFactorsList` simproc.
-/

namespace OMA.A105403Step

/-- Trial division of `n` by `d, d + 1, …`: `true` as soon as `n < d * d`, `false` at the first
divisor. When the fuel runs out it defers to Mathlib's decision procedure, so the test is exact
for every amount of fuel. -/
def trial (n : ℕ) : ℕ → ℕ → Bool
  | 0, _ => decide (Nat.Prime n)
  | fuel + 1, d => if n < d * d then true else if n % d = 0 then false else trial n fuel (d + 1)

theorem trial_iff (n : ℕ) (hn : 2 ≤ n) :
    ∀ fuel d, 2 ≤ d → (∀ m, 2 ≤ m → m < d → ¬ m ∣ n) → (trial n fuel d = true ↔ Nat.Prime n) := by
  intro fuel
  induction fuel with
  | zero => intro d _ _; simp [trial]
  | succ fuel ih =>
    intro d hd hsmall
    simp only [trial]
    split_ifs with h1 h2
    · simp only [true_iff]
      by_contra hnp
      have hsq := Nat.minFac_sq_le_self (by omega) hnp
      have hmp := Nat.minFac_prime (show n ≠ 1 by omega)
      have hlt : n.minFac < d := by
        by_contra hge
        have hle : d ≤ n.minFac := Nat.le_of_not_lt hge
        have : d * d ≤ n.minFac ^ 2 := by rw [sq]; exact Nat.mul_le_mul hle hle
        omega
      exact hsmall _ hmp.two_le hlt (Nat.minFac_dvd n)
    · simp only [false_iff]
      intro hp
      have hdvd : d ∣ n := Nat.dvd_of_mod_eq_zero h2
      rcases hp.eq_one_or_self_of_dvd d hdvd with h | h
      · omega
      · subst h
        have : d * 2 ≤ d * d := Nat.mul_le_mul_left d hd
        omega
    · apply ih (d + 1) (by omega)
      intro m hm hmd
      rcases Nat.lt_succ_iff_lt_or_eq.mp hmd with h | h
      · exact hsmall m hm h
      · subst h
        intro hdvd
        exact h2 (Nat.mod_eq_zero_of_dvd hdvd)

/-- An exact primality test that the kernel evaluates quickly. -/
def isPrimeB (n : ℕ) : Bool := if 2 ≤ n then trial n n 2 else false

theorem isPrimeB_iff (n : ℕ) : isPrimeB n = true ↔ Nat.Prime n := by
  unfold isPrimeB
  split_ifs with h
  · exact trial_iff n h n 2 le_rfl (fun m hm hm2 => absurd hm2 (by omega))
  · simp only [false_iff]
    exact fun hp => h hp.two_le

/-- `Nat.count Nat.Prime p`, the number of primes below `p`, computed with `isPrimeB`. -/
def primeCount (p : ℕ) : ℕ :=
  @Nat.count Nat.Prime (fun n => decidable_of_iff _ (isPrimeB_iff n)) p

theorem nth_prime_eq {k p : ℕ} (hp : Nat.Prime p) (hc : primeCount p = k) :
    Nat.nth Nat.Prime k = p := by
  rw [← hc]
  exact @Nat.nth_count Nat.Prime (fun n => decidable_of_iff _ (isPrimeB_iff n)) p hp

open OMA.S_oeis_a105403 in
/-- An index has the property once the two primes around it and their common largest prime
factor are known. -/
theorem mem_of_primes {n a b q : ℕ} (hn : 1 ≤ n) (ha : Nat.nth Nat.Prime (n - 1) = a)
    (hb : Nat.nth Nat.Prime n = b) (hqa : gpf (a - 1) = q) (hqb : gpf (b - 1) = q) :
    n ∈ {n : ℕ | 1 ≤ n ∧ gpf (prime n - 1) = gpf (prime (n + 1) - 1)} := by
  rw [Set.mem_ofPred_eq]
  refine ⟨hn, ?_⟩
  simp only [prime, Nat.add_sub_cancel, ha, hb, hqa, hqb]

end OMA.A105403Step

open OMA.S_oeis_a105403 OMA.A105403Step in
theorem OMA.solution : OMA.R_oeis_a105403_R1.H1 := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl
  · exact mem_of_primes (a := 3) (b := 5) (q := 2) (by norm_num)
      (nth_prime_eq (by norm_num) (by decide +kernel))
      (nth_prime_eq (by norm_num) (by decide +kernel))
      (by simp [gpf, Nat.primeFactors]) (by simp [gpf, Nat.primeFactors])
  · exact mem_of_primes (a := 113) (b := 127) (q := 7) (by norm_num)
      (nth_prime_eq (by norm_num) (by decide +kernel))
      (nth_prime_eq (by norm_num) (by decide +kernel))
      (by simp [gpf, Nat.primeFactors]) (by simp [gpf, Nat.primeFactors])
  · exact mem_of_primes (a := 241) (b := 251) (q := 5) (by norm_num)
      (nth_prime_eq (by norm_num) (by decide +kernel))
      (nth_prime_eq (by norm_num) (by decide +kernel))
      (by simp [gpf, Nat.primeFactors]) (by simp [gpf, Nat.primeFactors])
  · exact mem_of_primes (a := 1327) (b := 1361) (q := 17) (by norm_num)
      (nth_prime_eq (by norm_num) (by decide +kernel))
      (nth_prime_eq (by norm_num) (by decide +kernel))
      (by simp [gpf, Nat.primeFactors]) (by simp [gpf, Nat.primeFactors])
