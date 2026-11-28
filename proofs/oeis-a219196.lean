import OMAStatements.S_oeis_a219196
import Mathlib

open OMA.S_oeis_a219196


/-- The primes `p` with `p - 1` a power of two at most `2^31`. -/
def F : Finset ℕ := {2, 3, 5, 17, 257, 65537}

theorem two_pow_add_one_prime (i : ℕ) (hi : i ≤ 31) (hp : (2 ^ i + 1).Prime) :
    2 ^ i + 1 ∈ F := by
  interval_cases i <;> first | (norm_num at hp; done) | simp [F]

theorem F_prime : ∀ p ∈ F, p.Prime := by
  intro p hp
  simp only [F, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem F_pos : ∀ p ∈ F, 1 ≤ p := fun p hp => (F_prime p hp).one_lt.le

theorem filter_eq (j : ℕ) (hj : j ≤ 31) :
    (Finset.range (2 ^ j + 2)).filter (fun p => p.Prime ∧ (p - 1) ∣ 2 ^ j) =
      F.filter (fun p => (p - 1) ∣ 2 ^ j) := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, hp, hd⟩
    refine ⟨?_, hd⟩
    obtain ⟨i, hij, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
    have h1 := hp.one_lt
    have : p = 2 ^ i + 1 := by omega
    subst this
    exact two_pow_add_one_prime i (by omega) hp
  · rintro ⟨hF, hd⟩
    refine ⟨?_, F_prime p hF, hd⟩
    have := Nat.le_of_dvd (by positivity) hd
    omega

theorem den_eq (j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ 31) :
    (bernoulli (2 ^ j)).den = (∑ p ∈ F.filter (fun p => (p - 1) ∣ 2 ^ j), (1 : ℚ) / p).den := by
  have h2 : 2 ^ j = 2 * 2 ^ (j - 1) := by
    rw [← pow_succ']; congr 1; omega
  obtain ⟨m, hm⟩ := Bernoulli.vonStaudt_clausen (2 ^ (j - 1))
  rw [← h2, filter_eq j hj] at hm
  have : bernoulli (2 ^ j) = (m : ℚ) - ∑ p ∈ F.filter (fun p => (p - 1) ∣ 2 ^ j), (1 : ℚ) / p := by
    rw [hm]; ring
  rw [this, Rat.intCast_sub_den]

theorem OMA.solution : type_of% @OMA.S_oeis_a219196.main := by
  have key : ∀ n, 2 ≤ n → n ≤ 32 →
      a n = (∑ p ∈ F.filter (fun p => (p - 1) ∣ 2 ^ (n - 1)), (1 : ℚ) / p).den := by
    intro n h1 h2
    unfold a A027642 A131577
    rw [if_neg (by omega)]
    exact den_eq (n - 1) (by omega) (by omega)
  refine ⟨?_, ?_, ?_⟩
  · rw [key 15 (by norm_num) (by norm_num)]; decide +kernel
  · rw [key 16 (by norm_num) (by norm_num)]; decide +kernel
  · intro n h1 h2
    rw [key n (by omega) h2]
    interval_cases n <;> decide +kernel
