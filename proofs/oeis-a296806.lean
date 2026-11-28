import OMAStatements.S_oeis_a296806

-- Problem: A296806: Take a prime, convert it to base 2, remove its most significant digit and its least significant digit and convert it back to base 10. Sequence lists primes that generate another prime by this process.
-- Upstream: formal-conjectures statements/oeis-a296806.lean:0 (declaration OMA.S_oeis_a296806.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Disprove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: p = 1777796, 2p+1 = 3555593. By the covering {0 mod 2, 0 mod 3, 1 mod 4, 3 mod 8,
-- 7 mod 12, 23 mod 24} with the primes 3, 7, 5, 17, 13, 241 (each divides 2^24 - 1), for every
-- n one of these primes divides 3555593 + 2^n, which is larger, so it is never prime and the
-- set of primes q in the conjecture is empty for this p.

namespace H13A296806

theorem cover : ∀ r < 24, ∃ P ∈ [3, 5, 7, 13, 17, 241], (3555593 + 2 ^ r) % P = 0 := by
  decide

theorem period : ∀ P ∈ [3, 5, 7, 13, 17, 241], 3 ≤ P ∧ P ≤ 241 ∧ Nat.ModEq P (2 ^ 24) 1 := by
  decide

theorem composite (n : ℕ) : ¬ Nat.Prime (3555593 + 2 ^ n) := by
  obtain ⟨P, hP, hdiv⟩ := cover (n % 24) (Nat.mod_lt n (by norm_num))
  obtain ⟨hP3, hP241, h24⟩ := period P hP
  have h1 := h24.pow (n / 24)
  rw [one_pow, ← pow_mul] at h1
  have h2 := h1.mul_right (2 ^ (n % 24))
  rw [one_mul, ← pow_add, Nat.div_add_mod] at h2
  have hsum : Nat.ModEq P (3555593 + 2 ^ n) (3555593 + 2 ^ (n % 24)) := h2.add_left 3555593
  have hdvd : P ∣ 3555593 + 2 ^ n := Nat.dvd_of_mod_eq_zero (Eq.trans hsum hdiv)
  have hpos : 0 < 2 ^ n := by positivity
  intro hp
  rcases hp.eq_one_or_self_of_dvd P hdvd with h | h
  · omega
  · omega

end H13A296806

open OMA.S_oeis_a296806 H13A296806 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a296806.main) := by
  intro h
  obtain ⟨q, hq, n, hn⟩ := (h 1777796 (by norm_num)).nonempty
  have hpos : 0 < 2 ^ n := by positivity
  have hq' : q = 3555593 + 2 ^ n := by omega
  rw [hq'] at hq
  exact composite n hq
