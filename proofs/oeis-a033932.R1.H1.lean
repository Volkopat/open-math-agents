import OMAReductions.R_oeis_a033932_R1
import Mathlib

/-! Step oeis-a033932.R1.H1, the elementary facts about `a n`, the least `m ≥ 1` with `n! + m`
prime. A prime `q ≤ n` divides `n!`, so a prime factor `q ≤ n` of `a n` would divide the prime
`n! + a n`, which is impossible since `q ≤ a n < n! + a n`. Hence a composite `a n` has
`minFac ≥ n + 1` and so `a n ≥ (n + 1) ^ 2`. -/

namespace OMA.A033932H1

open OMA.S_oeis_a033932

lemma nonempty (n : ℕ) : {m : ℕ | 1 ≤ m ∧ (n.factorial + m).Prime}.Nonempty := by
  obtain ⟨p, hp, hpp⟩ := Nat.exists_infinite_primes (n.factorial + 1)
  exact ⟨p - n.factorial, by omega, by rwa [Nat.add_sub_cancel' (by omega)]⟩

lemma spec (n : ℕ) : 1 ≤ a n ∧ (n.factorial + a n).Prime := Nat.sInf_mem (nonempty n)

lemma big_factor (n : ℕ) (q : ℕ) (hq : q.Prime) (hqa : q ∣ a n) : n < q := by
  obtain ⟨h1, hp⟩ := spec n
  by_contra hle
  push Not at hle
  have h2 : q ∣ n.factorial + a n := dvd_add (Nat.dvd_factorial hq.pos hle) hqa
  rcases hp.eq_one_or_self_of_dvd q h2 with h3 | h3
  · exact hq.one_lt.ne' h3
  · have : q ≤ a n := Nat.le_of_dvd (by omega) hqa
    have := Nat.factorial_pos n
    omega

theorem main :
    (∀ n : ℕ, 1 ≤ a n) ∧
    (∀ n : ℕ, 1 < a n → ∀ q : ℕ, q.Prime → q ∣ a n → n < q) ∧
    (∀ n : ℕ, 1 < a n → ¬ (a n).Prime → (n + 1) ^ 2 ≤ a n) := by
  refine ⟨fun n => (spec n).1, fun n _ q hq hqa => big_factor n q hq hqa, fun n h1 hnp => ?_⟩
  have hmin := Nat.minFac_sq_le_self (by omega) hnp
  have hmf : n < (a n).minFac := big_factor n _ (Nat.minFac_prime (by omega)) (Nat.minFac_dvd _)
  have : (n + 1) ^ 2 ≤ (a n).minFac ^ 2 := Nat.pow_le_pow_left hmf 2
  omega

end OMA.A033932H1

theorem OMA.solution : OMA.R_oeis_a033932_R1.H1 :=
  OMA.A033932H1.main
