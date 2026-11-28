import OMAStatements.S_oeis_a172487
import Mathlib

/-!
# A172487: for a(n) > 3 the first differences are divisible by 6

Every term p is prime with p + 2 prime. If p > 3 then p is divisible by neither 2 nor 3, and
p + 2 is not divisible by 3 (else p + 2 = 3), so p % 6 = 5. If a(n) > 3 and a(n+1) is a term,
then a(n) is a term too (it is not the junk value 0), a(n+1) > a(n) > 3 because `Nat.nth` is
strictly increasing on the indices of actual terms, so both terms are 5 modulo 6 and their
difference is divisible by 6.
-/

namespace OMA.P172487

open OMA.S_oeis_a172487

/-- A term larger than 3 is congruent to 5 modulo 6. -/
lemma mod_six {p : ℕ} (hp : InA172487 p) (h3 : 3 < p) : p % 6 = 5 := by
  obtain ⟨_, hpp, hp2⟩ := hp
  have h2 : p % 2 ≠ 0 := by
    intro h
    have := Nat.Prime.eq_one_or_self_of_dvd hpp 2 (Nat.dvd_of_mod_eq_zero h)
    omega
  have h3' : p % 3 ≠ 0 := by
    intro h
    have := Nat.Prime.eq_one_or_self_of_dvd hpp 3 (Nat.dvd_of_mod_eq_zero h)
    omega
  have h3'' : (p + 2) % 3 ≠ 0 := by
    intro h
    have := Nat.Prime.eq_one_or_self_of_dvd hp2 3 (Nat.dvd_of_mod_eq_zero h)
    omega
  have key : p % 6 = 0 ∨ p % 6 = 1 ∨ p % 6 = 2 ∨ p % 6 = 3 ∨ p % 6 = 4 ∨ p % 6 = 5 := by
    omega
  rcases key with h | h | h | h | h | h <;> omega

/-- Terms are never the junk value 0 (0 is not prime). -/
lemma ne_zero_of_mem {p : ℕ} (hp : InA172487 p) : p ≠ 0 := by
  intro h
  subst h
  exact Nat.not_prime_zero hp.2.1

theorem sol : type_of% @OMA.S_oeis_a172487.main := by
  intro n hn h3 hnext
  have ha : a n = Nat.nth InA172487 (n - 1) := rfl
  have hb : a (n + 1) = Nat.nth InA172487 n := by
    show Nat.nth InA172487 (n + 1 - 1) = Nat.nth InA172487 n
    rfl
  have hne : Nat.nth InA172487 (n - 1) ≠ 0 := by
    rw [← ha]
    omega
  have hmem : InA172487 (a n) := by
    rw [ha]
    exact Nat.nth_mem_of_ne_zero hne
  have hne' : Nat.nth InA172487 n ≠ 0 := by
    rw [← hb]
    exact ne_zero_of_mem hnext
  have hlt : a n < a (n + 1) := by
    rw [ha, hb]
    exact Nat.nth_lt_nth' (by omega) (fun hf => Nat.lt_card_toFinset_of_nth_ne_zero hne' hf)
  have h5 := mod_six hmem h3
  have h5' := mod_six hnext (by omega)
  omega

end OMA.P172487

theorem OMA.solution : type_of% @OMA.S_oeis_a172487.main := OMA.P172487.sol
