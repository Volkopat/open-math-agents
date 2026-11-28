import OMAStatements.S_mo_239499
import Mathlib

/-!
For odd n, the candidate N = 4 + n² is 5 modulo 8. Euler's criterion
and the supplementary law for 2 certify every prime candidate.
A successful candidate also cannot have 17 as a factor, since squaring
the base-2 test modulo 17 gives opposite values for the same power.
-/

namespace OMA.R_mo_239499_R1

private theorem candidate_mod_eight {n : ℕ} (hn : n % 2 = 1) :
    (2 ^ 2 + n ^ 2) % 8 = 5 := by
  have h : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by omega
  have hs : n ^ 2 % 8 = 1 := by
    rw [Nat.pow_mod]
    rcases h with h | h | h | h <;> norm_num [h]
  rw [Nat.add_mod]
  norm_num [hs]

private theorem passes_of_prime {N : ℕ} (hN : N % 8 = 5) (hp : N.Prime) :
    N ∣ 2 ^ ((N - 1) / 2) + 1 := by
  let _ : Fact N.Prime := ⟨hp⟩
  have hN2 : N ≠ 2 := by omega
  have hne : (2 : ZMod N) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff 2 N).mp (by simpa using h)
    have hle := Nat.le_of_dvd (by decide : 0 < 2) hd
    omega
  have hns : ¬ IsSquare (2 : ZMod N) := by
    intro h
    have hh := (ZMod.exists_sq_eq_two_iff hN2).mp h
    omega
  have he : (2 : ZMod N) ^ (N / 2) = -1 := by
    rcases ZMod.pow_div_two_eq_neg_one_or_one N hne with h | h
    · exact (hns ((ZMod.euler_criterion N hne).mpr h)).elim
    · exact h
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  push_cast
  rw [show (N - 1) / 2 = N / 2 by omega, he, neg_add_cancel]

private theorem seventeen_not_dvd_of_passes {N : ℕ} (hN : N % 8 = 5)
    (hp : N ∣ 2 ^ ((N - 1) / 2) + 1) : ¬ 17 ∣ N := by
  intro h17
  have hc := (ZMod.natCast_eq_zero_iff _ _).mpr (h17.trans hp)
  push_cast at hc
  have he : (2 : ZMod 17) ^ ((N - 1) / 2) = -1 := by
    linear_combination hc
  have hs : ((2 : ZMod 17) ^ ((N - 1) / 2)) ^ 2 = (-1 : ZMod 17) ^ 2 :=
    congrArg (fun x : ZMod 17 => x ^ 2) he
  rw [← pow_mul, show ((N - 1) / 2) * 2 = 8 * (N / 8) + 4 by omega,
    pow_add, pow_mul] at hs
  simp only [show (2 : ZMod 17) ^ 8 = 1 by decide, one_pow, one_mul,
    show (2 : ZMod 17) ^ 4 = -1 by decide, neg_one_sq] at hs
  exact (by decide : ¬ (-1 : ZMod 17) = 1) hs

/-- Primes pass the test, and passing excludes a factor of seventeen. -/
def H1 : Prop := ∀ n : ℕ, n % 2 = 1 →
  let N := 2 ^ 2 + n ^ 2
  (N.Prime → N ∣ 2 ^ ((N - 1) / 2) + 1) ∧
  (N ∣ 2 ^ ((N - 1) / 2) + 1 → ¬ 17 ∣ N)

/-- The converse for candidates that have no factor of seventeen. -/
def H2 : Prop := ∀ n : ℕ, n % 2 = 1 →
  let N := 2 ^ 2 + n ^ 2
  ¬ 17 ∣ N → N ∣ 2 ^ ((N - 1) / 2) + 1 → N.Prime

theorem prime_and_seventeen : H1 := by
  intro n hn
  exact ⟨passes_of_prime (candidate_mod_eight hn),
    seventeen_not_dvd_of_passes (candidate_mod_eight hn)⟩

theorem main : H1 → H2 → type_of% @OMA.S_mo_239499.main := by
  intro elementary remaining n hn
  obtain ⟨forward, withoutSeventeen⟩ := elementary n hn
  exact ⟨forward, fun h => remaining n hn (withoutSeventeen h) h⟩

end OMA.R_mo_239499_R1
