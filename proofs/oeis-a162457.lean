import OMAStatements.S_oeis_a162457
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a162457.main := by
  classical
  have existsPrime (i : ℕ) :
      ∃ p : ℕ, p.Prime ∧ 10 ^ i ≤ p ∧ p < 10 ^ (i + 1) := by
    have hn : 0 < (10 : ℕ) ^ i := by positivity
    obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (10 ^ i) hn.ne'
    exact ⟨p, hp, hlt.le, by rw [pow_succ]; omega⟩
  choose p hp using existsPrime
  let f (k : ℕ) := ∏ i ∈ Finset.range (k + 1), p i
  have hmono : StrictMono f := by
    apply strictMono_nat_of_lt_succ
    intro k
    change (∏ i ∈ Finset.range (k + 1), p i) <
      ∏ i ∈ Finset.range ((k + 1) + 1), p i
    rw [Finset.prod_range_succ (n := k + 1)]
    have hpos : 0 < ∏ i ∈ Finset.range (k + 1), p i :=
      Finset.prod_pos fun i _ => (hp i).1.pos
    have h := Nat.mul_lt_mul_of_pos_left (hp (k + 1)).1.one_lt hpos
    simpa only [mul_one] using h
  apply Set.infinite_of_injective_forall_mem hmono.injective
  intro k
  exact ⟨k + 1, by omega, p, fun i _ => hp i, rfl⟩