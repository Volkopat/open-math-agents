import OMAReductions.R_OeisA78680_conjecture_R1
import Mathlib.NumberTheory.Fermat
import Mathlib.Tactic

/-!
A prime of the form `2^16 * 2^m + 1`, for `m > 0`, must be a Fermat
number with index at least five. The small indices are certified using
proper divisors from https://www.fermatsearch.org/factors/faclist.php.
-/

namespace OMA.R_OeisA78680_conjecture_R1_H1_R1

/-- Repeated squaring modulo a proposed divisor keeps the certificate small. -/
private theorem residue_spec (d k : ℕ) :
    ((fun r : ℕ => r * r % d)^[k]) (2 % d) = 2 ^ (2 ^ k) % d := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ (2 : ℕ) k, pow_mul, pow_two]
    exact (Nat.mul_mod _ _ _).symm

private theorem not_prime_of_factor {d k j : ℕ}
    (hj : j ≤ k) (hd : 1 < d) (hlt : d < Nat.fermatNumber j)
    (hr : (((fun r : ℕ => r * r % d)^[k]) (2 % d) + 1) % d = 0) :
    ¬ (Nat.fermatNumber k).Prime := by
  intro hp
  have hdiv : d ∣ Nat.fermatNumber k := by
    rw [Nat.dvd_iff_mod_eq_zero, Nat.fermatNumber]
    rw [residue_spec] at hr
    simpa only [Nat.mod_add_mod] using hr
  rcases (Nat.dvd_prime hp).mp hdiv with h | h
  · omega
  · exact (ne_of_lt (hlt.trans_le (Nat.fermatNumber_mono hj))) h

/-- The first fifteen possible Fermat numbers are composite. -/
def H1 : Prop := ∀ k : ℕ, 5 ≤ k → k < 20 → ¬ (Nat.fermatNumber k).Prime

/-- All subsequent Fermat numbers are composite. -/
def H2 : Prop := ∀ k : ℕ, 20 ≤ k → ¬ (Nat.fermatNumber k).Prime

theorem finite_cases : H1 := by
  intro k hk hlo
  interval_cases k
  · exact not_prime_of_factor (d := 641) (j := 5)
      (by decide) (by decide) (by norm_num [Nat.fermatNumber]) (by decide +kernel)
  · exact not_prime_of_factor (d := 274177) (j := 6)
      (by decide) (by decide) (by norm_num [Nat.fermatNumber]) (by decide +kernel)
  · exact not_prime_of_factor (d := 59649589127497217) (j := 7)
      (by decide) (by decide) (by norm_num [Nat.fermatNumber]) (by decide +kernel)
  · exact not_prime_of_factor (d := 1238926361552897) (j := 8)
      (by decide) (by decide) (by norm_num [Nat.fermatNumber]) (by decide +kernel)
  · exact not_prime_of_factor (d := 2424833) (j := 8)
      (by decide) (by decide) (by norm_num [Nat.fermatNumber]) (by decide +kernel)
  · exact not_prime_of_factor (d := 45592577) (j := 8)
      (by decide) (by decide) (by norm_num [Nat.fermatNumber]) (by decide +kernel)
  · exact not_prime_of_factor (d := 319489) (j := 8)
      (by decide) (by decide) (by norm_num [Nat.fermatNumber]) (by decide +kernel)
  · exact not_prime_of_factor (d := 114689) (j := 8)
      (by decide) (by decide) (by norm_num [Nat.fermatNumber]) (by decide +kernel)
  · exact not_prime_of_factor (d := 2710954639361) (j := 8)
      (by decide) (by decide) (by norm_num [Nat.fermatNumber]) (by decide +kernel)
  · exact not_prime_of_factor (d := 116928085873074369829035993834596371340386703423373313) (j := 8)
      (by decide) (by decide) (by norm_num [Nat.fermatNumber]) (by decide +kernel)
  · exact not_prime_of_factor (d := 1214251009) (j := 8)
      (by decide) (by decide) (by norm_num [Nat.fermatNumber]) (by decide +kernel)
  · exact not_prime_of_factor (d := 825753601) (j := 8)
      (by decide) (by decide) (by norm_num [Nat.fermatNumber]) (by decide +kernel)
  · exact not_prime_of_factor (d := 31065037602817) (j := 8)
      (by decide) (by decide) (by norm_num [Nat.fermatNumber]) (by decide +kernel)
  · exact not_prime_of_factor (d := 13631489) (j := 8)
      (by decide) (by decide) (by norm_num [Nat.fermatNumber]) (by decide +kernel)
  · exact not_prime_of_factor (d := 70525124609) (j := 8)
      (by decide) (by decide) (by norm_num [Nat.fermatNumber]) (by decide +kernel)

theorem main : H1 → H2 → OMA.R_OeisA78680_conjecture_R1.H1 := by
  intro hsmall hlarge
  change OeisA78680.a (2 ^ 16) = 0
  classical
  unfold OeisA78680.a
  split_ifs with hex
  · obtain ⟨m, hm, hp⟩ := hex
    rw [← pow_add] at hp
    obtain ⟨k, hk⟩ := Nat.pow_of_pow_add_prime (by decide : 1 < (2 : ℕ))
      (by omega : 16 + m ≠ 0) hp
    have hk5 : 5 ≤ k := by
      by_contra! h
      interval_cases k <;> norm_num at hk <;> omega
    rw [hk] at hp
    exact ((if h : k < 20 then hsmall k hk5 h else hlarge k (by omega)) hp).elim
  · rfl

end OMA.R_OeisA78680_conjecture_R1_H1_R1
