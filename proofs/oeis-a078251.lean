import OMAStatements.S_oeis_a078251
import Mathlib

/-!
# A078251: some repetition `nn…n` is divisible by the `n`-th prime (`n > 3`)

For `n > 3` the `n`-th prime `p` exceeds `5`, so `p` is coprime to `B = 10 ^ d`, where `d`
is the number of digits of `n`.  The `k`-fold repetition of `n` is `n * (1 + B + ⋯ + B^(k-1))`.

* If `B ≡ 1 (mod p)`, the geometric sum with `k = p` terms is `≡ p ≡ 0`.
* Otherwise `(1 + B + ⋯ + B^(p-2)) (B - 1) = B^(p-1) - 1 ≡ 0` by Fermat, and `B - 1` is
  invertible modulo `p`, so `k = p - 1` works.

Hence a valid `k` exists, and the corresponding repetition is a positive number.
-/

namespace OMA.S_oeis_a078251

open Finset

/-- A geometric sum with ratio coprime to `p` is divisible by `p` for a suitable length. -/
lemma exists_geom_dvd {p B : ℕ} (hp : p.Prime) (hB : ¬ p ∣ B) :
    ∃ k : ℕ, 0 < k ∧ p ∣ ∑ j ∈ range k, B ^ j := by
  have : Fact p.Prime := ⟨hp⟩
  have hx : (B : ZMod p) ≠ 0 := fun h => hB ((ZMod.natCast_eq_zero_iff B p).mp h)
  by_cases h1 : (B : ZMod p) = 1
  · refine ⟨p, hp.pos, (ZMod.natCast_eq_zero_iff _ p).mp ?_⟩
    push_cast
    simp [h1]
  · refine ⟨p - 1, Nat.sub_pos_of_lt hp.one_lt, (ZMod.natCast_eq_zero_iff _ p).mp ?_⟩
    push_cast
    have hgeo := geom_sum_mul (B : ZMod p) (p - 1)
    rw [ZMod.pow_card_sub_one_eq_one hx, sub_self] at hgeo
    rcases mul_eq_zero.mp hgeo with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) h1

end OMA.S_oeis_a078251

open OMA.S_oeis_a078251 Finset in
theorem OMA.solution : type_of% @OMA.S_oeis_a078251.main := by
  intro n hn
  have hp : (Nat.nth Nat.Prime (n - 1)).Prime := Nat.prime_nth_prime _
  have hp6 : 6 ≤ Nat.nth Nat.Prime (n - 1) := by
    have h5 : Nat.nth Nat.Prime 2 = 5 := by
      have := Nat.nth_count (p := Nat.Prime) Nat.prime_five
      rwa [show Nat.count Nat.Prime 5 = 2 by decide] at this
    have hlt : Nat.nth Nat.Prime 2 < Nat.nth Nat.Prime (n - 1) :=
      Nat.nth_strictMono Nat.infinite_setOfPred_prime (show 2 < n - 1 by omega)
    omega
  -- `p` does not divide the base `B = 10 ^ d`
  have hB : ¬ Nat.nth Nat.Prime (n - 1) ∣ 10 ^ (Nat.digits 10 n).length := by
    intro h
    have h10 := hp.dvd_of_dvd_pow h
    have hle := Nat.le_of_dvd (by norm_num) h10
    generalize Nat.nth Nat.Prime (n - 1) = p at *
    interval_cases p <;> first | omega | (norm_num at hp)
  obtain ⟨k, hk, hdvd⟩ := exists_geom_dvd hp hB
  have hex : ∃ k : ℕ, 0 < k ∧ Nat.nth Nat.Prime (n - 1) ∣ repConcat n k :=
    ⟨k, hk, Dvd.dvd.mul_left hdvd n⟩
  -- the least such `k` is positive, so the repetition is a positive number
  have hmem := Nat.sInf_mem (s := {k : ℕ | 0 < k ∧ Nat.nth Nat.Prime (n - 1) ∣ repConcat n k}) hex
  unfold a
  dsimp only
  rw [dif_pos hex]
  unfold repConcat
  exact Nat.mul_ne_zero (by omega)
    (Finset.sum_pos (fun j _ => by positivity) (nonempty_range_iff.mpr hmem.1.ne')).ne'
