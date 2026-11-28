import OMAStatements.S_wp_lucas_wieferich_prime
import Mathlib

/-!
Formalization slip: this proves the Lean statement as written, NOT the open problem.

The Lean definition `IsLucasWieferichPrime a p` asks only that `p` divide
`U_{p - (D/p)}` (with `D = a^2 + 4`), which is the classical Lucas congruence: it holds
for every odd prime `p`. The Lucas-Wieferich condition in the cited source (Wikipedia,
Lucas-Wieferich prime) requires `p^2` to divide `U_{p - (D/p)}`. So this file proves the
statement as written and leaves the real problem (infinitely many Lucas-Wieferich primes
for the pair `(a, -1)`) untouched.

Argument: for primes `p = 1 mod 4D` with `p > D`, Jacobi reciprocity (`jacobiSym.mod_right`)
gives `(D/p) = 1`, so `D = s^2` in `ZMod p`; with `alpha, beta = (a +- s)/2` one has
`U_n * s = alpha^n - beta^n`, and Fermat gives `alpha^(p-1) = beta^(p-1) = 1`, so `p | U_{p-1}`.
-/

namespace GLucas
open OMA.S_wp_lucas_wieferich_prime

/-- Binet-type formula for the cast of `lucasU a` into a commutative ring. -/
theorem binet {R : Type*} [CommRing R] (a : ℤ) (s α β : R)
    (hα : α ^ 2 = (a : R) * α + 1) (hβ : β ^ 2 = (a : R) * β + 1) (hs : α - β = s) :
    ∀ n : ℕ, (lucasU a n : R) * s = α ^ n - β ^ n ∧
      (lucasU a (n + 1) : R) * s = α ^ (n + 1) - β ^ (n + 1) := by
  intro n
  induction n with
  | zero => simp [lucasU, hs]
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have e : (lucasU a (n + 2) : R) = (a : R) * lucasU a (n + 1) + lucasU a n := by
      simp [lucasU]
    rw [e]
    linear_combination (a : R) * ih.2 + ih.1 - α ^ n * hα + β ^ n * hβ

theorem dvd_of_prime (a : ℤ) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hD0 : ((lucasDiscriminant a : ℤ) : ZMod p) ≠ 0)
    (hJ : jacobiSym (lucasDiscriminant a) p = 1) :
    (p : ℤ) ∣ lucasU a (p - 1) := by
  have := Fact.mk hp
  have hleg : legendreSym p (lucasDiscriminant a) = 1 := by
    rw [jacobiSym.legendreSym.to_jacobiSym]; exact hJ
  obtain ⟨s, hs⟩ := (legendreSym.eq_one_iff p hD0).mp hleg
  have hsD : s ^ 2 = (a : ZMod p) ^ 2 + 4 := by
    rw [sq, ← hs]; simp [lucasDiscriminant]
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this
    exact hp2 this
  set i : ZMod p := (2 : ZMod p)⁻¹ with hi_def
  have hi : 2 * i - 1 = 0 := by rw [hi_def, mul_inv_cancel₀ h2]; ring
  set α : ZMod p := ((a : ZMod p) + s) * i
  set β : ZMod p := ((a : ZMod p) - s) * i
  have hα : α ^ 2 = (a : ZMod p) * α + 1 := by
    simp only [α]
    linear_combination (1 + i * ((a : ZMod p) ^ 2 + a * s + 2)) * hi + i ^ 2 * hsD
  have hβ : β ^ 2 = (a : ZMod p) * β + 1 := by
    simp only [β]
    linear_combination (1 + i * ((a : ZMod p) ^ 2 - a * s + 2)) * hi + i ^ 2 * hsD
  have hαβ : α - β = s := by
    simp only [α, β]
    linear_combination s * hi
  have hprod : α * β = -1 := by
    simp only [α, β]
    linear_combination (-i ^ 2) * hsD - (2 * i + 1) * hi
  have hα0 : α ≠ 0 := by
    intro h; rw [h, zero_mul] at hprod; exact one_ne_zero (neg_eq_zero.mp hprod.symm)
  have hβ0 : β ≠ 0 := by
    intro h; rw [h, mul_zero] at hprod; exact one_ne_zero (neg_eq_zero.mp hprod.symm)
  have hs0 : s ≠ 0 := by
    intro h; apply hD0; rw [hs, h, mul_zero]
  have key := (binet a s α β hα hβ hαβ (p - 1)).1
  rw [ZMod.pow_card_sub_one_eq_one hα0, ZMod.pow_card_sub_one_eq_one hβ0, sub_self] at key
  have : ((lucasU a (p - 1) : ℤ) : ZMod p) = 0 := by
    rcases mul_eq_zero.mp key with h | h
    · exact h
    · exact absurd h hs0
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp this

theorem infinite (a : ℤ) (ha : 0 < a) : {p : ℕ | IsLucasWieferichPrime a p}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  set D := lucasDiscriminant a with hD
  have hDpos : 0 < D := by simp only [hD, lucasDiscriminant]; positivity
  have hk : 4 * D.natAbs ≠ 0 := by have : D.natAbs ≠ 0 := by omega
                                   omega
  obtain ⟨p, hp, hgt, hmod⟩ := Nat.exists_prime_gt_modEq_one (k := 4 * D.natAbs) (N + D.natAbs + 2) hk
  have hmod' : p % (4 * D.natAbs) = 1 := by
    have h1 : 1 % (4 * D.natAbs) = 1 := Nat.mod_eq_of_lt (by omega)
    rw [Nat.ModEq] at hmod; omega
  have hp2 : p ≠ 2 := by omega
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hJ : jacobiSym D p = 1 := by
    rw [jacobiSym.mod_right D hodd, hmod', jacobiSym.one_right]
  have hD0 : ((D : ℤ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro hdvd
    have := Int.le_of_dvd hDpos hdvd
    omega
  refine ⟨p, ⟨hp, ?_⟩, by omega⟩
  rw [← hD, hJ]
  have : ((p : ℤ) - 1).toNat = p - 1 := by omega
  rw [this]
  exact dvd_of_prime a p hp hp2 hD0 hJ

end GLucas

theorem OMA.solution : type_of% @OMA.S_wp_lucas_wieferich_prime.main := by
  intro a ha
  exact GLucas.infinite a ha
