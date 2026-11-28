import FormalConjectures.OEIS.«250131»
import Mathlib.Data.Nat.Digits.Div

/-!
# Finite cutoff for Shevelev's sieve conjecture

Multiplying by three twice adds at most one decimal digit. For exponents
at least two, nine divides the digit sum. Together they imply `2 * b n < n`
when `n ≥ 3`. If `b n` is composite, its least prime factor `p` therefore
satisfies `2 * p ^ 2 < n`. Any occurrence of `p` by that index rules out `n`
as a sieve survivor.

`H1` is the finite prime-occurrence check below the cutoff. `H2` is the
remaining question about composite terms beyond the cutoff whose least
prime factor is at least the cutoff.
-/

namespace OMA.R_OeisA250131_conjecture_1_R2

open Nat OeisA250131

/-- The primes below the cutoff appear by the latest index at which they
could be needed to remove a composite sieve term. -/
def H1 : Prop :=
  ∀ p : ℕ, p.Prime → p < 29947 →
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ 2 * p ^ 2 ∧ b k = p

/-- The remaining composites have an earlier nontrivial divisor. -/
def H2 : Prop :=
  ∀ n : ℕ, 2 * (29947 : ℕ) ^ 2 < n → 1 < b n → ¬ (b n).Prime →
    29947 ≤ (b n).minFac → ∃ k : ℕ, 1 ≤ k ∧ k < n ∧ b k ≠ 1 ∧ b k ∣ b n

theorem normalized_digits_le (m : ℕ) (hm : 2 ≤ m) : a m ≤ (m + 1) / 2 := by
  let L := (m + 1) / 2
  have hL : 0 < L := by dsimp [L]; omega
  have hmL : m ≤ 2 * L := by dsimp [L]; omega
  have hpow : 3 ^ m < (10 : ℕ) ^ L := calc
    3 ^ m ≤ (3 : ℕ) ^ (2 * L) := pow_le_pow_right' (by decide) hmL
    _ = 9 ^ L := by rw [pow_mul]; norm_num
    _ < 10 ^ L := Nat.pow_lt_pow_left (by decide : (9 : ℕ) < 10) hL.ne'
  let ds := Nat.digits 10 (3 ^ m)
  have hlen : ds.length ≤ L := (Nat.digits_length_le_iff (by decide) _).2 hpow
  have hsum : ds.sum ≤ 9 * ds.length := by
    simpa [nsmul_eq_mul, mul_comm] using
      (List.sum_le_card_nsmul ds 9 (fun d hd =>
        Nat.le_of_lt_succ (Nat.digits_lt_base (by decide : 1 < 10) hd)))
  change ds.sum / (3 ^ padicValNat 3 ds.sum * 2 ^ padicValNat 2 ds.sum) ≤ L
  by_cases hz : ds.sum = 0
  · rw [hz, Nat.zero_div]; exact Nat.zero_le _
  have hdiv : (3 : ℕ) ^ 2 ∣ ds.sum := (Nat.nine_dvd_iff _).1 (pow_dvd_pow 3 hm)
  have hval : 2 ≤ padicValNat 3 ds.sum :=
    (Nat.pow_dvd_iff_le_padicValNat (by decide) hz).1 hdiv
  have h9 : 9 ≤ (3 : ℕ) ^ padicValNat 3 ds.sum :=
    pow_le_pow_right' (by decide : 1 ≤ (3 : ℕ)) hval
  have htwo : 1 ≤ (2 : ℕ) ^ padicValNat 2 ds.sum :=
    Nat.succ_le_of_lt (pow_pos (by decide : 0 < (2 : ℕ)) _)
  have hden : 9 ≤ 3 ^ padicValNat 3 ds.sum * 2 ^ padicValNat 2 ds.sum :=
    h9.trans (by simpa using Nat.mul_le_mul_left (3 ^ padicValNat 3 ds.sum) htwo)
  exact Nat.div_le_of_le_mul ((hsum.trans (Nat.mul_le_mul_left 9 hlen)).trans
    (Nat.mul_le_mul_right L hden))

theorem twice_b_lt {n : ℕ} (hn : 3 ≤ n) : 2 * b n < n := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 3 := ⟨n - 3, by omega⟩
  change 2 * a (m + 1) < m + 3
  by_cases hm : m = 0
  · subst m; norm_num [OeisA250131.a_1]
  · have h := normalized_digits_le (m + 1) (by omega)
    omega

theorem main : H1 → H2 → type_of% @OeisA250131.conjecture_1 := by
  intro hsmall hlarge n hn
  rcases hn with ⟨hn₁, hn₀, hprevious⟩
  by_cases hn₃ : n < 3
  · interval_cases n <;> decide
  have hpos : 0 < b n := by
    by_contra! hz
    have he : b n = 0 := by omega
    exact (hprevious 1 ⟨by decide, by omega, by decide⟩) (by rw [he]; exact dvd_zero _)
  by_contra hc
  let p := (b n).minFac
  have hp : p.Prime := Nat.minFac_prime hn₀
  have hsq : p ^ 2 ≤ b n := Nat.minFac_sq_le_self hpos hc
  have hbound := twice_b_lt (by omega : 3 ≤ n)
  by_cases hpSmall : p < 29947
  · obtain ⟨k, hk₁, hk₂, hbk⟩ := hsmall p hp hpSmall
    have hkn : k < n := by omega
    exact (hprevious k ⟨hk₁, hkn, by rw [hbk]; exact hp.ne_one⟩)
      (by rw [hbk]; exact Nat.minFac_dvd _)
  · have hcut : 29947 ≤ p := by omega
    have hcutSq : (29947 : ℕ) ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hcut 2
    have hnCut : 2 * (29947 : ℕ) ^ 2 < n := by omega
    obtain ⟨k, hk₁, hkn, hk₀, hdiv⟩ := hlarge n hnCut (by omega) hc hcut
    exact (hprevious k ⟨hk₁, hkn, hk₀⟩) hdiv

end OMA.R_OeisA250131_conjecture_1_R2
