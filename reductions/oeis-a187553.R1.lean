import OMAStatements.S_oeis_a187553
import Mathlib

/-!
# Prime digit-square sums near their decimal mean

At digit length floor(2n/57), the mean of the sum of the squared digits
differs from n by less than one digit mean. A quantitative lower bound
on the number of matching primes therefore gives a route to the tail.
The two exceptional values are excluded directly.
-/

namespace OMA.R_oeis_a187553_R1

open OMA.S_oeis_a187553 Finset

private lemma small_digits (ds : List ℕ)
    (h : (ds.map (fun d => d^2)).sum ≤ 3) :
    ds.sum = (ds.map (fun d => d^2)).sum := by
  induction ds with
  | nil => rfl
  | cons d rest ih =>
    simp only [List.map_cons,List.sum_cons] at h ⊢
    have hd : d ≤ 1 := by
      by_contra! greater
      have bound := Nat.pow_le_pow_left (show 2 ≤ d by omega) 2
      omega
    have same : d^2=d := by interval_cases d <;> rfl
    rw [same,ih (by omega)]

private lemma value_zero (ds : List ℕ) (h : ds.sum=0) : Nat.ofDigits 10 ds=0 := by
  induction ds with
  | nil => rfl
  | cons d rest ih =>
    simp only [List.sum_cons] at h
    rw [Nat.ofDigits_cons,ih (by omega)]
    omega

theorem exceptions (p : ℕ) (hp : p.Prime) : digitSquareSum p ≠ 1 ∧ digitSquareSum p ≠ 3 := by
  have old := Nat.ofDigits_digits 10 p
  constructor
  · intro one
    have hs : (Nat.digits 10 p).sum=1 := (small_digits _ (by change digitSquareSum p ≤ 3; omega)).trans one
    cases ds : Nat.digits 10 p with
    | nil => simp [ds] at hs
    | cons d rest =>
      rw [ds,List.sum_cons] at hs
      rw [ds,Nat.ofDigits_cons] at old
      by_cases hd : d=0
      · have div : 10 ∣ p := ⟨Nat.ofDigits 10 rest,by simpa [hd] using old.symm⟩
        have two : 2=p := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
          (dvd_trans (by decide : 2 ∣ 10) div)
        rw [←two] at div
        exact (by decide : ¬10 ∣ 2) div
      · rw [value_zero rest (by omega)] at old
        have := hp.two_le
        omega
  · intro three
    have hs : (Nat.digits 10 p).sum=3 := (small_digits _ (by change digitSquareSum p ≤ 3; omega)).trans three
    have div : 3 ∣ p := (Nat.three_dvd_iff p).mpr (by simpa only [hs] using (dvd_refl 3))
    have eq : 3=p := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp div
    rw [←eq] at three
    exact (by decide : digitSquareSum 3 ≠ 3) three

/-- Check every target from 4 through 1024 with an explicit prime. -/
def H1 : Prop :=
  ∀ n : ℕ, 4 ≤ n → n ≤ 1024 → ∃ p : ℕ, p.Prime ∧ digitSquareSum p = n

/-- A lower bound on the fraction of primes at the central digit length. -/
def H2 : Prop :=
  ∀ n : ℕ, 1024 < n →
    let P := Nat.primesLE (10 ^ (2*n/57))
    P.card ≤ (16*n) * (P.filter (fun p => digitSquareSum p = n)).card

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a187553.main := by
  intro small counts n positive
  constructor
  · rintro ⟨p, prime, rfl⟩
    exact exceptions p prime
  · rintro ⟨one, three⟩
    by_cases two : n = 2
    · subst n
      exact ⟨11, by decide, by decide +kernel⟩
    by_cases finite : n ≤ 1024
    · exact small n (by omega) finite
    let P := Nat.primesLE (10 ^ (2*n/57))
    have h : P.card ≤ (16*n) * (P.filter (fun p => digitSquareSum p = n)).card :=
      counts n (by omega)
    have powBound : 2 ≤ 10 ^ (2*n/57) := calc
      2 ≤ 10 ^ 1 := by decide
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
    have twoIn : 2 ∈ P := Nat.mem_primesLE.mpr ⟨powBound, Nat.prime_two⟩
    have enough : 0 < P.card := Finset.card_pos.mpr ⟨2, twoIn⟩
    have hit : 0 < (P.filter (fun p => digitSquareSum p = n)).card := by
      by_contra! empty
      rw [Nat.eq_zero_of_le_zero empty, Nat.mul_zero] at h
      omega
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hit
    obtain ⟨pr, value⟩ := Finset.mem_filter.mp hp
    exact ⟨p, Nat.prime_of_mem_primesLE pr, value⟩

end OMA.R_oeis_a187553_R1
