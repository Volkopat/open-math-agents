import OMAReductions.R_oeis_a293482_R1

-- Step oeis-a293482.R1.H1
-- Credit: @grp06
-- Source: OEIS A293482, https://oeis.org/A293482/internal
-- The reduction by @Ciphore isolates the count at powers of two.

open OMA.S_oeis_a293482

theorem OMA.solution : OMA.R_oeis_a293482_R1.H1 := by
  classical
  have count_of_coprime_totient (m : ℕ) [NeZero m]
      (h : Nat.Coprime (Nat.totient m) 5) : a m = Nat.totient m := by
    have hcard : Nat.card (ZMod m)ˣ = Nat.totient m := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    have hcoprime : Nat.Coprime (Nat.card (ZMod m)ˣ) 5 := by
      rw [hcard]
      exact h
    have hrange : Set.range (fun x : (ZMod m)ˣ => x ^ (5 : ℕ)) = Set.univ :=
      Set.range_eq_univ.mpr (Nat.Coprime.pow_left_bijective hcoprime).surjective
    unfold a
    rw [hrange, Nat.card_univ, hcard]
  have count_two_pow (e : ℕ) (he : 1 ≤ e) : a (2 ^ e) = 2 ^ (e - 1) := by
    letI : NeZero (2 ^ e : ℕ) := ⟨pow_ne_zero e (by decide : (2 : ℕ) ≠ 0)⟩
    have htotient : Nat.totient (2 ^ e) = 2 ^ (e - 1) := by
      simpa using Nat.totient_prime_pow Nat.prime_two he
    have hcoprime : Nat.Coprime (Nat.totient (2 ^ e)) 5 := by
      rw [htotient]
      exact Nat.Coprime.pow_left _ (by decide : Nat.Coprime 2 5)
    exact (count_of_coprime_totient (2 ^ e) hcoprime).trans htotient
  change (∀ e : ℕ, e ≤ 1 → a (2 ^ e) = 1) ∧
    (∀ e : ℕ, 1 ≤ e → a (2 ^ e) = 2 ^ (e - 1))
  refine ⟨?_, count_two_pow⟩
  intro e he
  have hexp : e = 0 ∨ e = 1 := by omega
  rcases hexp with rfl | rfl
  · simpa only [pow_zero, Nat.totient_one] using
      count_of_coprime_totient 1 (by rw [Nat.totient_one]; decide)
  · simpa only [Nat.sub_self, pow_zero] using count_two_pow 1 (by decide)
