import OMAStatements.S_oeis_a137328
import Mathlib

/-!
# A137328: the conjecture fails at `p = 2`

For `n ≥ 1` the greatest `k` with `primorialFirst k ≤ prime n` is at least `1`, so the
primorial subtracted is even and positive. If `a n = 2` then `prime n` is an even prime
that is at least `4`, which is impossible. Hence `2` never appears.
-/

open OMA.S_oeis_a137328 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a137328.main) := by
  intro h
  obtain ⟨n, _, hn⟩ := h 2 Nat.prime_two
  have hp : (prime n).Prime := by
    unfold prime
    exact Nat.prime_nth_prime _
  have hpow : ∀ k, 2 ^ k ≤ primorialFirst k := by
    intro k
    unfold primorialFirst
    have := Finset.pow_card_le_prod (Finset.range k) (fun i => Nat.nth Nat.Prime i) 2
      (fun i _ => (Nat.prime_nth_prime i).two_le)
    simpa using this
  have hmem1 : (1 : ℕ) ∈ {k : ℕ | primorialFirst k ≤ prime n} := by
    simp only [Set.mem_setOf_eq, primorialFirst, Finset.prod_range_one, Nat.nth_prime_zero_eq_two]
    exact hp.two_le
  have hbdd : BddAbove {k : ℕ | primorialFirst k ≤ prime n} := by
    refine ⟨prime n, fun k hk => ?_⟩
    have h1 : primorialFirst k ≤ prime n := hk
    have h2 := hpow k
    have h3 : k < 2 ^ k := Nat.lt_two_pow_self
    omega
  have hK : greatestK n ∈ {k : ℕ | primorialFirst k ≤ prime n} :=
    Nat.sSup_mem ⟨1, hmem1⟩ hbdd
  have hK1 : 1 ≤ greatestK n := le_csSup hbdd hmem1
  have hle : primorialFirst (greatestK n) ≤ prime n := hK
  have hdvd : 2 ∣ primorialFirst (greatestK n) := by
    unfold primorialFirst
    have h0 : (0 : ℕ) ∈ Finset.range (greatestK n) := Finset.mem_range.mpr hK1
    have := Finset.dvd_prod_of_mem (fun i => Nat.nth Nat.Prime i) h0
    simpa [Nat.nth_prime_zero_eq_two] using this
  have hge := hpow (greatestK n)
  have hpos : 0 < 2 ^ greatestK n := by positivity
  have ha : prime n - primorialFirst (greatestK n) = 2 := hn
  have hd2 : 2 ∣ prime n := by omega
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hd2
  omega
