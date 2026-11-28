import OMAStatements.S_oeis_a187941
import Mathlib

/-!
# OEIS A187941: if the least number with exactly `n` even divisors is `2^n`, then `n` is prime or `1`

`2^n` has exactly `n` even divisors. If `n = r s` with `r, s ≥ 2`, the number
`m = 2^r · 3^(s-1)` also has exactly `r s` even divisors (the even divisors of `2 M` are the
doubles of the divisors of `M`, and `M = 2^(r-1) · 3^(s-1)` has `r s` divisors), and

  `m = 2^r · 3^(s-1) < 2^r · 4^(s-1) = 2^(r + 2(s-1)) ≤ 2^(r s)`.

So for composite `n` the least such number is smaller than `2^n`.
-/

open OMA.S_oeis_a187941

namespace OMA.A187941

/-- The even divisors of `2 M` are the doubles of the divisors of `M`. -/
lemma even_divisors (M : ℕ) (hM : 0 < M) :
    (2 * M).divisors.filter (fun d => 2 ∣ d) = M.divisors.image (fun d => 2 * d) := by
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_image]
  constructor
  · rintro ⟨⟨hd, -⟩, ⟨c, rfl⟩⟩
    exact ⟨c, ⟨Nat.dvd_of_mul_dvd_mul_left (by norm_num) hd, hM.ne'⟩, rfl⟩
  · rintro ⟨c, ⟨hc, -⟩, rfl⟩
    exact ⟨⟨Nat.mul_dvd_mul_left 2 hc, by omega⟩, Dvd.intro _ rfl⟩

/-- `2 M` has as many even divisors as `M` has divisors. -/
lemma evenDivisorCount_two_mul (M : ℕ) (hM : 0 < M) :
    evenDivisorCount (2 * M) = M.divisors.card := by
  unfold evenDivisorCount
  rw [even_divisors M hM]
  exact Finset.card_image_of_injective _ fun a b h => Nat.eq_of_mul_eq_mul_left (by norm_num) h

/-- A prime power `p^k` has `k + 1` divisors. -/
lemma card_divisors_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) : (p ^ k).divisors.card = k + 1 := by
  rw [Nat.divisors_prime_pow hp, Finset.card_map, Finset.card_range]

/-- For `r, s ≥ 2` some number below `2^(r s)` has exactly `r s` even divisors. -/
lemma small (r s : ℕ) (hr : 2 ≤ r) (hs : 2 ≤ s) : a (r * s) < 2 ^ (r * s) := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  -- `M = 2^r' · 3^s'` has `(r' + 1)(s' + 1)` divisors
  have hMpos : 0 < 2 ^ r' * 3 ^ s' := by positivity
  have hcard : (2 ^ r' * 3 ^ s').divisors.card = (r' + 1) * (s' + 1) := by
    rw [Nat.Coprime.card_divisors_mul (Nat.Coprime.pow _ _ (by norm_num)),
      card_divisors_prime_pow Nat.prime_two, card_divisors_prime_pow Nat.prime_three]
  have hmem : 0 < 2 * (2 ^ r' * 3 ^ s') ∧
      evenDivisorCount (2 * (2 ^ r' * 3 ^ s')) = (r' + 1) * (s' + 1) :=
    ⟨by positivity, by rw [evenDivisorCount_two_mul _ hMpos, hcard]⟩
  have hle : a ((r' + 1) * (s' + 1)) ≤ 2 * (2 ^ r' * 3 ^ s') := Nat.sInf_le hmem
  -- size comparison
  have h3 : 3 ^ s' < 4 ^ s' := Nat.pow_lt_pow_left (by norm_num) (by omega)
  have h4 : (4 : ℕ) ^ s' = 2 ^ (2 * s') := by rw [pow_mul]; norm_num
  have hexp : r' + 1 + 2 * s' ≤ (r' + 1) * (s' + 1) := by nlinarith
  have h5 : 2 ^ (r' + 1 + 2 * s') ≤ 2 ^ ((r' + 1) * (s' + 1)) :=
    Nat.pow_le_pow_right (by norm_num) hexp
  have h6 : 2 * (2 ^ r' * 3 ^ s') < 2 ^ (r' + 1 + 2 * s') := by
    rw [pow_add, pow_succ, ← h4]
    have : 0 < 2 ^ r' := by positivity
    nlinarith
  omega

end OMA.A187941

open OMA.A187941 in
theorem OMA.solution : type_of% @OMA.S_oeis_a187941.main := by
  intro n hn han
  by_contra hcon
  have hnp : ¬ n.Prime := fun h => hcon (Or.inl h)
  have hn1 : n ≠ 1 := fun h => hcon (Or.inr h)
  obtain ⟨r, ⟨s, rfl⟩, hr2, hrlt⟩ := Nat.exists_dvd_of_not_prime2 (by omega) hnp
  have hs2 : 2 ≤ s := by
    by_contra hs
    have : s = 0 ∨ s = 1 := by omega
    rcases this with rfl | rfl <;> omega
  have := small r s hr2 hs2
  omega
