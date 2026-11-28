import OMAStatements.S_oeis_a158460

-- Problem: A158460, prime(k-1) and prime(k) are twin primes ending in 1 and 3.
-- Credit: @ShoQo
-- Proof: with p = prime(k-1), prime(k+1) = p + 6 and p + 5 = s^2, so p ≡ s^2 - 5 (mod 10).
-- Squares end in 0, 1, 4, 5, 6, 9; p odd and not a multiple of 5, and p + 6 not a multiple
-- of 5, leave p ≡ 1 (mod 10). prime(k) is the only prime strictly between p and p + 6; it is
-- odd, and p + 4 ≡ 5 (mod 10) is a multiple of 5 above 5, so prime(k) = p + 2 ≡ 3 (mod 10).

open OMA.S_oeis_a158460

namespace OMA_A158460_Proof

lemma q_prime (i : ℕ) : (Nat.nth Nat.Prime i).Prime := Nat.prime_nth_prime i

lemma q_strictMono : StrictMono (Nat.nth Nat.Prime) := Nat.nth_strictMono Nat.infinite_setOfPred_prime

/-- A prime strictly between q i and q (i+2) is q (i+1). -/
lemma between {i x : ℕ} (hx : x.Prime) (h1 : Nat.nth Nat.Prime i < x)
    (h2 : x < Nat.nth Nat.Prime (i + 2)) : x = Nat.nth Nat.Prime (i + 1) := by
  have hc := Nat.nth_count hx
  set j := Nat.count Nat.Prime x
  rw [← hc] at h1 h2 ⊢
  have hij : i < j := q_strictMono.lt_iff_lt.1 h1
  have hji : j < i + 2 := q_strictMono.lt_iff_lt.1 h2
  rw [show j = i + 1 by omega]

lemma not_five_dvd {p : ℕ} (hp : p.Prime) (h5 : p ≠ 5) : p % 5 ≠ 0 := by
  intro h
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).1 (Nat.dvd_of_mod_eq_zero h)
  omega

lemma odd_of_ne_two {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : p % 2 = 1 :=
  Nat.odd_iff.1 (hp.odd_of_ne_two h2)

lemma sq_mod_ten (s : ℕ) : s ^ 2 % 10 = 0 ∨ s ^ 2 % 10 = 1 ∨ s ^ 2 % 10 = 4 ∨
    s ^ 2 % 10 = 5 ∨ s ^ 2 % 10 = 6 ∨ s ^ 2 % 10 = 9 := by
  rw [Nat.pow_mod]
  have : s % 10 < 10 := Nat.mod_lt _ (by norm_num)
  interval_cases (s % 10) <;> simp

end OMA_A158460_Proof

open OMA_A158460_Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a158460.main := by
  intro k hk ⟨s, hs⟩ heq
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 2 := ⟨k - 2, by omega⟩
  simp only [prime, show i + 2 - 1 = i + 1 by omega,
    show i + 2 + 1 - 1 = i + 2 by omega, Nat.add_sub_cancel] at hs heq ⊢
  set a := Nat.nth Nat.Prime i
  set b := Nat.nth Nat.Prime (i + 1)
  set c := Nat.nth Nat.Prime (i + 2)
  have ha := q_prime i
  have hb := q_prime (i + 1)
  have hc := q_prime (i + 2)
  have hab : a < b := q_strictMono (by omega)
  have hbc : b < c := q_strictMono (by omega)
  have hca : c = a + 6 := by omega
  have ha2 := ha.two_le
  -- a ≡ 1 (mod 10)
  have hsq := sq_mod_ten s
  have ha_ne2 : a ≠ 2 := by rintro h; rw [h] at hs; rcases hsq with h' | h' | h' | h' | h' | h' <;> omega
  have ha_ne5 : a ≠ 5 := by
    rintro h; rw [h] at hs
    rcases Nat.lt_or_ge s 4 with h' | h'
    · interval_cases s <;> omega
    · nlinarith
  have hao := odd_of_ne_two ha ha_ne2
  have ha5 := not_five_dvd ha ha_ne5
  have hc5 := not_five_dvd hc (by omega)
  have ha10 : a % 10 = 1 := by rcases hsq with h' | h' | h' | h' | h' | h' <;> omega
  -- b = a + 2
  have hbo := odd_of_ne_two hb (by omega)
  have hb5 := not_five_dvd hb (by omega)
  have hb2 : b = a + 2 := by omega
  exact ⟨hb2, ha10, by omega⟩
