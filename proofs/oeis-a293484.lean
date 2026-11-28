import OMAStatements.S_oeis_a293484
import Mathlib

/-! Seventh-power residues, following @caa1982 (#23289).
The cyclic unit-group counts and prime-power cases are retained. Surjectivity
of a coprime power map now gives its full range directly, and the coprimality
calculation uses the prime-divisibility API without redundant reversals. -/

open OMA.S_oeis_a293484


theorem range_eq (n k : ℕ) :
    (Set.range fun x : (ZMod n)ˣ => x ^ k) = ((powMonoidHom k : (ZMod n)ˣ →* (ZMod n)ˣ).range : Set (ZMod n)ˣ) := by
  rw [MonoidHom.coe_range]; rfl

theorem card_cyc (n k : ℕ) [NeZero n] (hc : IsCyclic (ZMod n)ˣ) :
    Nat.card (Set.range fun x : (ZMod n)ˣ => x ^ k) = Nat.totient n / (Nat.totient n).gcd k := by
  rw [range_eq]
  have := IsCyclic.card_powMonoidHom_range (ZMod n)ˣ k
  rw [Nat.card_eq_fintype_card (α := (ZMod n)ˣ), ZMod.card_units_eq_totient] at this
  exact this

theorem card_cop (n k : ℕ) [NeZero n] (h : (Nat.totient n).Coprime k) :
    Nat.card (Set.range fun x : (ZMod n)ˣ => x ^ k) = Nat.totient n := by
  have h' : (Nat.card (ZMod n)ˣ).Coprime k := by
    simpa [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient] using h
  rw [Set.range_eq_univ.mpr h'.pow_left_bijective.surjective, Nat.card_univ,
    Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

theorem odd_pp (k p e : ℕ) (hk : k.Prime) (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e) :
    Nat.card (Set.range fun x : (ZMod (p ^ e))ˣ => x ^ k) =
      p ^ (e - 1) * (p - 1) / (p ^ (e - 1) * (p - 1)).gcd k := by
  have : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [card_cyc _ _ (ZMod.isCyclic_units_of_prime_pow p hp hp2 e), Nat.totient_prime_pow hp he]

theorem gcd_one (k p e : ℕ) (hk : k.Prime) (hp : p.Prime) (h0 : p % k ≠ 0) (h1 : p % k ≠ 1) :
    (p ^ (e - 1) * (p - 1)).gcd k = 1 := by
  apply (hk.coprime_iff_not_dvd.mpr ?_).symm
  intro hd
  rcases hk.dvd_mul.mp hd with h | h
  · exact h0 (Nat.mod_eq_zero_of_dvd (hk.dvd_of_dvd_pow h))
  · apply h1
    conv_lhs => rw [← Nat.sub_add_cancel hp.one_lt.le]
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd h]
    simp [Nat.mod_eq_of_lt hk.one_lt]

theorem gcd_k (k p e : ℕ) (hp : p.Prime) (h1 : p % k = 1) :
    (p ^ (e - 1) * (p - 1)).gcd k = k := by
  apply Nat.gcd_eq_right
  apply Dvd.dvd.mul_left
  have := Nat.dvd_sub_mod (n := k) p
  rwa [h1] at this

theorem two_pow (k e : ℕ) (hk : k.Prime) (hk2 : k ≠ 2) :
    Nat.card (Set.range fun x : (ZMod (2 ^ e))ˣ => x ^ k) = Nat.totient (2 ^ e) := by
  have : NeZero (2 ^ e) := ⟨by positivity⟩
  apply card_cop
  rcases Nat.eq_zero_or_pos e with rfl | he
  · simp
  · rw [Nat.totient_prime_pow Nat.prime_two he]
    simp only [Nat.add_one_sub_one, mul_one]
    apply Nat.Coprime.pow_left
    exact (Nat.coprime_primes Nat.prime_two hk).2 (Ne.symm hk2)

theorem OMA.solution : type_of% @OMA.S_oeis_a293484.main := by
  have k7 : Nat.Prime 7 := by norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    unfold a
    rw [two_pow 7 e k7 (by norm_num)]
    interval_cases e <;> simp
  · intro e he
    unfold a
    rw [two_pow 7 e k7 (by norm_num), Nat.totient_prime_pow Nat.prime_two he]
    norm_num
  · unfold a
    rw [odd_pp 7 7 1 k7 k7 (by norm_num) le_rfl]; norm_num
  · intro e he
    unfold a
    rw [odd_pp 7 7 e k7 k7 (by norm_num) (by omega)]
    obtain ⟨f, rfl⟩ : ∃ f, e = f + 2 := ⟨e - 2, by omega⟩
    rw [show f + 2 - 1 = f + 1 by omega, show f + 2 - 2 = f by omega]
    have hg : (7 ^ (f + 1) * (7 - 1)).gcd 7 = 7 := by
      apply Nat.gcd_eq_right
      exact Dvd.dvd.mul_right (dvd_pow_self 7 (by omega)) _
    rw [hg, pow_succ]
    rw [show 7 ^ f * 7 * (7 - 1) = (6 * 7 ^ f) * 7 by ring, Nat.mul_div_cancel _ (by norm_num)]
  · intro p e hp hmod he
    unfold a
    by_cases hp2 : p = 2
    · subst hp2
      rw [two_pow 7 e k7 (by norm_num), Nat.totient_prime_pow Nat.prime_two he]
      simp
    · rw [odd_pp 7 p e k7 hp hp2 he, gcd_one 7 p e k7 hp (by omega) (by omega), Nat.div_one, mul_comm]
  · intro p e hp hmod he
    unfold a
    have hp2 : p ≠ 2 := by rintro rfl; norm_num at hmod
    rw [odd_pp 7 p e k7 hp hp2 he, gcd_k 7 p e hp hmod, mul_comm]
