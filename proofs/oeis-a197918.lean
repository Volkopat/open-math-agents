import OMAStatements.S_oeis_a197918

namespace OMA.S_oeis_a197918


/-- XOR with a number below 32 only touches the low five bits. -/
lemma xor_split (p q : ℕ) (hq : q < 32) : p ^^^ q = 32 * (p / 32) + (p % 32 ^^^ q) := by
  have h := Nat.div_add_mod (p ^^^ q) 32
  have hdiv : (p ^^^ q) / 32 = p / 32 := by
    have := Nat.xor_div_two_pow (a := p) (b := q) (n := 5)
    norm_num at this
    rw [this, Nat.div_eq_of_lt hq, Nat.xor_zero]
  have hmod : (p ^^^ q) % 32 = p % 32 ^^^ q := by
    have := Nat.xor_mod_two_pow (a := p) (b := q) (n := 5)
    norm_num at this
    rw [this, Nat.mod_eq_of_lt hq]
  rw [hdiv, hmod] at h
  exact h.symm

/-- The check over the low five bits. -/
lemma low_bits (r : ℕ) (hr : r < 32) : r % 2 = 1 → (2 ≤ r → r ^^^ 2 ≠ r - 2) →
    (5 ≤ r → r ^^^ 5 ≠ r - 5) → (17 ≤ r → r ^^^ 17 ≠ r - 17) → r ^^^ 22 = r + 22 := by
  interval_cases r <;> decide

/-- The conjecture of the entry: every term other than 2, 5, 17 satisfies `p XOR 22 = p + 22`. -/
theorem conjecture (p : ℕ) (hp : IsTerm p) (h2 : p ≠ 2) (h5 : p ≠ 5) (h17 : p ≠ 17) :
    p ^^^ 22 = p + 22 := by
  obtain ⟨hprime, -, hxor⟩ := hp
  have hodd : p % 2 = 1 := (hprime.eq_two_or_odd).resolve_left h2
  have hgt : 17 < p := by
    by_contra hle
    have hle' : p ≤ 17 := by omega
    interval_cases p <;> first
      | omega
      | exact hxor 2 Nat.prime_two (by norm_num) (by decide)
      | exact hxor 5 (by norm_num) (by norm_num) (by decide)
      | exact absurd hprime (by norm_num)
  have e2 := hxor 2 Nat.prime_two (by omega)
  have e5 := hxor 5 (by norm_num) (by omega)
  have e17 := hxor 17 (by norm_num) (by omega)
  rw [xor_split p 2 (by norm_num)] at e2
  rw [xor_split p 5 (by norm_num)] at e5
  rw [xor_split p 17 (by norm_num)] at e17
  rw [xor_split p 22 (by norm_num)]
  have hdm := Nat.div_add_mod p 32
  have hr : p % 32 < 32 := Nat.mod_lt _ (by norm_num)
  have key := low_bits (p % 32) hr (by omega) (fun h => by omega) (fun h => by omega)
    (fun h => by omega)
  omega

/-- Controls: the listed terms 41 and 73 are terms, and 13 is not. -/
example : (41 : ℕ) ^^^ 22 = 41 + 22 ∧ (73 : ℕ) ^^^ 22 = 73 + 22 ∧ (13 : ℕ) ^^^ 5 = 13 - 5 := by
  decide

end OMA.S_oeis_a197918

theorem OMA.solution : type_of% @OMA.S_oeis_a197918.main :=
  fun p hp h2 h5 h17 => OMA.S_oeis_a197918.conjecture p hp h2 h5 h17
