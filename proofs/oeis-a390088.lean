import OMAStatements.S_oeis_a390088

-- Problem: A390088: a(n) is the least integer base b > 1 in which the representation of n uses only prime digits; or 0 if no such base exists.
-- Upstream: formal-conjectures statements/oeis-a390088.lean:0 (declaration OMA.S_oeis_a390088.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: a(k) = 0 iff no base 2 <= b <= k + 1 works. Bases that work: k + 1 for
-- k = 2, 3, 5, 7 (one prime digit); b = (k - 2)/2 for even k >= 8 (digits 2, 2) and
-- b = (k - 3)/2 for odd k >= 11 (digits 3, 2). For k = 0 the range is empty, and for
-- k = 1, 4, 6, 9 every base 2 <= b <= k + 1 is checked by computing the digits.

open OMA.S_oeis_a390088 in
theorem OMA.solution : type_of% @OMA.S_oeis_a390088.main := by
  have A0 : ∀ k : ℕ, a k = 0 ↔ ¬ ∃ b, 2 ≤ b ∧ b ≤ k + 1 ∧ PrimeDigits b k := by
    classical
    intro k
    unfold a
    by_cases h : ∃ b, 2 ≤ b ∧ b ≤ k + 1 ∧ PrimeDigits b k
    · rw [dif_pos h]
      have h2 := (Nat.find_spec h).1
      constructor
      · intro h0
        omega
      · intro hn
        exact absurd h hn
    · rw [dif_neg h]
      exact ⟨fun _ => h, fun _ => rfl⟩
  have one : ∀ b x : ℕ, x < b → x.Prime → PrimeDigits b x := by
    intro b x hxb hx
    unfold PrimeDigits
    rw [Nat.digits_of_lt b x hx.ne_zero hxb]
    intro d hd
    rw [List.mem_singleton] at hd
    rw [hd]
    exact hx
  have two : ∀ b x y : ℕ, 2 ≤ b → x < b → y < b → x.Prime → y.Prime →
      PrimeDigits b (x + b * y) := by
    intro b x y hb hxb hyb hx hy
    unfold PrimeDigits
    rw [Nat.digits_add b (by omega) x y hxb (Or.inl hx.ne_zero),
      Nat.digits_of_lt b y hy.ne_zero hyb]
    intro d hd
    rcases List.mem_cons.mp hd with h | h
    · rw [h]
      exact hx
    · rw [List.mem_singleton] at h
      rw [h]
      exact hy
  intro k
  rw [A0 k]
  constructor
  · intro hno
    by_contra hk
    apply hno
    rcases (by omega : k = 2 ∨ k = 3 ∨ k = 5 ∨ k = 7 ∨ (k % 2 = 0 ∧ 8 ≤ k) ∨
        (k % 2 = 1 ∧ 11 ≤ k)) with h | h | h | h | h | h
    · subst h
      exact ⟨3, by norm_num, by norm_num, one 3 2 (by norm_num) Nat.prime_two⟩
    · subst h
      exact ⟨4, by norm_num, by norm_num, one 4 3 (by norm_num) Nat.prime_three⟩
    · subst h
      exact ⟨6, by norm_num, by norm_num, one 6 5 (by norm_num) (by norm_num)⟩
    · subst h
      exact ⟨8, by norm_num, by norm_num, one 8 7 (by norm_num) (by norm_num)⟩
    · obtain ⟨b, rfl⟩ : ∃ b, k = 2 + b * 2 := ⟨(k - 2) / 2, by omega⟩
      exact ⟨b, by omega, by omega,
        two b 2 2 (by omega) (by omega) (by omega) Nat.prime_two Nat.prime_two⟩
    · obtain ⟨b, rfl⟩ : ∃ b, k = 3 + b * 2 := ⟨(k - 3) / 2, by omega⟩
      exact ⟨b, by omega, by omega,
        two b 3 2 (by omega) (by omega) (by omega) Nat.prime_three Nat.prime_two⟩
  · rintro (rfl | rfl | rfl | rfl | rfl)
    · rintro ⟨b, hb2, hb, _⟩
      omega
    · rintro ⟨b, hb2, hb, hok⟩
      unfold PrimeDigits at hok
      interval_cases b
      norm_num at hok
    · rintro ⟨b, hb2, hb, hok⟩
      unfold PrimeDigits at hok
      interval_cases b
      · norm_num at hok
      · norm_num at hok
      · norm_num at hok
      · norm_num at hok
    · rintro ⟨b, hb2, hb, hok⟩
      unfold PrimeDigits at hok
      interval_cases b
      · norm_num at hok
      · norm_num at hok
      · norm_num at hok
      · norm_num at hok
      · norm_num at hok
      · norm_num at hok
    · rintro ⟨b, hb2, hb, hok⟩
      unfold PrimeDigits at hok
      interval_cases b
      · norm_num at hok
      · norm_num at hok
      · norm_num at hok
      · norm_num at hok
      · norm_num at hok
      · norm_num at hok
      · norm_num at hok
      · norm_num at hok
      · norm_num at hok
