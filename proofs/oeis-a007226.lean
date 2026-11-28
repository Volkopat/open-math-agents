import OMAStatements.S_oeis_a007226

-- Adjacent-ones test, one binary digit at a time: (2h+b) has no two adjacent 1 bits iff h has
-- none and, when b = 1, h is even.
theorem oeis_a007226_fib (h b : ℕ) (hb : b < 2) :
    (2 * h + b) &&& h = 0 ↔ (b = 1 → h % 2 = 0) ∧ h &&& (h / 2) = 0 := by
  have e : (2 * h + b) / 2 = h := by omega
  constructor
  · intro hz
    have key : ∀ i, ((2 * h + b).testBit i && h.testBit i) = false := by
      intro i
      rw [← Nat.testBit_and, hz, Nat.zero_testBit]
    constructor
    · intro hb1
      have k0 := key 0
      rw [Nat.testBit_zero, Nat.testBit_zero] at k0
      have h1 : (2 * h + b) % 2 = 1 := by omega
      simp [h1] at k0
      omega
    · apply Nat.zero_of_testBit_eq_false
      intro j
      have kj := key (j + 1)
      rw [← Nat.testBit_div_two, e] at kj
      rw [Nat.testBit_and, Nat.testBit_div_two]
      exact kj
  · rintro ⟨h0, hf⟩
    have key : ∀ j, (h.testBit j && h.testBit (j + 1)) = false := by
      intro j
      have h2 := congrArg (fun x => x.testBit j) hf
      simp only [Nat.testBit_and, Nat.testBit_div_two, Nat.zero_testBit] at h2
      exact h2
    apply Nat.zero_of_testBit_eq_false
    intro i
    rw [Nat.testBit_and]
    cases i with
    | zero =>
      rw [Nat.testBit_zero, Nat.testBit_zero]
      rcases Nat.lt_or_ge b 1 with hb0 | hb1
      · have h3 : ¬ (2 * h + b) % 2 = 1 := by omega
        rw [decide_eq_false h3, Bool.false_and]
      · have h4 : h % 2 = 0 := h0 (by omega)
        have h5 : ¬ h % 2 = 1 := by omega
        rw [decide_eq_false h5, Bool.and_false]
    | succ j =>
      rw [← Nat.testBit_div_two, e]
      exact key j

-- Lucas' theorem modulo 2, one binary digit at a time.
theorem oeis_a007226_lucas (n k : ℕ) :
    n.choose k % 2 = ((n % 2).choose (k % 2) * (n / 2).choose (k / 2)) % 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Choose.choose_modEq_choose_mod_mul_choose_div_nat

theorem oeis_a007226_zero (n k : ℕ) (hn : n % 2 = 0) (hk : k % 2 = 1) :
    n.choose k % 2 = 0 := by
  rw [oeis_a007226_lucas, hn, hk]
  simp

theorem oeis_a007226_keep (n k : ℕ) (h : ¬ (n % 2 = 0 ∧ k % 2 = 1)) :
    n.choose k % 2 = (n / 2).choose (k / 2) % 2 := by
  rw [oeis_a007226_lucas n k]
  have hn : n % 2 = 0 ∨ n % 2 = 1 := by omega
  have hk : k % 2 = 0 ∨ k % 2 = 1 := by omega
  rcases hn with hn | hn <;> rcases hk with hk | hk
  · rw [hn, hk]; simp
  · exact absurd ⟨hn, hk⟩ h
  · rw [hn, hk]; simp
  · rw [hn, hk]; simp

-- Parities of C(3n,n), C(3n+1,n) and C(3n+2,n+1), by induction on the binary digits of n.
theorem oeis_a007226_core (n : ℕ) :
    ((3 * n).choose n % 2 = 1 ↔ n &&& (n / 2) = 0) ∧
    ((3 * n + 1).choose n % 2 = 1 ↔ n % 2 = 0 ∧ n &&& (n / 2) = 0) ∧
    ((3 * n + 2).choose (n + 1) % 2 = 0) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd' n with ⟨h, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos h with rfl | hpos
      · refine ⟨by decide, by decide, by decide⟩
      · obtain ⟨hU, _, _⟩ := ih h (by omega)
        have e2 : 2 * h / 2 = h := by omega
        have f := oeis_a007226_fib h 0 (by omega)
        rw [Nat.add_zero] at f
        have fe : 2 * h &&& h = 0 ↔ h &&& (h / 2) = 0 :=
          ⟨fun hf => (f.mp hf).2, fun hf => f.mpr ⟨fun h01 => absurd h01 (by omega), hf⟩⟩
        refine ⟨?_, ?_, ?_⟩
        · have l := oeis_a007226_keep (3 * (2 * h)) (2 * h) (by omega)
          have e1 : 3 * (2 * h) / 2 = 3 * h := by omega
          rw [e1, e2] at l
          rw [l, e2, hU, fe]
        · have l := oeis_a007226_keep (3 * (2 * h) + 1) (2 * h) (by omega)
          have e1 : (3 * (2 * h) + 1) / 2 = 3 * h := by omega
          rw [e1, e2] at l
          rw [l, e2, hU, fe]
          constructor
          · intro hf; exact ⟨by omega, hf⟩
          · intro hf; exact hf.2
        · exact oeis_a007226_zero _ _ (by omega) (by omega)
    · obtain ⟨_, hW, hR⟩ := ih h (by omega)
      have e2 : (2 * h + 1) / 2 = h := by omega
      have f := oeis_a007226_fib h 1 (by omega)
      have fo : (2 * h + 1) &&& h = 0 ↔ h % 2 = 0 ∧ h &&& (h / 2) = 0 :=
        ⟨fun hf => ⟨(f.mp hf).1 rfl, (f.mp hf).2⟩, fun hf => f.mpr ⟨fun _ => hf.1, hf.2⟩⟩
      refine ⟨?_, ?_, ?_⟩
      · have l := oeis_a007226_keep (3 * (2 * h + 1)) (2 * h + 1) (by omega)
        have e1 : 3 * (2 * h + 1) / 2 = 3 * h + 1 := by omega
        rw [e1, e2] at l
        rw [l, e2, hW, fo]
      · have l := oeis_a007226_zero (3 * (2 * h + 1) + 1) (2 * h + 1) (by omega) (by omega)
        rw [l]
        constructor
        · intro hx; omega
        · intro hx; omega
      · have l := oeis_a007226_keep (3 * (2 * h + 1) + 2) (2 * h + 1 + 1) (by omega)
        have e1 : (3 * (2 * h + 1) + 2) / 2 = 3 * h + 2 := by omega
        have e3 : (2 * h + 1 + 1) / 2 = h + 1 := by omega
        rw [e1, e3] at l
        rw [l]
        exact hR

-- C(3j+1, j+1) is odd iff j is even with no two adjacent 1 bits.
theorem oeis_a007226_q (j : ℕ) :
    (3 * j + 1).choose (j + 1) % 2 = 1 ↔ j % 2 = 0 ∧ j &&& (j / 2) = 0 := by
  rcases Nat.even_or_odd' j with ⟨i, rfl | rfl⟩
  · obtain ⟨hU, _, _⟩ := oeis_a007226_core i
    have e2 : 2 * i / 2 = i := by omega
    have f := oeis_a007226_fib i 0 (by omega)
    rw [Nat.add_zero] at f
    have l := oeis_a007226_keep (3 * (2 * i) + 1) (2 * i + 1) (by omega)
    have e1 : (3 * (2 * i) + 1) / 2 = 3 * i := by omega
    have e3 : (2 * i + 1) / 2 = i := by omega
    rw [e1, e3] at l
    rw [l, e2, hU]
    constructor
    · intro hf; exact ⟨by omega, f.mpr ⟨fun h01 => absurd h01 (by omega), hf⟩⟩
    · intro hf; exact (f.mp hf.2).2
  · obtain ⟨_, _, hR⟩ := oeis_a007226_core i
    have l := oeis_a007226_keep (3 * (2 * i + 1) + 1) (2 * i + 1 + 1) (by omega)
    have e1 : (3 * (2 * i + 1) + 1) / 2 = 3 * i + 2 := by omega
    have e3 : (2 * i + 1 + 1) / 2 = i + 1 := by omega
    rw [e1, e3] at l
    rw [l, hR]
    constructor
    · intro hx; omega
    · intro hx; omega

-- C(3n, n+1) is odd iff n is odd with no two adjacent 1 bits.
theorem oeis_a007226_p (n : ℕ) :
    (3 * n).choose (n + 1) % 2 = 1 ↔ n % 2 = 1 ∧ n &&& (n / 2) = 0 := by
  rcases Nat.even_or_odd' n with ⟨j, rfl | rfl⟩
  · have l := oeis_a007226_zero (3 * (2 * j)) (2 * j + 1) (by omega) (by omega)
    rw [l]
    constructor
    · intro hx; omega
    · intro hx; omega
  · have hQ := oeis_a007226_q j
    have e2 : (2 * j + 1) / 2 = j := by omega
    have f := oeis_a007226_fib j 1 (by omega)
    have l := oeis_a007226_keep (3 * (2 * j + 1)) (2 * j + 1 + 1) (by omega)
    have e1 : 3 * (2 * j + 1) / 2 = 3 * j + 1 := by omega
    have e3 : (2 * j + 1 + 1) / 2 = j + 1 := by omega
    rw [e1, e3] at l
    rw [l, e2, hQ]
    constructor
    · intro hf; exact ⟨by omega, f.mpr ⟨fun _ => hf.1, hf.2⟩⟩
    · intro hf; exact ⟨(f.mp hf.2).1 rfl, (f.mp hf.2).2⟩

-- a(n) = 2 C(3n,n)/(n+1) = 2 C(3n,n) - C(3n,n+1), so it has the parity of C(3n,n+1).
theorem oeis_a007226_parity (n : ℕ) :
    OMA.S_oeis_a007226.a n % 2 = (3 * n).choose (n + 1) % 2 := by
  have hD := Nat.choose_succ_right_eq (3 * n) n
  have e : 3 * n - n = 2 * n := by omega
  rw [e] at hD
  have hle : (3 * n).choose (n + 1) ≤ 2 * (3 * n).choose n := by
    have h1 : (3 * n).choose (n + 1) * (n + 1) ≤ 2 * (3 * n).choose n * (n + 1) := by
      have h2 : 2 * (3 * n).choose n * (n + 1) =
          (3 * n).choose n * (2 * n) + 2 * (3 * n).choose n := by ring
      omega
    exact Nat.le_of_mul_le_mul_right h1 (by omega)
  obtain ⟨E, hE⟩ : ∃ E, 2 * (3 * n).choose n = (3 * n).choose (n + 1) + E :=
    ⟨2 * (3 * n).choose n - (3 * n).choose (n + 1), by omega⟩
  have h3 : ((3 * n).choose (n + 1) + E) * (n + 1) = 2 * (3 * n).choose n * (n + 1) := by
    rw [← hE]
  have h5 : (3 * n).choose (n + 1) * (n + 1) + E * (n + 1) =
      (3 * n).choose n * (2 * n) + 2 * (3 * n).choose n := by
    rw [← Nat.add_mul, h3]
    ring
  have h4 : 2 * (3 * n).choose n = E * (n + 1) := by omega
  have ha : OMA.S_oeis_a007226.a n = E := by
    unfold OMA.S_oeis_a007226.a
    exact Nat.div_eq_of_eq_mul_left (by omega) h4
  rw [ha]
  omega

theorem OMA.solution : type_of% @OMA.S_oeis_a007226.main := by
  intro n
  unfold OMA.S_oeis_a007226.IsOddFibbinary
  rw [oeis_a007226_parity, oeis_a007226_p, Nat.land_eq]
