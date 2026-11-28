import OMAStatements.S_oeis_a203298

/-!
Proof of OEIS A203298: stepping a(n) and the prefix sum S(n) = sum_{i=1..n} t(i) by 2
establishes the quartic closed forms for even and odd n, from which Barker's order-8
linear recurrence follows identically by parity.
-/

private def S (n : ℕ) : ℕ := ∑ i ∈ Finset.Icc 1 n, OMA.S_oeis_a203298.t i

private lemma a_succ (n : ℕ) :
    OMA.S_oeis_a203298.a (n + 1) = OMA.S_oeis_a203298.a n + S n * OMA.S_oeis_a203298.t (n + 1) := by
  unfold OMA.S_oeis_a203298.a S
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
  have hico : Finset.Ico 1 (n + 1) = Finset.Icc 1 n := by
    ext x
    simp [Finset.mem_Ico, Finset.mem_Icc]
  rw [hico, ← Finset.sum_mul]

private lemma S_succ (n : ℕ) : S (n + 1) = S n + OMA.S_oeis_a203298.t (n + 1) := by
  unfold S
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]

private lemma t_two_mul_add_one (k : ℕ) : OMA.S_oeis_a203298.t (2 * k + 1) = k + 1 := by
  unfold OMA.S_oeis_a203298.t
  omega

private lemma t_two_mul_add_two (k : ℕ) : OMA.S_oeis_a203298.t (2 * k + 2) = k + 2 := by
  unfold OMA.S_oeis_a203298.t
  omega

private lemma S_two_mul (k : ℕ) : S (2 * k) = k * (k + 2) := by
  induction k with
  | zero =>
    unfold S
    simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega, S_succ, S_succ, ih,
      show 2 * k + 1 + 1 = 2 * k + 2 by omega, t_two_mul_add_one, t_two_mul_add_two]
    ring

private lemma S_two_mul_add_one (k : ℕ) : S (2 * k + 1) = k * (k + 3) + 1 := by
  rw [S_succ, S_two_mul, t_two_mul_add_one]
  ring

private lemma a_two_mul (k : ℕ) :
    (OMA.S_oeis_a203298.a (2 * k) : ℚ) =
      (6 * ((2 * k : ℕ) : ℚ) ^ 4 + 40 * ((2 * k : ℕ) : ℚ) ^ 3 +
        48 * ((2 * k : ℕ) : ℚ) ^ 2 - 112 * ((2 * k : ℕ) : ℚ)) / 192 := by
  induction k with
  | zero =>
    unfold OMA.S_oeis_a203298.a
    norm_num
  | succ k ih =>
    have hstep : OMA.S_oeis_a203298.a (2 * (k + 1)) =
        OMA.S_oeis_a203298.a (2 * k) +
          S (2 * k) * OMA.S_oeis_a203298.t (2 * k + 1) +
          S (2 * k + 1) * OMA.S_oeis_a203298.t (2 * k + 2) := by
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega, a_succ, a_succ,
        show 2 * k + 1 + 1 = 2 * k + 2 by omega]
    rw [hstep, S_two_mul, S_two_mul_add_one, t_two_mul_add_one, t_two_mul_add_two]
    push_cast
    rw [ih]
    push_cast
    ring

private lemma a_two_mul_add_one (k : ℕ) :
    (OMA.S_oeis_a203298.a (2 * k + 1) : ℚ) =
      (6 * ((2 * k + 1 : ℕ) : ℚ) ^ 4 + 40 * ((2 * k + 1 : ℕ) : ℚ) ^ 3 +
        36 * ((2 * k + 1 : ℕ) : ℚ) ^ 2 - 136 * ((2 * k + 1 : ℕ) : ℚ) + 54) / 192 := by
  rw [a_succ, S_two_mul, t_two_mul_add_one]
  push_cast
  rw [a_two_mul k]
  push_cast
  ring

theorem OMA.solution : type_of% @OMA.S_oeis_a203298.main := by
  have hEven : ∀ n : ℕ, Even n →
      (OMA.S_oeis_a203298.a n : ℚ) =
        (6 * (n : ℚ) ^ 4 + 40 * (n : ℚ) ^ 3 + 48 * (n : ℚ) ^ 2 - 112 * (n : ℚ)) / 192 := by
    rintro n ⟨k, rfl⟩
    rw [show k + k = 2 * k by omega]
    exact a_two_mul k
  have hOdd : ∀ n : ℕ, Odd n →
      (OMA.S_oeis_a203298.a n : ℚ) =
        (6 * (n : ℚ) ^ 4 + 40 * (n : ℚ) ^ 3 + 36 * (n : ℚ) ^ 2 - 136 * (n : ℚ) + 54) / 192 := by
    rintro n ⟨k, rfl⟩
    exact a_two_mul_add_one k
  refine ⟨fun n _ hn => hEven n hn, fun n _ hn => hOdd n hn, ?_⟩
  intro n hn
  have hq : ((OMA.S_oeis_a203298.a n : ℤ) : ℚ) =
      ((2 * (OMA.S_oeis_a203298.a (n - 1) : ℤ) + 2 * (OMA.S_oeis_a203298.a (n - 2) : ℤ) -
        6 * (OMA.S_oeis_a203298.a (n - 3) : ℤ) + 6 * (OMA.S_oeis_a203298.a (n - 5) : ℤ) -
        2 * (OMA.S_oeis_a203298.a (n - 6) : ℤ) - 2 * (OMA.S_oeis_a203298.a (n - 7) : ℤ) +
        (OMA.S_oeis_a203298.a (n - 8) : ℤ)) : ℚ) := by
    push_cast
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · have hk5 : 5 ≤ k := by omega
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 5 := ⟨k - 5, by omega⟩
      have he0 : Even n := ⟨m + 5, by omega⟩
      have ho1 : Odd (n - 1) := ⟨m + 4, by omega⟩
      have he2 : Even (n - 2) := ⟨m + 4, by omega⟩
      have ho3 : Odd (n - 3) := ⟨m + 3, by omega⟩
      have ho5 : Odd (n - 5) := ⟨m + 2, by omega⟩
      have he6 : Even (n - 6) := ⟨m + 2, by omega⟩
      have ho7 : Odd (n - 7) := ⟨m + 1, by omega⟩
      have he8 : Even (n - 8) := ⟨m + 1, by omega⟩
      rw [hEven n he0, hOdd (n - 1) ho1, hEven (n - 2) he2, hOdd (n - 3) ho3,
        hOdd (n - 5) ho5, hEven (n - 6) he6, hOdd (n - 7) ho7, hEven (n - 8) he8]
      simp only [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : 2 ≤ n),
        Nat.cast_sub (by omega : 3 ≤ n), Nat.cast_sub (by omega : 5 ≤ n),
        Nat.cast_sub (by omega : 6 ≤ n), Nat.cast_sub (by omega : 7 ≤ n),
        Nat.cast_sub (by omega : 8 ≤ n)]
      push_cast
      ring
    · have hk5 : 5 ≤ k := by omega
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 5 := ⟨k - 5, by omega⟩
      have ho0 : Odd n := ⟨m + 5, by omega⟩
      have he1 : Even (n - 1) := ⟨m + 5, by omega⟩
      have ho2 : Odd (n - 2) := ⟨m + 4, by omega⟩
      have he3 : Even (n - 3) := ⟨m + 4, by omega⟩
      have he5 : Even (n - 5) := ⟨m + 3, by omega⟩
      have ho6 : Odd (n - 6) := ⟨m + 2, by omega⟩
      have he7 : Even (n - 7) := ⟨m + 2, by omega⟩
      have ho8 : Odd (n - 8) := ⟨m + 1, by omega⟩
      rw [hOdd n ho0, hEven (n - 1) he1, hOdd (n - 2) ho2, hEven (n - 3) he3,
        hEven (n - 5) he5, hOdd (n - 6) ho6, hEven (n - 7) he7, hOdd (n - 8) ho8]
      simp only [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : 2 ≤ n),
        Nat.cast_sub (by omega : 3 ≤ n), Nat.cast_sub (by omega : 5 ≤ n),
        Nat.cast_sub (by omega : 6 ≤ n), Nat.cast_sub (by omega : 7 ≤ n),
        Nat.cast_sub (by omega : 8 ≤ n)]
      push_cast
      ring
  exact_mod_cast hq
