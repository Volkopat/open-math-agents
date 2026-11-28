import OMAStatements.S_oeis_a347285

open OMA.S_oeis_a347285 in
lemma OMA.a347285_mono : StrictMono p := Nat.nth_strictMono Nat.infinite_setOfPred_prime

open OMA.S_oeis_a347285 in
lemma OMA.a347285_step_lt (n i : ℕ) (h : 0 < e n i) : e n (i + 1) < e n i := by
  show Nat.log (p (i + 1)) (p i ^ e n i) < e n i
  apply Nat.log_lt_of_lt_pow (pow_ne_zero _ (Nat.prime_nth_prime i).ne_zero)
  exact Nat.pow_lt_pow_left (OMA.a347285_mono (Nat.lt_succ_self i)) h.ne'

open OMA.S_oeis_a347285 in
lemma OMA.a347285_next_le (i : ℕ) : p (i + 1) ≤ 2 * p i := by
  obtain ⟨r, hr, h1, h2⟩ := Nat.exists_prime_lt_and_le_two_mul (p i) (Nat.prime_nth_prime i).ne_zero
  have hr' : p (Nat.count Nat.Prime r) = r := Nat.nth_count hr
  have hi : i < Nat.count Nat.Prime r := OMA.a347285_mono.lt_iff_lt.mp (by rw [hr']; exact h1)
  calc p (i + 1) ≤ p (Nat.count Nat.Prime r) := OMA.a347285_mono.monotone hi
    _ = r := hr'
    _ ≤ 2 * p i := h2

open OMA.S_oeis_a347285 in
lemma OMA.a347285_step_pos (n i : ℕ) (h : 2 ≤ e n i) : 0 < e n (i + 1) := by
  show 0 < Nat.log (p (i + 1)) (p i ^ e n i)
  have hp2 := (Nat.prime_nth_prime i).two_le
  apply Nat.log_pos (Nat.prime_nth_prime (i + 1)).one_lt
  calc p (i + 1) ≤ 2 * p i := OMA.a347285_next_le i
    _ ≤ p i * p i := Nat.mul_le_mul_right _ hp2
    _ = p i ^ 2 := (sq _).symm
    _ ≤ p i ^ e n i := Nat.pow_le_pow_right (Nat.prime_nth_prime i).pos h

/-- Sum of absolute first differences of a list. -/
def OMA.a347285_D (l : List ℕ) : ℤ :=
  ((l.zip l.tail).map (fun q => |(q.1 : ℤ) - q.2|)).sum

open OMA.S_oeis_a347285 in
lemma OMA.a347285_key (n : ℕ) : ∀ m i : ℕ, 0 < e n i → e n i ≤ m →
    ∃ rest, ((List.range' i m).map (e n)).takeWhile (fun x => 0 < x) = e n i :: rest ∧
      OMA.a347285_D (e n i :: rest) = (e n i : ℤ) - 1 := by
  intro m
  induction m with
  | zero => intro i h1 h2; omega
  | succ m ih =>
    intro i h1 h2
    rw [List.range'_succ, List.map_cons, List.takeWhile_cons_of_pos (by simpa using h1)]
    by_cases hpos : 0 < e n (i + 1)
    · have hlt := OMA.a347285_step_lt n i h1
      obtain ⟨rest, hr, hD⟩ := ih (i + 1) hpos (by omega)
      refine ⟨e n (i + 1) :: rest, by rw [hr], ?_⟩
      simp only [OMA.a347285_D, List.tail_cons, List.zip_cons_cons, List.map_cons,
        List.sum_cons] at hD ⊢
      rw [hD, abs_of_nonneg (by omega)]
      ring
    · have h0 : e n (i + 1) = 0 := by omega
      have h11 : e n i = 1 := by
        by_contra hne
        exact hpos (OMA.a347285_step_pos n i (by omega))
      refine ⟨[], ?_, ?_⟩
      · cases m with
        | zero => simp
        | succ m' =>
          rw [List.range'_succ, List.map_cons, List.takeWhile_cons_of_neg (by simp [h0])]
      · simp [OMA.a347285_D, h11]

theorem OMA.solution : type_of% @OMA.S_oeis_a347285.main := by
  intro n hn
  obtain ⟨rest, hr, hD⟩ := OMA.a347285_key n (n + 1) 0 (by simp [OMA.S_oeis_a347285.e]; omega)
    (by simp [OMA.S_oeis_a347285.e])
  have hrow : OMA.S_oeis_a347285.row n = OMA.S_oeis_a347285.e n 0 :: rest := by
    rw [OMA.S_oeis_a347285.row, if_neg (by omega), List.range_eq_range', hr]
  have hS : OMA.S_oeis_a347285.S n = OMA.a347285_D (OMA.S_oeis_a347285.e n 0 :: rest) := by
    rw [OMA.S_oeis_a347285.S, hrow, OMA.a347285_D]
  rw [hS, hD]
  simp [OMA.S_oeis_a347285.e]
