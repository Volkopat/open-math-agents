import OMAStatements.S_oeis_a094856

private lemma q_succ (i : ℕ) :
    OMA.S_oeis_a094856.q (i + 1) = (4 * (i : ℤ) + 1) * OMA.S_oeis_a094856.q i := by
  simp only [OMA.S_oeis_a094856.q, Finset.prod_range_succ, mul_comm]

private lemma a_eq_sum_range (n : ℕ) :
    OMA.S_oeis_a094856.a n =
      ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℤ) * ((4 : ℤ) ^ (n - i) * OMA.S_oeis_a094856.q i) :=
  Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => OMA.S_oeis_a094856.weight n (i, j)) n

private lemma nat_mul_choose_absorption (m j : ℕ) (hj : j ≤ m + 1) :
    (m + 1 - j) * (m + 1).choose j = (m + 1) * m.choose j := by
  induction m generalizing j with
  | zero =>
    rcases j with _ | _ | _
    · rfl
    · rfl
    · exfalso; omega
  | succ m ih =>
    rcases j with _ | j
    · simp only [Nat.sub_zero, Nat.choose_zero_right, mul_one]
    · rcases eq_or_lt_of_le (Nat.succ_le_succ_iff.mp hj) with rfl | hlt
      · rw [Nat.sub_self, zero_mul, Nat.choose_eq_zero_of_lt (Nat.lt_succ_self (m + 1)), mul_zero]
      · have hjle : j ≤ m + 1 := by omega
        have hj1le : j + 1 ≤ m + 1 := by omega
        have h1 : (m + 1 - j) * (m + 1).choose j = (m + 1) * m.choose j := ih j hjle
        have h2 : (m + 1 - (j + 1)) * (m + 1).choose (j + 1) = (m + 1) * m.choose (j + 1) :=
          ih (j + 1) hj1le
        have hsub : m + 1 + 1 - (j + 1) = m + 1 - j := by omega
        have hsub2 : m + 1 - j = (m + 1 - (j + 1)) + 1 := by omega
        have hc1 : (m + 1 + 1).choose (j + 1) = (m + 1).choose j + (m + 1).choose (j + 1) :=
          Nat.choose_succ_succ (m + 1) j
        have hc0 : (m + 1).choose (j + 1) = m.choose j + m.choose (j + 1) :=
          Nat.choose_succ_succ m j
        rw [hsub, hc1, mul_add, h1]
        have hl : (m + 1 - j) * (m + 1).choose (j + 1) =
            (m + 1) * m.choose (j + 1) + (m + 1).choose (j + 1) := by
          rw [hsub2, add_mul, one_mul, h2]
        rw [hl, hc0]
        ring

private lemma a_rec_succ (m : ℕ) :
    OMA.S_oeis_a094856.a (m + 2) -
        (4 * ((m + 2 : ℕ) : ℤ) + 1) * OMA.S_oeis_a094856.a (m + 1) +
        16 * (((m + 2 : ℕ) : ℤ) - 1) * OMA.S_oeis_a094856.a m = 0 := by
  have ha2 : OMA.S_oeis_a094856.a (m + 2) =
      (4 : ℤ) ^ (m + 2) +
        ∑ j ∈ Finset.range (m + 2),
          ((m + 1).choose (j + 1) : ℤ) *
            ((4 : ℤ) ^ (m + 1 - j) * OMA.S_oeis_a094856.q (j + 1)) +
        ∑ j ∈ Finset.range (m + 2),
          ((m + 1).choose j : ℤ) *
            ((4 : ℤ) ^ (m + 1 - j) * OMA.S_oeis_a094856.q (j + 1)) := by
    rw [a_eq_sum_range (m + 2), Finset.sum_range_succ']
    have h0 : ((m + 2).choose 0 : ℤ) *
        ((4 : ℤ) ^ (m + 2 - 0) * OMA.S_oeis_a094856.q 0) = (4 : ℤ) ^ (m + 2) := by
      simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero,
        OMA.S_oeis_a094856.q, Finset.range_zero, Finset.prod_empty, mul_one]
    have hsplit : ∀ j ∈ Finset.range (m + 2),
        ((m + 2).choose (j + 1) : ℤ) *
            ((4 : ℤ) ^ (m + 2 - (j + 1)) * OMA.S_oeis_a094856.q (j + 1)) =
          ((m + 1).choose (j + 1) : ℤ) *
              ((4 : ℤ) ^ (m + 1 - j) * OMA.S_oeis_a094856.q (j + 1)) +
            ((m + 1).choose j : ℤ) *
              ((4 : ℤ) ^ (m + 1 - j) * OMA.S_oeis_a094856.q (j + 1)) := by
      intro j _
      rw [Nat.choose_succ_succ, show m + 2 - (j + 1) = m + 1 - j by omega]
      push_cast
      ring
    rw [h0, Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
    ring
  have hpartA :
      4 * OMA.S_oeis_a094856.a (m + 1) =
        (4 : ℤ) ^ (m + 2) +
          ∑ j ∈ Finset.range (m + 2),
            ((m + 1).choose (j + 1) : ℤ) *
              ((4 : ℤ) ^ (m + 1 - j) * OMA.S_oeis_a094856.q (j + 1)) := by
    rw [a_eq_sum_range (m + 1), Finset.sum_range_succ', mul_add, Finset.mul_sum]
    have h0 : (4 : ℤ) * (((m + 1).choose 0 : ℤ) *
        ((4 : ℤ) ^ (m + 1 - 0) * OMA.S_oeis_a094856.q 0)) = (4 : ℤ) ^ (m + 2) := by
      simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero,
        OMA.S_oeis_a094856.q, Finset.range_zero, Finset.prod_empty, mul_one,
        pow_succ']
    rw [h0, add_comm]
    congr 1
    have hdrop :
        ∑ j ∈ Finset.range (m + 2),
            ((m + 1).choose (j + 1) : ℤ) *
              ((4 : ℤ) ^ (m + 1 - j) * OMA.S_oeis_a094856.q (j + 1)) =
          ∑ j ∈ Finset.range (m + 1),
            ((m + 1).choose (j + 1) : ℤ) *
              ((4 : ℤ) ^ (m + 1 - j) * OMA.S_oeis_a094856.q (j + 1)) := by
      rw [Finset.sum_range_succ]
      have hzero : ((m + 1).choose (m + 1 + 1) : ℤ) *
          ((4 : ℤ) ^ (m + 1 - (m + 1)) * OMA.S_oeis_a094856.q (m + 1 + 1)) = 0 := by
        rw [Nat.choose_eq_zero_of_lt (Nat.lt_succ_self (m + 1)), Nat.cast_zero, zero_mul]
      rw [hzero, add_zero]
    rw [hdrop]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [show m + 1 - j = (m + 1 - (j + 1)) + 1 by omega, pow_succ']
    ring
  have hpartB :
      ∑ j ∈ Finset.range (m + 2),
          ((m + 1).choose j : ℤ) *
            ((4 : ℤ) ^ (m + 1 - j) * OMA.S_oeis_a094856.q (j + 1)) =
        (4 * (m : ℤ) + 5) * OMA.S_oeis_a094856.a (m + 1) -
          16 * ((m : ℤ) + 1) * OMA.S_oeis_a094856.a m := by
    have hterm : ∀ j ∈ Finset.range (m + 2),
        ((m + 1).choose j : ℤ) *
            ((4 : ℤ) ^ (m + 1 - j) * OMA.S_oeis_a094856.q (j + 1)) =
          (4 * (m : ℤ) + 5) * (((m + 1).choose j : ℤ) *
              ((4 : ℤ) ^ (m + 1 - j) * OMA.S_oeis_a094856.q j)) -
            4 * (((m + 1 - j) * (m + 1).choose j : ℕ) : ℤ) *
              ((4 : ℤ) ^ (m + 1 - j) * OMA.S_oeis_a094856.q j) := by
      intro j hj
      have hjle : j ≤ m + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [q_succ]
      have hid : (4 * (j : ℤ) + 1) = (4 * (m : ℤ) + 5) - 4 * ((m + 1 - j : ℕ) : ℤ) := by
        rw [Nat.cast_sub hjle]
        push_cast
        ring
      rw [hid]
      push_cast
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← a_eq_sum_range (m + 1)]
    congr 1
    have habs : ∀ j ∈ Finset.range (m + 2),
        4 * (((m + 1 - j) * (m + 1).choose j : ℕ) : ℤ) *
            ((4 : ℤ) ^ (m + 1 - j) * OMA.S_oeis_a094856.q j) =
          4 * (((m + 1) * m.choose j : ℕ) : ℤ) *
            ((4 : ℤ) ^ (m + 1 - j) * OMA.S_oeis_a094856.q j) := by
      intro j hj
      have hjle : j ≤ m + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [nat_mul_choose_absorption m j hjle]
    rw [Finset.sum_congr rfl habs, Finset.sum_range_succ]
    have hzero : 4 * (((m + 1) * m.choose (m + 1) : ℕ) : ℤ) *
        ((4 : ℤ) ^ (m + 1 - (m + 1)) * OMA.S_oeis_a094856.q (m + 1)) = 0 := by
      rw [Nat.choose_eq_zero_of_lt (Nat.lt_succ_self m), mul_zero, Nat.cast_zero, mul_zero,
        zero_mul]
    rw [hzero, add_zero, a_eq_sum_range m, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [show m + 1 - j = (m - j) + 1 by omega, pow_succ']
    push_cast
    ring
  rw [ha2, ← hpartA, hpartB]
  push_cast
  ring

theorem OMA.solution : type_of% @OMA.S_oeis_a094856.main := by
  have hrec : ∀ n : ℕ, 2 ≤ n →
      OMA.S_oeis_a094856.a n -
          (4 * (n : ℤ) + 1) * OMA.S_oeis_a094856.a (n - 1) +
          16 * ((n : ℤ) - 1) * OMA.S_oeis_a094856.a (n - 2) = 0 := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    simpa only [Nat.add_sub_cancel, show m + 2 - 1 = m + 1 by omega] using a_rec_succ m
  refine ⟨hrec, ?_⟩
  intro k hk
  have : NeZero k := ⟨hk.ne'⟩
  let state (n : ℕ) : ZMod k × ZMod k × ZMod k :=
    ((n : ZMod k), (OMA.S_oeis_a094856.a (n + 1) : ZMod k), (OMA.S_oeis_a094856.a n : ZMod k))
  let step : ZMod k × ZMod k × ZMod k → ZMod k × ZMod k × ZMod k :=
    fun s => (s.1 + 1, (4 * (s.1 + 2) + 1) * s.2.1 - 16 * (s.1 + 1) * s.2.2, s.2.1)
  have hstep : ∀ n : ℕ, state (n + 1) = step (state n) := by
    intro n
    have hr := a_rec_succ n
    have ha2 : OMA.S_oeis_a094856.a (n + 2) =
        (4 * ((n + 2 : ℕ) : ℤ) + 1) * OMA.S_oeis_a094856.a (n + 1) -
          16 * (((n + 2 : ℕ) : ℤ) - 1) * OMA.S_oeis_a094856.a n := by
      linarith
    have hz := congrArg (Int.cast : ℤ → ZMod k) ha2
    push_cast at hz
    ext
    · simp only [state, step, Nat.cast_add, Nat.cast_one]
    · simp only [state, step, add_assoc]
      rw [hz]
      ring
    · rfl
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite state
  have hlt : ∃ N M : ℕ, N < M ∧ state N = state M := by
    rcases lt_or_gt_of_ne hij with hij_lt | hji_lt
    · exact ⟨i, j, hij_lt, heq⟩
    · exact ⟨j, i, hji_lt, heq.symm⟩
  obtain ⟨N, M, hNM, hst⟩ := hlt
  refine ⟨N, M - N, Nat.sub_pos_of_lt hNM, ?_⟩
  have hper : ∀ d : ℕ, state (N + (M - N) + d) = state (N + d) := by
    intro d
    induction d with
    | zero =>
      rw [add_zero, add_zero, Nat.add_sub_cancel' hNM.le]
      exact hst.symm
    | succ d ih =>
      rw [← add_assoc, ← add_assoc, hstep, hstep, ih]
  intro n hn
  obtain ⟨d, rfl⟩ : ∃ d, n = N + d := ⟨n - N, by omega⟩
  have hcoord := congrArg (fun s : ZMod k × ZMod k × ZMod k => s.2.2) (hper d)
  rw [show N + d + (M - N) = N + (M - N) + d by omega]
  exact (ZMod.intCast_eq_intCast_iff
    (OMA.S_oeis_a094856.a (N + (M - N) + d))
    (OMA.S_oeis_a094856.a (N + d)) k).mp hcoord
