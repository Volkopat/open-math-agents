import OMAStatements.S_mo_449243

open OMA.S_mo_449243

private lemma oddDF_succ (k : ℕ) :
    Nat.doubleFactorial (2 * (k + 1) - 1) = (2 * k + 1) * Nat.doubleFactorial (2 * k - 1) := by
  have h : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  rw [h, Nat.doubleFactorial_add_one]

private lemma range_sum_mul (m : ℕ) (f : ℕ → ℕ) (c : ℕ) :
    (Finset.range m).sum f * c = (Finset.range m).sum (fun i => f i * c) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, Nat.add_mul, ih, Finset.sum_range_succ]

private lemma range_mul_sum (m : ℕ) (c : ℕ) (f : ℕ → ℕ) :
    c * (Finset.range m).sum f = (Finset.range m).sum (fun i => c * f i) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, Nat.mul_add, ih, Finset.sum_range_succ]

private lemma range_sum_comm (a b : ℕ) (f : ℕ → ℕ → ℕ) :
    (Finset.range a).sum (fun i => (Finset.range b).sum (fun j => f i j)) =
      (Finset.range b).sum (fun j => (Finset.range a).sum (fun i => f i j)) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Finset.sum_range_succ, ih, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_range_succ]

private lemma int_cast_range_sum (m : ℕ) (f : ℕ → ℕ) :
    (((Finset.range m).sum f : ℕ) : ℤ) = (Finset.range m).sum (fun i => (f i : ℤ)) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, Nat.cast_add, ih, Finset.sum_range_succ]

private lemma hockey_stick (n q : ℕ) :
    1 + (Finset.range (q + 1)).sum (fun j => Nat.choose (j + n + 1) n) =
      Nat.choose (q + n + 2) (n + 1) := by
  induction q with
  | zero =>
    simp only [Finset.sum_range_one, zero_add, Nat.choose_succ_self_right]
    omega
  | succ q ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ih]
    have h1 : q + 1 + n + 1 = q + n + 2 := by omega
    have h2 : q + 1 + n + 2 = (q + n + 2) + 1 := by omega
    rw [h1, h2]
    rw [Nat.choose_succ_succ (q + n + 2) n, add_comm]

private lemma choose_absorb (n q : ℕ) :
    (q + 2) * Nat.choose (q + n + 2) n = (n + 1) * Nat.choose (q + n + 2) (n + 1) := by
  have h := Nat.choose_succ_right_eq (q + n + 2) n
  have hsub : q + n + 2 - n = q + 2 := by omega
  rw [hsub] at h
  rw [Nat.mul_comm (q + 2), ← h, Nat.mul_comm (n + 1)]

private lemma recurrence_conv (n : ℕ) :
    ∀ q : ℕ,
      (Finset.range (n + 1)).sum
          (fun i => recurrence i q * Nat.doubleFactorial (2 * (n - i) - 1)) =
        Nat.choose (q + n + 1) n * Nat.doubleFactorial (2 * (n + 1) - 1) := by
  induction n with
  | zero =>
    intro q
    simp [recurrence]
  | succ n ih =>
    intro q
    rw [Finset.sum_range_succ']
    have hsub0 : n + 1 - 0 = n + 1 := Nat.sub_zero (n + 1)
    have hrec0 : recurrence 0 q = 1 := rfl
    rw [hsub0, hrec0, one_mul]
    have hstep :
        (Finset.range (n + 1)).sum
            (fun i => recurrence (i + 1) q * Nat.doubleFactorial (2 * (n + 1 - (i + 1)) - 1)) =
          (Finset.range (n + 1)).sum
            (fun i =>
              2 * (q + 2) * (recurrence i (q + 1) * Nat.doubleFactorial (2 * (n - i) - 1)) +
                (Finset.range (q + 1)).sum
                  (fun j => recurrence i j * Nat.doubleFactorial (2 * (n - i) - 1))) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      have hsub : n + 1 - (i + 1) = n - i := by omega
      rw [hsub, recurrence, add_mul, mul_assoc, range_sum_mul]
    rw [hstep, Finset.sum_add_distrib, ← range_mul_sum, ih (q + 1), range_sum_comm]
    have hsum_j :
        (Finset.range (q + 1)).sum
            (fun j =>
              (Finset.range (n + 1)).sum
                (fun i => recurrence i j * Nat.doubleFactorial (2 * (n - i) - 1))) =
          (Finset.range (q + 1)).sum (fun j => Nat.choose (j + n + 1) n) *
            Nat.doubleFactorial (2 * (n + 1) - 1) := by
      rw [range_sum_mul]
      refine Finset.sum_congr rfl fun j _ => ih j
    rw [hsum_j]
    have h1 : q + 1 + n + 1 = q + n + 2 := by omega
    have h2 : q + (n + 1) + 1 = q + n + 2 := by omega
    rw [h1, h2]
    set D := Nat.doubleFactorial (2 * (n + 1) - 1)
    set S := (Finset.range (q + 1)).sum (fun j => Nat.choose (j + n + 1) n)
    set C0 := Nat.choose (q + n + 2) n
    set C1 := Nat.choose (q + n + 2) (n + 1)
    have hhs : 1 + S = C1 := hockey_stick n q
    have habs : (q + 2) * C0 = (n + 1) * C1 := choose_absorb n q
    have hdf : Nat.doubleFactorial (2 * (n + 1 + 1) - 1) = (2 * (n + 1) + 1) * D :=
      oddDF_succ (n + 1)
    have h_alg1 :
        2 * (q + 2) * (C0 * D) + S * D + D =
          (2 * ((q + 2) * C0) + (1 + S)) * D := by
      rw [← mul_assoc (2 * (q + 2)) C0 D, add_assoc]
      conv_lhs =>
        arg 2
        arg 2
        rw [← one_mul D]
      rw [add_comm (S * D) (1 * D), ← Nat.add_mul, ← Nat.add_mul, mul_assoc 2 (q + 2) C0]
    have h_alg2 :
        (2 * ((n + 1) * C1) + C1) * D = C1 * ((2 * (n + 1) + 1) * D) := by
      rw [← mul_assoc 2 (n + 1) C1]
      conv_lhs =>
        arg 1
        arg 2
        rw [← one_mul C1]
      rw [← Nat.add_mul, mul_comm (2 * (n + 1) + 1) C1, mul_assoc]
    rw [h_alg1, habs, hhs, h_alg2, ← hdf]

theorem OMA.solution : type_of% @OMA.S_mo_449243.main := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | m
    · omega
    · simp only [Nat.add_sub_cancel]
      have hseq : sequence (m + 1) = ((m + 1 : ℕ) : ℤ) * oddProduct (m + 1) -
          (Finset.range m).attach.sum
            (fun i => sequence (i.val + 1) * oddProduct (m - i.val)) := by
        rw [sequence]
      rw [hseq]
      have hih_sum :
          (Finset.range m).attach.sum
              (fun i => sequence (i.val + 1) * oddProduct (m - i.val)) =
            (Finset.range m).sum (fun i => (recurrence i 0 : ℤ) * oddProduct (m - i)) := by
        have h1 :
            (Finset.range m).attach.sum
                (fun i => sequence (i.val + 1) * oddProduct (m - i.val)) =
              (Finset.range m).attach.sum
                (fun i => (recurrence i.val 0 : ℤ) * oddProduct (m - i.val)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          have him : i.val < m := Finset.mem_range.mp i.property
          have heq : sequence (i.val + 1) = (recurrence i.val 0 : ℤ) := by
            have := ih (i.val + 1) (Nat.succ_lt_succ him) (Nat.succ_pos i.val)
            simpa only [Nat.add_sub_cancel] using this
          rw [heq]
        rw [h1]
        exact Finset.sum_attach (Finset.range m) (fun i => (recurrence i 0 : ℤ) * oddProduct (m - i))
      rw [hih_sum]
      have hconv :
          (Finset.range (m + 1)).sum (fun i => (recurrence i 0 : ℤ) * oddProduct (m - i)) =
            ((m + 1 : ℕ) : ℤ) * oddProduct (m + 1) := by
        have hnat := recurrence_conv m 0
        rw [zero_add, Nat.choose_succ_self_right] at hnat
        have hcast :
            (((Finset.range (m + 1)).sum
                (fun i => recurrence i 0 * Nat.doubleFactorial (2 * (m - i) - 1)) : ℕ) : ℤ) =
              (((m + 1) * Nat.doubleFactorial (2 * (m + 1) - 1) : ℕ) : ℤ) :=
          congrArg (Nat.cast : ℕ → ℤ) hnat
        rw [int_cast_range_sum, Nat.cast_mul] at hcast
        simpa only [Nat.cast_mul, oddProduct] using hcast
      rw [Finset.sum_range_succ, Nat.sub_self] at hconv
      have hodd0 : oddProduct 0 = 1 := rfl
      rw [hodd0, mul_one] at hconv
      rw [← hconv, add_sub_cancel_left]
