import OMAStatements.S_oeis_a226857
import Mathlib

open OMA.S_oeis_a226857

-- Vajda identity with n = 4: F(a+4) F(b+4) = 3 F(a+b+4) + F(a) F(b).
theorem a226857_vajda (a b : ℕ) :
    Nat.fib (a + 4) * Nat.fib (b + 4) = 3 * Nat.fib (a + b + 4) + Nat.fib a * Nat.fib b := by
  have h : Nat.fib (a + b + 4) =
      Nat.fib (a + 2) * Nat.fib (b + 1) + Nat.fib (a + 3) * Nat.fib (b + 2) := by
    have := Nat.fib_add (a + 2) (b + 1)
    rw [show a + 2 + (b + 1) + 1 = a + b + 4 by ring] at this
    exact this
  have e2a : Nat.fib (a + 2) = Nat.fib a + Nat.fib (a + 1) := Nat.fib_add_two
  have e3a : Nat.fib (a + 3) = Nat.fib (a + 1) + Nat.fib (a + 2) := Nat.fib_add_two
  have e4a : Nat.fib (a + 4) = Nat.fib (a + 2) + Nat.fib (a + 3) := Nat.fib_add_two
  have e2b : Nat.fib (b + 2) = Nat.fib b + Nat.fib (b + 1) := Nat.fib_add_two
  have e3b : Nat.fib (b + 3) = Nat.fib (b + 1) + Nat.fib (b + 2) := Nat.fib_add_two
  have e4b : Nat.fib (b + 4) = Nat.fib (b + 2) + Nat.fib (b + 3) := Nat.fib_add_two
  rw [h, e4a, e4b, e3a, e3b, e2a, e2b]
  ring

-- No sum of two Fibonacci numbers lies strictly between F(u+4)+F(u) and F(u+4)+F(u+1).
theorem a226857_gap (u a b N : ℕ) (hba : b ≤ a)
    (hlo : Nat.fib (u + 4) + Nat.fib u < N) (hhi : N < Nat.fib (u + 4) + Nat.fib (u + 1)) :
    Nat.fib a + Nat.fib b ≠ N := by
  intro hN
  have f2 : Nat.fib (u + 2) = Nat.fib u + Nat.fib (u + 1) := Nat.fib_add_two
  have f3 : Nat.fib (u + 3) = Nat.fib (u + 1) + Nat.fib (u + 2) := Nat.fib_add_two
  have f4 : Nat.fib (u + 4) = Nat.fib (u + 2) + Nat.fib (u + 3) := Nat.fib_add_two
  have f5 : Nat.fib (u + 5) = Nat.fib (u + 3) + Nat.fib (u + 4) := Nat.fib_add_two
  rcases Nat.lt_or_ge a (u + 4) with ha | ha
  · rcases Nat.lt_or_ge b (u + 3) with hb | hb
    · have m1 := Nat.fib_mono (show a ≤ u + 3 by omega)
      have m2 := Nat.fib_mono (show b ≤ u + 2 by omega)
      omega
    · have ea : a = u + 3 := by omega
      have eb : b = u + 3 := by omega
      rw [ea, eb] at hN
      omega
  · rcases Nat.lt_or_ge a (u + 5) with ha' | ha'
    · have ea : a = u + 4 := by omega
      rw [ea] at hN
      rcases Nat.lt_or_ge b (u + 1) with hb | hb
      · have m1 := Nat.fib_mono (show b ≤ u by omega)
        omega
      · have m1 := Nat.fib_mono hb
        omega
    · have m1 := Nat.fib_mono ha'
      omega

theorem a226857_notsum (i j a b : ℕ) (hi : 5 ≤ i) (hj : 5 ≤ j) :
    Nat.fib i * Nat.fib j ≠ Nat.fib a + Nat.fib b := by
  obtain ⟨p, rfl⟩ : ∃ p, i = p + 4 := ⟨i - 4, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q, j = q + 4 := ⟨j - 4, by omega⟩
  have hv := a226857_vajda p q
  have hp : 0 < Nat.fib p := Nat.fib_pos.mpr (by omega)
  have hq : 0 < Nat.fib q := Nat.fib_pos.mpr (by omega)
  have hpq : 0 < Nat.fib p * Nat.fib q := Nat.mul_pos hp hq
  have hadd := Nat.fib_add p q
  have hp1 : 0 < Nat.fib (p + 1) := Nat.fib_pos.mpr (by omega)
  have hq1 : 0 < Nat.fib (q + 1) := Nat.fib_pos.mpr (by omega)
  have hpq1 : 0 < Nat.fib (p + 1) * Nat.fib (q + 1) := Nat.mul_pos hp1 hq1
  have g2 : Nat.fib (p + q + 2) = Nat.fib (p + q) + Nat.fib (p + q + 1) := Nat.fib_add_two
  have g3 : Nat.fib (p + q + 3) = Nat.fib (p + q + 1) + Nat.fib (p + q + 2) := Nat.fib_add_two
  have g4 : Nat.fib (p + q + 4) = Nat.fib (p + q + 2) + Nat.fib (p + q + 3) := Nat.fib_add_two
  have g5 : Nat.fib (p + q + 5) = Nat.fib (p + q + 3) + Nat.fib (p + q + 4) := Nat.fib_add_two
  have g6 : Nat.fib (p + q + 2 + 4) = Nat.fib (p + q + 4) + Nat.fib (p + q + 5) :=
    Nat.fib_add_two
  have g7 : Nat.fib (p + q + 2 + 1) = Nat.fib (p + q + 3) := rfl
  intro h
  rcases le_total b a with hab | hab
  · exact a226857_gap (p + q + 2) a b (Nat.fib (p + 4) * Nat.fib (q + 4)) hab
      (by omega) (by omega) h.symm
  · exact a226857_gap (p + q + 2) b a (Nat.fib (p + 4) * Nat.fib (q + 4)) hab
      (by omega) (by omega) (by omega)

theorem a226857_three (k : ℕ) : ∃ x y : ℕ, Nat.fib x + Nat.fib y = 3 * Nat.fib k := by
  match k with
  | 0 => exact ⟨0, 0, by simp⟩
  | 1 => exact ⟨4, 0, by decide⟩
  | r + 2 =>
    refine ⟨r + 4, r, ?_⟩
    have e2 : Nat.fib (r + 2) = Nat.fib r + Nat.fib (r + 1) := Nat.fib_add_two
    have e3 : Nat.fib (r + 3) = Nat.fib (r + 1) + Nat.fib (r + 2) := Nat.fib_add_two
    have e4 : Nat.fib (r + 4) = Nat.fib (r + 2) + Nat.fib (r + 3) := Nat.fib_add_two
    omega

theorem a226857_good_of (m : ℕ)
    (h : ∃ k, m = Nat.fib k ∨ m = 2 * Nat.fib k ∨ m = 3 * Nat.fib k) : good m := by
  obtain ⟨k, hk | hk | hk⟩ := h
  · refine ⟨⟨Nat.fib k, 0, ⟨k, rfl⟩, ⟨0, rfl⟩, by rw [hk, Nat.add_zero]⟩,
      ⟨Nat.fib k, 1, ⟨k, rfl⟩, ⟨1, rfl⟩, by rw [hk, Nat.mul_one]⟩⟩
  · refine ⟨⟨Nat.fib k, Nat.fib k, ⟨k, rfl⟩, ⟨k, rfl⟩, by rw [hk]; ring⟩,
      ⟨2, Nat.fib k, ⟨3, by decide⟩, ⟨k, rfl⟩, by rw [hk]⟩⟩
  · obtain ⟨x, y, hxy⟩ := a226857_three k
    refine ⟨⟨Nat.fib x, Nat.fib y, ⟨x, rfl⟩, ⟨y, rfl⟩, by rw [hk, hxy]⟩,
      ⟨3, Nat.fib k, ⟨4, by decide⟩, ⟨k, rfl⟩, by rw [hk]⟩⟩

theorem a226857_of_good (m : ℕ) (h : good m) :
    ∃ k, m = Nat.fib k ∨ m = 2 * Nat.fib k ∨ m = 3 * Nat.fib k := by
  obtain ⟨⟨a, b, ⟨ia, rfl⟩, ⟨ib, rfl⟩, hab⟩, ⟨c, d, ⟨ic, rfl⟩, ⟨jd, rfl⟩, hcd⟩⟩ := h
  rcases Nat.lt_or_ge ic 5 with hc | hc
  · interval_cases ic
    · exact ⟨0, Or.inl (by rw [← hcd]; simp)⟩
    · exact ⟨jd, Or.inl (by rw [← hcd]; simp)⟩
    · exact ⟨jd, Or.inl (by rw [← hcd, show Nat.fib 2 = 1 by decide, Nat.one_mul])⟩
    · exact ⟨jd, Or.inr (Or.inl (by rw [← hcd, show Nat.fib 3 = 2 by decide]))⟩
    · exact ⟨jd, Or.inr (Or.inr (by rw [← hcd, show Nat.fib 4 = 3 by decide]))⟩
  · rcases Nat.lt_or_ge jd 5 with hd | hd
    · interval_cases jd
      · exact ⟨0, Or.inl (by rw [← hcd]; simp)⟩
      · exact ⟨ic, Or.inl (by rw [← hcd]; simp)⟩
      · exact ⟨ic, Or.inl (by rw [← hcd, show Nat.fib 2 = 1 by decide, Nat.mul_one])⟩
      · exact ⟨ic, Or.inr (Or.inl (by rw [← hcd, show Nat.fib 3 = 2 by decide, Nat.mul_comm]))⟩
      · exact ⟨ic, Or.inr (Or.inr (by rw [← hcd, show Nat.fib 4 = 3 by decide, Nat.mul_comm]))⟩
    · exact absurd (hcd.trans hab.symm) (a226857_notsum ic jd ia ib hc hd)

-- The explicit enumeration (0-based index).
def a226857_f (k : ℕ) : ℕ :=
  if k < 6 then k
  else if k % 3 = 0 then 2 * Nat.fib (k / 3 + 2)
  else if k % 3 = 1 then Nat.fib (k / 3 + 4)
  else 3 * Nat.fib (k / 3 + 2)

theorem a226857_f_small (k : ℕ) (hk : k < 6) : a226857_f k = k := by
  rw [a226857_f, if_pos hk]

theorem a226857_f0 (m : ℕ) (hm : 2 ≤ m) : a226857_f (3 * m) = 2 * Nat.fib (m + 2) := by
  rw [a226857_f, if_neg (show ¬ (3 * m < 6) by omega), if_pos (show 3 * m % 3 = 0 by omega),
    show 3 * m / 3 = m by omega]

theorem a226857_f1 (m : ℕ) (hm : 2 ≤ m) : a226857_f (3 * m + 1) = Nat.fib (m + 4) := by
  rw [a226857_f, if_neg (show ¬ (3 * m + 1 < 6) by omega),
    if_neg (show ¬ ((3 * m + 1) % 3 = 0) by omega), if_pos (show (3 * m + 1) % 3 = 1 by omega),
    show (3 * m + 1) / 3 = m by omega]

theorem a226857_f2 (m : ℕ) (hm : 2 ≤ m) : a226857_f (3 * m + 2) = 3 * Nat.fib (m + 2) := by
  rw [a226857_f, if_neg (show ¬ (3 * m + 2 < 6) by omega),
    if_neg (show ¬ ((3 * m + 2) % 3 = 0) by omega), if_neg (show ¬ ((3 * m + 2) % 3 = 1) by omega),
    show (3 * m + 2) / 3 = m by omega]

theorem a226857_f_mono : StrictMono a226857_f := by
  apply strictMono_nat_of_lt_succ
  intro k
  rcases Nat.lt_or_ge k 6 with hk | hk
  · interval_cases k <;> decide +kernel
  · obtain ⟨m, hm, h | h | h⟩ : ∃ m, 2 ≤ m ∧ (k = 3 * m ∨ k = 3 * m + 1 ∨ k = 3 * m + 2) :=
      ⟨k / 3, by omega, by omega⟩
    all_goals
      have e2 : Nat.fib (m + 2) = Nat.fib m + Nat.fib (m + 1) := Nat.fib_add_two
      have e3 : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := Nat.fib_add_two
      have e4 : Nat.fib (m + 4) = Nat.fib (m + 2) + Nat.fib (m + 3) := Nat.fib_add_two
      have l1 : Nat.fib m < Nat.fib (m + 1) := Nat.fib_lt_fib_succ hm
      have l0 : 0 < Nat.fib m := Nat.fib_pos.mpr (by omega)
    · rw [h, a226857_f0 m hm, a226857_f1 m hm]
      omega
    · rw [h, a226857_f1 m hm, show 3 * m + 1 + 1 = 3 * m + 2 by ring, a226857_f2 m hm]
      omega
    · have h3 : a226857_f (3 * (m + 1)) = 2 * Nat.fib (m + 3) := a226857_f0 (m + 1) (by omega)
      rw [h, a226857_f2 m hm, show 3 * m + 2 + 1 = 3 * (m + 1) by ring, h3]
      omega

theorem a226857_f_good (k : ℕ) : good (a226857_f k) := by
  apply a226857_good_of
  rcases Nat.lt_or_ge k 6 with hk | hk
  · rw [a226857_f_small k hk]
    interval_cases k
    · exact ⟨0, Or.inl (by decide)⟩
    · exact ⟨1, Or.inl (by decide)⟩
    · exact ⟨3, Or.inl (by decide)⟩
    · exact ⟨4, Or.inl (by decide)⟩
    · exact ⟨3, Or.inr (Or.inl (by decide))⟩
    · exact ⟨5, Or.inl (by decide)⟩
  · obtain ⟨m, hm, h | h | h⟩ : ∃ m, 2 ≤ m ∧ (k = 3 * m ∨ k = 3 * m + 1 ∨ k = 3 * m + 2) :=
      ⟨k / 3, by omega, by omega⟩
    · exact ⟨m + 2, Or.inr (Or.inl (by rw [h, a226857_f0 m hm]))⟩
    · exact ⟨m + 4, Or.inl (by rw [h, a226857_f1 m hm])⟩
    · exact ⟨m + 2, Or.inr (Or.inr (by rw [h, a226857_f2 m hm]))⟩

theorem a226857_f_surj (v : ℕ) (hv : good v) : ∃ k, a226857_f k = v := by
  obtain ⟨n, hn | hn | hn⟩ := a226857_of_good v hv
  · rcases Nat.lt_or_ge n 6 with h6 | h6
    · interval_cases n
      · exact ⟨0, by rw [hn]; decide⟩
      · exact ⟨1, by rw [hn]; decide⟩
      · exact ⟨1, by rw [hn]; decide⟩
      · exact ⟨2, by rw [hn]; decide⟩
      · exact ⟨3, by rw [hn]; decide⟩
      · exact ⟨5, by rw [hn]; decide⟩
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      exact ⟨3 * m + 1, by rw [hn, a226857_f1 m (by omega)]⟩
  · rcases Nat.lt_or_ge n 4 with h4 | h4
    · interval_cases n
      · exact ⟨0, by rw [hn]; decide⟩
      · exact ⟨2, by rw [hn]; decide⟩
      · exact ⟨2, by rw [hn]; decide⟩
      · exact ⟨4, by rw [hn]; decide⟩
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      exact ⟨3 * m, by rw [hn, a226857_f0 m (by omega)]⟩
  · rcases Nat.lt_or_ge n 4 with h4 | h4
    · interval_cases n
      · exact ⟨0, by rw [hn]; decide⟩
      · exact ⟨3, by rw [hn]; decide⟩
      · exact ⟨3, by rw [hn]; decide⟩
      · exact ⟨6, by rw [hn]; decide +kernel⟩
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      exact ⟨3 * m + 2, by rw [hn, a226857_f2 m (by omega)]⟩

theorem a226857_nth (k : ℕ) : Nat.nth good k = a226857_f k := by
  have hinf : (Set.ofPred good).Infinite :=
    Set.infinite_of_injective_forall_mem a226857_f_mono.injective a226857_f_good
  have hS : ∀ n : ℕ, n ∈ { n : ℕ | ∀ hf : Set.Finite (Set.ofPred good), n < hf.toFinset.card } :=
    fun n => Set.mem_ofPred.mpr (fun hf => absurd hf hinf)
  refine (Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn a226857_f ?_ ?_ ?_ (hS k)).symm
  · intro v hv
    obtain ⟨j, hj⟩ := a226857_f_surj v hv
    exact ⟨j, hS j, hj⟩
  · intro j _
    exact a226857_f_good j
  · exact a226857_f_mono.strictMonoOn _

theorem a226857_f_rec (K : ℕ) (hK : 12 ≤ K) :
    a226857_f K = a226857_f (K - 3) + a226857_f (K - 6) := by
  obtain ⟨m, hm, h | h | h⟩ : ∃ m, 2 ≤ m ∧ (K = 3 * m + 6 ∨ K = 3 * m + 7 ∨ K = 3 * m + 8) :=
    ⟨K / 3 - 2, by omega, by omega⟩
  · have A := a226857_f0 (m + 2) (by omega)
    have B := a226857_f0 (m + 1) (by omega)
    have C := a226857_f0 m hm
    have e : Nat.fib (m + 2 + 2) = Nat.fib (m + 2) + Nat.fib (m + 1 + 2) := Nat.fib_add_two
    rw [h, show 3 * m + 6 - 3 = 3 * (m + 1) by omega, show 3 * m + 6 - 6 = 3 * m by omega,
      show 3 * m + 6 = 3 * (m + 2) by ring, A, B, C, e]
    ring
  · have A := a226857_f1 (m + 2) (by omega)
    have B := a226857_f1 (m + 1) (by omega)
    have C := a226857_f1 m hm
    have e : Nat.fib (m + 2 + 4) = Nat.fib (m + 4) + Nat.fib (m + 1 + 4) := Nat.fib_add_two
    rw [h, show 3 * m + 7 - 3 = 3 * (m + 1) + 1 by omega, show 3 * m + 7 - 6 = 3 * m + 1 by omega,
      show 3 * m + 7 = 3 * (m + 2) + 1 by ring, A, B, C, e]
    ring
  · have A := a226857_f2 (m + 2) (by omega)
    have B := a226857_f2 (m + 1) (by omega)
    have C := a226857_f2 m hm
    have e : Nat.fib (m + 2 + 2) = Nat.fib (m + 2) + Nat.fib (m + 1 + 2) := Nat.fib_add_two
    rw [h, show 3 * m + 8 - 3 = 3 * (m + 1) + 2 by omega, show 3 * m + 8 - 6 = 3 * m + 2 by omega,
      show 3 * m + 8 = 3 * (m + 2) + 2 by ring, A, B, C, e]
    ring

theorem OMA.solution : type_of% @OMA.S_oeis_a226857.main := by
  intro n hn
  unfold term
  rw [a226857_nth, a226857_nth, a226857_nth, a226857_f_rec (n - 1) (by omega),
    show n - 1 - 3 = n - 3 - 1 by omega, show n - 1 - 6 = n - 6 - 1 by omega]
