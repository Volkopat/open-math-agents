import OMAStatements.S_oeis_a080239

-- Peeling off the first term of the sum: a(n+4) = a(n) + F(n+4).
theorem oeis_a080239_step (n : ℕ) :
    OMA.S_oeis_a080239.a (n + 4) = OMA.S_oeis_a080239.a n + Nat.fib (n + 4) := by
  unfold OMA.S_oeis_a080239.a
  have h : (n + 4) / 4 + 1 = (n / 4 + 1) + 1 := by omega
  rw [h, Finset.sum_range_succ']
  have e0 : n + 4 - 4 * 0 = n + 4 := by omega
  rw [e0]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  omega

-- F(4m+4), F(4m+5), F(4m+6), F(4m+7) in terms of F(2m+1) .. F(2m+4).
theorem oeis_a080239_f0 (m : ℕ) : Nat.fib (4 * m + 4) =
    Nat.fib (2 * m + 1) * Nat.fib (2 * m + 2) + Nat.fib (2 * m + 2) * Nat.fib (2 * m + 3) := by
  have h := Nat.fib_add (2 * m + 1) (2 * m + 2)
  have h1 : 2 * m + 1 + (2 * m + 2) + 1 = 4 * m + 4 := by ring
  have h2 : 2 * m + 1 + 1 = 2 * m + 2 := rfl
  have h3 : 2 * m + 2 + 1 = 2 * m + 3 := rfl
  rw [h1, h2, h3] at h
  exact h

theorem oeis_a080239_f1 (m : ℕ) : Nat.fib (4 * m + 1 + 4) =
    Nat.fib (2 * m + 2) * Nat.fib (2 * m + 2) + Nat.fib (2 * m + 3) * Nat.fib (2 * m + 3) := by
  have h := Nat.fib_add (2 * m + 2) (2 * m + 2)
  have h1 : 2 * m + 2 + (2 * m + 2) + 1 = 4 * m + 1 + 4 := by ring
  have h3 : 2 * m + 2 + 1 = 2 * m + 3 := rfl
  rw [h1, h3] at h
  exact h

theorem oeis_a080239_f2 (m : ℕ) : Nat.fib (4 * m + 2 + 4) =
    Nat.fib (2 * m + 2) * Nat.fib (2 * m + 3) + Nat.fib (2 * m + 3) * Nat.fib (2 * m + 4) := by
  have h := Nat.fib_add (2 * m + 2) (2 * m + 3)
  have h1 : 2 * m + 2 + (2 * m + 3) + 1 = 4 * m + 2 + 4 := by ring
  have h2 : 2 * m + 2 + 1 = 2 * m + 3 := rfl
  have h3 : 2 * m + 3 + 1 = 2 * m + 4 := rfl
  rw [h1, h2, h3] at h
  exact h

theorem oeis_a080239_f3 (m : ℕ) : Nat.fib (4 * m + 3 + 4) =
    Nat.fib (2 * m + 3) * Nat.fib (2 * m + 3) + Nat.fib (2 * m + 4) * Nat.fib (2 * m + 4) := by
  have h := Nat.fib_add (2 * m + 3) (2 * m + 3)
  have h1 : 2 * m + 3 + (2 * m + 3) + 1 = 4 * m + 3 + 4 := by ring
  have h3 : 2 * m + 3 + 1 = 2 * m + 4 := rfl
  rw [h1, h3] at h
  exact h

-- The four residue classes of n modulo 4.
theorem oeis_a080239_c0 (m : ℕ) :
    OMA.S_oeis_a080239.a (4 * m) = Nat.fib (2 * m + 2) * Nat.fib (2 * m) := by
  induction m with
  | zero => simp [OMA.S_oeis_a080239.a]
  | succ m ih =>
    have e2 : Nat.fib (2 * m + 2) = Nat.fib (2 * m) + Nat.fib (2 * m + 1) := Nat.fib_add_two
    have e3 : Nat.fib (2 * m + 3) = Nat.fib (2 * m + 1) + Nat.fib (2 * m + 2) := Nat.fib_add_two
    have e4 : Nat.fib (2 * m + 4) = Nat.fib (2 * m + 2) + Nat.fib (2 * m + 3) := Nat.fib_add_two
    have s : 4 * (m + 1) = 4 * m + 4 := by ring
    have t1 : 2 * (m + 1) + 2 = 2 * m + 4 := by ring
    have t2 : 2 * (m + 1) = 2 * m + 2 := by ring
    rw [s, oeis_a080239_step, ih, t1, t2, oeis_a080239_f0, e4, e3, e2]
    ring

theorem oeis_a080239_c1 (m : ℕ) :
    OMA.S_oeis_a080239.a (4 * m + 1) = Nat.fib (2 * m + 2) * Nat.fib (2 * m + 1) := by
  induction m with
  | zero => simp [OMA.S_oeis_a080239.a]
  | succ m ih =>
    have e2 : Nat.fib (2 * m + 2) = Nat.fib (2 * m) + Nat.fib (2 * m + 1) := Nat.fib_add_two
    have e3 : Nat.fib (2 * m + 3) = Nat.fib (2 * m + 1) + Nat.fib (2 * m + 2) := Nat.fib_add_two
    have e4 : Nat.fib (2 * m + 4) = Nat.fib (2 * m + 2) + Nat.fib (2 * m + 3) := Nat.fib_add_two
    have s : 4 * (m + 1) + 1 = 4 * m + 1 + 4 := by ring
    have t1 : 2 * (m + 1) + 2 = 2 * m + 4 := by ring
    have t2 : 2 * (m + 1) + 1 = 2 * m + 3 := by ring
    rw [s, oeis_a080239_step, ih, t1, t2, oeis_a080239_f1, e4, e3, e2]
    ring

theorem oeis_a080239_c2 (m : ℕ) :
    OMA.S_oeis_a080239.a (4 * m + 2) = Nat.fib (2 * m + 2) * Nat.fib (2 * m + 2) := by
  induction m with
  | zero => simp [OMA.S_oeis_a080239.a]
  | succ m ih =>
    have e2 : Nat.fib (2 * m + 2) = Nat.fib (2 * m) + Nat.fib (2 * m + 1) := Nat.fib_add_two
    have e3 : Nat.fib (2 * m + 3) = Nat.fib (2 * m + 1) + Nat.fib (2 * m + 2) := Nat.fib_add_two
    have e4 : Nat.fib (2 * m + 4) = Nat.fib (2 * m + 2) + Nat.fib (2 * m + 3) := Nat.fib_add_two
    have s : 4 * (m + 1) + 2 = 4 * m + 2 + 4 := by ring
    have t1 : 2 * (m + 1) + 2 = 2 * m + 4 := by ring
    rw [s, oeis_a080239_step, ih, t1, oeis_a080239_f2, e4, e3, e2]
    ring

theorem oeis_a080239_c3 (m : ℕ) :
    OMA.S_oeis_a080239.a (4 * m + 3) + 1 = Nat.fib (2 * m + 4) * Nat.fib (2 * m + 1) := by
  induction m with
  | zero =>
    have h3 : Nat.fib 3 = 2 := rfl
    have h4 : Nat.fib 4 = 3 := rfl
    simp [OMA.S_oeis_a080239.a, h3, h4]
  | succ m ih =>
    have e2 : Nat.fib (2 * m + 2) = Nat.fib (2 * m) + Nat.fib (2 * m + 1) := Nat.fib_add_two
    have e3 : Nat.fib (2 * m + 3) = Nat.fib (2 * m + 1) + Nat.fib (2 * m + 2) := Nat.fib_add_two
    have e4 : Nat.fib (2 * m + 4) = Nat.fib (2 * m + 2) + Nat.fib (2 * m + 3) := Nat.fib_add_two
    have e5 : Nat.fib (2 * m + 5) = Nat.fib (2 * m + 3) + Nat.fib (2 * m + 4) := Nat.fib_add_two
    have e6 : Nat.fib (2 * m + 6) = Nat.fib (2 * m + 4) + Nat.fib (2 * m + 5) := Nat.fib_add_two
    have s : 4 * (m + 1) + 3 = 4 * m + 3 + 4 := by ring
    have t1 : 2 * (m + 1) + 4 = 2 * m + 6 := by ring
    have t2 : 2 * (m + 1) + 1 = 2 * m + 3 := by ring
    have r : OMA.S_oeis_a080239.a (4 * m + 3) + Nat.fib (4 * m + 3 + 4) + 1 =
        (OMA.S_oeis_a080239.a (4 * m + 3) + 1) + Nat.fib (4 * m + 3 + 4) := by ring
    rw [s, oeis_a080239_step, r, ih, t1, t2, oeis_a080239_f3, e6, e5, e4, e3, e2]
    ring

theorem OMA.solution : type_of% @OMA.S_oeis_a080239.main := by
  intro n hn
  have h : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases h with h | h | h | h
  · obtain ⟨m, rfl⟩ : ∃ m, n = 4 * m := ⟨n / 4, by omega⟩
    have hp : OMA.S_oeis_a080239.p (4 * m) = 2 * m + 2 := by
      unfold OMA.S_oeis_a080239.p
      omega
    have hq : OMA.S_oeis_a080239.q (4 * m) = 2 := by
      unfold OMA.S_oeis_a080239.q
      rw [h]
      rfl
    have hs : 2 * m + 2 - 2 = 2 * m := by omega
    rw [hp, hq, hs, if_neg (by omega), Nat.sub_zero]
    exact oeis_a080239_c0 m
  · obtain ⟨m, rfl⟩ : ∃ m, n = 4 * m + 1 := ⟨n / 4, by omega⟩
    have hp : OMA.S_oeis_a080239.p (4 * m + 1) = 2 * m + 2 := by
      unfold OMA.S_oeis_a080239.p
      omega
    have hq : OMA.S_oeis_a080239.q (4 * m + 1) = 1 := by
      unfold OMA.S_oeis_a080239.q
      rw [h]
      rfl
    have hs : 2 * m + 2 - 1 = 2 * m + 1 := by omega
    rw [hp, hq, hs, if_neg (by omega), Nat.sub_zero]
    exact oeis_a080239_c1 m
  · obtain ⟨m, rfl⟩ : ∃ m, n = 4 * m + 2 := ⟨n / 4, by omega⟩
    have hp : OMA.S_oeis_a080239.p (4 * m + 2) = 2 * m + 2 := by
      unfold OMA.S_oeis_a080239.p
      omega
    have hq : OMA.S_oeis_a080239.q (4 * m + 2) = 0 := by
      unfold OMA.S_oeis_a080239.q
      rw [h]
      rfl
    rw [hp, hq, Nat.sub_zero, if_neg (by omega), Nat.sub_zero]
    exact oeis_a080239_c2 m
  · obtain ⟨m, rfl⟩ : ∃ m, n = 4 * m + 3 := ⟨n / 4, by omega⟩
    have hp : OMA.S_oeis_a080239.p (4 * m + 3) = 2 * m + 4 := by
      unfold OMA.S_oeis_a080239.p
      omega
    have hq : OMA.S_oeis_a080239.q (4 * m + 3) = 3 := by
      unfold OMA.S_oeis_a080239.q
      rw [h]
      rfl
    have hs : 2 * m + 4 - 3 = 2 * m + 1 := by omega
    rw [hp, hq, hs, if_pos h]
    exact Nat.eq_sub_of_add_eq (oeis_a080239_c3 m)
