import OMAStatements.S_oeis_a329421

-- Problem: A329421: a(n) = gcd(A330050(n), A330051(n)).
-- Upstream: formal-conjectures statements/oeis-a329421.lean:0 (declaration OMA.S_oeis_a329421.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: put u = F(2m), v = F(2m+1), so v^2 - uv - u^2 = 1 (Cassini). Every Fibonacci
-- number in A330050(4m+r) and A330051(4m+r) is a polynomial in u, v, and the two values are G*P
-- and G*Q with G = 5F(4m+1)F(2m), L(4m+2)L(2m+1), F(4m+3)L(2m+1), L(4m+4)F(2m+2) for
-- r = 0, 1, 2, 3, where P, Q are among L(2m+1) = 2u+v, F(2m) = u, 5F(2m+2) = 5(u+v); these are
-- coprime by explicit Bezout identities, so a(4m+r) = G. Each G is a product of a sequence with
-- x(m+2) = 7x(m+1) - x(m) and one with y(m+2) = 3y(m+1) - y(m), which gives the order-16
-- recurrence; the g.f. follows by comparing coefficients.

open OMA.S_oeis_a329421 in
theorem OMA.solution : type_of% @OMA.S_oeis_a329421.main := by
  have hF0 : ∀ k : ℕ, F (k : ℤ) = (Nat.fib k : ℤ) := fun k => rfl
  have hF1 : ∀ k : ℕ, F ((k : ℤ) + 1) = (Nat.fib (k + 1) : ℤ) := fun k => rfl
  have hF2 : ∀ k : ℕ, F (2 * (k : ℤ) + 1) = (Nat.fib (2 * k + 1) : ℤ) := fun k => rfl
  have hF4 : ∀ k : ℕ, F ((k : ℤ) + 4) = (Nat.fib (k + 4) : ℤ) := fun k => rfl
  have hrec : ∀ k : ℕ, (Nat.fib (k + 2) : ℤ) = Nat.fib k + Nat.fib (k + 1) := by
    intro k
    exact_mod_cast Nat.fib_add_two
  have hFm2 : ∀ k : ℕ, F ((k : ℤ) - 2) = 2 * (Nat.fib k : ℤ) - Nat.fib (k + 1) := by
    intro k
    match k with
    | 0 => rfl
    | 1 => rfl
    | j + 2 =>
      have e : ((j + 2 : ℕ) : ℤ) - 2 = (j : ℤ) := by omega
      rw [e, hF0]
      have h2 : (Nat.fib (j + 2) : ℤ) = Nat.fib j + Nat.fib (j + 1) := hrec j
      have h3 : (Nat.fib (j + 2 + 1) : ℤ) = Nat.fib (j + 1) + Nat.fib (j + 2) := hrec (j + 1)
      linear_combination h3 - h2
  have hcas : ∀ k : ℕ, (Nat.fib (k + 1) : ℤ) ^ 2 - Nat.fib (k + 1) * Nat.fib k -
      (Nat.fib k : ℤ) ^ 2 = (-1) ^ k := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      have h : (Nat.fib (k + 1 + 1) : ℤ) = Nat.fib k + Nat.fib (k + 1) := hrec k
      rw [h]
      linear_combination (-1 : ℤ) * ih
  have hdiv : ∀ y : ℤ, 2 * y / 2 = y := fun y => by omega
  have S50a : ∀ n : ℕ, (-1 : ℤ) ^ n = 1 →
      A330050 n = 5 * (Nat.fib (n + 1) : ℤ) ^ 2 - 5 * Nat.fib (n + 1) := by
    intro n h
    have d : ((3 : ℤ) * 1 + 7) / 2 = 5 := by norm_num
    unfold A330050
    rw [hF1, hF0, h, d]
    ring
  have S50b : ∀ n : ℕ, (-1 : ℤ) ^ n = -1 →
      A330050 n = 5 * (Nat.fib (n + 1) : ℤ) ^ 2 - 2 * Nat.fib (n + 1) - 4 * Nat.fib n + 4 := by
    intro n h
    have d : ((3 : ℤ) * -1 + 7) / 2 = 2 := by norm_num
    unfold A330050
    rw [hF1, hF0, h, d]
    ring
  have S51a : ∀ n : ℕ, (-1 : ℤ) ^ n = 1 →
      A330051 n = 1 + Nat.fib (2 * n + 1) - 2 * (Nat.fib (n + 1) : ℤ) := by
    intro n h
    have i2 : (Nat.fib (n + 2) : ℤ) = Nat.fib n + Nat.fib (n + 1) := hrec n
    have i3 : (Nat.fib (n + 3) : ℤ) = Nat.fib (n + 1) + Nat.fib (n + 2) := hrec (n + 1)
    have i4 : (Nat.fib (n + 4) : ℤ) = Nat.fib (n + 2) + Nat.fib (n + 3) := hrec (n + 2)
    have hn : (Nat.fib (n + 4) : ℤ) - (-1) ^ n * (2 * (Nat.fib n : ℤ) - Nat.fib (n + 1)) =
        2 * (2 * (Nat.fib (n + 1) : ℤ)) := by
      rw [h, i4, i3, i2]
      ring
    unfold A330051
    rw [hF2, hF4, hFm2, hn, hdiv]
  have S51b : ∀ n : ℕ, (-1 : ℤ) ^ n = -1 →
      A330051 n = 1 + Nat.fib (2 * n + 1) - (Nat.fib n + (Nat.fib (n + 2) : ℤ)) := by
    intro n h
    have i2 : (Nat.fib (n + 2) : ℤ) = Nat.fib n + Nat.fib (n + 1) := hrec n
    have i3 : (Nat.fib (n + 3) : ℤ) = Nat.fib (n + 1) + Nat.fib (n + 2) := hrec (n + 1)
    have i4 : (Nat.fib (n + 4) : ℤ) = Nat.fib (n + 2) + Nat.fib (n + 3) := hrec (n + 2)
    have hn : (Nat.fib (n + 4) : ℤ) - (-1) ^ n * (2 * (Nat.fib n : ℤ) - Nat.fib (n + 1)) =
        2 * (Nat.fib n + (Nat.fib (n + 2) : ℤ)) := by
      rw [h, i4, i3, i2]
      ring
    unfold A330051
    rw [hF2, hF4, hFm2, hn, hdiv]
  have base : ∀ m : ℕ, ∀ u v : ℤ, (Nat.fib (2 * m) : ℤ) = u → (Nat.fib (2 * m + 1) : ℤ) = v →
      v ^ 2 - v * u - u ^ 2 = 1 ∧ (Nat.fib (2 * m + 2) : ℤ) = u + v ∧
      (Nat.fib (4 * m) : ℤ) = -u ^ 2 + 2 * u * v ∧
      (Nat.fib (4 * m + 1) : ℤ) = u ^ 2 + v ^ 2 ∧
      (Nat.fib (4 * m + 2) : ℤ) = 2 * u * v + v ^ 2 ∧
      (Nat.fib (4 * m + 3) : ℤ) = u ^ 2 + 2 * u * v + 2 * v ^ 2 ∧
      (Nat.fib (4 * m + 4) : ℤ) = u ^ 2 + 4 * u * v + 3 * v ^ 2 ∧
      (Nat.fib (4 * m + 5) : ℤ) = 2 * u ^ 2 + 6 * u * v + 5 * v ^ 2 ∧
      (Nat.fib (4 * m + 6) : ℤ) = 3 * u ^ 2 + 10 * u * v + 8 * v ^ 2 ∧
      (Nat.fib (4 * m + 7) : ℤ) = 5 * u ^ 2 + 16 * u * v + 13 * v ^ 2 ∧
      (Nat.fib (8 * m + 1) : ℤ) = 2 * u ^ 4 - 4 * u ^ 3 * v + 6 * u ^ 2 * v ^ 2 + v ^ 4 ∧
      (Nat.fib (8 * m + 3) : ℤ) = u ^ 4 + 6 * u ^ 2 * v ^ 2 + 4 * u * v ^ 3 + 2 * v ^ 4 ∧
      (Nat.fib (8 * m + 5) : ℤ) =
        u ^ 4 + 4 * u ^ 3 * v + 12 * u ^ 2 * v ^ 2 + 12 * u * v ^ 3 + 5 * v ^ 4 ∧
      (Nat.fib (8 * m + 7) : ℤ) =
        2 * u ^ 4 + 12 * u ^ 3 * v + 30 * u ^ 2 * v ^ 2 + 32 * u * v ^ 3 + 13 * v ^ 4 := by
    intro m u v hu hv
    have cass : v ^ 2 - v * u - u ^ 2 = 1 := by
      rw [← hu, ← hv, hcas (2 * m), pow_mul]
      norm_num
    have U2 : (Nat.fib (2 * m + 2) : ℤ) = u + v := by
      rw [hrec (2 * m), hu, hv]
    have E1 : (Nat.fib (4 * m + 1) : ℤ) = u ^ 2 + v ^ 2 := by
      have h := Nat.fib_add (2 * m) (2 * m)
      rw [show 2 * m + 2 * m + 1 = 4 * m + 1 by ring] at h
      rw [h]
      push_cast
      rw [hu, hv]
      ring
    have E2 : (Nat.fib (4 * m + 2) : ℤ) = 2 * u * v + v ^ 2 := by
      have h := Nat.fib_add (2 * m) (2 * m + 1)
      rw [show 2 * m + (2 * m + 1) + 1 = 4 * m + 2 by ring,
        show 2 * m + 1 + 1 = 2 * m + 2 from rfl] at h
      rw [h]
      push_cast
      rw [U2, hu, hv]
      ring
    have E0 : (Nat.fib (4 * m) : ℤ) = -u ^ 2 + 2 * u * v := by
      have h : (Nat.fib (4 * m + 2) : ℤ) = Nat.fib (4 * m) + Nat.fib (4 * m + 1) := hrec (4 * m)
      linear_combination E2 - E1 - h
    have E3 : (Nat.fib (4 * m + 3) : ℤ) = u ^ 2 + 2 * u * v + 2 * v ^ 2 := by
      have h : (Nat.fib (4 * m + 3) : ℤ) = Nat.fib (4 * m + 1) + Nat.fib (4 * m + 2) :=
        hrec (4 * m + 1)
      rw [h, E1, E2]
      ring
    have E4 : (Nat.fib (4 * m + 4) : ℤ) = u ^ 2 + 4 * u * v + 3 * v ^ 2 := by
      have h : (Nat.fib (4 * m + 4) : ℤ) = Nat.fib (4 * m + 2) + Nat.fib (4 * m + 3) :=
        hrec (4 * m + 2)
      rw [h, E2, E3]
      ring
    have E5 : (Nat.fib (4 * m + 5) : ℤ) = 2 * u ^ 2 + 6 * u * v + 5 * v ^ 2 := by
      have h : (Nat.fib (4 * m + 5) : ℤ) = Nat.fib (4 * m + 3) + Nat.fib (4 * m + 4) :=
        hrec (4 * m + 3)
      rw [h, E3, E4]
      ring
    have E6 : (Nat.fib (4 * m + 6) : ℤ) = 3 * u ^ 2 + 10 * u * v + 8 * v ^ 2 := by
      have h : (Nat.fib (4 * m + 6) : ℤ) = Nat.fib (4 * m + 4) + Nat.fib (4 * m + 5) :=
        hrec (4 * m + 4)
      rw [h, E4, E5]
      ring
    have E7 : (Nat.fib (4 * m + 7) : ℤ) = 5 * u ^ 2 + 16 * u * v + 13 * v ^ 2 := by
      have h : (Nat.fib (4 * m + 7) : ℤ) = Nat.fib (4 * m + 5) + Nat.fib (4 * m + 6) :=
        hrec (4 * m + 5)
      rw [h, E5, E6]
      ring
    have B1 : (Nat.fib (8 * m + 1) : ℤ) = 2 * u ^ 4 - 4 * u ^ 3 * v + 6 * u ^ 2 * v ^ 2 + v ^ 4 := by
      have h := Nat.fib_add (4 * m) (4 * m)
      rw [show 4 * m + 4 * m + 1 = 8 * m + 1 by ring] at h
      rw [h]
      push_cast
      rw [E0, E1]
      ring
    have B3 : (Nat.fib (8 * m + 3) : ℤ) = u ^ 4 + 6 * u ^ 2 * v ^ 2 + 4 * u * v ^ 3 + 2 * v ^ 4 := by
      have h := Nat.fib_add (4 * m) (4 * m + 2)
      rw [show 4 * m + (4 * m + 2) + 1 = 8 * m + 3 by ring,
        show 4 * m + 2 + 1 = 4 * m + 3 from rfl] at h
      rw [h]
      push_cast
      rw [E0, E1, E2, E3]
      ring
    have B5 : (Nat.fib (8 * m + 5) : ℤ) =
        u ^ 4 + 4 * u ^ 3 * v + 12 * u ^ 2 * v ^ 2 + 12 * u * v ^ 3 + 5 * v ^ 4 := by
      have h := Nat.fib_add (4 * m) (4 * m + 4)
      rw [show 4 * m + (4 * m + 4) + 1 = 8 * m + 5 by ring,
        show 4 * m + 4 + 1 = 4 * m + 5 from rfl] at h
      rw [h]
      push_cast
      rw [E0, E1, E4, E5]
      ring
    have B7 : (Nat.fib (8 * m + 7) : ℤ) =
        2 * u ^ 4 + 12 * u ^ 3 * v + 30 * u ^ 2 * v ^ 2 + 32 * u * v ^ 3 + 13 * v ^ 4 := by
      have h := Nat.fib_add (4 * m) (4 * m + 6)
      rw [show 4 * m + (4 * m + 6) + 1 = 8 * m + 7 by ring,
        show 4 * m + 6 + 1 = 4 * m + 7 from rfl] at h
      rw [h]
      push_cast
      rw [E0, E1, E6, E7]
      ring
    exact ⟨cass, U2, E0, E1, E2, E3, E4, E5, E6, E7, B1, B3, B5, B7⟩
  have c0 : ∀ m : ℕ, (a (4 * m) : ℤ) = 5 * Nat.fib (4 * m + 1) * (Nat.fib (2 * m) : ℤ) := by
    intro m
    obtain ⟨u, hu⟩ : ∃ u : ℤ, (Nat.fib (2 * m) : ℤ) = u := ⟨_, rfl⟩
    obtain ⟨v, hv⟩ : ∃ v : ℤ, (Nat.fib (2 * m + 1) : ℤ) = v := ⟨_, rfl⟩
    obtain ⟨cass, U2, -, E1, -, -, -, -, -, -, B1, -, -, -⟩ := base m u v hu hv
    have p : (-1 : ℤ) ^ (4 * m) = 1 := by
      rw [pow_mul]
      norm_num
    have hX : A330050 (4 * m) = 5 * Nat.fib (4 * m + 1) * (Nat.fib (2 * m) : ℤ) *
        (Nat.fib (2 * m) + (Nat.fib (2 * m + 2) : ℤ)) := by
      rw [S50a _ p, E1, U2, hu]
      linear_combination (5 * u ^ 2 + 5 * v ^ 2) * cass
    have hY : A330051 (4 * m) = 5 * Nat.fib (4 * m + 1) * (Nat.fib (2 * m) : ℤ) *
        (Nat.fib (2 * m) : ℤ) := by
      rw [S51a _ p, show 2 * (4 * m) + 1 = 8 * m + 1 by ring, B1, E1, hu]
      linear_combination (3 * u ^ 2 + u * v + v ^ 2 - 1) * cass
    have hc : IsCoprime ((Nat.fib (2 * m) : ℤ) + Nat.fib (2 * m + 2)) (Nat.fib (2 * m) : ℤ) := by
      rw [U2, hu]
      exact ⟨v, -(3 * v + u), by linear_combination cass⟩
    have hG : (0 : ℤ) ≤ 5 * Nat.fib (4 * m + 1) * (Nat.fib (2 * m) : ℤ) := by positivity
    unfold a
    rw [hX, hY, Int.gcd_mul_left, Int.isCoprime_iff_gcd_eq_one.mp hc, mul_one,
      Int.natAbs_of_nonneg hG]
  have c1 : ∀ m : ℕ, (a (4 * m + 1) : ℤ) =
      (Nat.fib (4 * m + 1) + Nat.fib (4 * m + 3)) * (Nat.fib (2 * m) + (Nat.fib (2 * m + 2) : ℤ)) := by
    intro m
    obtain ⟨u, hu⟩ : ∃ u : ℤ, (Nat.fib (2 * m) : ℤ) = u := ⟨_, rfl⟩
    obtain ⟨v, hv⟩ : ∃ v : ℤ, (Nat.fib (2 * m + 1) : ℤ) = v := ⟨_, rfl⟩
    obtain ⟨cass, U2, -, E1, E2, E3, -, -, -, -, -, B3, -, -⟩ := base m u v hu hv
    have p : (-1 : ℤ) ^ (4 * m + 1) = -1 := by
      rw [pow_succ, pow_mul]
      norm_num
    have hX : A330050 (4 * m + 1) =
        (Nat.fib (4 * m + 1) + Nat.fib (4 * m + 3)) * (Nat.fib (2 * m) + (Nat.fib (2 * m + 2) : ℤ)) *
          (Nat.fib (2 * m) + (Nat.fib (2 * m + 2) : ℤ)) := by
      rw [S50b _ p, show 4 * m + 1 + 1 = 4 * m + 2 from rfl, E2, E1, E3, U2, hu]
      linear_combination (8 * u ^ 2 + 8 * u * v + 2 * v ^ 2 - 4) * cass
    have hY : A330051 (4 * m + 1) =
        (Nat.fib (4 * m + 1) + Nat.fib (4 * m + 3)) * (Nat.fib (2 * m) + (Nat.fib (2 * m + 2) : ℤ)) *
          (Nat.fib (2 * m) : ℤ) := by
      rw [S51b _ p, show 2 * (4 * m + 1) + 1 = 8 * m + 3 by ring,
        show 4 * m + 1 + 2 = 4 * m + 3 from rfl, B3, E1, E3, U2, hu]
      linear_combination (3 * u ^ 2 + 3 * u * v + 2 * v ^ 2 - 1) * cass
    have hc : IsCoprime ((Nat.fib (2 * m) : ℤ) + Nat.fib (2 * m + 2)) (Nat.fib (2 * m) : ℤ) := by
      rw [U2, hu]
      exact ⟨v, -(3 * v + u), by linear_combination cass⟩
    have hG : (0 : ℤ) ≤ (Nat.fib (4 * m + 1) + Nat.fib (4 * m + 3)) *
        (Nat.fib (2 * m) + (Nat.fib (2 * m + 2) : ℤ)) := by positivity
    unfold a
    rw [hX, hY, Int.gcd_mul_left, Int.isCoprime_iff_gcd_eq_one.mp hc, mul_one,
      Int.natAbs_of_nonneg hG]
  have c2 : ∀ m : ℕ, (a (4 * m + 2) : ℤ) =
      Nat.fib (4 * m + 3) * (Nat.fib (2 * m) + (Nat.fib (2 * m + 2) : ℤ)) := by
    intro m
    obtain ⟨u, hu⟩ : ∃ u : ℤ, (Nat.fib (2 * m) : ℤ) = u := ⟨_, rfl⟩
    obtain ⟨v, hv⟩ : ∃ v : ℤ, (Nat.fib (2 * m + 1) : ℤ) = v := ⟨_, rfl⟩
    obtain ⟨cass, U2, -, -, -, E3, -, -, -, -, -, -, B5, -⟩ := base m u v hu hv
    have p : (-1 : ℤ) ^ (4 * m + 2) = 1 := by
      rw [pow_add, pow_mul]
      norm_num
    have hX : A330050 (4 * m + 2) =
        Nat.fib (4 * m + 3) * (Nat.fib (2 * m) + (Nat.fib (2 * m + 2) : ℤ)) *
          (5 * (Nat.fib (2 * m + 2) : ℤ)) := by
      rw [S50a _ p, show 4 * m + 2 + 1 = 4 * m + 3 from rfl, E3, U2, hu]
      linear_combination (5 * u ^ 2 + 10 * u * v + 10 * v ^ 2) * cass
    have hY : A330051 (4 * m + 2) =
        Nat.fib (4 * m + 3) * (Nat.fib (2 * m) + (Nat.fib (2 * m + 2) : ℤ)) *
          (Nat.fib (2 * m) + (Nat.fib (2 * m + 2) : ℤ)) := by
      rw [S51a _ p, show 2 * (4 * m + 2) + 1 = 8 * m + 5 by ring,
        show 4 * m + 2 + 1 = 4 * m + 3 from rfl, B5, E3, U2, hu]
      linear_combination (3 * u ^ 2 + 5 * u * v + 3 * v ^ 2 - 1) * cass
    have hc : IsCoprime (5 * (Nat.fib (2 * m + 2) : ℤ))
        ((Nat.fib (2 * m) : ℤ) + Nat.fib (2 * m + 2)) := by
      rw [U2, hu]
      have h5 : IsCoprime (5 : ℤ) (u + (u + v)) :=
        ⟨1 - v ^ 2, u + (u + v), by linear_combination (-4 : ℤ) * cass⟩
      have h1 : IsCoprime (u + v) (u + (u + v)) := ⟨2 * v - u, -v, by linear_combination cass⟩
      exact h5.mul_left h1
    have hG : (0 : ℤ) ≤ Nat.fib (4 * m + 3) * (Nat.fib (2 * m) + (Nat.fib (2 * m + 2) : ℤ)) := by
      positivity
    unfold a
    rw [hX, hY, Int.gcd_mul_left, Int.isCoprime_iff_gcd_eq_one.mp hc, mul_one,
      Int.natAbs_of_nonneg hG]
  have c3 : ∀ m : ℕ, (a (4 * m + 3) : ℤ) =
      (Nat.fib (4 * m + 3) + Nat.fib (4 * m + 5)) * (Nat.fib (2 * m + 2) : ℤ) := by
    intro m
    obtain ⟨u, hu⟩ : ∃ u : ℤ, (Nat.fib (2 * m) : ℤ) = u := ⟨_, rfl⟩
    obtain ⟨v, hv⟩ : ∃ v : ℤ, (Nat.fib (2 * m + 1) : ℤ) = v := ⟨_, rfl⟩
    obtain ⟨cass, U2, -, -, -, E3, E4, E5, -, -, -, -, -, B7⟩ := base m u v hu hv
    have p : (-1 : ℤ) ^ (4 * m + 3) = -1 := by
      rw [pow_add, pow_mul]
      norm_num
    have hX : A330050 (4 * m + 3) =
        (Nat.fib (4 * m + 3) + Nat.fib (4 * m + 5)) * (Nat.fib (2 * m + 2) : ℤ) *
          (5 * (Nat.fib (2 * m + 2) : ℤ)) := by
      rw [S50b _ p, show 4 * m + 3 + 1 = 4 * m + 4 from rfl, E4, E3, E5, U2]
      linear_combination (10 * u ^ 2 + 20 * u * v + 10 * v ^ 2 - 4) * cass
    have hY : A330051 (4 * m + 3) =
        (Nat.fib (4 * m + 3) + Nat.fib (4 * m + 5)) * (Nat.fib (2 * m + 2) : ℤ) *
          (Nat.fib (2 * m) + (Nat.fib (2 * m + 2) : ℤ)) := by
      rw [S51b _ p, show 2 * (4 * m + 3) + 1 = 8 * m + 7 by ring,
        show 4 * m + 3 + 2 = 4 * m + 5 from rfl, B7, E3, E5, U2, hu]
      linear_combination (4 * u ^ 2 + 9 * u * v + 6 * v ^ 2 - 1) * cass
    have hc : IsCoprime (5 * (Nat.fib (2 * m + 2) : ℤ))
        ((Nat.fib (2 * m) : ℤ) + Nat.fib (2 * m + 2)) := by
      rw [U2, hu]
      have h5 : IsCoprime (5 : ℤ) (u + (u + v)) :=
        ⟨1 - v ^ 2, u + (u + v), by linear_combination (-4 : ℤ) * cass⟩
      have h1 : IsCoprime (u + v) (u + (u + v)) := ⟨2 * v - u, -v, by linear_combination cass⟩
      exact h5.mul_left h1
    have hG : (0 : ℤ) ≤ (Nat.fib (4 * m + 3) + Nat.fib (4 * m + 5)) * (Nat.fib (2 * m + 2) : ℤ) := by
      positivity
    unfold a
    rw [hX, hY, Int.gcd_mul_left, Int.isCoprime_iff_gcd_eq_one.mp hc, mul_one,
      Int.natAbs_of_nonneg hG]
  have R7 : ∀ k : ℕ, (Nat.fib (k + 8) : ℤ) = 7 * Nat.fib (k + 4) - Nat.fib k := by
    intro k
    have h2 : (Nat.fib (k + 2) : ℤ) = Nat.fib k + Nat.fib (k + 1) := hrec k
    have h3 : (Nat.fib (k + 3) : ℤ) = Nat.fib (k + 1) + Nat.fib (k + 2) := hrec (k + 1)
    have h4 : (Nat.fib (k + 4) : ℤ) = Nat.fib (k + 2) + Nat.fib (k + 3) := hrec (k + 2)
    have h5 : (Nat.fib (k + 5) : ℤ) = Nat.fib (k + 3) + Nat.fib (k + 4) := hrec (k + 3)
    have h6 : (Nat.fib (k + 6) : ℤ) = Nat.fib (k + 4) + Nat.fib (k + 5) := hrec (k + 4)
    have h7 : (Nat.fib (k + 7) : ℤ) = Nat.fib (k + 5) + Nat.fib (k + 6) := hrec (k + 5)
    have h8 : (Nat.fib (k + 8) : ℤ) = Nat.fib (k + 6) + Nat.fib (k + 7) := hrec (k + 6)
    rw [h8, h7, h6, h5, h4, h3, h2]
    ring
  have R3 : ∀ k : ℕ, (Nat.fib (k + 4) : ℤ) = 3 * Nat.fib (k + 2) - Nat.fib k := by
    intro k
    have h2 : (Nat.fib (k + 2) : ℤ) = Nat.fib k + Nat.fib (k + 1) := hrec k
    have h3 : (Nat.fib (k + 3) : ℤ) = Nat.fib (k + 1) + Nat.fib (k + 2) := hrec (k + 1)
    have h4 : (Nat.fib (k + 4) : ℤ) = Nat.fib (k + 2) + Nat.fib (k + 3) := hrec (k + 2)
    rw [h4, h3, h2]
    ring
  have X7 : ∀ c j : ℕ, (Nat.fib (4 * (j + 2) + c) : ℤ) =
      7 * Nat.fib (4 * (j + 1) + c) - Nat.fib (4 * j + c) := by
    intro c j
    rw [show 4 * (j + 2) + c = 4 * j + c + 8 by ring, show 4 * (j + 1) + c = 4 * j + c + 4 by ring]
    exact R7 (4 * j + c)
  have Y3 : ∀ c j : ℕ, (Nat.fib (2 * (j + 2) + c) : ℤ) =
      3 * Nat.fib (2 * (j + 1) + c) - Nat.fib (2 * j + c) := by
    intro c j
    rw [show 2 * (j + 2) + c = 2 * j + c + 4 by ring, show 2 * (j + 1) + c = 2 * j + c + 2 by ring]
    exact R3 (2 * j + c)
  have Y30 : ∀ j : ℕ, (Nat.fib (2 * (j + 2)) : ℤ) = 3 * Nat.fib (2 * (j + 1)) - Nat.fib (2 * j) := by
    intro j
    rw [show 2 * (j + 2) = 2 * j + 4 by ring, show 2 * (j + 1) = 2 * j + 2 by ring]
    exact R3 (2 * j)
  have X7' : ∀ c m : ℕ,
      (Nat.fib (4 * (m + 2) + c) : ℤ) = 7 * Nat.fib (4 * (m + 1) + c) - Nat.fib (4 * m + c) ∧
      (Nat.fib (4 * (m + 3) + c) : ℤ) = 7 * Nat.fib (4 * (m + 2) + c) - Nat.fib (4 * (m + 1) + c) ∧
      (Nat.fib (4 * (m + 4) + c) : ℤ) = 7 * Nat.fib (4 * (m + 3) + c) - Nat.fib (4 * (m + 2) + c) :=
    fun c m => ⟨X7 c m, X7 c (m + 1), X7 c (m + 2)⟩
  have Y3' : ∀ c m : ℕ,
      (Nat.fib (2 * (m + 2) + c) : ℤ) = 3 * Nat.fib (2 * (m + 1) + c) - Nat.fib (2 * m + c) ∧
      (Nat.fib (2 * (m + 3) + c) : ℤ) = 3 * Nat.fib (2 * (m + 2) + c) - Nat.fib (2 * (m + 1) + c) ∧
      (Nat.fib (2 * (m + 4) + c) : ℤ) = 3 * Nat.fib (2 * (m + 3) + c) - Nat.fib (2 * (m + 2) + c) :=
    fun c m => ⟨Y3 c m, Y3 c (m + 1), Y3 c (m + 2)⟩
  have Y30' : ∀ m : ℕ,
      (Nat.fib (2 * (m + 2)) : ℤ) = 3 * Nat.fib (2 * (m + 1)) - Nat.fib (2 * m) ∧
      (Nat.fib (2 * (m + 3)) : ℤ) = 3 * Nat.fib (2 * (m + 2)) - Nat.fib (2 * (m + 1)) ∧
      (Nat.fib (2 * (m + 4)) : ℤ) = 3 * Nat.fib (2 * (m + 3)) - Nat.fib (2 * (m + 2)) :=
    fun m => ⟨Y30 m, Y30 (m + 1), Y30 (m + 2)⟩
  have hrecZ : ∀ n : ℕ, 16 ≤ n →
      (a n : ℤ) = 21 * (a (n - 4) : ℤ) - 56 * (a (n - 8) : ℤ) + 21 * (a (n - 12) : ℤ) -
        (a (n - 16) : ℤ) := by
    intro n hn
    obtain ⟨m, rfl | rfl | rfl | rfl⟩ : ∃ m, n = 4 * (m + 4) ∨ n = 4 * (m + 4) + 1 ∨
        n = 4 * (m + 4) + 2 ∨ n = 4 * (m + 4) + 3 := ⟨n / 4 - 4, by omega⟩
    · obtain ⟨x0, x1, x2⟩ := X7' 1 m
      obtain ⟨y0, y1, y2⟩ := Y30' m
      rw [show 4 * (m + 4) - 4 = 4 * (m + 3) by omega, show 4 * (m + 4) - 8 = 4 * (m + 2) by omega,
        show 4 * (m + 4) - 12 = 4 * (m + 1) by omega, show 4 * (m + 4) - 16 = 4 * m by omega,
        c0 (m + 4), c0 (m + 3), c0 (m + 2), c0 (m + 1), c0 m, x2, x1, x0, y2, y1, y0]
      ring
    · obtain ⟨x0, x1, x2⟩ := X7' 1 m
      obtain ⟨z0, z1, z2⟩ := X7' 3 m
      obtain ⟨y0, y1, y2⟩ := Y30' m
      obtain ⟨w0, w1, w2⟩ := Y3' 2 m
      rw [show 4 * (m + 4) + 1 - 4 = 4 * (m + 3) + 1 by omega,
        show 4 * (m + 4) + 1 - 8 = 4 * (m + 2) + 1 by omega,
        show 4 * (m + 4) + 1 - 12 = 4 * (m + 1) + 1 by omega,
        show 4 * (m + 4) + 1 - 16 = 4 * m + 1 by omega,
        c1 (m + 4), c1 (m + 3), c1 (m + 2), c1 (m + 1), c1 m, x2, x1, x0, z2, z1, z0,
        y2, y1, y0, w2, w1, w0]
      ring
    · obtain ⟨z0, z1, z2⟩ := X7' 3 m
      obtain ⟨y0, y1, y2⟩ := Y30' m
      obtain ⟨w0, w1, w2⟩ := Y3' 2 m
      rw [show 4 * (m + 4) + 2 - 4 = 4 * (m + 3) + 2 by omega,
        show 4 * (m + 4) + 2 - 8 = 4 * (m + 2) + 2 by omega,
        show 4 * (m + 4) + 2 - 12 = 4 * (m + 1) + 2 by omega,
        show 4 * (m + 4) + 2 - 16 = 4 * m + 2 by omega,
        c2 (m + 4), c2 (m + 3), c2 (m + 2), c2 (m + 1), c2 m, z2, z1, z0,
        y2, y1, y0, w2, w1, w0]
      ring
    · obtain ⟨z0, z1, z2⟩ := X7' 3 m
      obtain ⟨t0, t1, t2⟩ := X7' 5 m
      obtain ⟨w0, w1, w2⟩ := Y3' 2 m
      rw [show 4 * (m + 4) + 3 - 4 = 4 * (m + 3) + 3 by omega,
        show 4 * (m + 4) + 3 - 8 = 4 * (m + 2) + 3 by omega,
        show 4 * (m + 4) + 3 - 12 = 4 * (m + 1) + 3 by omega,
        show 4 * (m + 4) + 3 - 16 = 4 * m + 3 by omega,
        c3 (m + 4), c3 (m + 3), c3 (m + 2), c3 (m + 1), c3 m, z2, z1, z0,
        t2, t1, t0, w2, w1, w0]
      ring
  refine ⟨?_, hrecZ⟩
  have v0 : (a 0 : ℚ) = 0 := by
    have h : (a (4 * 0) : ℤ) = 0 := by
      rw [c0 0]
      decide
    exact_mod_cast h
  have v1 : (a 1 : ℚ) = 3 := by
    have h : (a (4 * 0 + 1) : ℤ) = 3 := by
      rw [c1 0]
      decide
    exact_mod_cast h
  have v2 : (a 2 : ℚ) = 2 := by
    have h : (a (4 * 0 + 2) : ℤ) = 2 := by
      rw [c2 0]
      decide
    exact_mod_cast h
  have v3 : (a 3 : ℚ) = 7 := by
    have h : (a (4 * 0 + 3) : ℤ) = 7 := by
      rw [c3 0]
      decide
    exact_mod_cast h
  have v4 : (a 4 : ℚ) = 25 := by
    have h : (a (4 * 1) : ℤ) = 25 := by
      rw [c0 1]
      decide
    exact_mod_cast h
  have v5 : (a 5 : ℚ) = 72 := by
    have h : (a (4 * 1 + 1) : ℤ) = 72 := by
      rw [c1 1]
      decide
    exact_mod_cast h
  have v6 : (a 6 : ℚ) = 52 := by
    have h : (a (4 * 1 + 2) : ℤ) = 52 := by
      rw [c2 1]
      decide
    exact_mod_cast h
  have v7 : (a 7 : ℚ) = 141 := by
    have h : (a (4 * 1 + 3) : ℤ) = 141 := by
      rw [c3 1]
      decide
    exact_mod_cast h
  have v8 : (a 8 : ℚ) = 510 := by
    have h : (a (4 * 2) : ℤ) = 510 := by
      rw [c0 2]
      decide
    exact_mod_cast h
  have v9 : (a 9 : ℚ) = 1353 := by
    have h : (a (4 * 2 + 1) : ℤ) = 1353 := by
      rw [c1 2]
      decide
    exact_mod_cast h
  have v10 : (a 10 : ℚ) = 979 := by
    have h : (a (4 * 2 + 2) : ℤ) = 979 := by
      rw [c2 2]
      decide
    exact_mod_cast h
  have v11 : (a 11 : ℚ) = 2576 := by
    have h : (a (4 * 2 + 3) : ℤ) = 2576 := by
      rw [c3 2]
      decide
    exact_mod_cast h
  have v12 : (a 12 : ℚ) = 9320 := by
    have h : (a (4 * 3) : ℤ) = 9320 := by
      rw [c0 3]
      decide
    exact_mod_cast h
  have v13 : (a 13 : ℚ) = 24447 := by
    have h : (a (4 * 3 + 1) : ℤ) = 24447 := by
      rw [c1 3]
      decide
    exact_mod_cast h
  have v14 : (a 14 : ℚ) = 17690 := by
    have h : (a (4 * 3 + 2) : ℤ) = 17690 := by
      rw [c2 3]
      decide
    exact_mod_cast h
  have v15 : (a 15 : ℚ) = 46347 := by
    have h : (a (4 * 3 + 3) : ℤ) = 46347 := by
      rw [c3 3]
      decide
    exact_mod_cast h
  obtain ⟨A, hA⟩ : ∃ A : PowerSeries ℚ, A = PowerSeries.mk (fun n => (a n : ℚ)) := ⟨_, rfl⟩
  rw [← hA]
  have cA : ∀ m, PowerSeries.coeff m A = (a m : ℚ) := by
    intro m
    rw [hA, PowerSeries.coeff_mk]
  have h2 : (PowerSeries.C (2 : ℚ) : PowerSeries ℚ) = 2 := map_ofNat _ 2
  have h3 : (PowerSeries.C (3 : ℚ) : PowerSeries ℚ) = 3 := map_ofNat _ 3
  have h6 : (PowerSeries.C (6 : ℚ) : PowerSeries ℚ) = 6 := map_ofNat _ 6
  have h7 : (PowerSeries.C (7 : ℚ) : PowerSeries ℚ) = 7 := map_ofNat _ 7
  have h9 : (PowerSeries.C (9 : ℚ) : PowerSeries ℚ) = 9 := map_ofNat _ 9
  have h10 : (PowerSeries.C (10 : ℚ) : PowerSeries ℚ) = 10 := map_ofNat _ 10
  have h15 : (PowerSeries.C (15 : ℚ) : PowerSeries ℚ) = 15 := map_ofNat _ 15
  have h21 : (PowerSeries.C (21 : ℚ) : PowerSeries ℚ) = 21 := map_ofNat _ 21
  have h25 : (PowerSeries.C (25 : ℚ) : PowerSeries ℚ) = 25 := map_ofNat _ 25
  have h56 : (PowerSeries.C (56 : ℚ) : PowerSeries ℚ) = 56 := map_ofNat _ 56
  have e : A * ((1 + 4 * PowerSeries.X ^ 2 - PowerSeries.X ^ 4) * (1 + PowerSeries.X ^ 2 - PowerSeries.X ^ 4) *
      (1 - PowerSeries.X ^ 2 - PowerSeries.X ^ 4) * (1 - 4 * PowerSeries.X ^ 2 - PowerSeries.X ^ 4)) =
      A - PowerSeries.C (21 : ℚ) * (A * PowerSeries.X ^ 4) +
        PowerSeries.C (56 : ℚ) * (A * PowerSeries.X ^ 8) -
        PowerSeries.C (21 : ℚ) * (A * PowerSeries.X ^ 12) + A * PowerSeries.X ^ 16 := by
    rw [h21, h56]
    ring
  have e2 : (PowerSeries.X * (1 + PowerSeries.X) *
      (3 - PowerSeries.X + 8 * PowerSeries.X ^ 2 + 17 * PowerSeries.X ^ 3 - 8 * PowerSeries.X ^ 4 +
        18 * PowerSeries.X ^ 5 - 24 * PowerSeries.X ^ 6 + 9 * PowerSeries.X ^ 7 - PowerSeries.X ^ 9 +
        8 * PowerSeries.X ^ 10 + 2 * PowerSeries.X ^ 11 + PowerSeries.X ^ 12) : PowerSeries ℚ) =
      PowerSeries.C (3 : ℚ) * PowerSeries.X ^ 1 + PowerSeries.C (2 : ℚ) * PowerSeries.X ^ 2 +
        PowerSeries.C (7 : ℚ) * PowerSeries.X ^ 3 + PowerSeries.C (25 : ℚ) * PowerSeries.X ^ 4 +
        PowerSeries.C (9 : ℚ) * PowerSeries.X ^ 5 + PowerSeries.C (10 : ℚ) * PowerSeries.X ^ 6 -
        PowerSeries.C (6 : ℚ) * PowerSeries.X ^ 7 - PowerSeries.C (15 : ℚ) * PowerSeries.X ^ 8 +
        PowerSeries.C (9 : ℚ) * PowerSeries.X ^ 9 - PowerSeries.X ^ 10 +
        PowerSeries.C (7 : ℚ) * PowerSeries.X ^ 11 + PowerSeries.C (10 : ℚ) * PowerSeries.X ^ 12 +
        PowerSeries.C (3 : ℚ) * PowerSeries.X ^ 13 + PowerSeries.X ^ 14 := by
    rw [h3, h2, h7, h25, h9, h10, h6, h15]
    ring
  refine e.trans (Eq.trans ?_ e2.symm)
  ext m
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul]
  rcases Nat.lt_or_ge m 16 with hm | hm
  · interval_cases m <;> simp only [PowerSeries.coeff_mul_X_pow', cA, PowerSeries.coeff_X_pow] <;>
      norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15]
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 16 := ⟨m - 16, by omega⟩
    have t4 : PowerSeries.coeff (k + 16) (A * PowerSeries.X ^ 4) = (a (k + 12) : ℚ) := by
      rw [show k + 16 = k + 12 + 4 by omega, PowerSeries.coeff_mul_X_pow, cA]
    have t8 : PowerSeries.coeff (k + 16) (A * PowerSeries.X ^ 8) = (a (k + 8) : ℚ) := by
      rw [show k + 16 = k + 8 + 8 by omega, PowerSeries.coeff_mul_X_pow, cA]
    have t12 : PowerSeries.coeff (k + 16) (A * PowerSeries.X ^ 12) = (a (k + 4) : ℚ) := by
      rw [show k + 16 = k + 4 + 12 by omega, PowerSeries.coeff_mul_X_pow, cA]
    have t16 : PowerSeries.coeff (k + 16) (A * PowerSeries.X ^ 16) = (a k : ℚ) := by
      rw [PowerSeries.coeff_mul_X_pow, cA]
    have u1 : PowerSeries.coeff (k + 16) (PowerSeries.X ^ 1 : PowerSeries ℚ) = 0 := by
      rw [PowerSeries.coeff_X_pow, if_neg (show ¬(k + 16 = 1) by omega)]
    have u2 : PowerSeries.coeff (k + 16) (PowerSeries.X ^ 2 : PowerSeries ℚ) = 0 := by
      rw [PowerSeries.coeff_X_pow, if_neg (show ¬(k + 16 = 2) by omega)]
    have u3 : PowerSeries.coeff (k + 16) (PowerSeries.X ^ 3 : PowerSeries ℚ) = 0 := by
      rw [PowerSeries.coeff_X_pow, if_neg (show ¬(k + 16 = 3) by omega)]
    have u4 : PowerSeries.coeff (k + 16) (PowerSeries.X ^ 4 : PowerSeries ℚ) = 0 := by
      rw [PowerSeries.coeff_X_pow, if_neg (show ¬(k + 16 = 4) by omega)]
    have u5 : PowerSeries.coeff (k + 16) (PowerSeries.X ^ 5 : PowerSeries ℚ) = 0 := by
      rw [PowerSeries.coeff_X_pow, if_neg (show ¬(k + 16 = 5) by omega)]
    have u6 : PowerSeries.coeff (k + 16) (PowerSeries.X ^ 6 : PowerSeries ℚ) = 0 := by
      rw [PowerSeries.coeff_X_pow, if_neg (show ¬(k + 16 = 6) by omega)]
    have u7 : PowerSeries.coeff (k + 16) (PowerSeries.X ^ 7 : PowerSeries ℚ) = 0 := by
      rw [PowerSeries.coeff_X_pow, if_neg (show ¬(k + 16 = 7) by omega)]
    have u8 : PowerSeries.coeff (k + 16) (PowerSeries.X ^ 8 : PowerSeries ℚ) = 0 := by
      rw [PowerSeries.coeff_X_pow, if_neg (show ¬(k + 16 = 8) by omega)]
    have u9 : PowerSeries.coeff (k + 16) (PowerSeries.X ^ 9 : PowerSeries ℚ) = 0 := by
      rw [PowerSeries.coeff_X_pow, if_neg (show ¬(k + 16 = 9) by omega)]
    have u10 : PowerSeries.coeff (k + 16) (PowerSeries.X ^ 10 : PowerSeries ℚ) = 0 := by
      rw [PowerSeries.coeff_X_pow, if_neg (show ¬(k + 16 = 10) by omega)]
    have u11 : PowerSeries.coeff (k + 16) (PowerSeries.X ^ 11 : PowerSeries ℚ) = 0 := by
      rw [PowerSeries.coeff_X_pow, if_neg (show ¬(k + 16 = 11) by omega)]
    have u12 : PowerSeries.coeff (k + 16) (PowerSeries.X ^ 12 : PowerSeries ℚ) = 0 := by
      rw [PowerSeries.coeff_X_pow, if_neg (show ¬(k + 16 = 12) by omega)]
    have u13 : PowerSeries.coeff (k + 16) (PowerSeries.X ^ 13 : PowerSeries ℚ) = 0 := by
      rw [PowerSeries.coeff_X_pow, if_neg (show ¬(k + 16 = 13) by omega)]
    have u14 : PowerSeries.coeff (k + 16) (PowerSeries.X ^ 14 : PowerSeries ℚ) = 0 := by
      rw [PowerSeries.coeff_X_pow, if_neg (show ¬(k + 16 = 14) by omega)]
    have hq : (a (k + 16) : ℚ) = 21 * (a (k + 12) : ℚ) - 56 * (a (k + 8) : ℚ) +
        21 * (a (k + 4) : ℚ) - (a k : ℚ) := by
      have h := hrecZ (k + 16) (by omega)
      rw [show k + 16 - 4 = k + 12 by omega, show k + 16 - 8 = k + 8 by omega,
        show k + 16 - 12 = k + 4 by omega, show k + 16 - 16 = k by omega] at h
      exact_mod_cast h
    rw [cA (k + 16), t4, t8, t12, t16, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11, u12, u13, u14]
    linear_combination hq