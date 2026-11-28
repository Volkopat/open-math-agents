import OMAStatements.S_oeis_a095116

-- Problem: A095116: a(n) = prime(n) + n - 1.
-- Upstream: formal-conjectures statements/oeis-a095116.lean:0 (declaration OMA.S_oeis_a095116.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea (Robert Israel's argument in the entry, plus the characterisation): with
-- pi = Nat.primeCounting we have b(i+1) + pi(b(i)) = n, so
-- b(i+2) - b(i+1) = pi(b(i)) - pi(b(i+1)). For x <= y, 0 <= pi(y) - pi(x) <= y - x, strictly
-- less when y - x >= 2 unless (x, y) = (1, 3), and (1, 3) occurs only for n = 3. So for n /= 3
-- the distance |b(i+1) - b(i)| decreases until it is at most 1, and then b is constant or
-- alternates between y and y + 1. An alternation needs pi(y + 1) = pi(y) + 1, so y + 1 = p is
-- prime and n = p + pi(p) - 1 = prime(m) + m - 1 with m = pi(p). Conversely for
-- n = prime(m) + m - 1 the equation x + pi(x) = n has no solution, so b is never constant;
-- for n = 3, b alternates 3, 1, 3, 1, ...

open OMA.S_oeis_a095116 in
theorem OMA.solution : type_of% @OMA.S_oeis_a095116.main := by
  have H0 : ∀ x y : ℕ, y = x + 1 →
      Nat.primeCounting y = Nat.primeCounting x + if y.Prime then 1 else 0 := by
    intro x y hy
    subst hy
    exact Nat.count_succ _ _
  have Hi : ∀ x : ℕ, Nat.primeCounting (x + 1) ≤ Nat.primeCounting x + 1 := by
    intro x
    have e := H0 x (x + 1) rfl
    by_cases h : (x + 1).Prime
    · rw [if_pos h] at e
      omega
    · rw [if_neg h] at e
      omega
  have H1 : ∀ x d : ℕ, Nat.primeCounting (x + d) ≤ Nat.primeCounting x + d := by
    intro x d
    induction d with
    | zero => simp
    | succ d ih =>
      have h := Hi (x + d)
      rw [show x + (d + 1) = x + d + 1 by omega]
      omega
  have H1' : ∀ x y : ℕ, x ≤ y → Nat.primeCounting y ≤ Nat.primeCounting x + (y - x) := by
    intro x y hxy
    have h := H1 x (y - x)
    rw [Nat.add_sub_of_le hxy] at h
    exact h
  have Hmono : ∀ x y : ℕ, x ≤ y → Nat.primeCounting x ≤ Nat.primeCounting y :=
    fun x y hxy => Nat.monotone_primeCounting hxy
  have Ple : ∀ x : ℕ, Nat.primeCounting x ≤ x := by
    intro x
    have h := H1 0 x
    rw [Nat.primeCounting_zero, Nat.zero_add] at h
    omega
  have hP1 : Nat.primeCounting 1 = 0 := Nat.primeCounting_one
  have hP2 : Nat.primeCounting 2 = 1 := by
    have e := H0 1 2 rfl
    rw [if_pos Nat.prime_two, hP1] at e
    omega
  have hP3 : Nat.primeCounting 3 = 2 := by
    have e := H0 2 3 rfl
    rw [if_pos Nat.prime_three, hP2] at e
    omega
  have H2 : ∀ x : ℕ, x ≠ 1 → Nat.primeCounting (x + 2) ≤ Nat.primeCounting x + 1 := by
    intro x hx
    have e1 := H0 x (x + 1) rfl
    have e2 := H0 (x + 1) (x + 2) rfl
    by_cases h1 : (x + 1).Prime
    · by_cases h2 : (x + 2).Prime
      · exfalso
        have t := h1.two_le
        rcases h1.eq_two_or_odd with h | h <;> rcases h2.eq_two_or_odd with h' | h' <;> omega
      · rw [if_pos h1] at e1
        rw [if_neg h2] at e2
        omega
    · rw [if_neg h1] at e1
      by_cases h2 : (x + 2).Prime
      · rw [if_pos h2] at e2
        omega
      · rw [if_neg h2] at e2
        omega
  have Hs : ∀ x y : ℕ, x + 2 ≤ y → ¬ (x = 1 ∧ y = 3) →
      Nat.primeCounting y + 1 ≤ Nat.primeCounting x + (y - x) := by
    intro x y hxy hne
    by_cases hx : x = 1
    · subst hx
      have hy : 4 ≤ y := by omega
      have h4 : Nat.primeCounting 4 ≤ Nat.primeCounting 2 + 1 := H2 2 (by norm_num)
      have h5 := H1' 4 y hy
      omega
    · have h3 := H2 x hx
      have h5 := H1' (x + 2) y hxy
      omega
  have step : ∀ n u v w : ℕ, v + Nat.primeCounting u = n → w + Nat.primeCounting v = n →
      (w - v + (v - w) ≤ v - u + (u - v)) ∧
      (n ≠ 3 → 2 ≤ v - u + (u - v) → w - v + (v - w) < v - u + (u - v)) ∧
      (v = u + 1 → w = v ∨ w = u) ∧ (u = v + 1 → w = v ∨ w = u) ∧ (v = u → w = v) := by
    intro n u v w h1 h2
    rcases le_total u v with huv | hvu
    · have m1 := Hmono u v huv
      have m2 := H1' u v huv
      refine ⟨by omega, ?_, by omega, by omega, by omega⟩
      intro hn3 hd
      have hne : ¬ (u = 1 ∧ v = 3) := by
        rintro ⟨rfl, rfl⟩
        rw [hP1] at h1
        omega
      have m3 := Hs u v (by omega) hne
      omega
    · have m1 := Hmono v u hvu
      have m2 := H1' v u hvu
      refine ⟨by omega, ?_, by omega, by omega, by omega⟩
      intro hn3 hd
      have hne : ¬ (v = 1 ∧ u = 3) := by
        rintro ⟨rfl, rfl⟩
        rw [hP3] at h1
        omega
      have m3 := Hs v u (by omega) hne
      omega
  have hcount : ∀ y : ℕ, Nat.count Nat.Prime (y + 1) = Nat.primeCounting y := fun _ => rfl
  intro n _
  have hb0 : b n 0 = n := rfl
  have hbs : ∀ i : ℕ, b n (i + 1) = n - Nat.primeCounting (b n i) := fun _ => rfl
  have hble : ∀ i : ℕ, b n i ≤ n := by
    intro i
    cases i with
    | zero => exact le_of_eq hb0
    | succ i =>
      rw [hbs]
      exact Nat.sub_le _ _
  have E : ∀ i : ℕ, b n (i + 1) + Nat.primeCounting (b n i) = n := by
    intro i
    have h1 := hbs i
    have h2 := Ple (b n i)
    have h3 := hble i
    omega
  have S := fun i : ℕ => step n _ _ _ (E i) (E (i + 1))
  obtain ⟨D, hD⟩ : ∃ D : ℕ → ℕ, ∀ i : ℕ, D i = b n (i + 1) - b n i + (b n i - b n (i + 1)) :=
    ⟨_, fun _ => rfl⟩
  have T1 : n ≠ 3 → ∃ j : ℕ, D j ≤ 1 := by
    intro hn3
    have key : ∀ d i : ℕ, D i = d → ∃ j : ℕ, D j ≤ 1 := by
      intro d
      induction d using Nat.strong_induction_on with
      | _ d ih =>
        intro i hi
        by_cases hd : d ≤ 1
        · exact ⟨i, by omega⟩
        · have h := (S i).2.1 hn3
          rw [← hD i, ← hD (i + 1)] at h
          have hlt : D (i + 1) < d := by
            have h' := h (by omega)
            omega
          exact ih (D (i + 1)) hlt (i + 1) rfl
    exact key (D 0) 0 rfl
  have T2 : ∀ j : ℕ, D j ≤ 1 → ∀ i : ℕ, j ≤ i → D i ≤ 1 := by
    intro j hj i hi
    induction i, hi using Nat.le_induction with
    | base => exact hj
    | succ i _ ih =>
      have h := (S i).1
      rw [← hD i, ← hD (i + 1)] at h
      omega
  have T3 : ∀ j : ℕ, b n (j + 1) = b n j → ∀ i : ℕ, j ≤ i → b n (i + 1) = b n i := by
    intro j hj i hi
    induction i, hi using Nat.le_induction with
    | base => exact hj
    | succ i _ ih => exact (S i).2.2.2.2 ih
  have T4 : ∀ i : ℕ, D i ≤ 1 → b n (i + 1) ≠ b n i → b n (i + 1 + 1) ≠ b n (i + 1) →
      b n (i + 1 + 1) = b n i := by
    intro i hDi hne hne'
    rw [hD i] at hDi
    have h3 := (S i).2.2.1
    have h4 := (S i).2.2.2.1
    rcases (by omega : b n (i + 1) = b n i + 1 ∨ b n i = b n (i + 1) + 1) with h | h
    · rcases h3 h with h' | h'
      · exact absurd h' hne'
      · exact h'
    · rcases h4 h with h' | h'
      · exact absurd h' hne'
      · exact h'
  have orbit3 : n = 3 → ∀ i : ℕ,
      (b n i = 3 ∧ b n (i + 1) = 1) ∨ (b n i = 1 ∧ b n (i + 1) = 3) := by
    intro h3 i
    induction i with
    | zero =>
      have e := E 0
      have h0 : b n 0 = 3 := by rw [hb0, h3]
      rw [h0, hP3] at e
      left
      exact ⟨h0, by omega⟩
    | succ i ih =>
      have e := E (i + 1)
      rcases ih with ⟨_, h⟩ | ⟨_, h⟩
      · rw [h, hP1] at e
        right
        exact ⟨h, by omega⟩
      · rw [h, hP3] at e
        left
        exact ⟨h, by omega⟩
  have partA : ∃ N : ℕ, ∀ i : ℕ, N ≤ i → b n (i + 2) = b n i := by
    by_cases h3 : n = 3
    · refine ⟨0, fun i _ => ?_⟩
      show b n (i + 1 + 1) = b n i
      have e := E (i + 1)
      rcases orbit3 h3 i with ⟨h, h'⟩ | ⟨h, h'⟩
      · rw [h', hP1] at e
        omega
      · rw [h', hP3] at e
        omega
    · obtain ⟨j, hj⟩ := T1 h3
      by_cases hc : ∃ j' : ℕ, j ≤ j' ∧ b n (j' + 1) = b n j'
      · obtain ⟨j', _, hj'⟩ := hc
        refine ⟨j', fun i hi => ?_⟩
        show b n (i + 1 + 1) = b n i
        rw [T3 j' hj' (i + 1) (by omega), T3 j' hj' i hi]
      · have hc' : ∀ j' : ℕ, j ≤ j' → b n (j' + 1) ≠ b n j' :=
          fun j' hjj heq => hc ⟨j', hjj, heq⟩
        refine ⟨j, fun i hi => ?_⟩
        show b n (i + 1 + 1) = b n i
        exact T4 i (T2 j hj i hi) (hc' i hi) (hc' (i + 1) (by omega))
  refine ⟨partA, ?_⟩
  constructor
  · intro hnc
    by_cases h3 : n = 3
    · exact Or.inl h3
    · right
      obtain ⟨j, hj⟩ := T1 h3
      have hc : ∀ j' : ℕ, j ≤ j' → b n (j' + 1) ≠ b n j' := by
        intro j' _ heq
        exact hnc ⟨j', fun i hi => T3 j' heq i hi⟩
      have hDj := hj
      rw [hD j] at hDj
      have hne := hc j le_rfl
      have h2c := T4 j hj hne (hc (j + 1) (by omega))
      have e1 := E j
      have e2 := E (j + 1)
      obtain ⟨y, hy1, hy2⟩ : ∃ y : ℕ, y + 1 + Nat.primeCounting y = n ∧
          y + Nat.primeCounting (y + 1) = n := by
        rcases (by omega : b n (j + 1) = b n j + 1 ∨ b n j = b n (j + 1) + 1) with h | h
        · refine ⟨b n j, ?_, ?_⟩
          · rw [← h]
            exact e1
          · rw [← h, ← h2c]
            exact e2
        · refine ⟨b n (j + 1), ?_, ?_⟩
          · rw [← h, ← h2c]
            exact e2
          · rw [← h]
            exact e1
      have hpr : (y + 1).Prime := by
        by_contra hnp
        have e := H0 y (y + 1) rfl
        rw [if_neg hnp] at e
        omega
      have hn := Nat.nth_count hpr
      rw [hcount y] at hn
      refine ⟨Nat.primeCounting y + 1, by omega, ?_⟩
      show n = Nat.nth Nat.Prime (Nat.primeCounting y + 1 - 1) + (Nat.primeCounting y + 1) - 1
      rw [Nat.add_sub_cancel, hn]
      omega
  · rintro (h3 | ⟨m, hm, hma⟩) ⟨N, hN⟩
    · have h := hN N le_rfl
      rcases orbit3 h3 N with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    · have hfix := hN N le_rfl
      have e := E N
      rw [hfix] at e
      obtain ⟨q, rfl⟩ : ∃ q : ℕ, m = q + 1 := ⟨m - 1, by omega⟩
      have hma' : n = Nat.nth Nat.Prime q + q := by
        rw [hma]
        show Nat.nth Nat.Prime (q + 1 - 1) + (q + 1) - 1 = Nat.nth Nat.Prime q + q
        rw [Nat.add_sub_cancel]
        omega
      have hp := Nat.prime_nth_prime q
      have hp2 := hp.two_le
      have hc1 : Nat.primeCounting (Nat.nth Nat.Prime q - 1) = q := by
        rw [Nat.primeCounting_sub_one, Nat.primeCounting'_nth_eq]
      have hc2 : Nat.primeCounting (Nat.nth Nat.Prime q) = q + 1 := by
        have e2 := H0 (Nat.nth Nat.Prime q - 1) (Nat.nth Nat.Prime q) (by omega)
        rw [if_pos hp, hc1] at e2
        exact e2
      rcases le_or_gt (Nat.nth Nat.Prime q) (b n N) with hx | hx
      · have := Hmono _ _ hx
        omega
      · have := Hmono (b n N) (Nat.nth Nat.Prime q - 1) (by omega)
        omega
