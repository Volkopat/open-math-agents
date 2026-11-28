import OMAStatements.S_oeis_a321003

-- Problem: A321003: a(n) = 2^n*(4*3^n-1).
-- Upstream: formal-conjectures statements/oeis-a321003.lean:0 (declaration OMA.S_oeis_a321003.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea (Chai Wah Wu, comments of A175046): write A = A175046. From the binary digits,
-- for i >= 1: A(4i) = 2A(2i), A(4i+1) = 4A(2i) + 3, A(4i+2) = 4A(2i+1), A(4i+3) = 2A(2i+1) + 1.
-- Let f(k) be the sum of A(i) over 2^k <= i < 2^(k+1), and F(k) the sum of A(2l) + A(2l+1)
-- over 2^k <= l < 2^(k+1), so that f(k+1) = F(k). Grouping the terms of F(k+1) in fours gives
-- F(k+1) = 6F(k) + 4 * 2^k; with F(0) = A(2) + A(3) = 19 this yields
-- f(m+1) = 20*6^m - 2^m = 20*2^m*3^m - 2^m. The sum over 1 <= i < 2^(n+1) is then
-- 3 + f(1) + ... + f(n), and induction on n with f(n+1) gives 2^n*(4*3^n - 1).
open OMA.S_oeis_a321003 in
theorem OMA.solution : type_of% @OMA.S_oeis_a321003.main := by
  have d0 : ∀ m : ℕ, 0 < m → Nat.digits 2 (2 * m) = 0 :: Nat.digits 2 m := by
    intro m hm
    rw [Nat.digits_def' (by norm_num : 1 < 2) (by omega : 0 < 2 * m), Nat.mul_mod_right,
      Nat.mul_div_cancel_left m (by norm_num : 0 < 2)]
  have d1 : ∀ m : ℕ, Nat.digits 2 (2 * m + 1) = 1 :: Nat.digits 2 m := by
    intro m
    have h1 : (2 * m + 1) % 2 = 1 := by omega
    have h2 : (2 * m + 1) / 2 = m := by omega
    rw [Nat.digits_def' (by norm_num : 1 < 2) (by omega : 0 < 2 * m + 1), h1, h2]
  have e00 : ∀ L : List ℕ, expand (0 :: 0 :: L) = 0 :: expand (0 :: L) := by
    intro L
    simp [expand]
  have e10 : ∀ L : List ℕ, expand (1 :: 0 :: L) = 1 :: 1 :: expand (0 :: L) := by
    intro L
    simp [expand]
  have e01 : ∀ L : List ℕ, expand (0 :: 1 :: L) = 0 :: 0 :: expand (1 :: L) := by
    intro L
    simp [expand]
  have e11 : ∀ L : List ℕ, expand (1 :: 1 :: L) = 1 :: expand (1 :: L) := by
    intro L
    simp [expand]
  have r0 : ∀ i : ℕ, 0 < i → A175046 (2 * (2 * i)) = 2 * A175046 (2 * i) := by
    intro i hi
    unfold A175046
    rw [d0 (2 * i) (by omega), d0 i hi, e00, Nat.ofDigits_cons]
    simp
  have r1 : ∀ i : ℕ, 0 < i → A175046 (2 * (2 * i) + 1) = 4 * A175046 (2 * i) + 3 := by
    intro i hi
    unfold A175046
    rw [d1 (2 * i), d0 i hi, e10, Nat.ofDigits_cons, Nat.ofDigits_cons]
    ring
  have r2 : ∀ i : ℕ, A175046 (2 * (2 * i + 1)) = 4 * A175046 (2 * i + 1) := by
    intro i
    unfold A175046
    rw [d0 (2 * i + 1) (by omega), d1 i, e01, Nat.ofDigits_cons, Nat.ofDigits_cons]
    ring
  have r3 : ∀ i : ℕ, A175046 (2 * (2 * i + 1) + 1) = 2 * A175046 (2 * i + 1) + 1 := by
    intro i
    unfold A175046
    rw [d1 (2 * i + 1), d1 i, e11, Nat.ofDigits_cons]
    ring
  have hA1 : A175046 1 = 3 := by
    unfold A175046
    rw [Nat.digits_of_lt 2 1 one_ne_zero one_lt_two]
    decide
  have hA2 : A175046 (2 * 1) = 12 := by
    unfold A175046
    rw [d0 1 one_pos, Nat.digits_of_lt 2 1 one_ne_zero one_lt_two]
    decide
  have hA3 : A175046 (2 * 1 + 1) = 7 := by
    unfold A175046
    rw [d1 1, Nat.digits_of_lt 2 1 one_ne_zero one_lt_two]
    decide
  have pair : ∀ (g : ℕ → ℤ) (P Q : ℕ), P ≤ Q →
      ∑ j ∈ Finset.Ico (2 * P) (2 * Q), g j
        = ∑ i ∈ Finset.Ico P Q, (g (2 * i) + g (2 * i + 1)) := by
    intro g P Q hPQ
    induction Q, hPQ using Nat.le_induction with
    | base => simp
    | succ Q hQ ih =>
      rw [show 2 * (Q + 1) = 2 * Q + 1 + 1 by ring,
        Finset.sum_Ico_succ_top (by omega : 2 * P ≤ 2 * Q + 1),
        Finset.sum_Ico_succ_top (by omega : 2 * P ≤ 2 * Q), Finset.sum_Ico_succ_top hQ, ih]
      ring
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℤ, ∀ k : ℕ,
      f k = ∑ i ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), (A175046 i : ℤ) := ⟨_, fun _ => rfl⟩
  obtain ⟨F, hF_def⟩ : ∃ F : ℕ → ℤ, ∀ k : ℕ,
      F k = ∑ l ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
        ((A175046 (2 * l) : ℤ) + (A175046 (2 * l + 1) : ℤ)) := ⟨_, fun _ => rfl⟩
  have hF : ∀ k : ℕ, f (k + 1) = F k := by
    intro k
    have h1 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    have h2 : 2 ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := by ring
    have hp : ∑ j ∈ Finset.Ico (2 * 2 ^ k) (2 * 2 ^ (k + 1)), (A175046 j : ℤ)
        = ∑ l ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
          ((A175046 (2 * l) : ℤ) + (A175046 (2 * l + 1) : ℤ)) :=
      pair (fun j => (A175046 j : ℤ)) (2 ^ k) (2 ^ (k + 1))
        (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [← h1, ← h2] at hp
    rw [hf (k + 1), hF_def k]
    exact hp
  have h4 : ∀ k : ℕ, F (k + 1) = 6 * F k + 4 * 2 ^ k := by
    intro k
    have h1 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    have h2 : 2 ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := by ring
    have hp : ∑ j ∈ Finset.Ico (2 * 2 ^ k) (2 * 2 ^ (k + 1)),
          ((A175046 (2 * j) : ℤ) + (A175046 (2 * j + 1) : ℤ))
        = ∑ m ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
          (((A175046 (2 * (2 * m)) : ℤ) + (A175046 (2 * (2 * m) + 1) : ℤ))
            + ((A175046 (2 * (2 * m + 1)) : ℤ) + (A175046 (2 * (2 * m + 1) + 1) : ℤ))) :=
      pair (fun j => (A175046 (2 * j) : ℤ) + (A175046 (2 * j + 1) : ℤ)) (2 ^ k) (2 ^ (k + 1))
        (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [← h1, ← h2] at hp
    have hs : ∀ m ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
        (((A175046 (2 * (2 * m)) : ℤ) + (A175046 (2 * (2 * m) + 1) : ℤ))
            + ((A175046 (2 * (2 * m + 1)) : ℤ) + (A175046 (2 * (2 * m + 1) + 1) : ℤ)))
          = 6 * ((A175046 (2 * m) : ℤ) + (A175046 (2 * m + 1) : ℤ)) + 4 := by
      intro m hm
      have hm1 : 0 < m := by
        have hle := (Finset.mem_Ico.mp hm).1
        have hpos : 0 < 2 ^ k := by positivity
        omega
      rw [r0 m hm1, r1 m hm1, r2 m, r3 m]
      push_cast
      ring
    rw [hF_def (k + 1), hp, Finset.sum_congr rfl hs, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, Nat.card_Ico, hF_def k]
    have hc : 2 ^ (k + 1) - 2 ^ k = 2 ^ k := by
      rw [h1]
      omega
    rw [hc, nsmul_eq_mul]
    push_cast
    ring
  have hclosed : ∀ m : ℕ, f (m + 1) = 20 * (2 ^ m * 3 ^ m) - 2 ^ m := by
    intro m
    induction m with
    | zero =>
      have hA2' : (A175046 (2 * 1) : ℤ) = 12 := by exact_mod_cast hA2
      have hA3' : (A175046 (2 * 1 + 1) : ℤ) = 7 := by exact_mod_cast hA3
      rw [hF 0, hF_def 0, show (2 : ℕ) ^ 0 = 1 by norm_num,
        show (2 : ℕ) ^ (0 + 1) = 1 + 1 by norm_num, Finset.sum_Ico_succ_top (le_refl 1),
        Finset.Ico_self, Finset.sum_empty, hA2', hA3']
      norm_num
    | succ m ih =>
      rw [hF (m + 1), h4 m, ← hF m, ih]
      ring
  intro n
  induction n with
  | zero =>
    have hA1' : (A175046 1 : ℤ) = 3 := by exact_mod_cast hA1
    rw [show (2 : ℕ) ^ (0 + 1) = 1 + 1 by norm_num, Finset.sum_Ico_succ_top (le_refl 1),
      Finset.Ico_self, Finset.sum_empty, hA1']
    norm_num [a]
  | succ n ih =>
    rw [← Finset.sum_Ico_consecutive _ (Nat.one_le_two_pow : 1 ≤ 2 ^ (n + 1))
        (Nat.pow_le_pow_right (by norm_num) (by omega) : 2 ^ (n + 1) ≤ 2 ^ (n + 1 + 1)),
      ← ih, ← hf (n + 1), hclosed n]
    simp only [a]
    ring
