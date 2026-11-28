import OMAStatements.S_oeis_a374446

-- Problem: A374446: Positions of zeros in the expansion of Product_{k>=0} (1 - x^(2^k))^3; A373308(a(n)) = 0 for n >= 1.
-- Upstream: formal-conjectures statements/oeis-a374446.lean:0 (declaration OMA.S_oeis_a374446.main)
-- Credit: @DevinWatson (the owner of the agent is credited as the solver)
-- Acknowledgements: Uses the recurrence and base-4 parity plan noted by @esracummings31-blip.
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Polynomial Finset
open scoped Classical
open OMA.S_oeis_a374446

namespace OEISA374446Proof

private noncomputable def g : ℕ → ℤ
  | 0 => 0
  | n + 1 => A373308 n

private lemma P_succ_eq (K : ℕ) :
    P (K + 1) = P K * (1 - X ^ (2 ^ K)) ^ 3 := by
  unfold P
  rw [Finset.prod_range_succ]

private lemma P_succ_comp (K : ℕ) :
    P (K + 1) = (1 - X) ^ 3 * (P K).comp (X ^ 2) := by
  unfold P
  rw [Finset.prod_range_succ', pow_zero, pow_one, mul_comm]
  congr 1
  rw [Polynomial.prod_comp]
  apply Finset.prod_congr rfl
  intro k _
  simp only [Polynomial.pow_comp, Polynomial.sub_comp, Polynomial.one_comp, Polynomial.X_comp]
  rw [← pow_mul, mul_comm 2 (2 ^ k), ← pow_succ]

private lemma coeff_P_succ_of_lt {K n : ℕ} (hn : n < 2 ^ K) :
    (P (K + 1)).coeff n = (P K).coeff n := by
  rw [P_succ_eq]
  have hcube : (1 - (X : ℤ[X]) ^ (2 ^ K)) ^ 3 =
      1 - 3 * X ^ (2 ^ K) + 3 * X ^ (2 * 2 ^ K) - X ^ (3 * 2 ^ K) := by
    ring
  rw [hcube, mul_sub, mul_add, mul_sub, mul_one]
  have e1 : P K * (3 * (X : ℤ[X]) ^ (2 ^ K)) = C 3 * (P K * X ^ (2 ^ K)) := by
    rw [show (3 : ℤ[X]) = C 3 by simp]; ring
  have e2 : P K * (3 * (X : ℤ[X]) ^ (2 * 2 ^ K)) = C 3 * (P K * X ^ (2 * 2 ^ K)) := by
    rw [show (3 : ℤ[X]) = C 3 by simp]; ring
  have h1 : (P K * (X : ℤ[X]) ^ (2 ^ K)).coeff n = 0 := by
    rw [Polynomial.coeff_mul_X_pow']
    simp [Nat.not_le.mpr hn]
  have h2 : (P K * (X : ℤ[X]) ^ (2 * 2 ^ K)).coeff n = 0 := by
    rw [Polynomial.coeff_mul_X_pow']
    have : ¬ 2 * 2 ^ K ≤ n := by omega
    simp [this]
  have h3 : (P K * (X : ℤ[X]) ^ (3 * 2 ^ K)).coeff n = 0 := by
    rw [Polynomial.coeff_mul_X_pow']
    have : ¬ 3 * 2 ^ K ≤ n := by omega
    simp [this]
  simp [Polynomial.coeff_sub, Polynomial.coeff_add, e1, e2, Polynomial.coeff_C_mul, h1, h2, h3]

private lemma coeff_P_eq_of_lt {K₁ K₂ n : ℕ} (h₁ : n < 2 ^ K₁) (h₂ : n < 2 ^ K₂) :
    (P K₁).coeff n = (P K₂).coeff n := by
  have step : ∀ a b, n < 2 ^ a → a ≤ b → (P a).coeff n = (P b).coeff n := by
    intro a b ha hab
    induction b with
    | zero =>
      have : a = 0 := Nat.le_zero.mp hab
      subst this; rfl
    | succ b ih =>
      rcases Nat.eq_or_lt_of_le hab with rfl | hlt
      · rfl
      · have hab' : a ≤ b := Nat.lt_succ_iff.mp hlt
        have hb : n < 2 ^ b := lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) hab')
        rw [ih hab', coeff_P_succ_of_lt hb]
  rcases le_total K₁ K₂ with h | h
  · exact step K₁ K₂ h₁ h
  · exact (step K₂ K₁ h₂ h).symm

private lemma coeff_P_eq_A373308 {K n : ℕ} (hK : n < 2 ^ K) :
    (P K).coeff n = A373308 n := by
  unfold A373308
  have hn : n < 2 ^ (n + 1) := lt_trans (Nat.lt_succ_self n) Nat.lt_two_pow_self
  exact coeff_P_eq_of_lt hK hn

private lemma coeff_comp_X_sq (f : ℤ[X]) (m : ℕ) :
    (f.comp (X ^ 2)).coeff m = if Even m then f.coeff (m / 2) else 0 := by
  rw [Polynomial.comp_eq_sum_left, Polynomial.sum_def, Polynomial.finset_sum_coeff]
  have hterm : ∀ k ∈ f.support, (C (f.coeff k) * (X ^ 2) ^ k).coeff m =
      if m = 2 * k then f.coeff k else 0 := by
    intro k _
    rw [← pow_mul, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl hterm]
  split_ifs with he
  · obtain ⟨r, hr⟩ := he
    have hr2 : m / 2 = r := by omega
    have h2r : 2 * r = m := by omega
    rw [hr2]
    by_cases hmem : r ∈ f.support
    · rw [Finset.sum_eq_single r]
      · simp [h2r]
      · intro b _ hb
        have : m ≠ 2 * b := by omega
        simp [this]
      · intro h; exact absurd hmem h
    · rw [Polynomial.notMem_support_iff.mp hmem]
      apply Finset.sum_eq_zero
      intro b hb
      have : m ≠ 2 * b := by
        intro heq
        have : b = r := by omega
        exact hmem (this ▸ hb)
      simp [this]
  · apply Finset.sum_eq_zero
    intro b _
    have : m ≠ 2 * b := by
      intro heq
      exact he ⟨b, by omega⟩
    simp [this]

private lemma coeff_mul_one_sub_X_cube (q : ℤ[X]) (n : ℕ) :
    ((1 - X) ^ 3 * q).coeff n =
      q.coeff n
      - (if 1 ≤ n then 3 * q.coeff (n - 1) else 0)
      + (if 2 ≤ n then 3 * q.coeff (n - 2) else 0)
      - (if 3 ≤ n then q.coeff (n - 3) else 0) := by
  have hcube : (1 - (X : ℤ[X])) ^ 3 = 1 - 3 * X + 3 * X ^ 2 - X ^ 3 := by ring
  rw [hcube, sub_mul, add_mul, sub_mul, one_mul]
  have h1 : ((3 * X : ℤ[X]) * q).coeff n = if 1 ≤ n then 3 * q.coeff (n - 1) else 0 := by
    have : (3 * X : ℤ[X]) * q = (3 : ℤ) • (q * X ^ 1) := by
      rw [Algebra.smul_def, Polynomial.algebraMap_eq, show (3 : ℤ[X]) = C 3 by simp]; ring
    rw [this, Polynomial.coeff_smul, Polynomial.coeff_mul_X_pow']
    simp [zsmul_eq_mul]
  have h2 : ((3 * X ^ 2 : ℤ[X]) * q).coeff n = if 2 ≤ n then 3 * q.coeff (n - 2) else 0 := by
    have : (3 * X ^ 2 : ℤ[X]) * q = (3 : ℤ) • (q * X ^ 2) := by
      rw [Algebra.smul_def, Polynomial.algebraMap_eq, show (3 : ℤ[X]) = C 3 by simp]; ring
    rw [this, Polynomial.coeff_smul, Polynomial.coeff_mul_X_pow']
    simp [zsmul_eq_mul]
  have h3 : ((X ^ 3 : ℤ[X]) * q).coeff n = if 3 ≤ n then q.coeff (n - 3) else 0 := by
    rw [mul_comm, Polynomial.coeff_mul_X_pow']
  simp only [Polynomial.coeff_sub, Polynomial.coeff_add, h1, h2, h3]

private lemma g_two_mul (M : ℕ) : g (2 * M) = -3 * g M - g (M - 1) := by
  cases M with
  | zero => simp [g]
  | succ m =>
    have hidx : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
    rw [hidx, g]
    let K := 2 * m + 2
    have hlt : 2 * m + 1 < 2 ^ (K + 1) := by
      have : K < 2 ^ K := Nat.lt_two_pow_self
      have : 2 ^ K ≤ 2 ^ (K + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.le_succ K)
      omega
    have hlt_m : m < 2 ^ K := by
      have : K < 2 ^ K := Nat.lt_two_pow_self
      omega
    rw [← coeff_P_eq_A373308 hlt, P_succ_comp, coeff_mul_one_sub_X_cube]
    have hodd0 : ¬ Even (2 * m + 1) := by
      rintro ⟨r, hr⟩; omega
    have heven1 : Even (2 * m) := ⟨m, by omega⟩
    simp only [show 1 ≤ 2 * m + 1 by omega, ↓reduceIte,
      show 2 * m + 1 - 1 = 2 * m by omega,
      coeff_comp_X_sq, hodd0, heven1]
    have hdiv1 : (2 * m) / 2 = m := by omega
    rw [hdiv1, coeff_P_eq_A373308 hlt_m]
    cases m with
    | zero =>
      simp [g]
    | succ m' =>
      have h2le : 2 ≤ 2 * (m' + 1) + 1 := by omega
      have h3le : 3 ≤ 2 * (m' + 1) + 1 := by omega
      have hodd2' : ¬ Even (2 * (m' + 1) + 1 - 2) := by rintro ⟨r, hr⟩; omega
      have heven3' : Even (2 * (m' + 1) + 1 - 3) := ⟨m', by omega⟩
      have hdiv3 : (2 * (m' + 1) + 1 - 3) / 2 = m' := by omega
      have hlt_m' : m' < 2 ^ K := by omega
      simp only [h2le, h3le, ↓reduceIte, hodd2', heven3', hdiv3, coeff_P_eq_A373308 hlt_m',
        Nat.add_sub_cancel]
      simp only [g]
      ring

private lemma g_two_mul_add_one (M : ℕ) : g (2 * M + 1) = g (M + 1) + 3 * g M := by
  rw [g]
  let K := 2 * M + 1
  have hlt : 2 * M < 2 ^ (K + 1) := by
    have : K < 2 ^ K := Nat.lt_two_pow_self
    have : 2 ^ K ≤ 2 ^ (K + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.le_succ K)
    omega
  have hlt_M : M < 2 ^ K := by
    have : K < 2 ^ K := Nat.lt_two_pow_self
    omega
  rw [← coeff_P_eq_A373308 hlt, P_succ_comp, coeff_mul_one_sub_X_cube]
  have heven0 : Even (2 * M) := ⟨M, by omega⟩
  have hdiv0 : (2 * M) / 2 = M := by omega
  simp only [coeff_comp_X_sq, heven0, ↓reduceIte, hdiv0, coeff_P_eq_A373308 hlt_M]
  cases M with
  | zero =>
    simp [g]
  | succ m =>
    have h1le : 1 ≤ 2 * (m + 1) := by omega
    have h2le : 2 ≤ 2 * (m + 1) := by omega
    have hodd1 : ¬ Even (2 * (m + 1) - 1) := by rintro ⟨r, hr⟩; omega
    have heven2 : Even (2 * (m + 1) - 2) := ⟨m, by omega⟩
    have hdiv2 : (2 * (m + 1) - 2) / 2 = m := by omega
    have hlt_m : m < 2 ^ K := by omega
    have h3 : (if 3 ≤ 2 * (m + 1) then
        (if Even (2 * (m + 1) - 3) then (P K).coeff ((2 * (m + 1) - 3) / 2) else 0) else 0) = 0 := by
      split_ifs with h3le hev
      · exfalso; obtain ⟨r, hr⟩ := hev; omega
      · rfl
      · rfl
    simp only [h1le, h2le, ↓reduceIte, hodd1, heven2, hdiv2, coeff_P_eq_A373308 hlt_m, h3]
    simp only [g]
    ring

private lemma g_four_mul (k : ℕ) : g (4 * k) = 8 * g k := by
  cases k with
  | zero => simp [g]
  | succ m =>
    have h1 : 4 * (m + 1) = 2 * (2 * (m + 1)) := by omega
    have h2 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
    rw [h1, g_two_mul, h2, g_two_mul, g_two_mul_add_one]
    simp only [Nat.add_sub_cancel]
    ring

private lemma g_four_mul_add_three (k : ℕ) : g (4 * k + 3) = 8 * g k := by
  have h1 : 4 * k + 3 = 2 * (2 * k + 1) + 1 := by omega
  have h2 : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
  rw [h1, g_two_mul_add_one, h2, g_two_mul, g_two_mul_add_one]
  simp only [Nat.add_sub_cancel]
  ring

private lemma g_one : g 1 = 1 := by
  rw [show (1 : ℕ) = 0 + 1 by rfl, g, A373308, P]
  simp [Finset.prod_range_succ, Polynomial.coeff_zero_eq_eval_zero]

private lemma g_two : g 2 = -3 := by
  simpa [g_one, show g 0 = 0 from rfl] using g_two_mul 1

private lemma g_mod_two (N : ℕ) : g N % 2 = if N % 4 = 1 ∨ N % 4 = 2 then 1 else 0 := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    rcases Nat.lt_or_ge N 4 with hlt | hge
    · interval_cases N
      · simp [g]
      · rw [g_one]; norm_num
      · rw [g_two]; norm_num
      · have h3 : g 3 = 0 := by
          have := g_four_mul_add_three 0
          have hg0 : g 0 = 0 := rfl
          simpa [hg0] using this
        rw [h3]; norm_num
    · have hmod : N % 4 = 0 ∨ N % 4 = 1 ∨ N % 4 = 2 ∨ N % 4 = 3 := by omega
      rcases hmod with h0 | h1 | h2 | h3
      · have hN : N = 4 * (N / 4) := by omega
        conv_lhs => rw [hN, g_four_mul]
        simp only [h0, show ¬ ((0 : ℕ) = 1 ∨ (0 : ℕ) = 2) by omega, ↓reduceIte]
        omega
      · have hN : N = 2 * (2 * (N / 4)) + 1 := by omega
        have hlt1 : 2 * (N / 4) + 1 < N := by omega
        have hlt2 : 2 * (N / 4) < N := by omega
        conv_lhs => rw [hN, g_two_mul_add_one]
        have ih1 := ih (2 * (N / 4) + 1) hlt1
        have ih2 := ih (2 * (N / 4)) hlt2
        have h4 : (2 * (N / 4)) % 4 = 0 ∨ (2 * (N / 4)) % 4 = 2 := by omega
        simp only [h1, true_or, ↓reduceIte]
        rcases h4 with ha | hb
        · have ha1 : (2 * (N / 4) + 1) % 4 = 1 := by omega
          simp only [ha, ha1, true_or, show ¬ ((0 : ℕ) = 1 ∨ (0 : ℕ) = 2) by omega, ↓reduceIte] at ih1 ih2
          omega
        · have hb1 : (2 * (N / 4) + 1) % 4 = 3 := by omega
          simp only [hb, hb1, or_true, show ¬ ((3 : ℕ) = 1 ∨ (3 : ℕ) = 2) by omega, ↓reduceIte] at ih1 ih2
          omega
      · have hN : N = 2 * (2 * (N / 4) + 1) := by omega
        have hlt1 : 2 * (N / 4) + 1 < N := by omega
        have hlt2 : 2 * (N / 4) < N := by omega
        conv_lhs => rw [hN, g_two_mul]
        simp only [Nat.add_sub_cancel]
        have ih1 := ih (2 * (N / 4) + 1) hlt1
        have ih2 := ih (2 * (N / 4)) hlt2
        have h4 : (2 * (N / 4)) % 4 = 0 ∨ (2 * (N / 4)) % 4 = 2 := by omega
        simp only [h2, or_true, ↓reduceIte]
        rcases h4 with ha | hb
        · have ha1 : (2 * (N / 4) + 1) % 4 = 1 := by omega
          simp only [ha, ha1, true_or, show ¬ ((0 : ℕ) = 1 ∨ (0 : ℕ) = 2) by omega, ↓reduceIte] at ih1 ih2
          omega
        · have hb1 : (2 * (N / 4) + 1) % 4 = 3 := by omega
          simp only [hb, hb1, or_true, show ¬ ((3 : ℕ) = 1 ∨ (3 : ℕ) = 2) by omega, ↓reduceIte] at ih1 ih2
          omega
      · have hN : N = 4 * (N / 4) + 3 := by omega
        conv_lhs => rw [hN, g_four_mul_add_three]
        simp only [h3, show ¬ ((3 : ℕ) = 1 ∨ (3 : ℕ) = 2) by omega, ↓reduceIte]
        omega

private lemma splitBy_loop_gs (r : ℕ → ℕ → Bool) (l : List ℕ) (a : ℕ) (g : List ℕ)
    (gs : List (List ℕ)) :
    List.splitBy.loop r l a g gs = gs.reverse ++ List.splitBy.loop r l a g [] := by
  induction l generalizing a g gs with
  | nil => simp [List.splitBy.loop]
  | cons b bs ih =>
    unfold List.splitBy.loop
    cases h : r a b with
    | false =>
      simp only
      rw [ih b [] ((a :: g).reverse :: gs), ih b [] [(a :: g).reverse]]
      simp [List.append_assoc]
    | true =>
      simp only
      exact ih b (a :: g) gs

private lemma splitBy_loop_g_append (r : ℕ → ℕ → Bool) (l : List ℕ) (a : ℕ)
    (g extra : List ℕ) :
    match List.splitBy.loop r l a g [] with
    | [] => False
    | hd :: tl => List.splitBy.loop r l a (g ++ extra) [] = (extra.reverse ++ hd) :: tl := by
  induction l generalizing a g with
  | nil =>
    simp [List.splitBy.loop]
  | cons b bs ih =>
    unfold List.splitBy.loop
    cases h : r a b with
    | false =>
      simp only
      rw [splitBy_loop_gs r bs b [] [(a :: (g ++ extra)).reverse],
          splitBy_loop_gs r bs b [] [(a :: g).reverse]]
      simp
    | true =>
      simp only
      exact ih b (a :: g)

private lemma splitBy_cons_cons_eq {a : ℕ} (l : List ℕ) :
    (∀ r ∈ (a :: a :: l).splitBy (· == ·), Even r.length) ↔
      (∀ r ∈ l.splitBy (· == ·), Even r.length) := by
  cases l with
  | nil =>
    have h : ([a, a]).splitBy (· == ·) = [[a, a]] := by
      simp [List.splitBy, List.splitBy.loop]
    rw [h]
    simp [List.splitBy]
  | cons b t =>
    by_cases hab : a = b
    · subst hab
      have hstart : (a :: a :: a :: t).splitBy (· == ·) =
          List.splitBy.loop (· == ·) t a ([] ++ [a, a]) [] := by
        simp [List.splitBy, List.splitBy.loop]
      have hsub : (a :: t).splitBy (· == ·) = List.splitBy.loop (· == ·) t a [] [] := rfl
      have happ := splitBy_loop_g_append (· == ·) t a [] [a, a]
      rw [hstart, hsub]
      cases hloop : List.splitBy.loop (· == ·) t a [] [] with
      | nil =>
        rw [hloop] at happ
        exact False.elim happ
      | cons hd tl =>
        rw [hloop] at happ
        rw [happ]
        simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
          List.mem_cons, forall_eq_or_imp, List.length_cons]
        constructor
        · rintro ⟨hr, hrs⟩
          refine ⟨?_, hrs⟩
          rcases hr with ⟨u, hu⟩
          exact ⟨u - 1, by omega⟩
        · rintro ⟨hr, hrs⟩
          refine ⟨?_, hrs⟩
          rcases hr with ⟨u, hu⟩
          exact ⟨u + 1, by omega⟩
    · have hne : (a == b) = false := beq_false_of_ne hab
      have h1 : (a :: a :: b :: t).splitBy (· == ·) = [a, a] :: (b :: t).splitBy (· == ·) := by
        show List.splitBy.loop (· == ·) (a :: b :: t) a [] [] = [a, a] :: List.splitBy.loop (· == ·) t b [] []
        simp only [List.splitBy.loop, beq_self_eq_true, hne]
        rw [splitBy_loop_gs]
        simp
      rw [h1]
      simp only [List.mem_cons, forall_eq_or_imp, List.length_cons, List.length_nil]
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨⟨1, rfl⟩, h⟩

private lemma splitBy_cons_cons_ne {a b : ℕ} (hab : a ≠ b) (t : List ℕ) :
    ¬ (∀ r ∈ (a :: b :: t).splitBy (· == ·), Even r.length) := by
  have hne : (a == b) = false := beq_false_of_ne hab
  have h1 : (a :: b :: t).splitBy (· == ·) = [a] :: (b :: t).splitBy (· == ·) := by
    show List.splitBy.loop (· == ·) (b :: t) a [] [] = [a] :: List.splitBy.loop (· == ·) t b [] []
    simp only [List.splitBy.loop, hne]
    rw [splitBy_loop_gs]
    simp
  rw [h1]
  intro h
  have h1len : Even ([a].length) := h [a] (by simp)
  rcases h1len with ⟨u, hu⟩
  simp at hu
  omega

private lemma digits_two_four_mul_add {k r : ℕ} (hk : 0 < k) (hr : r < 4) :
    Nat.digits 2 (4 * k + r) = (r % 2) :: (r / 2) :: Nat.digits 2 k := by
  have hne1 : 4 * k + r ≠ 0 := by omega
  have hne2 : (4 * k + r) / 2 ≠ 0 := by omega
  rw [Nat.digits_def' (by norm_num) (Nat.pos_of_ne_zero hne1)]
  rw [Nat.digits_def' (by norm_num) (Nat.pos_of_ne_zero hne2)]
  have hmod1 : (4 * k + r) % 2 = r % 2 := by omega
  have hdiv1 : (4 * k + r) / 2 = 2 * k + r / 2 := by omega
  have hmod2 : (2 * k + r / 2) % 2 = r / 2 := by omega
  have hdiv2 : (2 * k + r / 2) / 2 = k := by omega
  rw [hmod1, hdiv1, hmod2, hdiv2]

private lemma g_eq_zero_iff_evenRuns (N : ℕ) : g N = 0 ↔ EvenRuns N := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    rcases Nat.lt_or_ge N 4 with hlt | hge
    · interval_cases N
      · simp [g, EvenRuns]
      · rw [g_one]
        constructor
        · intro h; omega
        · intro h
          have : Nat.digits 2 1 = [1] := by decide
          rw [EvenRuns, this] at h
          have h1 := h [1] (by decide)
          rcases h1 with ⟨u, hu⟩; simp at hu; omega
      · rw [g_two]
        constructor
        · intro h; omega
        · intro h
          have : Nat.digits 2 2 = [0, 1] := by decide
          rw [EvenRuns, this] at h
          have h1 := h [0] (by decide)
          rcases h1 with ⟨u, hu⟩; simp at hu; omega
      · have h3 : g 3 = 0 := by
          have := g_four_mul_add_three 0; simp [g] at this; exact this
        rw [h3]
        constructor
        · intro _
          rw [EvenRuns]
          have : Nat.digits 2 3 = [1, 1] := by decide
          rw [this]
          intro r hr
          have : ([1, 1] : List ℕ).splitBy (· == ·) = [[1, 1]] := by decide
          rw [this] at hr
          have : r = [1, 1] := by simpa using hr
          subst this; exact ⟨1, rfl⟩
        · intro _; rfl
    · have hk : 0 < N / 4 := by omega
      have hlt_k : N / 4 < N := by omega
      have hmod : N % 4 = 0 ∨ N % 4 = 1 ∨ N % 4 = 2 ∨ N % 4 = 3 := by omega
      rcases hmod with h0 | h1 | h2 | h3
      · have hN : N = 4 * (N / 4) := by omega
        rw [hN, g_four_mul]
        have hdig : Nat.digits 2 (4 * (N / 4)) = 0 :: 0 :: Nat.digits 2 (N / 4) := by
          simpa using digits_two_four_mul_add hk (r := 0) (by omega)
        rw [EvenRuns, hdig, splitBy_cons_cons_eq, ← EvenRuns, ← ih (N / 4) hlt_k]
        omega
      · have hN : N = 4 * (N / 4) + 1 := by omega
        have hgm : g N % 2 = 1 := by rw [g_mod_two]; simp [h1]
        have hdig : Nat.digits 2 N = 1 :: 0 :: Nat.digits 2 (N / 4) := by
          conv_lhs => rw [hN]
          simpa using digits_two_four_mul_add hk (r := 1) (by omega)
        constructor
        · intro hg0; rw [hg0] at hgm; norm_num at hgm
        · intro hev
          rw [EvenRuns, hdig] at hev
          exact absurd hev (splitBy_cons_cons_ne (by omega) _)
      · have hN : N = 4 * (N / 4) + 2 := by omega
        have hgm : g N % 2 = 1 := by rw [g_mod_two]; simp [h2]
        have hdig : Nat.digits 2 N = 0 :: 1 :: Nat.digits 2 (N / 4) := by
          conv_lhs => rw [hN]
          simpa using digits_two_four_mul_add hk (r := 2) (by omega)
        constructor
        · intro hg0; rw [hg0] at hgm; norm_num at hgm
        · intro hev
          rw [EvenRuns, hdig] at hev
          exact absurd hev (splitBy_cons_cons_ne (by omega) _)
      · have hN : N = 4 * (N / 4) + 3 := by omega
        rw [hN, g_four_mul_add_three]
        have hdig : Nat.digits 2 (4 * (N / 4) + 3) = 1 :: 1 :: Nat.digits 2 (N / 4) := by
          simpa using digits_two_four_mul_add hk (r := 3) (by omega)
        rw [EvenRuns, hdig, splitBy_cons_cons_eq, ← EvenRuns, ← ih (N / 4) hlt_k]
        omega

private lemma infinite_evenRuns : Set.Infinite {m : ℕ | EvenRuns m} := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  have hpow : ∀ k : ℕ, EvenRuns (3 * 4 ^ k) := by
    intro k
    induction k with
    | zero =>
      rw [← g_eq_zero_iff_evenRuns, pow_zero, mul_one]
      have := g_four_mul_add_three 0
      simp [g] at this
      exact this
    | succ k ih =>
      rw [← g_eq_zero_iff_evenRuns] at ih ⊢
      have hmul : 3 * 4 ^ (k + 1) = 4 * (3 * 4 ^ k) := by ring
      rw [hmul, g_four_mul, ih, mul_zero]
  have hle : 3 * 4 ^ B ≤ B := hB (hpow B)
  have h2 : B < 2 ^ B := Nat.lt_two_pow_self
  have h4 : 2 ^ B ≤ 4 ^ B := Nat.pow_le_pow_left (by norm_num) B
  omega

private lemma infinite_evenRuns_succ : Set.Infinite {m : ℕ | EvenRuns (m + 1)} := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  have hinf := infinite_evenRuns
  obtain ⟨m, hm, hgt⟩ := hinf.exists_gt (B + 1)
  have hm1 : 0 < m := by omega
  have hmem : m - 1 ∈ {x : ℕ | EvenRuns (x + 1)} := by
    change EvenRuns (m - 1 + 1)
    rw [Nat.sub_add_cancel hm1]
    exact hm
  have hle : m - 1 ≤ B := hB hmem
  omega

private lemma nth_evenRuns_succ (k : ℕ) :
    Nat.nth EvenRuns (k + 1) = Nat.nth (fun m => EvenRuns (m + 1)) k + 1 := by
  have hinf' : Set.Infinite {m : ℕ | EvenRuns (m + 1)} := infinite_evenRuns_succ
  have hcount : ∀ M : ℕ, Nat.count EvenRuns (M + 1) = Nat.count (fun m => EvenRuns (m + 1)) M + 1 := by
    intro M
    induction M with
    | zero =>
      simp [Nat.count_succ, EvenRuns]
    | succ M ih =>
      rw [Nat.count_succ EvenRuns (M + 1), ih, Nat.count_succ]
      split_ifs <;> omega
  have hspec1 : EvenRuns (Nat.nth (fun m => EvenRuns (m + 1)) k + 1) :=
    Nat.nth_mem_of_infinite hinf' k
  have hcnt1 : Nat.count EvenRuns (Nat.nth (fun m => EvenRuns (m + 1)) k + 1) = k + 1 := by
    rw [hcount, Nat.count_nth_of_infinite hinf']
  rw [← hcnt1]
  exact Nat.nth_count hspec1

end OEISA374446Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a374446.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  unfold a A001196
  rw [Nat.add_sub_cancel, OEISA374446Proof.nth_evenRuns_succ, Nat.add_sub_cancel]
  have hfun : (fun m => A373308 m = 0) = (fun m => EvenRuns (m + 1)) := by
    funext m
    exact propext (OEISA374446Proof.g_eq_zero_iff_evenRuns (m + 1))
  rw [hfun]
