import OMAStatements.S_oeis_a102395

-- Problem: A102395, every term is in A078008.
-- Credit: @ShoQo
-- Proof: let b_r(n) = Σ_k [n+k ≡ r (mod 3)] (C(n,k) mod 2). Lucas's theorem mod 2 gives
-- b_r(2n) = b_{2r}(n) and b_r(2n+1) = b_{2r+1}(n) + b_{2r+2}(n) (indices mod 3). By induction
-- b_0(n) + 2 J(s) = 2^s for some s (J the Jacobsthal numbers), and A078008(s) + 2 J(s) = 2^s.

open OMA.S_oeis_a102395

namespace OMA_A102395_Proof

/-- Lucas's theorem for p = 2, one binary digit at a time. -/
lemma lucas2 (n k : ℕ) :
    n.choose k % 2 = (n % 2).choose (k % 2) * (n / 2).choose (k / 2) % 2 :=
  @Choose.choose_modEq_choose_mod_mul_choose_div_nat n k 2 ⟨Nat.prime_two⟩

lemma c_ee (n j : ℕ) : (2 * n).choose (2 * j) % 2 = n.choose j % 2 := by
  rw [lucas2, show 2 * n % 2 = 0 by omega, show 2 * j % 2 = 0 by omega,
    show 2 * n / 2 = n by omega, show 2 * j / 2 = j by omega]; simp

lemma c_eo (n j : ℕ) : (2 * n).choose (2 * j + 1) % 2 = 0 := by
  rw [lucas2, show 2 * n % 2 = 0 by omega, show (2 * j + 1) % 2 = 1 by omega]; simp

lemma c_oe (n j : ℕ) : (2 * n + 1).choose (2 * j) % 2 = n.choose j % 2 := by
  rw [lucas2, show (2 * n + 1) % 2 = 1 by omega, show 2 * j % 2 = 0 by omega,
    show (2 * n + 1) / 2 = n by omega, show 2 * j / 2 = j by omega]; simp

lemma c_oo (n j : ℕ) : (2 * n + 1).choose (2 * j + 1) % 2 = n.choose j % 2 := by
  rw [lucas2, show (2 * n + 1) % 2 = 1 by omega, show (2 * j + 1) % 2 = 1 by omega,
    show (2 * n + 1) / 2 = n by omega, show (2 * j + 1) / 2 = j by omega]; simp

/-- The residue-class sums b_r(n). -/
def B (r n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), if (n + k) % 3 = r then n.choose k % 2 else 0

lemma sum_two_mul (f : ℕ → ℕ) (m : ℕ) :
    ∑ k ∈ Finset.range (2 * m), f k = ∑ j ∈ Finset.range m, (f (2 * j) + f (2 * j + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ]
    ring

lemma B_even (r n : ℕ) (hr : r < 3) : B r (2 * n) = B (2 * r % 3) n := by
  unfold B
  rw [Finset.sum_range_succ, sum_two_mul, Finset.sum_range_succ]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [c_ee, c_eo]; split_ifs <;> omega
  · rw [c_ee]; split_ifs <;> omega

lemma B_odd (r n : ℕ) (hr : r < 3) :
    B r (2 * n + 1) = B ((2 * r + 1) % 3) n + B ((2 * r + 2) % 3) n := by
  unfold B
  rw [show 2 * n + 1 + 1 = 2 * (n + 1) by ring, sum_two_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [c_oe, c_oo]; split_ifs <;> omega

/-- Jacobsthal numbers, as in A001045. -/
def J : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | (n + 2) => J (n + 1) + 2 * J n

lemma J_succ_add (s : ℕ) : J (s + 1) + J s = 2 ^ s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    have h : J (s + 2) = J (s + 1) + 2 * J s := rfl
    rw [h, pow_succ]; omega

lemma B_zero : B 0 0 = 1 ∧ B 1 0 = 0 ∧ B 2 0 = 0 := by simp [B]

/-- b₁ = b₂ = J(s) and b₀ + 2 J(s) = 2^s, with s the binary digit sum. -/
lemma triple (n : ℕ) : ∃ s, B 0 n + 2 * J s = 2 ^ s ∧ B 1 n = J s ∧ B 2 n = J s := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨0, by rw [B_zero.1]; rfl, B_zero.2.1, B_zero.2.2⟩
    obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 * m ∨ n = 2 * m + 1 := ⟨n / 2, by omega⟩
    · obtain ⟨s, h0, h1, h2⟩ := ih m (by omega)
      have e0 := B_even 0 m (by norm_num)
      have e1 := B_even 1 m (by norm_num)
      have e2 := B_even 2 m (by norm_num)
      norm_num at e0 e1 e2
      exact ⟨s, by rw [e0]; exact h0, by rw [e1]; exact h2, by rw [e2]; exact h1⟩
    · obtain ⟨s, h0, h1, h2⟩ := ih m (by omega)
      have e0 := B_odd 0 m (by norm_num)
      have e1 := B_odd 1 m (by norm_num)
      have e2 := B_odd 2 m (by norm_num)
      norm_num at e0 e1 e2
      have hJ := J_succ_add s
      refine ⟨s + 1, ?_, ?_, ?_⟩
      · rw [e0, pow_succ]; omega
      · rw [e1]; omega
      · rw [e2]; omega

lemma A_add_J (s : ℕ) : A078008 s + 2 * J s = 2 ^ s := by
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    match s, ih with
    | 0, _ => rfl
    | 1, _ => rfl
    | s + 2, ih =>
      have h1 := ih (s + 1) (by omega)
      have h0 := ih s (by omega)
      show A078008 (s + 1) + 2 * A078008 s + 2 * (J (s + 1) + 2 * J s) = 2 ^ (s + 2)
      rw [pow_succ, pow_succ] at *
      omega

end OMA_A102395_Proof

open OMA_A102395_Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a102395.main := by
  intro n
  obtain ⟨s, h0, _, _⟩ := triple n
  have := A_add_J s
  exact ⟨s, by unfold a; unfold B at h0; omega⟩
