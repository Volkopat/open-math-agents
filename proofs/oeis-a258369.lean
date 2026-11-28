import OMAStatements.S_oeis_a258369

-- Problem: A258369: Stirling-Bernoulli transform of A027656.
-- Upstream: formal-conjectures statements/oeis-a258369.lean:0 (declaration OMA.S_oeis_a258369.main)
-- Credit: @lettucrisp (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/- Both sides equal sum_k (k/2 + 1) k! S(n,k): the left side by the recurrence of S, the right side by
   sum_j C(n,j) S(j,k) = S(n+1,k+1) and binomial inversion. (An operator-based plan for this problem was
   posted by @tox5tox5; this proof takes a different, sum-based route.) -/

namespace OMA.A258369Proof
open OMA.S_oeis_a258369 Finset

/-- Stirling numbers of the second kind, as integers. -/
def S (n k : ℕ) : ℤ := (Nat.stirlingSecond n k : ℤ)

lemma S_succ (n k : ℕ) : S (n + 1) (k + 1) = (k + 1) * S n (k + 1) + S n k := by
  simp only [S, Nat.stirlingSecond_succ_succ]; push_cast; ring

lemma S_lt {n k : ℕ} (h : n < k) : S n k = 0 := by
  simp [S, Nat.stirlingSecond_eq_zero_of_lt h]

/-- Shifting the second index of a Stirling sum by one. -/
lemma shift (g : ℕ → ℤ) (n : ℕ) :
    ∑ k ∈ range (n + 1), g k * S (n + 1) (k + 1) =
      ∑ m ∈ range (n + 1), (g m + (if m = 0 then 0 else (m : ℤ) * g (m - 1))) * S n m := by
  let h : ℕ → ℤ := fun m => (if m = 0 then 0 else (m : ℤ) * g (m - 1)) * S n m
  have e1 : ∑ k ∈ range (n + 1), g k * ((k + 1) * S n (k + 1)) = ∑ m ∈ range (n + 1), h m := by
    have a := Finset.sum_range_succ' h (n + 1)
    have b := Finset.sum_range_succ h (n + 1)
    have h0 : h 0 = 0 := by simp [h]
    have hn : h (n + 1) = 0 := by simp [h, S_lt (Nat.lt_succ_self n)]
    rw [h0, add_zero] at a
    rw [hn, add_zero] at b
    rw [← b, a]
    apply Finset.sum_congr rfl; intro k _
    simp only [h, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]; push_cast; ring
  simp_rw [S_succ, mul_add, Finset.sum_add_distrib, e1, h, add_mul, Finset.sum_add_distrib]
  ring

/-- The common closed form. -/
def L (n : ℕ) : ℤ := ∑ m ∈ range (n + 1), ((m / 2 : ℕ) + 1 : ℤ) * (m.factorial : ℤ) * S n m

lemma c_even (t : ℕ) : a027656 (2 * t) = t + 1 := by
  unfold a027656; rw [if_pos (by omega), show 2 * t / 2 = t by omega]

lemma c_odd (t : ℕ) : a027656 (2 * t + 1) = 0 := by
  unfold a027656; rw [if_neg (by omega)]

lemma lhs_eq (n : ℕ) : a258369 n = L n := by
  have h1 : a258369 n = ∑ k ∈ range (n + 1),
      ((-1 : ℤ) ^ k * (k.factorial : ℤ) * a027656 k) * S (n + 1) (k + 1) := by
    unfold a258369; apply Finset.sum_congr rfl; intro k _; simp only [S]; ring
  rw [h1, shift, L]
  apply Finset.sum_congr rfl; intro m _
  congr 1
  rcases Nat.even_or_odd' m with ⟨t, rfl | rfl⟩
  · rcases t with _ | t
    · simp [a027656]
    · have hf : (2 * (t + 1)).factorial = (2 * (t + 1)) * (2 * t + 1).factorial := by
        rw [show 2 * (t + 1) = (2 * t + 1) + 1 by ring, Nat.factorial_succ]
      rw [if_neg (by omega), show 2 * (t + 1) - 1 = 2 * t + 1 by omega, c_even, c_odd,
        show 2 * (t + 1) / 2 = t + 1 by omega, hf, pow_mul]
      push_cast
      ring
  · have hf : (2 * t + 1).factorial = (2 * t + 1) * (2 * t).factorial := Nat.factorial_succ _
    rw [if_neg (by omega), show 2 * t + 1 - 1 = 2 * t by omega, c_even, c_odd,
      show (2 * t + 1) / 2 = t by omega, hf, pow_succ, pow_mul]
    push_cast
    ring

/-- `∑ C(n, j) S(j, k) = S(n + 1, k + 1)`. -/
lemma choose_S (n : ℕ) : ∀ k : ℕ,
    ∑ j ∈ range (n + 1), (n.choose j : ℤ) * S j k = S (n + 1) (k + 1) := by
  induction n with
  | zero =>
    intro k
    rcases k with _ | k
    · simp [S, Nat.stirlingSecond_self]
    · simp [S, Nat.stirlingSecond_eq_zero_of_lt (show 1 < k + 1 + 1 by omega)]
  | succ n ih =>
    intro k
    have e1 : ∑ j ∈ range (n + 1), (n.choose (j + 1) : ℤ) * S (j + 1) k =
        ∑ j ∈ range (n + 1), (n.choose j : ℤ) * S j k - S 0 k := by
      have := Finset.sum_range_succ' (fun j => (n.choose j : ℤ) * S j k) (n + 1)
      rw [Finset.sum_range_succ, Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero] at this
      rw [this]; simp
    have e2 : ∑ j ∈ range (n + 1), (n.choose j : ℤ) * S (j + 1) k =
        if k = 0 then 0 else (k : ℤ) * S (n + 1) (k + 1) + S (n + 1) k := by
      rcases k with _ | k
      · simp [S]
      · rw [if_neg (by omega)]
        have hs : ∑ j ∈ range (n + 1), (n.choose j : ℤ) * S (j + 1) (k + 1) =
            ∑ j ∈ range (n + 1), (((k : ℤ) + 1) * ((n.choose j : ℤ) * S j (k + 1)) +
              (n.choose j : ℤ) * S j k) :=
          Finset.sum_congr rfl (fun j _ => by rw [S_succ]; ring)
        rw [hs, Finset.sum_add_distrib, ← Finset.mul_sum, ih (k + 1), ih k]
        push_cast; ring
    have split : ∑ j ∈ range (n + 1 + 1), ((n + 1).choose j : ℤ) * S j k =
        ∑ j ∈ range (n + 1), (n.choose (j + 1) : ℤ) * S (j + 1) k +
          ∑ j ∈ range (n + 1), (n.choose j : ℤ) * S (j + 1) k + S 0 k := by
      rw [Finset.sum_range_succ', Nat.choose_zero_right, Nat.cast_one, one_mul]
      simp only [Nat.choose_succ_succ', Nat.cast_add, add_mul, Finset.sum_add_distrib]
      ring
    rw [split, e1, e2, ih k]
    rcases k with _ | k
    · simp [S, Nat.stirlingSecond_one_right]
    · rw [if_neg (by omega), S_succ (n + 1) (k + 1)]
      push_cast
      ring

/-- `a005649` in Stirling form. -/
lemma A_eq (n : ℕ) : a005649 n = ∑ j ∈ range (n + 1), (n.choose j : ℤ) * L j := by
  have ext : ∀ j ∈ range (n + 1), (n.choose j : ℤ) * L j =
      ∑ m ∈ range (n + 1), ((m / 2 : ℕ) + 1 : ℤ) * (m.factorial : ℤ) * ((n.choose j : ℤ) * S j m) := by
    intro j hj
    rw [L, Finset.mul_sum]
    rw [← Finset.sum_subset (Finset.range_subset_range.mpr (show j + 1 ≤ n + 1 by
      simp at hj; omega))]
    · apply Finset.sum_congr rfl; intro m _; ring
    · intro m _ hm
      simp at hm
      rw [S_lt (by omega)]; ring
  rw [Finset.sum_congr rfl ext, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, choose_S]
  rw [shift]
  unfold a005649
  apply Finset.sum_congr rfl; intro m _
  simp only [S]
  rcases m with _ | m
  · simp
  · rw [if_neg (by omega), show m + 1 - 1 = m by omega]
    have hpq : (m + 1) / 2 + m / 2 = m := by omega
    have key : ((m + 1) / 2 + 1) * (m + 1).factorial + (m + 1) * ((m / 2 + 1) * m.factorial) =
        (m + 1 + 1).factorial := by
      have e : ((m + 1) / 2 + 1) * (m + 1).factorial + (m + 1) * ((m / 2 + 1) * m.factorial) =
          (m + 1) * m.factorial * (((m + 1) / 2 + m / 2) + 2) := by
        rw [Nat.factorial_succ m]; ring
      rw [e, hpq, Nat.factorial_succ (m + 1), Nat.factorial_succ m]; ring
    have keyZ : ((((m + 1) / 2 : ℕ) : ℤ) + 1) * ((m + 1).factorial : ℤ) +
        ((m + 1 : ℕ) : ℤ) * (((((m / 2 : ℕ)) : ℤ) + 1) * (m.factorial : ℤ)) =
        ((m + 1 + 1).factorial : ℤ) := by exact_mod_cast key
    rw [← keyZ]; ring

/-- `∑_j (-1)^(n-j) C(n, j) C(j, i) = [i = n]`. -/
lemma alt_choose (n i : ℕ) (hi : i ≤ n) :
    ∑ j ∈ range (n + 1), (-1 : ℤ) ^ (n - j) * (n.choose j : ℤ) * (j.choose i : ℤ) =
      if i = n then 1 else 0 := by
  have h1 : ∑ j ∈ range (n + 1), (-1 : ℤ) ^ (n - j) * (n.choose j : ℤ) * (j.choose i : ℤ) =
      ∑ j ∈ Ico i (n + 1), (-1 : ℤ) ^ (n - j) * (n.choose j : ℤ) * (j.choose i : ℤ) := by
    rw [Finset.range_eq_Ico]
    symm
    apply Finset.sum_subset (Finset.Ico_subset_Ico_left (Nat.zero_le i))
    intro j hj hj'
    simp only [Finset.mem_Ico] at hj hj'
    have hji : j < i := by by_contra hc; exact hj' ⟨by omega, hj.2⟩
    rw [Nat.choose_eq_zero_of_lt (n := j) (k := i) hji]; simp
  rw [h1, Finset.sum_Ico_eq_sum_range, show n + 1 - i = (n - i) + 1 by omega]
  have h2 : ∀ t ∈ range (n - i + 1), (-1 : ℤ) ^ (n - (i + t)) * (n.choose (i + t) : ℤ) *
      ((i + t).choose i : ℤ) = (n.choose i : ℤ) * ((-1 : ℤ) ^ (n - i) * ((-1) ^ t * ((n - i).choose t : ℤ))) := by
    intro t ht
    simp at ht
    have e := Nat.choose_mul (n := n) (k := i + t) (s := i) (by omega)
    rw [show i + t - i = t by omega] at e
    have hp : (-1 : ℤ) ^ (n - (i + t)) = (-1) ^ (n - i) * (-1) ^ t := by
      rw [show n - i = (n - (i + t)) + t by omega, pow_add, mul_assoc, ← pow_add, ← two_mul, pow_mul]
      simp
    rw [hp, mul_assoc, show ((n.choose (i + t) : ℤ) * ((i + t).choose i : ℤ)) =
      ((n.choose i * (n - i).choose t : ℕ) : ℤ) by rw [← e]; push_cast; ring]
    push_cast; ring
  rw [Finset.sum_congr rfl h2, ← Finset.mul_sum, ← Finset.mul_sum, Int.alternating_sum_range_choose]
  by_cases h : i = n
  · subst h; simp
  · rw [if_neg (by omega), if_neg h]; simp

/-- Binomial inversion. -/
lemma inversion (Lf Af : ℕ → ℤ) (h : ∀ n, Af n = ∑ j ∈ range (n + 1), (n.choose j : ℤ) * Lf j)
    (n : ℕ) : ∑ j ∈ range (n + 1), (-1 : ℤ) ^ (n - j) * (n.choose j : ℤ) * Af j = Lf n := by
  simp_rw [h, Finset.mul_sum]
  have ext : ∀ j ∈ range (n + 1),
      ∑ i ∈ range (j + 1), (-1 : ℤ) ^ (n - j) * (n.choose j : ℤ) * ((j.choose i : ℤ) * Lf i) =
      ∑ i ∈ range (n + 1), (-1 : ℤ) ^ (n - j) * (n.choose j : ℤ) * ((j.choose i : ℤ) * Lf i) := by
    intro j hj
    apply Finset.sum_subset (Finset.range_subset_range.mpr (by simp at hj; omega))
    intro i _ hi
    simp only [Finset.mem_range, not_lt] at hi
    rw [Nat.choose_eq_zero_of_lt (n := j) (k := i) (by omega)]; simp
  rw [Finset.sum_congr rfl ext, Finset.sum_comm]
  have inner : ∀ i ∈ range (n + 1),
      ∑ j ∈ range (n + 1), (-1 : ℤ) ^ (n - j) * (n.choose j : ℤ) * ((j.choose i : ℤ) * Lf i) =
      (if i = n then 1 else 0) * Lf i := by
    intro i hi
    simp at hi
    rw [← alt_choose n i (by omega), Finset.sum_mul]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [Finset.sum_congr rfl inner]
  simp

end OMA.A258369Proof

open OMA.A258369Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a258369.main := by
  intro n
  rw [lhs_eq]
  exact (inversion L OMA.S_oeis_a258369.a005649 A_eq n).symm
