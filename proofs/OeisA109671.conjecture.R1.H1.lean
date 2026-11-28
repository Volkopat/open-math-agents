import OMAReductions.R_OeisA109671_conjecture_R1

/-!
The reverse focusing argument follows Daniel Larsen, *Focusing Sequences and
Self-Similarity*, Fibonacci Quarterly 58 (2020), Sections 2 and 3. https://www.fq.math.ca/Papers/58-3/larsen021620.pdf
-/

open OeisA109671 Finset
open OMA.R_OeisA109671_conjecture_R1 (a_even a_odd)

private theorem firstValue : a 1 = 1 := by rw [a.eq_def]; decide

private theorem parity (n : ℕ) : a n % 2 = if n % 3 = 0 then 0 else 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [a.eq_def]
        decide
      rw [a_even, ih k (by omega)]
      split <;> split <;> omega
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp [firstValue]
      have hp := ih (2 * k - 1) (by omega)
      have hq := ih k (by omega)
      rw [a_odd k hk]
      generalize hx : a (2 * k - 1) = x at hp ⊢
      generalize hy : a k = y at hq ⊢
      have hshift : 2 * k - 1 + 1 = 2 * k := Nat.sub_add_cancel (by omega)
      have hprev : (2 * k - 1) % 3 = (2 * (k % 3) + 2) % 3 := by omega
      have hnext : (2 * k + 1) % 3 = (2 * (k % 3) + 1) % 3 := by omega
      rw [hprev] at hp
      rw [hnext]
      have hc : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
      rcases hc with h | h | h <;> simp [h] at hp hq ⊢ <;> split <;> omega

private def prefixSum (s : ℕ → ℕ) (k : ℕ) : ℕ := ∑ i ∈ range k, s i

private theorem prefixSucc (s : ℕ → ℕ) (k : ℕ) :
    prefixSum s (k + 1) = prefixSum s k + s k := by
  exact sum_range_succ s k

private theorem oddSumLe (s t : ℕ → ℕ) (k : ℕ)
    (h : ∀ i < k, s i = t (2 * i + 1)) :
    prefixSum s k ≤ prefixSum t (2 * k) := by
  induction k with
  | zero => simp [prefixSum]
  | succ k ih =>
    rw [prefixSucc, show 2 * (k + 1) = (2 * k + 1) + 1 by omega,
      prefixSucc, prefixSucc, h k (by omega)]
    have hle := ih fun i hi => h i (by omega)
    omega

private def Focus (s : ℕ → ℕ) (m : ℕ) : Prop :=
  ∀ i < m, 2 * s i ≤ prefixSum s i + 2

private theorem focusInterleave {s t : ℕ → ℕ} {m n : ℕ}
    (hs : Focus s m) (hn : n ≤ 2 * m + 1)
    (hseed : t 0 = 1) (heven : ∀ j < m, s j = t (2 * j + 1))
    (hstep : ∀ j, 2 * j + 2 < n → t (2 * j + 2) ≤ t (2 * j) + t (2 * j + 1)) :
    Focus t n := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    rcases Nat.even_or_odd' i with ⟨k, rfl | rfl⟩
    · cases k with
      | zero => simp [hseed, prefixSum]
      | succ k =>
        have hi' : 2 * k + 2 < n := by omega
        have hk : k < m := by omega
        have hf := ih (2 * k) (by omega) (by omega)
        have hg := hs k hk
        rw [heven k hk] at hg
        have hle := oddSumLe s t k fun j hj => heven j (by omega)
        have ht := hstep k hi'
        rw [Nat.mul_succ, prefixSucc t (2 * k + 1), prefixSucc t (2 * k)]
        omega
    · have hk : k < m := by omega
      have hf := hs k hk
      have ht := oddSumLe s t k fun j hj => heven j (by omega)
      rw [heven k hk] at hf
      rw [prefixSucc]
      omega

private def reverseBlock (n i : ℕ) : ℕ := a (n - (i + 1))

-- Reading the old block backward bounds the new odd terms by the remaining budget.
private theorem firstDouble {n : ℕ} (hn : 0 < n) (hm : 3 ∣ n)
    (hfocus : Focus (reverseBlock n) (n - 1)) :
    reverseBlock (2 * n) 0 = 1 := by
  have bound (j : ℕ) (hj : j < n) :
      a (2 * j + 1) ≤ prefixSum (reverseBlock n) (n - 1 - j) + 2 := by
    induction j with
    | zero =>
      simpa only [Nat.mul_zero, Nat.zero_add, firstValue] using
        (show 1 ≤ prefixSum (reverseBlock n) (n - 1 - 0) + 2 by omega)
    | succ j ih =>
      have hj' : j < n := by omega
      let k := n - 1 - (j + 1)
      have eq : n - 1 - j = k + 1 := by dsimp [k]; omega
      have hk : k < n - 1 := by dsimp [k]; omega
      have ha : reverseBlock n k = a (j + 1) := by
        unfold reverseBlock
        congr 1
        dsimp [k]
        omega
      have hb := ih hj'
      rw [eq, prefixSucc, ha] at hb
      have hc := hfocus k hk
      rw [ha] at hc
      rw [a_odd (j + 1) (by omega), show 2 * (j + 1) - 1 = 2 * j + 1 by omega]
      change (if a (2 * j + 1) > a (j + 1) then a (2 * j + 1) - a (j + 1)
        else a (2 * j + 1) + a (j + 1)) ≤ prefixSum (reverseBlock n) k + 2
      split <;> omega
  have hlast := bound (n - 1) (by omega)
  rw [show 2 * (n - 1) + 1 = 2 * n - 1 by omega, Nat.sub_self] at hlast
  simp only [prefixSum, sum_range_zero, Nat.zero_add] at hlast
  have hmod : (2 * n - 1) % 3 ≠ 0 := by
    obtain ⟨q, hq⟩ := hm
    omega
  have hp := parity (2 * n - 1)
  rw [if_neg hmod] at hp
  change a (2 * n - 1) = 1
  omega

private theorem focusDouble {n : ℕ} (hn : 0 < n) (hm : 3 ∣ n)
    (hfocus : Focus (reverseBlock n) (n - 1)) :
    Focus (reverseBlock (2 * n)) (2 * n - 1) := by
  refine focusInterleave hfocus (by omega) (firstDouble hn hm hfocus) ?_ ?_
  · intro j hj
    unfold reverseBlock
    rw [show 2 * n - (2 * j + 1 + 1) = 2 * (n - (j + 1)) by omega, a_even]
  · intro j hj
    let k := n - (j + 1)
    have hk : 0 < k := by dsimp [k]; omega
    unfold reverseBlock
    rw [show 2 * n - (2 * j + 2 + 1) = 2 * k - 1 by dsimp [k]; omega,
      show 2 * n - (2 * j + 1) = 2 * k + 1 by dsimp [k]; omega,
      show 2 * n - (2 * j + 1 + 1) = 2 * k by dsimp [k]; omega,
      a_even, a_odd k hk]
    split <;> omega

theorem OMA.solution : OMA.R_OeisA109671_conjecture_R1.H1 := by
  intro k hk
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk) with ⟨j, rfl⟩
  have hf (j : ℕ) : Focus (reverseBlock (3 * 2 ^ j)) (3 * 2 ^ j - 1) := by
    induction j with
    | zero =>
      intro i hi
      have hi' : i = 0 ∨ i = 1 := by simpa using (show i < 2 → i = 0 ∨ i = 1 by omega) hi
      rcases hi' with rfl | rfl
      · change 2 * a 2 ≤ prefixSum (reverseBlock 3) 0 + 2
        have h : a 2 = 1 := by rw [show (2 : ℕ) = 2 * 1 by decide, a_even, firstValue]
        simp [h, prefixSum]
      · change 2 * a 1 ≤ prefixSum (reverseBlock 3) 1 + 2
        rw [firstValue]
        omega
    | succ j ih =>
      rw [pow_succ, show 3 * (2 ^ j * 2) = 2 * (3 * 2 ^ j) by ring]
      exact focusDouble (by positivity) (dvd_mul_right 3 _) ih
  rw [pow_succ, show 3 * (2 ^ j * 2) = 2 * (3 * 2 ^ j) by ring]
  exact firstDouble (by positivity) (dvd_mul_right 3 _) (hf j)
