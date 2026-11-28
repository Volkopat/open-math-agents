import OMAStatements.S_oeis_a355076

open scoped BigOperators
open OMA.S_oeis_a355076

private theorem fusc_even (m : ℕ) : fusc (2 * m) = fusc m := by
  by_cases h : m = 0
  · simp [h]
  · have e : 2 * m = (2 * m - 2) + 2 := by omega
    conv_lhs => rw [e, fusc]
    rw [if_neg (show ¬ (2 * m - 2) % 2 = 1 by omega), add_zero,
      show (2 * m - 2 + 2) / 2 = m by omega]

private theorem fusc_odd (m : ℕ) : fusc (2 * m + 1) = fusc m + fusc (m + 1) := by
  by_cases h : m = 0
  · subst m
    change fusc 1 = fusc 0 + fusc 1
    simp only [fusc, zero_add]
  · have e : 2 * m + 1 = (2 * m - 1) + 2 := by omega
    conv_lhs => rw [e, fusc]
    rw [if_pos (show (2 * m - 1) % 2 = 1 by omega),
      show (2 * m - 1 + 2) / 2 = m by omega,
      show (2 * m - 1 + 3) / 2 = m + 1 by omega]

private theorem fusc_pos {n : ℕ} (hn : 0 < n) : 0 < fusc n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h : n = 1
    · subst n
      simp only [fusc, Nat.zero_lt_one]
    have hm : 0 < n / 2 := by omega
    have hp := ih (n / 2) (by omega) hm
    by_cases hpar : n % 2 = 0
    · rwa [show n = 2 * (n / 2) by omega, fusc_even]
    · rw [show n = 2 * (n / 2) + 1 by omega, fusc_odd]
      omega

private theorem fusc_power (m : ℕ) : fusc (2 ^ m) = 1 := by
  induction m with
  | zero => change fusc 1 = 1; simp only [fusc]
  | succ m ih =>
    rw [pow_succ, Nat.mul_comm (2 ^ m), fusc_even, ih]

private theorem fusc_mirror (m i : ℕ) (hi : i ≤ 2 ^ m) :
    fusc (2 ^ m + i) = fusc (2 ^ m + (2 ^ m - i)) := by
  induction m generalizing i with
  | zero =>
    have h : i = 0 ∨ i = 1 := by norm_num at hi; omega
    rcases h with rfl | rfl
    · change fusc 1 = fusc 2
      rw [show 2 = 2 * 1 by decide, fusc_even]
    · change fusc 2 = fusc 1
      rw [show 2 = 2 * 1 by decide, fusc_even]
  | succ m ih =>
    set p := 2 ^ m with hp
    have he : 2 ^ (m + 1) = 2 * p := by rw [hp, pow_succ, Nat.mul_comm]
    rw [he] at hi ⊢
    let j := i / 2
    have hjdef : j = i / 2 := rfl
    by_cases hs : i % 2 = 0
    · rw [show 2 * p + i = 2 * (p + j) by omega, fusc_even,
        show 2 * p + (2 * p - i) = 2 * (p + (p - j)) by omega, fusc_even]
      exact ih j (by omega)
    · rw [show 2 * p + i = 2 * (p + j) + 1 by omega, fusc_odd,
        show 2 * p + (2 * p - i) = 2 * (p + (p - (j + 1))) + 1 by omega, fusc_odd]
      have h₁ := ih j (by omega)
      have h₂ := ih (j + 1) (by omega)
      rw [show p + j + 1 = p + (j + 1) by omega, h₁, h₂,
        show p + (p - (j + 1)) + 1 = p + (p - j) by omega, add_comm]

private def ratio (n : ℕ) : ℚ := (fusc n : ℚ) / fusc (n + 1)

private def piece (n : ℕ) : ℚ := (fusc n : ℚ) / ((fusc n : ℚ) + fusc (n + 1))

private theorem piece_row (m : ℕ) :
    2 * (∑ i ∈ Finset.range (2 ^ m), piece (2 ^ m + i)) = (2 : ℚ) ^ m := by
  let p : ℕ := 2 ^ m
  let other (i : ℕ) := (fusc (p + i + 1) : ℚ) / ((fusc (p + i) : ℚ) + fusc (p + i + 1))
  have href : (∑ i ∈ Finset.range p, other i) = ∑ i ∈ Finset.range p, piece (p + i) := by
    rw [← Finset.sum_range_reflect other p]
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hl := Finset.mem_range.mp hi
    have h₁ := fusc_mirror m i (by omega)
    have h₂ := fusc_mirror m (i + 1) (by omega)
    change fusc (p+i) = fusc (p+(p-i)) at h₁
    change fusc (p+(i+1)) = fusc (p+(p-(i+1))) at h₂
    unfold other piece
    rw [show p + (p - 1 - i) + 1 = p + (p - i) by omega, ← h₁,
      show p + (p - 1 - i) = p + (p - (i + 1)) by omega, ← h₂,
      show p + (i + 1) = p + i + 1 by omega]
    rw [add_comm ((fusc (p+i+1) : ℕ) : ℚ) (fusc (p+i) : ℚ)]
  have hsum : (∑ i ∈ Finset.range p, (piece (p+i) + other i)) = (p : ℚ) := by
    calc
      _ = ∑ _i ∈ Finset.range p, (1 : ℚ) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        unfold piece other
        rw [← add_div]
        exact div_self (by
          have hp := fusc_pos (Nat.succ_pos (p+i))
          positivity)
      _ = (p : ℚ) := by simp
  rw [Finset.sum_add_distrib, href, ← two_mul] at hsum
  simpa [p] using hsum

private theorem piece_prefix (m : ℕ) :
    2 * (∑ i ∈ Finset.range (2 ^ m), piece i) = (2 : ℚ) ^ m - 1 := by
  induction m with
  | zero => norm_num [piece, fusc]
  | succ m ih =>
    rw [pow_succ, show (2 : ℕ) ^ m * 2 = 2 ^ m + 2 ^ m by ring,
      Finset.sum_range_add, mul_add, ih, piece_row]
    ring

private theorem ratio_children (k : ℕ) :
    ratio (2*k) + ratio (2*k+1) = piece k + (ratio k + 1) := by
  unfold ratio piece
  rw [fusc_even, fusc_odd, show 2*k+1+1 = 2*(k+1) by omega, fusc_even]
  push_cast
  have hp := fusc_pos (show 0 < k + 1 by omega)
  have hn : (fusc (k+1) : ℚ) ≠ 0 := by positivity
  rw [add_div, div_self hn]

private theorem sum_pairs (g : ℕ → ℚ) (n : ℕ) :
    (∑ i ∈ Finset.range (2*n), g i) =
      ∑ i ∈ Finset.range n, (g (2*i) + g (2*i+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1) = 2*n+1+1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    ring

private theorem ratio_prefix (m : ℕ) :
    2 * (∑ k ∈ Finset.range (2 ^ m), ratio k) = 3 * (2 : ℚ)^m - 3 - m := by
  induction m with
  | zero => norm_num [ratio, fusc]
  | succ m ih =>
    rw [show (2 : ℕ) ^ (m+1) = 2 * 2 ^ m by rw [pow_succ, Nat.mul_comm], sum_pairs]
    simp_rw [ratio_children, Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
      Nat.cast_pow, Nat.cast_ofNat, Nat.cast_succ, pow_succ _ m]
    rw [mul_add, mul_add, piece_prefix, ih]
    ring

theorem OMA.solution : type_of% @OMA.S_oeis_a355076.main := by
  intro k
  let N : ℕ := 2 * 4 ^ k
  have hN : N = 2 ^ (2*k+1) := by rw [pow_succ, pow_mul]; ring
  have hpos : 2 ≤ N := by
    have : 0 < (4 : ℕ) ^ k := by positivity
    dsimp [N]
    omega
  have h := ratio_prefix (2*k+1)
  rw [← hN] at h
  have hpow : (2 : ℚ) ^ (2*k+1) = 2 * 4 ^ k := by rw [pow_succ, pow_mul]; ring
  let M : ℤ := 3 * (4 : ℤ)^k - (k : ℤ) - 2
  have hcast : (∑ i ∈ Finset.range N, ratio i) = (M : ℚ) := by
    rw [hpow] at h
    push_cast at h
    dsimp [M]
    push_cast
    linarith
  have hlast : ratio (N-1) = (fusc (N-1) : ℚ) := by
    unfold ratio
    rw [show N-1+1=N by omega, hN, fusc_power, Nat.cast_one, div_one]
  have hshort : (∑ i ∈ Finset.range (N-1), ratio i) = ((M - (fusc (N-1) : ℤ) : ℤ) : ℚ) := by
    have hs := Finset.sum_range_succ ratio (N-1)
    rw [show N-1+1=N by omega, hcast, hlast] at hs
    push_cast
    linarith
  change a (N-1) = 1 ∧ a (N-2) = 1
  unfold a
  change (∑ i ∈ Finset.range (N-1+1), ratio i).den = 1 ∧
    (∑ i ∈ Finset.range (N-2+1), ratio i).den = 1
  rw [show N-1+1=N by omega, show N-2+1=N-1 by omega, hcast, hshort]
  simp