import OMAReductions.R_OeisA109074_conjecture_R1_H2_R1

/-! # The two new numerator rows of the symplectic dimension formula
Credit: @shivareddy42.
Pair the previous weights 3k+1 and 3k+2. For a fixed k the four differences and
four sums form two blocks of four consecutive factors with the middle factor
repeated. Reflect the differences and append the sums to obtain 2n blocks. -/

open Finset

private theorem prod_pairs (f : ℕ → ℕ) (n : ℕ) :
    (∏ j ∈ range (2*n), f j) = ∏ k ∈ range n, f (2*k) * f (2*k+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1) = 2*n+1+1 by omega, prod_range_succ, prod_range_succ,
      ih, prod_range_succ, mul_assoc]

theorem OMA.solution : OMA.R_OeisA109074_conjecture_R1_H2_R1.H2 := by
  intro n
  let a (j : ℕ) := j+1+j/2
  let f (t j : ℕ) := (t - a j) * (t + a j)
  let d (k : ℕ) := (3*k+2) * (3*k+3)^2 * (3*k+4)
  have even (k : ℕ) : a (2*k) = 3*k+1 := by dsimp [a]; omega
  have odd (k : ℕ) : a (2*k+1) = 3*k+2 := by dsimp [a]; omega
  have block (k : ℕ) (hk : k < n) :
      (f (3*n+1) (2*k) * f (3*n+2) (2*k)) *
        (f (3*n+1) (2*k+1) * f (3*n+2) (2*k+1)) =
      d (n-1-k) * d (n+k) := by
    obtain ⟨t, ht⟩ : ∃ t, n = k+1+t := ⟨n-1-k, by omega⟩
    subst n
    simp only [f, even, odd, d]
    rw [show k+1+t-1-k = t by omega,
      show 3*(k+1+t)+1-(3*k+1) = 3*t+3 by omega,
      show 3*(k+1+t)+2-(3*k+1) = 3*t+4 by omega,
      show 3*(k+1+t)+1-(3*k+2) = 3*t+2 by omega,
      show 3*(k+1+t)+2-(3*k+2) = 3*t+3 by omega]
    ring
  have rows :
      (∏ i ∈ range (2*n), f (3*n+1) i) * (∏ i ∈ range (2*n), f (3*n+2) i) =
      ∏ k ∈ range (2*n), d k := by
    rw [← prod_mul_distrib, prod_pairs]
    calc
      _ = ∏ k ∈ range n, d (n-1-k) * d (n+k) :=
        prod_congr rfl (fun k hk => block k (mem_range.mp hk))
      _ = _ := by
        rw [prod_mul_distrib, prod_range_reflect, two_mul, prod_range_add]
  have factorials (m : ℕ) : (∏ k ∈ range m, d k) =
      (3*m+1).factorial * 3^m * m.factorial := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [prod_range_succ, ih, show 3*(m+1)+1 = (3*m+1)+1+1+1 by omega,
        Nat.factorial_succ ((3*m+1)+1+1), Nat.factorial_succ ((3*m+1)+1),
        Nat.factorial_succ (3*m+1), Nat.factorial_succ m, pow_succ]
      dsimp [d]
      ring
  change 2*(4*n+2) * ((a (2*n) * ∏ i ∈ range (2*n), f (a (2*n)) i) *
    (a (2*n+1) * ∏ i ∈ range (2*n+1), f (a (2*n+1)) i)) = _
  rw [even, odd, prod_range_succ]
  have last : f (3*n+2) (2*n) = 6*n+3 := by
    simp only [f, even, show 3*n+2-(3*n+1) = 1 by omega, one_mul]
    omega
  rw [last]
  have h := rows.trans (factorials (2*n))
  rw [show 3*(2*n)+1 = 6*n+1 by omega] at h
  rw [Nat.factorial_succ (6*n+3), Nat.factorial_succ (6*n+2),
    Nat.factorial_succ (6*n+1), Nat.factorial_succ (2*n)]
  calc
    _ = 2*(4*n+2)*(3*n+1)*(3*n+2)*(6*n+3) *
        ((∏ i ∈ range (2*n), f (3*n+1) i) * (∏ i ∈ range (2*n), f (3*n+2) i)) := by ring
    _ = _ := by rw [h]; ring
