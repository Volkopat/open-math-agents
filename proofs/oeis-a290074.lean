import OMAStatements.S_oeis_a290074

open OMA.S_oeis_a290074 PowerSeries

namespace Diagonal641

def background (r : ℕ) : ℕ → Bool
  | 0 => false
  | n+1 => r.testBit (9*(background r n).toNat)

lemma outside (r t : ℕ) (x y : ℤ) (h : (t : ℤ) < |x| ∨ (t : ℤ) < |y|) :
    state r t x y = background r t := by
  induction t generalizing x y with
  | zero =>
    simp only [state, background, decide_eq_false_iff_not]
    rintro ⟨rfl,rfl⟩
    simp at h
  | succ t ih =>
    simp only [Nat.cast_succ, lt_abs] at h
    simp only [state, background]
    rw [ih x y (by simp only [lt_abs]; omega),
        ih (x-1) y (by simp only [lt_abs]; omega),
        ih (x+1) y (by simp only [lt_abs]; omega),
        ih x (y-1) (by simp only [lt_abs]; omega),
        ih x (y+1) (by simp only [lt_abs]; omega)]
    cases background r t <;> rfl

lemma iterate_cycle (r s p n : ℕ) (h : state r (s+p) = state r s) :
    state r (s+n+p) = state r (s+n) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [show s+(n+1)+p = (s+n+p)+1 by omega, show s+(n+1) = (s+n)+1 by omega]
    funext x y
    simp only [state,ih]

lemma cycle : state 641 4 = state 641 2 := by
  funext x y
  by_cases h : (4 : ℤ) < |x| ∨ (4 : ℤ) < |y|
  · rw [outside 641 4 x y h, outside 641 2 x y (by rcases h with h|h <;> omega)]
    decide
  · simp only [not_or, not_lt, abs_le] at h
    obtain ⟨⟨_, _⟩, ⟨_, _⟩⟩ := h
    interval_cases x <;> interval_cases y <;> decide

lemma cycle_at (n : ℕ) (hn : 2 ≤ n) : state 641 (n+2) = state 641 n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 2+k := ⟨n-2, by omega⟩
  exact iterate_cycle 641 2 2 k cycle

lemma bg_on (n : ℕ) : background 641 (n+1) = true := by
  induction n with
  | zero => decide
  | succ n ih => rw [background, ih]; decide

lemma advance (n : ℕ) (hn : 2 ≤ n) : a (n+2) = 4*a n+3 := by
  have he : n ≠ 1 := by omega
  have bg : background 641 n = true := by
    convert bg_on (n-1) using 2 <;> omega
  have edge1 : state 641 n ((n+1 : ℕ) : ℤ) ((n+1 : ℕ) : ℤ) = true :=
    (outside _ _ _ _ (Or.inl (by simp only [lt_abs, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]; omega))).trans bg
  have edge2 : state 641 n ((n+1+1 : ℕ) : ℤ) ((n+1+1 : ℕ) : ℤ) = true :=
    (outside _ _ _ _ (Or.inl (by simp only [lt_abs, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]; omega))).trans bg
  unfold a digits
  rw [show n+2+1 = (n+1+1)+1 by omega, Finset.sum_range_succ, Finset.sum_range_succ,
    cycle_at n (by omega), edge1, edge2]
  have hs : (∑ i ∈ Finset.range (n+1), ((state 641 n (i : ℤ) (i : ℤ)).toNat : ℤ)*2^(n+2-i)) =
      (∑ i ∈ Finset.range (n+1), ((state 641 n (i : ℤ) (i : ℤ)).toNat : ℤ)*2^(n-i))*4 := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    rw [show n+2-i = n-i+2 by omega, pow_add]
    ring
  rw [hs]
  simp [show n+2-(n+1)=1 by omega]
  ring

lemma closed (n : ℕ) (hn : 1 < n) :
    2*a n = -2 + (-2 : ℤ)^n + 2^(1+n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hsmall : n ≤ 3
    · interval_cases n <;> first | omega | decide
    obtain ⟨k, rfl⟩ : ∃ k, n=k+2 := ⟨n-2, by omega⟩
    rw [advance k (by omega), show 1+(k+2)=1+k+2 by omega, pow_add, pow_add (2 : ℤ)]
    linarith [ih k (by omega) (by omega)]

lemma recurrence (n : ℕ) (hn : 4 < n) :
    a n = a (n-1)+4*a (n-2)-4*a (n-3) := by
  have h1 := advance (n-2) (by omega)
  have h2 := advance (n-3) (by omega)
  rw [show n-2+2=n by omega] at h1
  rw [show n-3+2=n-1 by omega] at h2
  linarith

lemma axis_agrees (n : ℕ) (hn : 2 ≤ n) (x : ℤ) : state 641 n x x = state 641 n x 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hsmall : n < 4
    · by_cases hx : (3 : ℤ) < |x|
      · rw [outside _ _ _ _ (Or.inl (by omega)), outside _ _ _ _ (Or.inl (by omega))]
      · simp only [not_lt, abs_le] at hx
        obtain ⟨_, _⟩ := hx
        interval_cases n <;> interval_cases x <;> first | omega | decide
    · obtain ⟨k, rfl⟩ : ∃ k, n=k+2 := ⟨n-2, by omega⟩
      rw [cycle_at k (by omega)]
      exact ih k (by omega) (by omega)

lemma crossref (n : ℕ) (hn : 1 < n) : a n = axis641 n := by
  unfold a digits axis641
  exact Finset.sum_congr rfl fun i _ => by rw [axis_agrees n hn (i : ℤ)]

lemma gf : mk a * ((1 - X) * (1 - 2 * X) * (1 + 2 * X)) = 1 - 2 * X ^ 3 + 4 * X ^ 4 := by
  have hd : mk a * ((1 - X) * (1 - 2 * X) * (1 + 2 * X)) = (1 : ℤ) • (mk a * X ^ 0)
      + (-1 : ℤ) • (mk a * X ^ 1)
      + (-4 : ℤ) • (mk a * X ^ 2)
      + (4 : ℤ) • (mk a * X ^ 3) := by
    simp only [zsmul_eq_mul]; push_cast; ring
  have hp : (1 - 2 * X ^ 3 + 4 * X ^ 4 : PowerSeries ℤ) = (1 : ℤ) • (X ^ 0 : PowerSeries ℤ)
      + (-2 : ℤ) • (X ^ 3 : PowerSeries ℤ)
      + (4 : ℤ) • (X ^ 4 : PowerSeries ℤ) := by
    simp only [zsmul_eq_mul]; push_cast; ring
  rw [hd,hp]
  ext n
  simp only [map_add, map_zsmul, coeff_mul_X_pow', coeff_X_pow, coeff_mk]
  by_cases h : n ≤ 4
  · have h0 : a 0 = 1 := by decide
    have h1 : a 1 = 1 := by decide
    have h2 : a 2 = 5 := by decide
    have h3 : a 3 = 3 := by decide
    have h4 : a 4 = 23 := by decide
    interval_cases n <;> norm_num [zsmul_eq_mul, h0, h1, h2, h3, h4]
  · simp only [Nat.sub_zero, zsmul_eq_mul, if_neg (show n ≠ 0 by omega),
      if_neg (show n ≠ 3 by omega),
      if_neg (show n ≠ 4 by omega),
      if_pos (show 0 ≤ n by omega),
      if_pos (show 1 ≤ n by omega),
      if_pos (show 2 ≤ n by omega),
      if_pos (show 3 ≤ n by omega)]
    norm_num
    linarith only [recurrence n (by omega)]

end Diagonal641

open Diagonal641

theorem OMA.solution : type_of% @OMA.S_oeis_a290074.main := by
  refine ⟨gf, ?_, fun n hn _ => crossref n hn, ?_, fun n hn _ => crossref n hn, recurrence⟩
  · intro n hn he
    obtain ⟨k, rfl⟩ : ∃ k, n=2*k+2 := ⟨n/2-1, by omega⟩
    have hh := closed (2*k+2) hn
    rw [show 2*k+2-1=2*k+1 by omega]
    simp only [pow_add, pow_mul] at hh ⊢
    norm_num at hh ⊢
    linarith
  · intro n hn ho
    obtain ⟨k, rfl⟩ : ∃ k, n=2*k+3 := ⟨n/2-1, by omega⟩
    have hh := closed (2*k+3) hn
    rw [show 2*k+3-1=2*k+2 by omega]
    simp only [pow_add, pow_mul] at hh ⊢
    norm_num at hh ⊢
    linarith
