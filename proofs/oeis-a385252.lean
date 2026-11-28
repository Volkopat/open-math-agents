import OMAStatements.S_oeis_a385252

/-!
# A385252: exact recurrence for ternary words

A proof of R. J. Mathar's July 2025 recurrence in OEIS A385252, including
its exact starting index. The proof counts words by the number of zero
symbols, derives a two-step boundary correction, and eliminates it.

Source: https://oeis.org/A385252
Credit: @CubeJerry
-/

namespace OMA.S_oeis_a385252

/-- Sum of a function of the zero count over length-m words. -/
def hist (m : ℕ) (f : ℕ → ℤ) : ℤ := ∑ w : Fin m → Fin 3, f (zeros w)

lemma hist_succ (m : ℕ) (f : ℕ → ℤ) :
    hist (m + 1) f = 2 * hist m f + hist m (fun z => f (z + 1)) := by
  classical
  let E := Fin.consEquiv (fun _ : Fin (m + 1) => Fin 3)
  have h : hist (m + 1) f =
      ∑ v : Fin 3 × (Fin m → Fin 3), f (zeros (Fin.cons v.1 v.2)) := by
    exact (Fintype.sum_equiv E _ _ (fun _ => rfl)).symm
  rw [h, Fintype.sum_prod_type, Fin.sum_univ_three]
  have zc (c : Fin 3) (w : Fin m → Fin 3) :
      zeros (Fin.cons c w) = (if c = 0 then 1 else 0) + zeros w := by
    unfold zeros
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
  simp only [zc, if_true, if_false, show (1 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 0 by decide, zero_add, hist, Nat.add_comm 1]
  ring

def weight (m j : ℕ) : ℤ := hist m (fun z => if z = j then 1 else 0)
def cut (m t : ℕ) : ℤ := hist m (fun z => if z < t then 1 else 0)

lemma weight_zero (m : ℕ) : weight m 0 = 2 ^ m := by
  induction m with
  | zero => simp [weight, hist, zeros]
  | succ m ih =>
    rw [weight, hist_succ]
    change 2 * weight m 0 + _ = _
    simp [ih, hist, pow_succ, mul_comm]

lemma weight_step (m j : ℕ) :
    weight (m + 1) (j + 1) = 2 * weight m (j + 1) + weight m j := by
  simp [weight, hist_succ]

lemma weight_formula (m j : ℕ) :
    weight m j = (m.choose j : ℤ) * 2 ^ (m - j) := by
  induction m generalizing j with
  | zero => cases j <;> simp [weight, hist, zeros]
  | succ m ih =>
    cases j with
    | zero => simp [weight_zero]
    | succ j =>
      rw [weight_step, ih, ih, Nat.choose_succ_succ, Nat.cast_add, Nat.succ_sub_succ_eq_sub]
      by_cases hj : j < m
      · rw [show m - j = (m - (j + 1)) + 1 by omega, pow_succ]
        ring
      · rw [Nat.choose_eq_zero_of_lt (by omega : m < j + 1)]
        simp

lemma cut_step (m t : ℕ) : cut m (t + 1) = cut m t + weight m t := by
  unfold cut weight hist
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w _
  by_cases h : zeros w < t
  · simp [h, Nat.lt_succ_of_lt h, Nat.ne_of_lt h]
  · by_cases e : zeros w = t
    · simp [e]
    · simp [h, e, show ¬zeros w < t + 1 by omega]

lemma cut_succ (m t : ℕ) : cut (m + 1) (t + 1) = 2 * cut m (t + 1) + cut m t := by
  simp [cut, hist_succ]

lemma a_cut (n : ℕ) (hn : 0 < n) : a n + 4 ^ n = cut (2 * n) n := by
  have hfour : (4 : ℤ) ^ n = weight (2 * n) 0 := by rw [weight_zero, pow_mul]; norm_num
  rw [hfour]
  unfold a weight cut hist
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w _
  by_cases h : zeros w = 0
  · simp [h, hn]
  · simp [h, Nat.pos_of_ne_zero h]

lemma cut_pair (n : ℕ) :
    cut (2 * (n + 1) + 2) (n + 2) =
      9 * cut (2 * (n + 1)) (n + 1) +
      4 * weight (2 * (n + 1)) (n + 1) - weight (2 * (n + 1)) n := by
  let m := 2 * (n + 1)
  change cut (m + 1 + 1) (n + 1 + 1) = _
  rw [cut_succ, cut_succ m (n+1), cut_succ m n, cut_step m (n+1), cut_step m n]
  dsimp [m]
  ring

/-- Central boundary correction after appending two symbols. -/
def b (n : ℕ) : ℤ := 2 ^ n * (catalan n : ℤ)

lemma weight_central (n : ℕ) :
    weight (2 * n) n = ((n : ℤ) + 1) * b n := by
  have hc : ((n : ℤ) + 1) * (catalan n : ℤ) = (n.centralBinom : ℤ) := by
    exact_mod_cast succ_mul_catalan_eq_centralBinom n
  rw [weight_formula, show 2 * n - n = n by omega]
  unfold b
  change (n.centralBinom : ℤ) * 2 ^ n = _
  rw [← hc]
  ring

lemma weight_below (n : ℕ) :
    weight (2 * (n + 1)) n = 2 * ((n : ℤ) + 1) * b (n + 1) := by
  let m := 2 * (n + 1)
  have h := Nat.choose_succ_right_eq m n
  have hs : m - n = n + 2 := by dsimp [m]; omega
  rw [hs] at h
  have hz : (m.choose (n+1) : ℤ) * ((n : ℤ)+1) = (m.choose n : ℤ) * ((n : ℤ)+2) := by
    exact_mod_cast h
  have hc : ((n : ℤ)+2) * (catalan (n+1) : ℤ) = (m.choose (n+1) : ℤ) := by
    exact_mod_cast succ_mul_catalan_eq_centralBinom (n+1)
  rw [← hc] at hz
  have hch : (m.choose n : ℤ) = ((n : ℤ)+1) * (catalan (n+1) : ℤ) := by
    have hh : ((m.choose n : ℤ) - ((n : ℤ)+1) * (catalan (n+1) : ℤ)) *
        ((n : ℤ)+2) = 0 := by linear_combination -hz
    rcases mul_eq_zero.mp hh with h | h
    · linarith
    · omega
  rw [weight_formula, hs, hch, show n + 2 = (n+1)+1 by omega, pow_succ (2 : ℤ) (n+1)]
  unfold b
  ring

lemma b_step (n : ℕ) :
    ((n : ℤ) + 2) * b (n + 1) = 4 * (2 * (n : ℤ) + 1) * b n := by
  have hn := Nat.succ_mul_centralBinom_succ n
  rw [← succ_mul_catalan_eq_centralBinom, ← succ_mul_catalan_eq_centralBinom] at hn
  have hz : ((n : ℤ)+1) * (((n : ℤ)+2) * (catalan (n+1) : ℤ)) =
      2 * (2 * (n : ℤ)+1) * (((n : ℤ)+1) * (catalan n : ℤ)) := by exact_mod_cast hn
  have hf : (((n : ℤ)+2) * (catalan (n+1) : ℤ) -
      2 * (2 * (n : ℤ)+1) * (catalan n : ℤ)) * ((n : ℤ)+1) = 0 := by
    linear_combination hz
  have hcat := (mul_eq_zero.mp hf).resolve_right (by omega)
  simp only [b, pow_succ]
  linear_combination (2 * (2 : ℤ)^n) * hcat

lemma a_step (t : ℕ) (ht : 0 < t) :
    a (t + 1) = 9 * a t + 5 * 4 ^ t + (2 * (t : ℤ) + 4) * b t := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
  have hh := cut_pair n
  rw [weight_central, weight_below] at hh
  rw [← a_cut (n+1) (by omega),
    show 2 * (n+1) + 2 = 2 * (n+1+1) by omega,
    ← a_cut (n+1+1) (by omega)] at hh
  push_cast at hh ⊢
  rw [pow_succ (4 : ℤ) (n+1)] at hh
  change a (n+1+1) = 9*a (n+1) + 5*4^(n+1) + (2*((n:ℤ)+1)+4)*b (n+1)
  linear_combination hh

/-- A polynomial identity eliminating the two auxiliary sequences from five adjacent steps. -/
lemma eliminate {t a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ b₃ b₄ g : ℤ}
    (s₀ : a₁ = 9*a₀ + 5*g + (2*t+4)*b₀)
    (s₁ : a₂ = 9*a₁ + 5*(4*g) + (2*(t+1)+4)*b₁)
    (s₂ : a₃ = 9*a₂ + 5*(16*g) + (2*(t+2)+4)*b₂)
    (s₃ : a₄ = 9*a₃ + 5*(64*g) + (2*(t+3)+4)*b₃)
    (s₄ : a₅ = 9*a₄ + 5*(256*g) + (2*(t+4)+4)*b₄)
    (c₀ : (t+2)*b₁ = 4*(2*t+1)*b₀)
    (c₁ : (t+3)*b₂ = 4*(2*(t+1)+1)*b₁)
    (c₂ : (t+4)*b₃ = 4*(2*(t+2)+1)*b₂)
    (c₃ : (t+5)*b₄ = 4*(2*(t+3)+1)*b₃) :
    (t+5)*a₅ + (36-37*(t+5))*a₄ + 4*(131*(t+5)-245)*a₃ +
      16*(605-221*(t+5))*a₂ + 192*(59*(t+5)-213)*a₁ +
      6912*(9-2*(t+5))*a₀ = 0 := by
  linear_combination (1536*t+768)*s₀ - (1088*t+1664)*s₁ + (272*t+704)*s₂ -
    (28*t+104)*s₃ + (t+5)*s₄ - (384*t+768)*c₀ + (224*t+704)*c₁ -
    (40*t+176)*c₂ + (2*t+12)*c₃

theorem solution : ∀ n : ℕ, 6 ≤ n → residual n = 0 := by
  intro n hn
  obtain ⟨t, ht, rfl⟩ : ∃ t, 0 < t ∧ n = t + 5 := ⟨n-5, by omega, by omega⟩
  unfold residual
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_ofNat]
  rw [show t+5-1 = t+4 by omega, show t+5-2 = t+3 by omega,
    show t+5-3 = t+2 by omega, show t+5-4 = t+1 by omega]
  apply eliminate (t := (t : ℤ)) (g := (4 : ℤ) ^ t)
    (b₀ := b t) (b₁ := b (t+1)) (b₂ := b (t+2)) (b₃ := b (t+3)) (b₄ := b (t+4))
  · exact a_step t ht
  · convert a_step (t+1) (by omega) using 1
    push_cast
    ring_nf
  · convert a_step (t+2) (by omega) using 1
    push_cast
    ring_nf
  · convert a_step (t+3) (by omega) using 1
    push_cast
    ring_nf
  · convert a_step (t+4) (by omega) using 1
    push_cast
    ring_nf
  · exact b_step t
  · convert b_step (t+1) using 1 <;> push_cast <;> ring_nf
  · convert b_step (t+2) using 1 <;> push_cast <;> ring_nf
  · convert b_step (t+3) using 1 <;> push_cast <;> ring_nf

end OMA.S_oeis_a385252

theorem OMA.solution : type_of% @OMA.S_oeis_a385252.main :=
  OMA.S_oeis_a385252.solution
