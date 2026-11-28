import OMAStatements.S_oeis_a264596
import Mathlib

namespace OMA.A264596Proof

open OMA.S_oeis_a264596

/-! ### Binary words -/

theorem dig_odd (s : ℕ) : Nat.digits 2 (2 * s + 1) = 1 :: Nat.digits 2 s := by
  have h := Nat.digits_def' (b := 2) (by norm_num) (n := 2 * s + 1) (by omega)
  have h1 : (2 * s + 1) % 2 = 1 := by omega
  have h2 : (2 * s + 1) / 2 = s := by omega
  rw [h1, h2] at h
  exact h

theorem dig_even (s : ℕ) (hs : 0 < s) : Nat.digits 2 (2 * s) = 0 :: Nat.digits 2 s := by
  have h := Nat.digits_def' (b := 2) (by norm_num) (n := 2 * s) (by omega)
  have h1 : (2 * s) % 2 = 0 := by omega
  have h2 : (2 * s) / 2 = s := by omega
  rw [h1, h2] at h
  exact h

theorem lex_cons (a b : ℕ) (l1 l2 : List ℕ) :
    List.Lex (· < ·) (a :: l1) (b :: l2) ↔ a < b ∨ a = b ∧ List.Lex (· < ·) l1 l2 :=
  List.cons_lex_cons_iff

theorem lex_irr (l : List ℕ) : ¬ List.Lex (· < ·) l l :=
  List.lex_irrefl (fun x => Nat.lt_irrefl x) l

theorem lex_nil_pos (n : ℕ) (hn : 0 < n) : List.Lex (· < ·) [] (Nat.digits 2 n) := by
  rw [Nat.digits_def' (by norm_num : 1 < 2) hn]
  exact List.Lex.nil

theorem lex_zero_pos (n : ℕ) (hn : 0 < n) : List.Lex (· < ·) [0] (Nat.digits 2 n) := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · have hk : 0 < k := by omega
    rw [dig_even k hk]
    exact List.Lex.cons (lex_nil_pos k hk)
  · rw [dig_odd k]
    exact List.Lex.rel Nat.zero_lt_one

theorem binLSB_zero : binLSB 0 = [0] := by
  unfold binLSB
  exact if_pos rfl

theorem binLSB_pos (n : ℕ) (hn : 0 < n) : binLSB n = Nat.digits 2 n := by
  unfold binLSB
  exact if_neg (by omega)

theorem ite_eq_of_iff {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) :
    (if P then 1 else 0 : ℕ) = if Q then 1 else 0 := by
  by_cases hp : P
  · rw [if_pos hp, if_pos (h.mp hp)]
  · rw [if_neg hp, if_neg (fun hq => hp (h.mpr hq))]

/-! ### The count with `Nat.digits` words, and its recurrence -/

/-- `1` if the word of `t` is below `L`, else `0`. -/
def ind (L : List ℕ) (t : ℕ) : ℕ := if List.Lex (· < ·) (Nat.digits 2 t) L then 1 else 0

/-- The number of `t ≤ n` whose word `Nat.digits 2 t` is below that of `n`. -/
def bc (n : ℕ) : ℕ := ∑ t ∈ Finset.range (n + 1), ind (Nat.digits 2 n) t

theorem ind_self (n : ℕ) : ind (Nat.digits 2 n) n = 0 := by
  unfold ind
  exact if_neg (lex_irr _)

theorem ind_odd_zero (s h : ℕ) : ind (0 :: Nat.digits 2 h) (2 * s + 1) = 0 := by
  unfold ind
  rw [dig_odd s]
  apply if_neg
  intro hl
  rcases (lex_cons _ _ _ _).mp hl with h1 | ⟨h1, _⟩ <;> omega

theorem ind_odd_one (s h : ℕ) : ind (1 :: Nat.digits 2 h) (2 * s + 1) = ind (Nat.digits 2 h) s := by
  unfold ind
  rw [dig_odd s]
  apply ite_eq_of_iff
  rw [lex_cons]
  constructor
  · rintro (h1 | ⟨_, h1⟩)
    · omega
    · exact h1
  · intro h1
    exact Or.inr ⟨rfl, h1⟩

theorem ind_even_one (s h : ℕ) : ind (1 :: Nat.digits 2 h) (2 * s) = 1 := by
  unfold ind
  apply if_pos
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · rw [Nat.mul_zero, Nat.digits_zero]
    exact List.Lex.nil
  · rw [dig_even s hs]
    exact List.Lex.rel Nat.zero_lt_one

theorem ind_even_zero (s h : ℕ) (hh : 0 < h) :
    ind (0 :: Nat.digits 2 h) (2 * s) = ind (Nat.digits 2 h) s := by
  unfold ind
  apply ite_eq_of_iff
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · rw [Nat.mul_zero, Nat.digits_zero]
    exact ⟨fun _ => lex_nil_pos h hh, fun _ => List.Lex.nil⟩
  · rw [dig_even s hs, lex_cons]
    constructor
    · rintro (h1 | ⟨_, h1⟩)
      · omega
      · exact h1
    · intro h1
      exact Or.inr ⟨rfl, h1⟩

theorem sum_range_two_mul (g : ℕ → ℕ) (N : ℕ) :
    ∑ t ∈ Finset.range (2 * N), g t = ∑ s ∈ Finset.range N, (g (2 * s) + g (2 * s + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_range_succ g (2 * N + 1),
      Finset.sum_range_succ g (2 * N), ih,
      Finset.sum_range_succ (fun s => g (2 * s) + g (2 * s + 1)) N]
    omega

theorem bc_zero : bc 0 = 0 := by
  unfold bc
  rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, ind_self]

theorem bc_odd (h : ℕ) : bc (2 * h + 1) = h + 1 + bc h := by
  unfold bc
  rw [dig_odd h, show 2 * h + 1 + 1 = 2 * (h + 1) by ring, sum_range_two_mul]
  have h1 : ∀ s ∈ Finset.range (h + 1),
      ind (1 :: Nat.digits 2 h) (2 * s) + ind (1 :: Nat.digits 2 h) (2 * s + 1)
        = 1 + ind (Nat.digits 2 h) s := by
    intro s _
    rw [ind_even_one s h, ind_odd_one s h]
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    smul_eq_mul, mul_one]

theorem bc_even (h : ℕ) (hpos : 0 < h) : bc (2 * h) = bc h := by
  unfold bc
  rw [dig_even h hpos, Finset.sum_range_succ (ind (0 :: Nat.digits 2 h)) (2 * h),
    Finset.sum_range_succ (ind (Nat.digits 2 h)) h, ind_even_zero h h hpos, ind_self,
    sum_range_two_mul]
  have h1 : ∀ s ∈ Finset.range h,
      ind (0 :: Nat.digits 2 h) (2 * s) + ind (0 :: Nat.digits 2 h) (2 * s + 1)
        = ind (Nat.digits 2 h) s := by
    intro s _
    rw [ind_even_zero s h hpos, ind_odd_zero s h, add_zero]
  rw [Finset.sum_congr rfl h1]

theorem a_eq_bc (n : ℕ) : A264596 n = bc n := by
  unfold A264596 bc
  rw [Finset.card_filter]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Finset.sum_range_succ, Finset.sum_range_zero, Finset.sum_range_succ, Finset.sum_range_zero,
      if_neg (lex_irr _), ind_self]
  · apply Finset.sum_congr rfl
    intro m _
    unfold ind
    apply ite_eq_of_iff
    rw [binLSB_pos n hn]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [binLSB_zero, Nat.digits_zero]
      exact ⟨fun _ => lex_nil_pos n hn, fun _ => lex_zero_pos n hn⟩
    · rw [binLSB_pos m hm]

/-! ### The 2-adic valuation of A293290 -/

theorem pv_prod (s : Finset ℕ) (f : ℕ → ℕ) (hf : ∀ i ∈ s, 0 < f i) :
    padicValNat 2 (∏ i ∈ s, f i) = ∑ i ∈ s, padicValNat 2 (f i) := by
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _
    rw [Finset.prod_empty, Finset.sum_empty]
    exact padicValNat_one_right 2
  · intro a s ha ih hf
    have hfa : f a ≠ 0 := Nat.pos_iff_ne_zero.mp (hf a (Finset.mem_insert_self a s))
    have hrest : ∀ i ∈ s, 0 < f i := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hprod : ∏ i ∈ s, f i ≠ 0 := Nat.pos_iff_ne_zero.mp (Finset.prod_pos hrest)
    rw [Finset.prod_insert ha, Finset.sum_insert ha, padicValNat.mul (p := 2) hfa hprod, ih hrest]

theorem v2_odd_num (c : ℕ) : padicValNat 2 (2 * c + 1) = 0 :=
  padicValNat.eq_zero_of_not_dvd (by omega)

theorem v2_two_mul (c : ℕ) (hc : c ≠ 0) : padicValNat 2 (2 * c) = 1 + padicValNat 2 c := by
  rw [padicValNat.mul (p := 2) (by norm_num) hc, padicValNat_self]

theorem v2_four_mul (c : ℕ) (hc : c ≠ 0) : padicValNat 2 (4 * c) = 2 + padicValNat 2 c := by
  have h1 : 4 * c = 2 * (2 * c) := by ring
  have h2 := v2_two_mul (2 * c) (by omega)
  have h3 := v2_two_mul c hc
  rw [h1]
  omega

theorem v2_odd_odd (a b : ℕ) : padicValNat 2 ((2 * a + 1) ^ 2 + (2 * b + 1) ^ 2) = 1 := by
  have h1 : (2 * a + 1) ^ 2 + (2 * b + 1) ^ 2 = 2 * (2 * (a ^ 2 + a + b ^ 2 + b) + 1) := by ring
  have h2 := v2_two_mul (2 * (a ^ 2 + a + b ^ 2 + b) + 1) (by omega)
  have h3 := v2_odd_num (a ^ 2 + a + b ^ 2 + b)
  rw [h1]
  omega

theorem v2_odd_even (a b : ℕ) : padicValNat 2 ((2 * a + 1) ^ 2 + (2 * b) ^ 2) = 0 := by
  have h1 : (2 * a + 1) ^ 2 + (2 * b) ^ 2 = 2 * (2 * (a ^ 2 + a + b ^ 2)) + 1 := by ring
  rw [h1]
  exact v2_odd_num _

theorem v2_even_odd (a b : ℕ) : padicValNat 2 ((2 * a) ^ 2 + (2 * b + 1) ^ 2) = 0 := by
  have h1 : (2 * a) ^ 2 + (2 * b + 1) ^ 2 = 2 * (2 * (a ^ 2 + b ^ 2 + b)) + 1 := by ring
  rw [h1]
  exact v2_odd_num _

theorem v2_even_even (a b : ℕ) (hb : 0 < b) :
    padicValNat 2 ((2 * a) ^ 2 + (2 * b) ^ 2) = 2 + padicValNat 2 (a ^ 2 + b ^ 2) := by
  have h1 : (2 * a) ^ 2 + (2 * b) ^ 2 = 4 * (a ^ 2 + b ^ 2) := by ring
  have h2 : 0 < b ^ 2 := pow_pos hb 2
  rw [h1]
  exact v2_four_mul _ (by omega)

theorem sum_Icc_eq_range (f : ℕ → ℕ) (i : ℕ) :
    ∑ j ∈ Finset.Icc 1 i, f j = ∑ t ∈ Finset.range i, f (t + 1) := by
  induction i with
  | zero =>
    rw [Finset.Icc_eq_empty_of_lt (show (0 : ℕ) < 1 by norm_num), Finset.sum_empty,
      Finset.sum_range_zero]
  | succ i ih =>
    rw [Finset.sum_Icc_succ_top (a := 1) (b := i) (by omega) f, ih, Finset.sum_range_succ]

/-- Row sum: `R k = ∑_{1 ≤ j ≤ k} v2 (k ^ 2 + j ^ 2)`. -/
def R (k : ℕ) : ℕ := ∑ j ∈ Finset.Icc 1 k, padicValNat 2 (k ^ 2 + j ^ 2)

/-- `Vs n = ∑_{1 ≤ k ≤ n} R k`. -/
def Vs (n : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 n, R k

theorem R_odd (i : ℕ) : R (2 * i + 1) = i + 1 := by
  unfold R
  rw [Finset.sum_Icc_succ_top (a := 1) (b := 2 * i) (by omega), sum_Icc_eq_range, sum_range_two_mul]
  have h1 : ∀ s ∈ Finset.range i,
      padicValNat 2 ((2 * i + 1) ^ 2 + (2 * s + 1) ^ 2)
        + padicValNat 2 ((2 * i + 1) ^ 2 + (2 * s + 1 + 1) ^ 2) = 1 := by
    intro s _
    have e1 := v2_odd_odd i s
    have e2 := v2_odd_even i (s + 1)
    rw [show 2 * (s + 1) = 2 * s + 1 + 1 by ring] at e2
    omega
  rw [Finset.sum_congr rfl h1, v2_odd_odd i i, Finset.sum_const, Finset.card_range, smul_eq_mul,
    mul_one]

theorem R_even (i : ℕ) : R (2 * i) = 2 * i + R i := by
  have e1 : R (2 * i) = ∑ s ∈ Finset.range i,
      (padicValNat 2 ((2 * i) ^ 2 + (2 * s + 1) ^ 2)
        + padicValNat 2 ((2 * i) ^ 2 + (2 * s + 1 + 1) ^ 2)) := by
    unfold R
    rw [sum_Icc_eq_range, sum_range_two_mul]
  have e2 : R i = ∑ s ∈ Finset.range i, padicValNat 2 (i ^ 2 + (s + 1) ^ 2) := by
    unfold R
    rw [sum_Icc_eq_range]
  have h1 : ∀ s ∈ Finset.range i,
      padicValNat 2 ((2 * i) ^ 2 + (2 * s + 1) ^ 2)
        + padicValNat 2 ((2 * i) ^ 2 + (2 * s + 1 + 1) ^ 2)
        = 2 + padicValNat 2 (i ^ 2 + (s + 1) ^ 2) := by
    intro s _
    have f1 := v2_even_odd i s
    have f2 := v2_even_even i (s + 1) (by omega)
    rw [show 2 * (s + 1) = 2 * s + 1 + 1 by ring] at f2
    omega
  rw [e1, e2, Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    smul_eq_mul]
  ring

theorem Vs_zero : Vs 0 = 0 := by
  unfold Vs
  rw [Finset.Icc_eq_empty_of_lt (show (0 : ℕ) < 1 by norm_num), Finset.sum_empty]

theorem Vs_succ (n : ℕ) : Vs (n + 1) = Vs n + R (n + 1) := by
  unfold Vs
  exact Finset.sum_Icc_succ_top (a := 1) (b := n) (by omega) R

theorem pos_term (k j : ℕ) (hj : j ∈ Finset.Icc 1 k) : 0 < k ^ 2 + j ^ 2 := by
  have h1 := (Finset.mem_Icc.mp hj).1
  have h2 : 0 < j ^ 2 := pow_pos (by omega) 2
  omega

theorem V_eq (n : ℕ) : padicValNat 2 (A293290 n) = Vs n := by
  unfold A293290 Vs
  rw [pv_prod (Finset.Icc 1 n) (fun k => ∏ j ∈ Finset.Icc 1 k, (k ^ 2 + j ^ 2))
    (fun k _ => Finset.prod_pos (fun j hj => pos_term k j hj))]
  apply Finset.sum_congr rfl
  intro k _
  unfold R
  exact pv_prod (Finset.Icc 1 k) (fun j => k ^ 2 + j ^ 2) (fun j hj => pos_term k j hj)

theorem Vs_even (h : ℕ) : 2 * Vs (2 * h) = 3 * h * (h + 1) + 2 * Vs h := by
  induction h with
  | zero => simp [Vs_zero]
  | succ h ih =>
    have e1 : Vs (2 * (h + 1)) = Vs (2 * h) + R (2 * h + 1) + R (2 * (h + 1)) := by
      rw [show 2 * (h + 1) = 2 * h + 1 + 1 by ring, Vs_succ, Vs_succ]
    have e2 : Vs (h + 1) = Vs h + R (h + 1) := Vs_succ h
    rw [e1, e2, R_odd, R_even]
    linarith

/-! ### The identity -/

theorem key (n : ℕ) : 2 * (bc n + Vs n) = n * (n + 3) := by
  refine Nat.strong_induction_on n ?_
  intro n ih
  rcases Nat.even_or_odd' n with ⟨h, rfl | rfl⟩
  · rcases Nat.eq_zero_or_pos h with rfl | hpos
    · simp [bc_zero, Vs_zero]
    · have ih' := ih h (by omega)
      have hv := Vs_even h
      rw [bc_even h hpos]
      linarith
  · have ih' := ih h (by omega)
    have hv := Vs_even h
    rw [bc_odd h, Vs_succ, R_odd]
    linarith

end OMA.A264596Proof

open OMA.S_oeis_a264596

theorem OMA.solution : type_of% @OMA.S_oeis_a264596.main := by
  intro n _
  have hk := OMA.A264596Proof.key n
  rw [← OMA.A264596Proof.a_eq_bc, ← OMA.A264596Proof.V_eq] at hk
  have hz : (2 : ℤ) * ((A264596 n : ℤ) + (A007814 (A293290 n) : ℤ)) = (n : ℤ) * ((n : ℤ) + 3) := by
    unfold A007814
    exact_mod_cast hk
  rw [← hz, Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0)]
  ring
