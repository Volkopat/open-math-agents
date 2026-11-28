import OMAStatements.S_oeis_a288671

namespace OMA.S_oeis_a288671

open Filter Topology





/-! ### One pass -/

/-- A word is closed when the pass over it followed by any word is the pass over it followed by
the pass over that word. -/
def Closed (u : List ℕ) : Prop := ∀ y, step (u ++ y) = step u ++ step y

lemma closed_append {u v : List ℕ} (hu : Closed u) (hv : Closed v) : Closed (u ++ v) := by
  intro y
  rw [List.append_assoc, hu (v ++ y), hv y, hu v, List.append_assoc]

lemma closed_zero : Closed [0, 0] := fun _ => rfl

lemma closed_one : Closed [0, 1, 1, 0] := fun _ => rfl

lemma closed_two : Closed [0, 1, 0, 0, 0] := fun _ => rfl

/-- Iterate n + 3 is iterate n twice followed by iterate n + 1, and every iterate is closed. -/
lemma iter_rec (n : ℕ) : Closed (iter n) ∧ Closed (iter (n + 1)) ∧ Closed (iter (n + 2)) ∧
    iter (n + 3) = iter n ++ iter n ++ iter (n + 1) := by
  induction n with
  | zero => exact ⟨closed_zero, closed_one, closed_two, rfl⟩
  | succ n ih =>
    obtain ⟨h0, h1, h2, h3⟩ := ih
    have h3' : Closed (iter (n + 3)) := by
      rw [h3]
      exact closed_append (closed_append h0 h0) h1
    refine ⟨h1, h2, h3', ?_⟩
    show step (iter (n + 3)) = step (iter n) ++ step (iter n) ++ step (iter (n + 1))
    rw [h3, closed_append h0 h0 (iter (n + 1)), h0 (iter n)]

lemma iter_three (n : ℕ) : iter (n + 3) = iter n ++ iter n ++ iter (n + 1) := (iter_rec n).2.2.2

lemma iter_prefix_three (n : ℕ) : iter n <+: iter (n + 3) := by
  rw [iter_three, List.append_assoc]
  exact List.prefix_append _ _

lemma iter_length_rec (n : ℕ) :
    (iter (n + 3)).length = 2 * (iter n).length + (iter (n + 1)).length := by
  rw [iter_three, List.length_append, List.length_append]
  ring

lemma iter_length_lin (n : ℕ) : n + 2 ≤ (iter n).length ∧ n + 3 ≤ (iter (n + 1)).length ∧
    n + 4 ≤ (iter (n + 2)).length := by
  induction n with
  | zero => decide
  | succ n ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    refine ⟨h1, h2, ?_⟩
    rw [show n + 1 + 2 = n + 3 by ring, iter_length_rec]
    omega

lemma iter_length (n : ℕ) : n + 2 ≤ (iter n).length := (iter_length_lin n).1

lemma iter_letters (n : ℕ) : (∀ x ∈ iter n, x ≤ 1) ∧ (∀ x ∈ iter (n + 1), x ≤ 1) ∧
    (∀ x ∈ iter (n + 2), x ≤ 1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    refine ⟨h1, h2, ?_⟩
    rw [show n + 1 + 2 = n + 3 by ring, iter_three]
    intro x hx
    simp only [List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · exact h0 x hx
    · exact h0 x hx
    · exact h1 x hx

lemma getD_prefix {l₁ l₂ : List ℕ} (h : l₁ <+: l₂) {i : ℕ} (hi : i < l₁.length) :
    l₁.getD i 0 = l₂.getD i 0 := by
  obtain ⟨s, rfl⟩ := h
  rw [List.getD_append _ _ _ _ hi]

/-! ### The limiting word -/

/-- The residue mod 3 of the iterates whose limit is W. -/
def res : ℕ := 1

/-- V k: iterate 3k + res. -/
def V (k : ℕ) : List ℕ := iter (3 * k + res)

lemma V_prefix_succ (k : ℕ) : V k <+: V (k + 1) := by
  unfold V
  rw [show 3 * (k + 1) + res = 3 * k + res + 3 by ring]
  exact iter_prefix_three _

lemma V_prefix {k k' : ℕ} (h : k ≤ k') : V k <+: V k' := by
  induction k', h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ k' _ ih => exact ih.trans (V_prefix_succ k')

lemma V_length (k : ℕ) : k + 2 ≤ (V k).length := by
  unfold V
  have := iter_length (3 * k + res)
  omega

lemma W_eq (k i : ℕ) (hi : i < (V k).length) : W i = (V k).getD i 0 := by
  have hW : W i = (V (i + 1)).getD i 0 := rfl
  have hi' : i < (V (i + 1)).length := by have := V_length (i + 1); omega
  rw [hW]
  rcases le_total (i + 1) k with h | h
  · exact getD_prefix (V_prefix h) hi'
  · exact (getD_prefix (V_prefix h) hi).symm

/-! ### The real root -/

lemma lam_exists : ∃ x : ℝ, 1.5213 ≤ x ∧ x ≤ 1.5214 ∧ x ^ 3 - x - 2 = 0 := by
  have hc : ContinuousOn (fun x : ℝ => x ^ 3 - x - 2) (Set.Icc 1.5213 1.5214) := by
    fun_prop
  have h := intermediate_value_Icc (show (1.5213 : ℝ) ≤ 1.5214 by norm_num) hc
  have h0 : (0 : ℝ) ∈ Set.Icc ((fun x : ℝ => x ^ 3 - x - 2) 1.5213)
      ((fun x : ℝ => x ^ 3 - x - 2) 1.5214) := by
    constructor <;> norm_num
  obtain ⟨x, ⟨hx1, hx2⟩, hx⟩ := h h0
  exact ⟨x, hx1, hx2, hx⟩

/-- The real root of x^3 - x - 2, 1.52137..., the growth rate of the iterates. -/
noncomputable def lam : ℝ := Classical.choose lam_exists

lemma lam_spec : 1.5213 ≤ lam ∧ lam ≤ 1.5214 ∧ lam ^ 3 - lam - 2 = 0 :=
  Classical.choose_spec lam_exists

/-- The limiting number of letters 0 per letter 1. -/
noncomputable def cc : ℝ := (6 * lam ^ 2 + 10 * lam + 2) / 13

lemma cc_bounds : 2.3922 ≤ cc ∧ cc ≤ 2.3925 := by
  obtain ⟨h1, h2, -⟩ := lam_spec
  unfold cc
  constructor <;> nlinarith

/-! ### The deviation of the iterates -/

/-- For a word, the number of letters 0 minus c times the number of letters 1. -/
noncomputable def gL (L : List ℕ) : ℝ := (L.count 0 : ℝ) - cc * (L.count 1 : ℝ)

lemma gL_append (u v : List ℕ) : gL (u ++ v) = gL u + gL v := by
  simp only [gL, List.count_append]
  push_cast
  ring

/-- d n: the deviation of iterate n. -/
noncomputable def d (n : ℕ) : ℝ := gL (iter n)

lemma d_rec3 (n : ℕ) : d (n + 3) = 2 * d n + d (n + 1) := by
  unfold d
  rw [iter_three, gL_append, gL_append]
  ring

lemma d_zero : d 0 = 2 := by
  have h0 : (iter 0).count 0 = 2 := by decide
  have h1 : (iter 0).count 1 = 0 := by decide
  unfold d gL
  rw [h0, h1]
  push_cast <;> ring

lemma d_one : d 1 = 2 - 2 * cc := by
  have h0 : (iter 1).count 0 = 2 := by decide
  have h1 : (iter 1).count 1 = 2 := by decide
  unfold d gL
  rw [h0, h1]
  push_cast <;> ring

lemma d_two : d 2 = 4 - cc := by
  have h0 : (iter 2).count 0 = 4 := by decide
  have h1 : (iter 2).count 1 = 1 := by decide
  unfold d gL
  rw [h0, h1]
  push_cast <;> ring

/-- The deviation follows the recurrence of the two complex roots. -/
lemma d_rec2 (n : ℕ) : d (n + 2) = -lam * d (n + 1) - (lam ^ 2 - 1) * d n := by
  obtain ⟨-, -, hp⟩ := lam_spec
  induction n with
  | zero =>
    show d 2 = -lam * d 1 - (lam ^ 2 - 1) * d 0
    rw [d_two, d_one, d_zero]
    unfold cc
    linear_combination (-12 / 13 : ℝ) * hp
  | succ n ih =>
    have h3 := d_rec3 n
    show d (n + 3) = -lam * d (n + 2) - (lam ^ 2 - 1) * d (n + 1)
    linear_combination h3 + lam * ih - d n * hp

/-! ### The quadratic form -/

/-- The quadratic form along the deviations. -/
noncomputable def E (n : ℕ) : ℝ :=
  d (n + 1) ^ 2 + lam * d (n + 1) * d n + (lam ^ 2 - 1) * d n ^ 2

lemma E_succ (n : ℕ) : E (n + 1) = (lam ^ 2 - 1) * E n := by
  unfold E
  rw [show n + 1 + 1 = n + 2 from rfl, d_rec2 n]
  ring

/-- The form is positive definite: it bounds the square of its second argument. -/
lemma E_ge (n : ℕ) : 0.735 * d n ^ 2 ≤ E n := by
  obtain ⟨hl1, hl2, -⟩ := lam_spec
  unfold E
  have h : d (n + 1) ^ 2 + lam * d (n + 1) * d n + (lam ^ 2 - 1) * d n ^ 2 =
      (d (n + 1) + lam / 2 * d n) ^ 2 + (3 / 4 * lam ^ 2 - 1) * d n ^ 2 := by ring
  rw [h]
  have h2 : 0.735 ≤ 3 / 4 * lam ^ 2 - 1 := by nlinarith
  have h3 : 0 ≤ d n ^ 2 := sq_nonneg _
  nlinarith [sq_nonneg (d (n + 1) + lam / 2 * d n)]

lemma E_nonneg (n : ℕ) : 0 ≤ E n := by
  have := E_ge n
  have h3 : 0 ≤ d n ^ 2 := sq_nonneg _
  linarith

lemma E_zero : E 0 ≤ 4.55 := by
  obtain ⟨hl1, hl2, -⟩ := lam_spec
  obtain ⟨hc1, hc2⟩ := cc_bounds
  unfold E
  rw [show (0 : ℕ) + 1 = 1 from rfl, d_one, d_zero]
  nlinarith [mul_nonneg (sub_nonneg.2 hl1) (sub_nonneg.2 hc1),
    mul_nonneg (sub_nonneg.2 hc1) (sub_nonneg.2 hc2),
    mul_nonneg (sub_nonneg.2 hl1) (sub_nonneg.2 hl2)]

lemma E_le (n : ℕ) : E n ≤ 4.55 * 1.3225 ^ n := by
  obtain ⟨hl1, hl2, -⟩ := lam_spec
  induction n with
  | zero => simpa using E_zero
  | succ n ih =>
    rw [E_succ n, pow_succ (1.3225 : ℝ) n]
    have h0 := E_nonneg n
    have hq : lam ^ 2 - 1 ≤ 1.3225 := by nlinarith
    have h1 := mul_le_mul_of_nonneg_right hq h0
    linarith

lemma d_bound (n : ℕ) : |d n| ≤ 2.5 * 1.15 ^ n := by
  apply abs_le_of_sq_le_sq _ (by positivity)
  have h1 := E_ge n
  have h2 := E_le n
  have e : (2.5 * (1.15 : ℝ) ^ n) ^ 2 = 6.25 * 1.3225 ^ n := by
    rw [mul_pow, ← pow_mul, mul_comm n 2, pow_mul]
    norm_num
  rw [e]
  have hp : 0 ≤ (1.3225 : ℝ) ^ n := by positivity
  linarith

/-! ### Prefixes of the iterates -/

lemma gL_take_le (w : List ℕ) (N : ℕ) : |gL (w.take N)| ≤ w.count 0 + cc * w.count 1 := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  have hz : (w.take N).count 0 ≤ w.count 0 := List.Sublist.count_le _ (List.take_sublist _ _)
  have ho : (w.take N).count 1 ≤ w.count 1 := List.Sublist.count_le _ (List.take_sublist _ _)
  have hz' : ((w.take N).count 0 : ℝ) ≤ w.count 0 := by exact_mod_cast hz
  have ho' : ((w.take N).count 1 : ℝ) ≤ w.count 1 := by exact_mod_cast ho
  have hz0 : (0 : ℝ) ≤ (w.take N).count 0 := Nat.cast_nonneg _
  have ho0 : (0 : ℝ) ≤ (w.take N).count 1 := Nat.cast_nonneg _
  unfold gL
  rw [abs_le]
  constructor <;> nlinarith

/-- The prefixes of iterate n + 3 from those of iterates n and n + 1. -/
lemma prefix_step (n : ℕ) (h0 : ∀ N, |gL ((iter n).take N)| ≤ 14 * 1.15 ^ n)
    (h1 : ∀ N, |gL ((iter (n + 1)).take N)| ≤ 14 * 1.15 ^ (n + 1)) (N : ℕ) :
    |gL ((iter (n + 3)).take N)| ≤ 14 * 1.15 ^ (n + 3) := by
  have hd := d_bound n
  unfold d at hd
  have hp : 0 ≤ (1.15 : ℝ) ^ n := by positivity
  have e3 : (1.15 : ℝ) ^ (n + 3) = 1.15 ^ n * 1.520875 := by
    rw [pow_add]
    norm_num
  have e1 : (1.15 : ℝ) ^ (n + 1) = 1.15 ^ n * 1.15 := pow_succ _ _
  rw [e3, iter_three, List.append_assoc]
  rcases le_or_gt N (iter n).length with h | h
  · rw [List.take_append_of_le_length h]
    have := h0 N
    linarith
  · rw [List.take_append, List.take_of_length_le h.le, gL_append]
    rcases le_or_gt (N - (iter n).length) (iter n).length with h' | h'
    · rw [List.take_append_of_le_length h']
      have h2 := h0 (N - (iter n).length)
      have h3 := abs_add_le (gL (iter n)) (gL ((iter n).take (N - (iter n).length)))
      linarith
    · rw [List.take_append, List.take_of_length_le h'.le, gL_append]
      have h2 := h1 (N - (iter n).length - (iter n).length)
      rw [e1] at h2
      have h3 := abs_add_le (gL (iter n))
        (gL (iter n) + gL ((iter (n + 1)).take (N - (iter n).length - (iter n).length)))
      have h4 := abs_add_le (gL (iter n))
        (gL ((iter (n + 1)).take (N - (iter n).length - (iter n).length)))
      linarith

/-- The deviation of every prefix of iterate n is at most 14 * 1.15^n. -/
lemma prefix_bound (n : ℕ) : (∀ N, |gL ((iter n).take N)| ≤ 14 * 1.15 ^ n) ∧
    (∀ N, |gL ((iter (n + 1)).take N)| ≤ 14 * 1.15 ^ (n + 1)) ∧
    (∀ N, |gL ((iter (n + 2)).take N)| ≤ 14 * 1.15 ^ (n + 2)) := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  induction n with
  | zero =>
    refine ⟨fun N => ?_, fun N => ?_, fun N => ?_⟩
    · show |gL ((iter 0).take N)| ≤ 14 * 1.15 ^ 0
      have h := gL_take_le (iter 0) N
      have e0 : (iter 0).count 0 = 2 := by decide
      have e1 : (iter 0).count 1 = 0 := by decide
      rw [e0, e1] at h
      norm_num at h ⊢
      linarith
    · show |gL ((iter 1).take N)| ≤ 14 * 1.15 ^ 1
      have h := gL_take_le (iter 1) N
      have e0 : (iter 1).count 0 = 2 := by decide
      have e1 : (iter 1).count 1 = 2 := by decide
      rw [e0, e1] at h
      norm_num at h ⊢
      linarith
    · show |gL ((iter 2).take N)| ≤ 14 * 1.15 ^ 2
      have h := gL_take_le (iter 2) N
      have e0 : (iter 2).count 0 = 4 := by decide
      have e1 : (iter 2).count 1 = 1 := by decide
      rw [e0, e1] at h
      norm_num at h ⊢
      linarith
  | succ n ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    refine ⟨h1, h2, fun N => ?_⟩
    rw [show n + 1 + 2 = n + 3 by ring]
    exact prefix_step n h0 h1 N

/-! ### The length of the iterates -/

lemma length_ge (n : ℕ) : 2 * lam ^ n ≤ ((iter n).length : ℝ) ∧
    2 * lam ^ (n + 1) ≤ ((iter (n + 1)).length : ℝ) ∧
    2 * lam ^ (n + 2) ≤ ((iter (n + 2)).length : ℝ) := by
  obtain ⟨hl1, hl2, hp⟩ := lam_spec
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · show 2 * lam ^ 0 ≤ ((iter 0).length : ℝ)
      rw [show (iter 0).length = 2 by decide]
      norm_num
    · show 2 * lam ^ 1 ≤ ((iter 1).length : ℝ)
      rw [show (iter 1).length = 4 by decide]
      norm_num <;> linarith
    · show 2 * lam ^ 2 ≤ ((iter 2).length : ℝ)
      rw [show (iter 2).length = 5 by decide]
      norm_num <;> nlinarith
  | succ n ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    refine ⟨h1, h2, ?_⟩
    show 2 * lam ^ (n + 3) ≤ ((iter (n + 3)).length : ℝ)
    rw [iter_length_rec]
    push_cast
    have e3 : lam ^ (n + 3) = lam ^ n * (lam + 2) := by
      rw [pow_add]
      congr 1
      linarith
    have e1 : lam ^ (n + 1) = lam ^ n * lam := pow_succ _ _
    rw [e3]
    rw [e1] at h1
    linarith

/-! ### Counting along the limiting word -/

lemma W_le (i : ℕ) : W i ≤ 1 := by
  have hi : i < (V (i + 1)).length := by have := V_length (i + 1); omega
  rw [W_eq (i + 1) i hi, List.getD_eq_getElem _ _ hi]
  exact (iter_letters _).1 _ (List.getElem_mem hi)

/-- Z(N): the number of letters 0 among the first N letters of W. -/
noncomputable def Z (N : ℕ) : ℕ := Nat.count (fun i => W i = 0) N

/-- O(N): the number of letters 1 among the first N letters of W. -/
noncomputable def O (N : ℕ) : ℕ := Nat.count (fun i => W i = 1) N

lemma Z_succ (N : ℕ) : Z (N + 1) = Z N + if W N = 0 then 1 else 0 := Nat.count_succ _ _

lemma O_succ (N : ℕ) : O (N + 1) = O N + if W N = 1 then 1 else 0 := Nat.count_succ _ _

lemma counts_eq (k N : ℕ) (hN : N ≤ (V k).length) :
    Z N = ((V k).take N).count 0 ∧ O N = ((V k).take N).count 1 := by
  induction N with
  | zero => simp [Z, O]
  | succ N ih =>
    have hN' : N < (V k).length := by omega
    have hW : W N = (V k)[N] := by rw [W_eq k N hN', List.getD_eq_getElem _ _ hN']
    obtain ⟨h1, h2⟩ := ih (by omega)
    rw [Z_succ, O_succ, h1, h2, List.take_add_one, List.getElem?_eq_getElem hN',
      List.count_append, List.count_append, hW]
    constructor <;> simp [List.count_singleton]

/-- D(N) = Z(N) - c O(N) is the deviation over the first N letters of W. -/
noncomputable def D (N : ℕ) : ℝ := (Z N : ℝ) - cc * (O N : ℝ)

lemma D_eq (k N : ℕ) (hN : N ≤ (V k).length) : D N = gL ((V k).take N) := by
  obtain ⟨h1, h2⟩ := counts_eq k N hN
  simp [D, gL, h1, h2]

lemma O_add_Z (N : ℕ) : O N + Z N = N := by
  induction N with
  | zero => simp [O, Z]
  | succ N ih =>
    rw [O_succ, Z_succ]
    have := W_le N
    split_ifs <;> omega

lemma pow_bound (J : ℕ) (hJ : 15 ≤ J) : 70 * 1.15 ^ (J + 3) < 2 * lam ^ J := by
  obtain ⟨hl1, hl2, -⟩ := lam_spec
  induction J, hJ using Nat.le_induction with
  | base =>
    have : (1.5213 : ℝ) ^ 15 ≤ lam ^ 15 := pow_le_pow_left₀ (by norm_num) hl1 15
    norm_num at this ⊢
    linarith
  | succ J hJ ih =>
    rw [pow_succ lam J, show J + 1 + 3 = J + 3 + 1 by ring, pow_succ (1.15 : ℝ) (J + 3)]
    have hp : 0 ≤ lam ^ J := by positivity
    have h := mul_le_mul_of_nonneg_left (show (1.15 : ℝ) ≤ lam by linarith) hp
    linarith

lemma V5_length : (V 5).length = 1897 := by decide +kernel

/-- For N > 1897 there is a level J >= 15 with 2 lam^J < N and |D(N)| <= 14 * 1.15^(J + 3). -/
lemma level (N : ℕ) (hN : 1897 < N) :
    ∃ J, 15 ≤ J ∧ 2 * lam ^ J < (N : ℝ) ∧ |D N| ≤ 14 * 1.15 ^ (J + 3) := by
  have hex : ∃ k, N ≤ (V k).length := ⟨N, by have := V_length N; omega⟩
  classical
  have hk : N ≤ (V (Nat.find hex)).length := Nat.find_spec hex
  have h5 := V5_length
  have hk6 : 6 ≤ Nat.find hex := by
    by_contra h
    have := (V_prefix (show Nat.find hex ≤ 5 by omega)).length_le
    omega
  have hmin : (V (Nat.find hex - 1)).length < N := by
    have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    omega
  refine ⟨3 * (Nat.find hex - 1) + res, by omega, ?_, ?_⟩
  · have hl := (length_ge (3 * (Nat.find hex - 1) + res)).1
    have : ((V (Nat.find hex - 1)).length : ℝ) < N := by exact_mod_cast hmin
    exact lt_of_le_of_lt hl this
  · rw [D_eq (Nat.find hex) N hk]
    have h3 : 3 * Nat.find hex + res = 3 * (Nat.find hex - 1) + res + 3 := by omega
    have e : V (Nat.find hex) = iter (3 * (Nat.find hex - 1) + res + 3) := by
      rw [← h3]
      rfl
    rw [e]
    exact (prefix_bound _).1 N

/-- Over every prefix of W longer than 1897 letters, |D| < N / 5. -/
lemma D_small (N : ℕ) (hN : 1897 < N) : |D N| < (N : ℝ) / 5 := by
  obtain ⟨J, hJ, hNr, hD⟩ := level N hN
  have hp := pow_bound J hJ
  linarith

/-- D(N)^2 <= 40000 N for every N >= 1. -/
lemma D_sq (N : ℕ) (hN : 1 ≤ N) : D N ^ 2 ≤ 40000 * N := by
  obtain ⟨hl1, hl2, -⟩ := lam_spec
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rcases le_or_gt N 1897 with h | h
  · have h5 := V5_length
    rw [D_eq 5 N (by omega)]
    have hb : |gL ((V 5).take N)| ≤ 14 * 1.15 ^ (3 * 5 + res) := (prefix_bound _).1 N
    have hres : res ≤ 2 := by decide
    have hpow : (1.15 : ℝ) ^ (3 * 5 + res) ≤ 1.15 ^ 17 :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have h1 : |gL ((V 5).take N)| ≤ 151 := by
      have : (14 : ℝ) * 1.15 ^ 17 ≤ 151 := by norm_num
      linarith
    have h2 : gL ((V 5).take N) ^ 2 ≤ 151 ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    clear hb h1 hpow h5
    generalize gL ((V 5).take N) = x at h2 ⊢
    nlinarith
  · obtain ⟨J, hJ, hNr, hD⟩ := level N h
    have h1 : D N ^ 2 ≤ (14 * 1.15 ^ (J + 3)) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hD 2
    have e : ((1.15 : ℝ) ^ (J + 3)) ^ 2 = 1.3225 ^ J * 1.3225 ^ 3 := by
      rw [← pow_mul, mul_comm (J + 3) 2, pow_mul, pow_add]
      norm_num
    rw [mul_pow, e] at h1
    have h2 : (1.3225 : ℝ) ^ J ≤ lam ^ J := pow_le_pow_left₀ (by norm_num) (by linarith) J
    have hp : 0 ≤ (1.3225 : ℝ) ^ J := by positivity
    clear hD
    nlinarith

/-! ### The positions of 0 -/

/-- The limit, (1 + c)/c = 1.41798... -/
noncomputable def m0 : ℝ := (1 + cc) / cc

lemma m0_bounds : 1.4179 ≤ m0 ∧ m0 ≤ 1.4181 := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  have hc : 0 < cc := by linarith
  unfold m0
  constructor
  · rw [le_div_iff₀ hc]
    linarith
  · rw [div_le_iff₀ hc]
    linarith

lemma zeros_infinite : (setOf (fun i => W i = 0)).Infinite := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  have hconst : ∀ j, Z (B + 1 + j) = Z (B + 1) := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      have hno : ¬ W (B + 1 + j) = 0 := fun h => by
        have := hB h
        omega
      rw [show B + 1 + (j + 1) = B + 1 + j + 1 by ring, Z_succ, if_neg hno, ih, add_zero]
  have h := D_small (B + 1 + (4 * Z (B + 1) + 1900)) (by omega)
  have hs := O_add_Z (B + 1 + (4 * Z (B + 1) + 1900))
  rw [hconst] at hs
  unfold D at h
  rw [hconst, abs_lt] at h
  obtain ⟨h1, -⟩ := h
  have hO : (O (B + 1 + (4 * Z (B + 1) + 1900)) : ℝ) =
      ((B + 1 + (4 * Z (B + 1) + 1900) : ℕ) : ℝ) - Z (B + 1) := by
    have : (O (B + 1 + (4 * Z (B + 1) + 1900)) : ℝ) + Z (B + 1) =
        ((B + 1 + (4 * Z (B + 1) + 1900) : ℕ) : ℝ) := by exact_mod_cast hs
    linarith
  rw [hO] at h1
  generalize hz : (Z (B + 1) : ℝ) = z at h1
  have hz0 : 0 ≤ z := by rw [← hz]; exact Nat.cast_nonneg _
  have hz' : ((B + 1 + (4 * Z (B + 1) + 1900) : ℕ) : ℝ) = (B : ℝ) + 1 + (4 * z + 1900) := by
    rw [← hz]; push_cast; ring
  rw [hz'] at h1
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  have hP := mul_le_mul_of_nonneg_right hc1 hz0
  have hQ := mul_le_mul_of_nonneg_right hc1 hB0
  clear hconst hs hO hz hz' hB
  nlinarith [hP, hQ]

lemma a_spec (n : ℕ) (hn : 1 ≤ n) : Z (a n) = n ∧ O (a n) = a n - n := by
  have hinf := zeros_infinite
  have hZp : Z (Nat.nth (fun i => W i = 0) (n - 1)) = n - 1 :=
    Nat.count_nth_of_infinite hinf (n - 1)
  have hWp : W (Nat.nth (fun i => W i = 0) (n - 1)) = 0 := Nat.nth_mem_of_infinite hinf (n - 1)
  have hZ1 : Z (a n) = n := by
    unfold a
    rw [Z_succ, if_pos hWp, hZp]
    omega
  refine ⟨hZ1, ?_⟩
  have := O_add_Z (a n)
  omega

/-- At the n-th 0, m n - a(n) = D/c. -/
lemma a_dev (n : ℕ) (hn : 1 ≤ n) : m0 * n - a n = D (a n) / cc := by
  obtain ⟨hc1, -⟩ := cc_bounds
  have hc : cc ≠ 0 := by linarith
  obtain ⟨hZ, hO⟩ := a_spec n hn
  have hle : n ≤ a n := by have := O_add_Z (a n); omega
  unfold D m0
  rw [hZ, hO]
  push_cast [hle]
  field_simp
  ring

/-- A linear scan of a word, checking 100 (t + 1) < 241 Z(t + 1) at each letter 0. -/
def chk : List ℕ → ℕ → ℕ → Bool
  | [], _, _ => true
  | x :: l, t, z =>
    if x = 0 then decide (100 * (t + 1) < 241 * (z + 1)) && chk l (t + 1) (z + 1)
    else chk l (t + 1) z

lemma chk_spec : ∀ (L : List ℕ) (t z : ℕ), chk L t z = true →
    ∀ i < L.length, L.getD i 0 = 0 →
      100 * (t + i + 1) < 241 * (z + (L.take (i + 1)).count 0) := by
  intro L
  induction L with
  | nil =>
    intro t z _ i hi
    simp at hi
  | cons x l ih =>
    intro t z h i hi hx
    by_cases h0 : x = 0
    · subst h0
      have h' : 100 * (t + 1) < 241 * (z + 1) ∧ chk l (t + 1) (z + 1) = true := by
        simpa [chk] using h
      rcases i with _ | i
      · simpa using h'.1
      · have := ih (t + 1) (z + 1) h'.2 i (by simp at hi; omega) (by simpa using hx)
        have e : ((0 :: l).take (i + 1 + 1)).count 0 = (l.take (i + 1)).count 0 + 1 := by
          simp [List.take_succ_cons]
        rw [e]
        omega
    · have h' : chk l (t + 1) z = true := by simpa [chk, h0] using h
      rcases i with _ | i
      · simp at hx
        exact absurd hx h0
      · have := ih (t + 1) z h' i (by simp at hi; omega) (by simpa using hx)
        have e : ((x :: l).take (i + 1 + 1)).count 0 = (l.take (i + 1)).count 0 := by
          simp [List.take_succ_cons, h0]
        rw [e]
        omega

lemma chk_word : chk (V 5) 0 0 = true := by decide +kernel

lemma bound_small (n : ℕ) (hn : 1 ≤ n) (ha : a n ≤ 1897) :
    -1 < m0 - (a n : ℝ) / n ∧ m0 - (a n : ℝ) / n < 1 := by
  obtain ⟨hm1, hm2⟩ := m0_bounds
  obtain ⟨hZ, hO⟩ := a_spec n hn
  have hinf := zeros_infinite
  have hWp : W (Nat.nth (fun i => W i = 0) (n - 1)) = 0 := Nat.nth_mem_of_infinite hinf (n - 1)
  have ha' : a n = Nat.nth (fun i => W i = 0) (n - 1) + 1 := rfl
  set t := Nat.nth (fun i => W i = 0) (n - 1) with ht
  have hlen := V5_length
  have hW : (V 5).getD t 0 = 0 := by rw [← W_eq 5 t (by omega)]; exact hWp
  have hc := chk_spec (V 5) 0 0 chk_word t (by omega) hW
  have hZ' : ((V 5).take (t + 1)).count 0 = n := by
    rw [← (counts_eq 5 (t + 1) (by omega)).1, ← ha', hZ]
  rw [hZ'] at hc
  simp only [zero_add] at hc
  have hle : n ≤ a n := by have := O_add_Z (a n); omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hc' : (100 : ℝ) * (a n) < 241 * n := by
    rw [ha']
    exact_mod_cast hc
  have hle' : (n : ℝ) ≤ a n := by exact_mod_cast hle
  have h1 : (a n : ℝ) / n < 2.41 := by
    rw [div_lt_iff₀ hnpos]
    linarith
  have h2 : 1 ≤ (a n : ℝ) / n := by
    rw [le_div_iff₀ hnpos]
    linarith
  constructor <;> linarith

lemma bound_large (n : ℕ) (hn : 1 ≤ n) (ha : 1897 < a n) :
    -1 < m0 - (a n : ℝ) / n ∧ m0 - (a n : ℝ) / n < 1 := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  have hc : 0 < cc := by linarith
  have hD := D_small (a n) ha
  obtain ⟨hZ, hO⟩ := a_spec n hn
  have hle : n ≤ a n := by have := O_add_Z (a n); omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hdev := a_dev n hn
  have hDdef : D (a n) = (n : ℝ) - cc * ((a n : ℝ) - n) := by
    unfold D
    rw [hZ, hO]
    push_cast [hle]
    ring
  rw [abs_lt, hDdef] at hD
  obtain ⟨hD1, hD2⟩ := hD
  have e : m0 - (a n : ℝ) / n = (m0 * n - a n) / n := by field_simp
  rw [e, hdev, hDdef]
  have hA0 : (0 : ℝ) ≤ a n := Nat.cast_nonneg _
  have hle' : (n : ℝ) ≤ a n := by exact_mod_cast hle
  have hP : 2.3922 * (a n : ℝ) ≤ cc * a n := mul_le_mul_of_nonneg_right hc1 hA0
  have hQ1 : 2.3922 * (n : ℝ) ≤ cc * n := mul_le_mul_of_nonneg_right hc1 hnpos.le
  have hQ2 : cc * (n : ℝ) ≤ 2.3925 * n := mul_le_mul_of_nonneg_right hc2 hnpos.le
  have hE : cc * ((a n : ℝ) - n) = cc * a n - cc * n := by ring
  rw [hE] at hD1 hD2 ⊢
  constructor
  · rw [lt_div_iff₀ hnpos, lt_div_iff₀ hc]
    linarith
  · rw [div_lt_iff₀ hnpos, div_lt_iff₀ hc]
    linarith

/-- Kimberling's conjecture: a(n)/n tends to a number m = 1.41..., and -1 < m - a(n)/n < 1
for n >= 1. -/
theorem conjecture : ∃ m : ℝ, (1.41 ≤ m ∧ m < 1.42) ∧
    Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 m) ∧
    ∀ n : ℕ, 1 ≤ n → -1 < m - (a n : ℝ) / n ∧ m - (a n : ℝ) / n < 1 := by
  obtain ⟨hm1, hm2⟩ := m0_bounds
  obtain ⟨hc1, hc2⟩ := cc_bounds
  have hc : 0 < cc := by linarith
  have hbound : ∀ n : ℕ, 1 ≤ n → -1 < m0 - (a n : ℝ) / n ∧ m0 - (a n : ℝ) / n < 1 := by
    intro n hn
    rcases le_or_gt (a n) 1897 with h | h
    · exact bound_small n hn h
    · exact bound_large n hn h
  refine ⟨m0, ⟨by linarith, by linarith⟩, ?_, hbound⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun n : ℕ => Real.sqrt (40000 * 3 / cc ^ 2 / n)) atTop (𝓝 0) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat (40000 * 3 / cc ^ 2)).sqrt
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨hZ, hO⟩ := a_spec n hn
  have hle : n ≤ a n := by have := O_add_Z (a n); omega
  have hsq := D_sq (a n) (le_trans hn hle)
  have hb := hbound n hn
  have ha3 : (a n : ℝ) ≤ 3 * n := by
    have h1 : (a n : ℝ) / n < 2.4182 := by linarith [hb.1]
    rw [div_lt_iff₀ hnpos] at h1
    linarith
  have hdev := a_dev n hn
  rw [Real.norm_eq_abs]
  apply Real.abs_le_sqrt
  have e : (a n : ℝ) / n - m0 = -(D (a n) / cc) / n := by
    rw [← hdev]
    field_simp
    ring
  have key : ((a n : ℝ) / n - m0) ^ 2 = D (a n) ^ 2 / (cc ^ 2 * n ^ 2) := by
    rw [e]
    field_simp
  rw [key, div_le_div_iff₀ (by positivity) hnpos]
  have hD3 : D (a n) ^ 2 ≤ 40000 * (3 * n) := by
    have : (40000 : ℝ) * (a n) ≤ 40000 * (3 * n) := by linarith
    linarith
  have e2 : 40000 * 3 / cc ^ 2 * (cc ^ 2 * (n : ℝ) ^ 2) = 40000 * 3 * n ^ 2 := by
    field_simp
  rw [e2]
  nlinarith [hD3, hnpos]

end OMA.S_oeis_a288671

theorem OMA.solution : type_of% @OMA.S_oeis_a288671.main :=
  OMA.S_oeis_a288671.conjecture
