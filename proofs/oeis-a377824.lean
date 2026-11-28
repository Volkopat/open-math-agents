import OMAStatements.S_oeis_a377824
import Mathlib

/-!
Proof that `a n ~ n^2 2^n / 32` for A377824 (sum over all compositions of `n` of the positions of
the minimal parts).

Every composition in `compositions n` has positive parts and at most `n` parts (`Good`). If a
composition contains a part `1`, its minimal parts are exactly its parts equal to `1`, so its
weight is `f1` (sum of the positions of the ones); otherwise `f1 = 0` and the weight is at most
`n^2`. Hence `S n <= a n <= S n + n^2 G n`, where `S n` sums `f1` and `G n` counts the
compositions without a part `1`.

The recursion `compositions (n+2) = map (cons 1) C ++ map bump C` gives linear recurrences for the
number of compositions, the number starting with `1`, the total number of ones and `S`, whose
solutions are `2^(n-1)`, `2^(n-2)`, `(n+2) 2^(n-3)` and `S n = (n+1)(n+6) 2^n / 32` (`n >= 2`).
It also gives `G (n+2) = H (n+1)`, `H (n+2) = G (n+1) + H (n+1)` for the count `H` of
compositions with no `1` after the first part, so `H n <= (13/8)^n`.

Therefore `(n+1)(n+6)/n^2 <= a n / (n^2 2^n / 32) <= (n+1)(n+6)/n^2 + 32 (13/16)^n` for `n >= 2`,
and both bounds tend to `1`.
-/

namespace OMA.Helpers

open OMA.S_oeis_a377824

/-- Marks the parts equal to one. -/
def p1 : ℕ → Bool := fun x => decide (x = 1)

/-- Sum of the positions of the parts equal to one. -/
def f1 (l : List ℕ) : ℕ := weights p1 l

/-- Number of parts equal to one. -/
def c1 (l : List ℕ) : ℕ := marks p1 l

/-- Whether the first part is one. -/
def hd1 : List ℕ → ℕ
  | [] => 0
  | x :: _ => if x = 1 then 1 else 0

/-- No part equals one. -/
def g (l : List ℕ) : ℕ := if 1 ∈ l then 0 else 1

/-- No part after the first equals one. -/
def hh (l : List ℕ) : ℕ := if 1 ∈ l.tail then 0 else 1

theorem marks_congr {p q : ℕ → Bool} : ∀ l : List ℕ, (∀ x ∈ l, p x = q x) →
    marks p l = marks q l
  | [], _ => rfl
  | x :: xs, h => by
    simp only [marks]
    rw [h x (by simp), marks_congr xs (fun y hy => h y (by simp [hy]))]

theorem weights_congr {p q : ℕ → Bool} : ∀ l : List ℕ, (∀ x ∈ l, p x = q x) →
    weights p l = weights q l
  | [], _ => rfl
  | x :: xs, h => by
    simp only [weights]
    rw [h x (by simp), marks_congr xs (fun y hy => h y (by simp [hy])),
      weights_congr xs (fun y hy => h y (by simp [hy]))]

theorem marks_le (p : ℕ → Bool) : ∀ l : List ℕ, marks p l ≤ l.length
  | [] => le_rfl
  | x :: xs => by
    simp only [marks, List.length_cons]
    have := marks_le p xs
    split_ifs <;> omega

theorem weights_le (p : ℕ → Bool) : ∀ l : List ℕ, weights p l ≤ l.length * l.length
  | [] => le_rfl
  | x :: xs => by
    simp only [weights, List.length_cons]
    have h1 := marks_le p xs
    have h2 := weights_le p xs
    have h3 : (if p x = true then 1 else 0) ≤ 1 := by split_ifs <;> omega
    nlinarith

theorem weights_false : ∀ l : List ℕ, weights (fun _ => false) l = 0
  | [] => rfl
  | x :: xs => by
    simp only [weights]
    rw [weights_false xs]
    have : marks (fun _ => false) xs = 0 := by
      induction xs with
      | nil => rfl
      | cons y ys ih => simp [marks, ih]
    simp [this]

/-- Parts are positive and there are at most `n` of them. -/
def Good (n : ℕ) (l : List ℕ) : Prop := (∀ x ∈ l, 1 ≤ x) ∧ l.length ≤ n

theorem good_cons {n : ℕ} {l : List ℕ} (h : Good n l) : Good (n + 1) (1 :: l) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact le_rfl
    · exact h.1 x hx
  · simp only [List.length_cons]
    have := h.2
    omega

theorem good_bump {n : ℕ} {l : List ℕ} (h : Good n l) : Good (n + 1) (bump l) := by
  cases l with
  | nil => exact ⟨by simp [bump], by simp [bump]⟩
  | cons x xs =>
    refine ⟨?_, ?_⟩
    · intro y hy
      simp only [bump, List.mem_cons] at hy
      rcases hy with rfl | hy
      · omega
      · exact h.1 y (by simp [hy])
    · simp only [bump, List.length_cons]
      have := h.2
      simp only [List.length_cons] at this
      omega

theorem comp_good : (n : ℕ) → ∀ l ∈ compositions n, Good n l
  | 0 => by
    intro l hl
    simp only [compositions, List.mem_singleton] at hl
    subst hl
    exact ⟨by simp, by simp⟩
  | 1 => by
    intro l hl
    simp only [compositions, List.mem_singleton] at hl
    subst hl
    exact ⟨by simp, by simp⟩
  | n + 2 => by
    intro l hl
    simp only [compositions, List.mem_append, List.mem_map] at hl
    rcases hl with ⟨l', hl', rfl⟩ | ⟨l', hl', rfl⟩
    · exact good_cons (comp_good (n + 1) l' hl')
    · exact good_bump (comp_good (n + 1) l' hl')

theorem total_ss (h : List ℕ → ℕ) (n : ℕ) :
    total h (n + 2) = total (fun l => h (1 :: l)) (n + 1) + total (fun l => h (bump l)) (n + 1) := by
  simp only [total, compositions, List.map_append, List.sum_append, List.map_map]
  rfl

theorem total_congr {h k : List ℕ → ℕ} (n : ℕ) (e : ∀ l, Good n l → h l = k l) :
    total h n = total k n := by
  unfold total
  rw [List.map_congr_left (fun l hl => e l (comp_good n l hl))]

theorem total_add (h k : List ℕ → ℕ) (n : ℕ) :
    total (fun l => h l + k l) n = total h n + total k n := by
  unfold total
  rw [List.sum_map_add]

theorem total_const (c : ℕ) (n : ℕ) :
    total (fun _ => c) n = c * total (fun _ => 1) n := by
  unfold total
  simp [Nat.mul_comm]

theorem total_mono {h k : List ℕ → ℕ} (n : ℕ) (e : ∀ l, Good n l → h l ≤ k l) :
    total h n ≤ total k n := by
  unfold total
  have : ∀ L : List (List ℕ), (∀ l ∈ L, Good n l) → (L.map h).sum ≤ (L.map k).sum := by
    intro L
    induction L with
    | nil => intro _; simp
    | cons x xs ih =>
      intro hL
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (e x (hL x (by simp))) (ih (fun l hl => hL l (by simp [hl])))
  exact this _ (comp_good n)


theorem total_mul (c : ℕ) (h : List ℕ → ℕ) (n : ℕ) :
    total (fun l => c * h l) n = c * total h n := by
  unfold total
  rw [List.sum_map_mul_left]

theorem f1_cons (l : List ℕ) : f1 (1 :: l) = 1 + c1 l + f1 l := by
  simp [f1, c1, weights, p1]

theorem c1_cons (l : List ℕ) : c1 (1 :: l) = 1 + c1 l := by
  simp [c1, marks, p1]

theorem f1_bump {n : ℕ} {l : List ℕ} (h : Good n l) : f1 (bump l) + hd1 l = f1 l := by
  cases l with
  | nil => rfl
  | cons x xs =>
    have hx : 1 ≤ x := h.1 x (by simp)
    simp only [f1, bump, weights, hd1, p1]
    by_cases h1 : x = 1
    · subst h1
      simp
      omega
    · have hx0 : x ≠ 0 := by omega
      simp [h1, hx0]

theorem c1_bump {n : ℕ} {l : List ℕ} (h : Good n l) : c1 (bump l) + hd1 l = c1 l := by
  cases l with
  | nil => rfl
  | cons x xs =>
    have hx : 1 ≤ x := h.1 x (by simp)
    simp only [c1, bump, marks, hd1, p1]
    by_cases h1 : x = 1
    · subst h1
      simp
      omega
    · have hx0 : x ≠ 0 := by omega
      simp [h1, hx0]

theorem hd1_bump {n : ℕ} {l : List ℕ} (h : Good n l) : hd1 (bump l) = 0 := by
  cases l with
  | nil => rfl
  | cons x xs =>
    have hx : 1 ≤ x := h.1 x (by simp)
    have hx0 : x ≠ 0 := by omega
    simp [bump, hd1, hx0]

theorem g_bump {n : ℕ} {l : List ℕ} (h : Good n l) : g (bump l) = hh l := by
  cases l with
  | nil => rfl
  | cons x xs =>
    have hx : 1 ≤ x := h.1 x (by simp)
    have hx0 : x ≠ 0 := by omega
    by_cases h1 : 1 ∈ xs <;> simp [bump, g, hh, hx0, h1]

theorem hh_bump (l : List ℕ) : hh (bump l) = hh l := by
  cases l with
  | nil => rfl
  | cons x xs => rfl

/-- The number of compositions. -/
def N (n : ℕ) : ℕ := total (fun _ => 1) n

theorem N_ss (n : ℕ) : N (n + 2) = 2 * N (n + 1) := by
  unfold N
  rw [total_ss]
  ring

theorem P_ss (n : ℕ) : total hd1 (n + 2) = N (n + 1) := by
  rw [total_ss, total_congr (n + 1) (fun l hl => hd1_bump hl)]
  simp only [hd1, if_true]
  rw [total_const 0]
  simp [N]

theorem C1_ss (n : ℕ) : total c1 (n + 2) + total hd1 (n + 1) = N (n + 1) + 2 * total c1 (n + 1) := by
  rw [total_ss, add_assoc, ← total_add]
  rw [total_congr (n + 1) (fun l hl => c1_bump hl)]
  simp only [c1_cons]
  rw [total_add, total_const 1, N]
  ring

theorem S_ss (n : ℕ) : total f1 (n + 2) + total hd1 (n + 1) =
    N (n + 1) + 2 * total f1 (n + 1) + total c1 (n + 1) := by
  rw [total_ss, add_assoc, ← total_add]
  rw [total_congr (n + 1) (fun l hl => f1_bump hl)]
  simp only [f1_cons]
  rw [total_add, total_add, total_const 1, N]
  ring

theorem G_ss (n : ℕ) : total g (n + 2) = total hh (n + 1) := by
  rw [total_ss, total_congr (n + 1) (fun l hl => g_bump hl)]
  have : total (fun l => g (1 :: l)) (n + 1) = total (fun _ => 0) (n + 1) := by
    unfold total
    simp [g]
  rw [this, total_const 0]
  simp

theorem H_ss (n : ℕ) : total hh (n + 2) = total g (n + 1) + total hh (n + 1) := by
  rw [total_ss]
  simp only [hh_bump]
  rfl

theorem N_closed (m : ℕ) : N (m + 1) = 2 ^ m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [N_ss, ih, pow_succ]; ring

theorem P_closed (m : ℕ) : total hd1 (m + 2) = 2 ^ m := by
  rw [P_ss, N_closed]

theorem CS_closed (m : ℕ) : 2 * total c1 (m + 2) = (m + 4) * 2 ^ m ∧
    8 * total f1 (m + 2) = (m + 3) * (m + 8) * 2 ^ m := by
  induction m with
  | zero => exact ⟨rfl, rfl⟩
  | succ m ih =>
    obtain ⟨ic, is⟩ := ih
    have ec := C1_ss (m + 1)
    have es := S_ss (m + 1)
    rw [P_closed, N_closed] at ec es
    rw [pow_succ] at ec es ⊢
    constructor
    · nlinarith
    · nlinarith


theorem minW_eq {n : ℕ} {l : List ℕ} (h : Good n l) (h1 : 1 ∈ l) : minWeights l = f1 l := by
  unfold minWeights f1
  apply weights_congr
  intro x hx
  simp only [p1]
  apply decide_eq_decide.mpr
  constructor
  · intro hall
    have e1 := hall 1 h1
    have e2 := h.1 x hx
    omega
  · rintro rfl y hy
    exact h.1 y hy

theorem f1_zero {l : List ℕ} (h1 : 1 ∉ l) : f1 l = 0 := by
  unfold f1
  rw [weights_congr (q := fun _ => false) l (fun x hx => by
    simp only [p1, decide_eq_false_iff_not]
    rintro rfl
    exact h1 hx), weights_false]

theorem minW_lo {n : ℕ} {l : List ℕ} (h : Good n l) : f1 l ≤ minWeights l := by
  by_cases h1 : 1 ∈ l
  · rw [minW_eq h h1]
  · rw [f1_zero h1]
    exact Nat.zero_le _

theorem minW_hi {n : ℕ} {l : List ℕ} (h : Good n l) : minWeights l ≤ f1 l + n * n * g l := by
  by_cases h1 : 1 ∈ l
  · rw [minW_eq h h1]
    simp [g, h1]
  · rw [f1_zero h1]
    simp only [g, h1, if_false, mul_one, zero_add]
    calc minWeights l ≤ l.length * l.length := weights_le _ l
      _ ≤ n * n := Nat.mul_le_mul h.2 h.2

theorem a_lo (n : ℕ) : total f1 n ≤ a n := total_mono n (fun _ h => minW_lo h)

theorem a_hi (n : ℕ) : a n ≤ total f1 n + n * n * total g n := by
  calc a n ≤ total (fun l => f1 l + n * n * g l) n := total_mono n (fun _ h => minW_hi h)
    _ = total f1 n + n * n * total g n := by rw [total_add, total_mul]

theorem g_le_hh (l : List ℕ) : g l ≤ hh l := by
  unfold g hh
  by_cases h1 : 1 ∈ l
  · simp [h1]
  · have : 1 ∉ l.tail := fun h => h1 (List.mem_of_mem_tail h)
    simp [h1, this]

theorem G_le_H (n : ℕ) : total g n ≤ total hh n := total_mono n (fun l _ => g_le_hh l)

theorem G_succ_le (n : ℕ) : total g (n + 1) ≤ total hh n := by
  cases n with
  | zero => decide
  | succ k => rw [G_ss]

theorem H_bound (n : ℕ) : total hh n * 8 ^ n ≤ 13 ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => decide
    | 1, _ => decide
    | k + 2, ih =>
      have e := H_ss k
      have h1 := G_succ_le k
      have i0 := ih k (by omega)
      have i1 := ih (k + 1) (by omega)
      have hk : total hh (k + 2) ≤ total hh k + total hh (k + 1) := by omega
      calc total hh (k + 2) * 8 ^ (k + 2) ≤ (total hh k + total hh (k + 1)) * 8 ^ (k + 2) :=
            Nat.mul_le_mul_right _ hk
        _ = 64 * (total hh k * 8 ^ k) + 8 * (total hh (k + 1) * 8 ^ (k + 1)) := by ring
        _ ≤ 64 * 13 ^ k + 8 * 13 ^ (k + 1) := by gcongr
        _ ≤ 13 ^ (k + 2) := by
          rw [show 13 ^ (k + 2) = 169 * 13 ^ k by ring, show 13 ^ (k + 1) = 13 * 13 ^ k by ring]
          omega

theorem S_real (m : ℕ) :
    (total f1 (m + 2) : ℝ) = (((m + 2 : ℕ) : ℝ) + 1) * (((m + 2 : ℕ) : ℝ) + 6) * 2 ^ (m + 2) / 32 := by
  have h8 : (8 : ℝ) * (total f1 (m + 2) : ℝ) = ((m : ℝ) + 3) * ((m : ℝ) + 8) * 2 ^ m := by
    exact_mod_cast (CS_closed m).2
  push_cast
  rw [pow_add]
  linarith

theorem G_real (n : ℕ) : (total g n : ℝ) ≤ (13 / 8 : ℝ) ^ n := by
  have h1 : (total hh n : ℝ) * 8 ^ n ≤ 13 ^ n := by exact_mod_cast H_bound n
  have h2 : (total g n : ℝ) ≤ total hh n := by exact_mod_cast G_le_H n
  rw [div_pow, le_div_iff₀ (by positivity)]
  nlinarith [pow_pos (show (0 : ℝ) < 8 by norm_num) n]

end OMA.Helpers

open Filter Topology OMA.S_oeis_a377824 OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a377824.main := by
  apply Asymptotics.isEquivalent_of_tendsto_one
  set lo : ℕ → ℝ := fun n => 1 + 7 * (1 / (n : ℝ)) + 6 * (1 / (n : ℝ)) ^ 2 with hlo_def
  set hi : ℕ → ℝ := fun n => lo n + 32 * (13 / 16 : ℝ) ^ n with hhi_def
  have hlo : Tendsto lo atTop (𝓝 1) := by
    have h0 := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
    have := ((tendsto_const_nhds (x := (1 : ℝ))).add (h0.const_mul 7)).add ((h0.pow 2).const_mul 6)
    rw [show (1 : ℝ) = 1 + 7 * 0 + 6 * 0 ^ 2 by norm_num]
    exact this
  have hhi : Tendsto hi atTop (𝓝 1) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (13 / 16 : ℝ)) (by norm_num) (by norm_num)
    have := hlo.add (hp.const_mul 32)
    rw [show (1 : ℝ) = 1 + 32 * 0 by norm_num]
    exact this
  have hloeq : ∀ m : ℕ, lo (m + 2) * (((m + 2 : ℕ) : ℝ) ^ 2 * 2 ^ (m + 2) / 32) =
      (total f1 (m + 2) : ℝ) := by
    intro m
    rw [S_real m]
    simp only [hlo_def]
    have hN : ((m + 2 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    simp only [Pi.div_apply]
    have hv : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) ^ 2 * 2 ^ (m + 2) / 32 := by positivity
    rw [le_div_iff₀ hv, hloeq m]
    exact_mod_cast a_lo (m + 2)
  · filter_upwards [eventually_ge_atTop 2] with n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    simp only [Pi.div_apply]
    have hv : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) ^ 2 * 2 ^ (m + 2) / 32 := by positivity
    rw [div_le_iff₀ hv]
    have e1 : hi (m + 2) * (((m + 2 : ℕ) : ℝ) ^ 2 * 2 ^ (m + 2) / 32) =
        lo (m + 2) * (((m + 2 : ℕ) : ℝ) ^ 2 * 2 ^ (m + 2) / 32) +
          ((m + 2 : ℕ) : ℝ) ^ 2 * ((13 / 16 : ℝ) ^ (m + 2) * 2 ^ (m + 2)) := by
      simp only [hhi_def]
      ring
    have e2 : (13 / 16 : ℝ) ^ (m + 2) * 2 ^ (m + 2) = (13 / 8 : ℝ) ^ (m + 2) := by
      rw [← mul_pow]
      norm_num
    rw [e1, e2, hloeq m]
    have h1 : (a (m + 2) : ℝ) ≤ (total f1 (m + 2) : ℝ) +
        ((m + 2 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) * (total g (m + 2) : ℝ) := by
      exact_mod_cast a_hi (m + 2)
    have h2 := G_real (m + 2)
    have h3 : (0 : ℝ) ≤ ((m + 2 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) := by positivity
    nlinarith
