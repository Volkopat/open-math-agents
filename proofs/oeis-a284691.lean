import OMAStatements.S_oeis_a284691
import Mathlib

/-
Proof of Conjecture 1 of A284691. With `X = 10`, `3 * A074992 i = 1 + X^i + X^(2i)` and
`10^c - 1 = 9 * (1 + X + ... + X^(c-1))`, so the term is
`N = (1 + ... + X^(c-1)) * (1 + X^i + X^(2i)) * (1 + X^j + X^(2j))`
`  = sum over a, b in {0, 1, 2} and s < c of X^(a*i + b*j + s)`.
Its coefficient at `X^t` is the number `coef i j c t` of pairs `(a, b)` with `a*i + b*j ≤ t < a*i + b*j + c`, so it
is at most `9`: these coefficients are the decimal digits of `N` (no carries), the top one is nonzero, and the
substitution `(a, b) ↦ (2 - a, 2 - b)` shows `coef` is symmetric about the middle.
-/

namespace OMA.A284691Proof

open OMA.S_oeis_a284691

/-- Indicator of `e ≤ t < e + c`. -/
def ind (e c t : ℕ) : ℕ := if e ≤ t ∧ t < e + c then 1 else 0

/-- The coefficient of `X^t` in the expansion of a term. -/
def coef (i j c t : ℕ) : ℕ :=
  ∑ a ∈ Finset.range 3, ∑ b ∈ Finset.range 3, ind (a * i + b * j) c t

theorem ind_le_one (e c t : ℕ) : ind e c t ≤ 1 := by
  unfold ind
  split_ifs <;> omega

theorem ind_reflect (e e' E c t : ℕ) (h : e + e' = E) (_hc : 1 ≤ c) (ht : t ≤ E + c - 1) :
    ind e c (E + c - 1 - t) = ind e' c t := by
  unfold ind
  split_ifs <;> omega

theorem coef_le_nine (i j c t : ℕ) : coef i j c t ≤ 9 := by
  unfold coef
  calc ∑ a ∈ Finset.range 3, ∑ b ∈ Finset.range 3, ind (a * i + b * j) c t
      ≤ ∑ a ∈ Finset.range 3, ∑ b ∈ Finset.range 3, (1 : ℕ) :=
        Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => ind_le_one _ _ _))
    _ = 9 := by simp

theorem coef_top (i j c : ℕ) (hc : 1 ≤ c) : coef i j c (2 * i + 2 * j + c - 1) ≠ 0 := by
  unfold coef
  intro h0
  rw [Finset.sum_eq_zero_iff] at h0
  have h1 := h0 2 (by simp)
  rw [Finset.sum_eq_zero_iff] at h1
  have h2 := h1 2 (by simp)
  have hcond : 2 * i + 2 * j ≤ 2 * i + 2 * j + c - 1 ∧ 2 * i + 2 * j + c - 1 < 2 * i + 2 * j + c :=
    ⟨by omega, by omega⟩
  rw [ind, if_pos hcond] at h2
  exact one_ne_zero h2

theorem reflect3 (g : ℕ → ℕ → ℕ) :
    ∑ a ∈ Finset.range 3, ∑ b ∈ Finset.range 3, g (2 - a) (2 - b) =
      ∑ a ∈ Finset.range 3, ∑ b ∈ Finset.range 3, g a b := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.reduceSub]
  ring

theorem coef_reflect (i j c t : ℕ) (hc : 1 ≤ c) (ht : t ≤ 2 * i + 2 * j + c - 1) :
    coef i j c (2 * i + 2 * j + c - 1 - t) = coef i j c t := by
  unfold coef
  have key : ∀ a ∈ Finset.range 3, ∀ b ∈ Finset.range 3,
      ind (a * i + b * j) c (2 * i + 2 * j + c - 1 - t) = ind ((2 - a) * i + (2 - b) * j) c t := by
    intro a ha b hb
    rw [Finset.mem_range] at ha hb
    refine ind_reflect _ _ (2 * i + 2 * j) c t ?_ hc ht
    rw [Nat.sub_mul, Nat.sub_mul]
    have h1 : a * i ≤ 2 * i := Nat.mul_le_mul (by omega) le_rfl
    have h2 : b * j ≤ 2 * j := Nat.mul_le_mul (by omega) le_rfl
    omega
  calc ∑ a ∈ Finset.range 3, ∑ b ∈ Finset.range 3, ind (a * i + b * j) c (2 * i + 2 * j + c - 1 - t)
      = ∑ a ∈ Finset.range 3, ∑ b ∈ Finset.range 3, ind ((2 - a) * i + (2 - b) * j) c t :=
        Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun b hb => key a ha b hb))
    _ = ∑ a ∈ Finset.range 3, ∑ b ∈ Finset.range 3, ind (a * i + b * j) c t :=
        reflect3 (fun a b => ind (a * i + b * j) c t)

theorem ofDigits_map_range (b : ℕ) (f : ℕ → ℕ) (n : ℕ) :
    Nat.ofDigits b ((List.range n).map f) = ∑ t ∈ Finset.range n, f t * b ^ t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, Nat.ofDigits_append, ih, Finset.sum_range_succ]
    simp only [List.length_map, List.length_range, List.map_cons, List.map_nil, Nat.ofDigits_singleton]
    ring

theorem sum_ind (X e c n : ℕ) (h : e + c ≤ n) :
    ∑ t ∈ Finset.range n, ind e c t * X ^ t = X ^ e * ∑ s ∈ Finset.range c, X ^ s := by
  have h1 : ∀ t ∈ Finset.range n,
      ind e c t * X ^ t = if t ∈ Finset.Ico e (e + c) then X ^ t else 0 := by
    intro t _
    unfold ind
    by_cases ht : e ≤ t ∧ t < e + c
    · rw [if_pos ht, if_pos (Finset.mem_Ico.mpr ht), one_mul]
    · rw [if_neg ht, if_neg (fun h' => ht (Finset.mem_Ico.mp h')), zero_mul]
  rw [Finset.sum_congr rfl h1, ← Finset.sum_filter]
  have h2 : (Finset.range n).filter (fun t => t ∈ Finset.Ico e (e + c)) = Finset.Ico e (e + c) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [h2, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left, Finset.mul_sum]
  simp only [pow_add]

theorem coef_sum (X i j c : ℕ) :
    ∑ t ∈ Finset.range (2 * i + 2 * j + c), coef i j c t * X ^ t =
      ∑ a ∈ Finset.range 3, ∑ b ∈ Finset.range 3, X ^ (a * i + b * j) * ∑ s ∈ Finset.range c, X ^ s := by
  simp only [coef, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b hb => ?_)
  apply sum_ind
  rw [Finset.mem_range] at ha hb
  have h1 : a * i ≤ 2 * i := Nat.mul_le_mul (by omega) le_rfl
  have h2 : b * j ≤ 2 * j := Nat.mul_le_mul (by omega) le_rfl
  omega

theorem expand (X i j R : ℕ) :
    ∑ a ∈ Finset.range 3, ∑ b ∈ Finset.range 3, X ^ (a * i + b * j) * R =
      R * (X ^ (2 * i) + X ^ i + 1) * (X ^ (2 * j) + X ^ j + 1) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  ring

theorem nine_R (c : ℕ) : 10 ^ c - 1 = 9 * ∑ s ∈ Finset.range c, 10 ^ s := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have : 0 < 10 ^ c := by positivity
    omega

theorem three_A (n : ℕ) : 3 * A074992 n = 10 ^ (2 * n) + 10 ^ n + 1 := by
  unfold A074992
  have h1 : 10 ^ (2 * n) % 3 = 1 := by rw [Nat.pow_mod]; norm_num
  have h2 : 10 ^ n % 3 = 1 := by rw [Nat.pow_mod]; norm_num
  omega

theorem value (c i j : ℕ) :
    (10 ^ c - 1) * A074992 i * A074992 j =
      ∑ a ∈ Finset.range 3, ∑ b ∈ Finset.range 3, 10 ^ (a * i + b * j) * ∑ s ∈ Finset.range c, 10 ^ s := by
  rw [expand, nine_R c, ← three_A i, ← three_A j]
  ring

theorem digits_eq (c i j : ℕ) (hc : 1 ≤ c) :
    Nat.digits 10 ((10 ^ c - 1) * A074992 i * A074992 j) =
      (List.range (2 * i + 2 * j + c)).map (coef i j c) := by
  have hv : (10 ^ c - 1) * A074992 i * A074992 j =
      Nat.ofDigits 10 ((List.range (2 * i + 2 * j + c)).map (coef i j c)) := by
    rw [ofDigits_map_range, coef_sum, value]
  rw [hv]
  apply Nat.digits_ofDigits 10 (by norm_num)
  · intro x hx
    rw [List.mem_map] at hx
    obtain ⟨t, _, rfl⟩ := hx
    have := coef_le_nine i j c t
    omega
  · intro hne
    simp only [List.getLast_map, List.getLast_range]
    exact coef_top i j c hc

theorem map_range_reverse (f : ℕ → ℕ) (n : ℕ) (h : ∀ t, t < n → f (n - 1 - t) = f t) :
    ((List.range n).map f).reverse = (List.range n).map f := by
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    have hk : k < n := by simpa using h2
    rw [List.getElem_reverse]
    simp only [List.getElem_map, List.getElem_range, List.length_map, List.length_range]
    exact h k hk

theorem palin (i j c : ℕ) (hc : 1 ≤ c) :
    ((List.range (2 * i + 2 * j + c)).map (coef i j c)).reverse =
      (List.range (2 * i + 2 * j + c)).map (coef i j c) := by
  apply map_range_reverse
  intro t ht
  exact coef_reflect i j c t hc (by omega)

end OMA.A284691Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a284691.main := by
  intro k hk
  obtain ⟨c, i, j, hc, rfl⟩ := hk
  rw [OMA.A284691Proof.digits_eq c i j hc]
  exact OMA.A284691Proof.palin i j c hc
