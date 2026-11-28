import OMAStatements.S_oeis_a222777
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Proof of OEIS A222777

We collapse `rows n k left right` to a function `F n k a b` depending only on the number of
introduced colours `k` and the cardinalities `a`, `b` of `left.toFinset` and `right.toFinset`,
whenever all entries of `left` and `right` are strictly less than `k`.
For `a = b = 2`, the resulting system is upper triangular in `k ∈ {3, 4, 5, 6, 7}`, yielding
exact integer-cleared closed forms in powers of `1, 4, 9, 25`.
Unrolling three steps from `(0, [], [])` gives the closed form for `4 * coeff (t + 3)`, and the
order-4 generating function recurrence follows immediately from `(x - 1)(x - 4)(x - 9)(x - 25)`.
-/

namespace OMA.Proof_oeis_a222777
open OMA.S_oeis_a222777

private def nextCard (a : ℕ) : ℕ := if a = 0 then 1 else 2

private def stepRight (b na : ℕ) (j : ℕ) (f : ℕ → ℕ → ℕ → ℤ) : ℤ :=
  ((j - b : ℕ) : ℤ) * f j (nextCard b) na +
    if j < 7 then f (j + 1) (nextCard b) na else 0

private def F : ℕ → ℕ → ℕ → ℕ → ℤ
  | 0, _, _, _ => 1
  | n + 1, k, a, b =>
      ((k - a : ℕ) : ℤ) * stepRight b (nextCard a) k (F n) +
        if k < 7 then stepRight b (nextCard a) (k + 1) (F n) else 0

private lemma card_sdiff_range (k : ℕ) (l : List ℕ) (hl : ∀ x ∈ l, x < k) :
    (Finset.range k \ l.toFinset).card = k - l.toFinset.card := by
  have hsub : l.toFinset ⊆ Finset.range k := by
    intro x hx
    exact Finset.mem_range.mpr (hl x (List.mem_toFinset.mp hx))
  rw [Finset.card_sdiff_of_subset hsub, Finset.card_range]

private lemma remember_lt {c k : ℕ} {l : List ℕ} (hc : c < k) (hl : ∀ x ∈ l, x < k) :
    ∀ x ∈ remember c l, x < k := by
  intro x hx
  simp only [remember, List.mem_cons] at hx
  rcases hx with rfl | hx
  · exact hc
  · exact hl x (List.mem_of_mem_take hx)

private lemma remember_card {c : ℕ} {l : List ℕ} (hc : c ∉ l.toFinset) :
    (remember c l).toFinset.card = nextCard l.toFinset.card := by
  cases l with
  | nil => simp [remember, nextCard]
  | cons a t =>
    have hca : c ≠ a := by
      intro h
      apply hc
      subst h
      simp
    simp [remember, nextCard, hca]

private lemma choices_const {k : ℕ} {blocked : List ℕ} {f : ℕ → ℕ → ℤ} {g : ℕ → ℤ}
    (hb : ∀ x ∈ blocked, x < k)
    (h1 : ∀ c ∈ Finset.range k \ blocked.toFinset, f c k = g k)
    (h2 : k < 7 → f k (k + 1) = g (k + 1)) :
    choices k blocked f =
      ((k - blocked.toFinset.card : ℕ) : ℤ) * g k + if k < 7 then g (k + 1) else 0 := by
  unfold choices
  rw [Finset.sum_congr rfl h1, Finset.sum_const, card_sdiff_range k blocked hb, nsmul_eq_mul]
  split_ifs with hk
  · rw [h2 hk]
  · rfl

private lemma rows_eq_F (n : ℕ) :
    ∀ k left right, (∀ x ∈ left, x < k) → (∀ x ∈ right, x < k) →
      rows n k left right = F n k left.toFinset.card right.toFinset.card := by
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro k left right hl hr
    simp only [rows, F]
    refine choices_const
      (g := fun j => stepRight right.toFinset.card (nextCard left.toFinset.card) j (F n))
      hl ?_ ?_
    · intro c hc
      have hclt : c < k := Finset.mem_range.mp (Finset.mem_sdiff.mp hc).1
      have hcnm : c ∉ left.toFinset := (Finset.mem_sdiff.mp hc).2
      refine choices_const
        (g := fun l => F n l (nextCard right.toFinset.card) (nextCard left.toFinset.card))
        hr ?_ ?_
      · intro e he
        have helt : e < k := Finset.mem_range.mp (Finset.mem_sdiff.mp he).1
        have henm : e ∉ right.toFinset := (Finset.mem_sdiff.mp he).2
        rw [ih k _ _ (remember_lt helt hr) (remember_lt hclt hl),
          remember_card henm, remember_card hcnm]
      · intro _
        have hknm : k ∉ right.toFinset :=
          fun h => Nat.lt_irrefl k (hr k (List.mem_toFinset.mp h))
        rw [ih (k + 1) _ _
          (remember_lt (Nat.lt_succ_self k) (fun x hx => Nat.lt_succ_of_lt (hr x hx)))
          (remember_lt (Nat.lt_succ_of_lt hclt) (fun x hx => Nat.lt_succ_of_lt (hl x hx))),
          remember_card hknm, remember_card hcnm]
    · intro _
      have hknm : k ∉ left.toFinset :=
        fun h => Nat.lt_irrefl k (hl k (List.mem_toFinset.mp h))
      have hr' : ∀ x ∈ right, x < k + 1 := fun x hx => Nat.lt_succ_of_lt (hr x hx)
      refine choices_const
        (g := fun l => F n l (nextCard right.toFinset.card) (nextCard left.toFinset.card))
        hr' ?_ ?_
      · intro e he
        have helt : e < k + 1 := Finset.mem_range.mp (Finset.mem_sdiff.mp he).1
        have henm : e ∉ right.toFinset := (Finset.mem_sdiff.mp he).2
        rw [ih (k + 1) _ _ (remember_lt helt hr')
          (remember_lt (Nat.lt_succ_self k) (fun x hx => Nat.lt_succ_of_lt (hl x hx))),
          remember_card henm, remember_card hknm]
      · intro _
        have hknm' : k + 1 ∉ right.toFinset :=
          fun h => Nat.lt_irrefl (k + 1) (hr' (k + 1) (List.mem_toFinset.mp h))
        rw [ih (k + 2) _ _
          (remember_lt (Nat.lt_succ_self (k + 1)) (fun x hx => Nat.lt_succ_of_lt (hr' x hx)))
          (remember_lt (by omega) (fun x hx => by have := hl x hx; omega)),
          remember_card hknm', remember_card hknm]

private lemma coeff_succ_eq_F (n : ℕ) : coeff (n + 1) = F (n + 1) 0 0 0 := by
  simpa [coeff] using rows_eq_F (n + 1) 0 [] [] (by simp) (by simp)

private lemma F_7 (n : ℕ) : F n 7 2 2 = 25 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [F, stepRight, nextCard, ih]
    ring

private lemma F_6 (n : ℕ) : F n 6 2 2 = 25 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [F, stepRight, nextCard, ih, F_7]
    ring

private lemma F_5 (n : ℕ) : 2 * F n 5 2 2 = 9 ^ n + 25 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hstep : F (n + 1) 5 2 2 = 9 * F n 5 2 2 + 7 * F n 6 2 2 + F n 7 2 2 := by
      simp [F, stepRight, nextCard]
      ring
    have h6 := F_6 n
    have h7 := F_7 n
    calc 2 * F (n + 1) 5 2 2
        = 9 * (2 * F n 5 2 2) + 14 * F n 6 2 2 + 2 * F n 7 2 2 := by linarith
      _ = 9 * (9 ^ n + 25 ^ n) + 14 * 25 ^ n + 2 * 25 ^ n := by rw [ih, h6, h7]
      _ = 9 ^ (n + 1) + 25 ^ (n + 1) := by ring

private lemma F_4 (n : ℕ) : 6 * F n 4 2 2 = 2 * 4 ^ n + 3 * 9 ^ n + 25 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hstep : F (n + 1) 4 2 2 = 4 * F n 4 2 2 + 5 * F n 5 2 2 + F n 6 2 2 := by
      simp [F, stepRight, nextCard]
      ring
    have h5 := F_5 n
    have h6 := F_6 n
    calc 6 * F (n + 1) 4 2 2
        = 4 * (6 * F n 4 2 2) + 15 * (2 * F n 5 2 2) + 6 * F n 6 2 2 := by linarith
      _ = 4 * (2 * 4 ^ n + 3 * 9 ^ n + 25 ^ n) + 15 * (9 ^ n + 25 ^ n) + 6 * 25 ^ n := by
            rw [ih, h5, h6]
      _ = 2 * 4 ^ (n + 1) + 3 * 9 ^ (n + 1) + 25 ^ (n + 1) := by ring

private lemma F_3 (n : ℕ) : 24 * F n 3 2 2 = 9 + 8 * 4 ^ n + 6 * 9 ^ n + 25 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hstep : F (n + 1) 3 2 2 = F n 3 2 2 + 3 * F n 4 2 2 + F n 5 2 2 := by
      simp [F, stepRight, nextCard]
      ring
    have h4 := F_4 n
    have h5 := F_5 n
    calc 24 * F (n + 1) 3 2 2
        = 24 * F n 3 2 2 + 12 * (6 * F n 4 2 2) + 12 * (2 * F n 5 2 2) := by linarith
      _ = (9 + 8 * 4 ^ n + 6 * 9 ^ n + 25 ^ n)
            + 12 * (2 * 4 ^ n + 3 * 9 ^ n + 25 ^ n) + 12 * (9 ^ n + 25 ^ n) := by
            rw [ih, h4, h5]
      _ = 9 + 8 * 4 ^ (n + 1) + 6 * 9 ^ (n + 1) + 25 ^ (n + 1) := by ring

private lemma F_start (t : ℕ) :
    F (t + 3) 0 0 0 = 6 * F t 3 2 2 + 18 * F t 4 2 2 + 9 * F t 5 2 2 + F t 6 2 2 := by
  simp [F, stepRight, nextCard]
  ring

private lemma four_mul_coeff (t : ℕ) :
    4 * coeff (t + 3) = 9 + 32 * 4 ^ t + 60 * 9 ^ t + 35 * 25 ^ t := by
  rw [coeff_succ_eq_F (t + 2), F_start]
  have h3 := F_3 t
  have h4 := F_4 t
  have h5 := F_5 t
  have h6 := F_6 t
  linarith

private lemma closed_form (t : ℕ) :
    4 * coeff (t + 3) = 9 + 4 * 2 ^ (2 * t + 3) + 20 * 3 ^ (2 * t + 1) + 7 * 5 ^ (2 * t + 1) := by
  rw [four_mul_coeff]
  have h2 : (2 : ℤ) ^ (2 * t + 3) = 8 * 4 ^ t := by
    rw [pow_add, pow_mul]
    ring
  have h3 : (3 : ℤ) ^ (2 * t + 1) = 3 * 9 ^ t := by
    rw [pow_add, pow_mul]
    ring
  have h5 : (5 : ℤ) ^ (2 * t + 1) = 5 * 25 ^ t := by
    rw [pow_add, pow_mul]
    ring
  rw [h2, h3, h5]
  ring

private lemma coeff_0 : coeff 0 = 0 := rfl

private lemma coeff_1 : coeff 1 = 2 := by
  rw [coeff_succ_eq_F 0]; rfl

private lemma coeff_2 : coeff 2 = 7 := by
  rw [coeff_succ_eq_F 1]; rfl

private lemma coeff_3 : coeff 3 = 34 := by
  have h := four_mul_coeff 0; norm_num at h; omega

private lemma coeff_4 : coeff 4 = 388 := by
  have h := four_mul_coeff 1; norm_num at h; omega

private lemma coeff_5 : coeff 5 = 6814 := by
  have h := four_mul_coeff 2; norm_num at h; omega

private lemma coeff_6 : coeff 6 = 148168 := by
  have h := four_mul_coeff 3; norm_num at h; omega

private lemma recurrence (m : ℕ) :
    coeff m - 39 * shift coeff 1 m + 399 * shift coeff 2 m
      - 1261 * shift coeff 3 m + 900 * shift coeff 4 m = numerator m := by
  by_cases hm : m ≤ 6
  · interval_cases m <;>
      norm_num [shift, numerator, coeff_0, coeff_1, coeff_2, coeff_3, coeff_4, coeff_5, coeff_6]
  · obtain ⟨t, rfl⟩ : ∃ t, m = t + 7 := ⟨m - 7, by omega⟩
    have hnum : numerator (t + 7) = 0 := by
      cases t <;> rfl
    rw [hnum]
    simp only [shift,
      show 1 ≤ t + 7 by omega, show 2 ≤ t + 7 by omega,
      show 3 ≤ t + 7 by omega, show 4 ≤ t + 7 by omega,
      ite_true,
      show t + 7 - 1 = t + 6 by omega, show t + 7 - 2 = t + 5 by omega,
      show t + 7 - 3 = t + 4 by omega, show t + 7 - 4 = t + 3 by omega]
    have h0 := four_mul_coeff t
    have h1 := four_mul_coeff (t + 1)
    have h2 := four_mul_coeff (t + 2)
    have h3 := four_mul_coeff (t + 3)
    have h4 := four_mul_coeff (t + 4)
    have hsum :
        4 * (coeff (t + 7) - 39 * coeff (t + 6) + 399 * coeff (t + 5)
          - 1261 * coeff (t + 4) + 900 * coeff (t + 3)) = 0 := by
      calc 4 * (coeff (t + 7) - 39 * coeff (t + 6) + 399 * coeff (t + 5)
              - 1261 * coeff (t + 4) + 900 * coeff (t + 3))
          = 4 * coeff (t + 4 + 3) - 39 * (4 * coeff (t + 3 + 3))
              + 399 * (4 * coeff (t + 2 + 3)) - 1261 * (4 * coeff (t + 1 + 3))
              + 900 * (4 * coeff (t + 3)) := by ring
        _ = (9 + 32 * 4 ^ (t + 4) + 60 * 9 ^ (t + 4) + 35 * 25 ^ (t + 4))
              - 39 * (9 + 32 * 4 ^ (t + 3) + 60 * 9 ^ (t + 3) + 35 * 25 ^ (t + 3))
              + 399 * (9 + 32 * 4 ^ (t + 2) + 60 * 9 ^ (t + 2) + 35 * 25 ^ (t + 2))
              - 1261 * (9 + 32 * 4 ^ (t + 1) + 60 * 9 ^ (t + 1) + 35 * 25 ^ (t + 1))
              + 900 * (9 + 32 * 4 ^ t + 60 * 9 ^ t + 35 * 25 ^ t) := by
                rw [h4, h3, h2, h1, h0]
        _ = 0 := by ring
    omega

theorem result : type_of% @OMA.S_oeis_a222777.main :=
  ⟨recurrence, closed_form⟩

end OMA.Proof_oeis_a222777

theorem OMA.solution : type_of% @OMA.S_oeis_a222777.main := OMA.Proof_oeis_a222777.result
