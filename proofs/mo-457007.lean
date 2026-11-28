import OMAStatements.S_mo_457007
import Mathlib
open OMA.S_mo_457007

/-- Decimal digits with fuel. -/
def dl : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, x => if x = 0 then [] else x % 10 :: dl k (x / 10)

lemma dl_eq : ∀ k x, x < 10 ^ k → dl k x = Nat.digits 10 x := by
  intro k
  induction k with
  | zero =>
    intro x hx
    have : x = 0 := by simpa using hx
    subst this; simp [dl]
  | succ k ih =>
    intro x hx
    by_cases h0 : x = 0
    · subst h0; simp [dl]
    · rw [dl, if_neg h0, Nat.digits_def' (by norm_num) (Nat.pos_of_ne_zero h0)]
      congr 1
      apply ih
      rw [pow_succ] at hx
      omega

lemma sum_fact_le : ∀ l : List ℕ, (∀ a ∈ l, a < 10) →
    (l.map Nat.factorial).sum ≤ 362880 * l.length := by
  intro l
  induction l with
  | nil => simp
  | cons a l ih =>
    intro h
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have ha : a < 10 := h a (by simp)
    have h1 : a.factorial ≤ Nat.factorial 9 := Nat.factorial_le (by omega)
    have h2 := ih (fun b hb => h b (by simp [hb]))
    have : Nat.factorial 9 = 362880 := by decide
    rw [this] at h1
    rw [mul_add, mul_one]
    omega

lemma pow_big : ∀ L : ℕ, 8 ≤ L → 3628800 * L < 10 ^ L := by
  intro L hL
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ L hL ih =>
    rw [pow_succ]
    omega

lemma bound (x : ℕ) (hx : 0 < x) (h : f x = x) : x < 10 ^ 7 := by
  have hlen : (Nat.digits 10 x).length ≤ 7 := by
    by_contra hc
    rw [not_le] at hc
    have h1 := Nat.base_pow_length_digits_le 10 x (by norm_num) hx.ne'
    have h2 := sum_fact_le (Nat.digits 10 x) (fun a ha => Nat.digits_lt_base (by norm_num) ha)
    have h3 := pow_big _ hc
    unfold f at h
    rw [h] at h2
    omega
  calc x < 10 ^ (Nat.digits 10 x).length := Nat.lt_base_pow_length_digits (by norm_num)
    _ ≤ 10 ^ 7 := Nat.pow_le_pow_right (by norm_num) hlen

lemma count_sum : ∀ l : List ℕ, (∀ a ∈ l, a < 10) →
    (l.map Nat.factorial).sum = ∑ d ∈ Finset.range 10, l.count d * d.factorial ∧
    l.length = ∑ d ∈ Finset.range 10, l.count d := by
  intro l
  induction l with
  | nil => simp
  | cons a l ih =>
    intro h
    have ha : a < 10 := h a (by simp)
    obtain ⟨ih1, ih2⟩ := ih (fun b hb => h b (by simp [hb]))
    have hmem : a ∈ Finset.range 10 := Finset.mem_range.mpr ha
    constructor
    · simp only [List.map_cons, List.sum_cons, List.count_cons, ih1]
      simp only [beq_iff_eq, add_mul, Finset.sum_add_distrib]
      rw [add_comm]
      congr 1
      rw [Finset.sum_eq_single a]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · intro hn; exact absurd hmem hn
    · simp only [List.length_cons, List.count_cons, ih2, Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_eq_single a]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · intro hn; exact absurd hmem hn

def V (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : ℕ) : ℕ :=
  c0 + c1 + 2 * c2 + 6 * c3 + 24 * c4 + 120 * c5 + 720 * c6 + 5040 * c7 + 40320 * c8 +
    362880 * c9

def leaf (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : ℕ) : Bool :=
  let v := V c0 c1 c2 c3 c4 c5 c6 c7 c8 c9
  let l := dl 7 v
  !(l.count 0 == c0 && l.count 1 == c1 && l.count 2 == c2 && l.count 3 == c3 &&
    l.count 4 == c4 && l.count 5 == c5 && l.count 6 == c6 && l.count 7 == c7 &&
    l.count 8 == c8 && l.count 9 == c9) ||
    (v == 0 || v == 1 || v == 2 || v == 145 || v == 40585)

def chk : Bool :=
  (List.range 8).all fun c0 =>
  (List.range (8 - c0)).all fun c1 =>
  (List.range (8 - c0 - c1)).all fun c2 =>
  (List.range (8 - c0 - c1 - c2)).all fun c3 =>
  (List.range (8 - c0 - c1 - c2 - c3)).all fun c4 =>
  (List.range (8 - c0 - c1 - c2 - c3 - c4)).all fun c5 =>
  (List.range (8 - c0 - c1 - c2 - c3 - c4 - c5)).all fun c6 =>
  (List.range (8 - c0 - c1 - c2 - c3 - c4 - c5 - c6)).all fun c7 =>
  (List.range (8 - c0 - c1 - c2 - c3 - c4 - c5 - c6 - c7)).all fun c8 =>
  (List.range (8 - c0 - c1 - c2 - c3 - c4 - c5 - c6 - c7 - c8)).all fun c9 =>
    leaf c0 c1 c2 c3 c4 c5 c6 c7 c8 c9

lemma chk_true : chk = true := by decide +kernel

lemma fixed_cases (x : ℕ) (hx : 0 < x) (h : f x = x) :
    x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 145 ∨ x = 40585 := by
  have hb := bound x hx h
  have hd := dl_eq 7 x hb
  set l := Nat.digits 10 x with hl
  have hlt : ∀ a ∈ l, a < 10 := fun a ha => Nat.digits_lt_base (by norm_num) ha
  obtain ⟨h1, h2⟩ := count_sum l hlt
  have hlen : l.length ≤ 7 := by
    by_contra hc
    rw [not_le] at hc
    have h3 : 10 ^ l.length ≤ 10 * x := Nat.base_pow_length_digits_le 10 x (by norm_num) hx.ne'
    have h4 : 10 ^ 8 ≤ 10 ^ l.length := Nat.pow_le_pow_right (by norm_num) hc
    omega
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h1 h2
  have hfx : f x = (l.map Nat.factorial).sum := rfl
  have hV : V (l.count 0) (l.count 1) (l.count 2) (l.count 3) (l.count 4) (l.count 5)
      (l.count 6) (l.count 7) (l.count 8) (l.count 9) = x := by
    rw [← h, hfx, h1]
    simp only [V, Nat.factorial]
    ring
  have hc := chk_true
  simp only [chk, List.all_eq_true, List.mem_range] at hc
  have hleaf := hc (l.count 0) (by omega) (l.count 1) (by omega) (l.count 2) (by omega)
    (l.count 3) (by omega) (l.count 4) (by omega) (l.count 5) (by omega) (l.count 6) (by omega)
    (l.count 7) (by omega) (l.count 8) (by omega) (l.count 9) (by omega)
  simp only [leaf, hV, hd] at hleaf
  simpa [or_assoc] using hleaf

theorem OMA.solution : type_of% @OMA.S_mo_457007.main := by
  intro x hx
  constructor
  · intro h
    rcases fixed_cases x hx h with h0 | h0
    · omega
    · exact h0
  · intro h
    rcases h with rfl | rfl | rfl | rfl
    all_goals (rw [f, ← dl_eq 7 _ (by norm_num)]; decide)
