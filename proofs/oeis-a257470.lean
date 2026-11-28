import OMAStatements.S_oeis_a257470
import Mathlib

namespace OMA.A257470Proof

open OMA.S_oeis_a257470

/-! ## The leader set `L = {o * 8 ^ c : o = 2 or o odd ≥ 3}` -/

def L (n : ℕ) : Prop := ∃ c o : ℕ, n = o * 8 ^ c ∧ (o = 2 ∨ (o % 2 = 1 ∧ 3 ≤ o))

noncomputable instance instDecL : DecidablePred L := Classical.decPred _

theorem L_odd {n : ℕ} (h : n % 2 = 1) (h3 : 3 ≤ n) : L n :=
  ⟨0, n, by simp, Or.inr ⟨h, h3⟩⟩

theorem L_two : L 2 := ⟨0, 2, by norm_num, Or.inl rfl⟩

theorem L_mul8 {m : ℕ} (h : L m) : L (8 * m) := by
  obtain ⟨c, o, rfl, ho⟩ := h
  exact ⟨c + 1, o, by ring, ho⟩

theorem L_two_le {n : ℕ} (h : L n) : 2 ≤ n := by
  obtain ⟨c, o, rfl, ho⟩ := h
  have h1 : 1 ≤ 8 ^ c := Nat.one_le_pow c 8 (by norm_num)
  have h2 : 2 ≤ o := by omega
  have h3 := Nat.mul_le_mul h2 h1
  omega

theorem L_of_mul8 {m : ℕ} (h : L (8 * m)) : L m := by
  obtain ⟨c, o, he, ho⟩ := h
  cases c with
  | zero =>
    rw [pow_zero, mul_one] at he
    exfalso
    omega
  | succ c =>
    refine ⟨c, o, ?_, ho⟩
    have h8 : 8 * m = 8 * (o * 8 ^ c) := by rw [he]; ring
    omega

theorem L_even {n : ℕ} (h : L n) (he : n % 2 = 0) : n = 2 ∨ ∃ m, n = 8 * m ∧ L m := by
  obtain ⟨c, o, rfl, ho⟩ := h
  cases c with
  | zero =>
    left
    rw [pow_zero, mul_one] at he ⊢
    omega
  | succ c =>
    right
    exact ⟨o * 8 ^ c, by ring, c, o, rfl, ho⟩

theorem L_cover : ∀ n : ℕ, 2 ≤ n → ∃ x, L x ∧ (n = x ∨ n = 2 * x ∨ n = 4 * x) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases (by omega : n % 2 = 1 ∨ n % 4 = 2 ∨ n % 8 = 4 ∨ n % 8 = 0) with h | h | h | h
    · exact ⟨n, L_odd h (by omega), Or.inl rfl⟩
    · by_cases h2 : n = 2
      · exact ⟨2, L_two, Or.inl h2⟩
      · exact ⟨n / 2, L_odd (by omega) (by omega), Or.inr (Or.inl (by omega))⟩
    · by_cases h4 : n = 4
      · exact ⟨2, L_two, Or.inr (Or.inl (by omega))⟩
      · exact ⟨n / 4, L_odd (by omega) (by omega), Or.inr (Or.inr (by omega))⟩
    · by_cases h8 : n = 8
      · exact ⟨2, L_two, Or.inr (Or.inr (by omega))⟩
      · obtain ⟨x, hx, hx'⟩ := ih (n / 8) (by omega) (by omega)
        exact ⟨8 * x, L_mul8 hx, by omega⟩

theorem L_not_dbl : ∀ x y : ℕ, L x → L y → (x = 2 * y ∨ x = 4 * y) → False := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro y hx hy hxy
    have hx2 := L_two_le hx
    have hy2 := L_two_le hy
    rcases L_even hx (by omega) with h | ⟨m, rfl, hm⟩
    · omega
    · have hm2 := L_two_le hm
      rcases L_even hy (by omega) with h' | ⟨m', rfl, hm'⟩
      · omega
      · exact ih m (by omega) m' hm hm' (by omega)

theorem L_ne_dbl {x y : ℕ} (hx : L x) (hy : L y) : x ≠ 2 * y :=
  fun h => L_not_dbl x y hx hy (Or.inl h)

theorem L_ne_quad {x y : ℕ} (hx : L x) (hy : L y) : x ≠ 4 * y :=
  fun h => L_not_dbl x y hx hy (Or.inr h)

/-! ## The increasing enumeration `ell` of `L` -/

noncomputable def ell : ℕ → ℕ
  | 0 => 2
  | k + 1 => if L (ell k + 1) then ell k + 1 else ell k + 2

theorem ell_zero : ell 0 = 2 := rfl

theorem ell_succ (k : ℕ) : ell (k + 1) = if L (ell k + 1) then ell k + 1 else ell k + 2 := rfl

theorem ell_cases (k : ℕ) :
    (ell (k + 1) = ell k + 1 ∧ L (ell k + 1)) ∨ (ell (k + 1) = ell k + 2 ∧ ¬ L (ell k + 1)) := by
  by_cases h : L (ell k + 1)
  · left
    exact ⟨by rw [ell_succ, if_pos h], h⟩
  · right
    exact ⟨by rw [ell_succ, if_neg h], h⟩

theorem ell_mem (k : ℕ) : L (ell k) := by
  induction k with
  | zero => exact L_two
  | succ k ih =>
    rcases ell_cases k with ⟨h, hL⟩ | ⟨h, hL⟩
    · rw [h]; exact hL
    · rw [h]
      have h2 := L_two_le ih
      have hev : (ell k + 1) % 2 = 0 := by
        by_contra hne
        exact hL (L_odd (by omega) (by omega))
      exact L_odd (by omega) (by omega)

theorem ell_two_le (k : ℕ) : 2 ≤ ell k := L_two_le (ell_mem k)

theorem ell_lt_succ (k : ℕ) : ell k < ell (k + 1) := by
  rcases ell_cases k with ⟨h, _⟩ | ⟨h, _⟩ <;> omega

theorem ell_succ_le (k : ℕ) : ell (k + 1) ≤ ell k + 2 := by
  rcases ell_cases k with ⟨h, _⟩ | ⟨h, _⟩ <;> omega

theorem ell_strictMono : StrictMono ell := strictMono_nat_of_lt_succ ell_lt_succ

theorem ell_inj {i j : ℕ} (h : ell i = ell j) : i = j := ell_strictMono.injective h

theorem ell_lt_iff {i j : ℕ} : ell i < ell j ↔ i < j := ell_strictMono.lt_iff_lt

theorem ell_one : ell 1 = 3 := by
  show ell (0 + 1) = 3
  rcases ell_cases 0 with ⟨h, _⟩ | ⟨h, hL⟩
  · have := ell_zero
    omega
  · exfalso
    apply hL
    rw [ell_zero]
    exact L_odd (by norm_num) (by norm_num)

theorem ell_bracket (m : ℕ) (hm : 2 ≤ m) : ∃ k, ell k ≤ m ∧ m < ell (k + 1) := by
  induction m, hm using Nat.le_induction with
  | base =>
    have h1 := ell_lt_succ 0
    have h0 := ell_zero
    exact ⟨0, by omega, by omega⟩
  | succ m hm ih =>
    obtain ⟨k, hk1, hk2⟩ := ih
    by_cases h : m + 1 < ell (k + 1)
    · exact ⟨k, by omega, h⟩
    · have := ell_lt_succ (k + 1)
      exact ⟨k + 1, by omega, by omega⟩

theorem ell_surj {m : ℕ} (hm : L m) : ∃ k, ell k = m := by
  obtain ⟨k, hk1, hk2⟩ := ell_bracket m (L_two_le hm)
  refine ⟨k, ?_⟩
  by_contra hne
  rcases ell_cases k with ⟨h, _⟩ | ⟨h, hL⟩
  · omega
  · have e : m = ell k + 1 := by omega
    rw [e] at hm
    exact hL hm

theorem ell_below {m k : ℕ} (hm : L m) (hlt : m < ell k) : ∃ j, j < k ∧ ell j = m := by
  obtain ⟨j, rfl⟩ := ell_surj hm
  exact ⟨j, ell_lt_iff.mp hlt, rfl⟩

/-! ## Counting `L` -/

theorem count_ell (k : ℕ) : Nat.count L (ell k) = k := by
  induction k with
  | zero =>
    have h0 : ¬ L 0 := fun h => by have := L_two_le h; omega
    have h1 : ¬ L 1 := fun h => by have := L_two_le h; omega
    have c1 : Nat.count L 1 = Nat.count L 0 := Nat.count_succ_eq_count_iff.mpr h0
    have c2 : Nat.count L 2 = Nat.count L 1 := Nat.count_succ_eq_count_iff.mpr h1
    have c0 : Nat.count L 0 = 0 := Nat.count_zero L
    rw [ell_zero]
    omega
  | succ k ih =>
    rcases ell_cases k with ⟨h, _⟩ | ⟨h, hL⟩
    · have c : Nat.count L (ell k + 1) = Nat.count L (ell k) + 1 :=
        Nat.count_succ_eq_succ_count_iff.mpr (ell_mem k)
      rw [h]
      omega
    · have c : Nat.count L (ell k + 1) = Nat.count L (ell k) + 1 :=
        Nat.count_succ_eq_succ_count_iff.mpr (ell_mem k)
      have c' : Nat.count L (ell k + 2) = Nat.count L (ell k + 1) :=
        Nat.count_succ_eq_count_iff.mpr hL
      rw [h]
      omega

theorem not_L_of_even {n : ℕ} (he : n % 2 = 0) (h2 : n ≠ 2) (h8 : n % 8 ≠ 0) : ¬ L n := by
  intro h
  rcases L_even h he with h' | ⟨t, ht, _⟩ <;> omega

theorem count_L_mul8 (m : ℕ) (hm : 1 ≤ m) : Nat.count L (8 * m) = 4 * m + Nat.count L m := by
  induction m, hm using Nat.le_induction with
  | base =>
    have h0 : ¬ L 0 := fun h => by have := L_two_le h; omega
    have h1 : ¬ L 1 := fun h => by have := L_two_le h; omega
    have h3 : L 3 := L_odd (by norm_num) (by norm_num)
    have h4 : ¬ L 4 := not_L_of_even (by norm_num) (by norm_num) (by norm_num)
    have h5 : L 5 := L_odd (by norm_num) (by norm_num)
    have h6 : ¬ L 6 := not_L_of_even (by norm_num) (by norm_num) (by norm_num)
    have h7 : L 7 := L_odd (by norm_num) (by norm_num)
    have c0 : Nat.count L 0 = 0 := Nat.count_zero L
    have c1 : Nat.count L 1 = Nat.count L 0 := Nat.count_succ_eq_count_iff.mpr h0
    have c2 : Nat.count L 2 = Nat.count L 1 := Nat.count_succ_eq_count_iff.mpr h1
    have c3 : Nat.count L 3 = Nat.count L 2 + 1 := Nat.count_succ_eq_succ_count_iff.mpr L_two
    have c4 : Nat.count L 4 = Nat.count L 3 + 1 := Nat.count_succ_eq_succ_count_iff.mpr h3
    have c5 : Nat.count L 5 = Nat.count L 4 := Nat.count_succ_eq_count_iff.mpr h4
    have c6 : Nat.count L 6 = Nat.count L 5 + 1 := Nat.count_succ_eq_succ_count_iff.mpr h5
    have c7 : Nat.count L 7 = Nat.count L 6 := Nat.count_succ_eq_count_iff.mpr h6
    have c8 : Nat.count L 8 = Nat.count L 7 + 1 := Nat.count_succ_eq_succ_count_iff.mpr h7
    show Nat.count L 8 = 4 * 1 + Nat.count L 1
    omega
  | succ m hm ih =>
    have hL1 : L (8 * m + 1) := L_odd (by omega) (by omega)
    have hL3 : L (8 * m + 3) := L_odd (by omega) (by omega)
    have hL5 : L (8 * m + 5) := L_odd (by omega) (by omega)
    have hL7 : L (8 * m + 7) := L_odd (by omega) (by omega)
    have hN2 : ¬ L (8 * m + 2) := not_L_of_even (by omega) (by omega) (by omega)
    have hN4 : ¬ L (8 * m + 4) := not_L_of_even (by omega) (by omega) (by omega)
    have hN6 : ¬ L (8 * m + 6) := not_L_of_even (by omega) (by omega) (by omega)
    have c2 : Nat.count L (8 * m + 2) = Nat.count L (8 * m + 1) + 1 :=
      Nat.count_succ_eq_succ_count_iff.mpr hL1
    have c3 : Nat.count L (8 * m + 3) = Nat.count L (8 * m + 2) := Nat.count_succ_eq_count_iff.mpr hN2
    have c4 : Nat.count L (8 * m + 4) = Nat.count L (8 * m + 3) + 1 :=
      Nat.count_succ_eq_succ_count_iff.mpr hL3
    have c5 : Nat.count L (8 * m + 5) = Nat.count L (8 * m + 4) := Nat.count_succ_eq_count_iff.mpr hN4
    have c6 : Nat.count L (8 * m + 6) = Nat.count L (8 * m + 5) + 1 :=
      Nat.count_succ_eq_succ_count_iff.mpr hL5
    have c7 : Nat.count L (8 * m + 7) = Nat.count L (8 * m + 6) := Nat.count_succ_eq_count_iff.mpr hN6
    have c8 : Nat.count L (8 * m + 8) = Nat.count L (8 * m + 7) + 1 :=
      Nat.count_succ_eq_succ_count_iff.mpr hL7
    rw [show 8 * (m + 1) = 8 * m + 8 by ring]
    by_cases hLm : L m
    · have c1 : Nat.count L (8 * m + 1) = Nat.count L (8 * m) + 1 :=
        Nat.count_succ_eq_succ_count_iff.mpr (L_mul8 hLm)
      have cm : Nat.count L (m + 1) = Nat.count L m + 1 := Nat.count_succ_eq_succ_count_iff.mpr hLm
      omega
    · have c1 : Nat.count L (8 * m + 1) = Nat.count L (8 * m) :=
        Nat.count_succ_eq_count_iff.mpr (fun h => hLm (L_of_mul8 h))
      have cm : Nat.count L (m + 1) = Nat.count L m := Nat.count_succ_eq_count_iff.mpr hLm
      omega

/-! ## The even leaders: `ell (P r) = 8 * ell r` with `P r = 4 * ell r + r` -/

noncomputable def P (r : ℕ) : ℕ := 4 * ell r + r

theorem ell_P (r : ℕ) : ell (P r) = 8 * ell r := by
  have hmem : L (8 * ell r) := L_mul8 (ell_mem r)
  obtain ⟨j, hj⟩ := ell_surj hmem
  have hc := count_ell j
  have h2 := ell_two_le r
  rw [hj, count_L_mul8 (ell r) (by omega), count_ell] at hc
  unfold P
  rw [hc]
  exact hj

theorem P_zero : P 0 = 8 := by
  unfold P
  have := ell_zero
  omega

theorem P_succ_ge (r : ℕ) : P r + 5 ≤ P (r + 1) := by
  unfold P
  have := ell_lt_succ r
  omega

theorem P_ge (r : ℕ) : r + 8 ≤ P r := by
  unfold P
  have := ell_two_le r
  omega

theorem P_gap (s : ℕ) : ∀ t, s < t → P s + 5 ≤ P t := by
  intro t
  induction t with
  | zero => intro h; omega
  | succ t ih =>
    intro h
    rcases (by omega : s < t ∨ s = t) with h' | h'
    · have := ih h'
      have := P_succ_ge t
      omega
    · rw [h']
      exact P_succ_ge t

theorem P_mono {s t : ℕ} (h : s ≤ t) : P s ≤ P t := by
  rcases (by omega : s = t ∨ s < t) with h' | h'
  · exact le_of_eq (by rw [h'])
  · have := P_gap s t h'
    omega

theorem ell_even_iff (i : ℕ) : ell i % 2 = 0 ↔ i = 0 ∨ ∃ r, i = P r := by
  constructor
  · intro h
    rcases L_even (ell_mem i) h with h2 | ⟨m, hm, hLm⟩
    · left
      exact ell_inj (h2.trans ell_zero.symm)
    · right
      obtain ⟨r, rfl⟩ := ell_surj hLm
      exact ⟨r, ell_inj (hm.trans (ell_P r).symm)⟩
  · rintro (h | ⟨r, h⟩)
    · rw [h]
      have := ell_zero
      omega
    · rw [h, ell_P]
      omega

theorem step_one_iff (t : ℕ) :
    ell (t + 1) = ell t + 1 ↔ (ell t % 2 = 0 ∨ ell (t + 1) % 2 = 0) := by
  rcases ell_cases t with ⟨h, _⟩ | ⟨h, hL⟩
  · constructor <;> intro hh <;> omega
  · have h2 := ell_two_le t
    have hev : (ell t + 1) % 2 = 0 := by
      by_contra hne
      exact hL (L_odd (by omega) (by omega))
    constructor <;> intro hh <;> omega

/-! ## The greedy sequence -/

theorem a_zero : a 0 = 0 := by
  rw [a]

theorem a_succ (n : ℕ) :
    a (n + 1) = sInf {m : ℕ | (∀ i ≤ n, a i ≠ m) ∧ 2 * min (a n) m ≤ max (a n) m} := by
  rw [a]

theorem sInf_eq_of {T : Set ℕ} {t0 : ℕ} (h1 : t0 ∈ T) (h2 : ∀ t < t0, t ∉ T) : sInf T = t0 := by
  have hle : sInf T ≤ t0 := Nat.sInf_le h1
  have hmem : sInf T ∈ T := Nat.sInf_mem ⟨t0, h1⟩
  rcases Nat.lt_or_ge (sInf T) t0 with hlt | hge
  · exact absurd hmem (h2 _ hlt)
  · omega

theorem a_greedy (n m0 : ℕ) (h1 : ∀ i ≤ n, a i ≠ m0) (h2 : 2 * min (a n) m0 ≤ max (a n) m0)
    (h3 : ∀ m < m0, (∃ i ≤ n, a i = m) ∨ ¬ (2 * min (a n) m ≤ max (a n) m)) :
    a (n + 1) = m0 := by
  rw [a_succ]
  apply sInf_eq_of
  · exact ⟨h1, h2⟩
  · intro m hm hmem
    have hmem' : (∀ i ≤ n, a i ≠ m) ∧ 2 * min (a n) m ≤ max (a n) m := hmem
    rcases h3 m hm with ⟨i, hi, hai⟩ | h
    · exact hmem'.1 i hi hai
    · exact h hmem'.2

theorem a_one : a 1 = 1 := by
  have h0 := a_zero
  have := a_greedy 0 1
    (by
      intro i hi
      have e : i = 0 := by omega
      rw [e]
      omega)
    (by omega)
    (by
      intro m hm
      left
      exact ⟨0, le_rfl, by omega⟩)
  exact this

/-- `m` is used after step `3k+1` (for the invariant). -/
def Cov (k m : ℕ) : Prop := m ≤ 1 ∨ ∃ j < k, m = ell j ∨ m = 2 * ell j ∨ m = 4 * ell j

def Inv (k : ℕ) : Prop :=
  (∀ m, (∃ i ≤ 3 * k + 1, a i = m) ↔ Cov k m) ∧
    2 * min (a (3 * k + 1)) (ell k) ≤ max (a (3 * k + 1)) (ell k)

theorem cov_of_lt {k m : ℕ} (h : m < ell k) : Cov k m := by
  by_cases hm : m ≤ 1
  · exact Or.inl hm
  · obtain ⟨x, hx, hmx⟩ := L_cover m (by omega)
    obtain ⟨j, hj, rfl⟩ := ell_below (k := k) hx (by omega)
    exact Or.inr ⟨j, hj, hmx⟩

theorem not_cov (k m : ℕ) (hm : m = ell k ∨ m = 2 * ell k ∨ m = 4 * ell k) : ¬ Cov k m := by
  rintro (h | ⟨j, hj, h⟩)
  · have := ell_two_le k
    omega
  · have hjk : ell j < ell k := ell_lt_iff.mpr hj
    have hLj := ell_mem j
    have hLk := ell_mem k
    rcases hm with rfl | rfl | rfl <;> rcases h with h | h | h <;>
      first
      | omega
      | exact L_ne_dbl hLk hLj (by omega)
      | exact L_ne_quad hLk hLj (by omega)

theorem inv_zero : Inv 0 := by
  have h0 := a_zero
  have h1 := a_one
  have e0 := ell_zero
  refine ⟨fun m => ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨i, hi, rfl⟩
    have : i = 0 ∨ i = 1 := by omega
    rcases this with rfl | rfl
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
  · rintro (h | ⟨j, hj, _⟩)
    · rcases (by omega : m = 0 ∨ m = 1) with rfl | rfl
      · exact ⟨0, by omega, h0⟩
      · exact ⟨1, by omega, h1⟩
    · exfalso
      omega
  · show 2 * min (a 1) (ell 0) ≤ max (a 1) (ell 0)
    omega

theorem inv_step (k : ℕ) (hI : Inv k) :
    a (3 * k + 2) = ell k ∧ a (3 * k + 3) = 2 * ell k ∧ a (3 * k + 4) = 4 * ell k ∧ Inv (k + 1) := by
  obtain ⟨hU, hc⟩ := hI
  have hk2 := ell_two_le k
  have hbelow : ∀ m, m < ell k → ∃ i ≤ 3 * k + 1, a i = m :=
    fun m hm => (hU m).mpr (cov_of_lt hm)
  have hnot : ∀ m, (m = ell k ∨ m = 2 * ell k ∨ m = 4 * ell k) → ∀ i ≤ 3 * k + 1, a i ≠ m :=
    fun m hm i hi hai => not_cov k m hm ((hU m).mp ⟨i, hi, hai⟩)
  have e2 : a (3 * k + 2) = ell k := by
    apply a_greedy (3 * k + 1) (ell k)
    · exact hnot _ (Or.inl rfl)
    · exact hc
    · intro m hm
      exact Or.inl (hbelow m hm)
  have e3 : a (3 * k + 3) = 2 * ell k := by
    apply a_greedy (3 * k + 2) (2 * ell k)
    · intro i hi hai
      rcases (by omega : i ≤ 3 * k + 1 ∨ i = 3 * k + 2) with h | h
      · exact hnot _ (Or.inr (Or.inl rfl)) i h hai
      · rw [h] at hai
        omega
    · omega
    · intro m hm
      by_cases hm1 : m < ell k
      · left
        obtain ⟨i, hi, hai⟩ := hbelow m hm1
        exact ⟨i, by omega, hai⟩
      · by_cases hm2 : m = ell k
        · left
          exact ⟨3 * k + 2, le_rfl, by omega⟩
        · right
          omega
  have e4 : a (3 * k + 4) = 4 * ell k := by
    apply a_greedy (3 * k + 3) (4 * ell k)
    · intro i hi hai
      rcases (by omega : i ≤ 3 * k + 1 ∨ i = 3 * k + 2 ∨ i = 3 * k + 3) with h | h | h
      · exact hnot _ (Or.inr (Or.inr rfl)) i h hai
      · rw [h] at hai
        omega
      · rw [h] at hai
        omega
    · omega
    · intro m hm
      by_cases hm1 : m < ell k
      · left
        obtain ⟨i, hi, hai⟩ := hbelow m hm1
        exact ⟨i, by omega, hai⟩
      · by_cases hm2 : m = ell k
        · left
          exact ⟨3 * k + 2, by omega, by omega⟩
        · by_cases hm3 : m = 2 * ell k
          · left
            exact ⟨3 * k + 3, le_rfl, by omega⟩
          · right
            omega
  refine ⟨e2, e3, e4, fun m => ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨i, hi, rfl⟩
    rcases (by omega : i ≤ 3 * k + 1 ∨ i = 3 * k + 2 ∨ i = 3 * k + 3 ∨ i = 3 * k + 4) with
      h | h | h | h
    · rcases (hU (a i)).mp ⟨i, h, rfl⟩ with h' | ⟨j, hj, h'⟩
      · exact Or.inl h'
      · exact Or.inr ⟨j, by omega, h'⟩
    · rw [h, e2]
      exact Or.inr ⟨k, by omega, Or.inl rfl⟩
    · rw [h, e3]
      exact Or.inr ⟨k, by omega, Or.inr (Or.inl rfl)⟩
    · rw [h, e4]
      exact Or.inr ⟨k, by omega, Or.inr (Or.inr rfl)⟩
  · rintro (h | ⟨j, hj, h⟩)
    · obtain ⟨i, hi, hai⟩ := (hU m).mpr (Or.inl h)
      exact ⟨i, by omega, hai⟩
    · rcases (by omega : j < k ∨ j = k) with hjk | hjk
      · obtain ⟨i, hi, hai⟩ := (hU m).mpr (Or.inr ⟨j, hjk, h⟩)
        exact ⟨i, by omega, hai⟩
      · rw [hjk] at h
        rcases h with h | h | h
        · exact ⟨3 * k + 2, by omega, by omega⟩
        · exact ⟨3 * k + 3, by omega, by omega⟩
        · exact ⟨3 * k + 4, by omega, by omega⟩
  · rw [show 3 * (k + 1) + 1 = 3 * k + 4 by ring]
    have := ell_succ_le k
    omega

theorem inv_all (k : ℕ) : Inv k := by
  induction k with
  | zero => exact inv_zero
  | succ k ih => exact (inv_step k ih).2.2.2

theorem a_lead (k : ℕ) : a (3 * k + 2) = ell k := (inv_step k (inv_all k)).1

theorem a_prev (k : ℕ) (hk : 0 < k) : a (3 * k - 1) = ell (k - 1) := by
  have h := a_lead (k - 1)
  rw [show 3 * (k - 1) + 2 = 3 * k - 1 by omega] at h
  exact h

/-! ## The set `S` -/

theorem mem_S_iff (k : ℕ) : k ∈ S ↔ 0 < k ∧ ell k = ell (k - 1) + 1 := by
  show (0 < k ∧ a (3 * k + 2) = a (3 * k - 1) + 1) ↔ _
  constructor
  · rintro ⟨hk, h⟩
    rw [a_lead, a_prev k hk] at h
    exact ⟨hk, h⟩
  · rintro ⟨hk, h⟩
    refine ⟨hk, ?_⟩
    rw [a_lead, a_prev k hk]
    exact h

theorem mem_S_iff' (k : ℕ) : k ∈ S ↔ k = 1 ∨ ∃ r, k = P r ∨ k = P r + 1 := by
  rw [mem_S_iff]
  constructor
  · rintro ⟨hk, h⟩
    obtain ⟨t, rfl⟩ : ∃ t, k = t + 1 := ⟨k - 1, by omega⟩
    rw [Nat.add_sub_cancel] at h
    rcases (step_one_iff t).mp h with h' | h'
    · rcases (ell_even_iff t).mp h' with h'' | ⟨r, hr⟩
      · left
        omega
      · right
        exact ⟨r, Or.inr (by omega)⟩
    · rcases (ell_even_iff (t + 1)).mp h' with h'' | ⟨r, hr⟩
      · exfalso
        omega
      · right
        exact ⟨r, Or.inl hr⟩
  · rintro (h | ⟨r, h | h⟩)
    · refine ⟨by omega, ?_⟩
      rw [h]
      show ell 1 = ell 0 + 1
      have := ell_one
      have := ell_zero
      omega
    · have hP := P_ge r
      refine ⟨by omega, ?_⟩
      obtain ⟨t, ht⟩ : ∃ t, P r = t + 1 := ⟨P r - 1, by omega⟩
      rw [h, ht, Nat.add_sub_cancel]
      apply (step_one_iff t).mpr
      right
      rw [← ht, ell_P]
      omega
    · refine ⟨by omega, ?_⟩
      rw [h, Nat.add_sub_cancel]
      apply (step_one_iff (P r)).mpr
      left
      rw [ell_P]
      omega

theorem one_mem_S : 1 ∈ S := (mem_S_iff' 1).mpr (Or.inl rfl)

theorem P_mem_S (r : ℕ) : P r ∈ S := (mem_S_iff' _).mpr (Or.inr ⟨r, Or.inl rfl⟩)

theorem P_succ_mem_S (r : ℕ) : P r + 1 ∈ S := (mem_S_iff' _).mpr (Or.inr ⟨r, Or.inr rfl⟩)

theorem not_mem_S_lt (x : ℕ) (h1 : x ≠ 1) (h2 : x < 8) : x ∉ S := by
  intro hx
  rcases (mem_S_iff' x).mp hx with h | ⟨r, h | h⟩
  · exact h1 h
  · have := P_ge r
    omega
  · have := P_ge r
    omega

theorem not_mem_S_between (r x : ℕ) (h1 : P r + 1 < x) (h2 : x < P (r + 1)) : x ∉ S := by
  intro hx
  have hr := P_ge r
  rcases (mem_S_iff' x).mp hx with h | ⟨t, h | h⟩
  · omega
  · rcases Nat.lt_or_ge t (r + 1) with ht | ht
    · have := P_mono (show t ≤ r by omega)
      omega
    · have := P_mono ht
      omega
  · rcases Nat.lt_or_ge t (r + 1) with ht | ht
    · have := P_mono (show t ≤ r by omega)
      omega
    · have := P_mono ht
      omega

/-! ## `Nat.nth` of a set with a known increasing enumeration -/

theorem nth_eq_of_strictMono {p : ℕ → Prop} {f : ℕ → ℕ} (hf : StrictMono f)
    (hp : ∀ x, p x ↔ ∃ n, f n = x) (n : ℕ) : Nat.nth p n = f n := by
  have hinf : (Set.ofPred p).Infinite :=
    Set.infinite_of_injective_forall_mem hf.injective (fun n => (hp (f n)).mpr ⟨n, rfl⟩)
  have hmono := Nat.nth_strictMono hinf
  have hrange : ∀ x, p x → ∃ m, Nat.nth p m = x := by
    intro x hx
    have hx' : x ∈ Set.range (Nat.nth p) := by
      rw [Nat.range_nth_of_infinite hinf]
      exact hx
    exact hx'
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases lt_trichotomy (Nat.nth p n) (f n) with h | h | h
    · obtain ⟨m, hm⟩ := (hp _).mp (Nat.nth_mem_of_infinite hinf n)
      have h' : f m < f n := by rw [hm]; exact h
      have hmn : m < n := hf.lt_iff_lt.mp h'
      have e1 := ih m hmn
      have e2 : Nat.nth p n = Nat.nth p m := hm.symm.trans e1.symm
      exact absurd (hmono.injective e2) (by omega)
    · exact h
    · obtain ⟨m, hm⟩ := hrange (f n) ((hp _).mpr ⟨n, rfl⟩)
      have h' : Nat.nth p m < Nat.nth p n := by rw [hm]; exact h
      have hmn : m < n := hmono.lt_iff_lt.mp h'
      have e1 := ih m hmn
      have e2 : f n = f m := hm.symm.trans e1
      exact absurd (hf.injective e2) (by omega)

/-! ## The enumeration of `S` -/

noncomputable def fS : ℕ → ℕ
  | 0 => 1
  | n + 1 => P (n / 2) + n % 2

theorem fS_odd (r : ℕ) : fS (2 * r + 1) = P r := by
  show P (2 * r / 2) + 2 * r % 2 = P r
  rw [show 2 * r / 2 = r by omega, show 2 * r % 2 = 0 by omega, Nat.add_zero]

theorem fS_even (r : ℕ) : fS (2 * r + 2) = P r + 1 := by
  show P ((2 * r + 1) / 2) + (2 * r + 1) % 2 = P r + 1
  rw [show (2 * r + 1) / 2 = r by omega, show (2 * r + 1) % 2 = 1 by omega]

theorem fS_lt_succ (n : ℕ) : fS n < fS (n + 1) := by
  rcases n with _ | t
  · show 1 < P 0 + 0
    have := P_zero
    omega
  · obtain ⟨r, hr | hr⟩ : ∃ r, t = 2 * r ∨ t = 2 * r + 1 := ⟨t / 2, by omega⟩
    · subst hr
      rw [fS_odd, show 2 * r + 1 + 1 = 2 * r + 2 by ring, fS_even]
      omega
    · subst hr
      rw [show 2 * r + 1 + 1 = 2 * r + 2 by ring, fS_even,
        show 2 * r + 2 + 1 = 2 * (r + 1) + 1 by ring, fS_odd]
      have := P_succ_ge r
      omega

theorem fS_strictMono : StrictMono fS := strictMono_nat_of_lt_succ fS_lt_succ

theorem mem_S_iff_fS (x : ℕ) : x ∈ S ↔ ∃ n, fS n = x := by
  rw [mem_S_iff']
  constructor
  · rintro (h | ⟨r, h | h⟩)
    · exact ⟨0, h.symm⟩
    · exact ⟨2 * r + 1, (fS_odd r).trans h.symm⟩
    · exact ⟨2 * r + 2, (fS_even r).trans h.symm⟩
  · rintro ⟨n, rfl⟩
    rcases n with _ | t
    · left
      rfl
    · obtain ⟨r, hr | hr⟩ : ∃ r, t = 2 * r ∨ t = 2 * r + 1 := ⟨t / 2, by omega⟩
      · subst hr
        right
        exact ⟨r, Or.inl (fS_odd r)⟩
      · subst hr
        right
        refine ⟨r, Or.inr ?_⟩
        rw [show 2 * r + 1 + 1 = 2 * r + 2 by ring]
        exact fS_even r

theorem s_eq (n : ℕ) : s n = fS n := nth_eq_of_strictMono fS_strictMono mem_S_iff_fS n

theorem S_infinite : S.Infinite :=
  Set.infinite_of_injective_forall_mem fS_strictMono.injective
    (fun n => (mem_S_iff_fS _).mpr ⟨n, rfl⟩)

/-! ## `D` and `E` -/

theorem D_even (k : ℕ) (hk : 0 < k) : D (2 * k) = 1 := by
  obtain ⟨r, rfl⟩ : ∃ r, k = r + 1 := ⟨k - 1, by omega⟩
  show s (2 * (r + 1)) - s (2 * (r + 1) - 1) = 1
  rw [show 2 * (r + 1) - 1 = 2 * r + 1 by omega, show 2 * (r + 1) = 2 * r + 2 by ring, s_eq, s_eq,
    fS_even, fS_odd]
  omega

theorem E_def (k : ℕ) : E k = s (2 * k + 1) - s (2 * k) := by
  show s (2 * k + 1) - s (2 * k + 1 - 1) = _
  rw [show 2 * k + 1 - 1 = 2 * k by omega]

theorem E_val (k : ℕ) (hk : 0 < k) : E k = 4 * (ell k - ell (k - 1)) := by
  obtain ⟨r, rfl⟩ : ∃ r, k = r + 1 := ⟨k - 1, by omega⟩
  rw [E_def, show 2 * (r + 1) = 2 * r + 2 by ring, s_eq, s_eq, show 2 * r + 2 + 1 = 2 * (r + 1) + 1 by ring,
    fS_odd, fS_even, Nat.add_sub_cancel]
  unfold P
  omega

theorem E_cases (k : ℕ) (hk : 0 < k) : (E k = 4 ∧ k ∈ S) ∨ (E k = 8 ∧ k ∉ S) := by
  rw [E_val k hk, mem_S_iff]
  obtain ⟨t, rfl⟩ : ∃ t, k = t + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  rcases ell_cases t with ⟨h, _⟩ | ⟨h, _⟩
  · left
    exact ⟨by omega, by omega, h⟩
  · right
    refine ⟨by omega, ?_⟩
    rintro ⟨_, h'⟩
    omega

theorem E_eq4_iff (k : ℕ) (hk : 0 < k) : E k = 4 ↔ k ∈ S := by
  rcases E_cases k hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨fun _ => h2, fun _ => h1⟩
  · exact ⟨fun h => by omega, fun h => absurd h h2⟩

theorem E_eq8_iff (k : ℕ) (hk : 0 < k) : E k = 8 ↔ k ∉ S := by
  rcases E_cases k hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨fun h => by omega, fun h => absurd h2 h⟩
  · exact ⟨fun _ => h2, fun _ => h1⟩

/-! ## Maximal blocks of pairs -/

theorem inPairs_of (f : ℕ → ℕ) (v lo : ℕ) (Q : ℕ → ℕ) (hQ : ∀ r, Q r + 3 ≤ Q (r + 1))
    (hQ0 : lo + 1 ≤ Q 0) (hf : ∀ k, lo ≤ k → (f k = v ↔ ∃ r, k = Q r ∨ k = Q r + 1)) :
    InPairs f v lo := by
  have hgap : ∀ s t, s < t → Q s + 3 ≤ Q t := by
    intro s t
    induction t with
    | zero => intro h; omega
    | succ t ih =>
      intro h
      rcases (by omega : s < t ∨ s = t) with h' | h'
      · have := ih h'
        have := hQ t
        omega
      · rw [h']
        exact hQ t
  have hmono : ∀ s t, s ≤ t → Q s ≤ Q t := by
    intro s t h
    rcases (by omega : s = t ∨ s < t) with h' | h'
    · exact le_of_eq (by rw [h'])
    · have := hgap s t h'
      omega
  have hQlo : ∀ r, lo + 1 ≤ Q r := fun r => le_trans hQ0 (hmono 0 r (Nat.zero_le r))
  have hW2 : ∀ r t, Q r + 2 = Q t ∨ Q r + 2 = Q t + 1 → False := by
    intro r t h
    rcases Nat.lt_or_ge r t with hrt | hrt
    · have := hgap r t hrt
      omega
    · have := hmono t r hrt
      omega
  have hWm : ∀ r t, Q r - 1 = Q t ∨ Q r - 1 = Q t + 1 → False := by
    intro r t h
    have := hQlo r
    rcases Nat.lt_or_ge t r with htr | htr
    · have := hgap t r htr
      omega
    · have := hmono r t htr
      omega
  refine ⟨?_, ?_⟩
  · intro k hk hfk
    obtain ⟨r, hr⟩ := (hf k hk).mp hfk
    have hlo := hQlo r
    refine ⟨Q r, Q r + 1, by omega, by omega, by omega, by omega, ?_, ?_, ?_⟩
    · intro t ht1 ht2
      exact (hf t (by omega)).mpr ⟨r, by omega⟩
    · right
      intro hv
      obtain ⟨t, ht⟩ := (hf (Q r - 1) (by omega)).mp hv
      exact hWm r t ht
    · intro hv
      obtain ⟨t, ht⟩ := (hf (Q r + 1 + 1) (by omega)).mp hv
      exact hW2 r t (by omega)
  · rintro i j ⟨hi, hij, hall, hleft, hright⟩
    have hfi : f i = v := hall i le_rfl hij
    obtain ⟨r, hr | hr⟩ := (hf i hi).mp hfi
    · have hlo := hQlo r
      have h1 : f (Q r + 1) = v := (hf _ (by omega)).mpr ⟨r, Or.inr rfl⟩
      have h2 : f (Q r + 2) ≠ v := by
        intro hv
        obtain ⟨t, ht⟩ := (hf _ (by omega)).mp hv
        exact hW2 r t ht
      rcases (by omega : j = i ∨ j = i + 1 ∨ i + 2 ≤ j) with hj | hj | hj
      · rw [hj, hr] at hright
        exact absurd h1 hright
      · exact hj
      · have := hall (Q r + 2) (by omega) (by omega)
        exact absurd this h2
    · exfalso
      have hlo := hQlo r
      rcases hleft with hl | hl
      · omega
      · apply hl
        rw [show i - 1 = Q r by omega]
        exact (hf _ (by omega)).mpr ⟨r, Or.inl rfl⟩

/-! ## Runs of 8's -/

theorem runStart_iff (k : ℕ) : RunStart k ↔ k = 2 ∨ ∃ r, k = P r + 2 := by
  constructor
  · rintro ⟨hk, h8, h1⟩
    have hkS : k ∉ S := (E_eq8_iff k (by omega)).mp h8
    have hk2 : 2 ≤ k := by
      by_contra hlt
      have e : k = 1 := by omega
      rw [e] at hkS
      exact hkS one_mem_S
    rcases h1 with h1 | h1
    · exfalso
      omega
    · have hk1S : k - 1 ∈ S := by
        by_contra hn
        exact h1 ((E_eq8_iff (k - 1) (by omega)).mpr hn)
      rcases (mem_S_iff' (k - 1)).mp hk1S with h | ⟨r, h | h⟩
      · left
        omega
      · exfalso
        apply hkS
        rw [show k = P r + 1 by omega]
        exact P_succ_mem_S r
      · right
        exact ⟨r, by omega⟩
  · rintro (h | ⟨r, h⟩)
    · rw [h]
      refine ⟨by norm_num, (E_eq8_iff 2 (by norm_num)).mpr (not_mem_S_lt 2 (by norm_num) (by norm_num)),
        Or.inr ?_⟩
      show ¬ (E 1 = 8)
      rw [E_eq8_iff 1 (by norm_num)]
      exact fun h => h one_mem_S
    · rw [h]
      have hg := P_succ_ge r
      refine ⟨by omega, (E_eq8_iff (P r + 2) (by omega)).mpr ?_, Or.inr ?_⟩
      · exact not_mem_S_between r (P r + 2) (by omega) (by omega)
      · rw [show P r + 2 - 1 = P r + 1 by omega, ne_eq, E_eq8_iff (P r + 1) (by omega)]
        exact fun h => h (P_succ_mem_S r)

noncomputable def gR : ℕ → ℕ
  | 0 => 2
  | r + 1 => P r + 2

theorem gR_strictMono : StrictMono gR := by
  apply strictMono_nat_of_lt_succ
  intro n
  rcases n with _ | r
  · show 2 < P 0 + 2
    have := P_zero
    omega
  · show P r + 2 < P (r + 1) + 2
    have := P_succ_ge r
    omega

theorem runStart_iff_gR (x : ℕ) : RunStart x ↔ ∃ n, gR n = x := by
  rw [runStart_iff]
  constructor
  · rintro (h | ⟨r, h⟩)
    · exact ⟨0, h.symm⟩
    · exact ⟨r + 1, h.symm⟩
  · rintro ⟨n, rfl⟩
    rcases n with _ | r
    · left
      rfl
    · right
      exact ⟨r, rfl⟩

theorem nth_runStart (n : ℕ) : Nat.nth RunStart n = gR n :=
  nth_eq_of_strictMono gR_strictMono runStart_iff_gR n

theorem R_one : R 1 = 6 := by
  unfold R
  rw [show (1 : ℕ) - 1 = 0 by norm_num, nth_runStart]
  apply sInf_eq_of
  · show ¬ (E 8 = 8)
    rw [E_eq8_iff 8 (by norm_num)]
    have h8 := P_mem_S 0
    rw [P_zero] at h8
    exact fun h => h h8
  · intro t ht hmem
    apply hmem
    show E (2 + t) = 8
    rw [E_eq8_iff (2 + t) (by omega)]
    exact not_mem_S_lt (2 + t) (by omega) (by omega)

theorem R_succ_succ (r : ℕ) : R (r + 2) = P (r + 1) - P r - 2 := by
  unfold R
  rw [show r + 2 - 1 = r + 1 by omega, nth_runStart]
  have hg := P_succ_ge r
  have hP := P_ge r
  apply sInf_eq_of
  · show ¬ (E (P r + 2 + (P (r + 1) - P r - 2)) = 8)
    rw [show P r + 2 + (P (r + 1) - P r - 2) = P (r + 1) by omega, E_eq8_iff (P (r + 1)) (by omega)]
    exact fun h => h (P_mem_S (r + 1))
  · intro t ht hmem
    apply hmem
    show E (P r + 2 + t) = 8
    rw [E_eq8_iff (P r + 2 + t) (by omega)]
    exact not_mem_S_between r (P r + 2 + t) (by omega) (by omega)

theorem R_val (j : ℕ) (hj : 2 ≤ j) : (R j = 3 ∧ j - 1 ∈ S) ∨ (R j = 7 ∧ j - 1 ∉ S) := by
  obtain ⟨r, rfl⟩ : ∃ r, j = r + 2 := ⟨j - 2, by omega⟩
  rw [R_succ_succ, show r + 2 - 1 = r + 1 by omega]
  have hlt := ell_lt_succ r
  rcases E_cases (r + 1) (by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    refine ⟨?_, h2⟩
    rw [E_val (r + 1) (by omega), Nat.add_sub_cancel] at h1
    unfold P
    omega
  · right
    refine ⟨?_, h2⟩
    rw [E_val (r + 1) (by omega), Nat.add_sub_cancel] at h1
    unfold P
    omega

/-! ## The four conjectures -/

theorem main_proof :
    (∀ k, 0 < k → a (3 * k + 2) = a (3 * k - 1) + 2 ∨ a (3 * k + 2) = a (3 * k - 1) + 1) ∧
    (S.Infinite ∧ ∀ k, 0 < k → D (2 * k) = 1) ∧
    ((∀ k, 0 < k → E k = 4 ∨ E k = 8) ∧ E 1 = 4 ∧ E 2 ≠ 4 ∧ InPairs E 4 2) ∧
    ({k | RunStart k}.Infinite ∧ R 1 = 6 ∧ R 2 = 3 ∧ (∀ j, 3 ≤ j → R j = 3 ∨ R j = 7) ∧
      InPairs R 3 3 ∧ ∀ j, ∃ j', j < j' ∧ R j' = 3) := by
  refine ⟨?_, ⟨S_infinite, D_even⟩, ?_, ?_⟩
  · -- (i)
    intro k hk
    rw [a_lead, a_prev k hk]
    obtain ⟨t, rfl⟩ : ∃ t, k = t + 1 := ⟨k - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    rcases ell_cases t with ⟨h, _⟩ | ⟨h, _⟩
    · right
      exact h
    · left
      exact h
  · -- (iii)
    refine ⟨fun k hk => ?_, (E_eq4_iff 1 (by norm_num)).mpr one_mem_S, ?_, ?_⟩
    · rcases E_cases k hk with ⟨h, _⟩ | ⟨h, _⟩
      · exact Or.inl h
      · exact Or.inr h
    · rw [ne_eq, E_eq4_iff 2 (by norm_num)]
      exact not_mem_S_lt 2 (by norm_num) (by norm_num)
    · refine inPairs_of E 4 2 P (fun r => by have := P_succ_ge r; omega)
        (by have := P_zero; omega) ?_
      intro k hk
      rw [E_eq4_iff k (by omega), mem_S_iff']
      constructor
      · rintro (h | h)
        · exfalso
          omega
        · exact h
      · intro h
        exact Or.inr h
  · -- (iv)
    refine ⟨?_, R_one, ?_, ?_, ?_, ?_⟩
    · exact Set.infinite_of_injective_forall_mem gR_strictMono.injective
        (fun n => (runStart_iff_gR _).mpr ⟨n, rfl⟩)
    · rcases R_val 2 le_rfl with ⟨h, _⟩ | ⟨_, h⟩
      · exact h
      · exact absurd one_mem_S h
    · intro j hj
      rcases R_val j (by omega) with ⟨h, _⟩ | ⟨h, _⟩
      · exact Or.inl h
      · exact Or.inr h
    · refine inPairs_of R 3 3 (fun r => P r + 1) ?_ ?_ ?_
      · intro r
        show P r + 1 + 3 ≤ P (r + 1) + 1
        have := P_succ_ge r
        omega
      · show 3 + 1 ≤ P 0 + 1
        have := P_zero
        omega
      · show ∀ k, 3 ≤ k → (R k = 3 ↔ ∃ r, k = P r + 1 ∨ k = P r + 1 + 1)
        intro k hk
        constructor
        · intro h
          rcases R_val k (by omega) with ⟨_, hS⟩ | ⟨h7, _⟩
          · rcases (mem_S_iff' (k - 1)).mp hS with h1 | ⟨r, h1 | h1⟩
            · exfalso
              omega
            · exact ⟨r, by omega⟩
            · exact ⟨r, by omega⟩
          · exfalso
            omega
        · rintro ⟨r, hr⟩
          rcases R_val k (by omega) with ⟨h3, _⟩ | ⟨_, hS⟩
          · exact h3
          · exfalso
            apply hS
            rcases hr with hr | hr
            · rw [show k - 1 = P r by omega]
              exact P_mem_S r
            · rw [show k - 1 = P r + 1 by omega]
              exact P_succ_mem_S r
    · intro j
      have hP := P_ge j
      refine ⟨P j + 1, by omega, ?_⟩
      rcases R_val (P j + 1) (by omega) with ⟨h, _⟩ | ⟨_, hS⟩
      · exact h
      · exfalso
        apply hS
        rw [Nat.add_sub_cancel]
        exact P_mem_S j

end OMA.A257470Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a257470.main := OMA.A257470Proof.main_proof
