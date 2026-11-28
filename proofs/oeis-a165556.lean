import OMAStatements.S_oeis_a165556
import Mathlib

namespace LtsA165556

def ins (r q : ℕ) : ℕ := if q < r then q else q + 1

def f : ℕ → ℕ → Bool → ℕ
  | 0, _, _ => 0
  | 1, _, _ => 0
  | S + 2, w, true => (f (S + 1) (if 2 ≤ w then w - 2 else if w = 1 then 0 else S) false + 2) % (S + 2)
  | S + 2, w, false => ins ((w + S) % (S + 2)) (f (S + 1) (((w + S) % (S + 2)) % (S + 1)) true)

lemma f_lt : ∀ S w t, f (S + 1) w t < S + 1 := by
  intro S
  induction S with
  | zero => intro w t; simp [f]
  | succ S ih =>
    intro w t
    cases t with
    | true => simp only [f]; exact Nat.mod_lt _ (by omega)
    | false =>
      simp only [f]
      have h1 := ih (((w + S) % (S + 2)) % (S + 1)) true
      have h2 : (w + S) % (S + 2) < S + 2 := Nat.mod_lt _ (by omega)
      unfold ins; split_ifs <;> omega

lemma modfix (a b n : ℕ) (h : (a < n ∧ a = b) ∨ (a = n ∧ b = 0)) : a % n = b := by
  rcases h with ⟨h1, rfl⟩ | ⟨rfl, rfl⟩
  · exact Nat.mod_eq_of_lt h1
  · exact Nat.mod_self _

lemma stepP (T w : ℕ) (h4 : 4 ≤ w) (hw : w ≤ T + 3) :
    f (T + 3) w true = (ins (w - 4) (f (T + 1) (w - 4) true) + 2) % (T + 3) := by
  have h1 : (w - 2 + T) % (T + 2) = w - 4 := by
    rw [show w - 2 + T = (w - 4) + (T + 2) by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have h2 : (w - 4) % (T + 1) = w - 4 := Nat.mod_eq_of_lt (by omega)
  show (f (T + 2) (if 2 ≤ w then w - 2 else if w = 1 then 0 else T + 1) false + 2) % (T + 3) = _
  rw [if_pos (by omega)]
  show (ins ((w - 2 + T) % (T + 2)) (f (T + 1) (((w - 2 + T) % (T + 2)) % (T + 1)) true) + 2) % (T + 3) = _
  rw [h1, h2]

def Phi (j S w q : ℕ) : ℕ :=
  if q + 4 * j < w then 2 * j + q
  else if q + 3 * j < w then w - 2 * j + 1 + 2 * (q + 4 * j - w)
  else if q + 3 * j < S then q + 3 * j
  else 2 * (q + 3 * j - S)

lemma iter : ∀ j S w, 4 * j ≤ w → w ≤ S → 2 * j + 1 ≤ S →
    f S w true = Phi j S w (f (S - 2 * j) (w - 4 * j) true) := by
  intro j
  induction j with
  | zero =>
    intro S w _ _ hS
    obtain ⟨T, rfl⟩ : ∃ T, S = T + 1 := ⟨S - 1, by omega⟩
    have := f_lt T w true
    simp only [Nat.mul_zero, Nat.sub_zero]
    unfold Phi; split_ifs <;> omega
  | succ j ih =>
    intro S w h1 h2 h3
    obtain ⟨T, rfl⟩ : ∃ T, S = T + 3 := ⟨S - 3, by omega⟩
    rw [stepP T w (by omega) h2, ih (T + 1) (w - 4) (by omega) (by omega) (by omega)]
    rw [show T + 3 - 2 * (j + 1) = T + 1 - 2 * j by omega, show w - 4 * (j + 1) = w - 4 - 4 * j by omega]
    obtain ⟨U, hU⟩ : ∃ U, T + 1 - 2 * j = U + 1 := ⟨T - 2 * j, by omega⟩
    have hq := f_lt U (w - 4 - 4 * j) true
    rw [← hU] at hq
    generalize f (T + 1 - 2 * j) (w - 4 - 4 * j) true = q at hq ⊢
    apply modfix
    unfold Phi ins
    split_ifs <;> omega

lemma stepA (T : ℕ) : f (T + 3) 3 true = (f (T + 1) 0 true + 2) % (T + 3) := by
  have h1 : (1 + T) % (T + 2) = T + 1 := by rw [Nat.mod_eq_of_lt (show 1 + T < T + 2 by omega)]; omega
  show (f (T + 2) (if 2 ≤ 3 then 3 - 2 else if 3 = 1 then 0 else T + 1) false + 2) % (T + 3) = _
  rw [if_pos (by omega)]
  show (ins ((1 + T) % (T + 2)) (f (T + 1) (((1 + T) % (T + 2)) % (T + 1)) true) + 2) % (T + 3) = _
  rw [h1, Nat.mod_self]
  have := f_lt T 0 true
  unfold ins; rw [if_pos this]

lemma stepB (T w : ℕ) (hw : w = 1 ∨ w = 2) :
    f (T + 4) w true = (ins (T + 1) (f (T + 2) (T + 1) true) + 2) % (T + 4) := by
  have h1 : (0 + (T + 1)) % (T + 3) = T + 1 := by rw [Nat.mod_eq_of_lt (show 0 + (T + 1) < T + 3 by omega)]; omega
  have h2 : (T + 1) % (T + 2) = T + 1 := Nat.mod_eq_of_lt (by omega)
  show (f (T + 3) (if 2 ≤ w then w - 2 else if w = 1 then 0 else T + 2) false + 2) % (T + 4) = _
  rw [show (if 2 ≤ w then w - 2 else if w = 1 then 0 else T + 2) = 0 by split_ifs <;> omega]
  show (ins ((0 + (T + 1)) % (T + 3)) (f (T + 2) (((0 + (T + 1)) % (T + 3)) % (T + 2)) true) + 2) % (T + 4) = _
  rw [h1, h2]

def D (n : ℕ) : ℕ := f n 0 true
def E (n : ℕ) : ℕ := f n (n - 1) true

lemma f_SS (S : ℕ) : f (S + 2) (S + 2) true = f (S + 2) 0 true := by
  simp [f]

lemma D_lt (n : ℕ) (h : 1 ≤ n) : D n < n := by
  obtain ⟨T, rfl⟩ : ∃ T, n = T + 1 := ⟨n - 1, by omega⟩
  exact f_lt T 0 true
lemma E_lt (n : ℕ) (h : 1 ≤ n) : E n < n := by
  obtain ⟨T, rfl⟩ : ∃ T, n = T + 1 := ⟨n - 1, by omega⟩
  exact f_lt T _ true

-- maps, k ≥ 1
lemma M1 (k : ℕ) (hk : 1 ≤ k) : D (4 * k) = Phi k (4 * k) (4 * k) (D (2 * k)) := by
  unfold D
  obtain ⟨T, hT⟩ : ∃ T, 4 * k = T + 2 := ⟨4 * k - 2, by omega⟩
  rw [hT, ← f_SS, iter k (T + 2) (T + 2) (by omega) le_rfl (by omega)]
  rw [show T + 2 - 2 * k = 2 * k by omega, show T + 2 - 4 * k = 0 by omega]

lemma M2 (k : ℕ) (hk : 1 ≤ k) : Even (D (4 * k + 1)) := by
  unfold D
  obtain ⟨T, hT⟩ : ∃ T, 4 * k + 1 = T + 2 := ⟨4 * k - 1, by omega⟩
  rw [hT, ← f_SS, iter k (T + 2) (T + 2) (by omega) le_rfl (by omega)]
  rw [show T + 2 - 2 * k = 2 * k + 1 by omega, show T + 2 - 4 * k = 1 by omega]
  have hq := f_lt (2 * k) 1 true
  generalize f (2 * k + 1) 1 true = q at hq ⊢
  unfold Phi
  split_ifs <;> (apply Nat.even_iff.mpr; omega)

lemma M3 (k : ℕ) (hk : 1 ≤ k) : D (4 * k + 2) =
    Phi k (4 * k + 2) (4 * k + 2) ((ins (2 * k - 1) (E (2 * k)) + 2) % (2 * k + 2)) := by
  unfold D E
  rw [show 4 * k + 2 = (4 * k) + 2 from rfl, ← f_SS, iter k (4 * k + 2) (4 * k + 2) (by omega) le_rfl (by omega)]
  rw [show 4 * k + 2 - 2 * k = (2 * k - 2) + 4 by omega, show 4 * k + 2 - 4 * k = 2 by omega,
    stepB (2 * k - 2) 2 (by omega)]
  rw [show 2 * k - 2 + 1 = 2 * k - 1 by omega, show 2 * k - 2 + 2 = 2 * k by omega,
    show 2 * k - 2 + 4 = 2 * k + 2 by omega]

lemma M4 (k : ℕ) (hk : 1 ≤ k) : Even (D (4 * k + 3)) := by
  unfold D
  rw [show 4 * k + 3 = (4 * k + 1) + 2 from rfl, ← f_SS, iter k (4 * k + 1 + 2) (4 * k + 1 + 2) (by omega) le_rfl (by omega)]
  rw [show 4 * k + 1 + 2 - 2 * k = (2 * k) + 3 by omega, show 4 * k + 1 + 2 - 4 * k = 3 by omega,
    stepA (2 * k)]
  have hq := f_lt (2 * k) 0 true
  generalize f (2 * k + 1) 0 true = q at hq ⊢
  rw [Nat.mod_eq_of_lt (show q + 2 < 2 * k + 3 by omega)]
  unfold Phi
  split_ifs <;> (apply Nat.even_iff.mpr; omega)

lemma M5 (k : ℕ) (hk : 1 ≤ k) : E (4 * k) =
    Phi (k - 1) (4 * k) (4 * k - 1) ((D (2 * k) + 2) % (2 * k + 2)) := by
  unfold D E
  rw [iter (k - 1) (4 * k) (4 * k - 1) (by omega) (by omega) (by omega)]
  rw [show 4 * k - 2 * (k - 1) = (2 * k - 1) + 3 by omega, show 4 * k - 1 - 4 * (k - 1) = 3 by omega,
    stepA (2 * k - 1)]
  rw [show 2 * k - 1 + 1 = 2 * k by omega, show 2 * k - 1 + 3 = 2 * k + 2 by omega]

lemma M6 (k : ℕ) (hk : 1 ≤ k) : E (4 * k + 2) =
    Phi k (4 * k + 2) (4 * k + 1) ((ins (2 * k - 1) (E (2 * k)) + 2) % (2 * k + 2)) := by
  unfold E
  rw [show 4 * k + 2 - 1 = 4 * k + 1 by omega,
    iter k (4 * k + 2) (4 * k + 1) (by omega) (by omega) (by omega)]
  rw [show 4 * k + 2 - 2 * k = (2 * k - 2) + 4 by omega, show 4 * k + 1 - 4 * k = 1 by omega,
    stepB (2 * k - 2) 1 (by omega)]
  rw [show 2 * k - 2 + 1 = 2 * k - 1 by omega, show 2 * k - 2 + 2 = 2 * k by omega,
    show 2 * k - 2 + 4 = 2 * k + 2 by omega]

lemma log2_double (m : ℕ) (h : 1 ≤ m) : Nat.log 2 (2 * m) = Nat.log 2 m + 1 := by
  rw [Nat.log_of_one_lt_of_le (by norm_num) (by omega)]; congr 2; omega
lemma log2_double1 (m : ℕ) (h : 1 ≤ m) : Nat.log 2 (2 * m + 1) = Nat.log 2 m + 1 := by
  rw [Nat.log_of_one_lt_of_le (by norm_num) (by omega)]; congr 2; omega

/-- invariant for m = 2k -/
lemma inv : ∀ k, 1 ≤ k → D (2 * k) ≠ k ∧ (k ≤ D (2 * k) ↔ Even (Nat.log 2 (2 * k))) ∧
    (k ≤ E (2 * k) ↔ Even (Nat.log 2 (2 * k))) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.lt_or_ge k 2 with h2 | h2
    · obtain rfl : k = 1 := by omega
      refine ⟨by decide, ?_, ?_⟩
      · rw [show Nat.log 2 (2 * 1) = 1 by norm_num]; decide
      · rw [show Nat.log 2 (2 * 1) = 1 by norm_num]; decide
    obtain ⟨c, hc | hc⟩ : ∃ c, k = 2 * c ∨ k = 2 * c + 1 := ⟨k / 2, by omega⟩
    · subst hc
      obtain ⟨i1, i2, i3⟩ := ih c (by omega) (by omega)
      have hl : Nat.log 2 (2 * (2 * c)) = Nat.log 2 (2 * c) + 1 := log2_double _ (by omega)
      rw [hl, Nat.even_add_one, ← i2]
      have hq := D_lt (2 * c) (by omega)
      rw [show 2 * (2 * c) = 4 * c by ring, M1 c (by omega), M5 c (by omega)]
      generalize D (2 * c) = q at hq i1 ⊢
      have hmod : (q + 2) % (2 * c + 2) = if q + 2 < 2 * c + 2 then q + 2 else 0 := by
        split_ifs with h
        · exact Nat.mod_eq_of_lt h
        · rw [show q + 2 = 2 * c + 2 by omega, Nat.mod_self]
      rw [hmod]
      unfold Phi
      refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega
    · subst hc
      obtain ⟨i1, i2, i3⟩ := ih c (by omega) (by omega)
      have hl : Nat.log 2 (2 * (2 * c + 1)) = Nat.log 2 (2 * c) + 1 := by
        rw [log2_double _ (by omega), log2_double1 _ (by omega), log2_double _ (by omega)]
      rw [hl, Nat.even_add_one, ← i3]
      have hq := E_lt (2 * c) (by omega)
      rw [show 2 * (2 * c + 1) = 4 * c + 2 by ring, M3 c (by omega), M6 c (by omega)]
      generalize E (2 * c) = q at hq ⊢
      unfold ins
      have hmod : ∀ x, x < 2 * c + 1 → (x + 2) % (2 * c + 2) = if x + 2 < 2 * c + 2 then x + 2 else 0 := by
        intro x hx
        split_ifs with h
        · exact Nat.mod_eq_of_lt h
        · rw [show x + 2 = 2 * c + 2 by omega, Nat.mod_self]
      split_ifs with hh
      · rw [hmod q (by omega)]; unfold Phi; refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega
      · rw [hmod (q + 1) (by omega)]; unfold Phi; refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega

/-- parity of D -/
lemma D_even_iff (n : ℕ) (hn : 1 ≤ n) :
    Even (D n) ↔ (¬ Even n ∨ ¬ Even (Nat.log 2 (n + 1))) := by
  rcases Nat.lt_or_ge n 4 with h4 | h4
  · interval_cases n
    · simp [D, f, Nat.even_iff]
    · rw [show Nat.log 2 (2 + 1) = 1 by norm_num]; simp [D, f, ins, Nat.even_iff]
    · simp [D, f, ins, Nat.even_iff]
  obtain ⟨k, s, hs, rfl⟩ : ∃ k s, s < 4 ∧ n = 4 * k + s := ⟨n / 4, n % 4, Nat.mod_lt _ (by norm_num), by omega⟩
  have hk : 1 ≤ k := by omega
  interval_cases s
  · have hl : Nat.log 2 (4 * k + 0 + 1) = Nat.log 2 (2 * k) + 1 := by
      rw [show 4 * k + 0 + 1 = 2 * (2 * k) + 1 by ring, log2_double1 _ (by omega)]
    rw [hl, Nat.even_add_one (n := Nat.log 2 (2 * k)), not_not, ← (inv k hk).2.1]
    have hq := D_lt (2 * k) (by omega)
    rw [show 4 * k + 0 = 4 * k by ring, M1 k hk]
    generalize D (2 * k) = q at hq ⊢
    have e1 : ¬ ¬ Even (4 * k) := by simp; exact ⟨2 * k, by ring⟩
    simp only [e1, false_or]
    unfold Phi
    split_ifs <;> simp only [Nat.even_iff] <;> omega
  · have := M2 k hk; simp only [this, true_iff]; left; rw [Nat.not_even_iff_odd]; exact ⟨2 * k, by ring⟩
  · have hl : Nat.log 2 (4 * k + 2 + 1) = Nat.log 2 (2 * k) + 1 := by
      rw [show 4 * k + 2 + 1 = 2 * (2 * k + 1) + 1 by ring, log2_double1 _ (by omega),
        log2_double1 _ (by omega), log2_double _ (by omega)]
    rw [hl, Nat.even_add_one (n := Nat.log 2 (2 * k)), not_not, ← (inv k hk).2.2]
    have hq := E_lt (2 * k) (by omega)
    rw [M3 k hk]
    have e1 : ¬ ¬ Even (4 * k + 2) := by simp; exact ⟨2 * k + 1, by ring⟩
    simp only [e1, false_or]
    generalize E (2 * k) = q at hq ⊢
    have hmod : ∀ x, x < 2 * k + 1 → (x + 2) % (2 * k + 2) = if x + 2 < 2 * k + 2 then x + 2 else 0 := by
      intro x hx
      split_ifs with h
      · exact Nat.mod_eq_of_lt h
      · rw [show x + 2 = 2 * k + 2 by omega, Nat.mod_self]
    unfold ins
    split_ifs with hh
    · rw [hmod q (by omega)]; unfold Phi; split_ifs <;> simp only [Nat.even_iff] <;> omega
    · rw [hmod (q + 1) (by omega)]; unfold Phi; split_ifs <;> simp only [Nat.even_iff] <;> omega
  · have := M4 k hk; simp only [this, true_iff]; left; rw [Nat.not_even_iff_odd]; exact ⟨2 * k + 1, by ring⟩

end LtsA165556

namespace LtsA165556
open OMA.S_oeis_a165556

lemma idx_lt {A : List ℕ} (hA : A.Pairwise (· < ·)) {i j : ℕ} (hi : i < A.length) (hj : j < A.length) :
    A[i] < A[j] ↔ i < j := by
  have H := List.pairwise_iff_getElem.mp hA
  constructor
  · intro h
    by_contra h'
    rcases Nat.lt_or_ge j i with h2 | h2
    · have := H j i hj hi h2; omega
    · have : i = j := by omega
      subst this; omega
  · intro h; exact H i j hi hj h

lemma nxt_eq {A : List ℕ} (hA : A.Pairwise (· < ·)) (hN : 0 < A.length) {p u : ℕ}
    (hu : u ≤ A.length) (H : ∀ i (hi : i < A.length), p < A[i] ↔ u ≤ i) :
    nxt A p = A[u % A.length]'(Nat.mod_lt _ hN) := by
  unfold nxt
  rcases Nat.lt_or_ge u A.length with h | h
  · have hm : (A.filter (fun y => decide (p < y))).min? = some A[u] := by
      rw [List.min?_eq_some_iff']
      refine ⟨List.mem_filter.mpr ⟨List.getElem_mem _, by simpa using (H u h).mpr le_rfl⟩, ?_⟩
      intro b hb
      obtain ⟨hb1, hb2⟩ := List.mem_filter.mp hb
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb1
      have := (H i hi).mp (by simpa using hb2)
      rcases Nat.lt_or_ge u i with h3 | h3
      · exact le_of_lt ((idx_lt hA h hi).mpr h3)
      · have : u = i := by omega
        subst this; exact le_rfl
    rw [hm]; simp only [Nat.mod_eq_of_lt h]
  · have hu' : u = A.length := by omega
    have hm : (A.filter (fun y => decide (p < y))).min? = none := by
      rw [List.min?_eq_none_iff, List.filter_eq_nil_iff]
      intro a ha
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
      have := (H i hi); simp; omega
    have hm2 : A.min? = some A[0] := by
      rw [List.min?_eq_some_iff']
      refine ⟨List.getElem_mem _, ?_⟩
      intro b hb
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
      rcases Nat.eq_zero_or_pos i with h3 | h3
      · subst h3; exact le_rfl
      · exact le_of_lt ((idx_lt hA hN hi).mpr h3)
    rw [hm]; simp only [hm2, Option.getD_some]
    simp only [hu', Nat.mod_self]

lemma prv_eq {A : List ℕ} (hA : A.Pairwise (· < ·)) (hN : 0 < A.length) {p v : ℕ}
    (hv : v ≤ A.length) (H : ∀ i (hi : i < A.length), A[i] < p ↔ i < v) :
    prv A p = A[(v + A.length - 1) % A.length]'(Nat.mod_lt _ hN) := by
  unfold prv
  rcases Nat.eq_zero_or_pos v with h | h
  · have hm : (A.filter (fun y => decide (y < p))).max? = none := by
      rw [List.max?_eq_none_iff, List.filter_eq_nil_iff]
      intro a ha
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
      have := (H i hi); simp; omega
    have hm2 : A.max? = some A[A.length - 1] := by
      rw [List.max?_eq_some_iff']
      refine ⟨List.getElem_mem _, ?_⟩
      intro b hb
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
      rcases Nat.lt_or_ge i (A.length - 1) with h3 | h3
      · exact le_of_lt ((idx_lt hA hi (by omega)).mpr h3)
      · have : i = A.length - 1 := by omega
        subst this; exact le_rfl
    rw [hm]; simp only [hm2, Option.getD_some]
    congr 1; subst h; rw [Nat.mod_eq_of_lt (by omega)]; omega
  · have hm : (A.filter (fun y => decide (y < p))).max? = some A[v - 1] := by
      rw [List.max?_eq_some_iff']
      refine ⟨List.mem_filter.mpr ⟨List.getElem_mem _, by simpa using (H (v - 1) (by omega)).mpr (by omega)⟩, ?_⟩
      intro b hb
      obtain ⟨hb1, hb2⟩ := List.mem_filter.mp hb
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb1
      have := (H i hi).mp (by simpa using hb2)
      rcases Nat.lt_or_ge i (v - 1) with h3 | h3
      · exact le_of_lt ((idx_lt hA hi (by omega)).mpr h3)
      · have : i = v - 1 := by omega
        subst this; exact le_rfl
    rw [hm]
    simp only
    congr 1
    rw [show v + A.length - 1 = (v - 1) + A.length by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

lemma modc (x n : ℕ) (hn : 0 < n) (h : x ≤ 2 * n) :
    (x < n ∧ x % n = x) ∨ (n ≤ x ∧ x < 2 * n ∧ x % n = x - n) ∨ (x = 2 * n ∧ x % n = 0) := by
  rcases Nat.lt_or_ge x n with h1 | h1
  · exact Or.inl ⟨h1, Nat.mod_eq_of_lt h1⟩
  rcases Nat.lt_or_ge x (2 * n) with h2 | h2
  · refine Or.inr (Or.inl ⟨h1, h2, ?_⟩)
    rw [show x = (x - n) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
  · refine Or.inr (Or.inr ⟨by omega, ?_⟩)
    rw [show x = 2 * n by omega]; simp

lemma run_one (k : ℕ) (A : List ℕ) (hA : A.length = 1) (p1 p2 : ℕ) (t : Bool) :
    run k A p1 p2 t = A.getD 0 0 := by
  match A, hA with
  | [x], _ =>
    cases k with
    | zero => rfl
    | succ k => simp [run]

set_option maxHeartbeats 8000000 in
theorem bridge : ∀ M k (A : List ℕ) (p1 p2 : ℕ) (t : Bool) (u v : ℕ),
    A.Pairwise (· < ·) → A.length = M + 1 → M ≤ k → u ≤ M + 1 → v ≤ M + 1 →
    (∀ i (hi : i < A.length), p1 < A[i] ↔ u ≤ i) → (∀ i (hi : i < A.length), A[i] < p2 ↔ i < v) →
    run k A p1 p2 t = A.getD ((u + f (M + 1) ((v + (M + 1) - u) % (M + 1)) t) % (M + 1)) 0 := by
  intro M
  induction M with
  | zero =>
    intro k A p1 p2 t u v _ hl _ _ _ _ _
    rw [run_one k A hl]
    simp [f, Nat.mod_one]
  | succ M ih =>
    intro k A p1 p2 t u v hA hl hk hu hv H1 H2
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hN : 0 < A.length := by omega
    have hnd : A.Nodup := hA.imp (fun h => ne_of_lt h)
    cases t with
    | true =>
      have e1 := nxt_eq hA hN (by omega) H1
      set i0 := u % A.length with hi0
      have hi0lt : i0 < A.length := Nat.mod_lt _ hN
      have e2 := nxt_eq hA hN (u := i0 + 1) (p := A[i0]) (by omega)
        (fun i hi => by rw [idx_lt hA hi0lt hi]; omega)
      set r := (i0 + 1) % A.length with hr
      have hrlt : r < A.length := Nat.mod_lt _ hN
      have hrun : run (k + 1) A p1 p2 true = run k (A.eraseIdx r) A[r] p2 false := by
        rw [run, if_neg (by omega), if_pos rfl, e1, e2, hnd.erase_getElem]
      rw [hrun]
      have hl' : (A.eraseIdx r).length = M + 1 := by rw [List.length_eraseIdx_of_lt hrlt]; omega
      have hA' : (A.eraseIdx r).Pairwise (· < ·) := hA.sublist (List.eraseIdx_sublist _ _)
      rw [ih k (A.eraseIdx r) A[r] p2 false r (if r < v then v - 1 else v) hA' hl' (by omega)
        (by omega) (by split_ifs <;> omega)
        (fun i hi => by
          rw [List.getElem_eraseIdx]
          split_ifs with h
          · rw [idx_lt hA hrlt] <;> omega
          · rw [idx_lt hA hrlt] <;> omega)
        (fun i hi => by
          rw [List.getElem_eraseIdx]
          split_ifs with h h'
          · rw [H2] <;> omega
          · rw [H2] <;> omega
          · rw [H2] <;> omega
          · rw [H2] <;> omega)]
      have hfeq : f (M + 1 + 1) ((v + (M + 1 + 1) - u) % (M + 1 + 1)) true =
          (f (M + 1) (((if r < v then v - 1 else v) + (M + 1) - r) % (M + 1)) false + 2) % (M + 1 + 1) := by
        show (f (M + 1) (if 2 ≤ (v + (M + 1 + 1) - u) % (M + 1 + 1) then (v + (M + 1 + 1) - u) % (M + 1 + 1) - 2
          else if (v + (M + 1 + 1) - u) % (M + 1 + 1) = 1 then 0 else M) false + 2) % (M + 1 + 1) = _
        congr 3
        have c1 := modc (v + (M + 1 + 1) - u) (M + 1 + 1) (by omega) (by omega)
        have c2 := modc u (M + 1 + 1) (by omega) (by omega)
        have c3 := modc (i0 + 1) (M + 1 + 1) (by omega) (by omega)
        have c4 := modc ((if r < v then v - 1 else v) + (M + 1) - r) (M + 1) (by omega)
          (by split_ifs <;> omega)
        rw [hl] at hi0 hr
        split_ifs at c4 ⊢ <;> omega
      rw [hfeq]
      have hq := f_lt M (((if r < v then v - 1 else v) + (M + 1) - r) % (M + 1)) false
      generalize f (M + 1) (((if r < v then v - 1 else v) + (M + 1) - r) % (M + 1)) false = q at hq ⊢
      have c2 := modc u (M + 1 + 1) (by omega) (by omega)
      have c3 := modc (i0 + 1) (M + 1 + 1) (by omega) (by omega)
      have c5 := modc (q + 2) (M + 1 + 1) (by omega) (by omega)
      have c6 := modc (r + q) (M + 1) (by omega) (by omega)
      have c7 := modc (u + (q + 2) % (M + 1 + 1)) (M + 1 + 1) (by omega) (by omega)
      rw [hl] at hi0 hr
      rw [List.getD_eq_getElem _ _ (by rw [hl']; exact Nat.mod_lt _ (by omega)),
        List.getD_eq_getElem _ _ (by rw [hl]; exact Nat.mod_lt _ (by omega)), List.getElem_eraseIdx]
      split_ifs with h
      · congr 1; omega
      · congr 1; omega
    | false =>
      have e1 := prv_eq hA hN (by omega) H2
      set j0 := (v + A.length - 1) % A.length with hj0
      have hj0lt : j0 < A.length := Nat.mod_lt _ hN
      have e2 := prv_eq hA hN (v := j0) (p := A[j0]) (by omega)
        (fun i hi => by rw [idx_lt hA hi hj0lt])
      set r := (j0 + A.length - 1) % A.length with hr
      have hrlt : r < A.length := Nat.mod_lt _ hN
      have hrun : run (k + 1) A p1 p2 false = run k (A.eraseIdx r) p1 A[r] true := by
        rw [run, if_neg (by omega), if_neg (by simp), e1, e2, hnd.erase_getElem]
      rw [hrun]
      have hl' : (A.eraseIdx r).length = M + 1 := by rw [List.length_eraseIdx_of_lt hrlt]; omega
      have hA' : (A.eraseIdx r).Pairwise (· < ·) := hA.sublist (List.eraseIdx_sublist _ _)
      rw [ih k (A.eraseIdx r) p1 A[r] true (if r < u then u - 1 else u) r hA' hl' (by omega)
        (by split_ifs <;> omega) (by omega)
        (fun i hi => by
          rw [List.getElem_eraseIdx]
          split_ifs with h h'
          · rw [H1] <;> omega
          · rw [H1] <;> omega
          · rw [H1] <;> omega
          · rw [H1] <;> omega)
        (fun i hi => by
          rw [List.getElem_eraseIdx]
          split_ifs with h
          · rw [idx_lt hA _ hrlt] <;> omega
          · rw [idx_lt hA _ hrlt] <;> omega)]
      set w := (v + (M + 1 + 1) - u) % (M + 1 + 1) with hw
      set rf := (w + M) % (M + 1 + 1) with hrf
      have hfeq : f (M + 1 + 1) w false = ins rf (f (M + 1) (rf % (M + 1)) true) := rfl
      rw [hfeq]
      have harg : (r + (M + 1) - (if r < u then u - 1 else u)) % (M + 1) = rf % (M + 1) := by
        have c1 := modc (v + (M + 1 + 1) - u) (M + 1 + 1) (by omega) (by omega)
        have c2 := modc (v + (M + 1 + 1) - 1) (M + 1 + 1) (by omega) (by omega)
        have c3 := modc (j0 + (M + 1 + 1) - 1) (M + 1 + 1) (by omega) (by omega)
        have c4 := modc (w + M) (M + 1 + 1) (by omega) (by omega)
        have c5 := modc ((r + (M + 1) - (if r < u then u - 1 else u))) (M + 1) (by omega)
          (by split_ifs <;> omega)
        have c6 := modc rf (M + 1) (by omega) (by omega)
        rw [hl] at hj0 hr
        split_ifs at c5 ⊢ <;> omega
      rw [harg]
      have hq := f_lt M (rf % (M + 1)) true
      generalize f (M + 1) (rf % (M + 1)) true = q at hq ⊢
      have c1 := modc (v + (M + 1 + 1) - u) (M + 1 + 1) (by omega) (by omega)
      have c2 := modc (v + (M + 1 + 1) - 1) (M + 1 + 1) (by omega) (by omega)
      have c3 := modc (j0 + (M + 1 + 1) - 1) (M + 1 + 1) (by omega) (by omega)
      have c4 := modc (w + M) (M + 1 + 1) (by omega) (by omega)
      rw [hl] at hj0 hr
      have hrfr : rf < M + 2 := by omega
      clear_value w rf r j0
      rcases Nat.lt_or_ge q rf with hq1 | hq1
      · rw [show ins rf q = q from if_pos hq1]
        have c8 := modc (u + q) (M + 1 + 1) (by omega) (by omega)
        rcases Nat.lt_or_ge r u with hru | hru
        · rw [if_pos hru]
          have c9 := modc (u - 1 + q) (M + 1) (by omega) (by omega)
          rw [List.getD_eq_getElem _ _ (by rw [hl']; exact Nat.mod_lt _ (by omega)),
            List.getD_eq_getElem _ _ (by rw [hl]; exact Nat.mod_lt _ (by omega)), List.getElem_eraseIdx]
          split <;> (congr 1; omega)
        · rw [if_neg (by omega)]
          have c9 := modc (u + q) (M + 1) (by omega) (by omega)
          rw [List.getD_eq_getElem _ _ (by rw [hl']; exact Nat.mod_lt _ (by omega)),
            List.getD_eq_getElem _ _ (by rw [hl]; exact Nat.mod_lt _ (by omega)), List.getElem_eraseIdx]
          split <;> (congr 1; omega)
      · rw [show ins rf q = q + 1 from if_neg (by omega)]
        have c8 := modc (u + (q + 1)) (M + 1 + 1) (by omega) (by omega)
        rcases Nat.lt_or_ge r u with hru | hru
        · rw [if_pos hru]
          have c9 := modc (u - 1 + q) (M + 1) (by omega) (by omega)
          rw [List.getD_eq_getElem _ _ (by rw [hl']; exact Nat.mod_lt _ (by omega)),
            List.getD_eq_getElem _ _ (by rw [hl]; exact Nat.mod_lt _ (by omega)), List.getElem_eraseIdx]
          split <;> (congr 1; omega)
        · rw [if_neg (by omega)]
          have c9 := modc (u + q) (M + 1) (by omega) (by omega)
          rw [List.getD_eq_getElem _ _ (by rw [hl']; exact Nat.mod_lt _ (by omega)),
            List.getD_eq_getElem _ _ (by rw [hl]; exact Nat.mod_lt _ (by omega)), List.getElem_eraseIdx]
          split <;> (congr 1; omega)

lemma JI_eq (n : ℕ) (hn : 1 ≤ n) : JI n = D n + 1 := by
  obtain ⟨M, rfl⟩ : ∃ M, n = M + 1 := ⟨n - 1, by omega⟩
  unfold JI
  rw [bridge M (M + 1) (List.range' 1 (M + 1)) 0 (M + 1 + 1) true 0 (M + 1)
    (List.pairwise_lt_range' ..) (by simp) (by omega) (by omega) le_rfl
    (fun i hi => by simp) (fun i hi => by simp at hi ⊢; omega)]
  have hm : (M + 1 + (M + 1) - 0) % (M + 1) = 0 := by
    rw [Nat.sub_zero, Nat.add_mod_right, Nat.mod_self]
  rw [hm]
  have := f_lt M 0 true
  rw [zero_add, Nat.mod_eq_of_lt this, List.getD_eq_getElem _ _ (by simpa using this)]
  simp [D]; omega

end LtsA165556

theorem OMA.solution : type_of% @OMA.S_oeis_a165556.main := by
  intro n hn
  have hJ := LtsA165556.JI_eq n hn
  have hE := LtsA165556.D_even_iff n hn
  unfold OMA.S_oeis_a165556.a
  rw [hJ]
  have key : Even (n + (n + 1) * Nat.log 2 (n + 1)) ↔ ¬ Even (LtsA165556.D n) := by
    rw [hE]
    rcases Nat.even_or_odd n with h | h
    · have h1 : ¬ Even (n + 1) := by rw [Nat.even_add_one]; exact not_not.mpr h
      simp [Nat.even_add, Nat.even_mul, h, h1]
    · have h0 : ¬ Even n := Nat.not_even_iff_odd.mpr h
      have h1 : Even (n + 1) := by rw [Nat.even_add_one]; exact h0
      simp [Nat.even_add, Nat.even_mul, h0, h1]
  split_ifs with h
  · have := key.mp h
    rw [Nat.not_even_iff_odd] at this
    obtain ⟨c, hc⟩ := this; omega
  · have : Even (LtsA165556.D n) := by
      by_contra h'; exact h (key.mpr h')
    obtain ⟨c, hc⟩ := this; omega
