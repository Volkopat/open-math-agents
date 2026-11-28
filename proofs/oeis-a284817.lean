import OMAStatements.S_oeis_a284817
import Mathlib

/-!
# A284817: 2n - 1 - A284776(n) is A189664(n-1)

Write phi for 0 -> 01, 1 -> 0011. Each image has as many letters 0 as letters 1, and the zeros
of phi(c) sit at offsets 0 (c = 0) or 0 and 1 (c = 1) of its block. So the j-th zero of phi(v),
counting from 0, sits at position p with p + b = 2j, where b is letter j of theta(v) and theta is
0 -> 0, 1 -> 01 (`keyB`). Since 2n - 1 - A284776(n) = 2(n-1) - p, a(n) is letter n-1 of
theta(S(n)). Next theta(w) 0 = 0 theta'(w) with theta' = 0 -> 0, 1 -> 10 (`conjC`), and
theta'(phi(w)) = psi(theta'(w)) for psi = 0 -> 010, 1 -> 001 (`interD`), so theta'(S(k)) = P(k).
Then letter n-1 of theta(S(n)) is letter n-1 of 0 P(n), which is 0 for n = 1 and letter n-2 of
P(n) = A189664(n-1) for n ≥ 2.
-/

namespace OMA.P284817

open OMA.S_oeis_a284817

/-- Positions of the letter 0, counted from 0. -/
def zp : List ℕ → List ℕ
  | [] => []
  | c :: w => if c = 0 then 0 :: (zp w).map (· + 1) else (zp w).map (· + 1)

lemma filter_eq (w : List ℕ) :
    (List.range w.length).filter (fun i => w.getD i 1 = 0) = zp w := by
  induction w with
  | nil => simp [zp]
  | cons c w ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_map]
    have h : ((fun i => decide ((c :: w).getD i 1 = 0)) ∘ Nat.succ) =
        (fun i => decide (w.getD i 1 = 0)) := by
      funext i
      simp
    rw [h, ih]
    by_cases hc : c = 0 <;> simp [zp, hc]

/-- theta: 0 -> 0, 1 -> 01. -/
def th : ℕ → List ℕ
  | 0 => [0]
  | _ => [0, 1]

/-- theta': 0 -> 0, 1 -> 10. -/
def th' : ℕ → List ℕ
  | 0 => [0]
  | _ => [1, 0]

lemma zp_zero_cons (w : List ℕ) : zp (0 :: w) = 0 :: (zp w).map (· + 1) := by simp [zp]

lemma zp_one_cons (w : List ℕ) : zp (1 :: w) = (zp w).map (· + 1) := by simp [zp]

/-- The j-th zero of phi(v) sits at position p with p + theta(v)(j) = 2j. -/
lemma keyB (v : List ℕ) : ∀ j b, (v.flatMap th)[j]? = some b →
    ∃ p, (zp (v.flatMap morph))[j]? = some p ∧ p + b = 2 * j := by
  induction v with
  | nil => intro j b h; simp at h
  | cons c v ih =>
    intro j b h
    rw [List.flatMap_cons] at h ⊢
    cases c with
    | zero =>
      have e1 : morph 0 ++ v.flatMap morph = 0 :: 1 :: v.flatMap morph := rfl
      have e2 : th 0 ++ v.flatMap th = 0 :: v.flatMap th := rfl
      rw [e2] at h
      rw [e1, zp_zero_cons, zp_one_cons]
      cases j with
      | zero =>
        simp at h
        exact ⟨0, by simp, by omega⟩
      | succ j =>
        rw [List.getElem?_cons_succ] at h
        obtain ⟨p, hp, hpb⟩ := ih j b h
        refine ⟨p + 1 + 1, ?_, by omega⟩
        simp [hp]
    | succ c =>
      have e1 : morph (c + 1) ++ v.flatMap morph = 0 :: 0 :: 1 :: 1 :: v.flatMap morph := rfl
      have e2 : th (c + 1) ++ v.flatMap th = 0 :: 1 :: v.flatMap th := rfl
      rw [e2] at h
      rw [e1, zp_zero_cons, zp_zero_cons, zp_one_cons, zp_one_cons]
      match j, h with
      | 0, h =>
        simp at h
        exact ⟨0, by simp, by omega⟩
      | 1, h =>
        simp at h
        exact ⟨1, by simp, by omega⟩
      | j + 2, h =>
        rw [List.getElem?_cons_succ, List.getElem?_cons_succ] at h
        obtain ⟨p, hp, hpb⟩ := ih j b h
        refine ⟨p + 1 + 1 + 1 + 1, ?_, by omega⟩
        simp [hp]

lemma conjC (w : List ℕ) : w.flatMap th ++ [0] = 0 :: w.flatMap th' := by
  induction w with
  | nil => simp
  | cons c w ih =>
    rw [List.flatMap_cons, List.flatMap_cons, List.append_assoc, ih]
    cases c <;> simp [th, th']

lemma interD (w : List ℕ) : (w.flatMap morph).flatMap th' = (w.flatMap th').flatMap morph3 := by
  induction w with
  | nil => simp
  | cons c w ih =>
    rw [List.flatMap_cons, List.flatMap_cons, List.flatMap_append, List.flatMap_append, ih]
    cases c <;> simp [morph, th', morph3]

lemma iterE (k : ℕ) : (iter k).flatMap th' = iter3 k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h1 : iter (k + 1) = (iter k).flatMap morph := rfl
    have h2 : iter3 (k + 1) = (iter3 k).flatMap morph3 := rfl
    rw [h1, h2, interD, ih]

lemma morph_length (c : ℕ) : 2 ≤ (morph c).length := by
  cases c <;> simp [morph]

lemma flatMap_length (w : List ℕ) : 2 * w.length ≤ (w.flatMap morph).length := by
  induction w with
  | nil => simp
  | cons c w ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    have := morph_length c
    omega

lemma iter_length (k : ℕ) : k + 1 ≤ (iter k).length := by
  induction k with
  | zero => simp [iter]
  | succ k ih =>
    have h := flatMap_length (iter k)
    have h2 : (iter (k + 1)).length = ((iter k).flatMap morph).length := rfl
    omega

lemma th_length (w : List ℕ) : w.length ≤ (w.flatMap th).length := by
  induction w with
  | nil => simp
  | cons c w ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    have : 1 ≤ (th c).length := by cases c <;> simp [th]
    omega

theorem sol : type_of% @OMA.S_oeis_a284817.main := by
  intro n hn
  have hlen : n - 1 < ((iter n).flatMap th).length := by
    have := iter_length n
    have := th_length (iter n)
    omega
  obtain ⟨b, hb⟩ : ∃ b, ((iter n).flatMap th)[n - 1]? = some b :=
    ⟨_, List.getElem?_eq_getElem hlen⟩
  obtain ⟨p, hp, hpb⟩ := keyB (iter n) (n - 1) b hb
  have hA : A284776 n = p + 1 := by
    unfold A284776 zeroPositions
    rw [filter_eq]
    have h1 : iter (n + 1) = (iter n).flatMap morph := rfl
    rw [h1, List.getD_eq_getElem?_getD, List.getElem?_map, hp]
    rfl
  have hC := conjC (iter n)
  rw [iterE] at hC
  have hb2 : (0 :: iter3 n)[n - 1]? = some b := by
    rw [← hC, List.getElem?_append_left hlen, hb]
  unfold a
  rw [hA]
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    simp at hb2
    simp [A189664]
    omega
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have e1 : m + 2 - 1 = m + 1 := by omega
    rw [e1, List.getElem?_cons_succ] at hb2
    unfold A189664
    rw [if_neg (by omega), e1, List.getD_eq_getElem?_getD]
    have e2 : m + 1 + 1 = m + 2 := by omega
    have e3 : m + 1 - 1 = m := by omega
    rw [e2, e3, hb2]
    simp
    rw [e1] at hpb
    omega

end OMA.P284817

theorem OMA.solution : type_of% @OMA.S_oeis_a284817.main := OMA.P284817.sol

