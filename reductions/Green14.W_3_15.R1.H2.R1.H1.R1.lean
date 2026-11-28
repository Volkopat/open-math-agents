import OMAReductions.R_Green14_W_3_15_R1_H2_R1
import Mathlib

namespace OMA.R_Green14_W_3_15_R1_H2_R1_H1_R1

private theorem endpoint_blocked_blue (r : Fin 217 → Bool) (c : Nat → Bool)
    (agree : ∀ i : Fin 217, c i.val = r i) (endpoint : c 217 = false)
    (noRed : ∀ a d : Fin 217, 0 < d.val → a.val + 2 * d.val < 217 →
      ¬ ∀ t : Fin 3, r (Fin.ofNat 217 (a.val + t.val * d.val)) = true)
    (noBlue : ∀ a d : Fin 217, 0 < d.val → a.val + 14 * d.val < 217 →
      ¬ ∀ t : Fin 15, r (Fin.ofNat 217 (a.val + t.val * d.val)) = false)
    (forces : ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 14)*d < 218 ∧
      ∀ t : Fin 15, t.val ≤ (if b then 2 else 14) → c (a+t.val*d) = b) :
    ∃ d : Fin 16, 0 < d.val ∧ ∀ t : Fin 14,
      r (Fin.ofNat 217 (217 - (14 - t.val) * d.val)) = false := by
  have color_at (p : Nat) (hp : p < 217) : c p = r (Fin.ofNat 217 p) := by
    have index : Fin.ofNat 217 p = ⟨p, hp⟩ := Fin.ext (Nat.mod_eq_of_lt hp)
    rw [index]
    exact agree ⟨p, hp⟩
  obtain ⟨b,a,d,positive,bounded,mono⟩ := forces
  cases b
  · simp only [Bool.false_eq_true, if_false] at bounded mono
    by_cases inside : a+14*d < 217
    · have ha : a < 217 := by omega
      have hd : d < 217 := by omega
      exfalso
      apply noBlue ⟨a,ha⟩ ⟨d,hd⟩ positive inside
      intro t
      have ht : t.val ≤ 14 := by omega
      have within : a+t.val*d < 217 :=
        (Nat.add_le_add_left (Nat.mul_le_mul_right d ht) a).trans_lt inside
      rw [← color_at _ within]
      exact mono t ht
    · have last : a+14*d = 217 := by omega
      refine ⟨⟨d, by omega⟩, positive, ?_⟩
      intro t
      have ht : t.val ≤ 13 := by omega
      have scaled := Nat.mul_le_mul_right d ht
      have within : a+t.val*d < 217 := by omega
      have same : 217 - (14-t.val)*d = a+t.val*d := by
        rw [Nat.sub_mul]
        omega
      rw [show 217-(14-t.val)*d = a+t.val*d from same, ← color_at _ within]
      exact mono ⟨t.val, by omega⟩ (by change t.val ≤ 14; omega)
  · simp only [if_true] at bounded mono
    have inside : a+2*d < 217 := by
      by_contra! outside
      have last : a+2*d = 217 := by omega
      have endRed := mono (2 : Fin 15) (by decide)
      change c (a+2*d) = true at endRed
      rw [last, endpoint] at endRed
      contradiction
    have ha : a < 217 := by omega
    have hd : d < 217 := by omega
    exfalso
    apply noRed ⟨a,ha⟩ ⟨d,hd⟩ positive inside
    intro t
    have ht : t.val ≤ 2 := by omega
    have within : a+t.val*d < 217 :=
      (Nat.add_le_add_left (Nat.mul_le_mul_right d ht) a).trans_lt inside
    rw [← color_at _ within]
    exact mono ⟨t.val, by omega⟩ ht

def H1 : Prop :=
  ∀ c : Nat → Bool, c 108 = true → c 120 = true → c 217 = false →
    (∀ i : Nat, 108 < i → i < 120 → c i = false) →
    (c 107 = true) →
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 14)*d < 218 ∧
      ∀ t : Fin 15, t.val ≤ (if b then 2 else 14) → c (a+t.val*d) = b

def H2 : Prop :=
  ∀ c : Nat → Bool, c 108 = true → c 120 = true → c 217 = false →
    (∀ i : Nat, 108 < i → i < 120 → c i = false) →
    (c 107 = false ∧ c 105 = true) →
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 14)*d < 218 ∧
      ∀ t : Fin 15, t.val ≤ (if b then 2 else 14) → c (a+t.val*d) = b

def H3 : Prop :=
  ∀ c : Nat → Bool, c 108 = true → c 120 = true → c 217 = false →
    (∀ i : Nat, 108 < i → i < 120 → c i = false) →
    (c 107 = false ∧ c 105 = false ∧ c 103 = true) →
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 14)*d < 218 ∧
      ∀ t : Fin 15, t.val ≤ (if b then 2 else 14) → c (a+t.val*d) = b

def H4 : Prop :=
  ∀ c : Nat → Bool, c 108 = true → c 120 = true → c 217 = false →
    (∀ i : Nat, 108 < i → i < 120 → c i = false) →
    (c 107 = false ∧ c 105 = false ∧ c 103 = false) →
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 14)*d < 218 ∧
      ∀ t : Fin 15, t.val ≤ (if b then 2 else 14) → c (a+t.val*d) = b

theorem main : H1 → H2 → H3 → H4 → OMA.R_Green14_W_3_15_R1_H2_R1.H1 := by
  intro part1 part2 part3 part4 r anchor chosen gap noRed noBlue
  let c (i : Nat) := if h : i < 217 then r ⟨i,h⟩ else false
  have agree (i : Fin 217) : c i.val = r i := by simp [c, i.isLt]
  have endpoint : c 217 = false := by simp [c]
  have mid : c 108 = true := (agree 108).trans anchor
  have at120 : c 120 = true := (agree 120).trans chosen
  have between (i : Nat) (lo : 108 < i) (hi : i < 120) : c i = false :=
    (agree ⟨i,by omega⟩).trans (gap ⟨i,by omega⟩ lo hi)
  apply endpoint_blocked_blue r c agree endpoint noRed noBlue
  cases h107 : c 107 with
  | true =>
    exact part1 c mid at120 endpoint between h107
  | false =>
    cases h105 : c 105 with
    | true =>
      exact part2 c mid at120 endpoint between ⟨h107,h105⟩
    | false =>
      cases h103 : c 103 with
      | true =>
        exact part3 c mid at120 endpoint between ⟨h107,h105,h103⟩
      | false =>
        exact part4 c mid at120 endpoint between ⟨h107,h105,h103⟩

end OMA.R_Green14_W_3_15_R1_H2_R1_H1_R1