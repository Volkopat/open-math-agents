import OMAStatements.S_oeis_a289035
import Mathlib

/-!
# A289035: the length conjecture fails at n = 22

The 22nd iterate has 268184 letters, while A289004 22 = 268182. The length is computed in the
kernel through a carry transducer run over a balanced tree of small chunks, which is proved
equivalent to the statement's `step`.
-/

namespace OMA.A289035

open OMA.S_oeis_a289035

/-- Letters still pending at the end of a run. -/
def cl : Option Bool → List Bool
  | none => []
  | some b => [b]

/-- The transducer reading one letter at a time, with a pending letter as carry. -/
def stepC : Option Bool → List Bool → List Bool × Option Bool
  | c, [] => ([], c)
  | none, x :: r => stepC (some x) r
  | some false, false :: r => (false :: false :: true :: false :: (stepC none r).1, (stepC none r).2)
  | some false, true :: r => (false :: true :: false :: (stepC none r).1, (stepC none r).2)
  | some true, false :: r => (false :: true :: false :: (stepC none r).1, (stepC none r).2)
  | some true, true :: r => (true :: (stepC (some true) r).1, (stepC (some true) r).2)

theorem stepC_spec : ∀ (n : ℕ) (l : List Bool), l.length ≤ n → ∀ c : Option Bool,
    (stepC c l).1 ++ cl (stepC c l).2 = step (cl c ++ l) := by
  intro n
  induction n with
  | zero =>
    intro l hl c
    have : l = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)
    subst this
    rcases c with _ | _ | _ <;> simp [stepC, cl, step]
  | succ n ih =>
    intro l hl c
    rcases l with _ | ⟨x, r⟩
    · rcases c with _ | _ | _ <;> simp [stepC, cl, step]
    · have hr : r.length ≤ n := by simpa using hl
      rcases c with _ | _ | _
      · rcases r with _ | ⟨y, s⟩
        · cases x <;> simp [stepC, cl, step]
        · have hs : s.length ≤ n := by
            have : s.length + 1 ≤ n := by simpa using hr
            omega
          have h1 := ih s hs none
          have h2 := ih s hs (some true)
          cases x <;> cases y <;> simp [stepC, cl, step] at h1 h2 ⊢ <;> first | exact h1 | exact h2
      · have h1 := ih r hr none
        cases x <;> simp [stepC, cl, step] at h1 ⊢ <;> exact h1
      · have h1 := ih r hr none
        have h2 := ih r hr (some true)
        cases x <;> simp [stepC, cl, step] at h1 h2 ⊢ <;> first | exact h1 | exact h2

theorem stepC_append : ∀ (a b : List Bool) (c : Option Bool),
    stepC c (a ++ b) =
      ((stepC c a).1 ++ (stepC (stepC c a).2 b).1, (stepC (stepC c a).2 b).2) := by
  intro a
  induction a with
  | nil => intro b c; simp [stepC]
  | cons x r ih =>
    intro b c
    rcases c with _ | _ | _ <;> cases x <;> simp [stepC, ih]

inductive T where
  | leaf : List Bool → T
  | node : T → T → T

def flat : T → List Bool
  | T.leaf l => l
  | T.node a b => flat a ++ flat b

def lenT : T → ℕ
  | T.leaf l => l.length
  | T.node a b => lenT a + lenT b

theorem lenT_eq (t : T) : lenT t = (flat t).length := by
  induction t with
  | leaf l => rfl
  | node a b iha ihb => simp [lenT, flat, iha, ihb]

def mk (o : List Bool) : T :=
  if 32 < o.length then T.node (T.leaf (o.take (o.length / 2))) (T.leaf (o.drop (o.length / 2)))
  else T.leaf o

theorem flat_mk (o : List Bool) : flat (mk o) = o := by
  unfold mk
  split <;> simp [flat]

def stepT : Option Bool → T → T × Option Bool
  | c, T.leaf l => (mk (stepC c l).1, (stepC c l).2)
  | c, T.node a b =>
    (T.node (stepT c a).1 (stepT (stepT c a).2 b).1, (stepT (stepT c a).2 b).2)

theorem stepT_spec (t : T) : ∀ c : Option Bool,
    flat (stepT c t).1 = (stepC c (flat t)).1 ∧ (stepT c t).2 = (stepC c (flat t)).2 := by
  induction t with
  | leaf l => intro c; simp [stepT, flat, flat_mk]
  | node a b iha ihb =>
    intro c
    simp [stepT, flat, stepC_append, (iha c).1, (iha c).2, (ihb _).1, (ihb _).2]

def next (t : T) : T := T.node (stepT none t).1 (T.leaf (cl (stepT none t).2))

theorem flat_next (t : T) : flat (next t) = step (flat t) := by
  have h := stepC_spec (flat t).length (flat t) le_rfl none
  simp only [next, flat, (stepT_spec t none).1, (stepT_spec t none).2]
  simpa [cl] using h

def W : ℕ → T
  | 0 => T.leaf [false, false]
  | n + 1 => next (W n)

theorem flat_W (n : ℕ) : flat (W n) = w n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [W, w, flat_next, ih]

theorem len22 : lenT (W 22) = 268184 := by decide +kernel

theorem a22 : A289004 22 = 268182 := by decide +kernel

end OMA.A289035

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a289035.main) := by
  intro h
  have h1 := h.1 22
  rw [← OMA.A289035.flat_W, ← OMA.A289035.lenT_eq, OMA.A289035.len22, OMA.A289035.a22] at h1
  norm_num at h1
