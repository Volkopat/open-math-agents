import OMAStatements.S_oeis_a329479
import Mathlib.Algebra.BigOperators.Ring.Finset

-- Original Lean proof: @justusklocke-cloud.

namespace A329479Aux

def stp (s : ZMod 3 × ZMod 3) (b : Bool) : ZMod 3 × ZMod 3 :=
  (1 * s.1 + OMA.S_oeis_a329479.bit b, 2 * s.2 + OMA.S_oeis_a329479.bit b)

def run (l : List Bool) (s : ZMod 3 × ZMod 3) : ZMod 3 × ZMod 3 :=
  (OMA.S_oeis_a329479.evalBits l 1 s.1, OMA.S_oeis_a329479.evalBits l 2 s.2)

lemma run_cons (b : Bool) (l : List Bool) (s : ZMod 3 × ZMod 3) :
    run (b :: l) s = run l (stp s b) := rfl

def G (n : ℕ) (s : ZMod 3 × ZMod 3) : ℤ :=
  ∑ w : Fin n → Bool, if run (List.ofFn w) s = (0, 0) then 1 else 0

lemma G_succ (n : ℕ) (s : ZMod 3 × ZMod 3) :
    G (n + 1) s = G n (stp s true) + G n (stp s false) := by
  unfold G
  have h1 : (∑ w : Fin (n + 1) → Bool, if run (List.ofFn w) s = (0, 0) then (1 : ℤ) else 0)
      = ∑ p : Bool × (Fin n → Bool),
          if run (List.ofFn p.2) (stp s p.1) = (0, 0) then (1 : ℤ) else 0 := by
    symm
    apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Bool))
    intro p
    have e : (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)) p = Fin.cons p.1 p.2 := rfl
    rw [e, List.ofFn_cons, run_cons]
  have h2 : (∑ p : Bool × (Fin n → Bool),
        if run (List.ofFn p.2) (stp s p.1) = (0, 0) then (1 : ℤ) else 0)
      = (∑ w : Fin n → Bool, if run (List.ofFn w) (stp s true) = (0, 0) then (1 : ℤ) else 0)
        + ∑ w : Fin n → Bool, if run (List.ofFn w) (stp s false) = (0, 0) then (1 : ℤ) else 0 :=
    (Fintype.sum_prod_type _).trans (Fintype.sum_bool _)
  exact h1.trans h2

lemma cond_iff (l : List Bool) :
    (∀ x : ZMod 3, x * OMA.S_oeis_a329479.evalBits l x 1 = 0) ↔ run l (1, 1) = (0, 0) := by
  have h2 : ∀ e : ZMod 3, 2 * e = 0 → e = 0 := by decide
  have h3 : ∀ x : ZMod 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  constructor
  · intro h
    have a1 := h 1
    have a2 := h 2
    rw [one_mul] at a1
    exact Prod.ext a1 (h2 _ a2)
  · intro h x
    have b1 : OMA.S_oeis_a329479.evalBits l 1 1 = 0 := congrArg Prod.fst h
    have b2 : OMA.S_oeis_a329479.evalBits l 2 1 = 0 := congrArg Prod.snd h
    rcases h3 x with rfl | rfl | rfl
    · rw [zero_mul]
    · rw [one_mul]; exact b1
    · rw [b2, mul_zero]

lemma a_eq (n : ℕ) : OMA.S_oeis_a329479.a (n + 1) = G n (1, 1) := by
  show (∑ w : Fin n → Bool,
      if ∀ x : ZMod 3, x * OMA.S_oeis_a329479.evalBits (List.ofFn w) x 1 = 0 then (1 : ℤ) else 0)
    = G n (1, 1)
  unfold G
  apply Finset.sum_congr rfl
  intro w _
  by_cases h : run (List.ofFn w) (1, 1) = (0, 0)
  · rw [if_pos h, if_pos ((cond_iff _).mpr h)]
  · rw [if_neg h, if_neg (fun h' => h ((cond_iff _).mp h'))]

private abbrev State := ZMod 3 × ZMod 3

/-- Number of paths of length k from s to t under the two bit transitions. -/
private def paths : ℕ → State → State → ℤ
  | 0, s, t => if s = t then 1 else 0
  | k + 1, s, t => paths k (stp s true) t + paths k (stp s false) t

private lemma G_shift (n k : ℕ) (s : State) :
    G (n + k) s = ∑ t : State, paths k s t * G n t := by
  induction k generalizing s with
  | zero => simp [paths, ite_mul]
  | succ k ih =>
    rw [show n + (k + 1) = n + k + 1 by omega, G_succ]
    simp only [ih, ← Finset.sum_add_distrib, paths, add_mul]

private lemma paths_recur : ∀ t : State,
    paths 8 (1, 1) t = 2 * paths 7 (1, 1) t + 2 * paths 6 (1, 1) t - 5 * paths 5 (1, 1) t -
      2 * paths 4 (1, 1) t + 10 * paths 3 (1, 1) t - 4 * paths 2 (1, 1) t -
      4 * paths 1 (1, 1) t + 8 * paths 0 (1, 1) t := by decide

theorem recurrence : type_of% @OMA.S_oeis_a329479.main := by
  intro n
  rw [a_eq (n+8), a_eq (n+7), a_eq (n+6), a_eq (n+5), a_eq (n+4),
    a_eq (n+3), a_eq (n+2), a_eq (n+1), a_eq n]
  have initial := G_shift n 0 (1, 1)
  rw [Nat.add_zero] at initial
  rw [G_shift n 8, G_shift n 7, G_shift n 6, G_shift n 5, G_shift n 4,
    G_shift n 3, G_shift n 2, G_shift n 1, initial]
  simp only [Finset.mul_sum, ← mul_assoc, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    ← add_mul, ← sub_mul]
  exact Finset.sum_congr rfl fun t _ => congrArg (· * G n t) (paths_recur t)

end A329479Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a329479.main := A329479Aux.recurrence
