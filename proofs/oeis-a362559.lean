import OMAStatements.S_oeis_a362559
import Mathlib

-- Problem: A362559: Number of integer partitions of n whose weighted sum is divisible by n.
-- Upstream: formal-conjectures statements/oeis-a362559.lean:0 (declaration OMA.S_oeis_a362559.main)
-- Credit: @rorcores (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
--
-- Proof.  Let y = (y_1, ..., y_k) have sum n.  The weighted sum of y is the sum of i * y_i and the
-- weighted sum of the reverse is the sum of (k + 1 - i) * y_i, so the two weighted sums add up to
-- (k + 1) * n, a multiple of n.  Hence n divides one of them if and only if it divides the other.
--
-- In Lean the identity  W(y) + W(reverse y) = (k + 1) * sum(y)  is proved by induction on the list,
-- through the auxiliary recursive function wFrom c y = c * y_1 + (c + 1) * y_2 + ...

namespace OMA.A362559

/-- `wFrom c (y_1, ..., y_k) = c * y_1 + (c + 1) * y_2 + ... + (c + k - 1) * y_k`. -/
def wFrom : ℕ → List ℕ → ℕ
  | _, [] => 0
  | c, a :: l => c * a + wFrom (c + 1) l

theorem fin_sum_eq (y : List ℕ) :
    ∀ c : ℕ, ∑ i : Fin y.length, (i.val + c) * y[i] = wFrom c y := by
  induction y with
  | nil => intro c; simp [wFrom]
  | cons a l ih =>
    intro c
    have h := ih (c + 1)
    show ∑ i : Fin (l.length + 1), (i.val + c) * (a :: l)[i] = wFrom c (a :: l)
    rw [Fin.sum_univ_succ]
    have e : ∀ i : Fin l.length,
        ((i.succ : Fin (l.length + 1)).val + c) * (a :: l)[i.succ] = (i.val + (c + 1)) * l[i] := by
      intro i
      have h1 : (a :: l)[i.succ] = l[i] := by simp
      rw [h1, Fin.val_succ]
      ring
    rw [Finset.sum_congr rfl (fun i _ => e i), h]
    simp [wFrom]

theorem wFrom_append_single (l : List ℕ) (a : ℕ) :
    ∀ c : ℕ, wFrom c (l ++ [a]) = wFrom c l + (c + l.length) * a := by
  induction l with
  | nil => intro c; simp [wFrom]
  | cons b l ih =>
    intro c
    have h := ih (c + 1)
    simp only [List.cons_append, wFrom, List.length_cons]
    rw [h]
    ring

theorem wFrom_succ (l : List ℕ) : ∀ c : ℕ, wFrom (c + 1) l = wFrom c l + l.sum := by
  induction l with
  | nil => intro c; simp [wFrom]
  | cons b l ih =>
    intro c
    have h := ih (c + 1)
    simp only [wFrom, List.sum_cons]
    rw [h]
    ring

theorem wFrom_add_reverse (l : List ℕ) :
    wFrom 1 l + wFrom 1 l.reverse = (l.length + 1) * l.sum := by
  induction l with
  | nil => simp [wFrom]
  | cons a l ih =>
    have h1 : wFrom 1 (a :: l) = a + wFrom 1 l + l.sum := by
      simp only [wFrom]
      rw [wFrom_succ l 1]
      ring
    have h2 : wFrom 1 (a :: l).reverse = wFrom 1 l.reverse + (1 + l.length) * a := by
      rw [List.reverse_cons, wFrom_append_single, List.length_reverse]
    rw [h1, h2, List.length_cons, List.sum_cons]
    have h3 : a + wFrom 1 l + l.sum + (wFrom 1 l.reverse + (1 + l.length) * a)
        = (wFrom 1 l + wFrom 1 l.reverse) + l.sum + (l.length + 2) * a := by ring
    rw [h3, ih]
    ring

theorem weightedSum_eq (y : List ℕ) : OMA.S_oeis_a362559.weightedSum y = wFrom 1 y := by
  unfold OMA.S_oeis_a362559.weightedSum
  exact fin_sum_eq y 1

end OMA.A362559

theorem OMA.solution : type_of% @OMA.S_oeis_a362559.main := by
  intro n y _ hy
  obtain ⟨_, _, hsum⟩ := hy
  have key : OMA.S_oeis_a362559.weightedSum y + OMA.S_oeis_a362559.weightedSum y.reverse
      = (y.length + 1) * n := by
    rw [OMA.A362559.weightedSum_eq, OMA.A362559.weightedSum_eq, OMA.A362559.wFrom_add_reverse, hsum]
  have hd : n ∣ OMA.S_oeis_a362559.weightedSum y + OMA.S_oeis_a362559.weightedSum y.reverse := by
    rw [key]
    exact Dvd.intro_left _ rfl
  constructor
  · intro h
    exact (Nat.dvd_add_right h).1 hd
  · intro h
    exact (Nat.dvd_add_left h).1 hd
