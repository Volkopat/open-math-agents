import OMAStatements.S_oeis_a187170
import Mathlib.Tactic

/-! At widths at least 8, every translate count is a polynomial of degree
at most 3. Its finite difference of order 4 vanishes. The proof applies
this identity to each actual walk shape and checks the initial coefficients. -/

namespace LatticeWalk170
open OMA.S_oeis_a187170

def total (n : ℕ) (xs : List Profile) : ℤ := (xs.map (placed n)).sum

@[simp] lemma total_nil (n : ℕ) : total n [] = 0 := rfl
@[simp] lemma total_cons (n : ℕ) (p : Profile) (ps : List Profile) :
    total n (p::ps) = placed n p + total n ps := rfl

lemma total_append (n : ℕ) (xs ys : List Profile) :
    total n (xs ++ ys) = total n xs + total n ys := by
  simp [total, List.map_append]

/-- Branch on the three spans as a single integer. Correctness of the sum
only uses the exact span comparison in the first branch. -/
def spanKey (s : Span) : ℕ := (9*s.1 + s.2.1)*9 + s.2.2

inductive Bins where
  | empty
  | node (p : Profile) (lo hi : Bins)
  deriving DecidableEq

def Bins.insert (p : Profile) : Bins → Bins
  | .empty => .node p .empty .empty
  | .node q lo hi =>
    if p.2 = q.2 then .node (p.1 + q.1, q.2) lo hi
    else if spanKey p.2 < spanKey q.2 then .node q (lo.insert p) hi
    else .node q lo (hi.insert p)

def Bins.weight (n : ℕ) : Bins → ℤ
  | .empty => 0
  | .node p lo hi => placed n p + lo.weight n + hi.weight n

def Bins.clear : Bins → Bins
  | .empty => .empty
  | .node p lo hi => .node (0, p.2) lo.clear hi.clear

def Bins.entries : Bins → List Profile
  | .empty => []
  | .node p lo hi => p :: (lo.entries ++ hi.entries)

lemma clearWeight (n : ℕ) (b : Bins) : b.clear.weight n = 0 := by
  induction b with
  | empty => rfl
  | node p lo hi ih jh => simp [Bins.clear, Bins.weight, placed, ih, jh]

lemma entriesWeight (n : ℕ) (b : Bins) : total n b.entries = b.weight n := by
  induction b with
  | empty => rfl
  | node p lo hi ih jh => simp [Bins.entries, Bins.weight, total_append, ih, jh, add_assoc]

lemma insertWeight (n : ℕ) (p : Profile) (b : Bins) :
    (b.insert p).weight n = placed n p + b.weight n := by
  induction b with
  | empty => simp [Bins.insert, Bins.weight]
  | node q lo hi ih jh =>
    obtain ⟨u, s⟩ := p
    obtain ⟨v, t⟩ := q
    by_cases eq : s = t
    · subst t
      simp [Bins.insert, Bins.weight, placed, Nat.cast_add]
      ring
    · by_cases smaller : spanKey s < spanKey t
      · simp [Bins.insert, eq, smaller, Bins.weight, ih, add_left_comm, add_assoc, add_comm]
      · simp [Bins.insert, eq, smaller, Bins.weight, jh, add_left_comm, add_assoc, add_comm]

lemma foldWeight (n : ℕ) (xs : List Profile) (seed : Bins) :
    (xs.foldl (fun acc p => acc.insert p) seed).weight n = total n xs + seed.weight n := by
  induction xs generalizing seed with
  | nil => simp
  | cons p ps ih => simp [List.foldl_cons, ih, insertWeight, add_left_comm, add_comm]

/-- The coordinate-span histogram. Each row is the total multiplicity and
three spans. The tree starts with these keys at zero before counting walks. -/
def bins : Bins :=
  (.node (9024, 2, 4, 1)
  (.node (2016, 1, 5, 1)
    (.node (288, 1, 2, 5)
      (.node (48, 1, 1, 6)
        (.node (2064, 1, 1, 4)
          (.node (3600, 1, 1, 3)
            (.node (2448, 1, 1, 2)
              .empty
              .empty)
            .empty)
          (.node (528, 1, 1, 5)
            .empty
            .empty))
        (.node (8112, 1, 2, 3)
          (.node (12432, 1, 2, 2)
            (.node (2928, 1, 2, 1)
              .empty
              .empty)
            .empty)
          (.node (2496, 1, 2, 4)
            .empty
            .empty)))
      (.node (168, 1, 4, 0)
        (.node (4320, 1, 3, 3)
          (.node (10128, 1, 3, 2)
            (.node (6816, 1, 3, 1)
              .empty
              .empty)
            .empty)
          (.node (720, 1, 3, 4)
            .empty
            .empty))
        (.node (960, 1, 4, 3)
          (.node (4320, 1, 4, 2)
            (.node (5136, 1, 4, 1)
              .empty
              .empty)
            .empty)
          (.node (264, 1, 5, 0)
            .empty
            .empty))))
    (.node (120, 2, 2, 0)
      (.node (3120, 2, 1, 1)
        (.node (288, 1, 6, 1)
          (.node (144, 1, 6, 0)
            (.node (720, 1, 5, 2)
              .empty
              .empty)
            .empty)
          (.node (24, 1, 7, 0)
            .empty
            .empty))
        (.node (2928, 2, 1, 4)
          (.node (9840, 2, 1, 3)
            (.node (14880, 2, 1, 2)
              .empty
              .empty)
            .empty)
          (.node (336, 2, 1, 5)
            .empty
            .empty)))
      (.node (1176, 2, 3, 0)
        (.node (11232, 2, 2, 3)
          (.node (30720, 2, 2, 2)
            (.node (23664, 2, 2, 1)
              .empty
              .empty)
            .empty)
          (.node (1680, 2, 2, 4)
            .empty
            .empty))
        (.node (3360, 2, 3, 3)
          (.node (15168, 2, 3, 2)
            (.node (21168, 2, 3, 1)
              .empty
              .empty)
            .empty)
          (.node (1536, 2, 4, 0)
            .empty
            .empty)))))
  (.node (7968, 4, 1, 1)
    (.node (23664, 3, 2, 1)
      (.node (9408, 3, 1, 1)
        (.node (1680, 2, 5, 1)
          (.node (768, 2, 5, 0)
            (.node (3360, 2, 4, 2)
              .empty
              .empty)
            .empty)
          (.node (168, 2, 6, 0)
            .empty
            .empty))
        (.node (1008, 3, 1, 4)
          (.node (5808, 3, 1, 3)
            (.node (13872, 3, 1, 2)
              .empty
              .empty)
            .empty)
          (.node (1440, 3, 2, 0)
            .empty
            .empty)))
      (.node (6048, 3, 3, 2)
        (.node (2208, 3, 3, 0)
          (.node (4032, 3, 2, 3)
            (.node (17280, 3, 2, 2)
              .empty
              .empty)
            .empty)
          (.node (13392, 3, 3, 1)
            .empty
            .empty))
        (.node (504, 3, 5, 0)
          (.node (4032, 3, 4, 1)
            (.node (1248, 3, 4, 0)
              .empty
              .empty)
            .empty)
          (.node (264, 4, 1, 0)
            .empty
            .empty))))
    (.node (4176, 5, 1, 1)
      (.node (5040, 4, 2, 2)
        (.node (1800, 4, 2, 0)
          (.node (1680, 4, 1, 3)
            (.node (6960, 4, 1, 2)
              .empty
              .empty)
            .empty)
          (.node (12240, 4, 2, 1)
            .empty
            .empty))
        (.node (840, 4, 4, 0)
          (.node (5040, 4, 3, 1)
            (.node (1440, 4, 3, 0)
              .empty
              .empty)
            .empty)
          (.node (456, 5, 1, 0)
            .empty
            .empty)))
      (.node (408, 6, 1, 0)
        (.node (3360, 5, 2, 1)
          (.node (1248, 5, 2, 0)
            (.node (1680, 5, 1, 2)
              .empty
              .empty)
            .empty)
          (.node (840, 5, 3, 0)
            .empty
            .empty))
        (.node (168, 7, 1, 0)
          (.node (504, 6, 2, 0)
            (.node (1008, 6, 1, 1)
              .empty
              .empty)
            .empty)
          (.node (6, 8, 0, 0)
            .empty
            .empty))))))

def table := bins.entries

set_option maxRecDepth 60000 in
set_option maxHeartbeats 8000000 in
lemma census : shapes.foldl (fun acc p => acc.insert p) bins.clear = bins := by
  decide +kernel

lemma useTable (n : ℕ) : sequence n = total n table := by
  have h := foldWeight n shapes bins.clear
  rw [census, clearWeight, add_zero] at h
  exact h.symm.trans (entriesWeight n bins).symm

abbrev bounded (w : Profile) := w.2.1 ≤ 8 ∧ w.2.2.1 ≤ 8 ∧ w.2.2.2 ≤ 8

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
lemma shapeBound : ∀ w ∈ table, bounded w := by
  have h : table.all (fun w => decide (bounded w)) = true := by decide +kernel
  intro w hw
  exact of_decide_eq_true (List.all_eq_true.mp h w hw)

lemma one (k : ℕ) (w : Profile) (ok : bounded w) : placed (k+12) w - 4*placed (k+11) w + 6*placed (k+10) w - 4*placed (k+9) w + placed (k+8) w = 0 := by
  obtain ⟨h0,h1,h2⟩ := ok
  simp (disch := omega) only [placed,Nat.cast_sub,Nat.cast_add,Nat.cast_ofNat]
  ring

lemma linearSum (k : ℕ) (xs : List Profile) (ok : ∀ w ∈ xs, bounded w) :
    (xs.map (placed (k+12))).sum - 4*(xs.map (placed (k+11))).sum + 6*(xs.map (placed (k+10))).sum - 4*(xs.map (placed (k+9))).sum + (xs.map (placed (k+8))).sum = 0 := by
  induction xs with
  | nil => simp
  | cons w xs ih =>
    have hw := one k w (ok w (by simp))
    have hx := ih (fun v hv => ok v (List.mem_cons_of_mem w hv))
    simp only [List.map_cons,List.sum_cons]
    linear_combination hw + hx

lemma recurrence (k : ℕ) : sequence (k+12) - 4*sequence (k+11) + 6*sequence (k+10) - 4*sequence (k+9) + sequence (k+8) = 0 := by
  simp only [useTable]
  exact linearSum k table shapeBound

def finiteLag (d n : ℕ) : ℤ := if d ≤ n then total (n-d) table else 0

lemma lag_eq (d n : ℕ) : lag d n = finiteLag d n := by
  simp [lag, finiteLag, useTable]

set_option maxRecDepth 26000 in
set_option maxHeartbeats 3000000 in
lemma initial : ∀ n : Fin 12, lag 0 n.val - 4*lag 1 n.val + 6*lag 2 n.val - 4*lag 3 n.val + lag 4 n.val = numerator n.val := by
  simp only [lag_eq]
  decide +kernel

lemma gf (n : ℕ) : lag 0 n - 4*lag 1 n + 6*lag 2 n - 4*lag 3 n + lag 4 n = numerator n := by
  by_cases hn : n < 12
  · exact initial ⟨n,hn⟩
  · obtain ⟨k,rfl⟩ : ∃ k : ℕ, n = k+12 := ⟨n-12,by omega⟩
    change sequence (k+12) - 4*sequence (k+11) + 6*sequence (k+10) - 4*sequence (k+9) + sequence (k+8) = 0
    exact recurrence k

end LatticeWalk170

theorem OMA.solution : type_of% @OMA.S_oeis_a187170.main := by
  refine ⟨LatticeWalk170.gf, ?_⟩
  intro k
  linear_combination LatticeWalk170.recurrence k
