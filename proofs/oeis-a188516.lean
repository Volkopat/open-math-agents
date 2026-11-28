import OMAStatements.S_oeis_a188516
import Mathlib

open OMA.S_oeis_a188516


namespace P188516

/-- Column entry accessor. -/
def gc {n : ℕ} (g : Fin n → Bool) (i : ℕ) : Bool := if h : i < n then g ⟨i, h⟩ else false

/-- A column without 1 1 0 read downward. -/
def cg {n : ℕ} (g : Fin n → Bool) : Prop :=
  ∀ i, i + 2 < n → ¬ (gc g i = true ∧ gc g (i + 1) = true ∧ gc g (i + 2) = false)

instance {n : ℕ} : DecidablePred (@cg n) := fun g => by
  unfold cg
  exact decidable_of_iff (∀ i < n, i + 2 < n → ¬ (gc g i = true ∧ gc g (i + 1) = true ∧ gc g (i + 2) = false))
    ⟨fun h i hi => h i (by omega) hi, fun h i _ hi => h i hi⟩

theorem good_iff {n : ℕ} (f : Fin n → Fin 2 → Bool) :
    good f ↔ cg (fun i => f i 0) ∧ cg (fun i => f i 1) := by
  have hc0 : ∀ i, cell f i 0 = gc (fun r => f r 0) i := by
    intro i; unfold cell gc; by_cases h : i < n <;> simp [h]
  have hc1 : ∀ i, cell f i 1 = gc (fun r => f r 1) i := by
    intro i; unfold cell gc; by_cases h : i < n <;> simp [h]
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have := (h ⟨i, by omega⟩ 0).1
      simp only [occurs, Fin.val_zero, Fin.isValue] at this
      rw [← hc0, ← hc0, ← hc0]
      intro ⟨h1, h2, h3⟩
      exact this ⟨by omega, by omega, by omega, by omega, by omega, by omega, h1, h2, h3⟩
    · have := (h ⟨i, by omega⟩ 1).1
      simp only [occurs, Fin.val_one, Fin.isValue] at this
      rw [← hc1, ← hc1, ← hc1]
      intro ⟨h1, h2, h3⟩
      exact this ⟨by omega, by omega, by omega, by omega, by omega, by omega, h1, h2, h3⟩
  · rintro ⟨h0, h1⟩ ⟨i, hi⟩ ⟨j, hj⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro ⟨_, _, _, _, hi2, _, e1, e2, e3⟩
      simp only at e1 e2 e3 ⊢
      interval_cases j
      · exact h0 i (by simpa using hi2)
          ⟨by rw [← hc0]; exact e1, by rw [← hc0]; exact e2, by rw [← hc0]; exact e3⟩
      · exact h1 i (by simpa using hi2)
          ⟨by rw [← hc1]; exact e1, by rw [← hc1]; exact e2, by rw [← hc1]; exact e3⟩
    · rintro ⟨_, _, _, _, _, hj2, _⟩; omega
    · rintro ⟨_, _, _, _, _, hj2, _⟩; omega
    · rintro ⟨_, hj2, _⟩; omega

theorem sum_cons {n : ℕ} (F : (Fin (n + 1) → Bool) → ℕ) :
    ∑ f, F f = ∑ x : Bool, ∑ g : Fin n → Bool, F (Fin.cons x g) := by
  rw [← (Fin.consEquiv (fun _ => Bool)).sum_comp, Fintype.sum_prod_type]
  rfl

theorem gc_zero {n : ℕ} (x : Bool) (g : Fin n → Bool) : gc (Fin.cons x g : Fin (n + 1) → Bool) 0 = x := by
  simp [gc]

theorem gc_succ {n : ℕ} (x : Bool) (g : Fin n → Bool) (i : ℕ) :
    gc (Fin.cons x g : Fin (n + 1) → Bool) (i + 1) = gc g i := by
  unfold gc
  by_cases h : i < n
  · rw [dif_pos (by omega), dif_pos h]
    exact Fin.cons_succ (α := fun _ => Bool) x g ⟨i, h⟩
  · rw [dif_neg (by omega), dif_neg h]

theorem cg_cons {n : ℕ} (x y z : Bool) (g : Fin n → Bool) :
    cg (Fin.cons x (Fin.cons y (Fin.cons z g : Fin (n + 1) → Bool) : Fin (n + 2) → Bool) : Fin (n + 3) → Bool) ↔
      ¬ (x = true ∧ y = true ∧ z = false) ∧ cg (Fin.cons y (Fin.cons z g : Fin (n + 1) → Bool) : Fin (n + 2) → Bool) := by
  unfold cg
  constructor
  · intro h
    refine ⟨?_, fun i hi => ?_⟩
    · have := h 0 (by omega)
      simpa [gc_zero, gc_succ] using this
    · have := h (i + 1) (by omega)
      simpa only [gc_succ] using this
  · rintro ⟨h0, h⟩ i hi
    rcases i with _ | i
    · simpa [gc_zero, gc_succ] using h0
    · have := h i (by omega)
      simpa only [gc_succ] using this

/-- Good columns of length `n + 2` starting with `x, y`. -/
def H (n : ℕ) (x y : Bool) : ℕ :=
  ∑ g : Fin n → Bool, if cg (Fin.cons x (Fin.cons y g : Fin (n + 1) → Bool) : Fin (n + 2) → Bool) then 1 else 0

theorem H_succ (n : ℕ) (x y : Bool) :
    H (n + 1) x y = ∑ z : Bool, if ¬ (x = true ∧ y = true ∧ z = false) then H n y z else 0 := by
  rw [H, sum_cons]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hz : x = true ∧ y = true ∧ z = false
  · rw [if_neg (not_not.mpr hz)]
    refine Finset.sum_eq_zero fun g _ => ?_
    obtain ⟨rfl, rfl, rfl⟩ := hz
    simp [cg_cons]
  · rw [if_pos hz, H]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp only [cg_cons, hz, not_false_eq_true, true_and]

theorem H0 (x y : Bool) : H 0 x y = 1 := by
  rw [H, Fintype.sum_unique, if_pos]
  intro i hi
  omega

theorem Hs (n : ℕ) :
    H (n + 1) false false = H n false false + H n false true ∧
    H (n + 1) false true = H n true false + H n true true ∧
    H (n + 1) true false = H n false false + H n false true ∧
    H (n + 1) true true = H n true true := by
  simp only [H_succ, Fintype.sum_bool]
  simp
  omega

theorem H11 (n : ℕ) : H n true true = 1 := by
  induction n with
  | zero => exact H0 _ _
  | succ n ih => rw [(Hs n).2.2.2, ih]

theorem SF (n : ℕ) :
    H n false false + H n false true + H n true false + H n true true + 1 = Nat.fib (n + 5) ∧
    H n false false + H n false true + 1 = Nat.fib (n + 4) := by
  induction n with
  | zero => simp [H0, Nat.fib_add_two]
  | succ n ih =>
    obtain ⟨e1, e2, e3, e4⟩ := Hs n
    have h11 := H11 n
    have f6 : Nat.fib (n + 6) = Nat.fib (n + 4) + Nat.fib (n + 5) := Nat.fib_add_two
    rw [show n + 1 + 5 = n + 6 by omega, show n + 1 + 4 = n + 5 by omega, e1, e2, e3, e4]
    omega

/-- The number of good columns of length `n`. -/
def c (n : ℕ) : ℕ := ∑ g : Fin n → Bool, if cg g then 1 else 0

theorem c_ss (n : ℕ) : c (n + 2) + 1 = Nat.fib (n + 5) := by
  have h : c (n + 2) = H n false false + H n false true + H n true false + H n true true := by
    rw [c, sum_cons, Fintype.sum_bool, sum_cons, sum_cons, Fintype.sum_bool, Fintype.sum_bool]
    simp only [H]
    ring
  rw [h]; exact (SF n).1

theorem c1 : c 1 = 2 := by
  rw [c, sum_cons, Fintype.sum_bool, Fintype.sum_unique, Fintype.sum_unique, if_pos, if_pos] <;>
    · intro i hi; omega

theorem a_eq (n : ℕ) : a n = c n ^ 2 := by
  let e : (Fin n → Fin 2 → Bool) ≃ (Fin n → Bool) × (Fin n → Bool) :=
    { toFun := fun f => (fun i => f i 0, fun i => f i 1)
      invFun := fun p i j => if j = 0 then p.1 i else p.2 i
      left_inv := fun f => by
        funext i j
        fin_cases j <;> simp
      right_inv := fun p => by simp }
  rw [a, Finset.card_filter, ← e.symm.sum_comp, Fintype.sum_prod_type, c, sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun g0 _ => Finset.sum_congr rfl fun g1 _ => ?_
  have h1 : (fun i => (e.symm (g0, g1)) i 0) = g0 := by funext i; simp [e]
  have h2 : (fun i => (e.symm (g0, g1)) i 1) = g1 := by funext i; simp [e]
  have hg : good (e.symm (g0, g1)) ↔ cg g0 ∧ cg g1 := by rw [good_iff, h1, h2]
  by_cases p : cg g0 <;> by_cases q : cg g1 <;> simp [hg, p, q]

end P188516

theorem OMA.solution : type_of% @OMA.S_oeis_a188516.main := by
  intro n hn
  rw [P188516.a_eq]
  rcases n with _ | _ | n
  · omega
  · rw [P188516.c1]; rfl
  · have := P188516.c_ss n
    show P188516.c (n + 2) ^ 2 = (Nat.fib (n + 5) - 1) ^ 2
    rw [show P188516.c (n + 2) = Nat.fib (n + 5) - 1 by omega]
