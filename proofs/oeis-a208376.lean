import OMAStatements.S_oeis_a208376
import Mathlib

namespace A208376Proof

open OMA.S_oeis_a208376

abbrev Row := Fin 5 → Fin 2

def good (r : Row) : Prop :=
  ∀ j : Fin 3,
    (r ⟨j.val, by omega⟩, r ⟨j.val + 1, by omega⟩, r ⟨j.val + 2, by omega⟩) ≠ (0,0,0) ∧
    (r ⟨j.val, by omega⟩, r ⟨j.val + 1, by omega⟩, r ⟨j.val + 2, by omega⟩) ≠ (1,1,1)

instance (r : Row) : Decidable (good r) := by unfold good; infer_instance

def below (s r : Row) : Prop := ∀ j, s j ≤ r j

instance (s r : Row) : Decidable (below s r) := by unfold below; infer_instance

def topRow : Row := fun _ => 1

/-- Add one legal row beneath the previous row, respecting coordinatewise order. -/
def T (f : Row → ℤ) (r : Row) : ℤ :=
  ∑ s : Row, if good s ∧ below s r then f s else 0

def C : ℕ → Row → ℤ
  | 0, _ => 1
  | n+1, r => T (C n) r

/-- All rows are legal, consecutive rows decrease, and the first is bounded by u. -/
private def Chain {n : ℕ} (u : Row) (w : Fin n → Row) : Prop :=
  (∀ i, good (w i)) ∧
  (∀ i j : Fin n, j.val = i.val + 1 → below (w j) (w i)) ∧
  (∀ i : Fin n, i.val = 0 → below (w i) u)

private theorem chain_cons {n : ℕ} (u s : Row) (w : Fin n → Row) :
    Chain u (Fin.cons s w) ↔ (good s ∧ below s u) ∧ Chain s w := by
  simp [Chain, Fin.forall_fin_succ]
  aesop

private theorem hpattern (x y z : Fin 2) :
    ((x.val,y.val,z.val) ≠ (0,0,0) ∧ (x.val,y.val,z.val) ≠ (1,1,1)) ↔
       ((x,y,z) ≠ (0,0,0) ∧ (x,y,z) ≠ (1,1,1)) := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;> decide

/-- Avoiding both vertical patterns is equivalent to the last bit being at most the middle bit. -/
private theorem vpattern (x y z : Fin 2) :
    ((x.val,y.val,z.val) ≠ (0,0,1) ∧ (x.val,y.val,z.val) ≠ (1,0,1)) ↔ z ≤ y := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;> decide

private theorem avoids_iff {n : ℕ} (w : Fin n → Row) :
    avoids w = true ↔ (∀ i, good (w i)) ∧
       (∀ i j : Fin n, 0 < i.val → j.val = i.val + 1 → below (w j) (w i)) := by
  simp only [avoids, decide_eq_true_eq]
  apply and_congr
  · constructor
    · intro h i t
      have p := h i.val i.isLt t.val (by omega)
      apply (hpattern _ _ _).mp
      simpa only [OMA.S_oeis_a208376.get, i.isLt, t.isLt, show t.val < 5 by omega, show t.val + 1 < 5 by omega,
        show t.val + 2 < 5 by omega, true_and, and_true, dite_true, Fin.eta] using p
    · intro h i hi j hj
      have p := h ⟨i, hi⟩ ⟨j, by omega⟩
      simpa only [OMA.S_oeis_a208376.get, hi, hj, show j < 5 by omega, show j+1 < 5 by omega,
        show j+2 < 5 by omega, true_and, and_true, dite_true, Fin.eta] using (hpattern _ _ _).mpr p
  · constructor
    · intro h i j hi hij c
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (show i.val ≠ 0 by omega)
      have p := h k (by omega) c.val c.isLt
      have hk0 : k < n := by omega
      have hk1 : k+1 < n := by omega
      have hk2 : k+2 < n := by omega
      have hi' : (⟨k+1,hk1⟩ : Fin n) = i := Fin.ext (by dsimp; omega)
      have hj' : (⟨k+2,hk2⟩ : Fin n) = j := Fin.ext (by dsimp; omega)
      simp only [OMA.S_oeis_a208376.get, hk0, hk1, hk2, c.isLt, and_true, dite_true, Fin.eta, hi', hj'] at p
      exact (vpattern _ _ _).mp p
    · intro h k hk c hc
      have hk0 : k < n := by omega
      have hk1 : k+1 < n := by omega
      have hk2 : k+2 < n := by omega
      have p := h ⟨k+1,hk1⟩ ⟨k+2,hk2⟩ (by simp) (by simp) ⟨c,hc⟩
      simp only [OMA.S_oeis_a208376.get, hk0, hk1, hk2, hc, and_true, dite_true]
      exact (vpattern _ _ _).mpr p

private theorem avoids_cons {n : ℕ} (s : Row) (w : Fin n → Row) :
    avoids (Fin.cons s w) = true ↔ good s ∧ Chain topRow w := by
  have ht (r : Row) : below r topRow := by
    intro j
    change r j ≤ (1 : Fin 2)
    exact_mod_cast (show (r j).val ≤ 1 by omega)
  simp [avoids_iff, Chain, Fin.forall_fin_succ, ht, and_assoc]

private theorem sum_rows {n : ℕ} (f : (Fin (n+1) → Row) → ℤ) :
    (∑ w, f w) = ∑ r : Row, ∑ w : Fin n → Row, f (Fin.cons r w) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Row)).sum_comp f, Fintype.sum_prod_type]
  rfl

private noncomputable def words {n : ℕ} (u : Row) : ℤ := by
  classical
  exact ∑ w : Fin n → Row, if Chain u w then 1 else 0

private theorem words_eq (n : ℕ) (u : Row) : @words n u = C n u := by
  classical
  induction n generalizing u with
  | zero =>
    have hc (w : Fin 0 → Row) : Chain u w := by simp [Chain]
    simp [words,hc,C]
  | succ n ih =>
    unfold words
    rw [sum_rows]
    simp only [chain_cons, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero]
    change (∑ s : Row, if good s then if below s u then @words n s else 0 else 0) = _
    simp only [ih,C,T,ite_and]

/-- The first row is independent of the decreasing sequence of rows underneath it. -/
theorem count_arrays (n : ℕ) (hcount : (∑ s : Row, if good s then (1 : ℤ) else 0) = 16) :
    a (n+1) = 16 * C n topRow := by
  classical
  unfold a
  rw [← Finset.sum_boole, sum_rows]
  simp only [avoids_cons, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero]
  change (∑ s : Row, if good s then @words n topRow else 0) = _
  rw [words_eq, ← hcount, Finset.sum_mul]
  simp only [ite_mul, one_mul, zero_mul]

theorem good_count : (∑ s : Row, if good s then (1 : ℤ) else 0) = 16 := by
  decide +kernel

set_option maxHeartbeats 800000 in
/-- Check the finite-difference recurrence at every one of the 32 possible upper bounds. -/
private theorem chain_base : ∀ r : Row, C 4 r = 3*C 3 r - 3*C 2 r + C 1 r := by
  decide +kernel

private theorem top_initial :
    C 1 topRow = 16 ∧ C 2 topRow = 44 ∧ C 3 topRow = 84 := by
  decide +kernel
private theorem transfer_rec (f g h k : Row → ℤ)
    (heq : ∀ r, f r = 3*g r - 3*h r + k r) (r : Row) :
    T f r = 3*T g r - 3*T h r + T k r := by
  simp only [T, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : good s ∧ below s r <;> simp [hs, heq]

private theorem chain_rec (n : ℕ) (r : Row) :
    C (n+4) r = 3*C (n+3) r - 3*C (n+2) r + C (n+1) r := by
  induction n generalizing r with
  | zero => exact chain_base r
  | succ n ih => exact transfer_rec _ _ _ _ ih r

theorem chain_formula (n : ℕ) : C (n+1) topRow = 6*(n:ℤ)^2 + 22*n + 16 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 3
    · interval_cases n <;> norm_num [top_initial.1, top_initial.2.1, top_initial.2.2]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k+3 := ⟨n-3, by omega⟩
      rw [chain_rec k, ih (k+2) (by omega), ih (k+1) (by omega), ih k (by omega)]
      push_cast
      ring

open PowerSeries

private theorem recurrenceFromCount (count : ∀ k : ℕ,
    (a (k+2) : ℚ) = 96*(k:ℚ)^2+352*k+256) (n : ℕ) (hn : 5 ≤ n) :
    (a n : ℚ) = 3*a (n-1)-3*a (n-2)+a (n-3) := by
  obtain ⟨k,rfl⟩ : ∃ k : ℕ, n=k+5 := ⟨n-5, by omega⟩
  change (a ((k+3)+2) : ℚ) = 3*a ((k+2)+2)-3*a ((k+1)+2)+a (k+2)
  simp only [count, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  ring

theorem seriesFromCount (first : a 1=16) (count : ∀ k : ℕ,
    (a (k+2) : ℚ) = 96*(k:ℚ)^2+352*k+256) :
    (mk (fun n => if n < 1 then 0 else (a n : ℚ)) * (1-X)^3 =
        16*X*(1+13*X-X^2-X^3)) ∧ (∀ n : ℕ, 5 ≤ n →
      (a n : ℚ) = 3*a (n-1)-3*a (n-2)+a (n-3)) := by
  refine ⟨?_,recurrenceFromCount count⟩
  let A : ℚ⟦X⟧ := mk fun n => if n<1 then 0 else (a n:ℚ)
  change A*_ = _
  have den : A*(1-X)^3 = A-(A*X^1+A*X^1+A*X^1)+(A*X^2+A*X^2+A*X^2)-A*X^3 := by ring
  have num : 16*(X : ℚ⟦X⟧)*(1+13*X-X^2-X^3)=PowerSeries.C (16:ℚ)*X^1+PowerSeries.C (208:ℚ)*X^2-PowerSeries.C (16:ℚ)*X^3-PowerSeries.C (16:ℚ)*X^4 := by
    simp only [map_ofNat]; ring
  rw [den,num]
  ext n
  simp only [map_sub,map_add,coeff_C_mul_X_pow]
  simp only [coeff_mul_X_pow',A,coeff_mk]
  by_cases small : n ≤ 4
  · have h2 := count 0
    have h3 := count 1
    have h4 := count 2
    norm_num at h2 h3 h4
    interval_cases n <;> norm_num [first,h2,h3,h4]
  · simp (disch := omega) only [if_pos,if_neg]
    linarith [recurrenceFromCount count n (by omega)]

end A208376Proof

open A208376Proof OMA.S_oeis_a208376 in
theorem OMA.solution : type_of% @OMA.S_oeis_a208376.main := by
  apply seriesFromCount
  · exact (count_arrays 0 good_count).trans (by decide)
  · intro k
    rw [count_arrays (k+1) good_count, chain_formula]
    push_cast
    ring
