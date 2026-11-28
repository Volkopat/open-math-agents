import OMAReductions.R_oeis_a000009_R10

/-!
# Counting candidates for the representation step of A000009

At x = n / 2 + 1, R10 can descend from n using a primitive strict partition
value in [x, 3*x/2]. Remove values divisible by a partition value s ≥ 1000
with s² ≤ x. Count the remaining values and the distinct values among them
that still have a proper partition divisor. For the latter, only cofactors k
with 2*k² < 3*a need to be considered. The cutoff for x comes from R10's
256-value base. Both uniform counting estimates below are open.
-/
namespace OMA.R_oeis_a000009_R10_H1_R1
open OMA.S_oeis_a000009

/-- Check supply at the initial window, a threshold rise, or a possible loss:
the old left endpoint departs, or a partition divisor reaches the square cutoff. -/
def H1 : Prop :=
  let Q := fun a : ℕ => ∃ m : ℕ, 0 < m ∧ a = strictPartitionCount m
  let live := fun x a : ℕ => Q a ∧ x ≤ a ∧ 2*a ≤ 3*x ∧
    ∀ s, 1000 ≤ s → Q s → s*s ≤ x → ¬ s ∣ a
  let start : ℕ := 30020900773769688559070113208459541809716021698140392739697
  ∀ x : ℕ, start ≤ x →
    (x = start ∨ (x-1).log2 / 32 < x.log2 / 32 ∨ live (x-1) (x-1) ∨
      ∃ a s, live (x-1) a ∧ 1000 ≤ s ∧ Q s ∧ s*s = x ∧ s ∣ a) →
    ∃ A : Finset ℕ, x.log2 / 32 < A.card ∧ ∀ a ∈ A, live x a

/-- Check exceptions initially and when an exceptional surviving value enters
at the right endpoint. Departures can only improve this bound. -/
def H2 : Prop :=
  let Q := fun a : ℕ => ∃ m : ℕ, 0 < m ∧ a = strictPartitionCount m
  let live := fun x a : ℕ => Q a ∧ x ≤ a ∧ 2*a ≤ 3*x ∧
    ∀ s, 1000 ≤ s → Q s → s*s ≤ x → ¬ s ∣ a
  let exceptional := fun a : ℕ =>
    ∃ k : ℕ, 2 ≤ k ∧ 2*k*k < 3*a ∧ k ∣ a ∧ 1000 ≤ a/k ∧ Q (a/k)
  let start : ℕ := 30020900773769688559070113208459541809716021698140392739697
  ∀ x : ℕ, start ≤ x →
    (x = start ∨ ∃ a, live x a ∧ exceptional a ∧ 3*(x-1) < 2*a) →
    ∀ B : Finset ℕ, (∀ a ∈ B, live x a ∧ exceptional a) → B.card ≤ x.log2 / 32

/-- These supply checks are equivalent to the estimate at every window. -/
theorem supply_at_events_iff (Q : ℕ → Prop) (t : ℕ → ℕ) (start : ℕ) :
  let live := fun x a : ℕ => Q a ∧ x ≤ a ∧ 2*a ≤ 3*x ∧
    ∀ s, 1000 ≤ s → Q s → s*s ≤ x → ¬ s ∣ a
  (∀ x : ℕ, start ≤ x → (x = start ∨ t (x-1) < t x ∨ live (x-1) (x-1) ∨
      ∃ a s, live (x-1) a ∧ 1000 ≤ s ∧ Q s ∧ s*s = x ∧ s ∣ a) →
    ∃ A : Finset ℕ, t x < A.card ∧ ∀ a ∈ A, live x a) ↔
  (∀ x : ℕ, start ≤ x → ∃ A : Finset ℕ, t x < A.card ∧ ∀ a ∈ A, live x a) := by
  intro live
  constructor
  · intro checks x hx
    induction x, hx using Nat.le_induction with
    | base => exact checks _ le_rfl (Or.inl rfl)
    | succ x hx ih =>
      by_cases rise : t x < t (x+1)
      · exact checks _ (by omega) (Or.inr (Or.inl (by simpa using rise)))
      by_cases leaves : live x x
      · exact checks _ (by omega) (Or.inr (Or.inr (Or.inl (by simpa using leaves))))
      by_cases square : ∃ a s, live x a ∧ 1000 ≤ s ∧ Q s ∧ s*s = x+1 ∧ s ∣ a
      · exact checks _ (by omega) (Or.inr (Or.inr (Or.inr (by simpa using square))))
      obtain ⟨A,count,good⟩ := ih
      refine ⟨A,by omega,?_⟩
      intro a ha
      have old := good a ha
      obtain ⟨qa,low,high,clean⟩ := good a ha
      have ne : a ≠ x := fun eq => leaves (eq ▸ old)
      refine ⟨qa,by omega,by omega,?_⟩
      intro s hs qs size divides
      by_cases prev : s*s ≤ x
      · exact clean s hs qs prev divides
      · exact square ⟨a,s,old,hs,qs,by omega,divides⟩
  · intro h x hx _
    exact h x hx

/-- Exception counts need only be controlled at arrivals if the allowance is
nondecreasing. The statement counts distinct values, including simultaneous arrivals. -/
theorem exceptions_at_entries_iff (Q exceptional : ℕ → Prop) (t : ℕ → ℕ)
    (mono : Monotone t) (start : ℕ) :
  let live := fun x a : ℕ => Q a ∧ x ≤ a ∧ 2*a ≤ 3*x ∧
    ∀ s, 1000 ≤ s → Q s → s*s ≤ x → ¬ s ∣ a
  (∀ x : ℕ, start ≤ x → (x = start ∨ ∃ a, live x a ∧ exceptional a ∧ 3*(x-1) < 2*a) →
    ∀ B : Finset ℕ, (∀ a ∈ B, live x a ∧ exceptional a) → B.card ≤ t x) ↔
  (∀ x : ℕ, start ≤ x → ∀ B : Finset ℕ, (∀ a ∈ B, live x a ∧ exceptional a) → B.card ≤ t x) := by
  intro live
  constructor
  · intro checks x hx
    induction x, hx using Nat.le_induction with
    | base => exact checks _ le_rfl (Or.inl rfl)
    | succ x hx ih =>
      by_cases enters : ∃ a, live (x+1) a ∧ exceptional a ∧ 3*x < 2*a
      · exact checks _ (by omega) (Or.inr (by simpa using enters))
      intro B good
      apply le_trans (ih B ?_) (mono (Nat.le_succ x))
      intro a ha
      obtain ⟨now,e⟩ := good a ha
      obtain ⟨qa,lo,hi,clean⟩ := now
      have upper : 2*a ≤ 3*x := by
        by_contra! late
        exact enters ⟨a,(good a ha).1,e,late⟩
      exact ⟨⟨qa,by omega,upper,fun s hs qs h => clean s hs qs (by omega)⟩,e⟩
  · intro h x hx _
    exact h x hx

/-- After sieving, a proper partition divisor exists exactly when a short
cofactor gives one. Multiple factorizations of the same value cost one exception. -/
theorem short_cofactor_iff (Q : ℕ → Prop) (x a : ℕ) (hi : 2*a ≤ 3*x)
    (clean : ∀ s, 1000 ≤ s → Q s → s*s ≤ x → ¬ s ∣ a) :
    (∃ s, 1000 ≤ s ∧ Q s ∧ 2*s ≤ a ∧ s ∣ a) ↔
      ∃ k : ℕ, 2 ≤ k ∧ 2*k*k < 3*a ∧ k ∣ a ∧ 1000 ≤ a/k ∧ Q (a/k) := by
  constructor
  · rintro ⟨s,hs,qs,low,d⟩
    have large : x < s*s := by
      by_contra! small
      exact clean s hs qs small d
    obtain ⟨k,rfl⟩ := d
    have hk : 2 ≤ k := by
      by_contra! h
      have h' : k = 0 ∨ k = 1 := by omega
      rcases h' with rfl | rfl <;> simp at low <;> omega
    have prod : s*(2*k) < s*(3*s) := by nlinarith
    have short := Nat.lt_of_mul_lt_mul_left prod
    have sq := Nat.mul_lt_mul_of_pos_right short (by omega : 0 < k)
    have div : s*k/k = s := Nat.mul_div_cancel _ (by omega)
    exact ⟨k,hk,by nlinarith only [sq],dvd_mul_left _ _,by rwa [div],by rwa [div]⟩
  · rintro ⟨k,hk,_,dvd,big,qs⟩
    have h := Nat.div_mul_cancel dvd
    exact ⟨a/k,big,qs,by nlinarith [Nat.mul_le_mul_left (a/k) hk],⟨k,h.symm⟩⟩

theorem main : H1 → H2 → OMA.R_oeis_a000009_R10.H1 := by
  intro supply exceptions
  let Q := fun a : ℕ => ∃ m : ℕ, 0 < m ∧ a = strictPartitionCount m
  let exc := fun a : ℕ => ∃ k : ℕ, 2 ≤ k ∧ 2*k*k < 3*a ∧ k ∣ a ∧ 1000 ≤ a/k ∧ Q (a/k)
  let bound := fun x : ℕ => x.log2 / 32
  have hmono : Monotone bound := by
    intro x y h
    apply Nat.div_le_div_right
    by_cases hx : x = 0
    · simp [hx]
    · exact (Nat.le_log2 (by omega : y ≠ 0)).2 ((Nat.log2_self_le hx).trans h)
  have allSupply := (supply_at_events_iff Q bound 30020900773769688559070113208459541809716021698140392739697).mp supply
  have allExceptions := (exceptions_at_entries_iff Q exc bound hmono 30020900773769688559070113208459541809716021698140392739697).mp exceptions
  apply OMA.R_oeis_a000009_R10.H1_of_intervals
  intro n hn
  let x := n/2+1
  have start : 30020900773769688559070113208459541809716021698140392739697 ≤ x := by
    dsimp only [x]; omega
  obtain ⟨A,count,good⟩ := allSupply x start
  classical
  by_contra! missing
  apply (Nat.not_le_of_gt count)
  apply allExceptions x start A
  intro a ha
  obtain ⟨qa,lo,hi,clean⟩ := good a ha
  refine ⟨good a ha,(short_cofactor_iff _ x a hi clean).mp ?_⟩
  exact missing a qa (by omega) (by dsimp only [x] at hi; omega)
    (by dsimp only [x] at lo; omega) (by dsimp only [x] at lo; omega)

end OMA.R_oeis_a000009_R10_H1_R1
