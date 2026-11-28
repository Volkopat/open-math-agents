import OMAStatements.S_oeis_a337742
import Mathlib

/-!
# Exact period doubling in the rotating XOR process

On a doubled ring, encode a smaller state (u,v) at positions 2j and 2j+1
as (0,v[j]) and (u[j],u[j]), respectively. Two updates preserve this
encoding and implement one update of the smaller ring. The encoding is
injective. On odd updates the current bit at position zero is off, whereas
the seed has it on. Thus the positive return times double exactly.
-/

namespace A337742Proof

open Function OMA.S_oeis_a337742

/-- Read both cyclic words as periodic words indexed by the integers. -/
private def liftState {n : ℕ} (s : State (ZMod n)) : State ℤ :=
  (fun i => s.1 i, fun i => s.2 i)

private theorem lift_injective (n : ℕ) : Injective (@liftState n) := by
  intro s t h
  apply Prod.ext <;> funext j <;> obtain ⟨i, rfl⟩ := ZMod.intCast_surjective j
  · exact congrArg (fun s : State ℤ => s.1 i) h
  · exact congrArg (fun s : State ℤ => s.2 i) h

private theorem lift_step (n : ℕ) : Semiconj (@liftState n) step step := by
  intro s
  apply Prod.ext
  · rfl
  · funext i
    simp [step, liftState]

private def stretch (s : State ℤ) : State ℤ :=
  (fun i => if i % 2 = 0 then false else s.1 (i/2),
   fun i => if i % 2 = 0 then s.2 (i/2) else s.1 (i/2))

private theorem stretch_even (s : State ℤ) (j : ℤ) :
    (stretch s).1 (2*j) = false ∧ (stretch s).2 (2*j) = s.2 j := by
  simp [stretch]

private theorem stretch_odd (s : State ℤ) (j : ℤ) :
    (stretch s).1 (2*j+1) = s.1 j ∧ (stretch s).2 (2*j+1) = s.1 j := by
  have q : (2*j+1) / 2 = j := by omega
  simp [stretch, q]

private theorem parity_cases (i : ℤ) : (∃ j, i = 2*j) ∨ (∃ j, i = 2*j+1) := by
  by_cases h : i % 2 = 0
  · exact Or.inl ⟨i/2, by omega⟩
  · exact Or.inr ⟨i/2, by omega⟩

private theorem stretch_injective : Injective stretch := by
  intro s t h
  apply Prod.ext <;> funext j
  · simpa only [(stretch_odd _ _).1] using congrArg (fun v : State ℤ => v.1 (2*j+1)) h
  · simpa only [(stretch_even _ _).2] using congrArg (fun v : State ℤ => v.2 (2*j)) h

private theorem half_step_even (s : State ℤ) (j : ℤ) :
    (step (stretch s)).1 (2*j) = s.2 j ∧ (step (stretch s)).2 (2*j) = false := by
  change _ ∧ ((stretch s).1 (2*j-1) ^^ (stretch s).2 (2*j-1)) = false
  rw [show 2*j-1 = 2*(j-1)+1 by ring]
  simp only [(stretch_odd _ _).1, (stretch_odd _ _).2,
    Bool.xor_self, and_true]
  exact (stretch_even s j).2

private theorem half_step_odd (s : State ℤ) (j : ℤ) :
    (step (stretch s)).1 (2*j+1) = s.1 j ∧ (step (stretch s)).2 (2*j+1) = s.2 j := by
  simp only [step, add_sub_cancel_right, (stretch_odd _ _).2, (stretch_even _ _).1,
    (stretch_even _ _).2, Bool.false_xor, and_self]

private theorem two_steps : Semiconj stretch step (step^[2]) := by
  intro s
  change stretch (step s) = step (step (stretch s))
  apply Prod.ext <;> funext i <;> rcases parity_cases i with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · exact (stretch_even _ _).1.trans (half_step_even _ _).2.symm
  · exact (stretch_odd _ _).1.trans (half_step_odd _ _).2.symm
  · change (stretch (step s)).2 (2*j) =
      ((step (stretch s)).1 (2*j-1) ^^ (step (stretch s)).2 (2*j-1))
    rw [show 2*j-1 = 2*(j-1)+1 by ring, (stretch_even _ _).2,
      (half_step_odd _ _).1, (half_step_odd _ _).2]
    rfl
  · change (stretch (step s)).2 (2*j+1) =
      ((step (stretch s)).1 (2*j+1-1) ^^ (step (stretch s)).2 (2*j+1-1))
    rw [add_sub_cancel_right, (stretch_odd _ _).2, (half_step_even _ _).1,
      (half_step_even _ _).2, Bool.xor_false]
    rfl

private theorem seed_double (n : ℕ) :
    liftState (seed (2*n)) = stretch (liftState (seed n)) := by
  apply Prod.ext <;> funext i <;> rcases parity_cases i with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · exact (stretch_even _ _).1.symm
  · exact (stretch_odd (liftState (seed n)) j).1.symm
  · rw [(stretch_even _ _).2]
    simp only [liftState, seed, ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_mul, Nat.cast_ofNat,
      Int.mul_dvd_mul_iff_left (by decide : (2 : ℤ) ≠ 0)]
  · rw [(stretch_odd _ _).2]
    have h : ¬ (2*(n:ℤ)) ∣ 2*j+1 := by
      intro hd
      have : (2 : ℤ) ∣ 2*j+1 := dvd_trans (dvd_mul_right _ _) hd
      omega
    simp [liftState, seed, ZMod.intCast_zmod_eq_zero_iff_dvd, h]

private theorem even_state (n t : ℕ) :
    liftState (step^[2*t] (seed (2*n))) = stretch (liftState (step^[t] (seed n))) := by
  rw [(lift_step _).iterate_right (2*t) _, seed_double, Function.iterate_mul,
    ← two_steps.iterate_right t _, ← (lift_step n).iterate_right t _]

private theorem even_return (n t : ℕ) :
    IsPeriodicPt step (2*t) (seed (2*n)) ↔ IsPeriodicPt step t (seed n) := by
  change step^[2*t] (seed (2*n)) = seed (2*n) ↔ step^[t] (seed n) = seed n
  rw [← (lift_injective (2*n)).eq_iff, even_state, seed_double, stretch_injective.eq_iff,
    (lift_injective n).eq_iff]

private theorem odd_no_return (n t : ℕ) : ¬ IsPeriodicPt step (2*t+1) (seed (2*n)) := by
  intro h
  change step^[2*t+1] (seed (2*n)) = seed (2*n) at h
  have hh := congrArg (@liftState (2*n)) h
  rw [Function.iterate_succ_apply', lift_step _ _, even_state] at hh
  have bit := congrArg (fun s : State ℤ => s.2 (2*0)) hh
  change (step (stretch _)).2 (2*0) = _ at bit
  rw [(half_step_even _ _).2] at bit
  simp [liftState, seed] at bit

private theorem step_injective (n : ℕ) : Injective (step (ι := ZMod n)) := by
  intro s t h
  have curr : s.2 = t.2 := congrArg Prod.fst h
  apply Prod.ext _ curr
  funext i
  have bit := congrArg (fun st : State (ZMod n) => st.2 (i+1)) h
  simp only [step, add_sub_cancel_right, curr] at bit
  cases hbit : t.2 i <;> simpa [hbit] using bit

private theorem positive (n : ℕ) (hn : 0 < n) : 0 < period n := by
  have : NeZero n := ⟨hn.ne'⟩
  exact minimalPeriod_pos_of_mem_periodicPts ((step_injective n).mem_periodicPts _)

private theorem doubling (n : ℕ) : period (2*n) = 2 * period n := by
  apply Nat.dvd_antisymm
  · exact ((even_return n _).mpr (isPeriodicPt_minimalPeriod step _)).minimalPeriod_dvd
  · have ret : IsPeriodicPt step (period (2*n)) (seed (2*n)) := isPeriodicPt_minimalPeriod step _
    let t := period (2*n) / 2
    have e : period (2*n) = 2*t := by
      by_contra hn
      have o : period (2*n) = 2*t+1 := by dsimp [t] at *; omega
      exact odd_no_return n t (o ▸ ret)
    have small := (even_return n t).mp (e ▸ ret)
    rw [e]
    exact Nat.mul_dvd_mul_left 2 small.minimalPeriod_dvd

end A337742Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a337742.main := by
  intro n hn
  exact ⟨A337742Proof.positive n hn, A337742Proof.doubling n⟩
