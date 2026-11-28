import OMAStatements.S_oeis_a356995
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases


/-!
The plateau and ramp description of A356988 is due to Peter Bala,
'Notes on A356988', September 27, 2022, https://oeis.org/A356988/a356988.pdf.
We formalize the known base theorem for applications to the open derived
sequence claims A356995 and A356992.
-/

namespace A356988Base

variable (b : ℕ → ℕ)

def Plateau (k : ℕ) : Prop :=
  ∀ j, j ≤ Nat.fib k →
    b (Nat.fib (k+3) + Nat.fib (k+1) + j) = Nat.fib (k+3)

def Ramp (k : ℕ) : Prop :=
  ∀ j, j ≤ Nat.fib (k+2) →
    b (Nat.fib (k+4) + j) = Nat.fib (k+3) + j

variable (rec : ∀ n, 2 ≤ n → b n = n - b (b (n - b (b (b (n-1))))))
include rec

lemma interval_step (u v : ℕ) (hv : 1 ≤ v)
    (r0 : ∀ j, j ≤ u+v → b (2*u+3*v+j) = u+2*v+j)
    (p1 : ∀ j, j ≤ v → b (3*u+4*v+j) = 2*u+3*v)
    (r1 : ∀ j, j ≤ u+2*v → b (3*u+5*v+j) = 2*u+3*v+j) :
    (∀ j, j ≤ u+v → b (4*u+7*v+j) = 3*u+5*v) ∧
    (∀ j, j ≤ 2*u+3*v → b (5*u+8*v+j) = 3*u+5*v+j) := by
  have p2 : ∀ j, j ≤ u+v → b (4*u+7*v+j) = 3*u+5*v := by
    intro j
    induction j with
    | zero =>
      intro _
      have h := r1 (u+2*v) (by omega)
      have ha : 3*u+5*v+(u+2*v) = 4*u+7*v := by omega
      have hb : 2*u+3*v+(u+2*v) = 3*u+5*v := by omega
      simpa only [ha,hb,Nat.add_zero] using h
    | succ j ih =>
      intro hj
      have hj0 : j ≤ u+v := by omega
      have h0 := ih hj0
      have h1 := r1 0 (by omega)
      have h2 := r0 0 (by omega)
      have h3 := r1 (j+1) (by omega)
      have h4 := r0 (j+1) (by omega)
      have hn := rec (4*u+7*v+(j+1)) (by omega)
      have prev : 4*u+7*v+(j+1)-1 = 4*u+7*v+j := by omega
      rw [prev, h0] at hn
      simp only [Nat.add_zero] at h1 h2
      rw [h1, h2] at hn
      have sub : 4*u+7*v+(j+1)-(u+2*v) = 3*u+5*v+(j+1) := by omega
      rw [sub, h3, h4] at hn
      omega
  refine ⟨p2, ?_⟩
  intro j
  induction j with
  | zero =>
    intro _
    have h := p2 (u+v) (by omega)
    have ha : 4*u+7*v+(u+v) = 5*u+8*v := by omega
    simpa only [ha,Nat.add_zero] using h
  | succ j ih =>
    intro hj
    have h0 := ih (by omega : j ≤ 2*u+3*v)
    have hn := rec (5*u+8*v+(j+1)) (by omega)
    have prev : 5*u+8*v+(j+1)-1 = 5*u+8*v+j := by omega
    rw [prev, h0] at hn
    by_cases ha : j < u+v
    · have h1 := r1 j (by omega)
      have h2 := r0 j (by omega)
      rw [h1, h2] at hn
      have sub : 5*u+8*v+(j+1)-(u+2*v+j) = 3*u+5*v+(u+v+1) := by omega
      have h3 := r1 (u+v+1) (by omega)
      have h4 := p1 1 (by omega)
      rw [sub, h3] at hn
      have arg : 2*u+3*v+(u+v+1) = 3*u+4*v+1 := by omega
      rw [arg, h4] at hn
      omega
    · by_cases hb : j < u+2*v
      · have h1 := r1 j (by omega)
        have h2 := p1 (j-(u+v)) (by omega)
        have arg : 2*u+3*v+j = 3*u+4*v+(j-(u+v)) := by omega
        rw [h1, arg, h2] at hn
        have sub : 5*u+8*v+(j+1)-(2*u+3*v) = 3*u+5*v+(j+1) := by omega
        have h3 := r1 (j+1) (by omega)
        have h4 := p1 (j+1-(u+v)) (by omega)
        have arg2 : 2*u+3*v+(j+1) = 3*u+4*v+(j+1-(u+v)) := by omega
        rw [sub, h3, arg2, h4] at hn
        omega
      · have h1 := p2 (j-(u+2*v)) (by omega)
        have arg : 3*u+5*v+j = 4*u+7*v+(j-(u+2*v)) := by omega
        have h2 := r1 0 (by omega)
        simp only [Nat.add_zero] at h2
        rw [arg, h1, h2] at hn
        have sub : 5*u+8*v+(j+1)-(2*u+3*v) = 4*u+7*v+(j+1-(u+2*v)) := by omega
        have h3 := p2 (j+1-(u+2*v)) (by omega)
        rw [sub, h3, h2] at hn
        omega

lemma small (h1 : b 1 = 1) :
    b 2 = 1 ∧ b 3 = 2 ∧ b 4 = 3 ∧ b 5 = 3 ∧ b 6 = 4 ∧ b 7 = 5 := by
  have h2 := rec 2 (by decide)
  norm_num [h1] at h2
  have h3 := rec 3 (by decide)
  norm_num [h1,h2] at h3
  have h4 := rec 4 (by decide)
  norm_num [h1,h2,h3] at h4
  have h5 := rec 5 (by decide)
  norm_num [h1,h2,h3,h4] at h5
  have h6 := rec 6 (by decide)
  norm_num [h1,h2,h3,h4,h5] at h6
  have h7 := rec 7 (by decide)
  norm_num [h1,h2,h3,h4,h5,h6] at h7
  exact ⟨h2,h3,h4,h5,h6,h7⟩

lemma intervals (h1 : b 1 = 1) (k : ℕ) : Plateau b k ∧ Ramp b k := by
  obtain ⟨h2,h3,h4,h5,h6,h7⟩ := small b rec h1
  induction k using Nat.twoStepInduction with
  | zero =>
    constructor
    · intro j hj
      have : j = 0 := Nat.eq_zero_of_le_zero hj
      subst j
      exact h3
    · intro j hj
      change j ≤ 1 at hj
      change b (3+j) = 2+j
      interval_cases j <;> norm_num [h3,h4]
  | one =>
    constructor
    · intro j hj
      change j ≤ 1 at hj
      change b (4+j) = 3
      interval_cases j <;> norm_num [h4,h5]
    · intro j hj
      change j ≤ 2 at hj
      change b (5+j) = 3+j
      interval_cases j <;> norm_num [h5,h6,h7]
  | more k ih0 ih1 =>
    have f2 : Nat.fib (k+2) = Nat.fib k + Nat.fib (k+1) := Nat.fib_add_two
    have f3 : Nat.fib (k+3) = Nat.fib k + 2*Nat.fib (k+1) := by
      rw [show k+3 = (k+1)+2 by omega, Nat.fib_add_two]
      simp only [show k+1+1 = k+2 by omega, f2]
      omega
    have f4 : Nat.fib (k+4) = 2*Nat.fib k + 3*Nat.fib (k+1) := by
      rw [show k+4 = (k+2)+2 by omega, Nat.fib_add_two]
      simp only [show k+2+1 = k+3 by omega, f2, f3]
      omega
    have f5 : Nat.fib (k+5) = 3*Nat.fib k + 5*Nat.fib (k+1) := by
      rw [show k+5 = (k+3)+2 by omega, Nat.fib_add_two]
      simp only [show k+3+1 = k+4 by omega, f3, f4]
      omega
    have f6 : Nat.fib (k+6) = 5*Nat.fib k + 8*Nat.fib (k+1) := by
      rw [show k+6 = (k+4)+2 by omega, Nat.fib_add_two]
      simp only [show k+4+1 = k+5 by omega, f4, f5]
      omega
    have hv : 1 ≤ Nat.fib (k+1) := Nat.fib_pos.mpr (by omega)
    have r0 : ∀ j, j ≤ Nat.fib k+Nat.fib (k+1) →
        b (2*Nat.fib k+3*Nat.fib (k+1)+j) = Nat.fib k+2*Nat.fib (k+1)+j := by
      simpa only [Ramp,f2,f3,f4] using ih0.2
    have p1 : ∀ j, j ≤ Nat.fib (k+1) →
        b (3*Nat.fib k+4*Nat.fib (k+1)+j) = 2*Nat.fib k+3*Nat.fib (k+1) := by
      intro j hj
      have h := ih1.1 j hj
      simp only [Nat.add_assoc, f2, f4] at h
      convert h using 1 <;> congr 1 <;> omega
    have r1 : ∀ j, j ≤ Nat.fib k+2*Nat.fib (k+1) →
        b (3*Nat.fib k+5*Nat.fib (k+1)+j) = 2*Nat.fib k+3*Nat.fib (k+1)+j := by
      simpa only [Ramp,Nat.add_assoc,f3,f4,f5] using ih1.2
    have hs := interval_step b rec _ _ hv r0 p1 r1
    constructor
    · intro j hj
      have hj' : j ≤ Nat.fib k+Nat.fib (k+1) := by simpa only [f2] using hj
      have h := hs.1 j hj'
      simp only [Nat.add_assoc, f3, f5]
      convert h using 1 <;> congr 1 <;> omega
    · simpa only [Ramp,Nat.add_assoc,f4,f5,f6] using hs.2

lemma early_ramp (h1 : b 1 = 1) {k : ℕ} (hk : 1 ≤ k) (j : ℕ)
    (hj : j ≤ Nat.fib k) :
    b (Nat.fib (k+2)+j) = Nat.fib (k+1)+j := by
  cases k with
  | zero => omega
  | succ k =>
    cases k with
    | zero =>
      obtain ⟨h2,h3,_,_,_,_⟩ := small b rec h1
      change j ≤ 1 at hj
      change b (2+j) = 1+j
      interval_cases j <;> norm_num [h2,h3]
    | succ k =>
      have h := (intervals b rec h1 k).2 j
      simpa only [Ramp,Nat.succ_eq_add_one,Nat.add_assoc] using h hj

lemma fib_value (h1 : b 1 = 1) {k : ℕ} (hk : 1 ≤ k) :
    b (Nat.fib (k+2)) = Nat.fib (k+1) := by
  simpa using early_ramp b rec h1 hk 0 (Nat.zero_le _)

end A356988Base


namespace A356995Proof

open OMA.S_oeis_a356995

lemma linear_shapes (b : ℕ → ℕ) (u v : ℕ) (hu : 1 ≤ u) (huv : u ≤ v)
    (r0 : ∀ j, j ≤ u → b (u+v+j) = v+j)
    (p0 : ∀ j, j+u ≤ v → b (2*u+v+j) = u+v)
    (p1 : ∀ j, j ≤ u → b (u+3*v+j) = u+2*v)
    (r1 : ∀ j, j ≤ u+v → b (2*u+3*v+j) = u+2*v+j)
    (p2 : ∀ j, j ≤ v → b (3*u+4*v+j) = 2*u+3*v)
    (r2 : ∀ j, j ≤ u+2*v → b (3*u+5*v+j) = 2*u+3*v+j) :
    (∀ j, j < u → a b (2*u+4*v+1+j) = (j : ℤ)+1) ∧
    (∀ j, j < u → a b (3*u+4*v+j) = (u : ℤ)-j) ∧
    (∀ j, j ≤ 2*v → a b (4*u+4*v+j) = 0) := by
  constructor
  · intro j hj
    have hn := r1 (v+1+j) (by omega)
    have he : 2*u+3*v+(v+1+j) = 2*u+4*v+1+j := by omega
    have he' : u+2*v+(v+1+j) = u+3*v+(1+j) := by omega
    rw [he, he'] at hn
    have hbb := p1 (1+j) (by omega)
    have hs : 2*u+4*v+1+j-(u+3*v+(1+j)) = u+v := by omega
    have hc := r0 0 (by omega)
    simp only [Nat.add_zero] at hc
    rw [a, hn, hbb, hs, hc]
    omega
  constructor
  · intro j hj
    have hn := p2 j (by omega)
    have hbb := r1 0 (by omega)
    simp only [Nat.add_zero] at hbb
    have hs : 3*u+4*v+j-(2*u+3*v) = u+v+j := by omega
    have hc := r0 j (by omega)
    rw [a, hn, hbb, hs, hc]
    omega
  · intro j hj
    by_cases h : u+j ≤ v
    · have hn := p2 (u+j) (by omega)
      have he : 3*u+4*v+(u+j) = 4*u+4*v+j := by omega
      rw [he] at hn
      have hbb := r1 0 (by omega)
      simp only [Nat.add_zero] at hbb
      have hs : 4*u+4*v+j-(2*u+3*v) = 2*u+v+j := by omega
      have hc := p0 j (by omega)
      rw [a, hn, hbb, hs, hc]
      omega
    · let t := u+j-v
      have ht : t ≤ u+v := by dsimp [t]; omega
      have hn := r2 t (by omega)
      have he : 3*u+5*v+t = 4*u+4*v+j := by dsimp [t]; omega
      rw [he] at hn
      have hbb := r1 t ht
      have hs : 4*u+4*v+j-(2*u+3*v+t) = u+2*v := by dsimp [t]; omega
      have hc := p0 (v-u) (by omega)
      have he' : 2*u+v+(v-u) = u+2*v := by omega
      rw [he'] at hc
      rw [a, hn, hbb, hs, hc]
      omega

lemma block_start (k : ℕ) (hk : 1 ≤ k) :
    blockStart k = 2*Nat.fib k + 4*Nat.fib (k+1)+1 := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    have hpos : 1 ≤ Nat.fib k := Nat.fib_pos.mpr (by omega)
    have hs := Finset.sum_Ico_succ_top hk
      (fun i => (2*Nat.fib i-1)+(1+2*Nat.fib (i+1)))
    simp only [blockStart] at ih ⊢
    rw [hs]
    have hf : Nat.fib (k+1+1) = Nat.fib k+Nat.fib (k+1) := by
      simpa only [Nat.add_assoc] using (Nat.fib_add_two (n := k))
    rw [hf]
    omega

lemma shapes_at (b : ℕ → ℕ)
    (rec : ∀ n, 2 ≤ n → b n = n-b (b (n-b (b (b (n-1))))))
    (h1 : b 1 = 1) (k : ℕ) (hk : 1 ≤ k) :
    (∀ j, j < Nat.fib k → a b (2*Nat.fib k+4*Nat.fib (k+1)+1+j) = (j : ℤ)+1) ∧
    (∀ j, j < Nat.fib k → a b (3*Nat.fib k+4*Nat.fib (k+1)+j) = (Nat.fib k : ℤ)-j) ∧
    (∀ j, j ≤ 2*Nat.fib (k+1) → a b (4*Nat.fib k+4*Nat.fib (k+1)+j) = 0) := by
  let u := Nat.fib k
  let v := Nat.fib (k+1)
  have hu : 1 ≤ u := Nat.fib_pos.mpr (by omega)
  have huv : u ≤ v := Nat.fib_mono (by omega)
  have f2 : Nat.fib (k+2) = u+v := Nat.fib_add_two
  have f3 : Nat.fib (k+3) = u+2*v := by
    rw [show k+3 = (k+1)+2 by omega, Nat.fib_add_two]
    simp only [show k+1+1 = k+2 by omega, f2]
    dsimp [v]
    omega
  have f4 : Nat.fib (k+4) = 2*u+3*v := by
    rw [show k+4 = (k+2)+2 by omega, Nat.fib_add_two]
    simp only [show k+2+1 = k+3 by omega, f2, f3]
    omega
  have f5 : Nat.fib (k+5) = 3*u+5*v := by
    rw [show k+5 = (k+3)+2 by omega, Nat.fib_add_two]
    simp only [show k+3+1 = k+4 by omega, f3, f4]
    omega
  have r0 : ∀ j, j ≤ u → b (u+v+j) = v+j := by
    intro j hj
    have h := A356988Base.early_ramp b rec h1 hk j hj
    simpa only [f2] using h
  have p0 : ∀ j, j+u ≤ v → b (2*u+v+j) = u+v := by
    intro j hj
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    have hm : Nat.fib m+u = v := by
      dsimp [u,v]
      simpa only [Nat.succ_eq_add_one,Nat.add_assoc] using
        (Nat.fib_add_two (n := m)).symm
    have h := (A356988Base.intervals b rec h1 m).1 j (by omega)
    change b (Nat.fib (m+3)+Nat.fib (m+1)+j) = Nat.fib (m+3) at h
    have he : Nat.fib (m+3) = u+v := by simpa only [Nat.succ_eq_add_one,Nat.add_assoc] using f2
    have he' : Nat.fib (m+1) = u := rfl
    rw [he,he'] at h
    convert h using 1 <;> congr 1 <;> omega
  have p1 : ∀ j, j ≤ u → b (u+3*v+j) = u+2*v := by
    intro j hj
    have h := (A356988Base.intervals b rec h1 k).1 j hj
    change b (Nat.fib (k+3)+Nat.fib (k+1)+j) = Nat.fib (k+3) at h
    rw [f3] at h
    change b (u+2*v+v+j) = u+2*v at h
    convert h using 1 <;> congr 1 <;> omega
  have r1 : ∀ j, j ≤ u+v → b (2*u+3*v+j) = u+2*v+j := by
    simpa only [A356988Base.Ramp,f2,f3,f4] using (A356988Base.intervals b rec h1 k).2
  have p2 : ∀ j, j ≤ v → b (3*u+4*v+j) = 2*u+3*v := by
    intro j hj
    have h := (A356988Base.intervals b rec h1 (k+1)).1 j hj
    change b (Nat.fib (k+1+3)+Nat.fib (k+1+1)+j) = Nat.fib (k+1+3) at h
    simp only [Nat.add_assoc,f2,f4] at h
    convert h using 1 <;> congr 1 <;> omega
  have r2 : ∀ j, j ≤ u+2*v → b (3*u+5*v+j) = 2*u+3*v+j := by
    simpa only [A356988Base.Ramp,Nat.add_assoc,f3,f4,f5] using (A356988Base.intervals b rec h1 (k+1)).2
  exact linear_shapes b u v hu huv r0 p0 p1 r1 p2 r2

theorem solution : type_of% @OMA.S_oeis_a356995.main := by
  intro b h1 rec k hk
  have hs := shapes_at b rec h1 k hk
  have hb := block_start k hk
  have hu : 1 ≤ Nat.fib k := Nat.fib_pos.mpr (by omega)
  have hz : zeroStart k = 4*Nat.fib k+4*Nat.fib (k+1) := by
    rw [zeroStart,hb]
    omega
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [hb] using hs.1
  · intro j hj
    have he : blockStart k+(Nat.fib k-1)+j = 3*Nat.fib k+4*Nat.fib (k+1)+j := by omega
    rw [he]
    exact hs.2.1 j hj
  · intro j hj
    rw [hz]
    exact hs.2.2 j (by omega)
  · have hn := (shapes_at b rec h1 (k+1) (by omega)).1 0
      (Nat.fib_pos.mpr (by omega))
    have hf : Nat.fib (k+1+1) = Nat.fib k+Nat.fib (k+1) := by
      simpa only [Nat.add_assoc] using (Nat.fib_add_two (n := k))
    rw [hf] at hn
    have he : zeroStart k+(1+2*Nat.fib (k+1)) =
        2*Nat.fib (k+1)+4*(Nat.fib k+Nat.fib (k+1))+1+0 := by omega
    rw [he,hn]
    decide

end A356995Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a356995.main := by
  exact A356995Proof.solution
