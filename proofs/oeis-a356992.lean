import OMAStatements.S_oeis_a356992
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

/-!
Proof of all five registered A356992 plateau assertions.
Credit: @CubeJerry, assisted by Codex (GPT-6.2 Astra).

The underlying A356988 interval description is Peter Bala's 2022 result;
its proof from the defining recurrence is reproduced below. The sixfold
complement composition is evaluated in seven linear cases. These formulas
then identify every maximal plateau of both a(n) and n-a(n), including the
exceptional initial plateau and the excluded initial run of ones.
-/


/-!
The plateau and ramp description of A356988 is due to Peter Bala,
Notes on A356988, September 27, 2022, https://oeis.org/A356988/a356988.pdf.
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

namespace A356992Proof

open OMA.S_oeis_a356992

lemma six_of_chain (b : ℕ → ℕ) (n x1 x2 x3 x4 x5 x6 : ℕ)
    (h1 : n - b n = x1) (h2 : n - b x1 = x2)
    (h3 : n - b x2 = x3) (h4 : n - b x3 = x4)
    (h5 : n - b x4 = x5) (h6 : n - b x5 = x6) : a b n = x6 := by
  dsimp [a]
  rw [h1, h2, h3, h4, h5, h6]

variable (b : ℕ → ℕ) (u v : ℕ) (hu : 0 ≤ u) (huv : u ≤ v)
  (rm : ∀ x, u+2*v ≤ x → x ≤ u+3*v → b x = x-v)
  (p0 : ∀ x, u+3*v ≤ x → x ≤ 2*u+3*v → b x = u+2*v)
  (r0 : ∀ x, 2*u+3*v ≤ x → x ≤ 3*u+4*v → b x = x-u-v)
  (p1 : ∀ x, 3*u+4*v ≤ x → x ≤ 3*u+5*v → b x = 2*u+3*v)
  (r1 : ∀ x, 3*u+5*v ≤ x → x ≤ 4*u+7*v → b x = x-u-2*v)
  (p2 : ∀ x, 4*u+7*v ≤ x → x ≤ 5*u+8*v → b x = 3*u+5*v)
  (r2 : ∀ x, 5*u+8*v ≤ x → x ≤ 7*u+11*v → b x = x-2*u-3*v)

include hu huv rm p0 r0 p1 r1 p2 r2

lemma composition_plateau (n : ℕ) (hn : 4*u+6*v ≤ n) (hn' : n ≤ 5*u+7*v) :
    a b n = 3*u+4*v := by
  by_cases hcut : n ≤ 4*u+7*v
  · have hb1 := r1 n (by omega) hcut
    have hb2 := rm (u+2*v) (by omega) (by omega)
    have hb3 := r1 (n-u-v) (by omega) (by omega)
    have hb4 := p0 (2*u+3*v) (by omega) (by omega)
    have hb5 := p1 (n-u-2*v) (by omega) (by omega)
    have hb6 := r0 (n-2*u-3*v) (by omega) (by omega)
    apply six_of_chain b n (u+2*v) (n-u-v) (2*u+3*v) (n-u-2*v) (n-2*u-3*v)
    all_goals omega
  · have hb1 := p2 n (by omega) (by omega)
    have hb2 := rm (n-3*u-5*v) (by omega) (by omega)
    have hb3 := r1 (3*u+6*v) (by omega) (by omega)
    have hb4 := r0 (n-2*u-4*v) (by omega) (by omega)
    have hb5 := p1 (3*u+5*v) (by omega) (by omega)
    have hb6 := r0 (n-2*u-3*v) (by omega) (by omega)
    apply six_of_chain b n (n-3*u-5*v) (3*u+6*v) (n-2*u-4*v) (3*u+5*v) (n-2*u-3*v)
    all_goals omega

lemma composition_ramp (n : ℕ) (hn : 5*u+7*v ≤ n) (hn' : n ≤ 6*u+10*v) :
    a b n = n-2*u-3*v := by
  by_cases ha : n ≤ 4*u+8*v
  · have hb1 := p2 n (by omega) (by omega)
    have hb2 := rm (n-3*u-5*v) (by omega) (by omega)
    have hb3 := r1 (3*u+6*v) (by omega) (by omega)
    have hb4 := r0 (n-2*u-4*v) (by omega) (by omega)
    have hb5 := p1 (3*u+5*v) (by omega) (by omega)
    have hb6 := p1 (n-2*u-3*v) (by omega) (by omega)
    apply six_of_chain b n (n-3*u-5*v) (3*u+6*v) (n-2*u-4*v) (3*u+5*v) (n-2*u-3*v)
    all_goals omega
  · by_cases hb : n ≤ 5*u+8*v
    · have hb1 := p2 n (by omega) (by omega)
      have hb2 := p0 (n-3*u-5*v) (by omega) (by omega)
      have hb3 := r1 (n-u-2*v) (by omega) (by omega)
      have hb4 := r0 (2*u+4*v) (by omega) (by omega)
      have hb5 := r1 (n-u-3*v) (by omega) (by omega)
      have hb6 := p1 (2*u+5*v) (by omega) (by omega)
      apply six_of_chain b n (n-3*u-5*v) (n-u-2*v) (2*u+4*v) (n-u-3*v) (2*u+5*v)
      all_goals omega
    · by_cases hc : n ≤ 5*u+9*v
      · have hb1 := r2 n (by omega) (by omega)
        have hb2 := p0 (2*u+3*v) (by omega) (by omega)
        have hb3 := r1 (n-u-2*v) (by omega) (by omega)
        have hb4 := r0 (2*u+4*v) (by omega) (by omega)
        have hb5 := r1 (n-u-3*v) (by omega) (by omega)
        have hb6 := p1 (2*u+5*v) (by omega) (by omega)
        apply six_of_chain b n (2*u+3*v) (n-u-2*v) (2*u+4*v) (n-u-3*v) (2*u+5*v)
        all_goals omega
      · by_cases hd : n ≤ 6*u+9*v
        · have hb1 := r2 n (by omega) (by omega)
          have hb2 := p0 (2*u+3*v) (by omega) (by omega)
          have hb3 := p2 (n-u-2*v) (by omega) (by omega)
          have hb4 := r0 (n-3*u-5*v) (by omega) (by omega)
          have hb5 := r1 (4*u+6*v) (by omega) (by omega)
          have hb6 := p1 (n-3*u-4*v) (by omega) (by omega)
          apply six_of_chain b n (2*u+3*v) (n-u-2*v) (n-3*u-5*v) (4*u+6*v) (n-3*u-4*v)
          all_goals omega
        · have hb1 := r2 n (by omega) (by omega)
          have hb2 := p0 (2*u+3*v) (by omega) (by omega)
          have hb3 := p2 (n-u-2*v) (by omega) (by omega)
          have hb4 := p1 (n-3*u-5*v) (by omega) (by omega)
          have hb5 := r1 (n-2*u-3*v) (by omega) (by omega)
          have hb6 := p1 (3*u+5*v) (by omega) (by omega)
          apply six_of_chain b n (2*u+3*v) (n-u-2*v) (n-3*u-5*v) (n-2*u-3*v) (3*u+5*v)
          all_goals omega

end A356992Proof

namespace A356992Proof

open OMA.S_oeis_a356992

def S (k : ℕ) : ℕ := if k = 0 then 5 else 2 * Nat.fib (k+4)
def D (k : ℕ) : ℕ := Nat.fib (k+4)
def H (k : ℕ) : ℕ := Nat.fib (k+2) + Nat.fib (k+4)
def E (k : ℕ) : ℕ := H k + D k

lemma lucas_eq_fib (k : ℕ) : lucas (k+1) = Nat.fib k + Nat.fib (k+2) := by
  induction k using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more k h0 h1 =>
    rw [show k+2+1 = (k+1)+2 by omega, lucas]
    rw [h0, h1]
    simp only [show k+2+2 = (k+2)+2 by omega, Nat.fib_add_two]
    omega

lemma H_eq_lucas (k : ℕ) : H k = lucas (k+3) := by
  simpa only [H, Nat.add_assoc] using (lucas_eq_fib (k+2)).symm

lemma E_eq_a013655 (k : ℕ) : E k = a013655 (k+3) := by
  simp only [a013655, E, D, H_eq_lucas, Nat.add_assoc]
  norm_num only
  omega

lemma S_zero : S 0 = 5 := by decide
lemma E_zero : E 0 = 7 := by decide
lemma H_zero : H 0 = 4 := by decide
lemma D_zero : D 0 = 3 := by decide

lemma S_succ (k : ℕ) : S (k+1) = H (k+1) + D k := by
  have hf : Nat.fib (k+5) = Nat.fib (k+3) + Nat.fib (k+4) := by
    simpa only [Nat.add_assoc] using (Nat.fib_add_two (n := k+3))
  simp only [S, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte, H, D,
    Nat.add_assoc]
  norm_num only at *
  omega

lemma H_strict (k : ℕ) : H k < H (k+1) := by
  have h0 := Nat.fib_le_fib_succ (n := k+2)
  have h1 := Nat.fib_lt_fib_succ (show 2 ≤ k+4 by omega)
  simp only [H, Nat.add_assoc]
  norm_num only [Nat.add_assoc] at *
  omega

lemma S_lt_E (k : ℕ) : S k < E k := by
  have hf : Nat.fib (k+2) > 0 := Nat.fib_pos.mpr (by omega)
  by_cases hk : k = 0
  · subst k; decide
  · simp only [S, hk, ↓reduceIte, E, H, D]
    omega

lemma E_lt_S_succ (k : ℕ) : E k < S (k+1) := by
  rw [S_succ, E]
  have := H_strict k
  omega

lemma S_strict (k : ℕ) : S k < S (k+1) := (S_lt_E k).trans (E_lt_S_succ k)

lemma S_mono : Monotone S := monotone_nat_of_le_succ (fun k => (S_strict k).le)

lemma S_ge_five (k : ℕ) : 5 ≤ S k := by
  have := S_mono (Nat.zero_le k)
  simpa only [S_zero] using this

lemma H_le_S (k : ℕ) : H k ≤ S k := by
  have hf := Nat.fib_mono (show k+2 ≤ k+4 by omega)
  by_cases hk : k=0
  · subst k; decide
  · simp only [H, S, hk, ↓reduceIte]
    omega

lemma exists_region (n : ℕ) (hn : 5 ≤ n) : ∃ k, S k ≤ n ∧ n < S (k+1) := by
  have he : ∃ k, n < S k := by
    refine ⟨n+1, ?_⟩
    have hf := Nat.le_fib_add_one (n+1+4)
    simp only [S, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte]
    omega
  let t := Nat.find he
  have ht : n < S t := Nat.find_spec he
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, S_zero] at ht
    omega
  refine ⟨t-1, ?_, ?_⟩
  · have hmin := Nat.find_min he (show t-1 < t by omega)
    omega
  · have h : t-1+1=t := by omega
    simpa only [h] using ht

def complement (f : ℕ → ℕ) (n : ℕ) : ℕ := n-f n

section Shape

variable (f : ℕ → ℕ)
  (small : ∀ n, 2 ≤ n → n ≤ 5 → f n = n-1)
  (plateau : ∀ k n, S k ≤ n → n ≤ E k → f n = H k)
  (ramp : ∀ k n, E k ≤ n → n ≤ S (k+1) → f n = n-D k)

include small plateau ramp

lemma f_le (n : ℕ) (hn : 2 ≤ n) : f n ≤ n := by
  by_cases hsmall : n ≤ 5
  · rw [small n hn hsmall]; omega
  · obtain ⟨k,hk,hk'⟩ := exists_region n (by omega)
    by_cases he : n ≤ E k
    · rw [plateau k n hk he]
      exact (H_le_S k).trans hk
    · rw [ramp k n (by omega) (by omega)]
      omega

lemma f_slow (n : ℕ) (hn : 2 ≤ n) : f (n+1) = f n ∨ f (n+1) = f n + 1 := by
  by_cases hs : n < 5
  · right
    rw [small n hn (by omega), small (n+1) (by omega) (by omega)]
    omega
  · obtain ⟨k,hk,hk'⟩ := exists_region n (by omega)
    by_cases he : n < E k
    · left
      rw [plateau k n hk (by omega), plateau k (n+1) (by omega) (by omega)]
    · right
      have hE : D k ≤ E k := by dsimp [E]; omega
      rw [ramp k n (by omega) (by omega), ramp k (n+1) (by omega) (by omega)]
      omega

lemma f_mono {x y : ℕ} (hx : 2 ≤ x) (hxy : x ≤ y) : f x ≤ f y := by
  induction y, hxy using Nat.le_induction with
  | base => exact le_rfl
  | succ y hxy ih =>
    have hs := f_slow f small plateau ramp y (by omega)
    omega

lemma f_before (k : ℕ) : f (S k-1)+1 = H k := by
  cases k with
  | zero =>
    rw [S_zero, H_zero]
    change f 4+1=4
    have := small 4 (by omega) (by omega)
    omega
  | succ k =>
    have he := E_lt_S_succ k
    have hb : E k ≤ S (k+1)-1 := by omega
    have hv := ramp k (S (k+1)-1) hb (by omega)
    have hS := S_succ k
    have hpos : 0 < H (k+1) := by
      have := H_strict k
      omega
    simpa only [Nat.succ_eq_add_one] using (show f (S (k+1)-1)+1 = H (k+1) by omega)

lemma f_after (k : ℕ) : f (E k+1) = H k+1 := by
  have he := E_lt_S_succ k
  have hv := ramp k (E k+1) (by omega) (by omega)
  have hE : E k=H k+D k := rfl
  omega

lemma plateau_of_k (k : ℕ) : IsPlateau f 2 (S k) (E k) := by
  have hS := S_ge_five k
  have hSE := S_lt_E k
  have hval := plateau k (S k) le_rfl hSE.le
  refine ⟨by omega, hSE, ?_, ?_, ?_⟩
  · intro i hi hi'
    rw [plateau k i hi hi', hval]
  · intro _
    have hb := f_before f small plateau ramp k
    omega
  · have ha := f_after f small plateau ramp k
    omega

lemma plateau_classification {s e : ℕ} (hp : IsPlateau f 2 s e) :
    ∃ k, s=S k ∧ e=E k := by
  obtain ⟨hs,hse,hconst,hleft,hright⟩ := hp
  have hnext := hconst (s+1) (by omega) (by omega)
  have hs5 : 5 ≤ s := by
    by_contra h
    have h0 := small s hs (by omega)
    have h1 := small (s+1) (by omega) (by omega)
    omega
  obtain ⟨k,hk,hk'⟩ := exists_region s hs5
  have he : s < E k := by
    by_contra h
    have h0 := ramp k s (by omega) hk'.le
    have h1 := ramp k (s+1) (by omega) (by omega)
    have hD : D k ≤ E k := by dsimp [E]; omega
    omega
  have hval := plateau k s hk he.le
  have hsEq : s=S k := by
    by_contra h
    have hprev := plateau k (s-1) (by omega) (by omega)
    have hleft' := hleft (by omega)
    omega
  have heEq : e=E k := by
    by_cases hlt : e < E k
    · have h1 := plateau k (e+1) (by omega) (by omega)
      omega
    · by_contra h
      have h1 := f_after f small plateau ramp k
      have h2 := f_mono f small plateau ramp (show 2 ≤ E k+1 by omega) (show E k+1 ≤ e by omega)
      have h3 := hconst e (by omega) le_rfl
      omega
  exact ⟨k,hsEq,heEq⟩


lemma complement_on_plateau (k n : ℕ) (hn : S k ≤ n) (hn' : n ≤ E k) :
    complement f n = n-H k := by
  simp only [complement, plateau k n hn hn']

lemma complement_on_ramp (k n : ℕ) (hn : E k ≤ n) (hn' : n ≤ S (k+1)) :
    complement f n = D k := by
  have hD : D k ≤ E k := by dsimp [E]; omega
  simp only [complement, ramp k n hn hn']
  omega

lemma complement_slow (n : ℕ) (hn : 2 ≤ n) :
    complement f (n+1) = complement f n ∨ complement f (n+1) = complement f n+1 := by
  have h0 := f_le f small plateau ramp n hn
  have h1 := f_slow f small plateau ramp n hn
  dsimp [complement]
  omega

lemma complement_mono {x y : ℕ} (hx : 2 ≤ x) (hxy : x ≤ y) :
    complement f x ≤ complement f y := by
  induction y, hxy using Nat.le_induction with
  | base => exact le_rfl
  | succ y hxy ih =>
    have hs := complement_slow f small plateau ramp y (by omega)
    omega

lemma complement_before (k : ℕ) : complement f (E k-1)+1 = D k := by
  have hSE := S_lt_E k
  have hval := complement_on_plateau f small plateau ramp k (E k-1) (by omega) (by omega)
  have hD : 0 < D k := Nat.fib_pos.mpr (by omega)
  have hE : E k=H k+D k := rfl
  omega

lemma complement_after (k : ℕ) : complement f (S (k+1)+1) = D k+1 := by
  have hSE := S_lt_E (k+1)
  have hval := complement_on_plateau f small plateau ramp (k+1) (S (k+1)+1) (by omega) (by omega)
  have hS := S_succ k
  omega

lemma complement_plateau_of_k (k : ℕ) :
    IsPlateau (complement f) 2 (E k) (S (k+1)) := by
  have hS := S_ge_five k
  have hSE := S_lt_E k
  have hES := E_lt_S_succ k
  have hval := complement_on_ramp f small plateau ramp k (E k) le_rfl hES.le
  refine ⟨by omega, hES, ?_, ?_, ?_⟩
  · intro i hi hi'
    rw [complement_on_ramp f small plateau ramp k i hi hi', hval]
  · intro _
    have hb := complement_before f small plateau ramp k
    omega
  · have ha := complement_after f small plateau ramp k
    omega

lemma complement_plateau_classification {s e : ℕ} (hs2 : 2 < s)
    (hp : IsPlateau (complement f) 2 s e) : ∃ k, s=E k ∧ e=S (k+1) := by
  obtain ⟨hs,hse,hconst,hleft,hright⟩ := hp
  have hnext := hconst (s+1) (by omega) (by omega)
  have hs5 : 5 < s := by
    by_contra h
    have h0 := small s hs (by omega)
    have h1 := small (s-1) (by omega) (by omega)
    have hh := hleft hs2
    dsimp [complement] at hh
    omega
  obtain ⟨k,hk,hk'⟩ := exists_region s (by omega)
  have he : E k ≤ s := by
    by_contra h
    have h0 := complement_on_plateau f small plateau ramp k s hk (by omega)
    have h1 := complement_on_plateau f small plateau ramp k (s+1) (by omega) (by omega)
    have hHS := H_le_S k
    omega
  have hval := complement_on_ramp f small plateau ramp k s he hk'.le
  have hsEq : s=E k := by
    by_contra h
    have hprev := complement_on_ramp f small plateau ramp k (s-1) (by omega) (by omega)
    have hleft' := hleft hs2
    omega
  have heEq : e=S (k+1) := by
    by_cases hlt : e < S (k+1)
    · have h1 := complement_on_ramp f small plateau ramp k (e+1) (by omega) (by omega)
      omega
    · by_contra h
      have h1 := complement_after f small plateau ramp k
      have h2 := complement_mono f small plateau ramp
        (show 2 ≤ S (k+1)+1 by have := S_ge_five (k+1); omega)
        (show S (k+1)+1 ≤ e by omega)
      have h3 := hconst e (by omega) le_rfl
      omega
  exact ⟨k,hsEq,heEq⟩

lemma consequences :
    (∀ n, 2 ≤ n → f (n+1) = f n ∨ f (n+1) = f n+1) ∧
    {h | ∃ s e, IsPlateau f 2 s e ∧ f s = h} = {h | ∃ k, 3 ≤ k ∧ h=lucas k} ∧
    {e | ∃ s, IsPlateau f 2 s e} = {e | ∃ k, 3 ≤ k ∧ e=a013655 k} ∧
    {s | ∃ e, IsPlateau f 2 s e} = {s | s=5 ∨ ∃ k, 5 ≤ k ∧ s=2*Nat.fib k} ∧
    {h | ∃ s e, 2<s ∧ IsPlateau (fun n => n-f n) 2 s e ∧ s-f s=h} =
      {h | ∃ k, 4 ≤ k ∧ h=Nat.fib k} := by
  refine ⟨f_slow f small plateau ramp, ?_, ?_, ?_, ?_⟩
  · ext h
    constructor
    · rintro ⟨s,e,hp,hv⟩
      obtain ⟨k,rfl,rfl⟩ := plateau_classification f small plateau ramp hp
      have hf := plateau k (S k) le_rfl (S_lt_E k).le
      exact ⟨k+3,by omega, by rw [← hv,hf,H_eq_lucas]⟩
    · rintro ⟨k,hk,rfl⟩
      have heq : k-3+3=k := by omega
      refine ⟨S (k-3),E (k-3),plateau_of_k f small plateau ramp (k-3),?_⟩
      rw [plateau (k-3) (S (k-3)) le_rfl (S_lt_E (k-3)).le, H_eq_lucas, heq]
  · ext e
    constructor
    · rintro ⟨s,hp⟩
      obtain ⟨k,rfl,rfl⟩ := plateau_classification f small plateau ramp hp
      exact ⟨k+3,by omega,E_eq_a013655 k⟩
    · rintro ⟨k,hk,rfl⟩
      have heq : k-3+3=k := by omega
      have hE : E (k-3)=a013655 k := by rw [E_eq_a013655,heq]
      exact ⟨S (k-3),hE ▸ plateau_of_k f small plateau ramp (k-3)⟩
  · ext s
    constructor
    · rintro ⟨e,hp⟩
      obtain ⟨k,rfl,rfl⟩ := plateau_classification f small plateau ramp hp
      by_cases hk : k=0
      · left; subst k; exact S_zero
      · exact Or.inr ⟨k+4,by omega,by simp only [S,hk,↓reduceIte]⟩
    · rintro (rfl | ⟨k,hk,rfl⟩)
      · exact ⟨E 0,S_zero ▸ plateau_of_k f small plateau ramp 0⟩
      · have hS : S (k-4)=2*Nat.fib k := by
          simp only [S,show k-4 ≠ 0 by omega,↓reduceIte,show k-4+4=k by omega]
        exact ⟨E (k-4),hS ▸ plateau_of_k f small plateau ramp (k-4)⟩
  · ext h
    constructor
    · rintro ⟨s,e,hs,hp,hv⟩
      obtain ⟨k,rfl,rfl⟩ := complement_plateau_classification f small plateau ramp hs hp
      have hf := complement_on_ramp f small plateau ramp k (E k) le_rfl (E_lt_S_succ k).le
      exact ⟨k+4,by omega,by simpa only [complement,D,hv] using hf⟩
    · rintro ⟨k,hk,rfl⟩
      have hE := S_lt_E (k-4)
      have hS := S_ge_five (k-4)
      refine ⟨E (k-4),S (k-4+1),by omega,
        complement_plateau_of_k f small plateau ramp (k-4),?_⟩
      have hf := complement_on_ramp f small plateau ramp (k-4) (E (k-4)) le_rfl (E_lt_S_succ (k-4)).le
      simpa only [complement,D,show k-4+4=k by omega] using hf

end Shape
end A356992Proof

namespace A356992Proof

open OMA.S_oeis_a356992

variable (b : ℕ → ℕ)
  (rec : ∀ n, 2 ≤ n → b n = n - b (b (n - b (b (b (n-1))))))
  (h1 : b 1 = 1)

include rec h1

lemma linear_shapes (k : ℕ) :
    (∀ n, 4*Nat.fib k+6*Nat.fib (k+1) ≤ n → n ≤ 5*Nat.fib k+7*Nat.fib (k+1) →
      a b n = 3*Nat.fib k+4*Nat.fib (k+1)) ∧
    (∀ n, 5*Nat.fib k+7*Nat.fib (k+1) ≤ n → n ≤ 6*Nat.fib k+10*Nat.fib (k+1) →
      a b n = n-2*Nat.fib k-3*Nat.fib (k+1)) := by
  let u := Nat.fib k
  let v := Nat.fib (k+1)
  have f2 : Nat.fib (k+2) = u+v := Nat.fib_add_two
  have f3 : Nat.fib (k+3) = u+2*v := by
    rw [show k+3=(k+1)+2 by omega,Nat.fib_add_two]
    simp only [show k+1+1=k+2 by omega,f2]
    dsimp [v]
    omega
  have f4 : Nat.fib (k+4) = 2*u+3*v := by
    rw [show k+4=(k+2)+2 by omega,Nat.fib_add_two]
    simp only [show k+2+1=k+3 by omega,f2,f3]
    omega
  have f5 : Nat.fib (k+5) = 3*u+5*v := by
    rw [show k+5=(k+3)+2 by omega,Nat.fib_add_two]
    simp only [show k+3+1=k+4 by omega,f3,f4]
    omega
  have f6 : Nat.fib (k+6) = 5*u+8*v := by
    rw [show k+6=(k+4)+2 by omega,Nat.fib_add_two]
    simp only [show k+4+1=k+5 by omega,f4,f5]
    omega
  have huv : u ≤ v := Nat.fib_le_fib_succ
  have rm : ∀ x, u+2*v ≤ x → x ≤ u+3*v → b x = x-v := by
    intro x hx hx'
    have h := A356988Base.early_ramp b rec h1 (show 1 ≤ k+1 by omega)
      (x-(u+2*v)) (by change x-(u+2*v) ≤ v; omega)
    simp only [Nat.add_assoc,f2,f3] at h
    have hi : u+2*v+(x-(u+2*v))=x := by omega
    simp only [Nat.add_assoc] at h hi
    rw [hi] at h
    omega
  have p0 : ∀ x, u+3*v ≤ x → x ≤ 2*u+3*v → b x = u+2*v := by
    intro x hx hx'
    have h := (A356988Base.intervals b rec h1 k).1
      (x-(u+3*v)) (by change x-(u+3*v) ≤ u; omega)
    simp only [f3] at h
    change b (u+2*v+v+(x-(u+3*v)))=u+2*v at h
    have hi : u+2*v+v+(x-(u+3*v))=x := by omega
    simp only [Nat.add_assoc] at h hi
    simpa only [hi] using h
  have r0 : ∀ x, 2*u+3*v ≤ x → x ≤ 3*u+4*v → b x = x-u-v := by
    intro x hx hx'
    have h := (A356988Base.intervals b rec h1 k).2
      (x-(2*u+3*v)) (by rw [f2]; omega)
    simp only [f3,f4] at h
    have hi : 2*u+3*v+(x-(2*u+3*v))=x := by omega
    simp only [Nat.add_assoc] at h hi
    rw [hi] at h
    omega
  have p1 : ∀ x, 3*u+4*v ≤ x → x ≤ 3*u+5*v → b x = 2*u+3*v := by
    intro x hx hx'
    have h := (A356988Base.intervals b rec h1 (k+1)).1
      (x-(3*u+4*v)) (by change x-(3*u+4*v) ≤ v; omega)
    simp only [Nat.add_assoc,f2,f4] at h
    have hi : 2*u+3*v+(u+v)+(x-(3*u+4*v))=x := by omega
    simp only [Nat.add_assoc] at h hi
    simpa only [hi] using h
  have r1 : ∀ x, 3*u+5*v ≤ x → x ≤ 4*u+7*v → b x = x-u-2*v := by
    intro x hx hx'
    have h := (A356988Base.intervals b rec h1 (k+1)).2
      (x-(3*u+5*v)) (by simp only [Nat.add_assoc,f3]; omega)
    simp only [Nat.add_assoc,f4,f5] at h
    have hi : 3*u+5*v+(x-(3*u+5*v))=x := by omega
    simp only [Nat.add_assoc] at h hi
    rw [hi] at h
    omega
  have p2 : ∀ x, 4*u+7*v ≤ x → x ≤ 5*u+8*v → b x = 3*u+5*v := by
    intro x hx hx'
    have h := (A356988Base.intervals b rec h1 (k+2)).1
      (x-(4*u+7*v)) (by rw [f2]; omega)
    simp only [Nat.add_assoc,f3,f5] at h
    have hi : 3*u+5*v+(u+2*v)+(x-(4*u+7*v))=x := by omega
    simp only [Nat.add_assoc] at h hi
    simpa only [hi] using h
  have r2 : ∀ x, 5*u+8*v ≤ x → x ≤ 7*u+11*v → b x = x-2*u-3*v := by
    intro x hx hx'
    have h := (A356988Base.intervals b rec h1 (k+2)).2
      (x-(5*u+8*v)) (by simp only [Nat.add_assoc,f4]; omega)
    simp only [Nat.add_assoc,f5,f6] at h
    have hi : 5*u+8*v+(x-(5*u+8*v))=x := by omega
    simp only [Nat.add_assoc] at h hi
    rw [hi] at h
    omega
  exact ⟨composition_plateau b u v (Nat.zero_le _) huv rm p0 r0 p1 r1 p2 r2,
    composition_ramp b u v (Nat.zero_le _) huv rm p0 r0 p1 r1 p2 r2⟩

lemma a_small (n : ℕ) (hn : 2 ≤ n) (hn' : n ≤ 5) : a b n = n-1 := by
  obtain ⟨h2,h3,h4,h5,h6,h7⟩ := A356988Base.small b rec h1
  interval_cases n <;> norm_num [a,h1,h2,h3,h4,h5]

lemma sequence_shapes :
    (∀ k n, S k ≤ n → n ≤ E k → a b n = H k) ∧
    (∀ k n, E k ≤ n → n ≤ S (k+1) → a b n = n-D k) := by
  have hshape : ∀ k,
      (∀ n, 2*Nat.fib (k+4) ≤ n → n ≤ E k → a b n=H k) ∧
      (∀ n, E k ≤ n → n ≤ S (k+1) → a b n=n-D k) := by
    intro k
    have hlin := linear_shapes b rec h1 k
    have f2 : Nat.fib (k+2)=Nat.fib k+Nat.fib (k+1) := Nat.fib_add_two
    have f3 : Nat.fib (k+3)=Nat.fib k+2*Nat.fib (k+1) := by
      rw [show k+3=(k+1)+2 by omega,Nat.fib_add_two]
      simp only [show k+1+1=k+2 by omega,f2]
      omega
    have f4 : Nat.fib (k+4)=2*Nat.fib k+3*Nat.fib (k+1) := by
      rw [show k+4=(k+2)+2 by omega,Nat.fib_add_two]
      simp only [show k+2+1=k+3 by omega,f2,f3]
      omega
    have f5 : Nat.fib (k+5)=3*Nat.fib k+5*Nat.fib (k+1) := by
      rw [show k+5=(k+3)+2 by omega,Nat.fib_add_two]
      simp only [show k+3+1=k+4 by omega,f3,f4]
      omega
    constructor
    · intro n hn hn'
      have he : E k=5*Nat.fib k+7*Nat.fib (k+1) := by simp only [E,H,D,f2,f4]; omega
      have hh : H k=3*Nat.fib k+4*Nat.fib (k+1) := by simp only [H,f2,f4]; omega
      rw [hh]
      apply hlin.1 n <;> omega
    · intro n hn hn'
      have he : E k=5*Nat.fib k+7*Nat.fib (k+1) := by simp only [E,H,D,f2,f4]; omega
      have hs : S (k+1)=6*Nat.fib k+10*Nat.fib (k+1) := by
        simp only [S,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,↓reduceIte,Nat.add_assoc,f5]
        omega
      have hd : D k=2*Nat.fib k+3*Nat.fib (k+1) := f4
      have h := hlin.2 n (by omega) (by omega)
      rw [hd]
      omega
  refine ⟨?_,fun k => (hshape k).2⟩
  intro k n hn hn'
  by_cases hk : k=0
  · subst k
    rw [S_zero] at hn
    by_cases hn5 : n=5
    · subst n
      have h := a_small b rec h1 5 (by omega) (by omega)
      simpa only [H_zero] using h
    · apply (hshape 0).1 n _ hn'
      change 6 ≤ n
      omega
  · apply (hshape k).1 n _ hn'
    simpa only [S,hk,↓reduceIte] using hn

end A356992Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a356992.main := by
  intro b h1 rec
  obtain ⟨hp,hr⟩ := A356992Proof.sequence_shapes b rec h1
  exact A356992Proof.consequences (OMA.S_oeis_a356992.a b)
    (A356992Proof.a_small b rec h1) hp hr
