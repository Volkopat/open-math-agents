import OMAStatements.S_oeis_a094603
import Mathlib

/-!
# Right-edge runs in Rule 30

In coordinates measured inward from the right edge, each new bit is its
old value XOR a function of two earlier bits. The period on a prefix of
width k therefore divides 2^k. The all-black prefix evolves to the initial
single-black-cell prefix, so run lengths are detected by return times.
-/

namespace Rule30Edge

open OMA.S_oeis_a094603 Function

def Bits : ℕ → Type
  | 0 => Unit
  | k+1 => Bits k × Bool

def last : (k : ℕ) → Bits k → Bool
  | 0, _ => false
  | _+1, v => v.2

def penult : (k : ℕ) → Bits k → Bool
  | 0, _ => false
  | k+1, v => last k v.1

def advance : (k : ℕ) → Bits k → Bits k
  | 0, v => v
  | k+1, v => (advance k v.1, xor v.2 (last k v.1 || penult k v.1))

def black : (k : ℕ) → Bits k
  | 0 => ()
  | k+1 => (black k, true)

def flip (k : ℕ) (v : Bits (k+1)) : Bits (k+1) := (v.1, !v.2)

lemma flip_flip (k : ℕ) (v : Bits (k+1)) : flip k (flip k v) = v := by
  rcases v with ⟨w,b⟩
  cases b <;> rfl

lemma flip_commute (k : ℕ) : Function.Commute (flip k) (advance (k+1)) := by
  intro v
  change (_, !(xor v.2 (last k v.1 || penult k v.1))) =
    (_, xor (!v.2) (last k v.1 || penult k v.1))
  cases v.2 <;> cases (last k v.1 || penult k v.1) <;> rfl

lemma iter_prefix (k j : ℕ) (v : Bits (k+1)) :
    ((advance (k+1))^[j] v).1 = (advance k)^[j] v.1 := by
  induction j generalizing v with
  | zero => rfl
  | succ j ih =>
    rw [iterate_succ_apply,iterate_succ_apply,ih]
    rfl

lemma period_pow (k : ℕ) (v : Bits k) : IsPeriodicPt (advance k) (2^k) v := by
  induction k with
  | zero => rfl
  | succ k ih =>
    let f := advance (k+1)
    let t := 2^k
    have prefix_eq : (f^[t] v).1 = v.1 := (iter_prefix k t v).trans (ih v.1)
    have either : f^[t] v = v ∨ f^[t] v = flip k v := by
      by_cases h : (f^[t] v).2 = v.2
      · exact Or.inl (Prod.ext prefix_eq h)
      · right
        apply Prod.ext
        · exact prefix_eq
        change (f^[t] v).2 = !v.2
        have opposite (b c : Bool) (hne : b ≠ c) : b = !c := by
          cases b <;> cases c <;> simp_all
        exact opposite _ _ h
    change f^[2^(k+1)] v = v
    rw [pow_succ,mul_two,iterate_add_apply]
    change f^[t] (f^[t] v) = v
    rcases either with he | he
    · rw [he,he]
    · calc
        f^[t] (f^[t] v) = f^[t] (flip k v) := congrArg _ he
        _ = flip k (f^[t] v) := ((flip_commute k).iterate_right t v).symm
        _ = v := by rw [he,flip_flip]

lemma return_iff (k n : ℕ) (hn : n ≠ 0) :
    IsPeriodicPt (advance k) n (black k) ↔
    IsPeriodicPt (advance k) (2 ^ padicValNat 2 n) (black k) := by
  obtain ⟨j,_,hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (period_pow k (black k)).minimalPeriod_dvd
  rw [isPeriodicPt_iff_minimalPeriod_dvd,isPeriodicPt_iff_minimalPeriod_dvd,hj,
    padicValNat_dvd_iff_le_of_ne_one (by decide : 2 ≠ 1) hn]
  exact (pow_dvd_pow_iff (by decide : (2:ℕ) ≠ 0) (by decide : ¬ IsUnit (2:ℕ))).symm


def cell (t : ℕ) (j : ℤ) : Bool := row t ((t : ℤ)-j)

lemma outside (t : ℕ) (x : ℤ) (h : (t:ℤ) < x ∨ x < -(t:ℤ)) : row t x = false := by
  induction t generalizing x with
  | zero =>
    simp only [row,decide_eq_false_iff_not]
    omega
  | succ t ih =>
    simp only [row]
    rw [ih (x-1) (by omega),ih x (by omega),ih (x+1) (by omega)]
    rfl

lemma step_cell (t : ℕ) (j : ℤ) : cell (t+1) j =
    xor (cell t j) (cell t (j-1) || cell t (j-2)) := by
  simp only [cell,row,Nat.cast_add,Nat.cast_one]
  rw [show (t:ℤ)+1-j-1 = t-j by ring,
    show (t:ℤ)-(j-1) = t+1-j by ring, show (t:ℤ)-(j-2) = (t+1-j)+1 by ring]

def snap (t : ℕ) : (k : ℕ) → Bits k
  | 0 => ()
  | k+1 => (snap t k,cell t k)

lemma last_snap (t k : ℕ) : last k (snap t k) = cell t ((k:ℤ)-1) := by
  cases k with
  | zero => exact (outside t _ (by left; omega)).symm
  | succ k => simp [last,snap]

lemma penult_snap (t k : ℕ) : penult k (snap t k) = cell t ((k:ℤ)-2) := by
  cases k with
  | zero => exact (outside t _ (by left; omega)).symm
  | succ k =>
    change last k (snap t k) = _
    rw [last_snap]
    congr 1
    omega

lemma snap_step (t k : ℕ) : snap (t+1) k = advance k (snap t k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    apply Prod.ext ih
    change cell (t+1) k = xor (cell t k) (last k (snap t k) || penult k (snap t k))
    rw [step_cell,last_snap,penult_snap]

lemma snap_initial (k : ℕ) : snap 0 k = advance k (black k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    apply Prod.ext ih
    cases k with
    | zero => rfl
    | succ k =>
      change cell 0 (k+1:ℕ) = xor true (true || penult (k+1) (black (k+1)))
      simp [cell,row]
      omega

lemma snap_iter (t k : ℕ) : snap t k = (advance k)^[t+1] (black k) := by
  induction t with
  | zero => exact snap_initial k
  | succ t ih =>
    rw [snap_step,ih,iterate_succ_apply' (advance k) (t+1)]

lemma snap_black_iff (t k : ℕ) :
    snap t k = black k ↔ ∀ j : ℕ, j < k → cell t j = true := by
  induction k with
  | zero =>
    simp [snap,black]
    rfl
  | succ k ih =>
    change (snap t k,cell t k) = (black k,true) ↔ _
    rw [Prod.mk.injEq,ih]
    constructor
    · rintro ⟨h,ht⟩ j hj
      obtain hlt | rfl := lt_or_eq_of_le (Nat.le_of_lt_succ hj)
      · exact h _ hlt
      · exact ht
    · intro h
      exact ⟨fun j hj => h j (by omega),h k (by omega)⟩

lemma le_run_iff (t k : ℕ) : k ≤ run t ↔ snap t k = black k := by
  rw [snap_black_iff]
  let W := {j : ℕ | cell t j = false}
  have hw : W.Nonempty := ⟨2*t+1, outside t _ (by right; push_cast; omega)⟩
  change k ≤ sInf W ↔ _
  constructor
  · intro hk j hj
    cases he : cell t j with
    | true => rfl
    | false =>
      have hlow : sInf W ≤ j := Nat.sInf_le he
      omega
  · intro h
    apply le_csInf hw
    intro j hj
    by_contra! hlt
    exact Bool.noConfusion ((h j hlt).symm.trans (show cell t j = false from hj))

end Rule30Edge

theorem OMA.solution : type_of% @OMA.S_oeis_a094603.main := by
  intro n hn
  have hpow : 0 < 2 ^ padicValNat 2 n := by positivity
  have same (k : ℕ) : k ≤ OMA.S_oeis_a094603.run (n-1) ↔
      k ≤ OMA.S_oeis_a094603.run (2^padicValNat 2 n-1) := by
    rw [Rule30Edge.le_run_iff,Rule30Edge.le_run_iff,Rule30Edge.snap_iter,Rule30Edge.snap_iter,
      Nat.sub_add_cancel hn,Nat.sub_add_cancel (by omega : 1 ≤ 2^padicValNat 2 n)]
    exact Rule30Edge.return_iff k n (by omega)
  exact Nat.le_antisymm ((same _).mp le_rfl) ((same _).mpr le_rfl)
