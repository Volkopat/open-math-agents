import OMAStatements.S_oeis_a254211
import Mathlib.Tactic

namespace OMA.Wheel254211
open OMA.S_oeis_a254211
lemma np {m n : ℕ} (h1 : m ∣ n := by omega) (h2 : 2 ≤ m := by decide) (h3 : m < n := by omega) :
    ¬ n.Prime := Nat.not_prime_of_dvd_of_lt h1 h2 h3

def copies (pattern : List ℕ) (k : ℕ) : List ℕ :=
  (List.replicate k pattern).flatten

lemma copies_succ (w : List ℕ) (k : ℕ) :
    copies w (k+1) = w ++ copies w k := by
  simp [copies, List.replicate_succ]

lemma copies_reverse (w : List ℕ) (k : ℕ) :
    (copies w k).reverse = copies w.reverse k := by
  simp [copies, List.reverse_flatten]

lemma length_copies (w : List ℕ) (k : ℕ) : (copies w k).length = k * w.length := by
  induction k with
  | zero => simp [copies]
  | succ k ih => simp [copies_succ, ih, Nat.succ_mul, Nat.add_comm]

lemma forward_steps (k : ℕ) (tail : List ℕ) (h : validSteps 2 tail) :
    validSteps 2 (copies [3,1,2] k ++ tail) := by
  induction k with
  | zero => simpa [copies] using h
  | succ k ih => simpa [copies_succ, validSteps] using ih

lemma backward_steps (k : ℕ) (tail : List ℕ) (h : validSteps 3 tail) :
    validSteps 3 (copies [2,1,3] k ++ tail) := by
  induction k with
  | zero => simpa [copies] using h
  | succ k ih => simpa [copies_succ, validSteps] using ih

def avoids := sumsSatisfy (fun x => ¬ x.Prime)

lemma forward_sums (k s : ℕ) (tail : List ℕ) (hs : 6 ∣ s) (hp : 6 ≤ s)
    (h : avoids (s+6*k) tail) : avoids s (copies [3,1,2] k ++ tail) := by
  induction k generalizing s with
  | zero => simpa [copies] using h
  | succ k ih =>
    rw [copies_succ, List.append_assoc]
    change ¬ (s+3).Prime ∧ ¬ (s+3+1).Prime ∧ ¬ (s+3+1+2).Prime ∧ _
    refine ⟨np (m:=3),
      np (m:=2),
      np (m:=2), ?_⟩
    apply ih (s+3+1+2) (by omega) (by omega)
    convert h using 1
    omega

lemma backward_sums (k s : ℕ) (tail : List ℕ) (hs : 6 ∣ s) (hp : 6 ≤ s)
    (h : avoids (s+6*k) tail) : avoids s (copies [2,1,3] k ++ tail) := by
  induction k generalizing s with
  | zero => simpa [copies] using h
  | succ k ih =>
    rw [copies_succ, List.append_assoc]
    change ¬ (s+2).Prime ∧ ¬ (s+2+1).Prime ∧ ¬ (s+2+1+3).Prime ∧ _
    refine ⟨np (m:=2),
      np (m:=3),
      np (m:=2), ?_⟩
    apply ih (s+2+1+3) (by omega) (by omega)
    convert h using 1
    omega

def half (k : ℕ) : List ℕ := [1,3,2] ++ copies [3,1,2] k ++ [3,2,3]
def word (k : ℕ) : List ℕ := half k ++ [2] ++ (half k).reverse

lemma word_expand (k : ℕ) : word k =
    [1,3,2] ++ (copies [3,1,2] k ++ ([3,2,3,2,3,2,3] ++
    (copies [2,1,3] k ++ [2,3,1]))) := by
  simp [word, half, List.reverse_append, copies_reverse, List.append_assoc]

lemma word_steps (k : ℕ) : validSteps 0 (word k) := by
  rw [word_expand]
  simp only [List.cons_append, List.nil_append, validSteps]
  norm_num
  apply forward_steps
  norm_num [validSteps]
  apply backward_steps
  norm_num [validSteps]

lemma word_sums (t : ℕ) : avoids 0 (word (35*t+11)) := by
  rw [word_expand]
  change ¬ Nat.Prime 1 ∧ ¬ Nat.Prime 4 ∧ ¬ Nat.Prime 6 ∧ _
  refine ⟨by decide, by decide, by decide, ?_⟩
  apply forward_sums (35*t+11) 6 _ (by decide) (by decide)
  let s := 6+6*(35*t+11)
  change ¬ (s+3).Prime ∧ ¬ (s+3+2).Prime ∧ ¬ (s+3+2+3).Prime ∧
    ¬ (s+3+2+3+2).Prime ∧ ¬ (s+3+2+3+2+3).Prime ∧
    ¬ (s+3+2+3+2+3+2).Prime ∧ ¬ (s+3+2+3+2+3+2+3).Prime ∧ _
  dsimp [s]
  refine ⟨np (m:=3),
    np (m:=7),
    np (m:=2),
    np (m:=2),
    np (m:=5),
    np (m:=3),
    np (m:=2), ?_⟩
  apply backward_sums (35*t+11) _ _ (by omega) (by omega)
  change ¬ (_+2).Prime ∧ ¬ (_+2+3).Prime ∧ ¬ (_+2+3+1).Prime ∧ True
  exact ⟨np (m:=2),
    np (m:=7),
    np (m:=2), trivial⟩

end OMA.Wheel254211

open OMA.Wheel254211
theorem OMA.solution : type_of% @OMA.S_oeis_a254211.main := by
  intro B
  let k := 35*B+11
  refine ⟨word k, ?_, word_steps k, word_sums B, ?_⟩
  · simp [word, half, length_copies, k]
    omega
  · have h : (word k).reverse = word k := by simp [word, List.append_assoc]
    rw [h]
    exact word_sums B
