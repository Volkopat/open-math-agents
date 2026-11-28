import OMAStatements.S_oeis_a071033
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open OMA.S_oeis_a071033

namespace Rule94Proof

def zig : ℕ → List Bool
  | 0 => []
  | t + 1 => true :: false :: zig t

def evenWord (t : ℕ) := true :: true :: false :: (zig t ++ [true, true])
def oddWord (t : ℕ) := true :: true :: true :: false :: (zig t ++ [true, true, true])

lemma scan_zig (t : ℕ) (s r : List Bool) (h : scan true false s = false :: r) :
    scan true false (zig t ++ s) = false :: (zig t ++ r) := by
  induction t with
  | zero => exact h
  | succ t ih =>
    change false :: true :: scan true false (zig t ++ s) =
      false :: true :: false :: (zig t ++ r)
    rw [ih]

lemma shift (t : ℕ) (s : List Bool) :
    zig t ++ (true :: false :: s) = true :: false :: (zig t ++ s) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change true :: false :: (zig t ++ (true :: false :: s)) =
      true :: false :: true :: false :: (zig t ++ s)
    rw [ih]

lemma step_even (t : ℕ) : scan false false (evenWord t) = oddWord t := by
  change true :: true :: true :: scan true false (zig t ++ [true, true]) = _
  rw [scan_zig t [true, true] [true, true, true] rfl]
  rfl

lemma step_odd (t : ℕ) : scan false false (oddWord t) = evenWord (t+2) := by
  change true :: true :: false :: true :: scan true false (zig t ++ [true, true, true]) = _
  rw [scan_zig t [true, true, true] [true, false, true, true] rfl]
  rw [shift t [true, true]]
  rfl

lemma words (k : ℕ) :
    row (2*k+2) = evenWord (2*k) ∧ row (2*k+3) = oddWord (2*k) := by
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    have he : row (2*(k+1)+2) = evenWord (2*(k+1)) := by
      rw [show 2*(k+1)+2 = (2*k+3)+1 by omega, row, ih.2, step_odd]
      congr 1
    refine ⟨he, ?_⟩
    rw [show 2*(k+1)+3 = (2*(k+1)+2)+1 by omega, row, he, step_even]

lemma read_append (s r : List Bool) (x : ℕ) :
    readWord x (s ++ r) = readWord (readWord x s) r := by
  induction s generalizing x with
  | nil => rfl
  | cons b s ih => exact ih _

lemma read_zig (t x : ℕ) : 99 * readWord x (zig t) + 10 = (99*x+10) * 100^t := by
  induction t generalizing x with
  | zero => simp [zig, readWord]
  | succ t ih =>
    change 99 * readWord ((x*10+1)*10+0) (zig t) + 10 = _
    rw [ih, pow_succ]
    ring

lemma even_value (t : ℕ) :
    990 * readWord 0 (evenWord t) = 1090 * 100^(t+2) + 890 := by
  change 990 * readWord 110 (zig t ++ [true, true]) = _
  rw [read_append]
  change 990 * ((readWord 110 (zig t)*10+1)*10+1) = _
  have hz := read_zig t 110
  rw [pow_add]
  norm_num at hz ⊢
  omega

lemma odd_value (t : ℕ) :
    990 * readWord 0 (oddWord t) = 1099 * 100^(t+3) + 9890 := by
  change 990 * readWord 1110 (zig t ++ [true, true, true]) = _
  rw [read_append]
  change 990 * (((readWord 1110 (zig t)*10+1)*10+1)*10+1) = _
  have hz := read_zig t 1110
  rw [pow_add]
  norm_num at hz ⊢
  omega

end Rule94Proof

open Rule94Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a071033.main := by
  intro n hn
  let k := (n-2)/2
  have shape := words k
  rcases (show n = 2*k+2 ∨ n = 2*k+3 by dsimp [k]; omega) with h | h
  · have hp : n % 2 ≠ 1 := by omega
    rw [if_neg hp, h, shape.1]
    have hv := even_value (2*k)
    omega
  · have hp : n % 2 = 1 := by omega
    rw [if_pos hp, h, shape.2]
    have hv := odd_value (2*k)
    omega
