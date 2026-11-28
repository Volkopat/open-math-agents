import Mathlib

/-!
# X + Y sorting

Source: https://en.wikipedia.org/wiki/X_%2B_Y_sorting
Credit: @eltociear

The source (Wikipedia, X + Y sorting) asks: is there a comparison-based algorithm that, given two
collections X and Y of n numbers each, outputs the n² pairs (x, y) sorted by x + y in time
asymptotically faster than O(n² log n), i.e. in time o(n² log n)?
(Fredman 1976: O(n²) comparisons suffice, but only non-uniformly; the best known running time
is O(n² log n).)

## Model of computation (the standard reading, made explicit)

The question is about the total running time of a single uniform algorithm, not about the
number of comparisons (that is Fredman's O(n²), already known). We fix the usual model:

* a word RAM with unit-cost instructions on w-bit words, w = c * (log₂ n + 1) for a constant c
  chosen by the algorithm (so w = Θ(log n), enough to hold indices and counters);
  arithmetic is reduced mod 2^w; memory is an array of words indexed by words, initially 0,
  except that cell 0 holds n;
* the input numbers are real numbers that the program can access only through comparisons of
  sums: one instruction tests x_i + y_j ≤ x_k + y_l (the comparison-based restriction of the
  source). This covers comparisons inside X or inside Y (x_i ≤ x_k iff x_i + y_0 ≤ x_k + y_0)
  and of differences (x_i - x_k ≤ y_l - y_j iff x_i + y_j ≤ x_k + y_l), as used by Lambert's
  algorithm. Out-of-range indices read the value 0;
* the program writes its output as a list of index pairs; it must halt within T(n) steps on
  every input of size n, and the output must list every pair (i, j) with i, j < n exactly once,
  in nondecreasing order of x_i + y_j (ties in any order).

`main` states the positive answer: such a program exists with T(n) = o(n² log n).
A proof of `¬` this statement would settle the question negatively.
-/

namespace OMA.S_wpc_x_plus_y_sorting

/-- Binary word operations available to the word RAM. -/
inductive BinOp
  | add | sub | mul | div | mod | land | lor | xor

/-- Instructions of the word RAM. Arguments are memory addresses (or a jump target / constant). -/
inductive Instr
  /-- `M[d] := k` -/
  | const (d k : ℕ)
  /-- `M[d] := M[a] op M[b]` -/
  | bin (op : BinOp) (d a b : ℕ)
  /-- indirect load `M[d] := M[M[a]]` -/
  | load (d a : ℕ)
  /-- indirect store `M[M[a]] := M[s]` -/
  | store (a s : ℕ)
  /-- jump to instruction `t` if `M[a] = 0` -/
  | jz (a t : ℕ)
  /-- `M[d] := 1` if `x_{M[i]} + y_{M[j]} ≤ x_{M[k]} + y_{M[l]}`, else `0` -/
  | cmp (d i j k l : ℕ)
  /-- append the pair `(M[a], M[b])` to the output -/
  | out (a b : ℕ)
  /-- stop -/
  | halt

/-- Machine state: program counter, memory, output written so far (in order). -/
structure State where
  pc : ℕ
  mem : ℕ → ℕ
  out : List (ℕ × ℕ)

/-- Read an input number; indices out of range read 0. -/
noncomputable def readIn {n : ℕ} (X : Fin n → ℝ) (i : ℕ) : ℝ :=
  if h : i < n then X ⟨i, h⟩ else 0

def BinOp.eval : BinOp → ℕ → ℕ → ℕ
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .div, a, b => a / b
  | .mod, a, b => a % b
  | .land, a, b => Nat.land a b
  | .lor, a, b => Nat.lor a b
  | .xor, a, b => Nat.xor a b

def write (m : ℕ → ℕ) (a v : ℕ) : ℕ → ℕ :=
  fun i => if i = a then v else m i

/-- The instruction at the program counter; `none` means the machine has halted
(explicit `halt`, or the program counter left the program). -/
def current (P : List Instr) (s : State) : Option Instr :=
  match P[s.pc]? with
  | some .halt => none
  | i => i

/-- One step of the word RAM with word size `w` on inputs `X`, `Y`. -/
noncomputable def exec {n : ℕ} (w : ℕ) (X Y : Fin n → ℝ) (s : State) : Instr → State
  | .const d k => { s with pc := s.pc + 1, mem := write s.mem d (k % 2 ^ w) }
  | .bin op d a b =>
      { s with pc := s.pc + 1, mem := write s.mem d (op.eval (s.mem a) (s.mem b) % 2 ^ w) }
  | .load d a => { s with pc := s.pc + 1, mem := write s.mem d (s.mem (s.mem a)) }
  | .store a src => { s with pc := s.pc + 1, mem := write s.mem (s.mem a) (s.mem src) }
  | .jz a t => { s with pc := if s.mem a = 0 then t else s.pc + 1 }
  | .cmp d i j k l =>
      { s with pc := s.pc + 1,
               mem := write s.mem d
                 (if readIn X (s.mem i) + readIn Y (s.mem j) ≤
                     readIn X (s.mem k) + readIn Y (s.mem l) then 1 else 0) }
  | .out a b => { s with pc := s.pc + 1, out := s.out ++ [(s.mem a, s.mem b)] }
  | .halt => s

/-- Run for at most `fuel` steps; `some s` if the machine has halted (in state `s`) within
`fuel` steps, `none` otherwise. -/
noncomputable def run (P : List Instr) {n : ℕ} (w : ℕ) (X Y : Fin n → ℝ) :
    ℕ → State → Option State
  | fuel, s =>
    match current P s with
    | none => some s
    | some ins =>
      match fuel with
      | 0 => none
      | k + 1 => run P w X Y k (exec w X Y s ins)

/-- Initial state on an input of size `n`: memory cell 0 holds `n`, every other cell is 0. -/
def init (n : ℕ) : State :=
  { pc := 0, mem := fun i => if i = 0 then n else 0, out := [] }

/-- `P` solves X + Y sorting with word size `c * (log₂ n + 1)` within `T n` steps. -/
def SortsXY (P : List Instr) (c : ℕ) (T : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) (X Y : Fin n → ℝ), ∃ s : State,
    run P (c * (Nat.log 2 n + 1)) X Y (T n) (init n) = some s ∧
    s.out.Perm (List.product (List.range n) (List.range n)) ∧
    s.out.Pairwise (fun p q => readIn X p.1 + readIn Y p.2 ≤ readIn X q.1 + readIn Y q.2)

theorem main :
    ∃ (P : List Instr) (c : ℕ) (T : ℕ → ℕ), SortsXY P c T ∧
      (fun n : ℕ => (T n : ℝ)) =o[Filter.atTop] (fun n : ℕ => (n : ℝ) ^ 2 * Real.log n) := by
  sorry

end OMA.S_wpc_x_plus_y_sorting
