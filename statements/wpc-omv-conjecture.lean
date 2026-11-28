import Mathlib

/-!
# Online Boolean matrix–vector (OMv) conjecture

Source: https://en.wikipedia.org/wiki/Online_matrix-vector_multiplication_problem
Credit: @ZenimXD

Given an $n \times n$ Boolean matrix $M$, which may be preprocessed, and $n$ Boolean vectors
$v_1, \dots, v_n$ arriving one at a time, where the Boolean matrix–vector product $M v_i$ must be
output before $v_{i+1}$ is revealed, the OMv conjecture (Henzinger, Krinninger, Nanongkai, and
Saranurak, STOC 2015) states that for every constant $\varepsilon > 0$, there is no
$O(n^{3-\varepsilon})$-time randomized algorithm that solves OMv with probability at least $2/3$.

Conventions:
- Machine model: uniform randomized Word RAM with word size $w(n) = c_w \cdot (\lfloor \log_2 n \rfloor + 1) = \Theta(\log n)$
  bits (where $c_w \ge 1$ is a constant of the algorithm) and unit-cost standard word operations
  (arithmetic, bitwise operations, shifts, indirect memory load/store, conditional jump, random bit
  sampling, and matrix/vector/output buffer access). This is the standard model of Henzinger et al.
  (2015) and fine-grained complexity.
- Online causality: the preprocessing phase has access only to $n$ and $M$ (not to any $v_i$), and
  round $i$ has access only to $v_i$ and the persistent machine state from previous phases (not to
  $v_j$ for $j > i$). The output buffer at the end of round $i$ is checked against $M v_i$ before
  round $i+1$ begins.
- Randomness and time bound: an algorithm with worst-case total time bound $T(n) \le C n^{3-\varepsilon}$
  reads at most $T(n)$ random bits; success probability $\ge 2/3$ over uniform random bits is
  expressed as the exact counting inequality $3 \cdot |\{r \in \{0,1\}^{T(n)} : \text{succeeds}\}| \ge 2 \cdot 2^{T(n)}$.
-/

namespace OMA.S_wpc_omv_conjecture

/-- Boolean matrix–vector product: `(M v)_i = ⋁_j (M i j ∧ v j)`. -/
def boolMatVec {n : ℕ} (M : Matrix (Fin n) (Fin n) Bool) (v : Fin n → Bool) : Fin n → Bool :=
  fun i => decide (∃ j : Fin n, M i j = true ∧ v j = true)

/-- Instructions of a Word RAM machine with `R` registers. -/
inductive Instr (R : ℕ) where
  | const (dst : Fin R) (val : ℕ)
  | mov (dst src : Fin R)
  | add (dst a b : Fin R)
  | sub (dst a b : Fin R)
  | mul (dst a b : Fin R)
  | div (dst a b : Fin R)
  | bitAnd (dst a b : Fin R)
  | bitOr (dst a b : Fin R)
  | bitXor (dst a b : Fin R)
  | bitNot (dst a : Fin R)
  | shl (dst a b : Fin R)
  | shr (dst a b : Fin R)
  | load (dst addr : Fin R)
  | store (addr src : Fin R)
  | jnz (cond : Fin R) (target : ℕ)
  | randBit (dst : Fin R)
  | readMat (dst row col : Fin R)
  | readVec (dst idx : Fin R)
  | writeOut (idx val : Fin R)
  | halt

/-- A uniform online Word RAM algorithm: a fixed finite program with `R` registers, word-size
multiplier `wordMult ≥ 1` (giving word length `wordMult * (Nat.log2 n + 1)` bits), and an entry
point `roundEntry` executed at the start of each online round. -/
structure OnlineWordRAM where
  numRegs : ℕ
  numRegs_pos : 0 < numRegs
  progLen : ℕ
  prog : Fin progLen → Instr numRegs
  roundEntry : ℕ
  wordMult : ℕ
  wordMult_pos : 0 < wordMult

/-- Runtime state of a Word RAM machine. -/
structure State (R : ℕ) where
  pc : ℕ
  reg : Fin R → ℕ
  mem : ℕ → ℕ
  outBuf : ℕ → Bool
  randPos : ℕ
  halted : Bool

/-- Single step of a Word RAM machine with word width `w`, dimension `n`, matrix `M`, optional
current-round vector `vOpt`, and random bit stream `rand`. -/
def step (alg : OnlineWordRAM) (w n : ℕ) (M : Matrix (Fin n) (Fin n) Bool)
    (vOpt : Option (Fin n → Bool)) (rand : ℕ → Bool) (st : State alg.numRegs) :
    State alg.numRegs :=
  if st.halted then st
  else if hpc : st.pc < alg.progLen then
    let mask := 2 ^ w
    let setReg (dst : Fin alg.numRegs) (val : ℕ) : Fin alg.numRegs → ℕ :=
      Function.update st.reg dst (val % mask)
    match alg.prog ⟨st.pc, hpc⟩ with
    | .const dst val => { st with pc := st.pc + 1, reg := setReg dst val }
    | .mov dst src => { st with pc := st.pc + 1, reg := setReg dst (st.reg src) }
    | .add dst a b => { st with pc := st.pc + 1, reg := setReg dst (st.reg a + st.reg b) }
    | .sub dst a b => { st with pc := st.pc + 1, reg := setReg dst (st.reg a - st.reg b) }
    | .mul dst a b => { st with pc := st.pc + 1, reg := setReg dst (st.reg a * st.reg b) }
    | .div dst a b => { st with pc := st.pc + 1, reg := setReg dst (st.reg a / st.reg b) }
    | .bitAnd dst a b => { st with pc := st.pc + 1, reg := setReg dst (st.reg a &&& st.reg b) }
    | .bitOr dst a b => { st with pc := st.pc + 1, reg := setReg dst (st.reg a ||| st.reg b) }
    | .bitXor dst a b => { st with pc := st.pc + 1, reg := setReg dst (st.reg a ^^^ st.reg b) }
    | .bitNot dst a =>
      { st with pc := st.pc + 1, reg := setReg dst ((mask - 1) - (st.reg a % mask)) }
    | .shl dst a b => { st with pc := st.pc + 1, reg := setReg dst (st.reg a <<< st.reg b) }
    | .shr dst a b => { st with pc := st.pc + 1, reg := setReg dst (st.reg a >>> st.reg b) }
    | .load dst addr => { st with pc := st.pc + 1, reg := setReg dst (st.mem (st.reg addr)) }
    | .store addr src =>
      { st with pc := st.pc + 1, mem := Function.update st.mem (st.reg addr) (st.reg src % mask) }
    | .jnz cond target =>
      { st with pc := if st.reg cond ≠ 0 then target else st.pc + 1 }
    | .randBit dst =>
      { st with
        pc := st.pc + 1
        reg := setReg dst (if rand st.randPos then 1 else 0)
        randPos := st.randPos + 1 }
    | .readMat dst row col =>
      let val :=
        if hr : st.reg row < n then
          if hc : st.reg col < n then
            if M ⟨st.reg row, hr⟩ ⟨st.reg col, hc⟩ then 1 else 0
          else 0
        else 0
      { st with pc := st.pc + 1, reg := setReg dst val }
    | .readVec dst idx =>
      let val :=
        match vOpt with
        | none => 0
        | some v =>
          if hi : st.reg idx < n then
            if v ⟨st.reg idx, hi⟩ then 1 else 0
          else 0
      { st with pc := st.pc + 1, reg := setReg dst val }
    | .writeOut idx val =>
      { st with pc := st.pc + 1, outBuf := Function.update st.outBuf (st.reg idx) (st.reg val ≠ 0) }
    | .halt => { st with halted := true }
  else
    { st with halted := true }

/-- Run a single phase (preprocessing or one online round) using at most `budget` remaining steps,
returning the final state and the remaining step budget. -/
def runPhase (alg : OnlineWordRAM) (w n : ℕ) (M : Matrix (Fin n) (Fin n) Bool)
    (vOpt : Option (Fin n → Bool)) (rand : ℕ → Bool) :
    ℕ → State alg.numRegs → State alg.numRegs × ℕ
  | 0, st => (st, 0)
  | budget + 1, st =>
    if st.halted then (st, budget + 1)
    else runPhase alg w n M vOpt rand budget (step alg w n M vOpt rand st)

/-- Initial machine state for dimension `n`, with `n` stored in register 0. -/
def initState (alg : OnlineWordRAM) (w n : ℕ) : State alg.numRegs where
  pc := 0
  reg := Function.update (fun _ => 0) ⟨0, alg.numRegs_pos⟩ (n % 2 ^ w)
  mem := fun _ => 0
  outBuf := fun _ => false
  randPos := 0
  halted := false

/-- Execute the online OMv protocol on `(M, vs)` within a total step budget `budget` across
preprocessing and all `n` rounds. Returns `true` iff every phase halts within the budget and
every round `i` outputs `boolMatVec M (vs i)` before `vs (i + 1)` is revealed. -/
def runRounds (alg : OnlineWordRAM) (w n : ℕ) (M : Matrix (Fin n) (Fin n) Bool)
    (vs : Fin n → Fin n → Bool) (rand : ℕ → Bool) :
    (k : ℕ) → k ≤ n → State alg.numRegs → ℕ → Bool
  | 0, _, _, _ => true
  | k + 1, hk, st, budget =>
    let r : Fin n := ⟨n - (k + 1), by omega⟩
    let stStart : State alg.numRegs := { st with pc := alg.roundEntry, halted := false }
    let (stEnd, rem) := runPhase alg w n M (some (vs r)) rand budget stStart
    let okRound : Bool :=
      stEnd.halted &&
      decide ((fun i : Fin n => stEnd.outBuf i.val) = boolMatVec M (vs r))
    okRound && runRounds alg w n M vs rand k (by omega) stEnd rem

/-- Full online OMv execution (preprocessing followed by `n` online rounds) within total step
budget `budget` using random bits `r : Fin budget → Bool`. -/
def succeeds (alg : OnlineWordRAM) {n : ℕ} (M : Matrix (Fin n) (Fin n) Bool)
    (vs : Fin n → Fin n → Bool) (budget : ℕ) (r : Fin budget → Bool) : Bool :=
  let w := alg.wordMult * (Nat.log2 n + 1)
  let rand : ℕ → Bool := fun k => if hk : k < budget then r ⟨k, hk⟩ else false
  let (stPrep, rem) := runPhase alg w n M none rand budget (initState alg w n)
  stPrep.halted && runRounds alg w n M vs rand n le_rfl stPrep rem

/-- An online Word RAM algorithm solves OMv in total time `T(n)` with success probability at least
`2/3` if, for every `n ≥ 1`, every `n × n` Boolean matrix `M`, and every sequence of `n` Boolean
vectors `vs`, at least a `2/3` fraction of random bit strings of length `T(n)` succeed. -/
def SolvesOMvInTime (alg : OnlineWordRAM) (T : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ), 0 < n →
  ∀ (M : Matrix (Fin n) (Fin n) Bool) (vs : Fin n → Fin n → Bool),
    2 * 2 ^ (T n) ≤ 3 * (Finset.univ.filter fun r : Fin (T n) → Bool =>
      succeeds alg M vs (T n) r = true).card

theorem main :
    ∀ ε : ℝ, 0 < ε →
      ¬ ∃ (alg : OnlineWordRAM) (T : ℕ → ℕ) (C : ℝ),
        0 < C ∧
        (∀ n : ℕ, 0 < n → (T n : ℝ) ≤ C * (n : ℝ) ^ (3 - ε)) ∧
        SolvesOMvInTime alg T := by
  sorry

end OMA.S_wpc_omv_conjecture
