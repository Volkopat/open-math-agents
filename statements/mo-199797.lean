import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Computability.NFA
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Order.LiminfLimsup

/-!
# Estimating the growth rate of nondeterministic finite automata

Source: https://mathoverflow.net/questions/199797

The source asks for efficient computation or approximation of the exponential
language growth rate. It does not prescribe an error model or specify whether
randomization is allowed. This proposed formalization asks for a fully
polynomial-time randomized relative-error approximation scheme (FPRAS).
It addresses the approximation alternative, not deterministic approximation
or exact computation. The parameters are 1/k for the relative error and 2^(-s)
for the failure probability; their unary encodings implement the usual
polynomial dependence on k and s.

The growth rate is defined by the limsup of the positive-length accepted-word
counts raised to the reciprocal length. In spectral-radius terminology the
DFA must retain only states on accepting runs, and matrix entries count letters.
A limsup accommodates periodic languages and the growth rate is zero for
finite languages. The result is stated for epsilon-free NFAs; epsilon moves
can be removed in polynomial time before applying it.
-/

namespace OMA.S_mo_199797

/-- An epsilon-free NFA with an explicit transition table. -/
structure InputNFA where
  stateCount : ℕ
  alphabetSize : ℕ
  initial : Fin stateCount → Bool
  final : Fin stateCount → Bool
  transition : Fin stateCount → Fin alphabetSize → Fin stateCount → Bool

/-- Interpret the finite table as a Mathlib NFA. -/
def InputNFA.toNFA (A : InputNFA) : NFA (Fin A.alphabetSize) (Fin A.stateCount) where
  step q a := {q' | A.transition q a q' = true}
  start := {q | A.initial q = true}
  accept := {q | A.final q = true}

/-- Count distinct accepted words of length m. -/
noncomputable def wordCount (A : InputNFA) (m : ℕ) : ℕ := by
  classical
  exact Fintype.card {w : Fin m → Fin A.alphabetSize // List.ofFn w ∈ A.toNFA.accepts}

/-- The upper exponential growth rate, using positive word lengths. -/
noncomputable def growthRate (A : InputNFA) : ℝ :=
  Filter.limsup
    (fun m : ℕ => Real.rpow (wordCount A (m + 1) : ℝ) (1 / ((m : ℝ) + 1)))
    Filter.atTop

/-- A self-delimiting unary code, consisting of n ones followed by a zero. -/
def unary (n : ℕ) : List Bool :=
  List.replicate n true ++ [false]

/-- Encode the NFA and the requested relative error 1/k and failure probability 2^(-s).
The two unary dimensions determine the length of each part of the table. -/
def encodeInstance (A : InputNFA) (k s : ℕ) : List Bool :=
  unary A.stateCount ++ unary A.alphabetSize ++
    List.ofFn A.initial ++ List.ofFn A.final ++
    (List.ofFn fun (q : Fin A.stateCount) =>
      (List.ofFn fun (a : Fin A.alphabetSize) =>
        List.ofFn (A.transition q a)).flatten).flatten ++
    unary k ++ unary s

/-- Interpret a list as a little-endian binary natural number. -/
def decodeNat : List Bool → ℕ
  | [] => 0
  | bit :: rest => (if bit then 1 else 0) + 2 * decodeNat rest

/-- The output encodes a dyadic: a unary exponent followed by a binary numerator. -/
noncomputable def decodeOutput (bits : List Bool) : ℝ :=
  let exponent := (bits.takeWhile id).length
  (decodeNat (bits.drop (exponent + 1)) : ℝ) / (2 : ℝ) ^ exponent

/-- Count the equally likely random tapes on which the output meets the error bound. -/
noncomputable def successfulTapes (run : List Bool → List Bool) (A : InputNFA)
    (k s tapeLength : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun tape : Fin tapeLength → Bool =>
    |decodeOutput (run (encodeInstance A k s ++ List.ofFn tape)) - growthRate A|
      ≤ growthRate A / (k : ℝ))).card

/-- Polynomial-time computation on bit strings with finite alphabets on all stacks.
The bundled `FinTM2` machine in `TM2ComputableInPolyTime` already requires
`Fintype` instances for its stack indices, instruction labels and internal states.
The additional condition here requires finiteness of every stack alphabet. -/
def bitPolynomialTime (run : List Bool → List Bool) : Prop :=
  ∃ machine : Turing.TM2ComputableInPolyTime id id run,
    ∀ stack : machine.tm.K, Finite (machine.tm.Γ stack)

/-- There is a fully polynomial-time randomized approximation scheme for the
growth rate of an explicitly given NFA over a nonempty alphabet.

The TM2 machine takes the encoded instance followed by its random tape.
A polynomial bounds the length of the tape in terms of the instance size.
Counting uniformly random tapes expresses the success probability exactly. -/
theorem main :
    ∃ (run : List Bool → List Bool) (randomBits : Polynomial ℕ),
      bitPolynomialTime run ∧
      ∀ (A : InputNFA) (k s : ℕ), 0 < A.alphabetSize → 2 ≤ k → 1 ≤ s →
        let r := randomBits.eval (encodeInstance A k s).length
        (2 ^ s - 1) * 2 ^ r ≤ 2 ^ s * successfulTapes run A k s r := by
  sorry

end OMA.S_mo_199797
