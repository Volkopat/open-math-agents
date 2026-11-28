import OMAReductions.R_PolyTime_isPolyTime_primeFactorsList_R1
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Size
import Mathlib.Data.Num.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Fintype.OfMap

/-!
# Polynomial-time bounded binary search

Credit: @neiam00

The finite-stack controller builds the encoded comparison for each bit,
runs the supplied comparator, and keeps the selected half of the interval.
The polynomial clock accounts for every transition, including preparing and
reading each call.
-/

/-!
# Length of the encoded prime factor list

The integer-factorization conjecture encodes each prime in binary, writing two
bits per payload bit and one delimiter per factor. The total length is at most
five times the floor of the binary logarithm of the input. Powers of two attain
the bound.
-/

namespace FactorEncoding

open BitstringEncoding

private theorem length_encodePosNum (p : PosNum) :
    (Computability.encodePosNum p).length = p.natSize := by
  induction p <;> simp_all [Computability.encodePosNum, PosNum.natSize]

/-- The canonical encoding uses the usual number of binary digits. -/
theorem length_bitEncode_nat (n : ℕ) : (bitEncode n).length = n.size := by
  have hnum (m : Num) : (Computability.encodeNum m).length = m.natSize := by
    cases m with
    | zero => rfl
    | pos p => exact length_encodePosNum p
  calc
    (bitEncode n).length = (n : Num).natSize := hnum (n : Num)
    _ = n.size := by rw [Num.natSize_to_nat, Num.to_of_nat]

private theorem length_bitEncode_pos {n : ℕ} (hn : n ≠ 0) :
    (bitEncode n).length = n.log2 + 1 := by
  rw [length_bitEncode_nat]
  have hlo : n.log2 < n.size := Nat.lt_size.mpr (Nat.log2_self_le hn)
  have hhi : n.size ≤ n.log2 + 1 := Nat.size_le.mpr Nat.lt_log2_self
  omega

private theorem length_bitEncode_cons (p : ℕ) (ps : List ℕ) :
    (bitEncode (p :: ps)).length = 2 * (bitEncode p).length + 1 + (bitEncode ps).length := by
  change (delimit (bitEncode p) ++ bitEncode ps).length = _
  rw [List.length_append, length_delimit]

private theorem length_bitEncode_le_log2_prod (ps : List ℕ) (h : ∀ p ∈ ps, 2 ≤ p) :
    (bitEncode ps).length ≤ 5 * ps.prod.log2 := by
  induction ps with
  | nil => decide
  | cons p ps ih =>
    have hp : 2 ≤ p := h p (by simp)
    have ht : ∀ q ∈ ps, 2 ≤ q := fun q hq => h q (by simp [hq])
    have hp0 : p ≠ 0 := by omega
    have ht0 : ps.prod ≠ 0 := by
      apply List.prod_ne_zero
      intro hz
      have := ht 0 hz
      omega
    have hbit : 1 ≤ p.log2 := (Nat.le_log2 hp0).mpr (by simpa using hp)
    have hlog : p.log2 + ps.prod.log2 ≤ (p * ps.prod).log2 := by
      apply (Nat.le_log2 (Nat.mul_ne_zero hp0 ht0)).mpr
      rw [pow_add]
      exact Nat.mul_le_mul (Nat.log2_self_le hp0) (Nat.log2_self_le ht0)
    have htail := ih ht
    rw [length_bitEncode_cons, length_bitEncode_pos hp0, List.prod_cons]
    omega

/-- A sharp upper bound on the length of the actual output in the conjecture. -/
theorem primeFactorsList_length_bound (n : ℕ) :
    (bitEncode n.primeFactorsList).length ≤ 5 * n.log2 := by
  by_cases hn : n = 0
  · subst n
    rw [Nat.primeFactorsList_zero]
    exact Nat.zero_le _
  · have h := length_bitEncode_le_log2_prod n.primeFactorsList
        (fun _ hp => (Nat.prime_of_mem_primeFactorsList hp).two_le)
    simpa only [Nat.prod_primeFactorsList hn] using h

/-- Each occurrence of the prime two contributes exactly five bits. -/
theorem primeFactorsList_length_two_pow (k : ℕ) :
    (bitEncode (2 ^ k).primeFactorsList).length = 5 * k := by
  rw [Nat.prime_two.primeFactorsList_pow]
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, length_bitEncode_cons, ih]
    have htwo : (bitEncode (2 : ℕ)).length = 2 := by decide
    omega

end FactorEncoding

/-!
# Cost of the comparator calls in the factor search

The recursion in the third hypothesis of the integer-factorization reduction
reads one threshold bit at a time. We record the pairs it passes to the
comparator. On an input of length `L`, the total of its comparator clocks is at
most `L * P.eval (3 * L + 1)`, for every clock polynomial `P` over the naturals.
This accounts for the oracle calls. A machine implementing the surrounding
control flow additionally needs to construct its queries and maintain its state.
-/

namespace FactorSearchClock

open BitstringEncoding

/-- The value and ordered oracle calls of a search in the interval
`[low, low + 2^k)`. -/
def run (query : ℕ × ℕ → Bool) (n : ℕ) : (k low : ℕ) → ℕ × List (ℕ × ℕ)
  | 0, low => (low, [])
  | k + 1, low =>
    let pivot := low + 2 ^ k - 1
    let next := if query (n, pivot) then low else low + 2 ^ k
    let rest := run query n k next
    (rest.1, (n, pivot) :: rest.2)

/-- Apply the guard and initial interval from the submitted reduction. -/
def search (query : ℕ × ℕ → Bool) (n : ℕ) : ℕ × List (ℕ × ℕ) :=
  if n < 2 then (2 - n, []) else run query n (n.log2 + 1) 0

private theorem run_value (query : ℕ × ℕ → Bool) (n k low : ℕ) :
    (run query n k low).1 =
      (Nat.rec (motive := fun _ => ℕ → ℕ) id
        (fun i search low =>
          if query (n, low + 2 ^ i - 1) then search low else search (low + 2 ^ i)) k) low := by
  induction k generalizing low with
  | zero => rfl
  | succ k ih =>
    simp only [run]
    split <;> apply ih

/-- Forgetting the trace gives the exact function in the third hypothesis. -/
theorem search_value (query : ℕ × ℕ → Bool) (n : ℕ) :
    (search query n).1 =
      if n < 2 then 2 - n else
        (Nat.rec (motive := fun _ => ℕ → ℕ) id
          (fun i search low =>
            if query (n, low + 2 ^ i - 1) then search low else search (low + 2 ^ i))
          (n.log2 + 1)) 0 := by
  by_cases hn : n < 2 <;> simp [search, hn, run_value]

private theorem run_queries (query : ℕ × ℕ → Bool) (n L k low : ℕ)
    (hi : low + 2 ^ k ≤ 2 ^ L) :
    (run query n k low).2.length = k ∧
    ∀ x ∈ (run query n k low).2, x.1 = n ∧ x.2 < 2 ^ L := by
  induction k generalizing low with
  | zero => simp [run]
  | succ k ih =>
    let next := if query (n, low + 2 ^ k - 1) then low else low + 2 ^ k
    rw [Nat.pow_succ] at hi
    have hp : 0 < 2 ^ k := Nat.pow_pos (by decide)
    have hnext : next + 2 ^ k ≤ 2 ^ L := by
      dsimp [next]
      split <;> omega
    obtain ⟨hc, hb⟩ := ih next hnext
    change ((n, low + 2 ^ k - 1) :: (run query n k next).2).length = k + 1 ∧ _
    constructor
    · simpa only [List.length_cons] using congrArg Nat.succ hc
    · intro x hx
      change x ∈ (n, low + 2 ^ k - 1) :: (run query n k next).2 at hx
      rcases List.mem_cons.mp hx with h | h
      · subst x
        exact ⟨rfl, by dsimp; omega⟩
      · exact hb x h

/-- The canonical binary pair format delimits its first component and appends
the bare encoding of its second component. -/
theorem pair_length (n b : ℕ) :
    (bitEncode (n, b)).length = 2 * n.size + 1 + b.size := by
  change (delimit (bitEncode n) ++ bitEncode b).length = _
  simp only [List.length_append, length_delimit, FactorEncoding.length_bitEncode_nat]

private theorem bit_length_eq_log2_succ {n : ℕ} (hn : n ≠ 0) : n.size = n.log2 + 1 := by
  have hlo := Nat.lt_size.mpr (Nat.log2_self_le hn)
  have hhi : n.size ≤ n.log2 + 1 := Nat.size_le.mpr Nat.lt_log2_self
  omega

/-- The number of calls and the size of every queried pivot and encoded pair.
Inputs zero and one issue no calls. -/
theorem search_queries (query : ℕ × ℕ → Bool) (n : ℕ) :
    (search query n).2.length = (if n < 2 then 0 else (bitEncode n).length) ∧
      ∀ x ∈ (search query n).2,
        (bitEncode x.2).length ≤ (bitEncode n).length ∧
        (bitEncode x).length ≤ 3 * (bitEncode n).length + 1 := by
  by_cases hn : n < 2
  · simp [search, hn]
  · have hL := bit_length_eq_log2_succ (by omega : n ≠ 0)
    obtain ⟨hl, hq⟩ := run_queries query n (n.log2 + 1) (n.log2 + 1) 0 (by simp)
    simp only [search, if_neg hn, FactorEncoding.length_bitEncode_nat]
    refine ⟨hl.trans hL.symm, ?_⟩
    rintro ⟨n', b⟩ hx
    obtain ⟨heq, hb⟩ := hq _ hx
    change n' = n at heq
    subst n'
    have hbits : b.size ≤ n.size := hL ▸ Nat.size_le.mpr hb
    simpa only [pair_length, FactorEncoding.length_bitEncode_nat] using
      And.intro hbits (by omega : 2 * n.size + 1 + b.size ≤ 3 * n.size + 1)

private theorem eval_monotone (P : Polynomial ℕ) : Monotone P.eval := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    intro a b h
    simpa only [Polynomial.eval_add] using Nat.add_le_add (hp h) (hq h)
  | monomial k c =>
    intro a b h
    simpa only [Polynomial.eval_monomial] using
      Nat.mul_le_mul_left c (Nat.pow_le_pow_left h k)

private theorem sum_map_le (f : α → ℕ) (xs : List α) (C : ℕ)
    (h : ∀ x ∈ xs, f x ≤ C) : (xs.map f).sum ≤ xs.length * C := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x List.mem_cons_self
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simpa only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul, Nat.add_comm C]
      using Nat.add_le_add hx ht

/-- The aggregate time budget for the actual comparator calls, with the same
bit encoding as the comparator's polynomial-time Turing machine. -/
theorem search_clock (query : ℕ × ℕ → Bool) (P : Polynomial ℕ) (n : ℕ) :
    (((search query n).2.map (fun x => P.eval (bitEncode x).length)).sum) ≤
      (bitEncode n).length * P.eval (3 * (bitEncode n).length + 1) := by
  obtain ⟨hl, hq⟩ := search_queries query n
  apply (sum_map_le _ _ _ (fun x hx => eval_monotone P (hq x hx).2)).trans
  apply Nat.mul_le_mul_right
  rw [hl]
  split <;> omega

/-- As a polynomial in the input length, the bound is `X * P(3X+1)`. -/
theorem search_clock_polynomial (query : ℕ × ℕ → Bool) (P : Polynomial ℕ) (n : ℕ) :
    (((search query n).2.map (fun x => P.eval (bitEncode x).length)).sum) ≤
      (Polynomial.X * P.comp (3 * Polynomial.X + 1)).eval (bitEncode n).length := by
  simpa using search_clock query P n

/-- Each transition count comes from the comparator machine's certified evaluation
on the actual pair sent to it. The clock bound therefore applies to the sum of
these transition counts. -/
theorem comparator_steps {query : ℕ × ℕ → Bool}
    (machine : Turing.TM2ComputableInPolyTime bitEncode bitEncode query) (n : ℕ) :
    (((search query n).2.map (fun x => (machine.outputsFun x).steps)).sum) ≤
      (Polynomial.X * machine.time.comp (3 * Polynomial.X + 1)).eval (bitEncode n).length := by
  apply le_trans _ (search_clock_polynomial query machine.time n)
  exact List.sum_le_sum fun x _ => (machine.outputsFun x).steps_le_m

end FactorSearchClock

/-!
# Building factor-search queries from bits

All words use the little-endian natural-number encoding in the factorization
conjecture. The search retains the already chosen high bits as a canonical
word. The remaining input bits serve as a counter, one bit per comparison.
-/

namespace FactorSearchBits

open Computability BitstringEncoding

/-- Extend the high prefix by a less significant digit, retaining the empty word
for zero. -/
def digit : Bool → List Bool → List Bool
  | false, [] => []
  | b, high => b :: high

/-- Each remaining bit supplies a low one in the last candidate of the lower
half. The zero immediately above these ones is significant when `high` is nonempty. -/
def pivot (remaining high : List Bool) : List Bool :=
  remaining.map (fun _ => true) ++ digit false high

/-- A raw query on the comparator's input stack. -/
def queryWord (input remaining high : List Bool) : List Bool :=
  delimit input ++ pivot remaining high

/-- Read one comparator answer per remaining bit, processing positions from
most to least significant. -/
def run (compare : List Bool → Bool) (input : List Bool) :
    List Bool → List Bool → List Bool
  | [], high => high
  | _ :: remaining, high =>
    let answer := compare (queryWord input remaining high)
    run compare input remaining (digit (!answer) high)

/-- Handle zero and one according to the search specification. For a canonical
input of length at least two, all bits contribute one comparison. -/
def search (compare : List Bool → Bool) (input : List Bool) : List Bool :=
  match input with
  | [] => [false, true]
  | [_] => [true]
  | _ :: _ :: _ => run compare input input []

/-- Extending a canonical prefix implements the binary place-value recurrence. -/
theorem digit_encode (b : Bool) (h : ℕ) :
    digit b (encodeNat h) = encodeNat (2 * h + b.toNat) := by
  have hb : 2 * h + b.toNat = Nat.bit b h := by cases b <;> simp [Nat.bit]
  change digit b (encodeNum (h : Num)) = encodeNum ((2 * h + b.toNat : ℕ) : Num)
  rw [hb, ← Num.ofNat'_eq (Nat.bit b h), Num.ofNat'_bit, Num.ofNat'_eq h]
  cases b <;> cases (h : Num) with
    | zero => rfl
    | pos p => cases p <;> rfl

private theorem leading_ones (remaining : List Bool) (x : ℕ) :
    remaining.map (fun _ => true) ++ encodeNat x =
      encodeNat ((x + 1) * 2 ^ remaining.length - 1) := by
  induction remaining with
  | nil => simp
  | cons bit rest ih =>
    change true :: (rest.map (fun _ => true) ++ encodeNat x) = _
    rw [ih]
    rw [← show digit true (encodeNat ((x + 1) * 2 ^ rest.length - 1)) =
        true :: encodeNat ((x + 1) * 2 ^ rest.length - 1) from rfl, digit_encode]
    congr 1
    have hp : 0 < (x + 1) * 2 ^ rest.length := Nat.mul_pos (by omega) (Nat.pow_pos (by decide))
    simp only [Bool.toNat_true, List.length_cons, Nat.pow_succ, ← Nat.mul_assoc]
    omega

/-- For `k` bits after the queried position, the interval starts at
`h * 2^(k+1)`, and the query asks about its lower half's upper endpoint. -/
theorem pivot_encode (remaining : List Bool) (h : ℕ) :
    pivot remaining (encodeNat h) =
      encodeNat (h * 2 ^ (remaining.length + 1) + 2 ^ remaining.length - 1) := by
  rw [pivot, digit_encode, leading_ones]
  simp only [Bool.toNat_false, Nat.add_zero, Nat.pow_succ]
  congr 2
  ring

/-- The concrete query word uses the exact paired-input encoding of H3. -/
theorem queryWord_encode (n : ℕ) (remaining : List Bool) (h : ℕ) :
    queryWord (encodeNat n) remaining (encodeNat h) =
      bitEncode (n, h * 2 ^ (remaining.length + 1) + 2 ^ remaining.length - 1) := by
  change delimit (encodeNat n) ++ pivot remaining (encodeNat h) = _
  rw [pivot_encode]
  rfl

/-- Invariant of the word search. With `k` unprocessed bits, the numeric
search interval starts at `h * 2^k`. -/
theorem run_encode (compare : List Bool → Bool) (query : ℕ × ℕ → Bool)
    (hq : ∀ x, compare (bitEncode x) = query x) (n : ℕ) (remaining : List Bool) (h : ℕ) :
    run compare (encodeNat n) remaining (encodeNat h) =
      encodeNat (FactorSearchClock.run query n remaining.length (h * 2 ^ remaining.length)).1 := by
  induction remaining generalizing h with
  | nil => simp [run, FactorSearchClock.run]
  | cons bit rest ih =>
    simp only [run, queryWord_encode, hq, List.length_cons, FactorSearchClock.run]
    cases ha : query (n, h * 2 ^ (rest.length + 1) + 2 ^ rest.length - 1) <;>
      simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, if_false, if_true,
        digit_encode, Bool.toNat_true, Bool.toNat_false, Nat.add_zero, ih]
    · congr 3
      rw [Nat.pow_succ]
      ring
    · congr 3
      rw [Nat.pow_succ]
      ring

/-- The output of the word-level algorithm is the canonical encoding of exactly
the guarded arithmetic recursion used in H3. -/
theorem search_encode (compare : List Bool → Bool) (query : ℕ × ℕ → Bool)
    (hq : ∀ x, compare (bitEncode x) = query x) (n : ℕ) :
    search compare (encodeNat n) = encodeNat
      (if n < 2 then 2 - n else
        (Nat.rec (motive := fun _ => ℕ → ℕ) id
          (fun i search low =>
            if query (n, low + 2 ^ i - 1) then search low else search (low + 2 ^ i))
          (n.log2 + 1)) 0) := by
  rw [← FactorSearchClock.search_value]
  by_cases hn : n < 2
  · rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl <;>
      simp only [FactorSearchClock.search, if_pos hn] <;> rfl
  · have hlen : (encodeNat n).length = n.log2 + 1 := by
      change (bitEncode n).length = _
      rw [FactorEncoding.length_bitEncode_nat]
      have hlo := Nat.lt_size.mpr (Nat.log2_self_le (by omega : n ≠ 0))
      have hhi : n.size ≤ n.log2 + 1 := Nat.size_le.mpr Nat.lt_log2_self
      omega
    have hlength : 2 ≤ (encodeNat n).length := by
      have := (Nat.le_log2 (by omega : n ≠ 0)).mpr (by omega : 2 ^ 1 ≤ n)
      omega
    have hstart : search compare (encodeNat n) = run compare (encodeNat n) (encodeNat n) [] := by
      cases hword : encodeNat n with
      | nil => simp [hword] at hlength
      | cons b rest =>
        cases rest <;> simp_all [search]
    rw [hstart, ← show encodeNat 0 = [] from rfl, run_encode compare query hq, hlen]
    simp [FactorSearchClock.search, hn]

end FactorSearchBits

/-! Run a TM2 statement on selected stacks of a larger machine, leaving the other stacks
unchanged. Halting may transfer control to a specified continuation label. -/

namespace FactorMachineLift

open Turing.TM2

variable {K J Λ Λ' σ σ' : Type} {Γ : K → Type} {Γ' : J → Type}

/-- The stack/symbol embedding and register operations for a machine inside a caller. -/
structure Lift (Γ : K → Type) (Γ' : J → Type) (Λ Λ' σ σ' : Type) where
  stack : K ↪ J
  symbol : ∀ k, Γ k ≃ Γ' (stack k)
  label : Λ → Λ'
  exitLabel : Option Λ'
  read : σ' → σ
  write : σ' → σ → σ'
  read_write : ∀ w v, read (write w v) = v
  write_write : ∀ w v u, write (write w v) u = write w u

namespace Lift

variable (e : Lift Γ Γ' Λ Λ' σ σ')

def mapLabel : Option Λ → Option Λ'
  | none => e.exitLabel
  | some l => some (e.label l)

/-- Translate operations on the callee's stacks, registers and control labels. -/
def stmt : Stmt Γ Λ σ → Stmt Γ' Λ' σ'
  | .push k f q => .push (e.stack k) (fun w => e.symbol k (f (e.read w))) (stmt q)
  | .peek k f q => .peek (e.stack k)
      (fun w a => e.write w (f (e.read w) (a.map (e.symbol k).symm))) (stmt q)
  | .pop k f q => .pop (e.stack k)
      (fun w a => e.write w (f (e.read w) (a.map (e.symbol k).symm))) (stmt q)
  | .load f q => .load (fun w => e.write w (f (e.read w))) (stmt q)
  | .branch f qt qf => .branch (fun w => f (e.read w)) (stmt qt) (stmt qf)
  | .goto f => .goto (fun w => e.label (f (e.read w)))
  | .halt => match e.exitLabel with
    | none => .halt
    | some l => .goto (fun _ => l)

/-- The selected stacks encode the callee's stacks and every other stack retains its
contents from the start of the call. -/
structure StacksMatch (frozen : ∀ j, List (Γ' j))
    (s : ∀ k, List (Γ k)) (t : ∀ j, List (Γ' j)) : Prop where
  inside : ∀ k, t (e.stack k) = (s k).map (e.symbol k)
  outside : ∀ j, (∀ k, e.stack k ≠ j) → t j = frozen j

structure Matches (base : σ') (frozen : ∀ j, List (Γ' j))
    (c : Cfg Γ Λ σ) (C : Cfg Γ' Λ' σ') : Prop where
  label_eq : C.l = e.mapLabel c.l
  state_eq : C.var = e.write base c.var
  stack_eq : e.StacksMatch frozen c.stk C.stk

variable [DecidableEq K] [DecidableEq J]

theorem StacksMatch.update {frozen s t} (h : e.StacksMatch frozen s t)
    (k : K) (xs : List (Γ k)) :
    e.StacksMatch frozen (Function.update s k xs)
      (Function.update t (e.stack k) (xs.map (e.symbol k))) := by
  constructor
  · intro i
    by_cases hi : i = k
    · subst i
      simp
    · have hkey : e.stack i ≠ e.stack k := fun a => hi (e.stack.injective a)
      simpa [Function.update_of_ne hi, Function.update_of_ne hkey] using h.inside i
  · intro j hj
    have hkey : j ≠ e.stack k := (hj k).symm
    simpa [Function.update_of_ne hkey] using h.outside j hj

private theorem decode_head {α β : Type} (h : α ≃ β) (xs : List α) :
    ((xs.map h).head?).map h.symm = xs.head? := by
  cases xs <;> simp

/-- A source statement and its translation take exactly one step, including every nested
stack primitive before the next goto or halt. -/
theorem stepAux_stmt (q : Stmt Γ Λ σ) (base : σ') (frozen : ∀ j, List (Γ' j))
    (v : σ) (s : ∀ k, List (Γ k)) (t : ∀ j, List (Γ' j))
    (h : e.StacksMatch frozen s t) :
    e.Matches base frozen (stepAux q v s) (stepAux (e.stmt q) (e.write base v) t) := by
  induction q generalizing v s t with
  | push k f q ih =>
    simp only [stmt, stepAux, e.read_write, h.inside k]
    exact ih _ _ _ (h.update e k (f v :: s k))
  | peek k f q ih =>
    simp only [stmt, stepAux, e.read_write, e.write_write, h.inside k, decode_head]
    exact ih _ _ _ h
  | pop k f q ih =>
    simp only [stmt, stepAux, e.read_write, e.write_write, h.inside k, decode_head]
    simpa using ih _ _ _ (h.update e k (s k).tail)
  | load f q ih =>
    simp only [stmt, stepAux, e.read_write, e.write_write]
    exact ih _ _ _ h
  | branch f qt qf iht ihf =>
    simp only [stmt, stepAux, e.read_write]
    cases f v
    · exact ihf _ _ _ h
    · exact iht _ _ _ h
  | goto f =>
    exact ⟨by simp [stmt, stepAux, mapLabel, e.read_write], rfl, h⟩
  | halt =>
    cases hx : e.exitLabel with
    | none => exact ⟨by simp [stmt, stepAux, mapLabel, hx], by simp [stmt, stepAux, hx],
                       by simpa [stmt, stepAux, hx] using h⟩
    | some l => exact ⟨by simp [stmt, stepAux, mapLabel, hx], by simp [stmt, stepAux, hx],
                         by simpa [stmt, stepAux, hx] using h⟩

omit [DecidableEq K] [DecidableEq J] in
/-- The callee configuration, caller register base and untouched stacks determine the host. -/
theorem Matches.unique {base frozen c C D}
    (hc : e.Matches base frozen c C) (hd : e.Matches base frozen c D) : C = D := by
  have hl := hc.label_eq.trans hd.label_eq.symm
  have hv := hc.state_eq.trans hd.state_eq.symm
  have hs : C.stk = D.stk := by
    funext j
    by_cases hj : ∃ k, e.stack k = j
    · obtain ⟨k, rfl⟩ := hj
      exact (hc.stack_eq.inside k).trans (hd.stack_eq.inside k).symm
    · have hout : ∀ k, e.stack k ≠ j := fun k hk => hj ⟨k, hk⟩
      exact (hc.stack_eq.outside j hout).trans (hd.stack_eq.outside j hout).symm
  cases C
  cases D
  congr

variable {p : Λ → Stmt Γ Λ σ} {P : Λ' → Stmt Γ' Λ' σ'}

/-- A live transition produces an agreeing host configuration. The rest of the host
program, including the continuation's code, is unrestricted. -/
theorem step_matches (hprog : ∀ l, P (e.label l) = e.stmt (p l))
    {base frozen c d C} (hc : e.Matches base frozen c C) (hs : step p c = some d) :
    ∃ D, step P C = some D ∧ e.Matches base frozen d D := by
  cases c with
  | mk l v s =>
    cases l with
    | none => simp [step] at hs
    | some l =>
      cases C with
      | mk L V S =>
        have hL : L = some (e.label l) := hc.label_eq
        have hV : V = e.write base v := hc.state_eq
        subst L
        subst V
        have hd : stepAux (p l) v s = d := Option.some.inj hs
        subst d
        exact ⟨_, by simp [step, hprog], e.stepAux_stmt _ _ _ _ _ _ hc.stack_eq⟩

/-- Transfer an exact number of live transitions. An embedded halt may be a live
continuation label, so the statement ends on the same step as the callee. -/
theorem iterate_matches (hprog : ∀ l, P (e.label l) = e.stmt (p l))
    (n : ℕ) {base frozen c d C} (hc : e.Matches base frozen c C)
    (hs : (flip bind (step p))^[n] (some c) = some d) :
    ∃ D, (flip bind (step P))^[n] (some C) = some D ∧ e.Matches base frozen d D := by
  induction n generalizing c C with
  | zero =>
    have hd : c = d := Option.some.inj hs
    subst d
    exact ⟨C, rfl, hc⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply] at hs ⊢
    change (flip bind (step p))^[n] (step p c) = some d at hs
    cases hnext : step p c with
    | none =>
      rw [hnext, Function.iterate_fixed (f := flip bind (step p)) (x := none) rfl n] at hs
      cases hs
    | some cnext =>
      obtain ⟨Cnext, hCnext, hmatch⟩ := e.step_matches hprog hc hnext
      obtain ⟨D, hsteps, hD⟩ := ih hmatch (hnext ▸ hs)
      exact ⟨D, by change (flip bind (step P))^[n] (step P C) = some D; rwa [hCnext], hD⟩

/-- Lift a time-bounded execution to named host configurations. Its step count is unchanged. -/
def evalsToInTime (hprog : ∀ l, P (e.label l) = e.stmt (p l))
    {base frozen c d C D budget} (hc : e.Matches base frozen c C)
    (hd : e.Matches base frozen d D)
    (run : StateTransition.EvalsToInTime (step p) c (some d) budget) :
    StateTransition.EvalsToInTime (step P) C (some D) budget where
  steps := run.steps
  steps_le_m := run.steps_le_m
  evals_in_steps := by
    obtain ⟨actual, ha, hactual⟩ := e.iterate_matches hprog run.steps hc run.evals_in_steps
    simpa only [hactual.unique e hd] using ha

end Lift

end FactorMachineLift

/-! Compilation of finite-stack programs making calls to a Boolean-valued TM2 machine. -/

namespace FactorOracleMachine

open Turing FactorMachineLift StateTransition

structure OracleProgram where
  K : Type
  [kDec : DecidableEq K]
  [kFin : Fintype K]
  Λ : Type
  [lDec : DecidableEq Λ]
  [lFin : Fintype Λ]
  σ : Type
  [sFin : Fintype σ]
  k₀ : K
  k₁ : K
  arg : K
  main : Λ
  call : Λ
  resume : Λ
  initialState : σ
  m : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ

instance (C : OracleProgram) : DecidableEq C.K := C.kDec
instance (C : OracleProgram) : Fintype C.K := C.kFin
instance (C : OracleProgram) : DecidableEq C.Λ := C.lDec
instance (C : OracleProgram) : Fintype C.Λ := C.lFin
instance (C : OracleProgram) : Fintype C.σ := C.sFin

namespace OracleProgram

variable (C : OracleProgram)

abbrev Cfg := TM2.Cfg (fun _ : C.K => Bool) C.Λ C.σ

def tm : FinTM2 where
  K := C.K
  Γ _ := Bool
  Λ := C.Λ
  σ := C.σ
  k₀ := C.k₀
  k₁ := C.k₁
  main := C.main
  initialState := C.initialState
  m := C.m

/-- An atomic call can be used only with a validly encoded argument. -/
inductive Run {A : Type} (encode : A → List Bool) (query : A → Bool) (cost : ℕ → ℕ) :
    C.Cfg → C.Cfg → ℕ → Prop
  | refl (c) : Run encode query cost c c 0
  | normal {c d} (hc : c.l ≠ some C.call) (hs : TM2.step C.m c = some d) : Run encode query cost c d 1
  | oracle (x : A) (v : C.σ) (s : C.K → List Bool) (h : s C.arg = encode x) :
      Run encode query cost ⟨some C.call, v, s⟩
        ⟨some C.resume, v, Function.update s C.arg [query x]⟩
        (cost (encode x).length + 2 * (encode x).length + 4)
  | trans {a b c t u} : Run encode query cost a b t → Run encode query cost b c u →
      Run encode query cost a c (t + u)
  | mono {a b t u} : Run encode query cost a b t → t ≤ u → Run encode query cost a b u

inductive Phase | reverse | transfer | finish deriving DecidableEq
instance : Fintype Phase := ⟨{.reverse, .transfer, .finish}, by intro p; cases p <;> simp⟩

variable (Q : FinTM2) (ei : Q.Γ Q.k₀ ≃ Bool) (eo : Q.Γ Q.k₁ ≃ Bool)

abbrev Index := C.K ⊕ (Q.K ⊕ Unit)
abbrev Label := C.Λ ⊕ (Q.Λ ⊕ Phase)
abbrev Register := C.σ × Q.σ × Option Bool
abbrev Alphabet : C.Index Q → Type := Sum.elim (fun _ => Bool) (Sum.elim Q.Γ (fun _ => Bool))
abbrev HostCfg := TM2.Cfg (C.Alphabet Q) (C.Label Q) (C.Register Q)

def caller : Lift (fun _ : C.K => Bool) (C.Alphabet Q) C.Λ (C.Label Q) C.σ (C.Register Q) where
  stack := ⟨Sum.inl, Sum.inl_injective⟩
  symbol _ := Equiv.refl _
  label := Sum.inl
  exitLabel := none
  read := Prod.fst
  write w v := (v, w.2)
  read_write _ _ := rfl
  write_write _ _ _ := rfl

def callee : Lift Q.Γ (C.Alphabet Q) Q.Λ (C.Label Q) Q.σ (C.Register Q) where
  stack := ⟨fun k => .inr (.inl k), fun _ _ h => Sum.inl.inj (Sum.inr.inj h)⟩
  symbol _ := Equiv.refl _
  label l := .inr (.inl l)
  exitLabel := some (.inr (.inr .finish))
  read v := v.2.1
  write w v := (w.1, v, w.2.2)
  read_write _ _ := rfl
  write_write _ _ _ := rfl

def program : C.Label Q → TM2.Stmt (C.Alphabet Q) (C.Label Q) (C.Register Q)
  | .inl l => if l = C.call then .goto (fun _ => .inr (.inr .reverse)) else (C.caller Q).stmt (C.m l)
  | .inr (.inl l) => (C.callee Q).stmt (Q.m l)
  | .inr (.inr .reverse) =>
      .pop (.inl C.arg) (fun w o => (w.1, w.2.1, o))
        (.branch (fun w => w.2.2.isSome)
          (.push (.inr (.inr ())) (fun w => w.2.2.getD false) (.goto fun _ => .inr (.inr .reverse)))
          (.goto fun _ => .inr (.inr .transfer)))
  | .inr (.inr .transfer) =>
      .pop (.inr (.inr ())) (fun w o => (w.1, w.2.1, o))
        (.branch (fun w => w.2.2.isSome)
          (.push (.inr (.inl Q.k₀)) (fun w => ei.symm (w.2.2.getD false)) (.goto fun _ => .inr (.inr .transfer)))
          (.goto fun _ => .inr (.inl Q.main)))
  | .inr (.inr .finish) =>
      .pop (.inr (.inl Q.k₁)) (fun w o => (w.1, w.2.1, o.map eo))
        (.push (.inl C.arg) (fun w => w.2.2.getD false)
          (.load (fun w => (w.1, w.2.1, none)) (.goto fun _ => .inl C.resume)))

def compiled : FinTM2 :=
  letI := Q.kFin
  letI := Q.ΛFin
  letI := Q.σFin
  { K := C.Index Q
    Γ := C.Alphabet Q
    Λ := C.Label Q
    σ := C.Register Q
    k₀ := .inl C.k₀
    k₁ := .inl C.k₁
    Γk₀Fin := inferInstanceAs (Fintype Bool)
    main := .inl C.main
    initialState := (C.initialState, Q.initialState, none)
    m := C.program Q ei eo }

def tapes (s : C.K → List Bool) (t : ∀ k, List (Q.Γ k)) (b : List Bool) :
    ∀ j, List (C.Alphabet Q j)
  | .inl k => s k
  | .inr (.inl k) => t k
  | .inr (.inr _) => b

def embed (c : C.Cfg) : C.HostCfg Q :=
  ⟨c.l.map Sum.inl, (c.var, Q.initialState, none), C.tapes Q c.stk (fun _ => []) []⟩

private abbrev Stores := ∀ k, List (Q.Γ k)

@[simp] private theorem tapes_c (s t b k) : C.tapes Q s t b (.inl k) = s k := rfl
@[simp] private theorem tapes_q (s t b k) : C.tapes Q s t b (.inr (.inl k)) = t k := rfl
@[simp] private theorem tapes_b (s t b) : C.tapes Q s t b (.inr (.inr ())) = b := rfl

@[simp] private theorem update_c (s t b k) (xs : List Bool) :
    Function.update (C.tapes Q s t b) (.inl k) xs = C.tapes Q (Function.update s k xs) t b := by
  funext j
  rcases j with i | i | u
  · by_cases h : i = k
    · subst i; simp [Function.update, tapes]
    · simp [Function.update, tapes, h]
  · simp [Function.update, tapes]
  · cases u; simp [Function.update, tapes]

@[simp] private theorem update_q (s t b k) (xs : List (Q.Γ k)) :
    Function.update (C.tapes Q s t b) (.inr (.inl k)) xs = C.tapes Q s (Function.update t k xs) b := by
  funext j
  rcases j with i | i | u
  · simp [Function.update, tapes]
  · by_cases h : i = k
    · subst i; simp [Function.update, tapes]
    · simp [Function.update, tapes, h]
  · cases u; simp [Function.update, tapes]

@[simp] private theorem update_b (s t b) (xs : List Bool) :
    Function.update (C.tapes Q s t b) (.inr (.inr ())) xs = C.tapes Q s t xs := by
  funext j
  rcases j with i | i | u
  · simp [Function.update, tapes]
  · simp [Function.update, tapes]
  · cases u; simp [Function.update, tapes]

private def oneStack {K : Type} [DecidableEq K] (Γ : K → Type) (k : K) (xs : List (Γ k)) :
    ∀ j, List (Γ j) := Function.update (fun j => ([] : List (Γ j))) k xs

private def stage (l : C.Label Q) (v : C.σ) (o : Option Bool) (s : C.K → List Bool)
    (t : Stores Q) (b : List Bool) : C.HostCfg Q :=
  ⟨some l, (v, Q.initialState, o), C.tapes Q s t b⟩

private def Exact (a b : C.HostCfg Q) (t : ℕ) : Prop :=
  (flip bind (TM2.step (C.program Q ei eo)))^[t] (some a) = some b

private theorem next {a b d t} (ab : TM2.step (C.program Q ei eo) a = some b)
    (bd : C.Exact Q ei eo b d t) : C.Exact Q ei eo a d (t+1) := by
  unfold Exact at *
  rw [Function.iterate_succ_apply]
  change (flip bind (TM2.step (C.program Q ei eo)))^[t] (TM2.step (C.program Q ei eo) a) = some d
  rwa [ab]

private theorem one {a b} (ab : TM2.step (C.program Q ei eo) a = some b) : C.Exact Q ei eo a b 1 := ab

private theorem join {a b d t u} (ab : C.Exact Q ei eo a b t) (bd : C.Exact Q ei eo b d u) :
    C.Exact Q ei eo a d (u+t) := by
  unfold Exact at *
  rw [Function.iterate_add_apply, ab, bd]

private theorem reverse_run (v : C.σ) (s : C.K → List Bool) (xs bs : List Bool) (o : Option Bool) :
    C.Exact Q ei eo
      (C.stage Q (.inr (.inr .reverse)) v o (Function.update s C.arg xs) (fun _ => []) bs)
      (C.stage Q (.inr (.inr .transfer)) v none (Function.update s C.arg []) (fun _ => []) (xs.reverse ++ bs))
      (xs.length+1) := by
  induction xs generalizing bs o with
  | nil => apply C.one; simp [stage, program, TM2.stepAux]
  | cons a xs ih =>
    simpa only [List.length_cons, List.reverse_cons, List.append_assoc, List.singleton_append] using
      (C.next Q ei eo (a := C.stage Q (.inr (.inr .reverse)) v o (Function.update s C.arg (a::xs)) (fun _ => []) bs)
        (by simp [stage, program, TM2.stepAux]) (ih (a::bs) (some a)))

private theorem transfer_run (v : C.σ) (s : C.K → List Bool) (bs : List Bool)
    (xs : List (Q.Γ Q.k₀)) (o : Option Bool) :
    C.Exact Q ei eo
      (C.stage Q (.inr (.inr .transfer)) v o s (oneStack Q.Γ Q.k₀ xs) bs)
      (C.stage Q (.inr (.inl Q.main)) v none s (oneStack Q.Γ Q.k₀ (bs.reverse.map ei.symm ++ xs)) [])
      (bs.length+1) := by
  induction bs generalizing xs o with
  | nil => apply C.one; simp [stage, program, TM2.stepAux]
  | cons a bs ih =>
    simpa only [List.length_cons, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc, List.singleton_append] using
      (C.next Q ei eo (a := C.stage Q (.inr (.inr .transfer)) v o s (oneStack Q.Γ Q.k₀ xs) (a::bs))
        (by simp [stage, program, TM2.stepAux, oneStack]) (ih (ei.symm a::xs) (some a)))

private theorem caller_match (c : C.Cfg) : (C.caller Q).Matches
    (C.initialState, Q.initialState, none) (fun _ => []) c (C.embed Q c) := by
  refine ⟨?_, rfl, ⟨?_, ?_⟩⟩
  · change c.l.map Sum.inl = (C.caller Q).mapLabel c.l
    cases c.l <;> rfl
  · intro k
    change c.stk k = (c.stk k).map id
    simp
  · rintro (k | k | u) h
    · exact False.elim (h k rfl)
    · rfl
    · cases u; rfl

private theorem ordinary_run {c d : C.Cfg} (hc : c.l ≠ some C.call) (hs : TM2.step C.m c = some d) :
    C.Exact Q ei eo (C.embed Q c) (C.embed Q d) 1 := by
  rcases c with ⟨_ | l, v, s⟩
  · contradiction
  · have hl : l ≠ C.call := fun h => hc (congrArg some h)
    have hd : TM2.stepAux (C.m l) v s = d := Option.some.inj hs
    subst d
    have hmatch := (C.caller Q).stepAux_stmt (C.m l) (C.initialState, Q.initialState, none)
      (fun _ => []) v s (C.tapes Q s (fun _ => []) []) (C.caller_match Q ⟨some l, v, s⟩).stack_eq
    apply C.one
    change some (TM2.stepAux (C.program Q ei eo (.inl l)) _ _) = _
    rw [show C.program Q ei eo (.inl l) = (C.caller Q).stmt (C.m l) by simp [program, hl]]
    exact congrArg some (hmatch.unique _ (C.caller_match Q _))

private def embedQuery (v : C.σ) (s : C.K → List Bool) (d : Q.Cfg) : C.HostCfg Q :=
  ⟨(C.callee Q).mapLabel d.l, (v, d.var, none), C.tapes Q s d.stk []⟩

private theorem callee_match (v : C.σ) (s : C.K → List Bool) (d : Q.Cfg) :
    (C.callee Q).Matches (v, Q.initialState, none) (C.tapes Q s (fun _ => []) []) d (C.embedQuery Q v s d) := by
  refine ⟨rfl, rfl, ⟨?_, ?_⟩⟩
  · intro k
    change d.stk k = (d.stk k).map id
    simp
  · rintro (k | k | u) h
    · rfl
    · exact False.elim (h k rfl)
    · cases u; rfl

private theorem init_tapes (T : FinTM2) (xs : List (T.Γ T.k₀)) :
    (initList T xs).stk = oneStack T.Γ T.k₀ xs := by
  funext j
  by_cases h : j = T.k₀
  · subst j; simp [initList, oneStack, Function.update]
  · simp [initList, oneStack, Function.update, h]

private theorem halt_tapes (T : FinTM2) (xs : List (T.Γ T.k₁)) :
    (haltList T xs).stk = oneStack T.Γ T.k₁ xs := by
  funext j
  by_cases h : j = T.k₁
  · subst j; simp [haltList, oneStack, Function.update]
  · simp [haltList, oneStack, Function.update, h]

private theorem nil_stack {K : Type} [DecidableEq K] (Γ : K → Type) (k : K) :
    oneStack Γ k [] = (fun _ => []) := by
  funext j
  by_cases h : j = k
  · subst j; simp [oneStack]
  · simp [oneStack, h]

private theorem start_call (v : C.σ) (s : C.K → List Bool) (w : List Bool) (harg : s C.arg = w) :
    C.Exact Q ei eo (C.embed Q ⟨some C.call, v, s⟩)
      (C.embedQuery Q v (Function.update s C.arg []) (initList Q (w.map ei.symm))) (2 * w.length + 3) := by
  have hrev := C.reverse_run Q ei eo v s w [] none
  have htrans := C.transfer_run Q ei eo v (Function.update s C.arg []) w.reverse [] none
  have hstart : Function.update s C.arg w = s := by rw [← harg]; exact Function.update_eq_self _ _
  rw [hstart, List.append_nil] at hrev
  rw [List.reverse_reverse, List.append_nil, nil_stack, List.length_reverse] at htrans
  have henter := C.one Q ei eo (a := C.embed Q ⟨some C.call, v, s⟩)
    (b := C.stage Q (.inr (.inr .reverse)) v none s (fun _ => []) []) (by simp [embed, stage, program, TM2.stepAux])
  have hs := C.join Q ei eo (C.join Q ei eo henter hrev) htrans
  convert hs using 1
  · unfold embedQuery stage
    rw [init_tapes]
    rfl
  · omega

private theorem finish_call (v : C.σ) (s : C.K → List Bool) (r : Bool) :
    C.Exact Q ei eo
      (C.embedQuery Q v (Function.update s C.arg []) (haltList Q [eo.symm r]))
      (C.embed Q ⟨some C.resume, v, Function.update s C.arg [r]⟩) 1 := by
  apply C.one
  unfold embedQuery embed
  rw [halt_tapes]
  change some (TM2.stepAux (C.program Q ei eo (.inr (.inr .finish)))
    (v, Q.initialState, none)
    (C.tapes Q (Function.update s C.arg []) (oneStack Q.Γ Q.k₁ [eo.symm r]) [])) = _
  simp [program, TM2.stepAux, oneStack]

private theorem call_run (v : C.σ) (s : C.K → List Bool) (w : List Bool) (r : Bool) (t : ℕ)
    (harg : s C.arg = w) (oracleRun : TM2OutputsInTime Q (w.map ei.symm) (some [eo.symm r]) t) :
    ∃ k ≤ t + 2*w.length + 4, C.Exact Q ei eo (C.embed Q ⟨some C.call, v, s⟩)
      (C.embed Q ⟨some C.resume, v, Function.update s C.arg [r]⟩) k := by
  let cleared := Function.update s C.arg []
  let middle := (C.callee Q).evalsToInTime (p := Q.m) (P := C.program Q ei eo) (fun _ => rfl)
    (C.callee_match Q v cleared (initList Q (w.map ei.symm)))
    (C.callee_match Q v cleared (haltList Q [eo.symm r])) oracleRun
  have hmiddle : C.Exact Q ei eo (C.embedQuery Q v cleared (initList Q (w.map ei.symm)))
      (C.embedQuery Q v cleared (haltList Q [eo.symm r])) middle.steps := middle.evals_in_steps
  have h := C.join Q ei eo (C.join Q ei eo (C.start_call Q ei eo v s w harg) hmiddle) (C.finish_call Q ei eo v s r)
  exact ⟨_, by have := middle.steps_le_m; omega, h⟩

private theorem simulate {A : Type} {encode : A → List Bool} {query : A → Bool} {cost : ℕ → ℕ}
    (oracleRun : ∀ x, TM2OutputsInTime Q ((encode x).map ei.symm) (some [eo.symm (query x)]) (cost (encode x).length))
    {a b : C.Cfg} {t : ℕ} (run : C.Run encode query cost a b t) :
    ∃ k ≤ t, C.Exact Q ei eo (C.embed Q a) (C.embed Q b) k := by
  induction run with
  | refl a => exact ⟨0, Nat.le_refl _, rfl⟩
  | normal hc hs => exact ⟨1, Nat.le_refl _, C.ordinary_run Q ei eo hc hs⟩
  | oracle x v s h => exact C.call_run Q ei eo v s _ _ _ h (oracleRun x)
  | trans _ _ ih ih' =>
    obtain ⟨k, hk, h⟩ := ih
    obtain ⟨j, hj, h'⟩ := ih'
    exact ⟨j+k, by omega, C.join Q ei eo h h'⟩
  | mono _ hle ih =>
    obtain ⟨k, hk, h⟩ := ih
    exact ⟨k, hk.trans hle, h⟩

private theorem singleCaller (k : C.K) (xs : List Bool) :
    C.tapes Q (oneStack (fun _ : C.K => Bool) k xs) (fun _ => []) [] =
      oneStack (C.Alphabet Q) (.inl k) xs := by
  have empty : C.tapes Q (fun _ => []) (fun _ => []) [] = (fun _ => []) := by
    funext j
    rcases j with i | i | u <;> rfl
  unfold oneStack
  rw [← update_c, empty]

private theorem embed_init (xs : List Bool) : C.embed Q (initList C.tm xs) =
    initList (C.compiled Q ei eo) xs := by
  apply congrArg (fun s => (⟨some (.inl C.main), (C.initialState, Q.initialState, none), s⟩ : C.HostCfg Q))
  change C.tapes Q (initList C.tm xs).stk (fun _ => []) [] = (initList (C.compiled Q ei eo) xs).stk
  exact (congrArg (fun s => C.tapes Q s (fun _ => []) []) (init_tapes C.tm xs)).trans
    ((C.singleCaller Q C.k₀ xs).trans (init_tapes (C.compiled Q ei eo) xs).symm)

private theorem embed_halt (xs : List Bool) : C.embed Q (haltList C.tm xs) =
    haltList (C.compiled Q ei eo) xs := by
  apply congrArg (fun s => (⟨none, (C.initialState, Q.initialState, none), s⟩ : C.HostCfg Q))
  change C.tapes Q (haltList C.tm xs).stk (fun _ => []) [] = (haltList (C.compiled Q ei eo) xs).stk
  exact (congrArg (fun s => C.tapes Q s (fun _ => []) []) (halt_tapes C.tm xs)).trans
    ((C.singleCaller Q C.k₁ xs).trans (halt_tapes (C.compiled Q ei eo) xs).symm)

/-- Any valid time-budgeted oracle program executes on a standard finite TM2 machine.
The caller's workspace survives every call and all callee workspace is cleared before resuming. -/
theorem compile_run {A : Type} {encode : A → List Bool} {query : A → Bool} {cost : ℕ → ℕ}
    (oracleRun : ∀ x, TM2OutputsInTime Q ((encode x).map ei.symm) (some [eo.symm (query x)]) (cost (encode x).length))
    {input output : List Bool} {t : ℕ}
    (run : C.Run encode query cost (initList C.tm input) (haltList C.tm output) t) :
    Nonempty (TM2OutputsInTime (C.compiled Q ei eo) input (some output) t) := by
  obtain ⟨k, hk, h⟩ := C.simulate Q ei eo oracleRun run
  unfold Exact at h
  rw [embed_init C Q ei eo, embed_halt C Q ei eo] at h
  exact ⟨⟨⟨k, h⟩, hk⟩⟩

end OracleProgram
end FactorOracleMachine

/-! A clocked finite-stack caller with a Boolean-valued polynomial-time subroutine
is itself a polynomial-time function on the canonical input and output encodings. -/

namespace FactorOraclePolytime

open FactorOracleMachine Turing ComplexityTheory BitstringEncoding

variable {A X Y : Type} [BitstringEncoding A] [BitstringEncoding X] [BitstringEncoding Y]
variable {query : A → Bool} {f : X → Y}

/-- Package a concrete comparator and a proof of the caller's clock into the
polynomial-time witness used in the factorization conjecture. -/
theorem of_machine (C : OracleProgram)
    (Q : TM2ComputableInPolyTime bitEncode bitEncode query) (budget : Polynomial ℕ)
    (run : ∀ x, C.Run bitEncode query Q.time.eval (initList C.tm (bitEncode x))
      (haltList C.tm (bitEncode (f x))) (budget.eval (bitEncode x).length)) :
    IsPolyTime f := by
  have reply (a : A) : TM2OutputsInTime Q.tm ((bitEncode a).map Q.inputAlphabet.symm)
      (some [Q.outputAlphabet.symm (query a)]) (Q.time.eval (bitEncode a).length) :=
    Q.outputsFun a
  refine ⟨{ tm := C.compiled Q.tm Q.inputAlphabet Q.outputAlphabet
            inputAlphabet := Equiv.refl Bool
            outputAlphabet := Equiv.refl Bool
            time := budget
            outputsFun := fun x => ?_ }⟩
  let result := Classical.choice
    (C.compile_run Q.tm Q.inputAlphabet Q.outputAlphabet reply (run x))
  change TM2OutputsInTime (C.compiled Q.tm Q.inputAlphabet Q.outputAlphabet) ((bitEncode x).map id)
    (some ((bitEncode (f x)).map id)) (budget.eval (bitEncode x).length)
  erw [List.map_id, List.map_id]
  exact result

/-- A clock transformation may depend on the comparator's polynomial. -/
theorem of_query (C : OracleProgram) (hq : IsPolyTime query)
    (budget : Polynomial ℕ → Polynomial ℕ)
    (run : ∀ (Q : TM2ComputableInPolyTime bitEncode bitEncode query) x,
      C.Run bitEncode query Q.time.eval (initList C.tm (bitEncode x))
        (haltList C.tm (bitEncode (f x))) ((budget Q.time).eval (bitEncode x).length)) :
    IsPolyTime f := by
  obtain ⟨Q⟩ := hq
  exact of_machine C Q (budget Q.time) (run Q)

end FactorOraclePolytime

/-! Finite-stack controller for the bounded binary search. The oracle replaces the
input/output stack with one Boolean and resumes the controller at a fixed label. -/

namespace FactorSearchController

open Turing.TM2

inductive Stack
  | io | inputRev | fuel | high | scratch
  deriving DecidableEq

inductive Label
  | start | checkSecond | saveInput | round | saveHigh | restoreHigh | writeOnes
  | restoreFuel | writeInput | restoreInput | ask | resume | finishHigh | finishOut | clearInput
  deriving DecidableEq

instance : Fintype Stack := Fintype.ofList [.io, .inputRev, .fuel, .high, .scratch]
  (by intro k; cases k <;> decide)

instance : Fintype Label := Fintype.ofList
  [.start, .checkSecond, .saveInput, .round, .saveHigh, .restoreHigh, .writeOnes,
   .restoreFuel, .writeInput, .restoreInput, .ask, .resume, .finishHigh, .finishOut, .clearInput]
  (by intro l; cases l <;> decide)

abbrev Code := Stmt (fun _ : Stack => Bool) Label (Option Bool)
abbrev Config := Cfg (fun _ : Stack => Bool) Label (Option Bool)

private def jump (l : Label) : Code := .load (fun _ => none) (.goto (fun _ => l))
private def stop : Code := .load (fun _ => none) .halt
private def putBit (k : Stack) (b : Bool) (q : Code) : Code := .push k (fun _ => b) q
private def putRead (k : Stack) (q : Code) : Code := .push k (fun s => s.getD false) q
private def take (k : Stack) (item empty : Code) : Code :=
  .pop k (fun _ b => b) (.branch Option.isSome item empty)
private def look (k : Stack) (item empty : Code) : Code :=
  .peek k (fun _ b => b) (.branch Option.isSome item empty)

/-- Each transfer executes one pop and a constant number of pushes per source bit. -/
def program : Label → Code
  | .start => take .io (putRead .inputRev (putRead .fuel (jump .checkSecond)))
      (putBit .io true (putBit .io false stop))
  | .checkSecond => look .io (jump .saveInput)
      (.pop .inputRev (fun s _ => s) (.pop .fuel (fun s _ => s) (putBit .io true stop)))
  | .saveInput => take .io (putRead .inputRev (putRead .fuel (jump .saveInput))) (jump .round)
  | .round => take .fuel (jump .saveHigh) (jump .finishHigh)
  | .saveHigh => take .high (putRead .scratch (jump .saveHigh)) (jump .restoreHigh)
  | .restoreHigh => take .scratch (putRead .high (putRead .io (jump .restoreHigh)))
      (look .high (putBit .io false (jump .writeOnes)) (jump .writeOnes))
  | .writeOnes => take .fuel (putRead .scratch (putBit .io true (jump .writeOnes)))
      (jump .restoreFuel)
  | .restoreFuel => take .scratch (putRead .fuel (jump .restoreFuel))
      (putBit .io false (jump .writeInput))
  | .writeInput => take .inputRev (putRead .scratch (putRead .io (putBit .io true (jump .writeInput))))
      (jump .restoreInput)
  | .restoreInput => take .scratch (putRead .inputRev (jump .restoreInput)) (jump .ask)
  | .ask => .halt
  | .resume => take .io
      (.branch (fun s => s.getD false)
        (look .high (putBit .high false (jump .round)) (jump .round))
        (putBit .high true (jump .round))) (jump .round)
  | .finishHigh => take .high (putRead .scratch (jump .finishHigh)) (jump .finishOut)
  | .finishOut => take .scratch (putRead .io (jump .finishOut)) (jump .clearInput)
  | .clearInput => take .inputRev (jump .clearInput) stop

def words (io inputRev fuel high scratch : List Bool) : Stack → List Bool
  | .io => io
  | .inputRev => inputRev
  | .fuel => fuel
  | .high => high
  | .scratch => scratch

def cfg (l : Option Label) (io inputRev fuel high scratch : List Bool) : Config :=
  ⟨l, none, words io inputRev fuel high scratch⟩

abbrev atL (l : Label) := cfg (some l)

/-- Ordinary paths exclude oracle calls, so are valid under every implementation of the oracle. -/
inductive Work : Config → Config → ℕ → Prop
  | refl (c) : Work c c 0
  | one {c d} : c.l ≠ some .ask → step program c = some d → Work c d 1
  | trans {a b c t u} : Work a b t → Work b c u → Work a c (t + u)

theorem workStep {l io nr fu hi sc d}
    (hne : l ≠ Label.ask)
    (hl : (stepAux (program l) none (words io nr fu hi sc)).l = d.l)
    (hv : (stepAux (program l) none (words io nr fu hi sc)).var = d.var)
    (hio : (stepAux (program l) none (words io nr fu hi sc)).stk .io = d.stk .io)
    (hnr : (stepAux (program l) none (words io nr fu hi sc)).stk .inputRev = d.stk .inputRev)
    (hfu : (stepAux (program l) none (words io nr fu hi sc)).stk .fuel = d.stk .fuel)
    (hhi : (stepAux (program l) none (words io nr fu hi sc)).stk .high = d.stk .high)
    (hsc : (stepAux (program l) none (words io nr fu hi sc)).stk .scratch = d.stk .scratch) :
    Work (atL l io nr fu hi sc) d 1 := by
  apply Work.one (fun h => hne (Option.some.inj h))
  apply congrArg some
  change stepAux _ _ _ = d
  have hstk : (stepAux (program l) none (words io nr fu hi sc)).stk = d.stk := by
    funext k
    cases k <;> assumption
  cases ha : stepAux (program l) none (words io nr fu hi sc) with
  | mk L V S =>
    rw [ha] at hl hv hstk
    cases d
    congr

/-- A stack pass reverses the source into its accumulator. The extra transition
detects the empty source and transfers to the next label. -/
theorem consume (stage : List Bool → List Bool → Config) (finish : List Bool → Config)
    (next : ∀ b xs acc, Work (stage (b :: xs) acc) (stage xs (b :: acc)) 1)
    (done_ : ∀ acc, Work (stage [] acc) (finish acc) 1)
    (xs acc : List Bool) : Work (stage xs acc) (finish (xs.reverse ++ acc)) (xs.length + 1) := by
  induction xs generalizing acc with
  | nil => simpa using done_ acc
  | cons b xs ih =>
    simpa [List.reverse_cons, List.append_assoc, Nat.add_comm 1 (xs.length + 1)] using
      (next b xs acc).trans (ih (b :: acc))

theorem prepareRound (input remaining high : List Bool) (v : Bool) :
    Work (atL .round [] input.reverse (v :: remaining) high [])
      (atL .ask (FactorSearchBits.queryWord input remaining high) input.reverse remaining high [])
      (2 * high.length + 2 * remaining.length + 2 * input.length + 7) := by
  have a : Work (atL .round [] input.reverse (v :: remaining) high [])
      (atL .saveHigh [] input.reverse remaining high []) 1 := by
    apply workStep <;> first | rfl | decide
  have b := consume (fun xs acc => atL .saveHigh [] input.reverse remaining xs acc)
      (fun acc => atL .restoreHigh [] input.reverse remaining [] acc)
      (by intros; apply workStep <;> first | rfl | decide)
      (by intros; apply workStep <;> first | rfl | decide) high []
  have c := consume (fun xs acc => atL .restoreHigh acc input.reverse remaining acc xs)
      (fun acc => atL .writeOnes (FactorSearchBits.digit false acc) input.reverse remaining acc [])
      (by intros; apply workStep <;> first | rfl | decide)
      (by intro acc; cases acc <;> apply workStep <;> first | rfl | decide) high.reverse []
  let low := FactorSearchBits.digit false high
  have d := consume (fun xs acc => atL .writeOnes ((acc.map (fun _ => true)) ++ low)
        input.reverse xs high acc)
      (fun acc => atL .restoreFuel ((acc.map (fun _ => true)) ++ low) input.reverse [] high acc)
      (by intros; apply workStep <;> first | rfl | decide)
      (by intros; apply workStep <;> first | rfl | decide) remaining []
  let pivot := FactorSearchBits.pivot remaining high
  have e := consume (fun xs acc => atL .restoreFuel pivot input.reverse acc high xs)
      (fun acc => atL .writeInput (false :: pivot) input.reverse acc high [])
      (by intros; apply workStep <;> first | rfl | decide)
      (by intros; apply workStep <;> first | rfl | decide) remaining.reverse []
  have f := consume (fun xs acc => atL .writeInput (BitstringEncoding.delimit acc ++ pivot)
        xs remaining high acc)
      (fun acc => atL .restoreInput (BitstringEncoding.delimit acc ++ pivot) [] remaining high acc)
      (by intros; apply workStep <;> first | rfl | decide)
      (by intros; apply workStep <;> first | rfl | decide) input.reverse []
  have g := consume (fun xs acc => atL .restoreInput (FactorSearchBits.queryWord input remaining high)
        acc remaining high xs)
      (fun acc => atL .ask (FactorSearchBits.queryWord input remaining high) acc remaining high [])
      (by intros; apply workStep <;> first | rfl | decide)
      (by intros; apply workStep <;> first | rfl | decide) input []
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at b c d e f g
  have hd : remaining.reverse.map (fun _ => true) = remaining.map (fun _ => true) := by simp
  rw [hd] at d
  convert ((((((a.trans b).trans c).trans d).trans e).trans f).trans g) using 1
  omega

theorem resumeRound (nr remaining high : List Bool) (answer : Bool) :
    Work (atL .resume [answer] nr remaining high [])
      (atL .round [] nr remaining (FactorSearchBits.digit (!answer) high) []) 1 := by
  cases answer <;> cases high <;> apply workStep <;> first | rfl | decide

end FactorSearchController

/-!
# Startup and cleanup for the binary-search TM2 controller

The first two transitions distinguish the empty and singleton encodings from
longer inputs. For longer inputs the controller saves one copy each in the
input and fuel stacks. With the fuel exhausted, two passes move the result to
the I/O stack in the original order, and one pass clears the saved input.
-/

namespace FactorSearchController

/-- The empty input is zero, whose exceptional result is two. -/
theorem start_empty :
    Work (atL .start [] [] [] [] []) (cfg none [false, true] [] [] [] []) 1 := by
  apply workStep <;> first | rfl | decide

/-- The only canonical singleton encodes one. The controller handles either
singleton with the same two-step path. -/
theorem start_singleton (b : Bool) :
    Work (atL .start [b] [] [] [] []) (cfg none [true] [] [] [] []) 2 := by
  have first : Work (atL .start [b] [] [] [] []) (atL .checkSecond [] [b] [b] [] []) 1 := by
    apply workStep <;> first | rfl | decide
  have last : Work (atL .checkSecond [] [b] [b] [] []) (cfg none [true] [] [] [] []) 1 := by
    apply workStep <;> first | rfl | decide
  exact first.trans last

/-- An input of length `L ≥ 2` starts its first comparison round after
`L + 2` transitions, with independent reversed copies of input and fuel. -/
theorem start_long (b c : Bool) (rest : List Bool) :
    Work (atL .start (b :: c :: rest) [] [] [] [])
      (atL .round [] (b :: c :: rest).reverse (b :: c :: rest).reverse [] [])
      ((b :: c :: rest).length + 2) := by
  have first : Work (atL .start (b :: c :: rest) [] [] [] [])
      (atL .checkSecond (c :: rest) [b] [b] [] []) 1 := by
    apply workStep <;> first | rfl | decide
  have second : Work (atL .checkSecond (c :: rest) [b] [b] [] [])
      (atL .saveInput (c :: rest) [b] [b] [] []) 1 := by
    apply workStep <;> first | rfl | decide
  have save := consume (fun xs acc => atL .saveInput xs acc acc [] [])
    (fun acc => atL .round [] acc acc [] [])
    (by intros; apply workStep <;> first | rfl | decide)
    (by intros; apply workStep <;> first | rfl | decide) (c :: rest) [b]
  convert (first.trans second).trans save using 1 <;>
    simp [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Once fuel runs out, finish with just the canonical prefix on the I/O stack.
The bound charges both passes over the prefix and the final erasure of the input. -/
theorem finish_round (nr high : List Bool) :
    Work (atL .round [] nr [] high []) (cfg none high [] [] [] [])
      (2 * high.length + nr.length + 4) := by
  have enter : Work (atL .round [] nr [] high []) (atL .finishHigh [] nr [] high []) 1 := by
    apply workStep <;> first | rfl | decide
  have stash := consume (fun xs acc => atL .finishHigh [] nr [] xs acc)
    (fun acc => atL .finishOut [] nr [] [] acc)
    (by intros; apply workStep <;> first | rfl | decide)
    (by intros; apply workStep <;> first | rfl | decide) high []
  have output := consume (fun xs acc => atL .finishOut acc nr [] [] xs)
    (fun acc => atL .clearInput acc nr [] [] [])
    (by intros; apply workStep <;> first | rfl | decide)
    (by intros; apply workStep <;> first | rfl | decide) high.reverse []
  have clear := consume (fun xs _ => atL .clearInput high xs [] [] [])
    (fun _ => cfg none high [] [] [] [])
    (by intros; apply workStep <;> first | rfl | decide)
    (by intros; apply workStep <;> first | rfl | decide) nr []
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at stash output
  convert ((enter.trans stash).trans output).trans clear using 1
  omega

end FactorSearchController

/-!
# Executing the binary-search controller

Every call contains a canonical pair. The accumulator and the unfinished low
bits together occupy at most as many bits as the original input. This bounds
the query clock as well as the ordinary transitions that prepare each call.
-/

namespace FactorSearchMachine

open Turing Computability ComplexityTheory BitstringEncoding FactorSearchController FactorOracleMachine

abbrev driver : OracleProgram where
  K := Stack
  Λ := Label
  σ := Option Bool
  k₀ := .io
  k₁ := .io
  arg := .io
  main := .start
  call := .ask
  resume := .resume
  initialState := none
  m := program

abbrev Runs (q : ℕ × ℕ → Bool) (P : Polynomial ℕ) :=
  driver.Run (bitEncode (α := ℕ × ℕ)) q P.eval

theorem work_runs {a b t} (hw : Work a b t) (q : ℕ × ℕ → Bool) (P : Polynomial ℕ) :
    Runs q P a b t := by
  induction hw with
  | refl c => exact OracleProgram.Run.refl (C := driver) c
  | one hn hs => exact .normal hn hs
  | trans _ _ hi hj => exact .trans hi hj

private def compareWord (q : ℕ × ℕ → Bool) (w : List Bool) : Bool :=
  ((bitDecode w : Option (ℕ × ℕ)).map q).getD false

private theorem compare_encode (q : ℕ × ℕ → Bool) (x : ℕ × ℕ) :
    compareWord q (bitEncode x) = q x := by simp [compareWord]

private theorem digit_length (b : Bool) (xs : List Bool) :
    (FactorSearchBits.digit b xs).length ≤ xs.length + 1 := by
  cases b <;> cases xs <;> simp [FactorSearchBits.digit]

private theorem result_length (q : List Bool → Bool) (input remaining high : List Bool) :
    (FactorSearchBits.run q input remaining high).length ≤ high.length + remaining.length := by
  induction remaining generalizing high with
  | nil => simp [FactorSearchBits.run]
  | cons v rest ih =>
    simp only [FactorSearchBits.run, List.length_cons]
    exact (ih _).trans (by have := digit_length (!(q (FactorSearchBits.queryWord input rest high))) high; omega)

private def stepBudget (P : Polynomial ℕ) (L : ℕ) := P.eval (3*L+1) + 12*L + 16

private theorem eval_mono (P : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : P.eval a ≤ P.eval b := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add] using Nat.add_le_add hp hq
  | monomial k c => simpa only [Polynomial.eval_monomial] using Nat.mul_le_mul_left c (Nat.pow_le_pow_left h k)

private theorem doCall (q : ℕ × ℕ → Bool) (P : Polynomial ℕ) (x : ℕ × ℕ)
    (nr fu high : List Bool) :
    Runs q P (atL .ask (bitEncode x) nr fu high [])
      (atL .resume [q x] nr fu high [])
      (P.eval (bitEncode x).length + 2 * (bitEncode x).length + 4) := by
  have hup : Function.update (words (bitEncode x) nr fu high []) .io [q x] =
      words [q x] nr fu high [] := by funext k; cases k <;> rfl
  have h := @OracleProgram.Run.oracle driver _ (bitEncode (α := ℕ × ℕ)) q P.eval x none
    (words (bitEncode x) nr fu high []) rfl
  change Runs q P _ ⟨some Label.resume, none,
    Function.update (words (bitEncode x) nr fu high []) Stack.io [q x]⟩ _ at h
  erw [hup] at h
  exact h

theorem rounds (q : ℕ × ℕ → Bool) (P : Polynomial ℕ) (n : ℕ) (remaining : List Bool) (h : ℕ)
    (cap : remaining.length + (encodeNat h).length ≤ (encodeNat n).length) :
    Runs q P (atL .round [] (encodeNat n).reverse remaining (encodeNat h) [])
      (atL .round [] (encodeNat n).reverse []
        (FactorSearchBits.run (compareWord q) (encodeNat n) remaining (encodeNat h)) [])
      (remaining.length * stepBudget P (encodeNat n).length) := by
  induction remaining generalizing h with
  | nil => simpa [FactorSearchBits.run] using
      (OracleProgram.Run.refl (C := driver) (encode := bitEncode) (query := q) (cost := P.eval)
        (atL .round [] (encodeNat n).reverse [] (encodeNat h) []))
  | cons v rest ih =>
    let input := encodeNat n
    let high := encodeNat h
    let x : ℕ × ℕ := (n, h * 2 ^ (rest.length + 1) + 2 ^ rest.length - 1)
    let w := FactorSearchBits.queryWord input rest high
    have hw : w = bitEncode x := FactorSearchBits.queryWord_encode n rest h
    have ha : compareWord q w = q x := hw ▸ compare_encode q x
    have hnew : FactorSearchBits.digit (!(q x)) high = encodeNat (2*h + (!(q x)).toNat) :=
      FactorSearchBits.digit_encode _ _
    have hcap : rest.length + (encodeNat (2*h + (!(q x)).toNat)).length ≤ input.length := by
      rw [← hnew]
      change rest.length + 1 + high.length ≤ input.length at cap
      have := digit_length (!(q x)) high
      omega
    have hsize : w.length ≤ 3 * input.length + 1 := by
      change rest.length + 1 + high.length ≤ input.length at cap
      have hs := digit_length false high
      simp only [w, FactorSearchBits.queryWord, FactorSearchBits.pivot, List.length_append,
        length_delimit, List.length_map]
      omega
    have hprepare := work_runs (prepareRound input rest high v) q P
    have hcall := doCall q P x input.reverse rest high
    rw [← hw] at hcall
    have hresume := work_runs (resumeRound input.reverse rest high (q x)) q P
    have first := (hprepare.trans hcall).trans hresume
    rw [hnew] at first
    have later := ih (2*h + (!(q x)).toNat) hcap
    have both := first.trans later
    change Runs q P _ (atL .round [] input.reverse []
      (FactorSearchBits.run (compareWord q) input rest (FactorSearchBits.digit (!(compareWord q w)) high)) []) _
    rw [ha, hnew]
    apply both.mono
    change rest.length + 1 + high.length ≤ input.length at cap
    simp only [List.length_cons, Nat.succ_mul]
    change _ ≤ rest.length * stepBudget P input.length + stepBudget P input.length
    have hp := eval_mono P hsize
    dsimp only [stepBudget, input] at *
    omega

private theorem initial (w : List Bool) :
    initList driver.tm w = atL .start w [] [] [] [] := by
  unfold initList atL cfg
  congr 1
  funext k
  cases k <;> rfl

private theorem finalCfg (w : List Bool) :
    haltList driver.tm w = cfg none w [] [] [] [] := by
  unfold haltList cfg
  congr 1
  funext k
  cases k <;> rfl

/-- The controller saves the fuel in reverse order. Its bits are only counted. -/
private theorem run_reverse (q : ℕ × ℕ → Bool) (n : ℕ) :
    FactorSearchBits.run (compareWord q) (encodeNat n) (encodeNat n).reverse [] =
      FactorSearchBits.run (compareWord q) (encodeNat n) (encodeNat n) [] := by
  change FactorSearchBits.run (compareWord q) _ _ (encodeNat 0) =
    FactorSearchBits.run (compareWord q) _ _ (encodeNat 0)
  rw [FactorSearchBits.run_encode _ q (compare_encode q) n (encodeNat n).reverse 0,
    FactorSearchBits.run_encode _ q (compare_encode q) n (encodeNat n) 0, List.length_reverse]

private noncomputable def totalBudget (P : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.X * (P.comp (3 * Polynomial.X + 1) + 12 * Polynomial.X + 16) +
    4 * Polynomial.X + 6

private theorem budget_eval (P : Polynomial ℕ) (L : ℕ) :
    (totalBudget P).eval L = L * stepBudget P L + 4*L + 6 := by
  simp [totalBudget, stepBudget]

theorem full_run (q : ℕ × ℕ → Bool) (P : Polynomial ℕ) (n : ℕ) :
    Runs q P (initList driver.tm (encodeNat n))
      (haltList driver.tm (FactorSearchBits.search (compareWord q) (encodeNat n)))
      ((totalBudget P).eval (encodeNat n).length) := by
  rw [initial, finalCfg, budget_eval]
  cases hw : encodeNat n with
  | nil =>
    exact (work_runs start_empty q P).mono (by simp)
  | cons b tail =>
    cases tail with
    | nil =>
      exact (work_runs (start_singleton b) q P).mono (by simp)
    | cons c rest =>
      let input := b :: c :: rest
      let out := FactorSearchBits.run (compareWord q) input input []
      have hbegin := work_runs (start_long b c rest) q P
      have hloop := rounds q P n (encodeNat n).reverse 0 (by simp [show encodeNat 0 = [] from rfl])
      rw [show encodeNat 0 = [] from rfl, run_reverse q n, hw, List.length_reverse] at hloop
      have hfinish := work_runs (finish_round input.reverse out) q P
      have path := (hbegin.trans hloop).trans hfinish
      have hlen : out.length ≤ input.length := by
        simpa using result_length (compareWord q) input input []
      apply path.mono
      change (input.length + 2 + input.length * stepBudget P input.length) +
        (2 * out.length + input.reverse.length + 4) ≤ _
      simp only [List.length_reverse]
      change _ ≤ input.length * stepBudget P input.length + 4 * input.length + 6
      omega

/-- The actual oracle-calling machine realizes the binary search on canonical inputs. -/
theorem search_polytime (q : ℕ × ℕ → Bool) (hq : IsPolyTime q) :
    IsPolyTime (fun n : ℕ =>
      if n < 2 then 2 - n else
      (Nat.rec (motive := fun _ => ℕ → ℕ) id
        (fun i search low => if q (n, low + 2 ^ i - 1) then search low else search (low + 2 ^ i))
        (n.log2 + 1)) 0) := by
  obtain ⟨Q⟩ := hq
  apply FactorOraclePolytime.of_machine driver Q (totalBudget Q.time)
  intro n
  have path := full_run q Q.time n
  rw [FactorSearchBits.search_encode _ q (compare_encode q)] at path
  exact path

end FactorSearchMachine

theorem OMA.solution : OMA.R_PolyTime_isPolyTime_primeFactorsList_R1.H3 := by
  exact FactorSearchMachine.search_polytime
