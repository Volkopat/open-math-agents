import Mathlib

/-!
# A165556: A symmetric version of the Josephus problem read modulo 2

Source: https://oeis.org/A165556

Definition: n numbers 1..n stand in a circle. Two elimination processes alternate, the
first process acting first at every stage. The first process starts at number 1 and goes
upward: it skips one surviving number and eliminates the next (2, 4, 6, ...). The second
process starts at number n and goes downward: it skips one surviving number and eliminates
the next (n-1, n-3, ...). JI(n) is the last survivor and a(n) = JI(n) mod 2, offset 1.

Conjecture (Velin Yanev, Nov 23 2016):
  a(n) = (1 - (-1)^(n + (n + 1)*floor(log_2(n + 1))))/2.

Formalized: the circle is the list of surviving numbers; each process remembers the number it
eliminated last (starting from the virtual positions 0 and n+1), and moves to the next
surviving number strictly above (resp. below) it, cyclically. The simulation with fuel n
(n - 1 eliminations are needed) reproduces the worked example JI(14) = 7 and agrees with the
recurrences of the entry for 8 <= n < 300. The right side of the conjecture is 0 or 1
according to the parity of n + (n+1)*floor(log_2(n+1)), written with Nat.log 2 (n+1).
The claim is stated for all n >= 1. Note: the listed data has a(64) = 1, while both the
definition (JI(64) = 54) and the conjecture give 0; the statement follows the definition.
-/

namespace OMA.S_oeis_a165556

/-- Next surviving number strictly above `x`, cyclically. -/
def nxt (A : List ℕ) (x : ℕ) : ℕ :=
  match (A.filter (fun y => decide (x < y))).min? with
  | some y => y
  | none => A.min?.getD 0

/-- Next surviving number strictly below `x`, cyclically. -/
def prv (A : List ℕ) (x : ℕ) : ℕ :=
  match (A.filter (fun y => decide (y < x))).max? with
  | some y => y
  | none => A.max?.getD 0

/-- Run the two alternating processes with fuel `k`; `t = true` means the first process acts. -/
def run : ℕ → List ℕ → ℕ → ℕ → Bool → ℕ
  | 0, A, _, _, _ => A.headD 0
  | k + 1, A, p1, p2, t =>
    if A.length ≤ 1 then A.headD 0
    else if t then
      run k (A.erase (nxt A (nxt A p1))) (nxt A (nxt A p1)) p2 false
    else
      run k (A.erase (prv A (prv A p2))) p1 (prv A (prv A p2)) true

/-- JI(n), the last survivor. -/
def JI (n : ℕ) : ℕ := run n (List.range' 1 n) 0 (n + 1) true

/-- a(n) = JI(n) mod 2. -/
def a (n : ℕ) : ℕ := JI n % 2

theorem main : ∀ n : ℕ, 1 ≤ n →
    a n = (if Even (n + (n + 1) * Nat.log 2 (n + 1)) then 0 else 1) := by
  sorry

end OMA.S_oeis_a165556
