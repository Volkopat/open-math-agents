import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# Eventually exact gcd test for twin-prime pairs

Source: user231922, MathOverflow 455020, September 21, 2023, CC BY-SA 4.0.
https://mathoverflow.net/questions/455020/not-a-twin-prime-pair-test-using-gcd-only

The PARI loop visits a mirror pair twice. Only its two endpoints affect it:
the first visit adds their gcd to both, then the second does the same with
the updated endpoints. The center of an odd length vector is visited once,
and its two assignments both update the same entry. Requiring all initial
entries positive, as in the source, gives odd m ≥ 3.
-/

namespace OMA.S_mo_455020

def entry (m i c : ℕ) := m*(i+1)-c
def target (m n c : ℕ) := m*(n+3)-2*c

def finalEntry (m n i : ℕ) : ℕ :=
  let j := n+1-i
  let x := entry m i 2
  let y := entry m j 2
  let g := x.gcd y
  if i=j then x+2*g else x+g+(x+g).gcd (y+g)

def passes (m n : ℕ) : Prop :=
  ∀ i ∈ Finset.Icc 1 n, finalEntry m n i = m*(i+1)

def twins (m n : ℕ) : Prop := (target m n 2).Prime ∧ (target m n 1).Prime

theorem main : ∀ m : ℕ, 3 ≤ m → Odd m →
    (∀ n : ℕ, 1 ≤ n → twins m n → passes m n) ∧
    (∃ N : ℕ, ∀ n ≥ N, passes m n ↔ twins m n) := by
  sorry

end OMA.S_mo_455020
