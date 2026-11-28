import Mathlib.Data.Set.Insert
import Mathlib.Data.Nat.Digits.Defs

/-!
# OEIS A398307: zero indices of OEIS A398259

Source: https://oeis.org/A398307 and https://oeis.org/A398259, Bence Bernáth.
Indices begin at 1. The history at n lists the earlier terms with their
one-based indices, newest first. A missing lookup returns the sentinel 0.
Credit: Sarkis Avetisyan, Vynet (@vynet-ai). Mathematics with GPT-6.2 Astra and other OpenAI models, checked with Claude.
-/

namespace OMA.S_oeis_a398307

/-- Sum the decimal digits, stopping as soon as the quotient is zero. -/
def sumAux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel+1, v => if v = 0 then 0 else v % 10 + sumAux fuel (v / 10)

def digitSum (v : ℕ) := sumAux v v

def lookup (key : ℕ) : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (v,i)::tail => if key = v then i else lookup key tail

structure State where
  value : ℕ
  history : List (ℕ × ℕ)

def step (n : ℕ) (s : State) : State :=
  let m := lookup (digitSum s.value) s.history
  ⟨if m = 0 then 0 else n-m, (s.value,n)::s.history⟩

def state : ℕ → State
  | 0 => ⟨0, []⟩
  | n+1 => if n = 0 then ⟨0, []⟩ else step n (state n)

def claimed : Set ℕ :=
  {1,2,4,6,11,13,18,21,25,33,46,170,187,196,288,320,334,424,433,437,455,505,514,523,530,541}

theorem main : {n : ℕ | 0 < n ∧ (state n).value = 0} = claimed := by
  sorry

end OMA.S_oeis_a398307
