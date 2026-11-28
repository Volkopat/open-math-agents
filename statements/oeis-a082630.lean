import Mathlib.Data.Nat.Basic

/-!
# The ratio-determined insertion sequence A082630

Starting with (1,1), insert x+y between adjacent x,y whenever 7y ≤ 11x.
The independent left-to-right algorithm published by Zhuorui He in 2025
emits x, adds x to y while 7(x+y) ≤ 11x, then replaces x by x+y.
The loop runs at most once, since after that addition y is at least x.
The first emitted value has source index 1.

A143643 uses its published linear recurrence for the lower convergent
numerators of sqrt(3), with an auxiliary value 0 at index 0. A005246 uses
its defining nonlinear recurrence. A001353 is the Lucas sequence U(4,1).
The targets express the Pell-type equation in the source, the sum formula
of Richard R. Forberg (2013), and the quotient of Andrei Zabolotskii (2024).

Sources: https://oeis.org/A082630, https://oeis.org/A143643,
https://oeis.org/A005246 and https://oeis.org/A001353
Credit: @KoaOkano
-/

namespace OMA.S_oeis_a082630

def stream : ℕ → ℕ × ℕ
  | 0 => (1,1)
  | k+1 =>
    let (x,y) := stream k
    let nextY := if 7*(x+y) ≤ 11*x then x+y else y
    (x+nextY,nextY)

def a (n : ℕ) : ℕ := (stream (n-1)).1

def lower : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | 3 => 5
  | k+4 => 4*lower (k+2)-lower k

def denominator : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | k+3 => (1+denominator (k+1)*denominator (k+2))/denominator k

def lucasU : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | k+2 => 4*lucasU (k+1)-lucasU k

def pell (x y : ℕ) : Prop := 0 < x ∧ x^2 = y^2/3+1

theorem main :
    (∀ n : ℕ, 1 ≤ n → pell (denominator n) (lower (n-1)) ∧
      a n = lower (n-1)+denominator n) ∧
    (∀ x y : ℕ, pell x y → ∃ n : ℕ, 1 ≤ n ∧ denominator n=x ∧ lower (n-1)=y) ∧
    ∀ n : ℕ, 1 ≤ n → a n = lucasU n / denominator (n+1) := by
  sorry

end OMA.S_oeis_a082630
