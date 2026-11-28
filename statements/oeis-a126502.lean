import Mathlib

/-!
# OEIS A126502: Barker's g.f. and recurrence for base 7 digit strings with adjacent digits differing by 4 or less

Source: https://oeis.org/A126502 (OEIS Foundation, CC BY-SA 4.0).
Credit: @Mapika (AI-assisted: Claude Code, model claude-opus-5-5).

Entry (R. H. Hardin, Dec 28 2006), offset 0: Number of base 7 n-digit numbers with adjacent digits
differing by four or less. Data: 1, 7, 43, 269, 1679, 10483, 65449, ... The formula section states:
Conjectures from Colin Barker, Jun 01 2017:
G.f.: (1 + x - x^2) / (1 - 6*x - 2*x^2 + 3*x^3).
a(n) = 6*a(n-1) + 2*a(n-2) - 3*a(n-3) for n>2.

Formalization notes:
* A base 7 n-digit number is read as a string of n digits in 0..6, i.e. a function
  `Fin n → Fin 7`, with leading zeros allowed. This is what the data counts: a(1) = 7 counts
  every digit including 0, and a(2) = 43 is the number of all digit pairs whose difference is at
  most 4 (excluding leading zeros would give a(1) = 6 and a(2) = 38). The same reading
  appears in the sibling entry A126474, whose original name was "Number of base 6 n-digit
  numbers with adjacent digits differing by three or less" and whose current name is "Number of
  arrays in [1..6]^n ...".
* "Adjacent digits differing by four or less": `List.IsChain near (List.ofFn f)`, i.e. every two
  consecutive digits f(i), f(i+1) satisfy |f(i) - f(i+1)| ≤ 4 (computed in ℤ).
* Offset 0: `a 0 = 1` counts the empty string, as in the data.
* `main` is the conjunction of both conjectures. The recurrence has a negative coefficient and is
  stated in ℤ for n > 2, as in the source. The g.f. is Sum_{n >= 0} a(n) x^n, and the identity
  A(x) = N(x)/D(x) is stated as A(x)*D(x) = N(x) in ℚ[[x]], which is equivalent because D has
  constant term 1.
* Controls: the definition gives a(0..4) = 1, 7, 43, 269, 1679, as in the entry.
-/

namespace OMA.S_oeis_a126502

/-- Two digits differ by four or less. -/
def near (x y : Fin 7) : Prop := |(x : ℤ) - (y : ℤ)| ≤ 4

instance : DecidableRel near := fun x y => by unfold near; infer_instance

/-- A126502: the number of base 7 digit strings of length n whose adjacent digits differ by
four or less. -/
def a (n : ℕ) : ℕ := (Finset.univ.filter fun f : Fin n → Fin 7 => (List.ofFn f).IsChain near).card

open PowerSeries in
/-- Barker's conjectures: the generating function and the recurrence for n > 2. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 6 * X - 2 * X ^ 2 + 3 * X ^ 3) = 1 + X - X ^ 2 ∧
    (∀ n : ℕ, 2 < n → (a n : ℤ) = 6 * a (n - 1) + 2 * a (n - 2) - 3 * a (n - 3)) := by
  sorry

end OMA.S_oeis_a126502
