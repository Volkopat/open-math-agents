import Mathlib

/-!
# OEIS A126474: Barker's recurrence and g.f. for arrays in [1..6]^n with adjacent differences at most 3

Source: https://oeis.org/A126474 (OEIS Foundation, CC BY-SA 4.0).
Credit: @Mapika (AI-assisted: Claude Code, model claude-opus-5-5).

Entry (R. H. Hardin, Dec 27 2006), offset 0: Number of arrays in [1..6]^n with adjacent elements
differing by three or less. Data: 1, 6, 30, 154, 788, 4034, 20650, ... The formula section states:
Conjectures from Colin Barker, Jan 20 2017:
a(n) = 5*a(n-1) + a(n-2) - 2*a(n-3) for n>2.
G.f.: (1 + x - x^2) / (1 - 5*x - x^2 + 2*x^3).
(A later formula line by Robert Israel, Jan 23 2018, explains why both hold.)

Formalization notes:
* An array in [1..6]^n is a function `Fin n → Fin 6`; the value `v : Fin 6` stands for the entry
  v + 1 ∈ [1..6]. The shift does not change differences.
* "Adjacent elements differing by three or less": `List.IsChain near (List.ofFn f)`, i.e. every
  two consecutive entries f(i), f(i+1) satisfy |f(i) - f(i+1)| ≤ 3 (computed in ℤ).
* Offset 0: `a 0 = 1` counts the empty array, as in the data.
* `main` is the conjunction of both conjectures. The recurrence has a negative coefficient and is
  stated in ℤ for n > 2, as in the source. The g.f. is Sum_{n >= 0} a(n) x^n, and the identity
  A(x) = N(x)/D(x) is stated as A(x)*D(x) = N(x) in ℚ[[x]], which is equivalent because D has
  constant term 1.
* Controls: the definition gives a(0..4) = 1, 6, 30, 154, 788, as in the entry.
-/

namespace OMA.S_oeis_a126474

/-- Two entries differ by three or less. -/
def near (x y : Fin 6) : Prop := |(x : ℤ) - (y : ℤ)| ≤ 3

instance : DecidableRel near := fun x y => by unfold near; infer_instance

/-- A126474: the number of arrays of length n over a 6-letter range whose adjacent entries
differ by three or less. -/
def a (n : ℕ) : ℕ := (Finset.univ.filter fun f : Fin n → Fin 6 => (List.ofFn f).IsChain near).card

open PowerSeries in
/-- Barker's conjectures: the recurrence for n > 2 and the generating function. -/
theorem main :
    (∀ n : ℕ, 2 < n → (a n : ℤ) = 5 * a (n - 1) + a (n - 2) - 2 * a (n - 3)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 5 * X - X ^ 2 + 2 * X ^ 3) = 1 + X - X ^ 2 := by
  sorry

end OMA.S_oeis_a126474
