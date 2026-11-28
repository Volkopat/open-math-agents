import Mathlib

/-!
# Purely periodic three-move subtraction games: necessity of the rotation tests

Source: https://arxiv.org/abs/2609.05358 (v2, 16 Sep 2026), Hikaru Manabe,
*Purely Periodic Three-move Subtraction Games*, Conjecture 52 (Conjecture 50 in v1, same text).

Subtraction game `S = {a, b, c}` with `0 < a < b < c`: from a heap `x` a move `s ∈ S` with
`s ≤ x` leads to `x - s`, and the Sprague-Grundy value is
`G_S(x) = mex {G_S(x - s) : s ∈ S, s ≤ x}`.
`G_S` is *purely periodic* if `G_S(x + p) = G_S(x)` for some `p ≥ 1` and every `x ≥ 0`.

Notation (Proposition 7 and Definition 19 of the paper), all read in `ℤ/(a+b)ℤ`:
`B = {a, b}`, `n = a + b`, `δ = b - a`, `ρ = c mod n`,
`Z = W₀(B) ∩ [0, n) = {x ∈ [0, n) : G_B(x) = 0}`, `D = [a, b) \ Z`, `Λ = [δ, b) \ Z`.

* (T0) `ρ ∈ Θ_{a+b}`  iff  `Z ∩ (Z + ρ) = ∅`;
* (T1) `ρ ∈ Θ_{c+a}`  iff  `(Z ∩ [0, δ)) ∩ (Z + (δ - ρ)) = ∅`;
* (T2) `ρ ∈ Θ_{c+b}`  iff  `(ρ + Λ) ∩ Z = ∅` and `(ρ + D) ∩ Λ = ∅`.

Conjecture 52: for `a ≥ 2`, `gcd(a, b, c) = 1` and `c ≠ a + b`, `G_S` is purely periodic iff
`ρ ∈ Θ_{a+b} ∪ Θ_{c+a} ∪ Θ_{c+b}`, and then the least period is the least admissible
`P ∈ {a+b, c+a, c+b}`. The paper proves the converse direction and the least-period formula
(Theorem 34) and says that only necessity remains open. `main` below is that open direction:
every purely periodic, primitive, non-additive game with `a ≥ 2` passes one of the three tests
(the catalogue line: the tests cover every purely periodic non-additive game).
-/

namespace OMA.S_arxiv_2609_05358

/-- Least natural number not in `t`. -/
def mex (t : Finset ℕ) : ℕ := Nat.find (Infinite.exists_notMem_finset t)

/-- Sprague-Grundy value of the heap `x` in the subtraction game with move set `S`:
the mex of the values of `x - s` over the moves `s ∈ S` with `0 < s ≤ x`. -/
def grundy (S : Finset ℕ) (x : ℕ) : ℕ :=
  mex ((S.filter (fun s => 0 < s ∧ s ≤ x)).attach.image (fun s => grundy S (x - s.1)))
termination_by x
decreasing_by
  have h := (Finset.mem_filter.mp s.2).2
  omega

/-- `Z = {x ∈ [0, a+b) : G_{a,b}(x) = 0}`, read in `ℤ/(a+b)`. -/
def Zset (a b : ℕ) : Finset (ZMod (a + b)) :=
  ((Finset.range (a + b)).filter (fun x => grundy {a, b} x = 0)).image (fun x : ℕ => (x : ZMod (a + b)))

/-- `D = [a, b) \ Z`. -/
def Dset (a b : ℕ) : Finset (ZMod (a + b)) :=
  ((Finset.Ico a b).filter (fun x => grundy {a, b} x ≠ 0)).image (fun x : ℕ => (x : ZMod (a + b)))

/-- `Λ = [δ, b) \ Z` with `δ = b - a`. -/
def Lam (a b : ℕ) : Finset (ZMod (a + b)) :=
  ((Finset.Ico (b - a) b).filter (fun x => grundy {a, b} x ≠ 0)).image (fun x : ℕ => (x : ZMod (a + b)))

/-- (T0) `Z ∩ (Z + ρ) = ∅`, with `ρ = c mod (a+b)`. -/
def T0 (a b c : ℕ) : Prop :=
  Disjoint (Zset a b) ((Zset a b).image (· + (c : ZMod (a + b))))

/-- (T1) `(Z ∩ [0, δ)) ∩ (Z + (δ - ρ)) = ∅`. -/
def T1 (a b c : ℕ) : Prop :=
  Disjoint ((Zset a b).filter (fun z => z.val < b - a))
    ((Zset a b).image (· + (((b - a : ℕ) : ZMod (a + b)) - (c : ZMod (a + b)))))

/-- (T2) `(ρ + Λ) ∩ Z = ∅` and `(ρ + D) ∩ Λ = ∅`. -/
def T2 (a b c : ℕ) : Prop :=
  Disjoint ((Lam a b).image (· + (c : ZMod (a + b)))) (Zset a b) ∧
  Disjoint ((Dset a b).image (· + (c : ZMod (a + b)))) (Lam a b)

/-- Conjecture 52 of arXiv 2609.05358, the open (necessity) direction: if `a ≥ 2`,
`a < b < c`, `gcd(a, b, c) = 1`, `c ≠ a + b` and the Grundy sequence of `{a, b, c}` is purely
periodic, then the angle `ρ = c mod (a + b)` passes (T0), (T1) or (T2). -/
theorem main : ∀ a b c : ℕ, 2 ≤ a → a < b → b < c → Nat.gcd (Nat.gcd a b) c = 1 → c ≠ a + b →
    (∃ p ≥ 1, ∀ x, grundy {a, b, c} (x + p) = grundy {a, b, c} x) →
    T0 a b c ∨ T1 a b c ∨ T2 a b c := by
  sorry

end OMA.S_arxiv_2609_05358
