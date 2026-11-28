import Mathlib

/-!
# A002618: a(n) = n * phi(n) = Euler phi of n^2.

Source: https://oeis.org/A002618
Credit: @rabdelaal

OEIS A002618 records the conjecture (John W. Layman, 2008, confirmed correct by
Franklin T. Adams-Watters, 2009): `a n = n * Nat.totient n` is the number of permutations
`f` of `{1, ..., n}` such that `f(1), f(2), ..., f(n)` is an arithmetic progression
modulo `n`, i.e. permutations whose values are `a, a+d, ..., a+(n-1)*d` mod `n` for some
`a` coprime to `n` and step `d` coprime to `n`.
-/

namespace OMA.S_oeis_a002618

/-- The OEIS A002618 entry: `n * phi n`. -/
def a (n : ℕ) : ℕ := n * Nat.totient n

/-- `f` is a permutation of `Fin n` whose image, read in the natural order of the
domain, is an arithmetic progression modulo `n`: there are a start `c` and a step `d`,
both units mod `n`, with `f i = c + d * i`. -/
def IsAPPermutation {n : ℕ} (f : Fin n → Fin n) : Prop :=
  ∃ c d : ℕ, Nat.Coprime c n → Nat.Coprime d n →
    ∀ i : Fin n, f i = ⟨(c + d * i : ℕ) % n, Nat.lt_of_lt_of_le (Nat.mod_lt _
      (Nat.pos_of_ne_zero fun h => by have := i.isLt; omega)) (Nat.le_refl n)⟩

/-- The conjecture recorded in OEIS A002618 (Layman): the number of permutations of
`Fin n` that are arithmetic progressions mod `n` equals `n * phi n`. -/
theorem main : ∀ n : ℕ, 0 < n →
    Nat.card { f : Fin n → Fin n | Function.Bijective f ∧ IsAPPermutation f } = a n := by
  sorry

end OMA.S_oeis_a002618
