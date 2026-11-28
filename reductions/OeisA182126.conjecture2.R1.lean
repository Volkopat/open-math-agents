import FormalConjectures.OEIS.«182126»

/-!
# A182126, conjecture 2: the residue is a product of two prime gaps

Write `p_k = Nat.nth Nat.Prime k` (so `p_0 = 2`); upstream `prime n` is `p_(n-1)` and
`a n = p_(n-1) * p_n % p_(n+1)`. Put `r = p_(k+2)`, `b = r - p_k` and `c = r - p_(k+1)`. Then
`p_k * p_(k+1) = (r - b) * (r - c)` is congruent to `b * c` modulo `r`, so `a (k+1) = b * c`
as soon as `b * c < r`. Conversely `a (k+1) < r`, so the conjecture for `n = k + 1` is
equivalent to the inequality `b * c < r` between two consecutive prime gaps and the prime
that ends them.

* `H1` is that inequality for the primes up to `10000`: a finite statement.
* `H2` is the inequality beyond `10000`. Together with `H1` it is the statement of the merged
  step `OeisA182126.conjecture3.R1.H1`, so one proof of the prime-gap inequality closes both
  conjectures. It asks for `g * (g + g') < r` for consecutive gaps `g'`, `g`, which follows from
  Cramér's conjecture and is not known unconditionally.

The modular identity is the one used in `OeisA182126.conjecture3.R1` by @jagong-cmu.
-/

namespace OMA.R_OeisA182126_conjecture2_R1

/-- The gap inequality for the primes `p_(k+2) ≤ 10000`, `k > 60`. -/
def H1 : Prop :=
  ∀ k : ℕ, 60 < k → Nat.nth Nat.Prime (k + 2) ≤ 10000 →
    (Nat.nth Nat.Prime (k + 2) - Nat.nth Nat.Prime k) *
      (Nat.nth Nat.Prime (k + 2) - Nat.nth Nat.Prime (k + 1)) < Nat.nth Nat.Prime (k + 2)

/-- The gap inequality for the primes `p_(k+2) > 10000`. -/
def H2 : Prop :=
  ∀ k : ℕ, 10000 < Nat.nth Nat.Prime (k + 2) →
    (Nat.nth Nat.Prime (k + 2) - Nat.nth Nat.Prime k) *
      (Nat.nth Nat.Prime (k + 2) - Nat.nth Nat.Prime (k + 1)) < Nat.nth Nat.Prime (k + 2)

theorem main : H1 → H2 → type_of% @OeisA182126.conjecture2 := by
  intro h1 h2 n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hlt : (Nat.nth Nat.Prime (m + 2) - Nat.nth Nat.Prime m) *
      (Nat.nth Nat.Prime (m + 2) - Nat.nth Nat.Prime (m + 1)) < Nat.nth Nat.Prime (m + 2) := by
    by_cases hB : Nat.nth Nat.Prime (m + 2) ≤ 10000
    · exact h1 m (by omega) hB
    · exact h2 m (by omega)
  have hmono : StrictMono (Nat.nth Nat.Prime) := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have hpr : Nat.nth Nat.Prime m ≤ Nat.nth Nat.Prime (m + 2) := (hmono (by omega : m < m + 2)).le
  have hqr : Nat.nth Nat.Prime (m + 1) ≤ Nat.nth Nat.Prime (m + 2) :=
    (hmono (by omega : m + 1 < m + 2)).le
  show OeisA182126.a (m + 1) =
    (OeisA182126.prime (m + 1 + 2) - OeisA182126.prime (m + 1)) *
      (OeisA182126.prime (m + 1 + 2) - OeisA182126.prime (m + 1 + 1))
  have ha : OeisA182126.a (m + 1) =
      (Nat.nth Nat.Prime m * Nat.nth Nat.Prime (m + 1)) % Nat.nth Nat.Prime (m + 2) := by
    unfold OeisA182126.a OeisA182126.prime
    simp
  have e0 : OeisA182126.prime (m + 1) = Nat.nth Nat.Prime m := rfl
  have e1 : OeisA182126.prime (m + 1 + 1) = Nat.nth Nat.Prime (m + 1) := rfl
  have e2 : OeisA182126.prime (m + 1 + 2) = Nat.nth Nat.Prime (m + 2) := rfl
  rw [ha, e0, e1, e2]
  generalize Nat.nth Nat.Prime m = p at *
  generalize Nat.nth Nat.Prime (m + 1) = q at *
  generalize Nat.nth Nat.Prime (m + 2) = r at *
  have hid : p * q + r * ((r - p) + (r - q)) = (r - p) * (r - q) + r * r := by
    zify [hpr, hqr]
    ring
  have m1 : (p * q + r * ((r - p) + (r - q))) % r = (p * q) % r :=
    Nat.add_mul_mod_self_left _ _ _
  have m2 : ((r - p) * (r - q) + r * r) % r = ((r - p) * (r - q)) % r :=
    Nat.add_mul_mod_self_left _ _ _
  rw [← m1, hid, m2, Nat.mod_eq_of_lt hlt]

end OMA.R_OeisA182126_conjecture2_R1
