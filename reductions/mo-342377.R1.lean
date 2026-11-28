import OMAStatements.S_mo_342377

-- Reduction mo-342377.R1 of Near Pochhammer symbols: the equation $(n)_m-(k)_l=2$ for integers greater than or equal to two
-- Credit: @futurum-dev
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Splitting `(a)_b = (c)_d + 2` by the lengths `b` and `d`

Write `(n)_m = n (n+1) ⋯ (n+m-1)` (`Nat.ascFactorial n m`) and consider `(a)_b = (c)_d + 2` with
`a, b, c, d ≥ 2`.

* `H1`: there is no solution with `b ≥ 3`, and none with `b = d = 2`.
  For `b ≥ 3`, `3 ∣ b! ∣ (a)_b`; but `(c)_d mod 3 ∈ {0, 2}` for every `d ≥ 2` (`3 ∣ (c)_d` when
  `d ≥ 3`, and `c (c+1) mod 3 ∈ {0, 2}`), so `(c)_d + 2 mod 3 ∈ {1, 2}`. For `b = d = 2`,
  `c (c+1) + 2` lies strictly between the consecutive pronic numbers `c (c+1)` and `(c+1)(c+2)`.
* So `b = 2` and `d ≥ 3`, and since `a (a+1) - 2 = (a-1)(a+2)` the equation becomes
  `(a-1)(a+2) = (c)_d`: a product of two integers differing by `3` equal to a product of `d ≥ 3`
  consecutive integers.
* `H2`: the case `d = 4` has no solution: `(c)_4 = m (m+2)` with `m = c² + 3c`, and
  `x (x+3) = m (m+2)` is impossible for `m ≥ 1` because `(m-1)(m+2) < m (m+2) < m (m+3)`.
* `H3`: the case `d = 3`, i.e. integral points on the elliptic curve
  `(2a+1)² = 4c(c+1)(c+2) + 9`. Finite by Siegel's theorem (effective by Baker); solutions
  include `(a, c) = (22, 7), (31, 9), (18958, 710)`.
* `H4`: the range `d ≥ 5`, the open core of the question (each fixed `d` is a curve of genus
  `≥ 1`, finite by Siegel, but finiteness uniformly in `d` is open).
-/

namespace OMA.R_mo_342377_R1

/-- No solution with `b ≥ 3` (a congruence modulo `3`), and none with `b = d = 2` (size). -/
def H1 : Prop :=
  ∀ a b c d : ℕ, 2 ≤ a → 2 ≤ c → 2 ≤ d → (3 ≤ b ∨ (b = 2 ∧ d = 2)) →
    Nat.ascFactorial a b ≠ Nat.ascFactorial c d + 2

/-- The case `d = 4`: `(a-1)(a+2) = c(c+1)(c+2)(c+3)` has no solution. -/
def H2 : Prop :=
  ∀ a c : ℕ, 2 ≤ a → 2 ≤ c → (a - 1) * (a + 2) ≠ Nat.ascFactorial c 4

/-- The case `d = 3`: `(a-1)(a+2) = c(c+1)(c+2)` has finitely many solutions. -/
def H3 : Prop :=
  Set.Finite {p : ℕ × ℕ | 2 ≤ p.1 ∧ 2 ≤ p.2 ∧ (p.1 - 1) * (p.1 + 2) = Nat.ascFactorial p.2 3}

/-- The open range `d ≥ 5`: `(a-1)(a+2) = c(c+1)⋯(c+d-1)` has finitely many solutions. -/
def H4 : Prop :=
  Set.Finite {t : ℕ × ℕ × ℕ | 2 ≤ t.1 ∧ 2 ≤ t.2.1 ∧ 5 ≤ t.2.2 ∧
    (t.1 - 1) * (t.1 + 2) = Nat.ascFactorial t.2.1 t.2.2}

theorem pronic (a : ℕ) (ha : 1 ≤ a) : Nat.ascFactorial a 2 = (a - 1) * (a + 2) + 2 := by
  obtain ⟨e, rfl⟩ : ∃ e, a = e + 1 := ⟨a - 1, by omega⟩
  simp [Nat.ascFactorial_succ]
  ring

theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_mo_342377.main := by
  intro h1 h2 h3 h4
  let f : ℕ × ℕ → ℕ × ℕ × ℕ × ℕ := fun p => (p.1, 2, p.2, 3)
  let g : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ × ℕ := fun t => (t.1, 2, t.2.1, t.2.2)
  refine ((h3.image f).union (h4.image g)).subset ?_
  rintro ⟨a, b, c, d⟩ ⟨ha, hb, hc, hd, h⟩
  simp only at ha hb hc hd h
  have hb2 : b = 2 := by
    by_contra hne
    exact h1 a b c d ha hc hd (Or.inl (by omega)) h
  subst hb2
  have hd3 : 3 ≤ d := by
    by_contra hlt
    exact h1 a 2 c d ha hc hd (Or.inr ⟨rfl, by omega⟩) h
  have heq : (a - 1) * (a + 2) = Nat.ascFactorial c d := by
    rw [pronic a (by omega)] at h
    omega
  rcases Nat.lt_or_ge d 4 with hd4 | hd4
  · have : d = 3 := by omega
    subst this
    left
    exact ⟨(a, c), ⟨ha, hc, heq⟩, rfl⟩
  · have hd5 : 5 ≤ d := by
      by_contra hlt
      have : d = 4 := by omega
      subst this
      exact h2 a c ha hc heq
    right
    exact ⟨(a, c, d), ⟨ha, hc, hd5, heq⟩, rfl⟩

end OMA.R_mo_342377_R1
