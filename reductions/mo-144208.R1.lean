import OMAStatements.S_mo_144208

-- Reduction mo-144208.R1 of If $\left(1^a+2^a+\cdots+n^{a}\right)^b=1^c+2^c+\cdots+n^c$ for some $n$, then $(a,b,c)=(1,2,3)$?
-- Credit: @futurum-dev
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Splitting by the number of terms

The equation `(1^a + ⋯ + n^a)^b = 1^c + ⋯ + n^c` is split according to `n`.

* `H1`: the case `n = 2`, i.e. `(1 + 2^a)^b = 1 + 2^c`. Writing `(1 + 2^a)^b ≡ 1 + b·2^a`
  modulo `2^(a+1)` shows that `b` is even, and then `((1+2^a)^m - 1)((1+2^a)^m + 1) = 2^c`
  forces `(1+2^a)^m = 3` (the MathOverflow question, item 2).
* `H2`: the case `n = 3`, i.e. `(1 + 2^a + 3^a)^b = 1 + 2^c + 3^c`. Size gives `c > ab`;
  modulo `8` the case `b ≥ 3` is impossible; for `b = 2` and `a ≥ 2` one has
  `3^c < (1 + 2^a + 3^a)^2 < 3^(2a+1)`, contradicting `c > 2a` (the question, item 3).
* `H3`: the case `n = 4`, given `c > ab` (supplied by `main`). Modulo `8` again `b = 2`; then
  `1 + 2^a + 3^a < 4^a` for `a ≥ 2` gives `(1 + 2^a + 3^a + 4^a)^2 < 4^(2a+1) ≤ 4^c`.
* `H4`: the remaining range `n ≥ 5`, which is the open part of the question. Here `main`
  already supplies `c > ab`: for every `n ≥ 2`, `T = 1^a + ⋯ + n^a > n^a`, so
  `∑ k^c ≤ ∑ k^(ab) ≤ T·(n^a)^(b-1) < T^b` whenever `c ≤ ab`.
-/

namespace OMA.R_mo_144208_R1

/-- The case `n = 2`: `(1 + 2^a)^b = 1 + 2^c` only for `(a, b, c) = (1, 2, 3)`. -/
def H1 : Prop :=
  ∀ a b c : ℕ, 0 < a → 2 ≤ b → 0 < c →
    (1 + 2 ^ a) ^ b = 1 + 2 ^ c → (a, b, c) = (1, 2, 3)

/-- The case `n = 3`: `(1 + 2^a + 3^a)^b = 1 + 2^c + 3^c` only for `(a, b, c) = (1, 2, 3)`. -/
def H2 : Prop :=
  ∀ a b c : ℕ, 0 < a → 2 ≤ b → 0 < c →
    (1 + 2 ^ a + 3 ^ a) ^ b = 1 + 2 ^ c + 3 ^ c → (a, b, c) = (1, 2, 3)

/-- The case `n = 4`, where one may assume `c > ab`. -/
def H3 : Prop :=
  ∀ a b c : ℕ, 0 < a → 2 ≤ b → a * b < c →
    (1 + 2 ^ a + 3 ^ a + 4 ^ a) ^ b = 1 + 2 ^ c + 3 ^ c + 4 ^ c → (a, b, c) = (1, 2, 3)

/-- The open range `n ≥ 5`, where one may assume `c > ab`. -/
def H4 : Prop :=
  ∀ a b c n : ℕ, 0 < a → 2 ≤ b → a * b < c → 5 ≤ n →
    (∑ k ∈ Finset.Icc 1 n, k ^ a) ^ b = ∑ k ∈ Finset.Icc 1 n, k ^ c → (a, b, c) = (1, 2, 3)

theorem sum_two (a : ℕ) : (∑ k ∈ Finset.Icc 1 2, k ^ a) = 1 + 2 ^ a := by
  rw [show Finset.Icc 1 2 = {1, 2} from rfl]; simp

theorem sum_three (a : ℕ) : (∑ k ∈ Finset.Icc 1 3, k ^ a) = 1 + 2 ^ a + 3 ^ a := by
  rw [show Finset.Icc 1 3 = {1, 2, 3} from rfl]; simp; ring

theorem sum_four (a : ℕ) :
    (∑ k ∈ Finset.Icc 1 4, k ^ a) = 1 + 2 ^ a + 3 ^ a + 4 ^ a := by
  rw [show Finset.Icc 1 4 = {1, 2, 3, 4} from rfl]; simp; ring

/-- If `c ≤ ab` the right side is strictly smaller than the left side. -/
theorem size (a b c n : ℕ) (hb : 2 ≤ b) (hn : 2 ≤ n) (hc : c ≤ a * b) :
    ∑ k ∈ Finset.Icc 1 n, k ^ c < (∑ k ∈ Finset.Icc 1 n, k ^ a) ^ b := by
  set T := ∑ k ∈ Finset.Icc 1 n, k ^ a with hT
  have hT1 : 1 + n ^ a ≤ T := by
    have hsub : ({1, n} : Finset ℕ) ⊆ Finset.Icc 1 n := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp <;> omega
    have := Finset.sum_le_sum_of_subset (f := fun k => k ^ a) hsub
    rw [Finset.sum_pair (by omega), one_pow] at this
    exact this
  have h1 : ∑ k ∈ Finset.Icc 1 n, k ^ c ≤ ∑ k ∈ Finset.Icc 1 n, k ^ (a * b) := by
    apply Finset.sum_le_sum
    intro k hk
    exact Nat.pow_le_pow_right (by simp at hk; omega) hc
  have h2 : ∑ k ∈ Finset.Icc 1 n, k ^ (a * b) ≤ T * (n ^ a) ^ (b - 1) := by
    rw [hT, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro k hk
    have hkn : k ≤ n := by simp at hk; omega
    have : k ^ (a * b) = k ^ a * (k ^ a) ^ (b - 1) := by
      rw [← pow_mul, ← pow_add]; congr 1
      obtain ⟨e, rfl⟩ : ∃ e, b = e + 1 := ⟨b - 1, by omega⟩
      simp [Nat.mul_succ]; ring
    rw [this]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.pow_le_pow_left hkn a) _)
  have h3 : (n ^ a) ^ (b - 1) < T ^ (b - 1) :=
    Nat.pow_lt_pow_left (by omega) (by omega)
  have hTpos : 0 < T := by omega
  have h4 : T * (n ^ a) ^ (b - 1) < T ^ b := by
    calc T * (n ^ a) ^ (b - 1) < T * T ^ (b - 1) := Nat.mul_lt_mul_of_pos_left h3 hTpos
      _ = T ^ b := by
        obtain ⟨e, rfl⟩ : ∃ e, b = e + 1 := ⟨b - 1, by omega⟩
        simp [pow_succ]; ring
  omega

theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_mo_144208.main := by
  intro h1 h2 h3 h4 a b c n ha hb hc hn h
  have hcab : a * b < c := by
    by_contra hle
    have := size a b c n hb hn (by omega)
    rw [h] at this
    exact lt_irrefl _ this
  rcases Nat.lt_or_ge n 5 with hn5 | hn5
  · interval_cases n
    · rw [sum_two, sum_two] at h
      exact h1 a b c ha hb hc h
    · rw [sum_three, sum_three] at h
      exact h2 a b c ha hb hc h
    · rw [sum_four, sum_four] at h
      exact h3 a b c ha hb hcab h
  · exact h4 a b c n ha hb hcab hn5 h

end OMA.R_mo_144208_R1
