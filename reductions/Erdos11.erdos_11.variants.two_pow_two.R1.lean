import FormalConjectures.ErdosProblems.«11»

-- Reduction Erdos11.erdos_11.variants.two_pow_two.R1 of Erdős Problem 11 (two powers of 2)
-- Credit: @LordMike
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Erdős 11 with two powers of 2, from the one-power form for `n ≡ 1 (mod 4)`

The two-power form follows from the one-power form (`Erdos11.erdos_11.variants.all_odd`), and
only half of the odd numbers are needed.

* If `n ≡ 1 (mod 4)` and `n = k + 2 ^ l` with `k` squarefree, then `l ≥ 1`, because
  `l = 0` gives `k = n - 1`, which is divisible by `4`. So `n = k + 2 ^ (l - 1) + 2 ^ (l - 1)`.
* If `n ≡ 3 (mod 4)` and `n ≥ 7`, then `n - 2 ≡ 1 (mod 4)` and `n - 2 = k + 2 ^ l` gives
  `n = k + 2 ^ l + 2 ^ 1`. And `3 = 1 + 2 ^ 0 + 2 ^ 0`.

The one-power form for `n ≡ 1 (mod 4)` is split by the residue modulo `8`:

* `H1` (open): every `n ≡ 1 (mod 8)`, `n > 1`, is a squarefree number plus a power of `2`.
* `H2` (open): every `n ≡ 5 (mod 8)` is a squarefree number plus a power of `2`.

Both are special cases of the sibling `all_odd`, not of the target: for these `n` they are
stronger than the target. So this is a link to the sibling problem. It shows that the target
needs only the residue class `1 (mod 4)` of it.
-/

namespace OMA.R_Erdos11_erdos_11_variants_two_pow_two_R1

/-- Every `n ≡ 1 (mod 8)` with `n > 1` is the sum of a squarefree number and a power of `2`. -/
def H1 : Prop :=
  ∀ n : ℕ, n % 8 = 1 → 1 < n → ∃ k l : ℕ, Squarefree k ∧ n = k + 2 ^ l

/-- Every `n ≡ 5 (mod 8)` is the sum of a squarefree number and a power of `2`. -/
def H2 : Prop :=
  ∀ n : ℕ, n % 8 = 5 → ∃ k l : ℕ, Squarefree k ∧ n = k + 2 ^ l

/-- For `n ≡ 1 (mod 4)` a representation with one power of two splits into two powers. -/
lemma split_pow {n k l : ℕ} (hn : n % 4 = 1) (hk : Squarefree k) (h : n = k + 2 ^ l) :
    ∃ k' a b : ℕ, Squarefree k' ∧ n = k' + 2 ^ a + 2 ^ b := by
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · exfalso
    have h4 : 4 ∣ k := by
      rw [pow_zero] at h
      omega
    have h2 : (2 : ℕ) * 2 ∣ k := h4
    have := hk 2 h2
    simp at this
  · obtain ⟨j, rfl⟩ : ∃ j, l = j + 1 := ⟨l - 1, by omega⟩
    exact ⟨k, j, j, hk, by rw [h, pow_succ]; ring⟩

lemma one_mod_four (h1 : H1) (h2 : H2) {n : ℕ} (hn : n % 4 = 1) (hn' : 1 < n) :
    ∃ k l : ℕ, Squarefree k ∧ n = k + 2 ^ l := by
  have hcase : n % 8 = 1 ∨ n % 8 = 5 := by omega
  rcases hcase with h | h
  · exact h1 n h hn'
  · exact h2 n h

theorem main : H1 → H2 → type_of% @Erdos11.erdos_11.variants.two_pow_two := by
  intro h1 h2 n hn hn'
  obtain ⟨m, rfl⟩ := hn
  have hcase : (2 * m + 1) % 4 = 1 ∨ (2 * m + 1) % 4 = 3 := by omega
  rcases hcase with h | h
  · obtain ⟨k, l, hk, hkl⟩ := one_mod_four h1 h2 h hn'
    exact split_pow h hk hkl
  · by_cases h3 : 2 * m + 1 = 3
    · exact ⟨1, 0, 0, squarefree_one, by rw [h3]; norm_num⟩
    · obtain ⟨k, l, hk, hkl⟩ := one_mod_four h1 h2 (n := 2 * m + 1 - 2) (by omega) (by omega)
      exact ⟨k, l, 1, hk, by rw [pow_one]; omega⟩

end OMA.R_Erdos11_erdos_11_variants_two_pow_two_R1
