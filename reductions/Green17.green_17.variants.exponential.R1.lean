import FormalConjectures.GreensOpenProblems.«17»

-- Reduction Green17.green_17.variants.exponential.R1 of Green's Problem 17, exponential density
-- Credit: @LordMike
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Green 17 with exponential density: infinitely many dimensions are enough

A restricted progression in `𝔽₃ n` is a triple `x, x + d, x + 2d` with `d` a nonzero vector in
`{0, 1} ^ n`. The target asks for a constant `0 < c < 1` such that, for all large `n`, every set
`A` in `𝔽₃ n` with `(1 - c) ^ n * 3 ^ n ≤ A.card` contains a restricted progression.

* `H1` says that sets with no restricted progression can be multiplied: from such sets in `𝔽₃ m`
  and `𝔽₃ n` we get one in `𝔽₃ (m + n)` whose size is the product. This is elementary. Take the
  product set. A nonzero `d` in `{0, 1} ^ (m + n)` is nonzero on one of the two blocks, and the
  restriction to that block is a restricted progression there.
* `H2` is the open core: the bound of the target with some constant `c`, but only for infinitely
  many `n`. It is a formal consequence of the target.

`main` is the product (tensor power) trick. Let `A` in `𝔽₃ n` have no restricted progression and
size at least `((1 - c / 2) * 3) ^ n`, with `n ≥ 1`. By `H1`, for every `N` there is such a set in
`𝔽₃ N` of size `A.card ^ (N / n)`: take the power `N / n` and pad with `N % n` constant
coordinates. For large `N` this size is at least `((1 - c) * 3) ^ N`, which contradicts `H2` at a
large `N` from its infinite set. So the target holds with `c / 2`, for all `n ≥ 1`.

Hence the target is equivalent to `sup_n (maxFree n) ^ (1 / n) < 3`, and a proof may use any
infinite set of dimensions, for example the powers of two.

Source: B. Green, *100 open problems*, Problem 17.
-/

open Filter

namespace OMA.R_Green17_green_17_variants_exponential_R1

/-- Sets with no restricted progression can be multiplied. -/
def H1 : Prop :=
  ∀ (m n : ℕ) (A : Finset (𝔽₃ m)) (B : Finset (𝔽₃ n)),
    ¬ Green17.HasRestrictedAP A → ¬ Green17.HasRestrictedAP B →
    ∃ C : Finset (𝔽₃ (m + n)), C.card = A.card * B.card ∧ ¬ Green17.HasRestrictedAP C

/-- The exponential bound holds for infinitely many dimensions. This is the open core. -/
def H2 : Prop :=
  ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∃ᶠ n : ℕ in atTop, ∀ A : Finset (𝔽₃ n),
    (1 - c) ^ n * 3 ^ n ≤ (A.card : ℝ) → Green17.HasRestrictedAP A

/-- A one-point set has no restricted progression. -/
lemma singleton_free (r : ℕ) :
    ∃ C : Finset (𝔽₃ r), C.card = 1 ∧ ¬ Green17.HasRestrictedAP C := by
  refine ⟨{0}, Finset.card_singleton _, ?_⟩
  rintro ⟨x, d, hd, -, hx, hxd, -⟩
  rw [Finset.mem_singleton] at hx hxd
  apply hd
  rw [hx, zero_add] at hxd
  exact hxd

/-- Padding: a progression-free set in `𝔽₃ a` gives one of the same size in `𝔽₃ (a + b)`. -/
lemma pad_free (h1 : H1) (a b N : ℕ) (hN : a + b = N) (C : Finset (𝔽₃ a))
    (hC : ¬ Green17.HasRestrictedAP C) :
    ∃ E : Finset (𝔽₃ N), E.card = C.card ∧ ¬ Green17.HasRestrictedAP E := by
  subst hN
  obtain ⟨D, hD, hDfree⟩ := singleton_free b
  obtain ⟨E, hE, hEfree⟩ := h1 a b C D hC hDfree
  exact ⟨E, by rw [hE, hD, mul_one], hEfree⟩

/-- Powers: a progression-free set in `𝔽₃ n` gives one of size `A.card ^ k` in `𝔽₃ (n * k)`. -/
lemma pow_free (h1 : H1) (n : ℕ) (A : Finset (𝔽₃ n)) (hA : ¬ Green17.HasRestrictedAP A) :
    ∀ k N : ℕ, N = n * k →
      ∃ C : Finset (𝔽₃ N), C.card = A.card ^ k ∧ ¬ Green17.HasRestrictedAP C := by
  intro k
  induction k with
  | zero =>
    intro N _
    obtain ⟨C, hC, hfree⟩ := singleton_free N
    exact ⟨C, by rw [hC, pow_zero], hfree⟩
  | succ k ih =>
    intro N hN
    obtain ⟨C, hC, hfree⟩ := ih (n * k) rfl
    obtain ⟨D, hD, hDfree⟩ := h1 (n * k) n C A hfree hA
    have e : n * k + n = N := by rw [hN, Nat.mul_succ]
    subst e
    exact ⟨D, by rw [hD, hC, pow_succ], hDfree⟩

/-- The gain of the power beats the loss from padding once `N` is large. -/
lemma growth (u v : ℝ) (hv : 0 < v) (hv3 : v ≤ 3) (huv : v < u) (n : ℕ) (hn : 1 ≤ n) :
    ∃ K : ℕ, ∀ N : ℕ, K * n ≤ N → v ^ N ≤ (u ^ n) ^ (N / n) := by
  have hq : 1 < u / v := (one_lt_div hv).mpr huv
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt ((3 : ℝ) ^ n) hq
  refine ⟨K, fun N hN => ?_⟩
  have hk : K ≤ N / n := (Nat.le_div_iff_mul_le (by omega)).mpr hN
  have hk' : K ≤ n * (N / n) := le_trans hk (Nat.le_mul_of_pos_left _ (by omega))
  have e : n * (N / n) + N % n = N := Nat.div_add_mod N n
  have hr : N % n < n := Nat.mod_lt _ (by omega)
  have h1 : v ^ (N % n) ≤ (u / v) ^ (n * (N / n)) := by
    calc v ^ (N % n) ≤ 3 ^ (N % n) := pow_le_pow_left₀ hv.le hv3 _
      _ ≤ 3 ^ n := pow_le_pow_right₀ (by norm_num) hr.le
      _ ≤ (u / v) ^ K := hK.le
      _ ≤ (u / v) ^ (n * (N / n)) := pow_le_pow_right₀ hq.le hk'
  have h2 : v ^ (n * (N / n)) * (u / v) ^ (n * (N / n)) = u ^ (n * (N / n)) := by
    rw [← mul_pow]
    congr 1
    field_simp
  calc v ^ N = v ^ (n * (N / n)) * v ^ (N % n) := by rw [← pow_add, e]
    _ ≤ v ^ (n * (N / n)) * (u / v) ^ (n * (N / n)) :=
        mul_le_mul_of_nonneg_left h1 (pow_nonneg hv.le _)
    _ = u ^ (n * (N / n)) := h2
    _ = (u ^ n) ^ (N / n) := pow_mul u n (N / n)

theorem main : H1 → H2 → type_of% @Green17.green_17.variants.exponential := by
  rintro h1 ⟨c, hc0, hc1, hfreq⟩
  refine ⟨c / 2, by linarith, by linarith, ?_⟩
  rw [eventually_atTop]
  refine ⟨1, fun n hn A hA => ?_⟩
  by_contra hfree
  obtain ⟨K, hK⟩ := growth ((1 - c / 2) * 3) ((1 - c) * 3) (by linarith) (by linarith)
    (by linarith) n hn
  obtain ⟨N, hN, hP⟩ := hfreq.forall_exists_of_atTop (K * n)
  obtain ⟨C, hC, hCfree⟩ := pow_free h1 n A hfree (N / n) _ rfl
  obtain ⟨E, hE, hEfree⟩ := pad_free h1 _ (N % n) N (Nat.div_add_mod N n) C hCfree
  apply hEfree
  apply hP
  rw [hE, hC]
  push_cast
  calc (1 - c) ^ N * 3 ^ N = ((1 - c) * 3) ^ N := (mul_pow _ _ _).symm
    _ ≤ (((1 - c / 2) * 3) ^ n) ^ (N / n) := hK N hN
    _ ≤ (A.card : ℝ) ^ (N / n) := by
        apply pow_le_pow_left₀ (pow_nonneg (by linarith) _)
        rw [mul_pow]
        exact hA

end OMA.R_Green17_green_17_variants_exponential_R1
