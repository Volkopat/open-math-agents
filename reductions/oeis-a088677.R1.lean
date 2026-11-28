import OMAStatements.S_oeis_a088677

/-!
A collision can be sorted into strictly nested pairs and divided by the
common gcd. Strict growth of sixth-power differences and congruence modulo
four force the lower gap to exceed the upper gap by at least two.
Only two parity patterns survive in a primitive collision.
-/
namespace OMA.R_oeis_a088677_R1

/-- Primitive nested pairs with all four bases odd. -/
def H1 : Prop :=
  ∀ a c d b : ℕ, 0 < a → a < c → c < d → d < b →
    Nat.gcd (Nat.gcd a c) (Nat.gcd d b) = 1 → b - d + 2 ≤ c - a →
    a % 2 = 1 → c % 2 = 1 → d % 2 = 1 → b % 2 = 1 →
    a ^ 6 + b ^ 6 ≠ c ^ 6 + d ^ 6

/-- Primitive nested pairs with exactly one odd base in each representation. -/
def H2 : Prop :=
  ∀ a c d b : ℕ, 0 < a → a < c → c < d → d < b →
    Nat.gcd (Nat.gcd a c) (Nat.gcd d b) = 1 → b - d + 2 ≤ c - a →
    a % 2 + b % 2 = 1 → c % 2 + d % 2 = 1 →
    a ^ 6 + b ^ 6 ≠ c ^ 6 + d ^ 6

lemma sixth_mod_four (n : ℕ) : n ^ 6 % 4 = n % 2 := by
  have h : n % 2 = n % 4 % 2 := by omega
  rw [h, Nat.pow_mod]
  have hb := Nat.mod_lt n (by decide : 0 < 4)
  generalize n % 4 = v at *
  interval_cases v <;> decide

lemma gap_strict {a c d b : ℕ} (hac : a < c) (hcd : c < d)
    (he : a ^ 6 + b ^ 6 = c ^ 6 + d ^ 6) : b - d < c - a := by
  by_contra! h
  let u := c - a
  have hu : 0 < u := by dsimp [u]; omega
  have had : a < d := by omega
  let f (x : ℕ) := u * (2*x + u) * (3*x^2 + 3*x*u + u^2) * (x^2 + x*u + u^2)
  have expand (x : ℕ) : (x+u)^6 = x^6 + f x := by dsimp [f]; ring
  have grows : f a < f d := by
    dsimp [f]
    gcongr
  have low : a + u = c := by dsimp [u]; omega
  have high : d + u ≤ b := by dsimp [u]; omega
  have bound := Nat.pow_le_pow_left high 6
  rw [expand] at bound
  rw [← low, expand] at he
  omega

lemma primitive_impossible (oneCase : H1) (mixedCase : H2)
    {a c d b : ℕ} (ha : 0 < a) (hac : a < c) (hcd : c < d) (hdb : d < b)
    (hg : Nat.gcd (Nat.gcd a c) (Nat.gcd d b) = 1)
    (he : a ^ 6 + b ^ 6 = c ^ 6 + d ^ 6) : False := by
  have hmod := congrArg (fun t : ℕ => t % 4) he
  change (a ^ 6 + b ^ 6) % 4 = (c ^ 6 + d ^ 6) % 4 at hmod
  rw [Nat.add_mod, Nat.add_mod (c ^ 6), sixth_mod_four, sixth_mod_four,
    sixth_mod_four, sixth_mod_four] at hmod
  have parity : a % 2 + b % 2 = c % 2 + d % 2 := by omega
  have gap := gap_strict hac hcd he
  have gapTwo : b - d + 2 ≤ c - a := by omega
  rcases (show a % 2 + b % 2 = 0 ∨ a % 2 + b % 2 = 1 ∨ a % 2 + b % 2 = 2 by omega) with h | h | h
  · have hdiv : 2 ∣ Nat.gcd (Nat.gcd a c) (Nat.gcd d b) :=
      Nat.dvd_gcd (Nat.dvd_gcd (by omega) (by omega)) (Nat.dvd_gcd (by omega) (by omega))
    rw [hg] at hdiv
    omega
  · exact mixedCase a c d b ha hac hcd hdb hg gapTwo h (by omega) he
  · exact oneCase a c d b ha hac hcd hdb hg gapTwo (by omega) (by omega) (by omega) (by omega) he

lemma nested_impossible (oneCase : H1) (mixedCase : H2)
    {a c d b : ℕ} (ha : 0 < a) (hac : a < c) (hcd : c < d) (hdb : d < b)
    (he : a ^ 6 + b ^ 6 = c ^ 6 + d ^ 6) : False := by
  let g := Nat.gcd (Nat.gcd a c) (Nat.gcd d b)
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ (Nat.gcd_pos_of_pos_left _ ha)
  have h₁ : g ∣ Nat.gcd a c := Nat.gcd_dvd_left _ _
  have h₂ : g ∣ Nat.gcd d b := Nat.gcd_dvd_right _ _
  obtain ⟨A, hA⟩ := h₁.trans (Nat.gcd_dvd_left a c)
  obtain ⟨C, hC⟩ := h₁.trans (Nat.gcd_dvd_right a c)
  obtain ⟨D, hD⟩ := h₂.trans (Nat.gcd_dvd_left d b)
  obtain ⟨B, hB⟩ := h₂.trans (Nat.gcd_dvd_right d b)
  have hn : Nat.gcd (Nat.gcd A C) (Nat.gcd D B) = 1 := by
    apply Nat.eq_of_mul_eq_mul_left hg
    calc
      g * Nat.gcd (Nat.gcd A C) (Nat.gcd D B) = Nat.gcd (Nat.gcd (g*A) (g*C)) (Nat.gcd (g*D) (g*B)) := by simp only [Nat.gcd_mul_left]
      _ = g * 1 := by rw [← hA, ← hC, ← hD, ← hB, Nat.mul_one]
  have hApos : 0 < A := by by_contra! h; simp [show A = 0 by omega] at hA; omega
  rw [hA, hC] at hac
  rw [hC, hD] at hcd
  rw [hD, hB] at hdb
  rw [hA, hB, hC, hD] at he
  simp only [mul_pow, ← Nat.mul_add] at he
  exact primitive_impossible oneCase mixedCase hApos (Nat.lt_of_mul_lt_mul_left hac)
    (Nat.lt_of_mul_lt_mul_left hcd) (Nat.lt_of_mul_lt_mul_left hdb) hn
    (Nat.eq_of_mul_eq_mul_left (pow_pos hg 6) he)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a088677.main := by
  intro oneCase mixedCase a b c d ha hab hc hcd he
  rcases lt_trichotomy a c with h | h | h
  · have hdb : d < b := by
      by_contra! hn
      have h₁ : a ^ 6 < c ^ 6 := Nat.pow_lt_pow_left h (by decide)
      have h₂ : b ^ 6 ≤ d ^ 6 := Nat.pow_le_pow_left hn 6
      omega
    exact (nested_impossible oneCase mixedCase ha h hcd hdb he).elim
  · subst c
    have hb : b ^ 6 = d ^ 6 := by omega
    exact ⟨rfl, (Nat.pow_left_inj (by decide : 6 ≠ 0)).mp hb⟩
  · have hbd : b < d := by
      by_contra! hn
      have h₁ : c ^ 6 < a ^ 6 := Nat.pow_lt_pow_left h (by decide)
      have h₂ : d ^ 6 ≤ b ^ 6 := Nat.pow_le_pow_left hn 6
      omega
    exact (nested_impossible oneCase mixedCase hc h hab hbd he.symm).elim

end OMA.R_oeis_a088677_R1
