import OMAStatements.S_oeis_a088256

-- Reduction oeis-a088256.R1 of the finiteness conjecture for twin primorial primes.
-- Credit: @Pixelstorm44

namespace OMA.R_oeis_a088256_R1
open OMA.S_oeis_a088256 renaming primorial → primorialAt

private theorem primorial_shape (n : ℕ) :
    ∃ m, primorialAt (n+2) = 12*m+6 := by
  induction n with
  | zero =>
    exact ⟨0, by simp [primorialAt, Finset.prod_range_succ, Nat.nth_prime_zero_eq_two,
      Nat.nth_prime_one_eq_three]⟩
  | succ n ih =>
    obtain ⟨m, hm⟩ := ih
    let a := Nat.nth Nat.Prime (n+2)
    have ha : 2 < a := by
      calc
        2 = Nat.nth Nat.Prime 0 := Nat.nth_prime_zero_eq_two.symm
        _ < a := Nat.nth_strictMono Nat.infinite_setOfPred_prime (by omega)
    have ho := (Nat.prime_nth_prime (n+2)).eq_two_or_odd.resolve_left (by change a ≠ 2; omega)
    change a % 2 = 1 at ho
    have he : a = 2*(a/2)+1 := by omega
    refine ⟨2*m*(a/2)+m+a/2, ?_⟩
    change primorialAt ((n+2)+1) = _
    rw [show primorialAt ((n+2)+1) = primorialAt (n+2)*a from Finset.prod_range_succ .., hm]
    conv_lhs => rw [he]
    ring

private theorem neighbor_symbols {P a : ℕ} (shape : P % 4 = 2) (large : 6 ≤ P)
    (ha : a.Prime) (odd : a ≠ 2) (divides : a ∣ P)
    (hm : (P-1).Prime) (hp : (P+1).Prime) :
    letI : Fact (P-1).Prime := ⟨hm⟩
    letI : Fact (P+1).Prime := ⟨hp⟩
    legendreSym (P-1) a = (-1 : ℤ)^(a/2) ∧ legendreSym (P+1) a = (-1 : ℤ)^(a/2) := by
  let : Fact (P-1).Prime := ⟨hm⟩
  let : Fact (P+1).Prime := ⟨hp⟩
  let : Fact a.Prime := ⟨ha⟩
  have hz := (ZMod.natCast_eq_zero_iff P a).2 divides
  have hn : ((P-1 : ℕ) : ZMod a) = -1 := by
    rw [Nat.cast_sub (by omega), hz]
    simp
  have hm' : legendreSym a (P-1 : ℕ) = legendreSym a (-1) := by
    simp only [legendreSym, Int.cast_natCast, Int.cast_neg, Int.cast_one, hn]
  have hp' : legendreSym a (P+1 : ℕ) = legendreSym a 1 := by
    simp [legendreSym, hz]
  constructor
  · rw [← legendreSym.quadratic_reciprocity_one_mod_four (p := P-1) (q := a) (by omega) odd,
        hm', legendreSym.at_neg_one odd, ZMod.χ₄_eq_neg_one_pow (ha.eq_two_or_odd.resolve_left odd)]
  · rw [legendreSym.quadratic_reciprocity' (p := a) odd (by omega),
        Nat.mul_comm (a/2), pow_mul, ZMod.neg_one_pow_div_two_of_three_mod_four (by omega),
        hp', legendreSym.at_one, mul_one]

/-- A simultaneous Euler test modulo the product of the two neighbors. -/
theorem euler_test_of_twins {P : ℕ} (shape : P % 4 = 2) (large : 6 ≤ P)
    (hm : (P-1).Prime) (hp : (P+1).Prime) :
    ∀ a : ℕ, a.Prime → a ≠ 2 → a ∣ P →
    ((P-1 : ℕ) : ℤ) * (P+1 : ℕ) ∣
      2*(a : ℤ)^(P/2) - (-1 : ℤ)^(a/2) * (((a : ℤ)-1)*P+a+1) := by
  intro a ha odd divides
  let : Fact (P-1).Prime := ⟨hm⟩
  let : Fact (P+1).Prime := ⟨hp⟩
  obtain ⟨sm, sp⟩ := neighbor_symbols shape large ha odd divides hm hp
  have em := legendreSym.eq_pow (P-1) a
  have ep := legendreSym.eq_pow (P+1) a
  rw [sm, Int.cast_natCast] at em
  rw [sp, Int.cast_natCast] at ep
  push_cast at em ep
  apply ((Nat.coprime_primes hm hp).2 (by omega)).isCoprime.mul_dvd
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1
    push_cast
    have hP : (P : ZMod (P-1)) = 1 := by
      have h := ZMod.natCast_self (P-1)
      rw [Nat.cast_sub (by omega), Nat.cast_one] at h
      exact sub_eq_zero.mp h
    rw [hP, show P/2 = (P-1)/2+1 by omega, pow_succ, ← em]
    ring
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1
    push_cast
    have hP : (P : ZMod (P+1)) = -1 := by
      have h := ZMod.natCast_self (P+1)
      push_cast at h
      linear_combination h
    rw [hP, show P/2 = (P+1)/2 by omega, ← ep]
    ring

/-- A fourth-root test at the lower neighbor and two cubic-character cases at the upper neighbor. -/
theorem profiles_of_twins {m P : ℕ} (shape : P = 12*m+6)
    (hm : (P-1).Prime) (hp : (P+1).Prime) :
    let sign (a : ℕ) : ℤ := (-1)^(a/2)
    let Base (P a : ℕ) : Prop := a.Prime ∧ a ≠ 2 ∧ a ∣ P
    let fourth (P a : ℕ) : ZMod (P-1) := (a : ZMod (P-1))^((P-2)/4)
    let third (P a : ℕ) : ZMod (P+1) := (sign a : ZMod (P+1)) * (a : ZMod (P+1))^(P/6)
    let QuarticTest (P : ℕ) : Prop :=
      fourth P 3 ^ 2 = -1 ∧ ∀ a, Base P a →
        let v := if sign a = 1 then 1 else fourth P 3
        fourth P a = v ∨ fourth P a = -v
    let AllCubes (P : ℕ) : Prop := ∀ a, Base P a → third P a = 1
    let CommonRoot (P : ℕ) : Prop :=
      ∃ b, Base P b ∧ third P b ≠ 1 ∧ third P b ^ 2 + third P b + 1 = 0 ∧
        ∀ a, Base P a → ∃ i < 3, third P a = third P b ^ i
    QuarticTest P ∧ (AllCubes P ∨ CommonRoot P) := by
  intro sign Base fourth third QuarticTest AllCubes CommonRoot
  let : Fact (P-1).Prime := ⟨hm⟩
  let : Fact (P+1).Prime := ⟨hp⟩
  have lower (a : ℕ) (ha : Base P a) : fourth P a ^ 2 = (sign a : ZMod (P-1)) := by
    have h := (neighbor_symbols (by omega) (by omega) ha.1 ha.2.1 ha.2.2 hm hp).1
    dsimp only [fourth]
    change _ = (((-1 : ℤ)^(a/2) : ℤ) : ZMod (P-1))
    rw [← pow_mul, show (P-2)/4*2 = (P-1)/2 by omega, ← h]
    simpa using (legendreSym.eq_pow (P-1) a).symm
  have upper (a : ℕ) (ha : Base P a) : third P a ^ 3 = 1 := by
    have h := (neighbor_symbols (by omega) (by omega) ha.1 ha.2.1 ha.2.2 hm hp).2
    have he := legendreSym.eq_pow (P+1) a
    rw [h, Int.cast_natCast] at he
    change (sign a : ZMod (P+1)) = _ at he
    dsimp only [third]
    rw [mul_pow, ← pow_mul, show P/6*3 = (P+1)/2 by omega, ← he, ← pow_succ]
    rcases neg_one_pow_eq_or ℤ (a/2) with hs | hs <;> simp [sign, hs] <;> norm_num
  have h3 : Base P 3 := ⟨Nat.prime_three, by decide, ⟨4*m+2, by omega⟩⟩
  have root : fourth P 3 ^ 2 = -1 := by simpa [sign] using lower 3 h3
  constructor
  · refine ⟨root, ?_⟩
    intro a ha
    dsimp only
    split_ifs with h
    · apply sq_eq_one_iff.mp
      rw [lower a ha, h, Int.cast_one]
    · apply sq_eq_sq_iff_eq_or_eq_neg.mp
      have hs : sign a = -1 := by
        rcases neg_one_pow_eq_or (R := ℤ) (a/2) with h' | h'
        · exact (h h').elim
        · exact h'
      rw [lower a ha, root, hs]
      norm_num
  · by_cases h : AllCubes P
    · exact Or.inl h
    · right
      dsimp only [AllCubes] at h
      push Not at h
      obtain ⟨b, hb, hne⟩ := h
      let z := third P b
      have hz : z^3 = 1 := upper b hb
      have hfac : (z-1)*(z^2+z+1) = 0 := by linear_combination hz
      have hquad := (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hne)
      have hprim : IsPrimitiveRoot z 3 :=
        isPrimitiveRoot_of_mem_nthRootsFinset Nat.prime_three
          ((Polynomial.mem_nthRootsFinset (by decide : 0 < 3) 1).mpr hz) hne
      refine ⟨b, hb, hne, hquad, ?_⟩
      intro a ha
      obtain ⟨i, hi, he⟩ := hprim.eq_pow_of_pow_eq_one (upper a ha)
      exact ⟨i, hi, he.symm⟩

/-- Finiteness for the primorial indices passing the lower test when every upper
    base has trivial cubic character. -/
def H1 : Prop := Set.Finite {n : ℕ |
    let P := primorialAt (n+2)
    let sign (a : ℕ) : ℤ := (-1)^(a/2)
    let base (a : ℕ) : Prop := a.Prime ∧ a ≠ 2 ∧ a ∣ P
    let fourth (a : ℕ) : ZMod (P-1) := (a : ZMod (P-1))^((P-2)/4)
    let third (a : ℕ) : ZMod (P+1) := (sign a : ZMod (P+1)) * (a : ZMod (P+1))^(P/6)
    let lower := fourth 3 ^ 2 = -1 ∧ ∀ a, base a →
        let v := if sign a = 1 then 1 else fourth 3
        fourth a = v ∨ fourth a = -v
    lower ∧ ∀ a, base a → third a = 1}

/-- Finiteness for the indices passing the lower test when the upper bases
    produce a common nontrivial cubic root of unity. -/
def H2 : Prop := Set.Finite {n : ℕ |
    let P := primorialAt (n+2)
    let sign (a : ℕ) : ℤ := (-1)^(a/2)
    let base (a : ℕ) : Prop := a.Prime ∧ a ≠ 2 ∧ a ∣ P
    let fourth (a : ℕ) : ZMod (P-1) := (a : ZMod (P-1))^((P-2)/4)
    let third (a : ℕ) : ZMod (P+1) := (sign a : ZMod (P+1)) * (a : ZMod (P+1))^(P/6)
    let lower := fourth 3 ^ 2 = -1 ∧ ∀ a, base a →
        let v := if sign a = 1 then 1 else fourth 3
        fourth a = v ∨ fourth a = -v
    lower ∧ ∃ b, base b ∧ third b ≠ 1 ∧ third b ^ 2 + third b + 1 = 0 ∧
        ∀ a, base a → ∃ i < 3, third a = third b ^ i}

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a088256.main := by
  intro h₁ h₂
  apply ((h₁.union h₂).image (fun n => primorialAt (n+2))).subset
  rintro P ⟨⟨n, rfl⟩, hm, hp⟩
  match n with
  | 0 => exact (Nat.not_prime_zero (by simpa [primorialAt] using hm)).elim
  | 1 => exact (Nat.not_prime_one (by simpa [primorialAt, Nat.nth_prime_zero_eq_two] using hm)).elim
  | n+2 =>
    obtain ⟨m, shape⟩ := primorial_shape n
    obtain ⟨lower, upper⟩ := profiles_of_twins shape hm hp
    refine ⟨n, ?_, rfl⟩
    exact upper.elim (fun h => Or.inl ⟨lower, h⟩) (fun h => Or.inr ⟨lower, h⟩)

end OMA.R_oeis_a088256_R1
