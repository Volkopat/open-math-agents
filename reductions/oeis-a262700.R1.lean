import OMAStatements.S_oeis_a262700

-- Credit: @Pixelstorm44
namespace OMA.R_oeis_a262700_R1

/-- Above each cutoff, cover the counts on a finite set of primes by fewer
square classes than there are primes. A class is represented by a squarefree d. -/
def H1 : Prop :=
  ∀ B : ℕ, ∃ P D : Finset ℕ, D.card < P.card ∧
    ∀ p ∈ P, B < p ∧ p.Prime ∧
      ∃ d ∈ D, Squarefree d ∧ ∃ a : ℕ, (p ^ 2).primeCounting = d * a ^ 2

/-- At exponent four, some prime detects a failure of divisibility by four
in the sum of the two valuations. -/
def H2 : Prop :=
  ∀ x y : ℕ, 2 ≤ x → 2 ≤ y →
    ∃ r : ℕ, r.Prime ∧ ¬ 4 ∣
      ((x ^ 4).primeCounting.factorization r + (y ^ 4).primeCounting.factorization r)

/-- The corresponding local obstruction at odd prime exponents. -/
def H3 : Prop :=
  ∀ p x y : ℕ, p.Prime → 2 < p → 2 ≤ x → 2 ≤ y →
    ∃ r : ℕ, r.Prime ∧ ¬ p ∣
      ((x ^ p).primeCounting.factorization r + (y ^ p).primeCounting.factorization r)

lemma squareClassCollision (h : H1) : OMA.S_oeis_a262700.S.Infinite := by
  classical
  apply Set.infinite_iff_exists_gt.mpr
  intro B
  obtain ⟨P, D, hcard, hP⟩ := h B
  choose d hd _ a ha using fun p : P => (hP p p.property).2.2
  obtain ⟨p, q, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun p : P => (⟨d p, hd p⟩ : D)) (by simpa using hcard)
  have hclass : d p = d q := congrArg Subtype.val heq
  have hs : IsSquare (((p : ℕ) ^ 2).primeCounting * ((q : ℕ) ^ 2).primeCounting) := by
    refine ⟨d q * a p * a q, ?_⟩
    rw [ha p, ha q, hclass]
    ring
  have hp := hP p p.property
  have hq := hP q q.property
  rcases lt_or_gt_of_ne (show (p : ℕ) ≠ q from fun e => hne (Subtype.ext e)) with hlt | hgt
  · exact ⟨q, ⟨hq.2.1, p, hp.2.1, hlt, by simpa only [mul_comm] using hs⟩, hq.1⟩
  · exact ⟨p, ⟨hp.2.1, q, hq.2.1, hgt, hs⟩, hp.1⟩

/-- Strip off one factor of two when the exponent is even. Unless four
divides the exponent, the remaining cofactor is odd and greater than one. -/
lemma primitiveDivisor (n : ℕ) (hn : 2 < n) :
    ∃ k : ℕ, k ∣ n ∧ (k = 4 ∨ k.Prime ∧ 2 < k) := by
  by_cases h4 : 4 ∣ n
  · exact ⟨4, h4, Or.inl rfl⟩
  by_cases h2 : 2 ∣ n
  · obtain ⟨m, rfl⟩ := h2
    obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd (show m ≠ 1 by omega)
    have hne : p ≠ 2 := by
      rintro rfl
      omega
    exact ⟨p, dvd_mul_of_dvd_right hd 2, Or.inr ⟨hp, lt_of_le_of_ne hp.two_le (Ne.symm hne)⟩⟩
  · obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
    have hne : p ≠ 2 := fun e => h2 (e ▸ hd)
    exact ⟨p, hd, Or.inr ⟨hp, lt_of_le_of_ne hp.two_le (Ne.symm hne)⟩⟩

lemma exponentObstruction {k : ℕ}
    (h : ∀ x y : ℕ, 2 ≤ x → 2 ≤ y → ∃ r : ℕ, r.Prime ∧ ¬ k ∣
      ((x ^ k).primeCounting.factorization r + (y ^ k).primeCounting.factorization r))
    (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (x ^ k).primeCounting * (y ^ k).primeCounting ≠ z ^ k := by
  intro he
  have hnz : (x ^ k).primeCounting * (y ^ k).primeCounting ≠ 0 := he ▸ pow_ne_zero _ hz.ne'
  have hx2 : 2 ≤ x := by
    by_contra! hsmall
    obtain rfl : x = 1 := by omega
    simp at hnz
  have hy2 : 2 ≤ y := by
    by_contra! hsmall
    obtain rfl : y = 1 := by omega
    simp at hnz
  obtain ⟨r, _, hr⟩ := h x y hx2 hy2
  apply hr
  refine ⟨z.factorization r, ?_⟩
  have hf := congrArg (fun t : ℕ => t.factorization r) he
  simpa [Nat.factorization_mul (left_ne_zero_of_mul hnz) (right_ne_zero_of_mul hnz),
    Nat.factorization_pow] using hf

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a262700.main := by
  intro h1 h2 h3
  refine ⟨squareClassCollision h1, ?_⟩
  intro n x y z hn hx hy hz
  obtain ⟨k, ⟨m, rfl⟩, hk⟩ := primitiveDivisor n hn
  rw [Nat.mul_comm k m, pow_mul, pow_mul, pow_mul]
  rcases hk with rfl | ⟨hp, hgt⟩
  · exact exponentObstruction h2 _ _ _ (pow_pos hx _) (pow_pos hy _) (pow_pos hz _)
  · exact exponentObstruction (fun a b => h3 k a b hp hgt) _ _ _
      (pow_pos hx _) (pow_pos hy _) (pow_pos hz _)

end OMA.R_oeis_a262700_R1
