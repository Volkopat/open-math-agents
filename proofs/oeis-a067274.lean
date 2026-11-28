import OMAStatements.S_oeis_a067274

-- Problem: A067274, integer-root quadratics x^2 + b x + c with |b|, |c| <= n.
-- Upstream: statements/oeis-a067274.lean (declaration OMA.S_oeis_a067274.main)
--
-- Proof outline. The pairs counted by a(n) but not by a(n-1) are those on the boundary of the
-- box. Writing the polynomial as (x - r)(x - s):
-- * |c| < n forces b = n or b = -n, and then {r, s} is {0, n} or {1, n - 1} up to sign,
--   so c is 0 or n - 1: four pairs.
-- * c = -n gives one pair per divisor d of n (roots d and -n/d); c = n needs a divisor
--   strictly between 1 and n.
-- For a prime p this leaves exactly six new pairs. At n = 1 there are three, and for a
-- composite n a nontrivial divisor d gives a seventh pair (n/d - d, -n).

namespace OMA.P067274

open OMA.S_oeis_a067274

open Classical

/-- The pairs counted by `a n`. -/
noncomputable def P (n : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n).filter (fun p => IntRoots p.1 p.2)

lemma a_eq (n : ℕ) : a n = (P n).card := rfl

lemma mem_P {n : ℕ} {b c : ℤ} :
    (b, c) ∈ P n ↔ -(n : ℤ) ≤ b ∧ b ≤ n ∧ -(n : ℤ) ≤ c ∧ c ≤ n ∧ IntRoots b c := by
  simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  tauto

lemma P_mono (n : ℕ) : P (n - 1) ⊆ P n := by
  rintro ⟨b, c⟩ h
  rw [mem_P] at h ⊢
  have : ((n - 1 : ℕ) : ℤ) ≤ n := by exact_mod_cast Nat.sub_le n 1
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨by linarith, by linarith, by linarith, by linarith, h5⟩

lemma diff_eq (n : ℕ) : (a n : ℤ) - a (n - 1) = ((P n) \ (P (n - 1))).card := by
  rw [a_eq, a_eq, Finset.card_sdiff_of_subset (P_mono n),
    Nat.cast_sub (Finset.card_le_card (P_mono n))]

/-- The pairs that are new at level `n`: on the boundary of the box. -/
lemma mem_new {n : ℕ} (hn : 1 ≤ n) {b c : ℤ} : (b, c) ∈ P n \ P (n - 1) ↔
    IntRoots b c ∧ -(n : ℤ) ≤ b ∧ b ≤ n ∧ -(n : ℤ) ≤ c ∧ c ≤ n ∧
      (b = n ∨ b = -n ∨ c = n ∨ c = -n) := by
  rw [Finset.mem_sdiff, mem_P, mem_P]
  have hc : ((n - 1 : ℕ) : ℤ) = n - 1 := by omega
  rw [hc]
  constructor
  · rintro ⟨⟨h1, h2, h3, h4, h5⟩, h6⟩
    refine ⟨h5, h1, h2, h3, h4, ?_⟩
    by_contra h
    simp only [not_or] at h
    exact h6 ⟨by omega, by omega, by omega, by omega, h5⟩
  · rintro ⟨h5, h1, h2, h3, h4, h6⟩
    refine ⟨⟨h1, h2, h3, h4, h5⟩, ?_⟩
    rintro ⟨g1, g2, g3, g4, -⟩
    omega

/-- Roots summing to `n` whose product is smaller than `n` in size: the product is `0` or `n - 1`. -/
lemma side {n r s : ℤ} (hn : 1 ≤ n) (h1 : r + s = n) (h2 : -n < r * s) (h3 : r * s < n) :
    r * s = 0 ∨ r * s = n - 1 := by
  have hs : s = n - r := by linarith
  subst hs
  rcases (show r ≤ -1 ∨ r = 0 ∨ r = 1 ∨ (2 ≤ r ∧ r ≤ n - 2) ∨ r = n - 1 ∨ r = n ∨ n + 1 ≤ r by
    omega) with h | h | h | h | h | h | h
  · exfalso
    nlinarith [mul_nonneg (show (0:ℤ) ≤ -1 - r by linarith) (show (0:ℤ) ≤ n by linarith),
      mul_nonneg (show (0:ℤ) ≤ -1 - r by linarith) (show (0:ℤ) ≤ -1 - r by linarith)]
  · left; subst h; ring
  · right; subst h; ring
  · exfalso
    nlinarith [mul_nonneg (show (0:ℤ) ≤ r - 2 by linarith) (show (0:ℤ) ≤ n - r - 2 by linarith)]
  · right; subst h; ring
  · left; subst h; ring
  · exfalso
    nlinarith [mul_nonneg (show (0:ℤ) ≤ r - n - 1 by linarith) (show (0:ℤ) ≤ r by linarith)]

lemma int_eq_pm {x : ℤ} {m : ℕ} (h : x.natAbs = m) : x = m ∨ x = -(m : ℤ) := by
  rcases Int.natAbs_eq x with hx | hx <;> rw [h] at hx
  · left; exact hx
  · right; exact hx

/-- A factorisation of `±p` over `ℤ`, for a prime `p`. -/
lemma prime_factor {p : ℕ} (hp : p.Prime) {r s : ℤ} (h : r.natAbs * s.natAbs = p) :
    (r = 1 ∨ r = -1) ∧ (s = p ∨ s = -(p : ℤ)) ∨ (r = p ∨ r = -(p : ℤ)) ∧ (s = 1 ∨ s = -1) := by
  have hd : r.natAbs ∣ p := ⟨s.natAbs, h.symm⟩
  rcases hp.eq_one_or_self_of_dvd _ hd with h1 | h1
  · left
    rw [h1, one_mul] at h
    exact ⟨by simpa using int_eq_pm h1, int_eq_pm h⟩
  · right
    rw [h1] at h
    have hs : s.natAbs = 1 := Nat.eq_of_mul_eq_mul_left hp.pos (h.trans (mul_one p).symm)
    exact ⟨int_eq_pm h1, by simpa using int_eq_pm hs⟩

/-- At a prime level exactly six pairs are new. -/
lemma new_prime {p : ℕ} (hp : p.Prime) :
    P p \ P (p - 1) = {((p : ℤ), 0), (-(p : ℤ), 0), ((p : ℤ), (p : ℤ) - 1), (-(p : ℤ), (p : ℤ) - 1),
      ((p : ℤ) - 1, -(p : ℤ)), (1 - (p : ℤ), -(p : ℤ))} := by
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  ext ⟨b, c⟩
  rw [mem_new hp.one_le]
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨r, s, rfl, rfl⟩, h1, h2, h3, h4, h5⟩
    by_cases hc : r * s = p ∨ r * s = -(p : ℤ)
    · have hab : r.natAbs * s.natAbs = p := by
        rw [← Int.natAbs_mul]
        rcases hc with hc | hc <;> rw [hc] <;> simp
      clear h5 h3 h4
      rcases prime_factor hp hab with ⟨hr, hs⟩ | ⟨hr, hs⟩ <;>
        rcases hr with rfl | rfl <;> rcases hs with rfl | rfl <;> clear hab hc <;>
        ring_nf at h1 h2 ⊢ <;> first | omega | simp
    · rw [not_or] at hc
      have hlo : -(p : ℤ) < r * s := lt_of_le_of_ne h3 (fun h => hc.2 h.symm)
      have hhi : r * s < (p : ℤ) := lt_of_le_of_ne h4 hc.1
      have hb : -(r + s) = p ∨ -(r + s) = -(p : ℤ) := by omega
      rcases hb with hb | hb
      · have := side (by omega : (1 : ℤ) ≤ p) (show -r + -s = p by linarith)
          (by rw [neg_mul_neg]; exact hlo) (by rw [neg_mul_neg]; exact hhi)
        rw [neg_mul_neg] at this
        omega
      · have := side (by omega : (1 : ℤ) ≤ p) (show r + s = p by linarith) hlo hhi
        omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨⟨0, -(p : ℤ), by ring, by ring⟩, by omega, by omega, by omega, by omega, by omega⟩
    · exact ⟨⟨0, (p : ℤ), by ring, by ring⟩, by omega, by omega, by omega, by omega, by omega⟩
    · exact ⟨⟨-1, 1 - (p : ℤ), by ring, by ring⟩, by omega, by omega, by omega, by omega, by omega⟩
    · exact ⟨⟨1, (p : ℤ) - 1, by ring, by ring⟩, by omega, by omega, by omega, by omega, by omega⟩
    · exact ⟨⟨1, -(p : ℤ), by ring, by ring⟩, by omega, by omega, by omega, by omega, by omega⟩
    · exact ⟨⟨-1, (p : ℤ), by ring, by ring⟩, by omega, by omega, by omega, by omega, by omega⟩

/-- At level `1` exactly three pairs are new. -/
lemma new_one : P 1 \ P (1 - 1) = {(1, 0), (-1, 0), (0, -1)} := by
  ext ⟨b, c⟩
  rw [mem_new le_rfl]
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Nat.cast_one]
  constructor
  · rintro ⟨⟨r, s, rfl, rfl⟩, h1, h2, h3, h4, h5⟩
    by_cases hc : r * s = 0
    · omega
    · have hab : r.natAbs * s.natAbs = 1 := by
        rw [← Int.natAbs_mul]
        have : r * s = 1 ∨ r * s = -1 := by omega
        rcases this with h | h <;> rw [h] <;> rfl
      have hr : r.natAbs = 1 := Nat.eq_one_of_mul_eq_one_right hab
      have hs : s.natAbs = 1 := Nat.eq_one_of_mul_eq_one_left hab
      rcases int_eq_pm hr with rfl | rfl <;> rcases int_eq_pm hs with rfl | rfl <;> norm_num at *
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨⟨0, -1, by ring, by ring⟩, by omega, by omega, by omega, by omega, by omega⟩
    · exact ⟨⟨0, 1, by ring, by ring⟩, by omega, by omega, by omega, by omega, by omega⟩
    · exact ⟨⟨1, -1, by ring, by ring⟩, by omega, by omega, by omega, by omega, by omega⟩

/-- At a composite level at least seven pairs are new. -/
lemma new_composite {n : ℕ} (h2 : 2 ≤ n) (hnp : ¬ n.Prime) : 7 ≤ (P n \ P (n - 1)).card := by
  obtain ⟨d, ⟨e, rfl⟩, hd2, hdn⟩ := Nat.exists_dvd_of_not_prime2 h2 hnp
  have he2 : 2 ≤ e := by
    rcases Nat.lt_or_ge e 2 with h | h
    · interval_cases e <;> simp at hdn
    · exact h
  have h2d : 2 * d ≤ d * e := by nlinarith
  have h2e : 2 * e ≤ d * e := by nlinarith
  set N : ℕ := d * e with hN
  have hN4 : 4 ≤ N := by nlinarith
  have zd : (2 : ℤ) * d ≤ N := by exact_mod_cast h2d
  have ze : (2 : ℤ) * e ≤ N := by exact_mod_cast h2e
  have z4 : (4 : ℤ) ≤ N := by exact_mod_cast hN4
  have zde : (d : ℤ) * e = N := by exact_mod_cast hN.symm
  have zd2 : (2 : ℤ) ≤ d := by exact_mod_cast hd2
  have ze2 : (2 : ℤ) ≤ e := by exact_mod_cast he2
  let S : Finset (ℤ × ℤ) := {((N : ℤ), 0), (-(N : ℤ), 0), ((N : ℤ), (N : ℤ) - 1),
    (-(N : ℤ), (N : ℤ) - 1), ((N : ℤ) - 1, -(N : ℤ)), (1 - (N : ℤ), -(N : ℤ)), ((e : ℤ) - d, -(N : ℤ))}
  have hsub : S ⊆ P N \ P (N - 1) := by
    rintro ⟨b, c⟩ hx
    simp only [S, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hx
    rw [mem_new (by omega)]
    rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩
    · exact ⟨⟨0, -(N : ℤ), by ring, by ring⟩, by omega, by omega, by omega, by omega, by omega⟩
    · exact ⟨⟨0, (N : ℤ), by ring, by ring⟩, by omega, by omega, by omega, by omega, by omega⟩
    · exact ⟨⟨-1, 1 - (N : ℤ), by ring, by ring⟩, by omega, by omega, by omega, by omega, by omega⟩
    · exact ⟨⟨1, (N : ℤ) - 1, by ring, by ring⟩, by omega, by omega, by omega, by omega, by omega⟩
    · exact ⟨⟨1, -(N : ℤ), by ring, by ring⟩, by omega, by omega, by omega, by omega, by omega⟩
    · exact ⟨⟨-1, (N : ℤ), by ring, by ring⟩, by omega, by omega, by omega, by omega, by omega⟩
    · exact ⟨⟨(d : ℤ), -(e : ℤ), by ring, by rw [← zde]; ring⟩, by omega, by omega, by omega,
        by omega, by omega⟩
  have hcard : S.card = 7 := by
    simp only [S]
    repeat rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert,
      Finset.mem_singleton, Prod.mk.injEq, not_or]; omega)]
    rfl
  calc 7 = S.card := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

theorem main_proof : ∀ n : ℕ, 1 ≤ n → ((a n : ℤ) - a (n - 1) = 6 ↔ n.Prime) := by
  intro n hn
  rw [diff_eq]
  by_cases hp : n.Prime
  · simp only [hp, iff_true]
    have hp2 : (2 : ℤ) ≤ n := by exact_mod_cast hp.two_le
    rw [new_prime hp]
    repeat rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert,
      Finset.mem_singleton, Prod.mk.injEq, not_or]; omega)]
    rfl
  · simp only [hp, iff_false]
    rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | h2
    · rw [new_one]
      decide
    · have := new_composite h2 hp
      omega

end OMA.P067274

theorem OMA.solution : type_of% @OMA.S_oeis_a067274.main := OMA.P067274.main_proof
