import OMAStatements.S_oeis_a089305

-- Reduction oeis-a089305.R1 of A089305: Smallest prime of the form n*(n+1)*(n+2)...(n+k) + 1, k > 0, i.e., a(n) > n+1, or 0 if no such prime exists.
-- Credit: @yuka30240
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_oeis_a089305_R1

private theorem asc_congr {d a b : ℕ} (h : a ≡ b [MOD d]) (m : ℕ) :
    a.ascFactorial m ≡ b.ascFactorial m [MOD d] := by
  induction m with
  | zero => rfl
  | succ m ih => simpa only [Nat.ascFactorial_succ] using (h.add_right m).mul ih

-- No finite length cutoff works, even on a single arithmetic progression.
-- Shift a positive representative by a multiple of all its first B candidates.
theorem unbounded_lengths_in_progression (a d B X : ℕ) (ha : 0 < a) (hd : 0 < d) :
    ∃ n : ℕ, X < n ∧ n ≡ a [MOD d] ∧
      ∀ m : ℕ, 2 ≤ m → m ≤ B → ¬(n.ascFactorial m + 1).Prime := by
  let D := ∏ j ∈ Finset.range (B + 1), (a.ascFactorial j + 1)
  have hD : 0 < D := Finset.prod_pos fun j _ => Nat.succ_pos _
  let n := a + (X + 1) * (d * D)
  have hstep : X + 1 ≤ (X + 1) * (d * D) :=
    Nat.le_mul_of_pos_right _ (Nat.mul_pos hd hD)
  have hlarge : X < n := by dsimp [n]; omega
  have shift (c : ℕ) (hc : c ∣ d * D) : n ≡ a [MOD c] := by
    change (a + (X + 1) * (d * D)) % c = a % c
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd (hc.trans (dvd_mul_left _ _))]
    simp
  refine ⟨n, hlarge, shift d (dvd_mul_right _ _), ?_⟩
  intro m hm hB hp
  let b := a.ascFactorial m + 1
  have hb : b ∣ D := Finset.dvd_prod_of_mem (fun j : ℕ => a.ascFactorial j + 1)
    (Finset.mem_range.2 (by omega))
  have hh := (asc_congr (shift b (hb.trans (dvd_mul_left D d))) m).add_right 1
  have hbdiv : b ∣ n.ascFactorial m + 1 := Nat.dvd_of_mod_eq_zero
    (Eq.trans (show (n.ascFactorial m + 1) % b = b % b from hh) (Nat.mod_self b))
  have pos (v : ℕ) (hv : 0 < v) : 0 < v.ascFactorial m := by
    obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hv.ne'
    exact Nat.ascFactorial_pos s m
  have hprod : n ≤ n.ascFactorial m := by
    apply Nat.le_of_dvd (pos n (by omega))
    rw [Nat.ascFactorial_eq_prod_range]
    simpa using (Finset.dvd_prod_of_mem (fun j : ℕ => n + j)
      (Finset.mem_range.2 (show 0 < m by omega)))
  have hble : b ≤ (X + 1) * (d * D) :=
    Nat.le_of_dvd (Nat.mul_pos (Nat.succ_pos X) (Nat.mul_pos hd hD))
      (hb.trans ((dvd_mul_left D d).trans (dvd_mul_left _ _)))
  rcases hp.eq_one_or_self_of_dvd b hbdiv with h | h
  · have := pos a ha
    dsimp [b] at h
    omega
  · have hshift : (X + 1) * (d * D) < n := by dsimp only [n]; omega
    exact (ne_of_lt ((hble.trans_lt hshift).trans (Nat.lt_succ_of_le hprod))) h

private theorem cast_asc_mod (n m r : ℕ) :
    ((n % r).ascFactorial m : ZMod r) = (n.ascFactorial m : ℕ) :=
  (ZMod.natCast_eq_natCast_iff _ _ _).2 (asc_congr (Nat.mod_modEq n r) m)

-- A divisor of the candidate cannot divide any term of the interval.
-- On reducing the start modulo r, the entire interval lies in [1,r).
private theorem block_in_residues {n m r : ℕ} (hm : 0 < m) (hr : r.Prime)
    (hd : r ∣ n.ascFactorial m + 1) : 0 < n % r ∧ n % r + m ≤ r := by
  have avoid (i : ℕ) (hi : i < m) : ¬ r ∣ n % r + i := by
    intro h
    have hz := (ZMod.natCast_eq_zero_iff _ _).2 h
    simp only [Nat.cast_add, ZMod.natCast_mod] at hz
    have hd' : r ∣ n + i := (ZMod.natCast_eq_zero_iff _ _).1 (by simpa using hz)
    have hprod : n + i ∣ n.ascFactorial m := by
      rw [Nat.ascFactorial_eq_prod_range]
      exact Finset.dvd_prod_of_mem (fun j => n + j) (Finset.mem_range.2 hi)
    exact hr.not_dvd_one ((Nat.dvd_add_iff_right (hd'.trans hprod)).2 hd)
  constructor
  · by_contra! h
    exact avoid 0 hm (by simp [Nat.eq_zero_of_le_zero h])
  · have ha := Nat.mod_lt n hr.pos
    by_contra! h
    apply avoid (r - n % r) (by omega)
    rw [Nat.add_sub_of_le ha.le]

-- Reflect the unused residues at the right endpoint. Wilson's theorem then
-- describes divisibility using only the two factorials outside the block.
theorem dvd_iff_wilson_complement {n m r : ℕ} (hm : 0 < m) (hr : r.Prime) :
    let a := n % r
    let t := r - (a + m)
    r ∣ n.ascFactorial m + 1 ↔ 0 < a ∧ a + m ≤ r ∧
      ((a - 1).factorial : ZMod r) * t.factorial * (-1) ^ t = 1 := by
  let : Fact r.Prime := ⟨hr⟩
  let a := n % r
  let t := r - (a + m)
  have hw (ha : 0 < a) (hend : a + m ≤ r) :
      (n.ascFactorial m : ZMod r) *
        (((a - 1).factorial : ZMod r) * t.factorial * (-1) ^ t) = -1 := by
    have hleft := congrArg (fun x : ℕ => (x : ZMod r)) (Nat.factorial_mul_ascFactorial' a m ha)
    have hright := congrArg (fun x : ℕ => (x : ZMod r))
      (Nat.factorial_mul_descFactorial (n := r - 1) (k := t) (by dsimp [t]; omega))
    have hcut : r - 1 - t = a + m - 1 := by dsimp [t]; omega
    simp only [Nat.cast_mul] at hleft
    simp only [Nat.cast_mul, hcut, ZMod.wilsons_lemma,
      ZMod.cast_descFactorial (show t ≤ r by dsimp [t]; omega)] at hright
    rw [← hleft, cast_asc_mod] at hright
    linear_combination hright
  have hdvd : r ∣ n.ascFactorial m + 1 ↔ (n.ascFactorial m : ZMod r) = -1 := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_one]
    exact add_eq_zero_iff_eq_neg
  constructor
  · intro hd
    obtain ⟨ha, hend⟩ := block_in_residues hm hr hd
    refine ⟨ha, hend, ?_⟩
    have h := hw ha hend
    rw [hdvd.1 hd] at h
    simpa only [neg_one_mul, neg_inj] using h
  · rintro ⟨ha, hend, he⟩
    change ((a - 1).factorial : ZMod r) * t.factorial * (-1) ^ t = 1 at he
    apply hdvd.2
    simpa only [he, mul_one] using hw ha hend

theorem prime_iff_wilson_sieve {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    (n.ascFactorial m + 1).Prime ↔
    ∀ r : ℕ, r.Prime → r ^ 2 ≤ n.ascFactorial m + 1 →
      let a := n % r
      let t := r - (a + m)
      0 < a → a + m ≤ r → ((a - 1).factorial : ZMod r) * t.factorial * (-1) ^ t ≠ 1 := by
  have hpos : 0 < n.ascFactorial m := by
    obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    exact Nat.ascFactorial_pos s m
  constructor
  · intro hprime r hr hrsize
    dsimp only
    intro ha hend he
    have hd := (dvd_iff_wilson_complement hm hr).2 ⟨ha, hend, he⟩
    rcases hprime.eq_one_or_self_of_dvd r hd with h | h
    · exact hr.ne_one h
    · have := hr.two_le
      nlinarith
  · intro hs
    by_contra h
    let r := (n.ascFactorial m + 1).minFac
    have hr : r.Prime := Nat.minFac_prime (by omega)
    obtain ⟨ha, he, hbad⟩ := (dvd_iff_wilson_complement hm hr).1 (Nat.minFac_dvd _)
    exact hs r hr (Nat.minFac_sq_le_self (by omega) h) ha he hbad

private theorem order_three_of_factor {n p : ℕ} (hp : p.Prime)
    (hd : p ∣ n * (n + 1) + 1) (h3 : n % 3 ≠ 1) :
    orderOf (n : ZMod p) = 3 ∧ p % 3 = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hz := (ZMod.natCast_eq_zero_iff _ _).2 hd
  push_cast at hz
  have h0 : (n : ZMod p) ≠ 0 := by
    intro he
    simp [he] at hz
  have h1 : (n : ZMod p) ≠ 1 := by
    intro he
    have hchar : (3 : ZMod p) = 0 := by linear_combination hz - (n + 2 : ZMod p) * he
    have hp3 : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).1 hchar
    rcases Nat.prime_three.eq_one_or_self_of_dvd p hp3 with h | h
    · exact hp.ne_one h
    · subst p
      have hh := (ZMod.natCast_eq_natCast_iff n 1 3).1 (by simpa using he)
      exact h3 hh
  have ho : orderOf (n : ZMod p) = 3 := by
    apply orderOf_eq_prime _ h1
    linear_combination ((n : ZMod p) - 1) * hz
  have hdiv := ZMod.orderOf_dvd_card_sub_one h0
  rw [ho] at hdiv
  exact ⟨ho, ((Nat.modEq_iff_dvd' hp.pos).2 hdiv).symm⟩

-- Lucas certificates only need primes dividing one of the interval factors.
private theorem binary_power {M : Type*} [Monoid M] (g : M) (k : ℕ) :
    npowBinRec k g = g ^ k := by
  induction k with
  | zero => rw [npowBinRec_zero, pow_zero]
  | succ k ih => rw [npowBinRec_succ, ih, pow_succ]

private theorem certified_length (n m g : ℕ) (hn : 0 < n) (hm : 2 ≤ m)
    (cert :
      let u := n.ascFactorial m
      let a : ZMod (u + 1) := g
      npowBinRec u a = 1 ∧
        ∀ q : Fin (n + m), q.val.Prime → q.val ∣ u → npowBinRec (u / q.val) a ≠ 1) :
    ∃ k : ℕ, 0 < k ∧ ((∏ i ∈ Finset.range (k + 1), (n + i)) + 1).Prime := by
  refine ⟨m - 1, by omega, ?_⟩
  rw [show m - 1 + 1 = m by omega, ← Nat.ascFactorial_eq_prod_range]
  apply lucas_primality _ (g : ZMod (n.ascFactorial m + 1))
  · simpa only [Nat.add_sub_cancel, binary_power] using cert.1
  · intro q hq hd
    simp only [Nat.add_sub_cancel] at hd ⊢
    have hprod := hd
    rw [Nat.ascFactorial_eq_prod_range, hq.prime.dvd_finsetProd_iff] at hprod
    obtain ⟨i, hi, hiq⟩ := hprod
    have hlt := Finset.mem_range.1 hi
    have hle := Nat.le_of_dvd (show 0 < n + i by omega) hiq
    simpa only [binary_power] using cert.2 ⟨q, by omega⟩ hq hd

-- Entries are (length, Lucas base) for consecutive starts 1 through 100.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem small_starts {n : ℕ} (hn : 0 < n) (h : n ≤ 100) :
    ∃ k : ℕ, 0 < k ∧ ((∏ i ∈ Finset.range (k + 1), (n + i)) + 1).Prime := by
  let witnesses : List (ℕ × ℕ) :=
    [(2, 2), (2, 3), (2, 2), (7, 11), (2, 3), (2, 3), (5, 38), (2, 5),
      (3, 6), (3, 13), (10, 23), (2, 5), (3, 3), (2, 2), (2, 7), (6, 13),
      (2, 5), (3, 22), (5, 17), (2, 2), (2, 3), (8, 17), (18, 61), (2, 7),
      (3, 3), (6, 19), (2, 2), (5, 11), (9, 26), (3, 17), (12, 23), (7, 13),
      (2, 2), (3, 23), (8, 17), (18, 71), (74, 151), (2, 2), (5, 11), (3, 22),
      (2, 3), (5, 62), (14, 31), (3, 17), (6, 11), (8, 11), (9, 46), (18, 46),
      (3, 3), (2, 6), (3, 5), (12, 37), (3, 2), (2, 10), (19, 53), (3, 5),
      (2, 2), (6, 17), (2, 7), (8, 23), (3, 5), (2, 2), (115, 223), (5, 43),
      (6, 19), (2, 3), (16, 53), (5, 44), (2, 3), (6, 38), (2, 19), (6, 29),
      (5, 31), (3, 11), (2, 2), (3, 5), (2, 3), (2, 3), (6, 17), (2, 7),
      (6, 13), (27, 67), (3, 6), (3, 11), (10, 53), (3, 5), (5, 34), (9, 34),
      (2, 14), (2, 17), (3, 2), (24, 43), (8, 41), (3, 17), (13, 47), (11, 31),
      (13, 29), (3, 13), (2, 2), (3, 11)]
  have checked : ∀ j : Fin 100,
      let t := j.val + 1
      let w := witnesses[j.val]!
      let u := t.ascFactorial w.1
      let a : ZMod (u + 1) := w.2
      2 ≤ w.1 ∧ npowBinRec u a = 1 ∧
        ∀ q : Fin (t + w.1), q.val.Prime → q.val ∣ u → npowBinRec (u / q.val) a ≠ 1 := by
    dsimp only [witnesses]
    decide +kernel
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have cert := checked ⟨j, by omega⟩
  exact certified_length (j + 1) _ _ (by omega) cert.1 cert.2

private theorem no_common_factor {n p : ℕ} (hp : p.Prime)
    (h₂ : p ∣ n * (n + 1) + 1) (h₃ : p ∣ n * (n + 1) * (n + 2) + 1) : False := by
  let : Fact p.Prime := ⟨hp⟩
  have a := (ZMod.natCast_eq_zero_iff _ _).2 h₂
  have b := (ZMod.natCast_eq_zero_iff _ _).2 h₃
  push_cast at a b
  have h : (1 : ZMod p) = 0 := by
    linear_combination (1 - (n : ZMod p) * (n + 2)) * a + (n : ZMod p) * b
  exact one_ne_zero h

-- Length two gives the third cyclotomic polynomial. Its exceptional prime
-- divisor is 3. Length three gives a second, coprime polynomial value.
-- Length four gives the square of n² + 3n + 1. The remaining search thus
-- starts at length five in both families.
def H1 : Prop :=
  ∀ n q : ℕ, 100 < n → n % 3 = 1 →
    q.Prime → q ^ 2 ≤ n * (n + 1) * (n + 2) + 1 →
    q ∣ n * (n + 1) * (n + 2) + 1 →
    ∃ m : ℕ, 5 ≤ m ∧ ∀ r : ℕ, r.Prime → r ^ 2 ≤ n.ascFactorial m + 1 →
      let a := n % r
      let t := r - (a + m)
      0 < a → a + m ≤ r → ((a - 1).factorial : ZMod r) * t.factorial * (-1) ^ t ≠ 1

def H2 : Prop :=
  ∀ n p q : ℕ, 100 < n → n % 3 ≠ 1 →
    p.Prime → p ≤ n → p % 3 = 1 → orderOf (n : ZMod p) = 3 →
    q.Prime → p ≠ q → q ^ 2 ≤ n * (n + 1) * (n + 2) + 1 →
    q ∣ n * (n + 1) * (n + 2) + 1 →
    ∃ m : ℕ, 5 ≤ m ∧ ∀ r : ℕ, r.Prime → r ^ 2 ≤ n.ascFactorial m + 1 →
      let a := n % r
      let t := r - (a + m)
      0 < a → a + m ≤ r → ((a - 1).factorial : ZMod r) * t.factorial * (-1) ^ t ≠ 1

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a089305.main := by
  intro h₁ h₂ n hn
  by_cases hsmall : n ≤ 100
  · exact small_starts hn hsmall
  by_cases ha : (n * (n + 1) + 1).Prime
  · exact ⟨1, by decide, by simpa [Finset.prod_range_succ, Nat.mul_comm] using ha⟩
  by_cases hb : (n * (n + 1) * (n + 2) + 1).Prime
  · exact ⟨2, by decide, by simpa [Finset.prod_range_succ] using hb⟩
  let q := (n * (n + 1) * (n + 2) + 1).minFac
  have hq : q.Prime := Nat.minFac_prime (by
    exact (Nat.succ_lt_succ (Nat.mul_pos (Nat.mul_pos hn n.succ_pos) (n + 1).succ_pos)).ne')
  have hqd : q ∣ n * (n + 1) * (n + 2) + 1 := Nat.minFac_dvd _
  have hqs := Nat.minFac_sq_le_self (by positivity) hb
  suffices h : ∃ m : ℕ, 5 ≤ m ∧ (n.ascFactorial m + 1).Prime by
    obtain ⟨m, hm, hprime⟩ := h
    exact ⟨m - 1, by omega, by rwa [show m - 1 + 1 = m by omega, ← Nat.ascFactorial_eq_prod_range]⟩
  by_cases h3 : n % 3 = 1
  · obtain ⟨m, hm, hs⟩ := h₁ n q (by omega) h3 hq hqs hqd
    exact ⟨m, hm, (prime_iff_wilson_sieve hn (by omega)).2 hs⟩
  · let p := (n * (n + 1) + 1).minFac
    have hp : p.Prime := Nat.minFac_prime (by nlinarith)
    have hpd : p ∣ n * (n + 1) + 1 := Nat.minFac_dvd _
    have hps : p ^ 2 ≤ n * (n + 1) + 1 := Nat.minFac_sq_le_self (by positivity) ha
    have hpn : p ≤ n := by
      by_contra! h
      nlinarith [Nat.mul_self_le_mul_self h]
    have hne : p ≠ q := fun h => no_common_factor hp hpd (h ▸ hqd)
    obtain ⟨horder, hres⟩ := order_three_of_factor hp hpd h3
    obtain ⟨m, hm, hs⟩ := h₂ n p q (by omega) h3 hp hpn hres horder hq hne hqs hqd
    exact ⟨m, hm, (prime_iff_wilson_sieve hn (by omega)).2 hs⟩

end OMA.R_oeis_a089305_R1
