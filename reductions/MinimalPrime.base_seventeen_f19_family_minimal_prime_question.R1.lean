import FormalConjectures.Wikipedia.MinimalPrime

/-!
# The unresolved base-17 F19...9 family: digital closure and an arithmetic reduction

The first prime, if any, in this family is minimal in base 17. We prove this
precisely: every prime digit-subsequence is another member of the same family,
and a family member is minimal exactly when it is the first prime member.
The proof classifies all sublists and excludes the other three digit patterns.
In particular the 19...9 pattern is excluded for every length, using parity and
an explicit integral factorization, rather than bounded computation.

We also prove that every prime family member has exponent 3 modulo 6, with
certificates modulo 2, 7 and 13, and identify its value exactly as
(4105 * 17^k - 9) / 16. Thus `existence_iff` is an unconditional equivalence
between the catalog question and H2, a pure arithmetic existence question.

This is NOT a proof that the family contains a prime. H1 (digital closure) is
fully discharged by `prime_subsequence` in this file; H2 remains unresolved.
`main` uses both steps explicitly, in the required two-step reduction format.

The family and exclusion of its other digit patterns come from C. Bright,
R. Devillers and J. Shallit, "Minimal elements for the prime numbers",
Experimental Mathematics 25 (2016), 321-331. See also Bright's slides:
https://cs.uwaterloo.ca/~cbright/talks/minimal-slides.pdf
This submission formalizes that structural argument; it does not claim a new
primality discovery. Lists in the Lean proofs put the least significant digit first.
-/

namespace OMA.R_MinimalPrime_base_seventeen_f19_family_minimal_prime_question_R1
open MinimalPrime

/-- Digital closure: any prime subsequence stays in the same family. This step
is proved in full below, in `prime_subsequence`. -/
def H1 : Prop :=
  ∀ k q : ℕ, q.Prime →
    (Nat.digits 17 q).Sublist (List.replicate k 9 ++ [1, 15]) →
    ∃ j ≤ k, q = Nat.ofDigits 17 (List.replicate j 9 ++ [1, 15])

/-- The remaining arithmetic existence problem, restricted to the sole exponent
class surviving the mod 2, 7 and 13 certificates. No primality assertion is assumed
or proved for a specific member of the family. -/
def H2 : Prop :=
  ∃ t : ℕ, ((4105 * 17 ^ (6 * t + 3) - 9) / 16).Prime

lemma prefix_scale (k : ℕ) :
    16 * Nat.ofDigits 17 (List.replicate k 9 ++ [1]) + 9 = 25 * 17 ^ k := by
  induction k with
  | zero => norm_num [Nat.ofDigits]
  | succ k ih =>
    simp only [List.replicate_succ, List.cons_append, Nat.ofDigits_cons, pow_succ]
    nlinarith

lemma prefix_parity (k : ℕ) :
    Nat.ofDigits 17 (List.replicate k 9 ++ [1]) % 2 = (k + 1) % 2 := by
  induction k with
  | zero => norm_num [Nat.ofDigits]
  | succ k ih =>
    simp only [List.replicate_succ, List.cons_append, Nat.ofDigits_cons]
    omega

lemma prefix_lower (k : ℕ) (hk : 0 < k) :
    26 ≤ Nat.ofDigits 17 (List.replicate k 9 ++ [1]) := by
  have hs := prefix_scale k
  have hp : 17 ≤ 17 ^ k := by
    simpa using (Nat.pow_le_pow_right (by decide : 1 ≤ 17) hk)
  omega

/-- The non-family subsequences beginning in 1 are composite, including the even-length
factorization from Bright--Devillers--Shallit's analysis. -/
lemma prefix_not_prime :
    ∀ k : ℕ, ¬ (Nat.ofDigits 17 (List.replicate k 9 ++ [1])).Prime := by
  intro k hp
  by_cases hk : k = 0
  · subst k
    norm_num [Nat.ofDigits] at hp
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  have hl := prefix_lower k hkpos
  by_cases ho : k % 2 = 1
  · have he : Nat.ofDigits 17 (List.replicate k 9 ++ [1]) % 2 = 0 := by
      have := prefix_parity k
      omega
    have hd : 2 ∣ Nat.ofDigits 17 (List.replicate k 9 ++ [1]) := Nat.dvd_of_mod_eq_zero he
    have := (Nat.dvd_prime hp).mp hd
    omega
  · have hk2 : k = 2 * (k / 2) := by omega
    let s : ℕ := 17 ^ (k / 2)
    have hs : 17 ≤ s := by
      dsimp [s]
      have : 1 ≤ k / 2 := by omega
      simpa using (Nat.pow_le_pow_right (by decide : 1 ≤ 17) this)
    have hs8 : s % 8 = 1 := by
      dsimp [s]
      norm_num [Nat.pow_mod]
    let a : ℕ := (5 * s + 3) / 8
    let b : ℕ := (5 * s - 3) / 2
    have ha : 8 * a = 5 * s + 3 := by
      have hmod : (5 * s + 3) % 8 = 0 := by omega
      have := Nat.mod_add_div (5 * s + 3) 8
      dsimp [a]
      omega
    have hb : 2 * b + 3 = 5 * s := by
      have hmod : (5 * s - 3) % 2 = 0 := by omega
      have := Nat.mod_add_div (5 * s - 3) 2
      dsimp [b]
      omega
    have ha1 : 1 < a := by omega
    have hb1 : 1 < b := by omega
    have hsquare : 17 ^ k = s * s := by
      calc
        17 ^ k = 17 ^ (k / 2 + k / 2) := by congr 1; omega
        _ = s * s := by rw [pow_add]
    have hn := prefix_scale k
    rw [hsquare] at hn
    have heq : a * b = Nat.ofDigits 17 (List.replicate k 9 ++ [1]) := by
      nlinarith [mul_pos (show 0 < a by omega) (show 0 < b by omega)]
    have hd : a ∣ Nat.ofDigits 17 (List.replicate k 9 ++ [1]) :=
      heq ▸ dvd_mul_right a b
    rcases (Nat.dvd_prime hp).mp hd with he | he
    · omega
    · have : a * b > a := by nlinarith
      omega

lemma nines_divisible (k : ℕ) (d : ℕ) (hd : 3 ∣ d) :
    3 ∣ Nat.ofDigits 17 (List.replicate k 9 ++ [d]) := by
  induction k with
  | zero => simpa using hd
  | succ k ih =>
    simp only [List.replicate_succ, List.cons_append, Nat.ofDigits_cons]
    exact dvd_add (by decide) (dvd_mul_of_dvd_right ih 17)

lemma nines_not_prime (k : ℕ) :
    ¬ (Nat.ofDigits 17 (List.replicate k 9)).Prime := by
  cases k with
  | zero => norm_num [Nat.ofDigits]
  | succ k =>
    have hd : 9 ∣ Nat.ofDigits 17 (List.replicate (k + 1) 9) := by
      have hh : ∀ t : ℕ, 9 ∣ Nat.ofDigits 17 (List.replicate t 9) := by
        intro t
        induction t with
        | zero => simp
        | succ t ih =>
          simp only [List.replicate_succ, Nat.ofDigits_cons]
          exact dvd_add (dvd_refl _) (dvd_mul_of_dvd_right ih 17)
      exact hh _
    intro hp
    have := (Nat.dvd_prime hp).mp hd
    rcases this with h | h
    · norm_num at h
    · exact (by decide : ¬ Nat.Prime 9) (h.symm ▸ hp)

lemma f_nines_not_prime (k : ℕ) :
    ¬ (Nat.ofDigits 17 (List.replicate k 9 ++ [15])).Prime := by
  intro hp
  have hd := nines_divisible k 15 (by decide)
  have heq : Nat.ofDigits 17 (List.replicate k 9 ++ [15]) = 3 := by
    have := (Nat.dvd_prime hp).mp hd
    omega
  have hl : 15 ≤ Nat.ofDigits 17 (List.replicate k 9 ++ [15]) := by
    rw [Nat.ofDigits_append]
    simp only [List.length_replicate, Nat.ofDigits_singleton]
    have : 0 < 17 ^ k := by positivity
    omega
  omega

lemma family_digits (k : ℕ) :
    Nat.digits 17 (Nat.ofDigits 17 (List.replicate k 9 ++ [1, 15])) =
      List.replicate k 9 ++ [1, 15] := by
  apply Nat.digits_ofDigits 17 (by decide)
  · simp only [List.mem_append, List.mem_replicate, List.mem_cons, List.mem_nil_iff, or_false]
    intro d h
    rcases h with ⟨_, rfl⟩ | rfl | rfl <;> omega
  · intro h
    simp

lemma family_value (k : ℕ) :
    Nat.ofDigits 17 (List.replicate k 9 ++ [1, 15]) =
      15 * 17 ^ (k + 1) + 17 ^ k + ∑ i ∈ Finset.range k, 9 * 17 ^ i := by
  have hn : Nat.ofDigits 17 (List.replicate k 9) = ∑ i ∈ Finset.range k, 9 * 17 ^ i := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [List.replicate_succ', Nat.ofDigits_append]
      simp only [List.length_replicate, Nat.ofDigits_singleton, Finset.sum_range_succ]
      rw [ih]
      ring
  rw [Nat.ofDigits_append, hn]
  simp only [List.length_replicate, Nat.ofDigits_cons, Nat.ofDigits_nil]
  ring

lemma prime_subsequence : H1 := by
  intro k q hq hsub
  obtain ⟨l, u, heq, hl, hu⟩ := List.sublist_append_iff.mp hsub
  obtain ⟨j, hj, rfl⟩ := List.sublist_replicate_iff.mp hl
  have hu' : u = [] ∨ u = [1] ∨ u = [15] ∨ u = [1, 15] := by
    simpa [List.sublists] using List.mem_sublists.mpr hu
  have hval : q = Nat.ofDigits 17 (List.replicate j 9 ++ u) := by
    rw [← heq, Nat.ofDigits_digits]
  rcases hu' with rfl | rfl | rfl | rfl
  · rw [List.append_nil] at hval
    exact False.elim (nines_not_prime j (hval ▸ hq))
  · exact False.elim (prefix_not_prime j (hval ▸ hq))
  · exact False.elim (f_nines_not_prime j (hval ▸ hq))
  · exact ⟨j, hj, hval⟩

lemma family_scale (k : ℕ) :
    16 * Nat.ofDigits 17 (List.replicate k 9 ++ [1, 15]) + 9 = 4105 * 17 ^ k := by
  induction k with
  | zero => norm_num [Nat.ofDigits]
  | succ k ih =>
    simp only [List.replicate_succ, List.cons_append, Nat.ofDigits_cons, pow_succ]
    nlinarith

lemma family_quotient (k : ℕ) :
    Nat.ofDigits 17 (List.replicate k 9 ++ [1, 15]) = (4105 * 17 ^ k - 9) / 16 := by
  have := family_scale k
  omega

lemma family_lower (k : ℕ) :
    256 ≤ Nat.ofDigits 17 (List.replicate k 9 ++ [1, 15]) := by
  have hs := family_scale k
  have : 0 < 17 ^ k := by positivity
  omega

lemma family_parity (k : ℕ) :
    Nat.ofDigits 17 (List.replicate k 9 ++ [1, 15]) % 2 = k % 2 := by
  induction k with
  | zero => norm_num [Nat.ofDigits]
  | succ k ih =>
    simp only [List.replicate_succ, List.cons_append, Nat.ofDigits_cons]
    omega

lemma power_mod_six (k p : ℕ) (hp0 : 1 < p) (hp : 17 ^ 6 % p = 1) :
    17 ^ k % p = 17 ^ (k % 6) % p := by
  calc
    17 ^ k % p = 17 ^ (6 * (k / 6) + k % 6) % p := by congr 2; omega
    _ = 17 ^ (k % 6) % p := by
      rw [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod, hp, one_pow,
        Nat.mod_eq_of_lt hp0, one_mul, Nat.mod_mod]

/-- Small modular certificates eliminate five of the six exponent classes. -/
lemma prime_exponent_class {k : ℕ}
    (hp : (Nat.ofDigits 17 (List.replicate k 9 ++ [1, 15])).Prime) : k % 6 = 3 := by
  have hl := family_lower k
  have ho : k % 2 = 1 := by
    by_contra h
    have hd : 2 ∣ Nat.ofDigits 17 (List.replicate k 9 ++ [1, 15]) := by
      apply Nat.dvd_of_mod_eq_zero
      rw [family_parity]
      omega
    rcases (Nat.dvd_prime hp).mp hd with he | he <;> omega
  have h1 : k % 6 ≠ 1 := by
    intro he
    have hh := congrArg (fun x : ℕ => x % 7) (family_scale k)
    have hw : 17 ^ k % 7 = 3 := by
      rw [power_mod_six k 7 (by decide) (by decide), he]
      norm_num
    norm_num [Nat.add_mod, Nat.mul_mod, hw] at hh
    have hd : 7 ∣ Nat.ofDigits 17 (List.replicate k 9 ++ [1, 15]) := by
      apply Nat.dvd_of_mod_eq_zero
      omega
    rcases (Nat.dvd_prime hp).mp hd with he | he <;> omega
  have h5 : k % 6 ≠ 5 := by
    intro he
    have hh := congrArg (fun x : ℕ => x % 13) (family_scale k)
    have hw : 17 ^ k % 13 = 10 := by
      rw [power_mod_six k 13 (by decide) (by decide), he]
      norm_num
    norm_num [Nat.add_mod, Nat.mul_mod, hw] at hh
    have hd : 13 ∣ Nat.ofDigits 17 (List.replicate k 9 ++ [1, 15]) := by
      apply Nat.dvd_of_mod_eq_zero
      omega
    rcases (Nat.dvd_prime hp).mp hd with he | he <;> omega
  omega

lemma family_increasing (k : ℕ) :
    Nat.ofDigits 17 (List.replicate k 9 ++ [1, 15]) <
      Nat.ofDigits 17 (List.replicate (k + 1) 9 ++ [1, 15]) := by
  simp only [List.replicate_succ, List.cons_append, Nat.ofDigits_cons]
  omega

lemma family_strictMono : StrictMono (fun k : ℕ =>
    Nat.ofDigits 17 (List.replicate k 9 ++ [1, 15])) :=
  strictMono_nat_of_lt_succ family_increasing

/-- Precisely the first prime in this family is minimal; no other prime-digit
subsequence obstruction remains. -/
lemma minimal_iff_first_prime (k : ℕ) :
    IsMinimalPrimeInBase 17 (Nat.ofDigits 17 (List.replicate k 9 ++ [1, 15])) ↔
      (Nat.ofDigits 17 (List.replicate k 9 ++ [1, 15])).Prime ∧
        ∀ j < k, ¬ (Nat.ofDigits 17 (List.replicate j 9 ++ [1, 15])).Prime := by
  constructor
  · intro h
    refine ⟨h.2.1, ?_⟩
    intro j hj hp
    apply h.2.2
    refine ⟨_, hp, ?_, ?_⟩
    · exact ne_of_lt (family_strictMono hj)
    · rw [family_digits, family_digits]
      exact ((List.replicate_sublist_replicate 9).mpr (Nat.le_of_lt hj)).append_right _
  · rintro ⟨hp, hfirst⟩
    refine ⟨by decide, hp, ?_⟩
    rintro ⟨q, hq, hne, hsub⟩
    rw [family_digits] at hsub
    obtain ⟨j, hj, hval⟩ := prime_subsequence k q hq hsub
    by_cases he : j = k
    · subst j
      exact hne hval
    · exact hfirst j (by omega) (hval ▸ hq)

/-- The digit-minimality question is equivalent to plain primality somewhere in
this exponential family. This theorem does not assert that such a prime exists. -/
lemma existence_iff :
    (∃ k : ℕ, IsMinimalPrimeInBase 17
      (15 * 17 ^ (k + 1) + 17 ^ k + ∑ i ∈ Finset.range k, 9 * 17 ^ i)) ↔ H2 := by
  constructor
  · rintro ⟨k, hk⟩
    have hp : (Nat.ofDigits 17 (List.replicate k 9 ++ [1, 15])).Prime :=
      (family_value k).symm ▸ hk.2.1
    have hc := prime_exponent_class hp
    refine ⟨k / 6, ?_⟩
    have he : 6 * (k / 6) + 3 = k := by omega
    rw [he, ← family_quotient]
    exact hp
  · rintro ⟨t, ht⟩
    have h : ∃ k : ℕ, (Nat.ofDigits 17 (List.replicate k 9 ++ [1, 15])).Prime := by
      refine ⟨6 * t + 3, ?_⟩
      rwa [family_quotient]
    let k := Nat.find h
    have hk : (Nat.ofDigits 17 (List.replicate k 9 ++ [1, 15])).Prime := Nat.find_spec h
    refine ⟨k, ?_⟩
    rw [← family_value, minimal_iff_first_prime]
    exact ⟨hk, fun j hj => Nat.find_min h hj⟩

/-- The format has two independent steps. The digital step H1 is already proved
in this file; the arithmetic step H2 is the unresolved part. -/
theorem main : H1 → H2 → type_of% @MinimalPrime.base_seventeen_f19_family_minimal_prime_question := by
  intro h1 ⟨t, ht⟩
  have h : ∃ k : ℕ, (Nat.ofDigits 17 (List.replicate k 9 ++ [1, 15])).Prime := by
    refine ⟨6 * t + 3, ?_⟩
    rwa [family_quotient]
  let k := Nat.find h
  have hk : (Nat.ofDigits 17 (List.replicate k 9 ++ [1, 15])).Prime := Nat.find_spec h
  refine ⟨k, ?_⟩
  rw [← family_value]
  refine ⟨by decide, hk, ?_⟩
  rintro ⟨q, hq, hne, hsub⟩
  rw [family_digits] at hsub
  obtain ⟨j, hj, hval⟩ := h1 k q hq hsub
  by_cases he : j = k
  · subst j
    exact hne hval
  · exact Nat.find_min h (by omega : j < k) (hval ▸ hq)

end OMA.R_MinimalPrime_base_seventeen_f19_family_minimal_prime_question_R1
