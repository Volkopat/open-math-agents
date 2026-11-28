import OMAStatements.S_oeis_a376639
import Mathlib

namespace OMA.A376639Proof

open OMA.S_oeis_a376639

/-- If every prime factor of `t` divides `m`, then `φ (t * m) = t * φ m`. -/
theorem totient_mul_of_subset {t m : ℕ} (ht : t ≠ 0) (hm : m ≠ 0)
    (h : t.primeFactors ⊆ m.primeFactors) : Nat.totient (t * m) = t * Nat.totient m := by
  have hpf : (t * m).primeFactors = m.primeFactors := by
    rw [Nat.primeFactors_mul ht hm]
    exact Finset.union_eq_right.mpr h
  have h1 := Nat.totient_mul_prod_primeFactors (t * m)
  have h2 := Nat.totient_mul_prod_primeFactors m
  rw [hpf] at h1
  have hP : 0 < ∏ p ∈ m.primeFactors, p :=
    Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
  apply Nat.eq_of_mul_eq_mul_right hP
  calc Nat.totient (t * m) * ∏ p ∈ m.primeFactors, p
        = t * (m * ∏ p ∈ m.primeFactors, (p - 1)) := by rw [h1, mul_assoc]
    _ = t * Nat.totient m * ∏ p ∈ m.primeFactors, p := by rw [← h2, mul_assoc]

/-- Conversely, `φ (t * m) = t * φ m` forces every prime factor of `t` to divide `m`. -/
theorem subset_of_totient_mul {t m : ℕ} (ht : t ≠ 0) (hm : m ≠ 0)
    (h : Nat.totient (t * m) = t * Nat.totient m) : t.primeFactors ⊆ m.primeFactors := by
  have hBU : m.primeFactors ⊆ (t * m).primeFactors := by
    rw [Nat.primeFactors_mul ht hm]
    exact Finset.subset_union_right
  have hAU : t.primeFactors ⊆ (t * m).primeFactors := by
    rw [Nat.primeFactors_mul ht hm]
    exact Finset.subset_union_left
  have h1 := Nat.totient_mul_prod_primeFactors (t * m)
  have h2 := Nat.totient_mul_prod_primeFactors m
  have ePU : ∏ p ∈ (t * m).primeFactors, p
      = (∏ p ∈ (t * m).primeFactors \ m.primeFactors, p) * ∏ p ∈ m.primeFactors, p :=
    (Finset.prod_sdiff hBU).symm
  have eQU : ∏ p ∈ (t * m).primeFactors, (p - 1)
      = (∏ p ∈ (t * m).primeFactors \ m.primeFactors, (p - 1)) * ∏ p ∈ m.primeFactors, (p - 1) :=
    (Finset.prod_sdiff hBU).symm
  rw [ePU, eQU, h] at h1
  by_contra hns
  obtain ⟨q, hqA, hqB⟩ := Finset.not_subset.mp hns
  have hD : ((t * m).primeFactors \ m.primeFactors).Nonempty :=
    ⟨q, Finset.mem_sdiff.mpr ⟨hAU hqA, hqB⟩⟩
  have hlt : ∏ p ∈ (t * m).primeFactors \ m.primeFactors, (p - 1)
      < ∏ p ∈ (t * m).primeFactors \ m.primeFactors, p := by
    apply Finset.prod_lt_prod_of_nonempty _ _ hD
    · intro p hp
      have := (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hp).1).two_le
      omega
    · intro p hp
      have := (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hp).1).two_le
      omega
  have hQB : 0 < ∏ p ∈ m.primeFactors, (p - 1) := by
    apply Finset.prod_pos
    intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have htm : 0 < t * m * ∏ p ∈ m.primeFactors, (p - 1) :=
    Nat.mul_pos (Nat.mul_pos (Nat.pos_of_ne_zero ht) (Nat.pos_of_ne_zero hm)) hQB
  set PD := ∏ p ∈ (t * m).primeFactors \ m.primeFactors, p
  set QD := ∏ p ∈ (t * m).primeFactors \ m.primeFactors, (p - 1)
  set PB := ∏ p ∈ m.primeFactors, p
  set QB := ∏ p ∈ m.primeFactors, (p - 1)
  have h3 : t * m * QB * PD = t * m * QB * QD := by
    calc t * m * QB * PD = t * (m * QB) * PD := by ring
      _ = t * (Nat.totient m * PB) * PD := by rw [h2]
      _ = t * Nat.totient m * (PD * PB) := by ring
      _ = t * m * (QD * QB) := h1
      _ = t * m * QB * QD := by ring
  exact hlt.ne' (Nat.eq_of_mul_eq_mul_left htm h3)

/-- A prime dividing `φ n` divides `n` or divides `r - 1` for a prime factor `r` of `n`. -/
theorem prime_dvd_totient {q n : ℕ} (hq : q.Prime) (h : q ∣ Nat.totient n) :
    q ∣ n ∨ ∃ r ∈ n.primeFactors, q ∣ r - 1 := by
  have hkey := Nat.totient_mul_prod_primeFactors n
  have h' : q ∣ n * ∏ p ∈ n.primeFactors, (p - 1) := by
    rw [← hkey]
    exact Dvd.dvd.mul_right h _
  rcases (Nat.Prime.dvd_mul hq).mp h' with h1 | h1
  · exact Or.inl h1
  · exact Or.inr ((Prime.dvd_finsetProd_iff hq.prime _).mp h1)

/-- A151999 is closed under `φ`. -/
theorem totient_mem {m : ℕ} (hm : InA151999 m) : InA151999 (Nat.totient m) := by
  obtain ⟨hm0, hmd⟩ := hm
  refine ⟨Nat.totient_pos.mpr hm0, fun q hq => ?_⟩
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
  rcases prime_dvd_totient hqp (Nat.dvd_of_mem_primeFactors hq) with h | ⟨r, hr, hqr⟩
  · exact h
  · have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
    have hrm : r ∣ m := hmd r hr
    have hr1 : r - 1 ∣ Nat.totient m := by
      rw [← Nat.totient_prime hrp]
      exact Nat.totient_dvd_of_dvd hrm
    exact dvd_trans hqr hr1

/-- Every term `m` of A151999 solves `φ m ^ 2 = φ (φ m * m)`. -/
theorem sq_of_mem {m : ℕ} (hm : InA151999 m) :
    Nat.totient m ^ 2 = Nat.totient (Nat.totient m * m) := by
  obtain ⟨hm0, hmd⟩ := hm
  have ht : Nat.totient m ≠ 0 := (Nat.totient_pos.mpr hm0).ne'
  have hsub : (Nat.totient m).primeFactors ⊆ m.primeFactors := by
    intro p hp
    exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp, hmd p hp, hm0.ne'⟩
  rw [totient_mul_of_subset ht hm0.ne' hsub, sq]

/-- The totient of a term of A151999 is a term of A293928. -/
theorem mem_A293928 {m : ℕ} (hm : InA151999 m) : InA293928 (Nat.totient m) :=
  ⟨m, hm.1, rfl, sq_of_mem hm⟩

/-- A term of A293928 is the totient of a term of A151999. -/
theorem mem_of_A293928 {t : ℕ} (h : InA293928 t) : ∃ m, InA151999 m ∧ Nat.totient m = t := by
  obtain ⟨m, hm0, rfl, heq⟩ := h
  have ht : Nat.totient m ≠ 0 := (Nat.totient_pos.mpr hm0).ne'
  have h2 : Nat.totient (Nat.totient m * m) = Nat.totient m * Nat.totient m := by
    rw [← heq, sq]
  have hsub := subset_of_totient_mul ht hm0.ne' h2
  exact ⟨m, ⟨hm0, fun p hp => Nat.dvd_of_mem_primeFactors (hsub hp)⟩, rfl⟩

/-- Conjecture 2. -/
theorem conj2 {t : ℕ} (ht : InA293928 t) : InA151999 t := by
  obtain ⟨m, hm, rfl⟩ := mem_of_A293928 ht
  exact totient_mem hm

/-- `2 * 5 ^ (j + 1)` is a term of A376639. -/
theorem mem_family (j : ℕ) : InA376639 (2 * 5 ^ (j + 1)) := by
  have h5 : (5 : ℕ) ∣ 2 * 5 ^ (j + 1) :=
    Dvd.dvd.mul_left (dvd_pow_self 5 (Nat.succ_ne_zero j)) 2
  have hodd : (5 ^ (j + 1)) % 2 = 1 := Nat.odd_iff.mp (Odd.pow (by decide : Odd 5))
  refine ⟨⟨by positivity, fun q hq => ?_⟩, ?_⟩
  · have hqp := Nat.prime_of_mem_primeFactors hq
    rcases prime_dvd_totient hqp (Nat.dvd_of_mem_primeFactors hq) with h | ⟨r, hr, hqr⟩
    · exact h
    · have hrp := Nat.prime_of_mem_primeFactors hr
      have hrd := Nat.dvd_of_mem_primeFactors hr
      rcases (Nat.Prime.dvd_mul hrp).mp hrd with h2 | h2
      · have hr2 : r = 2 := (Nat.prime_dvd_prime_iff_eq hrp Nat.prime_two).mp h2
        subst hr2
        have h1 : q ∣ 1 := by simpa using hqr
        exact absurd h1 hqp.not_dvd_one
      · have hr5 : r = 5 :=
          (Nat.prime_dvd_prime_iff_eq hrp Nat.prime_five).mp (hrp.dvd_of_dvd_pow h2)
        subst hr5
        have h4 : q ∣ 2 ^ 2 := by simpa using hqr
        exact Dvd.dvd.mul_right (hqp.dvd_of_dvd_pow h4) _
  · intro h
    obtain ⟨m, ⟨hm0, hmd⟩, hmt⟩ := mem_of_A293928 h
    have h5m : 5 ∣ m := hmd 5 (by
      rw [hmt]
      exact Nat.mem_primeFactors.mpr ⟨Nat.prime_five, h5, by positivity⟩)
    have h4 : 4 ∣ 2 * 5 ^ (j + 1) := by
      rw [← hmt]
      have h54 := Nat.totient_dvd_of_dvd h5m
      rw [Nat.totient_prime Nat.prime_five] at h54
      simpa using h54
    generalize 5 ^ (j + 1) = x at h4 hodd
    omega

/-- A376639 is infinite. -/
theorem infinite_A376639 : (Set.ofPred InA376639).Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun j : ℕ => 2 * 5 ^ (j + 1))
  · intro i j hij
    have h1 : 5 ^ (i + 1) = 5 ^ (j + 1) := Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) hij
    have h2 : i + 1 = j + 1 := Nat.pow_right_injective (by norm_num : 2 ≤ 5) h1
    omega
  · intro j
    exact mem_family j

end OMA.A376639Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a376639.main := by
  refine ⟨fun n _ => ?_, fun t ht => OMA.A376639Proof.conj2 ht⟩
  rintro ⟨k, _, hk⟩
  have hinf := OMA.A376639Proof.infinite_A376639
  have hn : OMA.S_oeis_a376639.InA376639 (OMA.S_oeis_a376639.a n) :=
    Nat.nth_mem_of_infinite hinf (n - 1)
  have hk' : OMA.S_oeis_a376639.InA376639 (OMA.S_oeis_a376639.a k) :=
    Nat.nth_mem_of_infinite hinf (k - 1)
  have hmem := OMA.A376639Proof.mem_A293928 hk'.1
  rw [← hk] at hmem
  exact hn.2 hmem

