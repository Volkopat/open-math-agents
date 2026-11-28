import OMAStatements.S_oeis_a327569
import Mathlib

-- Problem: OEIS A327569, conjecture of Jianing Song: the exponent of the group SL(2, Z/p^e) is
-- (p^2 - 1) p^e / 2 for an odd prime p, and 3 * 2^e for p = 2 (e >= 1).
-- Statement: statements/oeis-a327569.lean (declaration OMA.S_oeis_a327569.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. All work is done with 2 x 2 matrices of determinant 1.
-- Upper bound modulo p (p odd). Let h have trace t, so h^2 = t h - 1 and M = 2h - t satisfies
-- M^2 = t^2 - 4. In characteristic p, 2 h^p - t = M^p = e M with e = (t^2 - 4)^((p-1)/2), which
-- is 0, 1 or -1. Thus h^(2p) = 1, h^(p-1) = 1 or h^(p+1) = 1. Each of these exponents divides
-- K = p (p^2 - 1)/2. Modulo 2, a finite check gives h^6 = 1.
-- Upper bound modulo p^e. If g^K == 1 (mod p), then g^K = 1 + p C. If a = 1 + p^k C with
-- k >= 1, then a^p = 1 + p^(k+1) C' (use a^p - 1 = (a - 1)(1 + a + ... + a^(p-1))). Thus
-- g^(K p^(e-1)) = 1.
-- Lower bound. Let X be the exponent. The matrix [[1,1],[0,1]] gives p^e | X. Each matrix of
-- determinant 1 over Z/p has a lift of determinant 1 over Z/p^e, thus its X-th power is 1.
-- The matrix diag(r, 1/r) with a primitive root r gives p - 1 | X. The multiplication by a
-- generator of the unit group of the field with p^2 elements is a matrix G of order p^2 - 1,
-- and G^(p-1) has determinant 1 and order p + 1, thus p + 1 | X. So
-- lcm(p^e, p - 1, p + 1) = p^e (p^2 - 1)/2 divides X. For p = 2 the matrix [[0,-1],[1,-1]] has
-- order 3, thus 3 * 2^e divides X.

namespace OMA.A327569

open Matrix Finset

lemma form_pow {A : Type*} [Ring A] (q : ℕ) (a : A) (h : ∃ C : A, a = 1 + q • C) :
    ∀ i : ℕ, ∃ C : A, a ^ i = 1 + q • C := by
  obtain ⟨C0, rfl⟩ := h
  intro i
  induction i with
  | zero => exact ⟨0, by simp⟩
  | succ i ih =>
    obtain ⟨Ci, hi⟩ := ih
    refine ⟨Ci + C0 + q • (Ci * C0), ?_⟩
    rw [pow_succ, hi]
    simp only [mul_add, add_mul, mul_one, one_mul, smul_mul_assoc, mul_smul_comm, smul_add]
    abel

lemma form_step {A : Type*} [Ring A] (q k : ℕ) (hk : 1 ≤ k) (a : A)
    (h : ∃ C : A, a = 1 + q ^ k • C) : ∃ C : A, a ^ q = 1 + q ^ (k + 1) • C := by
  obtain ⟨C, hC⟩ := h
  have h1 : ∃ C' : A, a = 1 + q • C' := by
    refine ⟨q ^ (k - 1) • C, ?_⟩
    rw [hC, smul_smul, ← pow_succ']
    congr 3; omega
  choose D hD using form_pow q a h1
  have hsum : ∑ i ∈ range q, a ^ i = q • (1 + ∑ i ∈ range q, D i) := by
    rw [sum_congr rfl (fun i _ => hD i), sum_add_distrib, sum_const, card_range, ← smul_sum,
      smul_add]
  have hg := mul_geom_sum a q
  have ha1 : a - 1 = q ^ k • C := by rw [hC, add_sub_cancel_left]
  rw [hsum, ha1, smul_mul_assoc, mul_smul_comm, smul_smul] at hg
  refine ⟨C * (1 + ∑ i ∈ range q, D i), ?_⟩
  rw [pow_succ, hg]; abel

lemma form_iter {A : Type*} [Ring A] (q : ℕ) (a : A) (h : ∃ C : A, a = 1 + q • C) :
    ∀ j : ℕ, ∃ C : A, a ^ (q ^ j) = 1 + q ^ (j + 1) • C := by
  intro j
  induction j with
  | zero => simpa using h
  | succ j ih =>
    have := form_step q (j + 1) (by omega) _ ih
    rwa [← pow_mul, ← pow_succ] at this

lemma ch {R : Type*} [CommRing R] (h : Matrix (Fin 2) (Fin 2) R) (hd : h.det = 1) :
    h * h = (h 0 0 + h 1 1) • h - 1 := by
  rw [Matrix.det_fin_two] at hd
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination -hd
  · ring
  · ring
  · linear_combination -hd

lemma two_ne (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h2)

/-- A matrix of determinant 1 over Z/p has order dividing p - 1, p + 1 or 2 p. -/
lemma modp (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (h : Matrix (Fin 2) (Fin 2) (ZMod p))
    (hd : h.det = 1) : h ^ (p - 1) = 1 ∨ h ^ (p + 1) = 1 ∨ h ^ (2 * p) = 1 := by
  have hp : p.Prime := Fact.out
  have hsq := ch h hd
  have hd' := hd
  rw [Matrix.det_fin_two] at hd'
  generalize ht : h 0 0 + h 1 1 = t at hsq
  have hM2 : (h + h - t • 1) * (h + h - t • 1)
      = (t ^ 2 - 4) • (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
    subst ht
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination (-4) * hd'
    · ring
    · ring
    · linear_combination (-4) * hd'
  have hodd : p = 2 * (p / 2) + 1 := by
    obtain ⟨k, hk⟩ := hp.eq_two_or_odd'.resolve_left hp2
    omega
  have gen : ∀ k : ℕ, (h + h - t • 1) ^ (2 * k + 1) = ((t ^ 2 - 4) ^ k) • (h + h - t • 1) := by
    intro k
    rw [pow_succ, pow_mul, pow_two, hM2, smul_pow, one_pow, smul_mul_assoc, one_mul]
  have hMp : (h + h - t • 1) ^ p = ((t ^ 2 - 4) ^ (p / 2)) • (h + h - t • 1) := by
    have h' := gen (p / 2)
    rwa [← hodd] at h'
  have hcomm : Commute (h + h) (t • (1 : Matrix (Fin 2) (Fin 2) (ZMod p))) :=
    (Commute.one_right _).smul_right t
  have hMp' : (h + h - t • 1) ^ p = h ^ p + h ^ p - t • 1 := by
    rw [sub_pow_char_of_commute p hcomm, add_pow_char_of_commute p (Commute.refl h), smul_pow,
      one_pow, ZMod.pow_card]
  have h2 := two_ne p hp2
  have hinv : h * (t • 1 - h) = 1 := by
    rw [mul_sub, mul_smul_comm, mul_one, hsq]; abel
  have hpp : p - 1 + 1 = p := by have := hp.pos; omega
  by_cases hD : t ^ 2 - 4 = 0
  · right; right
    have hz : (t ^ 2 - 4) ^ (p / 2) = 0 := by
      rw [hD]; exact zero_pow (by have := hp.two_le; omega)
    rw [hz, zero_smul] at hMp
    have e : h ^ p + h ^ p = t • 1 := sub_eq_zero.1 (hMp'.symm.trans hMp)
    have e2 : (h ^ p + h ^ p) * (h ^ p + h ^ p)
        = (4 : ZMod p) • (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
      rw [e, smul_mul_assoc, one_mul, smul_smul]
      congr 1
      linear_combination hD
    have e3 : (4 : ZMod p) • (h ^ p * h ^ p - 1) = 0 := by
      have e4 : (4 : ZMod p) = 1 + 1 + 1 + 1 := by norm_num
      have e5 : (h ^ p + h ^ p) * (h ^ p + h ^ p)
          = h ^ p * h ^ p + h ^ p * h ^ p + h ^ p * h ^ p + h ^ p * h ^ p := by noncomm_ring
      rw [e5] at e2
      rw [smul_sub, ← e2, e4]
      simp only [add_smul, one_smul]
      abel
    have h4 : (4 : ZMod p) ≠ 0 := by
      have : (4 : ZMod p) = 2 * 2 := by norm_num
      rw [this]; exact mul_ne_zero h2 h2
    have e6 : h ^ p * h ^ p = 1 := sub_eq_zero.1 ((smul_eq_zero.1 e3).resolve_left h4)
    rw [mul_comm, pow_mul, pow_two, e6]
  · rcases ZMod.pow_div_two_eq_neg_one_or_one p hD with he | he
    · left
      rw [he, one_smul] at hMp
      have e : h ^ p + h ^ p - t • 1 = h + h - t • 1 := hMp'.symm.trans hMp
      have e2 : (2 : ZMod p) • (h ^ p - h) = 0 := by
        rw [two_smul]
        have : h ^ p - h + (h ^ p - h) = (h ^ p + h ^ p - t • 1) - (h + h - t • 1) := by abel
        rw [this, e, sub_self]
      have hqp : h ^ p = h := sub_eq_zero.1 ((smul_eq_zero.1 e2).resolve_left h2)
      have h1 : h ^ (p - 1) * h = h := by rw [← pow_succ, hpp, hqp]
      calc h ^ (p - 1) = h ^ (p - 1) * (h * (t • 1 - h)) := by rw [hinv, mul_one]
        _ = (h ^ (p - 1) * h) * (t • 1 - h) := by rw [mul_assoc]
        _ = 1 := by rw [h1, hinv]
    · right; left
      rw [he, neg_one_smul] at hMp
      have e : h ^ p + h ^ p - t • 1 = -(h + h - t • 1) := hMp'.symm.trans hMp
      have e2 : (2 : ZMod p) • (h ^ p - (t • 1 - h)) = 0 := by
        rw [two_smul]
        have : h ^ p - (t • 1 - h) + (h ^ p - (t • 1 - h))
            = (h ^ p + h ^ p - t • 1) - (-(h + h - t • 1)) := by abel
        rw [this, e, sub_self]
      have hqp : h ^ p = t • 1 - h := sub_eq_zero.1 ((smul_eq_zero.1 e2).resolve_left h2)
      rw [pow_succ, hqp, sub_mul, smul_mul_assoc, one_mul, hsq]; abel

lemma nsmul_self_eq_zero (N : ℕ) (C : Matrix (Fin 2) (Fin 2) (ZMod N)) : N • C = 0 := by
  ext i j
  rw [Matrix.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]; rfl

/-- An element of the kernel of the reduction Z/N -> Z/p is a multiple of p. -/
lemma ker_elt (p N : ℕ) [NeZero N] (hpN : p ∣ N) (x : ZMod N)
    (h : ZMod.castHom hpN (ZMod p) x = 0) : ∃ y : ZMod N, x = p • y := by
  have hx : ((x.val : ℕ) : ZMod N) = x := ZMod.natCast_zmod_val x
  rw [← hx, map_natCast, ZMod.natCast_eq_zero_iff] at h
  obtain ⟨k, hk⟩ := h
  refine ⟨(k : ZMod N), ?_⟩
  rw [← hx, hk, nsmul_eq_mul]; push_cast; ring

lemma ker_form (p N : ℕ) [NeZero N] (hpN : p ∣ N) (A : Matrix (Fin 2) (Fin 2) (ZMod N))
    (h : (ZMod.castHom hpN (ZMod p)).mapMatrix A = 1) :
    ∃ C : Matrix (Fin 2) (Fin 2) (ZMod N), A = 1 + p • C := by
  have key : ∀ i j, ∃ y : ZMod N, (A - 1) i j = p • y := by
    intro i j
    apply ker_elt p N hpN
    have h2 : (ZMod.castHom hpN (ZMod p)).mapMatrix (A - 1) = 0 := by
      rw [map_sub, h, map_one, sub_self]
    have h3 := congrFun (congrFun h2 i) j
    simpa using h3
  choose C hC using key
  refine ⟨Matrix.of C, ?_⟩
  have : A - 1 = p • Matrix.of C := by
    ext i j
    rw [Matrix.smul_apply, Matrix.of_apply]; exact hC i j
  rw [← this]; abel

/-- Upper bound: if every matrix of determinant 1 over Z/p has K-th power 1, then every matrix
of determinant 1 over Z/p^e has (K p^(e-1))-th power 1. -/
lemma upper (p e : ℕ) (he : 0 < e) [NeZero (p ^ e)] (K : ℕ)
    (hK : ∀ h : Matrix (Fin 2) (Fin 2) (ZMod p), h.det = 1 → h ^ K = 1)
    (g : Matrix (Fin 2) (Fin 2) (ZMod (p ^ e))) (hg : g.det = 1) : g ^ (K * p ^ (e - 1)) = 1 := by
  have hpN : p ∣ p ^ e := dvd_pow_self p (by omega)
  have hdet : ((ZMod.castHom hpN (ZMod p)).mapMatrix g).det = 1 := by
    rw [← RingHom.map_det, hg, map_one]
  have h1 : (ZMod.castHom hpN (ZMod p)).mapMatrix (g ^ K) = 1 := by
    rw [map_pow]; exact hK _ hdet
  obtain ⟨C, hC⟩ := form_iter p (g ^ K) (ker_form p (p ^ e) hpN _ h1) (e - 1)
  have e1 : e - 1 + 1 = e := by omega
  rw [pow_mul, hC, e1, nsmul_self_eq_zero, add_zero]

lemma unip_pow {R : Type*} [CommRing R] (k : ℕ) :
    (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) R) ^ k = !![1, (k : R); 0, 1] := by
  induction k with
  | zero => simp [Matrix.one_fin_two]
  | succ k ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring

lemma diag_pow {R : Type*} [CommRing R] (a b : R) (k : ℕ) :
    (!![a, 0; 0, b] : Matrix (Fin 2) (Fin 2) R) ^ k = !![a ^ k, 0; 0, b ^ k] := by
  induction k with
  | zero => simp [Matrix.one_fin_two]
  | succ k ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, pow_succ]

lemma diag_entry {R : Type*} [CommRing R] (a b : R) (hab : a * b = 1) (X : ℕ)
    (HX : ∀ g : Matrix (Fin 2) (Fin 2) R, g.det = 1 → g ^ X = 1) : a ^ X = 1 := by
  have h := HX !![a, 0; 0, b] (by rw [Matrix.det_fin_two_of, hab]; ring)
  rw [diag_pow] at h
  have h00 := congrFun (congrFun h 0) 0
  simpa using h00

/-- N divides X. -/
lemma lower_N (N X : ℕ)
    (HX : ∀ g : Matrix (Fin 2) (Fin 2) (ZMod N), g.det = 1 → g ^ X = 1) : N ∣ X := by
  have h := HX !![1, 1; 0, 1] (by simp [Matrix.det_fin_two_of])
  rw [unip_pow] at h
  have h01 := congrFun (congrFun h 0) 1
  simp at h01
  exact (ZMod.natCast_eq_zero_iff X N).1 h01

/-- Lifting: a property of all matrices of determinant 1 over Z/p^e goes down to Z/p. -/
lemma descend (p e X : ℕ) [Fact p.Prime] (he : 0 < e) [NeZero (p ^ e)]
    (HX : ∀ g : Matrix (Fin 2) (Fin 2) (ZMod (p ^ e)), g.det = 1 → g ^ X = 1)
    (h : Matrix (Fin 2) (Fin 2) (ZMod p)) (hd : h.det = 1) : h ^ X = 1 := by
  have hp : p.Prime := Fact.out
  have hpN : p ∣ p ^ e := dvd_pow_self p (by omega)
  let c := ZMod.castHom hpN (ZMod p)
  let A : Matrix (Fin 2) (Fin 2) (ZMod (p ^ e)) := h.map (fun x => ((x.val : ℕ) : ZMod (p ^ e)))
  have hA : c.mapMatrix A = h := by
    ext i j
    simp [A, c]
  have hdet : c A.det = 1 := by
    rw [RingHom.map_det, hA, hd]
  have hunit : IsUnit A.det := by
    have hx : ((A.det.val : ℕ) : ZMod (p ^ e)) = A.det := ZMod.natCast_zmod_val _
    rw [← hx, ZMod.isUnit_iff_coprime]
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro hdv
    have h0 : ((A.det.val : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hdv
    have h1 : c (((A.det.val : ℕ) : ZMod (p ^ e))) = 1 := by rw [hx]; exact hdet
    rw [map_natCast, h0] at h1
    exact zero_ne_one h1
  obtain ⟨w, hw⟩ := hunit
  have hcw : c (↑w⁻¹ : ZMod (p ^ e)) = 1 := by
    have h1 : c (↑w⁻¹ : ZMod (p ^ e)) * c (↑w : ZMod (p ^ e)) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    rw [hw, hdet, mul_one] at h1
    exact h1
  have hB : (A * !![1, 0; 0, (↑w⁻¹ : ZMod (p ^ e))]).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_fin_two_of, ← hw]
    simp
  have hcB : c.mapMatrix (A * !![1, 0; 0, (↑w⁻¹ : ZMod (p ^ e))]) = h := by
    rw [map_mul, hA]
    have : c.mapMatrix !![1, 0; 0, (↑w⁻¹ : ZMod (p ^ e))] = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hcw]
    rw [this, mul_one]
  have h2 := HX _ hB
  have h3 := congrArg c.mapMatrix h2
  rw [map_pow, hcB, map_one] at h3
  exact h3

/-- p - 1 divides X. -/
lemma lower_pm1 (p X : ℕ) [Fact p.Prime]
    (HX : ∀ h : Matrix (Fin 2) (Fin 2) (ZMod p), h.det = 1 → h ^ X = 1) : (p - 1) ∣ X := by
  obtain ⟨r, hr⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hord : orderOf r = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hr, Nat.card_eq_fintype_card, ZMod.card_units]
  have h00 := diag_entry (r : ZMod p) (↑r⁻¹ : ZMod p) (Units.mul_inv r) X HX
  have hrX : r ^ X = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h00]; rfl)
  rw [← hord]; exact orderOf_dvd_of_pow_eq_one hrX

/-- A matrix of determinant 1 over Z/p whose order is a multiple of p + 1. It comes from the
multiplication by a generator of the unit group of the field with p^2 elements. -/
lemma exists_H (p : ℕ) [Fact p.Prime] :
    ∃ H : Matrix (Fin 2) (Fin 2) (ZMod p), H.det = 1 ∧ ∀ k : ℕ, H ^ k = 1 → (p + 1) ∣ k := by
  classical
  have hp : p.Prime := Fact.out
  have hfr : Module.finrank (ZMod p) (GaloisField p 2) = 2 := GaloisField.finrank p (by norm_num)
  have hfin : Module.Finite (ZMod p) (GaloisField p 2) :=
    Module.finite_of_finrank_pos (by rw [hfr]; norm_num)
  have hinj := Algebra.leftMulMatrix_injective
    (Module.finBasisOfFinrankEq (ZMod p) (GaloisField p 2) hfr)
  generalize Algebra.leftMulMatrix (Module.finBasisOfFinrankEq (ZMod p) (GaloisField p 2) hfr)
    = φ at hinj
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := (GaloisField p 2)ˣ)
  have hcard : Nat.card (GaloisField p 2)ˣ = p ^ 2 - 1 := by
    rw [Nat.card_units, GaloisField.card p 2 (by norm_num)]
  have hord : orderOf γ = p ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hγ, hcard]
  have hGk : ∀ k : ℕ, φ (γ : GaloisField p 2) ^ k = 1 → (p ^ 2 - 1) ∣ k := by
    intro k hk
    rw [← map_pow, ← map_one φ] at hk
    have h1 := hinj hk
    have h2 : γ ^ k = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h1]; rfl)
    rw [← hord]; exact orderOf_dvd_of_pow_eq_one h2
  have hdet : (φ (γ : GaloisField p 2)).det ≠ 0 := by
    intro h0
    have h1 : φ (γ : GaloisField p 2) * φ (↑γ⁻¹ : GaloisField p 2) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h2
    exact zero_ne_one h2
  refine ⟨φ (γ : GaloisField p 2) ^ (p - 1), ?_, ?_⟩
  · rw [Matrix.det_pow]; exact ZMod.pow_card_sub_one_eq_one hdet
  · intro k hk
    rw [← pow_mul] at hk
    have h1 := hGk _ hk
    have e : p ^ 2 - 1 = (p - 1) * (p + 1) := by
      obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := hp.pos; omega⟩
      rw [Nat.add_sub_cancel]
      apply Nat.sub_eq_of_eq_add; ring
    rw [e] at h1
    exact Nat.dvd_of_mul_dvd_mul_left (by have := hp.two_le; omega) h1

lemma mod2 : ∀ h : Matrix (Fin 2) (Fin 2) (ZMod 2), h.det = 1 → h ^ 6 = 1 := by decide

lemma three_dvd {R : Type*} [CommRing R] [Nontrivial R] (X : ℕ)
    (HX : ∀ g : Matrix (Fin 2) (Fin 2) R, g.det = 1 → g ^ X = 1) : 3 ∣ X := by
  have hw3 : (!![0, -1; 1, -1] : Matrix (Fin 2) (Fin 2) R) ^ 3 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
  have h := HX !![0, -1; 1, -1] (by rw [Matrix.det_fin_two_of]; ring)
  have hdm : X = 3 * (X / 3) + X % 3 := (Nat.div_add_mod X 3).symm
  rw [hdm, pow_add, pow_mul, hw3, one_pow, one_mul] at h
  have hr : X % 3 = 0 ∨ X % 3 = 1 ∨ X % 3 = 2 := by omega
  rcases hr with hr | hr | hr
  · exact Nat.dvd_of_mod_eq_zero hr
  · exfalso
    rw [hr, pow_one] at h
    have h00 := congrFun (congrFun h 0) 0
    simp at h00
  · exfalso
    rw [hr, pow_two] at h
    have h01 := congrFun (congrFun h 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h01

lemma of_exponent (R : Type*) [CommRing R] (g : Matrix (Fin 2) (Fin 2) R) (hg : g.det = 1) :
    g ^ Monoid.exponent (Matrix.SpecialLinearGroup (Fin 2) R) = 1 := by
  have h := Monoid.pow_exponent_eq_one (G := Matrix.SpecialLinearGroup (Fin 2) R) ⟨g, hg⟩
  have h2 := congrArg
    (fun x : Matrix.SpecialLinearGroup (Fin 2) R => (x : Matrix (Fin 2) (Fin 2) R)) h
  simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one] at h2
  exact h2

lemma exponent_dvd (R : Type*) [CommRing R] (E : ℕ)
    (h : ∀ g : Matrix (Fin 2) (Fin 2) R, g.det = 1 → g ^ E = 1) :
    Monoid.exponent (Matrix.SpecialLinearGroup (Fin 2) R) ∣ E := by
  apply Monoid.exponent_dvd_of_forall_pow_eq_one
  intro g
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow]
  exact h g.1 g.2

theorem odd_case (p e : ℕ) (hp : p.Prime) (hp2 : 2 < p) (he : 0 < e) :
    Monoid.exponent (Matrix.SpecialLinearGroup (Fin 2) (ZMod (p ^ e)))
      = (p ^ 2 - 1) * p ^ e / 2 := by
  have hfact : Fact p.Prime := ⟨hp⟩
  have hne : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  obtain ⟨a, ha⟩ : ∃ a, p = 2 * a + 1 := by
    obtain ⟨k, hk⟩ := hp.eq_two_or_odd'.resolve_left (by omega)
    exact ⟨k, hk⟩
  have ha1 : 1 ≤ a := by omega
  have hE : (p ^ 2 - 1) * p ^ e / 2 = 2 * a * (a + 1) * p ^ e := by
    have h1 : p ^ 2 - 1 = 2 * (2 * a * (a + 1)) := by
      rw [ha]; apply Nat.sub_eq_of_eq_add; ring
    rw [h1, mul_assoc, Nat.mul_div_cancel_left _ (by norm_num)]
  rw [hE]
  apply Nat.dvd_antisymm
  · -- upper bound
    apply exponent_dvd
    intro g hg
    have hK : ∀ h : Matrix (Fin 2) (Fin 2) (ZMod p), h.det = 1 →
        h ^ (2 * a * (a + 1) * p) = 1 := by
      intro h hd
      rcases modp p (by omega) h hd with h1 | h1 | h1
      · have e1 : 2 * a * (a + 1) * p = (p - 1) * ((a + 1) * p) := by
          have : p - 1 = 2 * a := by omega
          rw [this]; ring
        rw [e1, pow_mul, h1, one_pow]
      · have e1 : 2 * a * (a + 1) * p = (p + 1) * (a * p) := by
          have : p + 1 = 2 * (a + 1) := by omega
          rw [this]; ring
        rw [e1, pow_mul, h1, one_pow]
      · have e1 : 2 * a * (a + 1) * p = (2 * p) * (a * (a + 1)) := by ring
        rw [e1, pow_mul, h1, one_pow]
    have h := upper p e he _ hK g hg
    have e2 : 2 * a * (a + 1) * p * p ^ (e - 1) = 2 * a * (a + 1) * p ^ e := by
      have : p ^ e = p * p ^ (e - 1) := by rw [← pow_succ']; congr 1; omega
      rw [this]; ring
    rwa [e2] at h
  · -- lower bound
    have HX := of_exponent (ZMod (p ^ e))
    generalize Monoid.exponent (Matrix.SpecialLinearGroup (Fin 2) (ZMod (p ^ e))) = X at HX
    have hN : p ^ e ∣ X := lower_N _ X HX
    have Hp := descend p e X he HX
    have h1 : (p - 1) ∣ X := lower_pm1 p X Hp
    obtain ⟨H, hHd, hH⟩ := exists_H p
    have h2 : (p + 1) ∣ X := hH X (Hp H hHd)
    have e1 : p - 1 = 2 * a := by omega
    have e2 : p + 1 = 2 * (a + 1) := by omega
    rw [e1] at h1
    rw [e2] at h2
    have hl : Nat.lcm (2 * a) (2 * (a + 1)) ∣ X := Nat.lcm_dvd h1 h2
    have hg : Nat.gcd (2 * a) (2 * (a + 1)) = 2 := by
      rw [Nat.gcd_mul_left]; simp
    have hgl := Nat.gcd_mul_lcm (2 * a) (2 * (a + 1))
    rw [hg] at hgl
    have hlcm : Nat.lcm (2 * a) (2 * (a + 1)) = 2 * a * (a + 1) := by
      have : 2 * Nat.lcm (2 * a) (2 * (a + 1)) = 2 * (2 * a * (a + 1)) := by rw [hgl]; ring
      omega
    rw [hlcm] at hl
    have hc1 : Nat.Coprime p (2 * a) := by
      rw [hp.coprime_iff_not_dvd]
      intro hd
      have := Nat.le_of_dvd (by omega) hd
      omega
    have hc2 : Nat.Coprime p (a + 1) := by
      rw [hp.coprime_iff_not_dvd]
      intro hd
      have := Nat.le_of_dvd (by omega) hd
      omega
    have hc : Nat.Coprime (2 * a * (a + 1)) (p ^ e) :=
      (Nat.Coprime.pow_left e (Nat.Coprime.mul_right hc1 hc2)).symm
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hc hl hN

theorem two_case (e : ℕ) (he : 0 < e) :
    Monoid.exponent (Matrix.SpecialLinearGroup (Fin 2) (ZMod (2 ^ e))) = 3 * 2 ^ e := by
  have hne : NeZero (2 ^ e) := ⟨pow_ne_zero e (by norm_num)⟩
  have hnt : Fact (1 < 2 ^ e) := ⟨Nat.one_lt_two_pow (by omega)⟩
  apply Nat.dvd_antisymm
  · apply exponent_dvd
    intro g hg
    have h := upper 2 e he 6 mod2 g hg
    have e2 : 6 * 2 ^ (e - 1) = 3 * 2 ^ e := by
      have : 2 ^ e = 2 * 2 ^ (e - 1) := by rw [← pow_succ']; congr 1; omega
      rw [this]; ring
    rwa [e2] at h
  · have HX := of_exponent (ZMod (2 ^ e))
    generalize Monoid.exponent (Matrix.SpecialLinearGroup (Fin 2) (ZMod (2 ^ e))) = X at HX
    have hN : 2 ^ e ∣ X := lower_N _ X HX
    have h3 : 3 ∣ X := three_dvd X HX
    have hc : Nat.Coprime 3 (2 ^ e) := Nat.Coprime.pow_right e (by norm_num)
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hc h3 hN

end OMA.A327569

theorem OMA.solution : type_of% @OMA.S_oeis_a327569.main :=
  ⟨fun p e hp hp2 he => OMA.A327569.odd_case p e hp hp2 he,
    fun e he => OMA.A327569.two_case e he⟩
