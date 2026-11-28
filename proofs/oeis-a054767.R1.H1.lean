import OMAReductions.R_oeis_a054767_R1

/-!
# Proof of `oeis-a054767.R1.H1`

Proves the theorem of Touchard (1933) and Hall (1934): for every prime `p`,
`N_p = (p ^ p - 1) / (p - 1)` is a positive period of the Bell numbers modulo `p`.

Define the `ZMod p`-linear umbral functional `φ : Polynomial (ZMod p) →ₗ[ZMod p] ZMod p` by
`φ (X ^ n) = (Nat.bell n : ZMod p)`.
1. By `Nat.bell_succ`, `φ (P.comp (X + 1)) = φ (X * P)` for every `P : Polynomial (ZMod p)`.
2. Induction on `k` yields `φ ((∏ j ∈ range k, (X - C (j : ZMod p))) * P) = φ (P.comp (X + C (k : ZMod p)))`.
3. At `k = p`, `∏ j ∈ range p, (X - C (j : ZMod p)) = X ^ p - X` and `P.comp (X + C (p : ZMod p)) = P`,
   so `φ ((X ^ p - X - 1) * P) = 0` for all `P` (Touchard's congruence).
4. In the quotient ring `Polynomial (ZMod p) ⧸ Ideal.span {X ^ p - X - 1}`, Frobenius gives
   `x ^ (p ^ k) = x + k` by induction on `k`, so
   `x ^ N_p = ∏ k ∈ range p, (x + k) = x ^ p - x = 1`.
5. Hence `(X ^ p - X - 1) ∣ X ^ n * (X ^ N_p - 1)`, so `φ (X ^ (n + N_p)) = φ (X ^ n)`,
   i.e. `(n + N_p).bell % p = n.bell % p` for all `n : ℕ`.
-/

namespace OeisA054767R1H1Proof

open Polynomial Finset

private def umbral (p : ℕ) (P : Polynomial (ZMod p)) : ZMod p :=
  P.sum fun i c => c * (Nat.bell i : ZMod p)

private lemma umbral_add (p : ℕ) (P Q : Polynomial (ZMod p)) :
    umbral p (P + Q) = umbral p P + umbral p Q := by
  unfold umbral
  exact Polynomial.sum_add_index P Q (fun i c => c * (Nat.bell i : ZMod p)) (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

private lemma umbral_sub (p : ℕ) (P Q : Polynomial (ZMod p)) :
    umbral p (P - Q) = umbral p P - umbral p Q := by
  have h := umbral_add p (P - Q) Q
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm

private lemma umbral_zero (p : ℕ) : umbral p 0 = 0 := by
  unfold umbral; simp

private lemma umbral_monomial (p n : ℕ) (c : ZMod p) :
    umbral p (Polynomial.monomial n c) = c * (Nat.bell n : ZMod p) := by
  unfold umbral
  exact Polynomial.sum_monomial_index c (fun i a => a * (Nat.bell i : ZMod p)) (zero_mul _)

private lemma umbral_X_pow (p n : ℕ) :
    umbral p (X ^ n) = (Nat.bell n : ZMod p) := by
  rw [Polynomial.X_pow_eq_monomial, umbral_monomial, one_mul]

private lemma umbral_C_mul (p : ℕ) (c : ZMod p) (P : Polynomial (ZMod p)) :
    umbral p (C c * P) = c * umbral p P := by
  induction P using Polynomial.induction_on' with
  | add P Q ihP ihQ =>
    rw [mul_add, umbral_add, umbral_add, mul_add, ihP, ihQ]
  | monomial n a =>
    rw [Polynomial.C_mul_monomial, umbral_monomial, umbral_monomial, mul_assoc]

private lemma umbral_comp_X_add_one (p : ℕ) (P : Polynomial (ZMod p)) :
    umbral p (P.comp (X + 1)) = umbral p (X * P) := by
  induction P using Polynomial.induction_on' with
  | add P Q ihP ihQ =>
    rw [Polynomial.add_comp, mul_add, umbral_add, umbral_add, ihP, ihQ]
  | monomial n c =>
    have hmon : Polynomial.monomial n c = C c * X ^ n := by
      rw [Polynomial.C_mul_X_pow_eq_monomial]
    rw [hmon, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp, Polynomial.X_comp]
    rw [mul_left_comm, umbral_C_mul, umbral_C_mul]
    congr 1
    rw [add_pow, ← pow_succ', umbral_X_pow]
    have hsum : umbral p (∑ m ∈ range (n + 1), X ^ m * 1 ^ (n - m) * (n.choose m : Polynomial (ZMod p))) =
        ∑ m ∈ range (n + 1), umbral p (C (n.choose m : ZMod p) * X ^ m) := by
      have hlin : ∀ (s : Finset ℕ) (f : ℕ → Polynomial (ZMod p)),
          umbral p (∑ m ∈ s, f m) = ∑ m ∈ s, umbral p (f m) := by
        intro s f
        induction s using Finset.induction_on with
        | empty => simp [umbral_zero]
        | insert a t ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha, umbral_add, ih]
      rw [hlin]
      refine Finset.sum_congr rfl fun m _ => ?_
      simp [mul_comm]
    rw [hsum]
    have hterms : ∑ m ∈ range (n + 1), umbral p (C (n.choose m : ZMod p) * X ^ m) =
        ∑ m ∈ range (n + 1), ((n.choose m * Nat.bell m : ℕ) : ZMod p) := by
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [umbral_C_mul, umbral_X_pow, Nat.cast_mul]
    rw [hterms, ← Nat.cast_sum]
    congr 1
    rw [Nat.bell_succ, show Finset.Iic n = Finset.range (n + 1) by ext x; simp]
    rw [← Finset.sum_range_reflect (fun m => n.choose m * Nat.bell m) (n + 1)]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_range] at hm
    have hsub : n + 1 - 1 - m = n - m := by omega
    rw [hsub, Nat.choose_symm (by omega : m ≤ n)]

private lemma umbral_falling_mul (p : ℕ) :
    ∀ (k : ℕ) (P : Polynomial (ZMod p)),
      umbral p ((∏ j ∈ range k, (X - C (j : ZMod p))) * P) =
        umbral p (P.comp (X + C (k : ZMod p))) := by
  intro k
  induction k with
  | zero =>
    intro P
    simp
  | succ k ih =>
    intro P
    rw [Finset.prod_range_succ, mul_assoc]
    have hstep := ih ((X - C (k : ZMod p)) * P)
    rw [hstep, Polynomial.mul_comp, Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp]
    have hcancel : (X + C (k : ZMod p) - C (k : ZMod p)) = X := by ring
    rw [hcancel, ← umbral_comp_X_add_one, Polynomial.comp_assoc]
    have hcomp : (X + C (k : ZMod p)).comp (X + 1) = X + C ((k + 1 : ℕ) : ZMod p) := by
      simp [Polynomial.add_comp, Polynomial.X_comp, add_assoc, add_comm]
    rw [hcomp]

private lemma prod_X_sub_eq_X_pow_sub_X {p : ℕ} (hp : p.Prime) :
    ∏ j ∈ range p, (X - C (j : ZMod p)) = X ^ p - X := by
  have : Fact p.Prime := ⟨hp⟩
  have h1 : ∏ j ∈ range p, (X - C (j : ZMod p)) = ∏ a : ZMod p, (X - C a) := by
    refine Finset.prod_nbij' (fun j => (j : ZMod p)) (fun a => a.val) ?_ ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro a _; exact Finset.mem_range.mpr (ZMod.val_lt a)
    · intro j hj; exact ZMod.val_natCast_of_lt (Finset.mem_range.mp hj)
    · intro a _; exact ZMod.natCast_zmod_val a
    · intro _ _; rfl
  rw [h1]
  have hdvd : (∏ a : ZMod p, (X - C a)) ∣ X ^ p - X := by
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro a _ b _ hab
      exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hab))
    · intro a _
      rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot, eval_sub, eval_pow, eval_X, ZMod.pow_card,
        sub_self]
  have hmon1 : (∏ a : ZMod p, (X - C a)).Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_sub_C _)
  have hmon2 : (X ^ p - X : Polynomial (ZMod p)).Monic := by
    have hlt : (X : Polynomial (ZMod p)).degree < (X ^ p : Polynomial (ZMod p)).degree := by
      rw [Polynomial.degree_X, Polynomial.degree_X_pow]; exact_mod_cast hp.one_lt
    exact (Polynomial.monic_X_pow p).sub_of_left hlt
  have hdeg1 : (∏ a : ZMod p, (X - C a)).natDegree = p := by
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_sub_C _)]
    simp [ZMod.card p]
  have hdeg2 : (X ^ p - X : Polynomial (ZMod p)).natDegree ≤ p := by
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le (Polynomial.natDegree_X_pow_le p) ?_)
    rw [Polynomial.natDegree_X]; exact hp.one_le
  exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmon1 hmon2 hdvd (by omega)).symm

private lemma umbral_touchard_mul {p : ℕ} (hp : p.Prime) (P : Polynomial (ZMod p)) :
    umbral p ((X ^ p - X - 1) * P) = 0 := by
  have h := umbral_falling_mul p p P
  rw [prod_X_sub_eq_X_pow_sub_X hp] at h
  have hp0 : (p : ZMod p) = 0 := ZMod.natCast_self p
  rw [hp0, map_zero, add_zero, Polynomial.comp_X] at h
  have hsub : (X ^ p - X - 1) * P = (X ^ p - X) * P - P := by ring
  rw [hsub, umbral_sub, h, sub_self]

private lemma sum_pow_eq_div {p : ℕ} (hp : 2 ≤ p) :
    ∑ k ∈ range p, p ^ k = (p ^ p - 1) / (p - 1) := by
  have hgeom : (p - 1) * ∑ k ∈ range p, p ^ k = p ^ p - 1 := by
    have h := geom_sum_mul (p : ℤ) p
    have hge1 : 1 ≤ p ^ p := Nat.one_le_pow p p (by omega)
    zify [show 1 ≤ p by omega, hge1]
    linarith
  rw [← hgeom, Nat.mul_div_cancel_left _ (by omega)]

private lemma dvd_X_pow_period_sub_one {p : ℕ} (hp : p.Prime) :
    (X ^ p - X - 1 : Polynomial (ZMod p)) ∣ X ^ ((p ^ p - 1) / (p - 1)) - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  let M : Polynomial (ZMod p) := X ^ p - X - 1
  let I : Ideal (Polynomial (ZMod p)) := Ideal.span ({M} : Set (Polynomial (ZMod p)))
  let π : Polynomial (ZMod p) →+* Polynomial (ZMod p) ⧸ I := Ideal.Quotient.mk I
  let x : Polynomial (ZMod p) ⧸ I := π X
  have hx_rel : x ^ p = x + 1 := by
    have hM0 : π M = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton M))
    have h1 : x ^ p - x - 1 = 0 := by simpa [x, M, map_sub, map_pow, map_one] using hM0
    exact eq_add_of_sub_eq' (sub_eq_zero.mp h1)
  have hchar : CharP (Polynomial (ZMod p) ⧸ I) p := by
    refine ⟨fun n => ?_⟩
    constructor
    · intro hn
      have hcast : π (C (n : ZMod p)) = 0 := by simpa [map_natCast] using hn
      have hmem : C (n : ZMod p) ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hcast
      rw [Ideal.mem_span_singleton] at hmem
      obtain ⟨Q, hQ⟩ := hmem
      by_contra hndvd
      have hc_ne0 : (n : ZMod p) ≠ 0 := by
        intro h0; exact hndvd ((ZMod.natCast_eq_zero_iff n p).mp h0)
      have hQ_ne0 : Q ≠ 0 := by
        intro h0; rw [h0, mul_zero] at hQ; exact hc_ne0 (C_eq_zero.mp hQ)
      have hdegM : M.natDegree = p := by
        have hp2 : 2 ≤ p := hp.two_le
        have h1 : (X ^ p - X - 1 : Polynomial (ZMod p)) = X ^ p + (-(X + 1)) := by ring
        dsimp [M]; rw [h1]
        have hlt : (-(X + 1) : Polynomial (ZMod p)).natDegree < (X ^ p : Polynomial (ZMod p)).natDegree := by
          rw [Polynomial.natDegree_neg, Polynomial.natDegree_X_pow]
          have : (X + 1 : Polynomial (ZMod p)).natDegree ≤ 1 := by compute_degree!
          omega
        rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt hlt, Polynomial.natDegree_X_pow]
      have hM_ne0 : M ≠ 0 := by
        intro h0; rw [h0] at hdegM; simp at hdegM; have := hp.two_le; omega
      have hdeg_lhs : (C (n : ZMod p)).natDegree = 0 := Polynomial.natDegree_C _
      have hdeg_rhs : (M * Q).natDegree = M.natDegree + Q.natDegree :=
        Polynomial.natDegree_mul hM_ne0 hQ_ne0
      rw [hQ, hdeg_rhs, hdegM] at hdeg_lhs
      have := hp.two_le
      omega
    · intro hdvd
      have : (n : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff n p).mpr hdvd
      have h1 : ((n : ℕ) : Polynomial (ZMod p) ⧸ I) = π (C (n : ZMod p)) := by simp
      rw [h1, this, map_zero, map_zero]
  have hfrob : ∀ k : ℕ, x ^ (p ^ k) = x + (k : Polynomial (ZMod p) ⧸ I) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, pow_mul, ih, add_pow_char, hx_rel]
      have hk_pow : ((k : Polynomial (ZMod p) ⧸ I)) ^ p = (k : Polynomial (ZMod p) ⧸ I) := by
        have h1 : ((k : ZMod p) ^ p) = (k : ZMod p) := ZMod.pow_card _
        have h2 := congrArg (fun a : ZMod p => π (C a)) h1
        rw [map_pow, map_pow, map_natCast, map_natCast] at h2
        exact h2
      rw [hk_pow]
      push_cast
      ring
  have hprod : x ^ ((p ^ p - 1) / (p - 1)) = 1 := by
    rw [← sum_pow_eq_div hp.two_le, ← Finset.prod_pow_eq_pow_sum]
    have h1 : ∏ k ∈ range p, x ^ (p ^ k) = ∏ k ∈ range p, (x + (k : Polynomial (ZMod p) ⧸ I)) :=
      Finset.prod_congr rfl fun k _ => hfrob k
    rw [h1]
    have h2 : ∏ k ∈ range p, (x + (k : Polynomial (ZMod p) ⧸ I)) =
        ∏ j ∈ range p, (x - (j : Polynomial (ZMod p) ⧸ I)) := by
      refine Finset.prod_nbij' (fun k => if k = 0 then 0 else p - k)
        (fun j => if j = 0 then 0 else p - j) ?_ ?_ ?_ ?_ ?_
      · intro k hk; rw [Finset.mem_range] at hk ⊢; split_ifs <;> omega
      · intro j hj; rw [Finset.mem_range] at hj ⊢; split_ifs <;> omega
      · intro k hk; rw [Finset.mem_range] at hk; split_ifs <;> omega
      · intro j hj; rw [Finset.mem_range] at hj; split_ifs <;> omega
      · intro k hk
        rw [Finset.mem_range] at hk
        split_ifs with hk0
        · subst hk0; simp
        · have hsub : ((p - k : ℕ) : Polynomial (ZMod p) ⧸ I) = -(k : Polynomial (ZMod p) ⧸ I) := by
            have hadd : ((p - k : ℕ) : Polynomial (ZMod p) ⧸ I) + (k : Polynomial (ZMod p) ⧸ I) = 0 := by
              rw [← Nat.cast_add, Nat.sub_add_cancel (by omega : k ≤ p), CharP.cast_eq_zero]
            exact eq_neg_of_add_eq_zero_left hadd
          rw [hsub, sub_neg_eq_add]
    rw [h2]
    have h3 : ∏ j ∈ range p, (x - (j : Polynomial (ZMod p) ⧸ I)) =
        π (∏ j ∈ range p, (X - C (j : ZMod p))) := by
      rw [map_prod]
      refine Finset.prod_congr rfl fun j _ => by simp [x]
    rw [h3, prod_X_sub_eq_X_pow_sub_X hp]
    simp only [map_sub, map_pow, ← show x = π X from rfl]
    rw [hx_rel]
    ring
  have hzero : π (X ^ ((p ^ p - 1) / (p - 1)) - 1) = 0 := by
    simp only [map_sub, map_pow, map_one, ← show x = π X from rfl, hprod, sub_self]
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hzero)

end OeisA054767R1H1Proof

theorem OMA.solution : OMA.R_oeis_a054767_R1.H1 := by
  intro p hp
  have hp2 : 2 ≤ p := hp.two_le
  set N := (p ^ p - 1) / (p - 1)
  have hN_pos : 0 < N := by
    have hsum := OeisA054767R1H1Proof.sum_pow_eq_div hp2
    have h0 : 0 ∈ Finset.range p := Finset.mem_range.mpr hp.pos
    have hge : 1 ≤ ∑ k ∈ Finset.range p, p ^ k := by
      have := Finset.single_le_sum (f := fun k => p ^ k) (fun _ _ => Nat.zero_le _) h0
      simpa using this
    omega
  refine ⟨hN_pos, fun n => ?_⟩
  obtain ⟨Q, hQ⟩ := OeisA054767R1H1Proof.dvd_X_pow_period_sub_one hp
  have hmul : (Polynomial.X ^ (n + N) - Polynomial.X ^ n : Polynomial (ZMod p)) =
      (Polynomial.X ^ p - Polynomial.X - 1) * (Polynomial.X ^ n * Q) := by
    calc (Polynomial.X ^ (n + N) - Polynomial.X ^ n : Polynomial (ZMod p))
        = Polynomial.X ^ n * (Polynomial.X ^ N - 1) := by rw [pow_add]; ring
      _ = Polynomial.X ^ n * ((Polynomial.X ^ p - Polynomial.X - 1) * Q) := by rw [hQ]
      _ = (Polynomial.X ^ p - Polynomial.X - 1) * (Polynomial.X ^ n * Q) := by ring
  have h0 : OeisA054767R1H1Proof.umbral p (Polynomial.X ^ (n + N) - Polynomial.X ^ n) = 0 := by
    rw [hmul]
    exact OeisA054767R1H1Proof.umbral_touchard_mul hp _
  rw [OeisA054767R1H1Proof.umbral_sub, OeisA054767R1H1Proof.umbral_X_pow,
    OeisA054767R1H1Proof.umbral_X_pow] at h0
  have heq : (Nat.bell (n + N) : ZMod p) = (Nat.bell n : ZMod p) := sub_eq_zero.mp h0
  exact (ZMod.natCast_eq_natCast_iff _ _ p).mp heq
