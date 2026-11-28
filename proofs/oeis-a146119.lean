import OMAStatements.S_oeis_a146119

-- Problem: A146119, the Bell numbers mod 29 are periodic with period (p^p - 1)/(p - 1), p = 29.
-- Proof (Touchard's congruence, umbral form): on F_p[X] let L be the linear functional with L(X^n) = B_n.
-- The Bell recurrence says L(X f) = L(f(X + 1)); iterating p times gives L((X^p - X) g) = L(g), so
-- L((X^p - X - 1) g) = 0. In F_p[X]/(X^p - X - 1) the class x of X satisfies x^(p^j) = x + j (Frobenius),
-- hence x^N = prod_j (x + j) = x^p - x = 1 for N = 1 + p + ... + p^(p-1). So X^p - X - 1 divides
-- X^n (X^N - 1), and B_(n+N) = B_n in F_p.

namespace OMA.BellPeriod

open Polynomial Finset

noncomputable def L (p : ℕ) : (ZMod p)[X] →ₗ[ZMod p] ZMod p :=
  Polynomial.lsum fun n => (Nat.bell n : ZMod p) • LinearMap.id

lemma L_monomial (p n : ℕ) (c : ZMod p) : L p (monomial n c) = (Nat.bell n : ZMod p) * c := by
  simp [L, Polynomial.sum_monomial_index]

lemma L_C_mul_X_pow (p n : ℕ) (c : ZMod p) : L p (C c * X ^ n) = (Nat.bell n : ZMod p) * c := by
  rw [C_mul_X_pow_eq_monomial, L_monomial]

lemma L_X_pow (p n : ℕ) : L p (X ^ n) = (Nat.bell n : ZMod p) := by
  simpa using L_C_mul_X_pow p n 1

lemma bell_succ_sum (n : ℕ) :
    Nat.bell (n + 1) = ∑ m ∈ range (n + 1), n.choose m * Nat.bell m := by
  rw [Nat.bell_succ, ← Nat.range_succ_eq_Iic, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [show n + 1 - 1 - j = n - j by omega, Nat.choose_symm hj, Nat.sub_sub_self hj]

lemma L_X_mul (p : ℕ) (f : (ZMod p)[X]) : L p (X * f) = L p (f.comp (X + 1)) := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => rw [mul_add, add_comp, map_add, map_add, hf, hg]
  | monomial n c =>
    rw [← C_mul_X_pow_eq_monomial, mul_left_comm, ← pow_succ', L_C_mul_X_pow, mul_comp, C_comp,
      X_pow_comp, add_pow, Finset.mul_sum, map_sum]
    have h : ∀ m ∈ range (n + 1), L p (C c * (X ^ m * 1 ^ (n - m) * (n.choose m : (ZMod p)[X])))
        = (Nat.bell m : ZMod p) * (c * n.choose m) := by
      intro m _
      rw [one_pow, mul_one, ← C_eq_natCast, show C c * (X ^ m * C (n.choose m : ZMod p))
        = C (c * n.choose m) * X ^ m by rw [C_mul]; ring, L_C_mul_X_pow]
    rw [Finset.sum_congr rfl h, bell_succ_sum]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => by ring

lemma L_prod (p k : ℕ) : ∀ g : (ZMod p)[X],
    L p ((∏ j ∈ range k, (X - C (j : ZMod p))) * g) = L p (g.comp (X + C (k : ZMod p))) := by
  induction k with
  | zero => intro g; simp
  | succ k ih =>
    intro g
    rw [Finset.prod_range_succ']
    simp only [Nat.cast_zero, C_0, sub_zero]
    rw [mul_comm _ X, mul_assoc, L_X_mul, mul_comp, Polynomial.prod_comp]
    have h : ∀ j ∈ range k, (X - C ((j + 1 : ℕ) : ZMod p)).comp (X + 1) = X - C (j : ZMod p) := by
      intro j _
      simp only [sub_comp, X_comp, C_comp]
      push_cast
      simp only [map_add, map_one]
      ring
    rw [Finset.prod_congr rfl h, ih, comp_assoc]
    congr 2
    simp only [add_comp, X_comp, one_comp]
    push_cast
    simp only [map_add, map_one]
    ring

lemma prod_range_eq_univ (p : ℕ) [NeZero p] {R : Type*} [CommMonoid R] (f : ZMod p → R) :
    ∏ j ∈ range p, f (j : ZMod p) = ∏ x : ZMod p, f x := by
  refine Finset.prod_nbij' (fun j => (j : ZMod p)) (fun x => x.val) (by simp) ?_ ?_ ?_ (by simp)
  · intro x _; simpa using ZMod.val_lt x
  · intro j hj; simpa using ZMod.val_cast_of_lt (Finset.mem_range.mp hj)
  · intro x _; simp

lemma prod_univ_X_sub_C (p : ℕ) [Fact p.Prime] :
    ∏ x : ZMod p, (X - C x) = (X ^ p - X : (ZMod p)[X]) := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hroots := FiniteField.roots_X_pow_card_sub_X (ZMod p)
  rw [ZMod.card] at hroots
  have hmon : (X ^ p - X : (ZMod p)[X]).Monic := by
    apply Polynomial.monic_X_pow_sub
    rw [degree_X]; exact_mod_cast hp
  have hdeg := FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod p) hp
  have := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon
    (by rw [hroots, hdeg]; simp)
  rw [hroots] at this
  exact this

lemma prod_sub (p : ℕ) [Fact p.Prime] :
    ∏ j ∈ range p, (X - C (j : ZMod p)) = (X ^ p - X : (ZMod p)[X]) := by
  rw [prod_range_eq_univ p (fun x => X - C x), prod_univ_X_sub_C]

lemma prod_add (p : ℕ) [Fact p.Prime] :
    ∏ j ∈ range p, (X + C (j : ZMod p)) = (X ^ p - X : (ZMod p)[X]) := by
  rw [prod_range_eq_univ p (fun x => X + C x), ← prod_univ_X_sub_C]
  exact Fintype.prod_equiv (Equiv.neg _) _ _ (fun x => by simp [sub_eq_add_neg])

lemma L_kill (p : ℕ) [Fact p.Prime] (g : (ZMod p)[X]) : L p ((X ^ p - X - 1) * g) = 0 := by
  have h := L_prod p p g
  rw [prod_sub, ZMod.natCast_self, C_0, add_zero, comp_X] at h
  rw [sub_mul, map_sub, h, one_mul, sub_self]

lemma dvd_X_pow_sub_one (p : ℕ) [Fact p.Prime] :
    (X ^ p - X - 1 : (ZMod p)[X]) ∣ X ^ (∑ j ∈ range p, p ^ j) - 1 := by
  set I := Ideal.span {(X ^ p - X - 1 : (ZMod p)[X])}
  let π := Ideal.Quotient.mk I
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
  have hx : π X ^ p = π X + 1 := by
    have h0 : π (X ^ p - X - 1) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
    rw [map_sub, map_sub, map_pow, map_one] at h0
    linear_combination h0
  have hfrob : ∀ c : ZMod p, (π X + π (C c)) ^ p = π X ^ p + π (C c) := by
    intro c
    rw [← map_add, ← map_pow, ← ZMod.expand_card]
    simp
  have hpow : ∀ j : ℕ, π X ^ (p ^ j) = π X + π (C (j : ZMod p)) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, pow_mul, ih, hfrob, hx]
      push_cast
      simp only [map_add, map_one]
      ring
  rw [map_sub, map_pow, map_one, ← Finset.prod_pow_eq_pow_sum, Finset.prod_congr rfl
    (fun j _ => hpow j)]
  have : ∏ j ∈ range p, (π X + π (C (j : ZMod p))) = π (X ^ p - X) := by
    rw [← prod_add, map_prod]; simp
  rw [this, map_sub, map_pow, hx]
  ring

theorem bell_period (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Nat.bell (n + ∑ j ∈ range p, p ^ j) % p = Nat.bell n % p := by
  obtain ⟨h, hh⟩ := dvd_X_pow_sub_one p
  have key : L p (X ^ n * (X ^ (∑ j ∈ range p, p ^ j) - 1)) = 0 := by
    rw [hh, mul_left_comm, L_kill]
  rw [mul_sub, mul_one, ← pow_add, map_sub, L_X_pow, L_X_pow, sub_eq_zero] at key
  exact (ZMod.natCast_eq_natCast_iff' _ _ p).mp key

end OMA.BellPeriod

theorem OMA.solution : type_of% @OMA.S_oeis_a146119.main := by
  intro n
  have : Fact (Nat.Prime 29) := ⟨by norm_num⟩
  have h := OMA.BellPeriod.bell_period 29 n
  have hN : ∑ j ∈ Finset.range 29, 29 ^ j = 91703076898614683377208150526107718802981 := by
    simp [Finset.sum_range_succ]
  rw [hN] at h
  exact h
