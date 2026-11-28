import OMAStatements.S_oeis_a317534
import Mathlib

/-!
# Proof of the A317534 classification

The poset of factorizations of `k` (refinement order) fails to be a lattice iff some `s` of prime signature
`{5}`, `{1,3}` or `{1,1,2}` divides `k`.

* Non-lattice direction: explicit pairs with two incomparable minimal upper bounds for `p^5`, `p q^3`,
  `p q r^2`, and non-lattice passes to multiples, since the factorizations of `k` embed (as `F ↦ F + P`, `P`
  the prime factors of `n / k`) as the principal ideal below `k ::ₘ P` in the factorizations of `n`.
* Lattice direction: the remaining `k` are squarefree, `p^a` (`a ≤ 4`), `p^2 q` or `p^2 q^2`. Every poset here
  is finite-height with a bottom and a top, and meets follow from joins (and joins from meets) by a cardinality
  extremum. Squarefree: meets are all nonunit gcds. Otherwise only incomparable pairs with at least three
  factors need checking, and for `p^2 q^2` these are three explicit pairs.
-/

namespace OMA.A317534Proof
open OMA.S_oeis_a317534

/-! ## Generic facts about factorizations and refinement -/

/-- `z` is a least upper bound of `x` and `y` among the factorizations of `k`. -/
def JoinSpec (k : ℕ) (x y z : Multiset ℕ) : Prop :=
  IsFact k z ∧ Refines x z ∧ Refines y z ∧ ∀ u, IsFact k u → Refines x u → Refines y u → Refines z u

/-- `w` is a greatest lower bound of `x` and `y` among the factorizations of `k`. -/
def MeetSpec (k : ℕ) (x y w : Multiset ℕ) : Prop :=
  IsFact k w ∧ Refines w x ∧ Refines w y ∧ ∀ u, IsFact k u → Refines u x → Refines u y → Refines u w

theorem JoinSpec.symm {k : ℕ} {x y z : Multiset ℕ} (h : JoinSpec k x y z) : JoinSpec k y x z :=
  ⟨h.1, h.2.2.1, h.2.1, fun u hu h1 h2 => h.2.2.2 u hu h2 h1⟩

theorem isFact_ne_one {k : ℕ} {F : Multiset ℕ} (h : IsFact k F) : ∀ g ∈ F, g ≠ 1 := by
  intro g hg
  have := h.1 g hg
  omega

theorem map_eq_cons' {α β : Type*} (f : α → β) (s : Multiset α) (t : Multiset β) (b : β)
    (h : s.map f = b ::ₘ t) : ∃ a u, s = a ::ₘ u ∧ f a = b ∧ u.map f = t := by
  have hb : b ∈ s.map f := by
    rw [h]
    exact Multiset.mem_cons_self _ _
  obtain ⟨a, h1, rfl⟩ := Multiset.mem_map.mp hb
  obtain ⟨u, rfl⟩ := Multiset.exists_cons_of_mem h1
  rw [Multiset.map_cons, Multiset.cons_inj_right] at h
  exact ⟨a, u, rfl, rfl, h⟩

theorem map_eq_add' {α β : Type*} (f : α → β) (t r : Multiset β) :
    ∀ s : Multiset α, s.map f = t + r → ∃ s1 s2, s = s1 + s2 ∧ s1.map f = t ∧ s2.map f = r := by
  induction t using Multiset.induction with
  | empty =>
    intro s h
    refine ⟨0, s, by simp, by simp, ?_⟩
    simpa using h
  | cons b t ih =>
    intro s h
    rw [Multiset.cons_add] at h
    obtain ⟨a, u, rfl, hab, hu⟩ := map_eq_cons' f s _ b h
    obtain ⟨s1, s2, rfl, h1, h2⟩ := ih u hu
    exact ⟨a ::ₘ s1, s2, by rw [Multiset.cons_add], by rw [Multiset.map_cons, h1, hab], h2⟩

theorem lift_join {α β : Type*} (f : α → β) :
    ∀ (T : Multiset (Multiset β)) (S : Multiset α), S.map f = T.join →
      ∃ U : Multiset (Multiset α), U.join = S ∧ U.map (Multiset.map f) = T := by
  intro T
  induction T using Multiset.induction with
  | empty =>
    intro S h
    refine ⟨0, ?_, by simp⟩
    simp at h
    simp [h]
  | cons t T ih =>
    intro S h
    rw [Multiset.join_cons] at h
    obtain ⟨S1, S2, rfl, h1, h2⟩ := map_eq_add' f t T.join S h
    obtain ⟨U, hU1, hU2⟩ := ih S2 h2
    exact ⟨S1 ::ₘ U, by rw [Multiset.join_cons, hU1], by rw [Multiset.map_cons, hU2, h1]⟩

theorem join_map_join {α : Type*} (U : Multiset (Multiset (Multiset α))) :
    (U.map Multiset.join).join = U.join.join := by
  induction U using Multiset.induction with
  | empty => simp
  | cons a U ih => simp [ih]

theorem join_map_singleton (F : Multiset ℕ) : (F.map (fun x => ({x} : Multiset ℕ))).join = F := by
  induction F using Multiset.induction with
  | empty => simp
  | cons a F ih => simp [ih, Multiset.singleton_add]

theorem refines_refl (F : Multiset ℕ) : Refines F F :=
  ⟨F.map (fun x => ({x} : Multiset ℕ)), join_map_singleton F, by simp [Multiset.map_map]⟩

theorem refines_trans {F G K : Multiset ℕ} (h1 : Refines F G) (h2 : Refines G K) : Refines F K := by
  obtain ⟨H1, hj1, hm1⟩ := h1
  obtain ⟨H2, hj2, hm2⟩ := h2
  obtain ⟨U, hU1, hU2⟩ := lift_join Multiset.prod H2 H1 (by rw [hm1, hj2])
  refine ⟨U.map Multiset.join, ?_, ?_⟩
  · rw [← hj1, ← hU1]
    exact join_map_join U
  · rw [← hm2, ← hU2, Multiset.map_map, Multiset.map_map]
    apply Multiset.map_congr rfl
    intro B _
    simp [Function.comp, Multiset.prod_join]

theorem refines_top (F : Multiset ℕ) : Refines F {F.prod} := ⟨{F}, by simp, by simp⟩

theorem card_join_aux : ∀ H : Multiset (Multiset ℕ), (∀ b ∈ H, b ≠ 0) →
    Multiset.card H ≤ Multiset.card H.join ∧
      (Multiset.card H = Multiset.card H.join → H.join = H.map Multiset.prod) := by
  intro H
  induction H using Multiset.induction with
  | empty => intro _; simp
  | cons b H ih =>
    intro hne
    have hb : b ≠ 0 := hne b (Multiset.mem_cons_self _ _)
    obtain ⟨ih1, ih2⟩ := ih (fun c hc => hne c (Multiset.mem_cons_of_mem hc))
    have hb1 : 1 ≤ Multiset.card b := Multiset.card_pos.mpr hb
    rw [Multiset.join_cons, Multiset.card_add, Multiset.card_cons, Multiset.map_cons]
    refine ⟨by omega, fun heq => ?_⟩
    have h1 : Multiset.card b = 1 := by omega
    have h2 : Multiset.card H = Multiset.card H.join := by omega
    obtain ⟨a, rfl⟩ := Multiset.card_eq_one.mp h1
    rw [ih2 h2]
    simp [Multiset.singleton_add]

theorem refines_card {F G : Multiset ℕ} (h : Refines F G) (hG : ∀ g ∈ G, g ≠ 1) :
    Multiset.card G ≤ Multiset.card F ∧ (Multiset.card G = Multiset.card F → F = G) := by
  obtain ⟨H, rfl, rfl⟩ := h
  have hne : ∀ b ∈ H, b ≠ 0 := by
    intro b hb h0
    apply hG b.prod (Multiset.mem_map_of_mem _ hb)
    rw [h0, Multiset.prod_zero]
  obtain ⟨h1, h2⟩ := card_join_aux H hne
  rw [Multiset.card_map]
  exact ⟨h1, h2⟩

theorem one_merge_aux : ∀ H : Multiset (Multiset ℕ), (∀ b ∈ H, b ≠ 0) →
    Multiset.card H.join = Multiset.card H + 1 →
    ∃ a b s, H.join = a ::ₘ b ::ₘ s ∧ H.map Multiset.prod = (a * b) ::ₘ s := by
  intro H
  induction H using Multiset.induction with
  | empty => intro _ h; simp at h
  | cons t H ih =>
    intro hne hc
    have ht : t ≠ 0 := hne t (Multiset.mem_cons_self _ _)
    have hne' : ∀ c ∈ H, c ≠ 0 := fun c hc => hne c (Multiset.mem_cons_of_mem hc)
    obtain ⟨hH1, hH2⟩ := card_join_aux H hne'
    have ht1 : 1 ≤ Multiset.card t := Multiset.card_pos.mpr ht
    rw [Multiset.join_cons, Multiset.card_add, Multiset.card_cons] at hc
    rcases Nat.lt_or_ge 1 (Multiset.card t) with hlt | hle
    · have e2 : Multiset.card t = 2 := by omega
      have e3 : Multiset.card H = Multiset.card H.join := by omega
      obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.mp e2
      refine ⟨a, b, H.map Multiset.prod, ?_, ?_⟩
      · rw [Multiset.join_cons, hH2 e3]
        simp [Multiset.singleton_add]
      · simp
    · have e1 : Multiset.card t = 1 := by omega
      have e3 : Multiset.card H.join = Multiset.card H + 1 := by omega
      obtain ⟨c, rfl⟩ := Multiset.card_eq_one.mp e1
      obtain ⟨a, b, s, hj, hm⟩ := ih hne' e3
      refine ⟨a, b, c ::ₘ s, ?_, ?_⟩
      · rw [Multiset.join_cons, hj, Multiset.singleton_add, Multiset.cons_swap c a,
          Multiset.cons_swap c b]
      · rw [Multiset.map_cons, hm, Multiset.prod_singleton, Multiset.cons_swap]

theorem refines_one_merge {F G : Multiset ℕ} (h : Refines F G) (hG : ∀ g ∈ G, g ≠ 1)
    (hc : Multiset.card F = Multiset.card G + 1) :
    ∃ a b s, F = a ::ₘ b ::ₘ s ∧ G = (a * b) ::ₘ s := by
  obtain ⟨H, rfl, rfl⟩ := h
  have hne : ∀ b ∈ H, b ≠ 0 := by
    intro b hb h0
    apply hG b.prod (Multiset.mem_map_of_mem _ hb)
    rw [h0, Multiset.prod_zero]
  rw [Multiset.card_map] at hc
  exact one_merge_aux H hne hc

theorem prime_multiset_eq {Q R : Multiset ℕ} (hQ : ∀ q ∈ Q, q.Prime) (hR : ∀ r ∈ R, r.Prime)
    (h : Q.prod = R.prod) : Q = R := by
  have e1 : UniqueFactorizationMonoid.normalizedFactors Q.prod = Q :=
    UniqueFactorizationMonoid.normalizedFactors_prod_of_prime (fun q hq => Nat.prime_iff.mp (hQ q hq))
  have e2 : UniqueFactorizationMonoid.normalizedFactors R.prod = R :=
    UniqueFactorizationMonoid.normalizedFactors_prod_of_prime (fun r hr => Nat.prime_iff.mp (hR r hr))
  calc Q = UniqueFactorizationMonoid.normalizedFactors Q.prod := e1.symm
    _ = UniqueFactorizationMonoid.normalizedFactors R.prod := by rw [h]
    _ = R := e2

theorem map_prod_pf {F : Multiset ℕ} (hF : ∀ x ∈ F, 2 ≤ x) :
    (F.map (fun x => (x.primeFactorsList : Multiset ℕ))).map Multiset.prod = F := by
  rw [Multiset.map_map]
  conv_rhs => rw [← Multiset.map_id' F]
  apply Multiset.map_congr rfl
  intro x hx
  simp only [Function.comp, Multiset.prod_coe]
  exact Nat.prod_primeFactorsList (by have := hF x hx; omega)

theorem refines_bottom {Q F : Multiset ℕ} (hQ : ∀ q ∈ Q, q.Prime) (hF : ∀ x ∈ F, 2 ≤ x)
    (h : Q.prod = F.prod) : Refines Q F := by
  refine ⟨F.map (fun x => (x.primeFactorsList : Multiset ℕ)), ?_, map_prod_pf hF⟩
  symm
  apply prime_multiset_eq hQ
  · intro r hr
    obtain ⟨s, hs, hrs⟩ := Multiset.mem_join.mp hr
    obtain ⟨x, _, rfl⟩ := Multiset.mem_map.mp hs
    exact Nat.prime_of_mem_primeFactorsList (Multiset.mem_coe.mp hrs)
  · rw [h, Multiset.prod_join, map_prod_pf hF]

theorem merge12 (a b c : ℕ) : Refines (a ::ₘ b ::ₘ c ::ₘ 0) ((a * b) ::ₘ c ::ₘ 0) :=
  ⟨(a ::ₘ b ::ₘ 0) ::ₘ (c ::ₘ 0) ::ₘ 0, by simp [Multiset.singleton_add, Multiset.cons_add],
    by simp⟩

theorem merge13 (a b c : ℕ) : Refines (a ::ₘ b ::ₘ c ::ₘ 0) ((a * c) ::ₘ b ::ₘ 0) := by
  refine ⟨(a ::ₘ c ::ₘ 0) ::ₘ (b ::ₘ 0) ::ₘ 0, ?_, by simp⟩
  rw [Multiset.cons_swap b c]
  simp [Multiset.singleton_add, Multiset.cons_add]

theorem merge23 (a b c : ℕ) : Refines (a ::ₘ b ::ₘ c ::ₘ 0) ((b * c) ::ₘ a ::ₘ 0) := by
  refine ⟨(b ::ₘ c ::ₘ 0) ::ₘ (a ::ₘ 0) ::ₘ 0, ?_, by simp⟩
  rw [Multiset.cons_swap a b, Multiset.cons_swap a c]
  simp [Multiset.singleton_add, Multiset.cons_add]

theorem refines_swap2 {F : Multiset ℕ} {a b : ℕ} (h : Refines F (a ::ₘ b ::ₘ 0)) :
    Refines F (b ::ₘ a ::ₘ 0) := by
  rw [Multiset.cons_swap]
  exact h

-- PART A BEGIN
-- Exponent vector of n at the primes p and q.
noncomputable def A_vv (p q n : ℕ) : ℕ × ℕ := (n.factorization p, n.factorization q)

-- Concrete exponent-vector images of the factorizations involved.
def A_Zv0 : Multiset (ℕ × ℕ) := (1, 0) ::ₘ (1, 0) ::ₘ (0, 1) ::ₘ (0, 1) ::ₘ 0
def A_Ev0 : Multiset (ℕ × ℕ) := (0, 2) ::ₘ (1, 0) ::ₘ (1, 0) ::ₘ 0
def A_Fv0 : Multiset (ℕ × ℕ) := (2, 0) ::ₘ (0, 1) ::ₘ (0, 1) ::ₘ 0
def A_Gv0 : Multiset (ℕ × ℕ) := (1, 1) ::ₘ (1, 0) ::ₘ (0, 1) ::ₘ 0
def A_Av0 : Multiset (ℕ × ℕ) := (2, 0) ::ₘ (0, 2) ::ₘ 0
def A_Bv0 : Multiset (ℕ × ℕ) := (1, 2) ::ₘ (1, 0) ::ₘ 0
def A_Cv0 : Multiset (ℕ × ℕ) := (2, 1) ::ₘ (0, 1) ::ₘ 0

-- Finite checks on the concrete vectors.
theorem A_dec_Z : ∀ v ∈ A_Zv0, ∀ w ∈ A_Zv0.erase v,
    (v + w) ::ₘ (A_Zv0.erase v).erase w = A_Ev0 ∨ (v + w) ::ₘ (A_Zv0.erase v).erase w = A_Fv0 ∨
      (v + w) ::ₘ (A_Zv0.erase v).erase w = A_Gv0 := by
  decide

theorem A_ne_EF : A_Ev0 ≠ A_Fv0 := by decide
theorem A_ne_EG : A_Ev0 ≠ A_Gv0 := by decide
theorem A_ne_FG : A_Fv0 ≠ A_Gv0 := by decide

theorem A_dec_EF : ∀ v ∈ A_Ev0, ∀ w ∈ A_Ev0.erase v, ∀ v' ∈ A_Fv0, ∀ w' ∈ A_Fv0.erase v',
    (v + w) ::ₘ (A_Ev0.erase v).erase w = (v' + w') ::ₘ (A_Fv0.erase v').erase w' →
      (v + w) ::ₘ (A_Ev0.erase v).erase w = A_Av0 := by
  decide

theorem A_dec_EG : ∀ v ∈ A_Ev0, ∀ w ∈ A_Ev0.erase v, ∀ v' ∈ A_Gv0, ∀ w' ∈ A_Gv0.erase v',
    (v + w) ::ₘ (A_Ev0.erase v).erase w = (v' + w') ::ₘ (A_Gv0.erase v').erase w' →
      (v + w) ::ₘ (A_Ev0.erase v).erase w = A_Bv0 := by
  decide

theorem A_dec_FG : ∀ v ∈ A_Fv0, ∀ w ∈ A_Fv0.erase v, ∀ v' ∈ A_Gv0, ∀ w' ∈ A_Gv0.erase v',
    (v + w) ::ₘ (A_Fv0.erase v).erase w = (v' + w') ::ₘ (A_Gv0.erase v').erase w' →
      (v + w) ::ₘ (A_Fv0.erase v).erase w = A_Cv0 := by
  decide

-- Exponent vectors: multiplicativity and the values on p, q and p^i q^j.
theorem A_vv_mul (p q : ℕ) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    A_vv p q (a * b) = A_vv p q a + A_vv p q b := by
  simp [A_vv, Nat.factorization_mul ha hb]

theorem A_vv_p {p q : ℕ} (hp : p.Prime) (hpq : p ≠ q) : A_vv p q p = (1, 0) := by
  simp [A_vv, hp.factorization, Ne.symm hpq]

theorem A_vv_q {p q : ℕ} (hq : q.Prime) (hpq : p ≠ q) : A_vv p q q = (0, 1) := by
  simp [A_vv, hq.factorization, hpq]

theorem A_vv_pow {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (i j : ℕ) :
    A_vv p q (p ^ i * q ^ j) = (i, j) := by
  rw [A_vv_mul p q (pow_ne_zero i hp.ne_zero) (pow_ne_zero j hq.ne_zero)]
  simp [A_vv, hp.factorization_pow, hq.factorization_pow, hpq, Ne.symm hpq]

-- A divisor of p^2 q^2 is determined by its exponent vector.
theorem A_key {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {d : ℕ}
    (hd : d ∣ p ^ 2 * q ^ 2) : p ^ (A_vv p q d).1 * q ^ (A_vv p q d).2 = d := by
  obtain ⟨d1, d2, h1, h2, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hd
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp h1
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hq).mp h2
  simp only [A_vv_pow hp hq hpq i j]

theorem A_inj {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {X Y : Multiset ℕ}
    (hX : ∀ g ∈ X, g ∣ p ^ 2 * q ^ 2) (hY : ∀ g ∈ Y, g ∣ p ^ 2 * q ^ 2)
    (h : X.map (A_vv p q) = Y.map (A_vv p q)) : X = Y := by
  have e : ∀ W : Multiset ℕ, (∀ g ∈ W, g ∣ p ^ 2 * q ^ 2) →
      (W.map (A_vv p q)).map (fun v : ℕ × ℕ => p ^ v.1 * q ^ v.2) = W := by
    intro W hW
    rw [Multiset.map_map]
    conv_rhs => rw [← Multiset.map_id W]
    exact Multiset.map_congr rfl (fun d hd => A_key hp hq hpq (hW d hd))
  calc X = (X.map (A_vv p q)).map (fun v : ℕ × ℕ => p ^ v.1 * q ^ v.2) := (e X hX).symm
    _ = (Y.map (A_vv p q)).map (fun v : ℕ × ℕ => p ^ v.1 * q ^ v.2) := by rw [h]
    _ = Y := e Y hY

theorem A_ne_zero {k : ℕ} {X : Multiset ℕ} (hX : IsFact k X) : ∀ g ∈ X, g ≠ 0 := by
  intro g hg
  have := hX.1 g hg
  omega

theorem A_dvd {k : ℕ} {X : Multiset ℕ} (hX : IsFact k X) : ∀ g ∈ X, g ∣ k := by
  intro g hg
  rw [← hX.2]
  exact Multiset.dvd_prod hg

-- One merge, seen on exponent vectors.
theorem A_merge_vv (p q : ℕ) {X u : Multiset ℕ} (hX0 : ∀ g ∈ X, g ≠ 0) (h : Refines X u)
    (hu : ∀ g ∈ u, g ≠ 1) (hc : Multiset.card X = Multiset.card u + 1) :
    ∃ v ∈ X.map (A_vv p q), ∃ w ∈ (X.map (A_vv p q)).erase v,
      u.map (A_vv p q) = (v + w) ::ₘ ((X.map (A_vv p q)).erase v).erase w := by
  obtain ⟨a, b, s, rfl, rfl⟩ := refines_one_merge h hu hc
  have ha : a ≠ 0 := hX0 a (by simp)
  have hb : b ≠ 0 := hX0 b (by simp)
  refine ⟨A_vv p q a, ?_, A_vv p q b, ?_, ?_⟩
  · simp
  · simp [Multiset.erase_cons_head]
  · simp [Multiset.erase_cons_head, A_vv_mul p q ha hb]

theorem A_k_ge {p q : ℕ} (hp : p.Prime) (hq : q.Prime) : 16 ≤ p ^ 2 * q ^ 2 :=
  calc 16 = 2 ^ 2 * 2 ^ 2 := by norm_num
    _ ≤ p ^ 2 * q ^ 2 :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hp.two_le 2) (Nat.pow_le_pow_left hq.two_le 2)

theorem A_Z_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    ∀ r ∈ p ::ₘ p ::ₘ q ::ₘ q ::ₘ 0, r.Prime := by
  intro r hr
  simp only [Multiset.mem_cons] at hr
  rcases hr with h | h | h | h | h
  · rw [h]; exact hp
  · rw [h]; exact hp
  · rw [h]; exact hq
  · rw [h]; exact hq
  · simp at h

theorem A_ge3 {a b c : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    ∀ g ∈ a ::ₘ b ::ₘ c ::ₘ 0, 2 ≤ g := by
  intro g hg
  simp only [Multiset.mem_cons] at hg
  rcases hg with h | h | h | h
  · rw [h]; exact ha
  · rw [h]; exact hb
  · rw [h]; exact hc
  · simp at h

theorem A_ge2 {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) : ∀ g ∈ a ::ₘ b ::ₘ 0, 2 ≤ g := by
  intro g hg
  simp only [Multiset.mem_cons] at hg
  rcases hg with h | h | h
  · rw [h]; exact ha
  · rw [h]; exact hb
  · simp at h

theorem A_mul2 {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) : 2 ≤ a * b := by nlinarith

theorem A_bottom {p q : ℕ} (hp : p.Prime) (hq : q.Prime) {x : Multiset ℕ}
    (hx : IsFact (p ^ 2 * q ^ 2) x) : Refines (p ::ₘ p ::ₘ q ::ₘ q ::ₘ 0) x :=
  refines_bottom (A_Z_prime hp hq) hx.1
    (by rw [hx.2]; simp only [Multiset.prod_cons, Multiset.prod_zero]; ring)

-- The three atoms E, F, G and the three joins A, B, C are factorizations of p^2 q^2.
theorem A_fact_E {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    IsFact (p ^ 2 * q ^ 2) ((q * q) ::ₘ p ::ₘ p ::ₘ 0) :=
  ⟨A_ge3 (A_mul2 hq.two_le hq.two_le) hp.two_le hp.two_le,
    by simp only [Multiset.prod_cons, Multiset.prod_zero]; ring⟩

theorem A_fact_F {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    IsFact (p ^ 2 * q ^ 2) ((p * p) ::ₘ q ::ₘ q ::ₘ 0) :=
  ⟨A_ge3 (A_mul2 hp.two_le hp.two_le) hq.two_le hq.two_le,
    by simp only [Multiset.prod_cons, Multiset.prod_zero]; ring⟩

theorem A_fact_G {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    IsFact (p ^ 2 * q ^ 2) ((p * q) ::ₘ p ::ₘ q ::ₘ 0) :=
  ⟨A_ge3 (A_mul2 hp.two_le hq.two_le) hp.two_le hq.two_le,
    by simp only [Multiset.prod_cons, Multiset.prod_zero]; ring⟩

theorem A_fact_A {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    IsFact (p ^ 2 * q ^ 2) ((p * p) ::ₘ (q * q) ::ₘ 0) :=
  ⟨A_ge2 (A_mul2 hp.two_le hp.two_le) (A_mul2 hq.two_le hq.two_le),
    by simp only [Multiset.prod_cons, Multiset.prod_zero]; ring⟩

theorem A_fact_B {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    IsFact (p ^ 2 * q ^ 2) ((q * q * p) ::ₘ p ::ₘ 0) :=
  ⟨A_ge2 (A_mul2 (A_mul2 hq.two_le hq.two_le) hp.two_le) hp.two_le,
    by simp only [Multiset.prod_cons, Multiset.prod_zero]; ring⟩

theorem A_fact_C {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    IsFact (p ^ 2 * q ^ 2) ((p * p * q) ::ₘ q ::ₘ 0) :=
  ⟨A_ge2 (A_mul2 (A_mul2 hp.two_le hp.two_le) hq.two_le) hq.two_le,
    by simp only [Multiset.prod_cons, Multiset.prod_zero]; ring⟩

-- Their exponent-vector images.
theorem A_Zv {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    (p ::ₘ p ::ₘ q ::ₘ q ::ₘ 0).map (A_vv p q) = A_Zv0 := by
  simp [A_Zv0, A_vv_p hp hpq, A_vv_q hq hpq]

theorem A_Ev {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ((q * q) ::ₘ p ::ₘ p ::ₘ 0).map (A_vv p q) = A_Ev0 := by
  simp [A_Ev0, A_vv_mul p q hq.ne_zero hq.ne_zero, A_vv_p hp hpq, A_vv_q hq hpq]

theorem A_Fv {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ((p * p) ::ₘ q ::ₘ q ::ₘ 0).map (A_vv p q) = A_Fv0 := by
  simp [A_Fv0, A_vv_mul p q hp.ne_zero hp.ne_zero, A_vv_p hp hpq, A_vv_q hq hpq]

theorem A_Gv {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ((p * q) ::ₘ p ::ₘ q ::ₘ 0).map (A_vv p q) = A_Gv0 := by
  simp [A_Gv0, A_vv_mul p q hp.ne_zero hq.ne_zero, A_vv_p hp hpq, A_vv_q hq hpq]

theorem A_Av {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ((p * p) ::ₘ (q * q) ::ₘ 0).map (A_vv p q) = A_Av0 := by
  simp [A_Av0, A_vv_mul p q hp.ne_zero hp.ne_zero, A_vv_mul p q hq.ne_zero hq.ne_zero,
    A_vv_p hp hpq, A_vv_q hq hpq]

theorem A_Bv {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ((q * q * p) ::ₘ p ::ₘ 0).map (A_vv p q) = A_Bv0 := by
  simp [A_Bv0, A_vv_mul p q (mul_ne_zero hq.ne_zero hq.ne_zero) hp.ne_zero,
    A_vv_mul p q hq.ne_zero hq.ne_zero, A_vv_p hp hpq, A_vv_q hq hpq]

theorem A_Cv {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ((p * p * q) ::ₘ q ::ₘ 0).map (A_vv p q) = A_Cv0 := by
  simp [A_Cv0, A_vv_mul p q (mul_ne_zero hp.ne_zero hp.ne_zero) hq.ne_zero,
    A_vv_mul p q hp.ne_zero hp.ne_zero, A_vv_p hp hpq, A_vv_q hq hpq]

-- A factorization with at least 3 factors, other than the bottom, is one of E, F, G.
theorem A_class {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {x : Multiset ℕ}
    (hx : IsFact (p ^ 2 * q ^ 2) x) (hx3 : 3 ≤ Multiset.card x)
    (hne : x ≠ p ::ₘ p ::ₘ q ::ₘ q ::ₘ 0) :
    x = (q * q) ::ₘ p ::ₘ p ::ₘ 0 ∨ x = (p * p) ::ₘ q ::ₘ q ::ₘ 0 ∨
      x = (p * q) ::ₘ p ::ₘ q ::ₘ 0 := by
  have hZ := A_bottom hp hq hx
  have h4 : Multiset.card (p ::ₘ p ::ₘ q ::ₘ q ::ₘ 0) = 4 := by simp
  obtain ⟨hle, heq⟩ := refines_card hZ (isFact_ne_one hx)
  rw [h4] at hle heq
  have h3 : Multiset.card x = 3 := by
    by_contra hn
    exact hne (heq (by omega)).symm
  obtain ⟨v, hv, w, hw, hxv⟩ := A_merge_vv p q (fun g hg => (A_Z_prime hp hq g hg).ne_zero) hZ
    (isFact_ne_one hx) (by omega)
  rw [A_Zv hp hq hpq] at hv hw hxv
  rcases A_dec_Z v hv w hw with h | h | h
  · left
    exact A_inj hp hq hpq (A_dvd hx) (A_dvd (A_fact_E hp hq))
      (hxv.trans (h.trans (A_Ev hp hq hpq).symm))
  · right; left
    exact A_inj hp hq hpq (A_dvd hx) (A_dvd (A_fact_F hp hq))
      (hxv.trans (h.trans (A_Fv hp hq hpq).symm))
  · right; right
    exact A_inj hp hq hpq (A_dvd hx) (A_dvd (A_fact_G hp hq))
      (hxv.trans (h.trans (A_Gv hp hq hpq).symm))

-- Universal property of the join of two 3-factor factorizations X and Y.
theorem A_univ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {X Y z : Multiset ℕ}
    (hX : IsFact (p ^ 2 * q ^ 2) X) (hY : IsFact (p ^ 2 * q ^ 2) Y)
    (hz : IsFact (p ^ 2 * q ^ 2) z)
    (hX3 : Multiset.card X = 3) (hY3 : Multiset.card Y = 3)
    (hXY : X.map (A_vv p q) ≠ Y.map (A_vv p q))
    (hconc : ∀ v ∈ X.map (A_vv p q), ∀ w ∈ (X.map (A_vv p q)).erase v,
      ∀ v' ∈ Y.map (A_vv p q), ∀ w' ∈ (Y.map (A_vv p q)).erase v',
      (v + w) ::ₘ ((X.map (A_vv p q)).erase v).erase w =
          (v' + w') ::ₘ ((Y.map (A_vv p q)).erase v').erase w' →
        (v + w) ::ₘ ((X.map (A_vv p q)).erase v).erase w = z.map (A_vv p q)) :
    ∀ u, IsFact (p ^ 2 * q ^ 2) u → Refines X u → Refines Y u → Refines z u := by
  intro u hu hXu hYu
  obtain ⟨hleX, heqX⟩ := refines_card hXu (isFact_ne_one hu)
  obtain ⟨hleY, heqY⟩ := refines_card hYu (isFact_ne_one hu)
  rw [hX3] at hleX heqX
  rw [hY3] at hleY heqY
  have hcases : Multiset.card u = 0 ∨ Multiset.card u = 1 ∨ Multiset.card u = 2 ∨
      Multiset.card u = 3 := by omega
  rcases hcases with h0 | h1 | h2 | h3
  · exfalso
    have e := hu.2
    rw [Multiset.card_eq_zero.mp h0, Multiset.prod_zero] at e
    have hk := A_k_ge hp hq
    rw [← e] at hk
    omega
  · obtain ⟨a, rfl⟩ := Multiset.card_eq_one.mp h1
    have e := hu.2
    rw [Multiset.prod_singleton] at e
    rw [e]
    have t := refines_top z
    rw [hz.2] at t
    exact t
  · obtain ⟨v, hv, w, hw, e1⟩ :=
      A_merge_vv p q (A_ne_zero hX) hXu (isFact_ne_one hu) (by omega)
    obtain ⟨v', hv', w', hw', e2⟩ :=
      A_merge_vv p q (A_ne_zero hY) hYu (isFact_ne_one hu) (by omega)
    have huz : u = z := A_inj hp hq hpq (A_dvd hu) (A_dvd hz)
      (e1.trans (hconc v hv w hw v' hv' w' hw' (e1.symm.trans e2)))
    rw [huz]
    exact refines_refl z
  · exfalso
    apply hXY
    rw [heqX h3, heqY h3]

-- The three joins.
theorem A_join_EF {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    JoinSpec (p ^ 2 * q ^ 2) ((q * q) ::ₘ p ::ₘ p ::ₘ 0) ((p * p) ::ₘ q ::ₘ q ::ₘ 0)
      ((p * p) ::ₘ (q * q) ::ₘ 0) := by
  refine ⟨A_fact_A hp hq, merge23 (q * q) p p, refines_swap2 (merge23 (p * p) q q), ?_⟩
  refine A_univ hp hq hpq (A_fact_E hp hq) (A_fact_F hp hq) (A_fact_A hp hq)
    (by simp) (by simp) ?_ ?_
  · rw [A_Ev hp hq hpq, A_Fv hp hq hpq]
    exact A_ne_EF
  · rw [A_Ev hp hq hpq, A_Fv hp hq hpq, A_Av hp hq hpq]
    exact A_dec_EF

theorem A_join_EG {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    JoinSpec (p ^ 2 * q ^ 2) ((q * q) ::ₘ p ::ₘ p ::ₘ 0) ((p * q) ::ₘ p ::ₘ q ::ₘ 0)
      ((q * q * p) ::ₘ p ::ₘ 0) := by
  have hG : Refines ((p * q) ::ₘ p ::ₘ q ::ₘ 0) ((q * q * p) ::ₘ p ::ₘ 0) := by
    have h := merge13 (p * q) p q
    have e : p * q * q = q * q * p := by ring
    rw [e] at h
    exact h
  refine ⟨A_fact_B hp hq, merge12 (q * q) p p, hG, ?_⟩
  refine A_univ hp hq hpq (A_fact_E hp hq) (A_fact_G hp hq) (A_fact_B hp hq)
    (by simp) (by simp) ?_ ?_
  · rw [A_Ev hp hq hpq, A_Gv hp hq hpq]
    exact A_ne_EG
  · rw [A_Ev hp hq hpq, A_Gv hp hq hpq, A_Bv hp hq hpq]
    exact A_dec_EG

theorem A_join_FG {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    JoinSpec (p ^ 2 * q ^ 2) ((p * p) ::ₘ q ::ₘ q ::ₘ 0) ((p * q) ::ₘ p ::ₘ q ::ₘ 0)
      ((p * p * q) ::ₘ q ::ₘ 0) := by
  have hG : Refines ((p * q) ::ₘ p ::ₘ q ::ₘ 0) ((p * p * q) ::ₘ q ::ₘ 0) := by
    have h := merge12 (p * q) p q
    have e : p * q * p = p * p * q := by ring
    rw [e] at h
    exact h
  refine ⟨A_fact_C hp hq, merge12 (p * p) q q, hG, ?_⟩
  refine A_univ hp hq hpq (A_fact_F hp hq) (A_fact_G hp hq) (A_fact_C hp hq)
    (by simp) (by simp) ?_ ?_
  · rw [A_Fv hp hq hpq, A_Gv hp hq hpq]
    exact A_ne_FG
  · rw [A_Fv hp hq hpq, A_Gv hp hq hpq, A_Cv hp hq hpq]
    exact A_dec_FG

theorem hard_p2q2 {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ∀ x y : Multiset ℕ, IsFact (p ^ 2 * q ^ 2) x → IsFact (p ^ 2 * q ^ 2) y →
      3 ≤ Multiset.card x → 3 ≤ Multiset.card y → ¬ Refines x y → ¬ Refines y x →
      ∃ z, JoinSpec (p ^ 2 * q ^ 2) x y z := by
  intro x y hx hy hx3 hy3 hxy hyx
  have hxZ : x ≠ p ::ₘ p ::ₘ q ::ₘ q ::ₘ 0 := by
    intro h
    apply hxy
    rw [h]
    exact A_bottom hp hq hy
  have hyZ : y ≠ p ::ₘ p ::ₘ q ::ₘ q ::ₘ 0 := by
    intro h
    apply hyx
    rw [h]
    exact A_bottom hp hq hx
  rcases A_class hp hq hpq hx hx3 hxZ with rfl | rfl | rfl <;>
    rcases A_class hp hq hpq hy hy3 hyZ with rfl | rfl | rfl
  all_goals first
    | exact absurd (refines_refl _) hxy
    | exact ⟨_, A_join_EF hp hq hpq⟩
    | exact ⟨_, (A_join_EF hp hq hpq).symm⟩
    | exact ⟨_, A_join_EG hp hq hpq⟩
    | exact ⟨_, (A_join_EG hp hq hpq).symm⟩
    | exact ⟨_, A_join_FG hp hq hpq⟩
    | exact ⟨_, (A_join_FG hp hq hpq).symm⟩
-- PART A END

-- PART B BEGIN: InS_two_le, not_lattice_of_InS, classify (with B_ helpers).

theorem InS_two_le {s : ℕ} (hs : InS s) : 2 ≤ s := by
  rcases hs with ⟨p, hp, rfl⟩ | ⟨p, q, hp, hq, _, rfl⟩ | ⟨p, q, r, hp, hq, hr, _, _, _, rfl⟩
  · have h2 : 2 ≤ p := hp.two_le
    have h1 : 1 ≤ p ^ 4 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 4 hp.ne_zero)
    have h3 : 2 * 1 ≤ p * p ^ 4 := Nat.mul_le_mul h2 h1
    have h4 : p ^ 5 = p * p ^ 4 := by ring
    rw [h4]
    omega
  · have h2 : 2 ≤ p := hp.two_le
    have h1 : 1 ≤ q ^ 3 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 3 hq.ne_zero)
    have h3 : 2 * 1 ≤ p * q ^ 3 := Nat.mul_le_mul h2 h1
    omega
  · have h2 : 2 ≤ p := hp.two_le
    have h1 : 1 ≤ q * r ^ 2 :=
      Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hq.ne_zero (pow_ne_zero 2 hr.ne_zero))
    have h3 : 2 * 1 ≤ p * (q * r ^ 2) := Nat.mul_le_mul h2 h1
    have h4 : p * q * r ^ 2 = p * (q * r ^ 2) := by ring
    rw [h4]
    omega

theorem B_lt_mul {a b : ℕ} (ha : 2 ≤ a) (hb : 1 ≤ b) : b < a * b := by
  have h := Nat.mul_le_mul ha (le_refl b)
  omega

theorem B_lt_mul' {a b : ℕ} (ha : 2 ≤ a) (hb : 1 ≤ b) : b < b * a := by
  have h := Nat.mul_le_mul (le_refl b) ha
  omega

theorem B_isFact2 {s a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (h : a * b = s) :
    IsFact s (a ::ₘ b ::ₘ 0) := by
  refine ⟨fun m hm => ?_, ?_⟩
  · rcases Multiset.mem_cons.mp hm with h1 | h1
    · rw [h1]
      exact ha
    rcases Multiset.mem_cons.mp h1 with h2 | h2
    · rw [h2]
      exact hb
    simp at h2
  · simp only [Multiset.prod_cons, Multiset.prod_zero, mul_one]
    exact h

theorem B_isFact3 {s a b c : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (h : a * (b * c) = s) :
    IsFact s (a ::ₘ b ::ₘ c ::ₘ 0) := by
  refine ⟨fun m hm => ?_, ?_⟩
  · rcases Multiset.mem_cons.mp hm with h1 | h1
    · rw [h1]
      exact ha
    rcases Multiset.mem_cons.mp h1 with h2 | h2
    · rw [h2]
      exact hb
    rcases Multiset.mem_cons.mp h2 with h3 | h3
    · rw [h3]
      exact hc
    simp at h3
  · simp only [Multiset.prod_cons, Multiset.prod_zero, mul_one]
    exact h

theorem B_card2 (a b : ℕ) : Multiset.card (a ::ₘ b ::ₘ 0) = 2 := by
  simp

theorem B_card3 (a b c : ℕ) : Multiset.card (a ::ₘ b ::ₘ c ::ₘ 0) = 3 := by
  simp

theorem B_not_mem2 {a b c : ℕ} (hb : a ≠ b) (hc : a ≠ c) : a ∉ (b ::ₘ c ::ₘ 0) := by
  intro hm
  rcases Multiset.mem_cons.mp hm with h | hm
  · exact hb h
  rcases Multiset.mem_cons.mp hm with h | hm
  · exact hc h
  simp at hm

theorem B_not_mem3 {a b c d : ℕ} (hb : a ≠ b) (hc : a ≠ c) (hd : a ≠ d) :
    a ∉ (b ::ₘ c ::ₘ d ::ₘ 0) := by
  intro hm
  rcases Multiset.mem_cons.mp hm with h | hm
  · exact hb h
  rcases Multiset.mem_cons.mp hm with h | hm
  · exact hc h
  rcases Multiset.mem_cons.mp hm with h | hm
  · exact hd h
  simp at hm

theorem B_ne_of_mem {x y : Multiset ℕ} {a : ℕ} (hx : a ∈ x) (hy : a ∉ y) : x ≠ y := by
  intro h
  rw [h] at hx
  exact hy hx

-- Two 3-part factorizations below two distinct 2-part ones: no least upper bound.
theorem B_not_lattice_of_witness {s : ℕ} {x y U1 U2 : Multiset ℕ}
    (hx : IsFact s x) (hy : IsFact s y) (hU1 : IsFact s U1) (hU2 : IsFact s U2)
    (cx : Multiset.card x = 3) (cy : Multiset.card y = 3)
    (c1 : Multiset.card U1 = 2) (c2 : Multiset.card U2 = 2)
    (hxy : x ≠ y) (hU : U1 ≠ U2)
    (h1 : Refines x U1) (h2 : Refines x U2) (h3 : Refines y U1) (h4 : Refines y U2) :
    ¬ IsLatticeFact s := by
  intro hL
  obtain ⟨⟨z, hz, hxz, hyz, hzmin⟩, _⟩ := hL x y hx hy
  have hz1 : Refines z U1 := hzmin U1 hU1 h1 h3
  have hz2 : Refines z U2 := hzmin U2 hU2 h2 h4
  have ax := refines_card hxz (isFact_ne_one hz)
  have ay := refines_card hyz (isFact_ne_one hz)
  have a1 := refines_card hz1 (isFact_ne_one hU1)
  have a2 := refines_card hz2 (isFact_ne_one hU2)
  by_cases h3c : Multiset.card z = 3
  · have e1 : x = z := ax.2 (h3c.trans cx.symm)
    have e2 : y = z := ay.2 (h3c.trans cy.symm)
    exact hxy (e1.trans e2.symm)
  · have hz2c : Multiset.card z = 2 := by
      have t1 := ax.1
      have t2 := a1.1
      omega
    have e1 : z = U1 := a1.2 (c1.trans hz2c.symm)
    have e2 : z = U2 := a2.2 (c2.trans hz2c.symm)
    exact hU (e1.symm.trans e2)

theorem not_lattice_of_InS {s : ℕ} (hs : InS s) : ¬ IsLatticeFact s := by
  rcases hs with ⟨p, hp, rfl⟩ | ⟨p, q, hp, hq, hpq, rfl⟩ |
      ⟨p, q, r, hp, hq, hr, hpq, hpr, _, rfl⟩
  · -- s = p ^ 5
    have h2 : 2 ≤ p := hp.two_le
    have l1 : p < p * p := B_lt_mul h2 (by omega)
    have l2 : p * p < p * p * p := B_lt_mul' h2 (by omega)
    have l3 : p * p * p < p * p * p * p := B_lt_mul' h2 (by omega)
    refine B_not_lattice_of_witness (x := (p * p * p) ::ₘ p ::ₘ p ::ₘ 0)
      (y := (p * p) ::ₘ (p * p) ::ₘ p ::ₘ 0)
      (U1 := (p * p * p * p) ::ₘ p ::ₘ 0) (U2 := (p * p * p) ::ₘ (p * p) ::ₘ 0)
      (B_isFact3 (by omega) h2 h2 (by ring)) (B_isFact3 (by omega) (by omega) h2 (by ring))
      (B_isFact2 (by omega) h2 (by ring)) (B_isFact2 (by omega) (by omega) (by ring))
      (B_card3 _ _ _) (B_card3 _ _ _) (B_card2 _ _) (B_card2 _ _)
      (B_ne_of_mem (a := p * p * p) (by simp) (B_not_mem3 (by omega) (by omega) (by omega)))
      (B_ne_of_mem (a := p) (by simp) (B_not_mem2 (by omega) (by omega)))
      (merge12 (p * p * p) p p) (refines_swap2 (merge23 (p * p * p) p p)) ?_
      (merge13 (p * p) (p * p) p)
    have h := merge12 (p * p) (p * p) p
    rw [show p * p * (p * p) = p * p * p * p by ring] at h
    exact h
  · -- s = p * q ^ 3
    have hp2 : 2 ≤ p := hp.two_le
    have hq2 : 2 ≤ q := hq.two_le
    have l1 : q < q * q := B_lt_mul hq2 (by omega)
    have l2 : p < p * q := B_lt_mul' hq2 (by omega)
    have l3 : q < p * q := B_lt_mul hp2 (by omega)
    have l4 : p < p * (q * q) := B_lt_mul' (by omega) (by omega)
    refine B_not_lattice_of_witness (x := p ::ₘ q ::ₘ (q * q) ::ₘ 0)
      (y := q ::ₘ q ::ₘ (p * q) ::ₘ 0)
      (U1 := (p * (q * q)) ::ₘ q ::ₘ 0) (U2 := (p * q) ::ₘ (q * q) ::ₘ 0)
      (B_isFact3 hp2 hq2 (by omega) (by ring)) (B_isFact3 hq2 hq2 (by omega) (by ring))
      (B_isFact2 (by omega) hq2 (by ring)) (B_isFact2 (by omega) (by omega) (by ring))
      (B_card3 _ _ _) (B_card3 _ _ _) (B_card2 _ _) (B_card2 _ _)
      (B_ne_of_mem (a := p) (by simp) (B_not_mem3 hpq hpq (by omega)))
      (B_ne_of_mem (a := q) (by simp) (B_not_mem2 (by omega) (by omega)))
      (merge13 p q (q * q)) (merge12 p q (q * q)) ?_ (refines_swap2 (merge12 q q (p * q)))
    have h := merge13 q q (p * q)
    rw [show q * (p * q) = p * (q * q) by ring] at h
    exact h
  · -- s = p * q * r ^ 2
    have hp2 : 2 ≤ p := hp.two_le
    have hq2 : 2 ≤ q := hq.two_le
    have hr2 : 2 ≤ r := hr.two_le
    have l1 : p < p * r := B_lt_mul' hr2 (by omega)
    have l2 : q < q * r := B_lt_mul' hr2 (by omega)
    have l3 : p < p * q := B_lt_mul' hq2 (by omega)
    have l4 : p * q < p * q * r := B_lt_mul' hr2 (by omega)
    have l5 : r < p * r := B_lt_mul hp2 (by omega)
    have l6 : r < q * r := B_lt_mul hq2 (by omega)
    refine B_not_lattice_of_witness (x := p ::ₘ r ::ₘ (q * r) ::ₘ 0)
      (y := q ::ₘ r ::ₘ (p * r) ::ₘ 0)
      (U1 := (p * r) ::ₘ (q * r) ::ₘ 0) (U2 := r ::ₘ (p * q * r) ::ₘ 0)
      (B_isFact3 hp2 hr2 (by omega) (by ring)) (B_isFact3 hq2 hr2 (by omega) (by ring))
      (B_isFact2 (by omega) (by omega) (by ring)) (B_isFact2 hr2 (by omega) (by ring))
      (B_card3 _ _ _) (B_card3 _ _ _) (B_card2 _ _) (B_card2 _ _)
      (B_ne_of_mem (a := p) (by simp) (B_not_mem3 hpq hpr (by omega)))
      (Ne.symm (B_ne_of_mem (a := r) (by simp) (B_not_mem2 (by omega) (by omega))))
      (merge12 p r (q * r)) ?_ (refines_swap2 (merge12 q r (p * r))) ?_
    · have h := merge13 p r (q * r)
      rw [show p * (q * r) = p * q * r by ring] at h
      exact refines_swap2 h
    · have h := merge13 q r (p * r)
      rw [show q * (p * r) = p * q * r by ring] at h
      exact refines_swap2 h

theorem classify {k : ℕ} (hk : 1 ≤ k) (h : ¬ ∃ s, InS s ∧ s ∣ k) :
    Squarefree k ∨ (∃ p, p.Prime ∧ (k = p ^ 2 ∨ k = p ^ 3 ∨ k = p ^ 4)) ∨
    (∃ p q, p.Prime ∧ q.Prime ∧ p ≠ q ∧ (k = p ^ 2 * q ∨ k = p ^ 2 * q ^ 2)) := by
  by_cases hsq : Squarefree k
  · exact Or.inl hsq
  right
  have hk0 : k ≠ 0 := by omega
  obtain ⟨p, hp, hpp⟩ : ∃ p, p.Prime ∧ p * p ∣ k := by
    by_contra hne
    exact hsq (Nat.squarefree_iff_prime_squarefree.mpr fun x hx hxx => hne ⟨x, hx, hxx⟩)
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk0 p hp.ne_one
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero p)
  have ha2 : 2 ≤ a := by
    by_contra hlt
    have ha' : a = 0 ∨ a = 1 := by omega
    rcases ha' with rfl | rfl
    · rw [pow_zero, one_mul] at hpp
      exact hm (dvd_trans (dvd_mul_right p p) hpp)
    · rw [pow_one] at hpp
      exact hm ((mul_dvd_mul_iff_left hp.ne_zero).mp hpp)
  have ha4 : a ≤ 4 := by
    by_contra hlt
    apply h
    refine ⟨p ^ 5, Or.inl ⟨p, hp, rfl⟩, ?_⟩
    exact dvd_trans (pow_dvd_pow p (by omega)) (dvd_mul_right _ _)
  by_cases hm1 : m = 1
  · subst hm1
    refine Or.inl ⟨p, hp, ?_⟩
    rw [mul_one]
    have ha' : a = 2 ∨ a = 3 ∨ a = 4 := by omega
    rcases ha' with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · right
    obtain ⟨q, hq, hqm⟩ : ∃ q, q.Prime ∧ q ∣ m :=
      ⟨m.minFac, Nat.minFac_prime hm1, Nat.minFac_dvd m⟩
    have hqp : q ≠ p := by
      rintro rfl
      exact hm hqm
    obtain ⟨b, m', hm', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0 q hq.ne_one
    have hb1 : 1 ≤ b := by
      by_contra hb0
      have hb : b = 0 := by omega
      rw [hb, pow_zero, one_mul] at hqm
      exact hm' hqm
    have ha3 : ¬ 3 ≤ a := by
      intro ha3
      apply h
      refine ⟨q * p ^ 3, Or.inr (Or.inl ⟨q, p, hq, hp, hqp, rfl⟩), ?_⟩
      have e : q * p ^ 3 = p ^ 3 * q := mul_comm _ _
      rw [e]
      exact mul_dvd_mul (pow_dvd_pow p ha3) hqm
    have ha : a = 2 := by omega
    subst ha
    by_cases hm'1 : m' = 1
    · subst hm'1
      have hb3 : ¬ 3 ≤ b := by
        intro hb3
        apply h
        refine ⟨p * q ^ 3, Or.inr (Or.inl ⟨p, q, hp, hq, hqp.symm, rfl⟩), ?_⟩
        exact mul_dvd_mul (dvd_pow_self p (by norm_num))
          (dvd_trans (pow_dvd_pow q hb3) (dvd_mul_right _ _))
      have hb' : b = 1 ∨ b = 2 := by omega
      refine ⟨p, q, hp, hq, hqp.symm, ?_⟩
      rcases hb' with rfl | rfl
      · left
        ring
      · right
        ring
    · exfalso
      apply h
      obtain ⟨r, hr, hrm⟩ : ∃ r, r.Prime ∧ r ∣ m' :=
        ⟨m'.minFac, Nat.minFac_prime hm'1, Nat.minFac_dvd m'⟩
      have hrq : q ≠ r := by
        rintro rfl
        exact hm' hrm
      have hrp : r ≠ p := by
        rintro rfl
        exact hm (dvd_trans hrm (dvd_mul_left _ _))
      refine ⟨q * r * p ^ 2, Or.inr (Or.inr ⟨q, r, p, hq, hr, hp, hrq, hqp, hrp, rfl⟩), ?_⟩
      have e : q * r * p ^ 2 = p ^ 2 * (q * r) := by ring
      rw [e]
      exact mul_dvd_mul (dvd_refl _) (mul_dvd_mul (dvd_pow_self q (by omega)) hrm)
-- PART B END

/-! ## Small facts about factorizations -/

theorem isFact_top {k : ℕ} (hk : 2 ≤ k) : IsFact k {k} := by
  refine ⟨fun x hx => ?_, Multiset.prod_singleton k⟩
  rw [Multiset.mem_singleton] at hx
  omega

theorem isFact_card_pos {k : ℕ} (hk : 2 ≤ k) {F : Multiset ℕ} (h : IsFact k F) :
    1 ≤ Multiset.card F := by
  rcases Nat.eq_zero_or_pos (Multiset.card F) with h0 | h0
  · rw [Multiset.card_eq_zero] at h0
    have e := h.2
    rw [h0, Multiset.prod_zero] at e
    omega
  · exact h0

theorem isFact_card_one {k : ℕ} {F : Multiset ℕ} (h : IsFact k F) (hc : Multiset.card F = 1) :
    F = {k} := by
  obtain ⟨a, rfl⟩ := Multiset.card_eq_one.mp hc
  have e := h.2
  rw [Multiset.prod_singleton] at e
  rw [e]

theorem eq_zero_of_prod_one {b : Multiset ℕ} (hb : ∀ x ∈ b, 2 ≤ x) (h : b.prod = 1) : b = 0 := by
  by_contra hne
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hne
  have h1 := Multiset.dvd_prod ha
  rw [h, Nat.dvd_one] at h1
  have := hb a ha
  omega

theorem isFact_one {F : Multiset ℕ} (h : IsFact 1 F) : F = 0 := eq_zero_of_prod_one h.1 h.2

theorem eq_single_of_prime {b : Multiset ℕ} (hb : ∀ x ∈ b, 2 ≤ x) (h : b.prod.Prime) :
    b = {b.prod} := by
  have hne : b ≠ 0 := by
    rintro rfl
    rw [Multiset.prod_zero] at h
    exact Nat.not_prime_one h
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hne
  obtain ⟨b', rfl⟩ := Multiset.exists_cons_of_mem ha
  rw [Multiset.prod_cons] at h
  have ha2 := hb a (Multiset.mem_cons_self a b')
  have hb' : b'.prod = 1 := by
    rcases Nat.prime_mul_iff.mp h with ⟨_, h1⟩ | ⟨_, h1⟩
    · exact h1
    · omega
  have e : b' = 0 := eq_zero_of_prod_one (fun x hx => hb x (Multiset.mem_cons_of_mem hx)) hb'
  subst e
  simp

theorem refines_dvd {F G : Multiset ℕ} (h : Refines F G) {a : ℕ} (ha : a ∈ F) : ∃ b ∈ G, a ∣ b := by
  obtain ⟨H, rfl, rfl⟩ := h
  obtain ⟨s, hs, has⟩ := Multiset.mem_join.mp ha
  exact ⟨s.prod, Multiset.mem_map_of_mem _ hs, Multiset.dvd_prod has⟩

/-! ## Joins from meets and meets from joins (by cardinality) -/

theorem joins_of_meets {k : ℕ} (hk : 2 ≤ k)
    (hmeet : ∀ x y, IsFact k x → IsFact k y → ∃ w, MeetSpec k x y w) :
    ∀ x y, IsFact k x → IsFact k y → ∃ z, JoinSpec k x y z := by
  classical
  intro x y hx hy
  let P : ℕ → Prop := fun c => ∃ z, IsFact k z ∧ Refines x z ∧ Refines y z ∧ Multiset.card z = c
  have hP1 : P 1 := by
    refine ⟨{k}, isFact_top hk, ?_, ?_, Multiset.card_singleton k⟩
    · rw [← hx.2]; exact refines_top x
    · rw [← hy.2]; exact refines_top y
  have h1x : 1 ≤ Multiset.card x := isFact_card_pos hk hx
  obtain ⟨z, hz, hxz, hyz, hcz⟩ := Nat.findGreatest_spec h1x hP1
  refine ⟨z, hz, hxz, hyz, fun u hu hxu hyu => ?_⟩
  obtain ⟨m, hm, hmz, hmu, hmuniv⟩ := hmeet z u hz hu
  have hxm := hmuniv x hx hxz hxu
  have hym := hmuniv y hy hyz hyu
  have hcm_le : Multiset.card m ≤ Multiset.card x := (refines_card hxm (isFact_ne_one hm)).1
  have hPm : P (Multiset.card m) := ⟨m, hm, hxm, hym, rfl⟩
  have h1 : Multiset.card m ≤ Nat.findGreatest P (Multiset.card x) := Nat.le_findGreatest hcm_le hPm
  obtain ⟨h2a, h2b⟩ := refines_card hmz (isFact_ne_one hz)
  have heq : Multiset.card z = Multiset.card m := by omega
  rw [h2b heq] at hmu
  exact hmu

theorem meets_of_joins {k : ℕ} {Z : Multiset ℕ} (hZ : IsFact k Z)
    (hbot : ∀ F, IsFact k F → Refines Z F)
    (hjoin : ∀ x y, IsFact k x → IsFact k y → ∃ z, JoinSpec k x y z) :
    ∀ x y, IsFact k x → IsFact k y → ∃ w, MeetSpec k x y w := by
  classical
  intro x y hx hy
  have hex : ∃ c, ∃ w, IsFact k w ∧ Refines w x ∧ Refines w y ∧ Multiset.card w = c :=
    ⟨_, Z, hZ, hbot x hx, hbot y hy, rfl⟩
  obtain ⟨w, hw, hwx, hwy, hcw⟩ := Nat.find_spec hex
  refine ⟨w, hw, hwx, hwy, fun l hl hlx hly => ?_⟩
  obtain ⟨j, hj, hwj, hlj, hjuniv⟩ := hjoin w l hw hl
  have hjx := hjuniv x hx hwx hlx
  have hjy := hjuniv y hy hwy hly
  have h1 : Nat.find hex ≤ Multiset.card j := Nat.find_min' hex ⟨j, hj, hjx, hjy, rfl⟩
  obtain ⟨h2a, h2b⟩ := refines_card hwj (isFact_ne_one hj)
  have heq : Multiset.card j = Multiset.card w := by omega
  rw [← h2b heq] at hlj
  exact hlj

theorem join_of_le {k : ℕ} {x y : Multiset ℕ} (hy : IsFact k y) (h : Refines x y) :
    JoinSpec k x y y :=
  ⟨hy, h, refines_refl y, fun _ _ _ h2 => h2⟩

theorem join_top {k : ℕ} (hk : 2 ≤ k) {x y : Multiset ℕ} (hx : IsFact k x) (hy : IsFact k y)
    (hc : Multiset.card x ≤ 2) (hyx : ¬ Refines y x) : JoinSpec k x y {k} := by
  refine ⟨isFact_top hk, ?_, ?_, fun u hu hxu hyu => ?_⟩
  · rw [← hx.2]; exact refines_top x
  · rw [← hy.2]; exact refines_top y
  · obtain ⟨h1a, h1b⟩ := refines_card hxu (isFact_ne_one hu)
    have hne : Multiset.card u ≠ Multiset.card x := by
      intro he
      rw [h1b he] at hyx
      exact hyx hyu
    have hpos := isFact_card_pos hk hu
    have hu1 : Multiset.card u = 1 := by omega
    rw [isFact_card_one hu hu1]
    exact refines_refl _

/-- A lattice criterion: only incomparable pairs with at least three factors each need a join. -/
theorem lattice_of_hard {k : ℕ} (hk : 2 ≤ k) {Z : Multiset ℕ} (hZ : ∀ q ∈ Z, q.Prime)
    (hZk : Z.prod = k)
    (hhard : ∀ x y, IsFact k x → IsFact k y → 3 ≤ Multiset.card x → 3 ≤ Multiset.card y →
      ¬ Refines x y → ¬ Refines y x → ∃ z, JoinSpec k x y z) : IsLatticeFact k := by
  have hZf : IsFact k Z := ⟨fun q hq => (hZ q hq).two_le, hZk⟩
  have hbot : ∀ F, IsFact k F → Refines Z F := fun F hF => refines_bottom hZ hF.1 (by rw [hZk, hF.2])
  have hjoin : ∀ x y, IsFact k x → IsFact k y → ∃ z, JoinSpec k x y z := by
    intro x y hx hy
    by_cases hxy : Refines x y
    · exact ⟨y, join_of_le hy hxy⟩
    by_cases hyx : Refines y x
    · exact ⟨x, (join_of_le hx hyx).symm⟩
    by_cases hcx : Multiset.card x ≤ 2
    · exact ⟨{k}, join_top hk hx hy hcx hyx⟩
    by_cases hcy : Multiset.card y ≤ 2
    · exact ⟨{k}, (join_top hk hy hx hcy hxy).symm⟩
    exact hhard x y hx hy (by omega) (by omega) hxy hyx
  have hmeet := meets_of_joins hZf hbot hjoin
  intro x y hx hy
  obtain ⟨z, hz⟩ := hjoin x y hx hy
  obtain ⟨w, hw⟩ := hmeet x y hx hy
  exact ⟨⟨z, hz⟩, ⟨w, hw⟩⟩

theorem lattice_of_card_le3 {k : ℕ} (hk : 2 ≤ k) {Z : Multiset ℕ} (hZ : ∀ q ∈ Z, q.Prime)
    (hZk : Z.prod = k) (hc : Multiset.card Z ≤ 3) : IsLatticeFact k := by
  apply lattice_of_hard hk hZ hZk
  intro x y hx hy hcx _ hxy _
  exfalso
  have hb := refines_bottom hZ hx.1 (by rw [hZk, hx.2])
  obtain ⟨h1a, h1b⟩ := refines_card hb (isFact_ne_one hx)
  have e : Z = x := h1b (by omega)
  apply hxy
  rw [← e]
  exact refines_bottom hZ hy.1 (by rw [hZk, hy.2])

theorem lattice_p4 {p : ℕ} (hp : p.Prime) : IsLatticeFact (p ^ 4) := by
  have hk : 2 ≤ p ^ 4 :=
    le_trans hp.two_le (by
      calc p = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ 4 := Nat.pow_le_pow_right hp.pos (by norm_num))
  have hZ : ∀ q ∈ Multiset.replicate 4 p, q.Prime := by
    intro q hq
    rw [Multiset.eq_of_mem_replicate hq]
    exact hp
  have hZk : (Multiset.replicate 4 p).prod = p ^ 4 := Multiset.prod_replicate 4 p
  have shape : ∀ F, IsFact (p ^ 4) F → Multiset.card F = 3 →
      F = (p * p) ::ₘ Multiset.replicate 2 p := by
    intro F hF hc
    have hb := refines_bottom hZ hF.1 (by rw [hZk, hF.2])
    obtain ⟨a, b, s, h1, h2⟩ :=
      refines_one_merge hb (isFact_ne_one hF) (by rw [Multiset.card_replicate]; omega)
    have ham : a ∈ Multiset.replicate 4 p := by
      rw [h1]
      exact Multiset.mem_cons_self _ _
    have hbm : b ∈ Multiset.replicate 4 p := by
      rw [h1]
      exact Multiset.mem_cons_of_mem (Multiset.mem_cons_self _ _)
    have hs : s = Multiset.replicate 2 p := by
      rw [Multiset.eq_replicate]
      constructor
      · have e := congrArg Multiset.card h1
        simp at e
        omega
      · intro c hc'
        have hcm : c ∈ Multiset.replicate 4 p := by
          rw [h1]
          exact Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem hc')
        exact Multiset.eq_of_mem_replicate hcm
    rw [h2, Multiset.eq_of_mem_replicate ham, Multiset.eq_of_mem_replicate hbm, hs]
  have c3 : ∀ F G, IsFact (p ^ 4) F → IsFact (p ^ 4) G → 3 ≤ Multiset.card F → ¬ Refines F G →
      Multiset.card F = 3 := by
    intro F G hF hG hcF hFG
    have hb := refines_bottom hZ hF.1 (by rw [hZk, hF.2])
    obtain ⟨h1a, h1b⟩ := refines_card hb (isFact_ne_one hF)
    rw [Multiset.card_replicate] at h1a h1b
    by_contra hne
    have e : Multiset.replicate 4 p = F := h1b (by omega)
    apply hFG
    rw [← e]
    exact refines_bottom hZ hG.1 (by rw [hZk, hG.2])
  apply lattice_of_hard hk hZ hZk
  intro x y hx hy hcx hcy hxy hyx
  exfalso
  have ex := shape x hx (c3 x y hx hy hcx hxy)
  have ey := shape y hy (c3 y x hy hx hcy hyx)
  apply hxy
  rw [ex, ey]
  exact refines_refl _

theorem lattice_p2q2 {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    IsLatticeFact (p ^ 2 * q ^ 2) := by
  have hk : 2 ≤ p ^ 2 * q ^ 2 :=
    le_trans (by norm_num)
      (Nat.mul_le_mul (Nat.pow_le_pow_left hp.two_le 2) (Nat.pow_le_pow_left hq.two_le 2))
  apply lattice_of_hard (Z := p ::ₘ p ::ₘ q ::ₘ q ::ₘ 0) hk (by simp [hp, hq])
    (by simp only [Multiset.prod_cons, Multiset.prod_zero]; ring)
  exact hard_p2q2 hp hq hpq

/-! ## The squarefree case: meets are computed by gcds -/

theorem prod_filter_ne_one' (s : Multiset ℕ) : (s.filter (· ≠ 1)).prod = s.prod := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    by_cases h : a = 1
    · rw [Multiset.filter_cons_of_neg (p := fun x => x ≠ 1) s (by simp [h]), ih,
        Multiset.prod_cons, h, one_mul]
    · rw [Multiset.filter_cons_of_pos (p := fun x => x ≠ 1) s h, Multiset.prod_cons,
        Multiset.prod_cons, ih]

theorem gcd_prod_sf (a : ℕ) : ∀ y : Multiset ℕ, Squarefree y.prod →
    (y.map (fun c => Nat.gcd a c)).prod = Nat.gcd a y.prod := by
  intro y
  induction y using Multiset.induction with
  | empty => intro _; simp
  | cons b y ih =>
    intro hsq
    rw [Multiset.prod_cons] at hsq
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons, ih (Squarefree.of_mul_right hsq),
      Nat.Coprime.gcd_mul a (Nat.coprime_of_squarefree_mul hsq)]

theorem filter_gcd_single {w : Multiset ℕ} (hsq : Squarefree w.prod) {c d0 : ℕ} (hd0 : d0 ∈ w)
    (hc : c ∣ d0) (hc1 : c ≠ 1) : (w.map (fun d => Nat.gcd d c)).filter (· ≠ 1) = {c} := by
  obtain ⟨w', rfl⟩ := Multiset.exists_cons_of_mem hd0
  rw [Multiset.prod_cons] at hsq
  have hcop : Nat.Coprime d0 w'.prod := Nat.coprime_of_squarefree_mul hsq
  have hrest : (w'.map (fun d => Nat.gcd d c)).filter (· ≠ 1) = 0 := by
    rw [Multiset.filter_eq_nil]
    intro e he
    obtain ⟨d, hd, rfl⟩ := Multiset.mem_map.mp he
    have h1 : Nat.Coprime d0 d := hcop.coprime_dvd_right (Multiset.dvd_prod hd)
    have h2 : Nat.Coprime c d := h1.coprime_dvd_left hc
    rw [Nat.gcd_comm]
    exact fun h => h h2
  have hne : Nat.gcd d0 c ≠ 1 := by
    rw [Nat.gcd_eq_right hc]
    exact hc1
  rw [Multiset.map_cons, Multiset.filter_cons_of_pos (p := fun x => x ≠ 1) _ hne, hrest,
    Nat.gcd_eq_right hc, Multiset.cons_zero]

/-- For a squarefree product, refinement is decided by divisibility of the factors. -/
theorem sf_refines {u w : Multiset ℕ} (hsq : Squarefree w.prod) (hprod : u.prod = w.prod)
    (hu1 : ∀ c ∈ u, c ≠ 1) (hdiv : ∀ c ∈ u, ∃ d ∈ w, c ∣ d) : Refines u w := by
  have hsqu : Squarefree u.prod := by
    rw [hprod]
    exact hsq
  refine ⟨w.map (fun d => (u.map (fun c => Nat.gcd d c)).filter (· ≠ 1)), ?_, ?_⟩
  · have e1 : (w.map (fun d => (u.map (fun c => Nat.gcd d c)).filter (· ≠ 1))).join
        = (w.bind (fun d => u.map (fun c => Nat.gcd d c))).filter (· ≠ 1) := by
      rw [Multiset.filter_bind]
      rfl
    have e2 : (u.bind fun c => (w.map fun d => Nat.gcd d c).filter (· ≠ 1))
        = u.bind fun c => ({c} : Multiset ℕ) := by
      apply Multiset.bind_congr
      intro c hc
      obtain ⟨d0, hd0, hcd⟩ := hdiv c hc
      exact filter_gcd_single hsq hd0 hcd (hu1 c hc)
    rw [e1, Multiset.bind_map_comm, Multiset.filter_bind, e2, Multiset.bind_singleton,
      Multiset.map_id']
  · rw [Multiset.map_map]
    conv_rhs => rw [← Multiset.map_id' w]
    apply Multiset.map_congr rfl
    intro d hd
    show ((u.map fun c => Nat.gcd d c).filter (· ≠ 1)).prod = d
    rw [prod_filter_ne_one', gcd_prod_sf d u hsqu, hprod]
    exact Nat.gcd_eq_left (Multiset.dvd_prod hd)

/-- The meet of two factorizations of a squarefree number: all gcds of a factor of each. -/
def sfMeet (x y : Multiset ℕ) : Multiset ℕ :=
  (x.bind fun a => y.map fun b => Nat.gcd a b).filter (· ≠ 1)

theorem mem_sfMeet {x y : Multiset ℕ} {e : ℕ} :
    e ∈ sfMeet x y ↔ e ≠ 1 ∧ ∃ a ∈ x, ∃ b ∈ y, Nat.gcd a b = e := by
  unfold sfMeet
  rw [Multiset.mem_filter, Multiset.mem_bind]
  constructor
  · rintro ⟨⟨a, ha, he⟩, h1⟩
    obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.mp he
    exact ⟨h1, a, ha, b, hb, rfl⟩
  · rintro ⟨h1, a, ha, b, hb, rfl⟩
    exact ⟨⟨a, ha, Multiset.mem_map_of_mem _ hb⟩, h1⟩

theorem sf_meet {k : ℕ} (hsq : Squarefree k) {x y : Multiset ℕ} (hx : IsFact k x) (hy : IsFact k y) :
    MeetSpec k x y (sfMeet x y) := by
  have hsqy : Squarefree y.prod := by
    rw [hy.2]
    exact hsq
  have hprodw : (sfMeet x y).prod = k := by
    unfold sfMeet
    rw [prod_filter_ne_one', Multiset.prod_bind, ← hx.2]
    congr 1
    conv_rhs => rw [← Multiset.map_id' x]
    apply Multiset.map_congr rfl
    intro a ha
    show (y.map fun b => Nat.gcd a b).prod = a
    rw [gcd_prod_sf a y hsqy, hy.2, ← hx.2]
    exact Nat.gcd_eq_left (Multiset.dvd_prod ha)
  have hw : IsFact k (sfMeet x y) := by
    refine ⟨fun e he => ?_, hprodw⟩
    obtain ⟨h1, a, ha, b, _, rfl⟩ := mem_sfMeet.mp he
    have ha0 : 0 < a := by
      have := hx.1 a ha
      omega
    have := Nat.gcd_pos_of_pos_left b ha0
    omega
  have hsqw : Squarefree (sfMeet x y).prod := by
    rw [hprodw]
    exact hsq
  refine ⟨hw, ?_, ?_, ?_⟩
  · apply sf_refines (by rw [hx.2]; exact hsq) (by rw [hprodw, hx.2]) (isFact_ne_one hw)
    intro e he
    obtain ⟨_, a, ha, b, _, rfl⟩ := mem_sfMeet.mp he
    exact ⟨a, ha, Nat.gcd_dvd_left a b⟩
  · apply sf_refines (by rw [hy.2]; exact hsq) (by rw [hprodw, hy.2]) (isFact_ne_one hw)
    intro e he
    obtain ⟨_, a, _, b, hb, rfl⟩ := mem_sfMeet.mp he
    exact ⟨b, hb, Nat.gcd_dvd_right a b⟩
  · intro u hu hux huy
    apply sf_refines hsqw (by rw [hu.2, hprodw]) (isFact_ne_one hu)
    intro c hc
    obtain ⟨a, ha, hca⟩ := refines_dvd hux hc
    obtain ⟨b, hb, hcb⟩ := refines_dvd huy hc
    refine ⟨Nat.gcd a b, mem_sfMeet.mpr ⟨?_, a, ha, b, hb, rfl⟩, Nat.dvd_gcd hca hcb⟩
    intro h1
    have hd := Nat.dvd_gcd hca hcb
    rw [h1, Nat.dvd_one] at hd
    have := hu.1 c hc
    omega

theorem lattice_sf {k : ℕ} (hk : 1 ≤ k) (hsq : Squarefree k) : IsLatticeFact k := by
  rcases Nat.lt_or_ge k 2 with h1 | h2
  · have hk1 : k = 1 := by omega
    subst hk1
    intro x y hx hy
    have ex := isFact_one hx
    have ey := isFact_one hy
    subst ex
    subst ey
    exact ⟨⟨0, hx, refines_refl 0, refines_refl 0, fun _ _ h _ => h⟩,
      ⟨0, hx, refines_refl 0, refines_refl 0, fun _ _ h _ => h⟩⟩
  · have hmeet : ∀ x y, IsFact k x → IsFact k y → ∃ w, MeetSpec k x y w :=
      fun x y hx hy => ⟨sfMeet x y, sf_meet hsq hx hy⟩
    have hjoin := joins_of_meets h2 hmeet
    intro x y hx hy
    obtain ⟨z, hz⟩ := hjoin x y hx hy
    obtain ⟨w, hw⟩ := hmeet x y hx hy
    exact ⟨⟨z, hz⟩, ⟨w, hw⟩⟩

/-! ## Non-lattice passes to multiples (the principal ideal below {k} + P) -/

theorem refines_add_right {F G : Multiset ℕ} (h : Refines F G) (P : Multiset ℕ) :
    Refines (F + P) (G + P) := by
  obtain ⟨H, rfl, rfl⟩ := h
  refine ⟨H + P.map (fun x => ({x} : Multiset ℕ)), ?_, ?_⟩
  · rw [Multiset.join_add, join_map_singleton]
  · rw [Multiset.map_add, Multiset.map_map]
    congr 1
    conv_rhs => rw [← Multiset.map_id' P]
    apply Multiset.map_congr rfl
    intro x _
    simp

theorem ideal_shape {H P : Multiset ℕ} {k : ℕ} (hP : ∀ q ∈ P, q.Prime) (hH : ∀ x ∈ H, 2 ≤ x)
    (h : Refines H (k ::ₘ P)) : ∃ F, H = F + P ∧ F.prod = k := by
  obtain ⟨B, hBj, hBm⟩ := h
  obtain ⟨b0, B', rfl, hb0, hB'⟩ := map_eq_cons' Multiset.prod B P k hBm
  have hsing : ∀ b ∈ B', b = {b.prod} := by
    intro b hb
    apply eq_single_of_prime
    · intro x hx
      apply hH
      rw [← hBj, Multiset.join_cons]
      exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_join.mpr ⟨b, hb, hx⟩))
    · rw [← hB'] at hP
      exact hP _ (Multiset.mem_map_of_mem _ hb)
  have hB'eq : B' = P.map (fun x => ({x} : Multiset ℕ)) := by
    rw [← hB', Multiset.map_map]
    conv_lhs => rw [← Multiset.map_id' B']
    apply Multiset.map_congr rfl
    intro b hb
    exact hsing b hb
  refine ⟨b0, ?_, hb0⟩
  rw [← hBj, Multiset.join_cons, hB'eq, join_map_singleton]

theorem refines_cancel {F G : Multiset ℕ} (hF : ∀ x ∈ F, 2 ≤ x) :
    ∀ P : Multiset ℕ, (∀ q ∈ P, q.Prime) → Refines (F + P) (G + P) → Refines F G := by
  intro P
  induction P using Multiset.induction with
  | empty => intro _ h; simpa using h
  | cons p P ih =>
    intro hP h
    apply ih (fun q hq => hP q (Multiset.mem_cons_of_mem hq))
    obtain ⟨B, hBj, hBm⟩ := h
    rw [Multiset.add_cons] at hBm hBj
    obtain ⟨b, B', rfl, hbp, hB'⟩ := map_eq_cons' Multiset.prod B (G + P) p hBm
    have hpp : p.Prime := hP p (Multiset.mem_cons_self p P)
    have hb2 : ∀ x ∈ b, 2 ≤ x := by
      intro x hx
      have hx' : x ∈ p ::ₘ (F + P) := by
        rw [← hBj, Multiset.join_cons]
        exact Multiset.mem_add.mpr (Or.inl hx)
      rcases Multiset.mem_cons.mp hx' with h1 | h1
      · rw [h1]
        exact hpp.two_le
      · rcases Multiset.mem_add.mp h1 with h2 | h2
        · exact hF x h2
        · exact (hP x (Multiset.mem_cons_of_mem h2)).two_le
    have hbs : b = {p} := by
      have e := eq_single_of_prime hb2 (by rw [hbp]; exact hpp)
      rw [hbp] at e
      exact e
    rw [Multiset.join_cons, hbs, Multiset.singleton_add, Multiset.cons_inj_right] at hBj
    exact ⟨B', hBj, hB'⟩

theorem lattice_of_dvd {k n : ℕ} (hk : 2 ≤ k) (hn : 0 < n) (hkn : k ∣ n) (h : IsLatticeFact n) :
    IsLatticeFact k := by
  obtain ⟨m, rfl⟩ := hkn
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hn
  obtain ⟨P, hP, hPprod⟩ : ∃ P : Multiset ℕ, (∀ q ∈ P, q.Prime) ∧ P.prod = m :=
    ⟨(m.primeFactorsList : Multiset ℕ),
      fun q hq => Nat.prime_of_mem_primeFactorsList (Multiset.mem_coe.mp hq),
      by rw [Multiset.prod_coe, Nat.prod_primeFactorsList hm0]⟩
  have hP2 : ∀ q ∈ P, 2 ≤ q := fun q hq => (hP q hq).two_le
  have liftF : ∀ F, IsFact k F → IsFact (k * m) (F + P) := by
    intro F hF
    refine ⟨fun x hx => ?_, by rw [Multiset.prod_add, hF.2, hPprod]⟩
    rcases Multiset.mem_add.mp hx with h1 | h1
    · exact hF.1 x h1
    · exact hP2 x h1
  have hG : IsFact (k * m) (k ::ₘ P) := by
    refine ⟨fun x hx => ?_, by rw [Multiset.prod_cons, hPprod]⟩
    rcases Multiset.mem_cons.mp hx with h1 | h1
    · rw [h1]
      exact hk
    · exact hP2 x h1
  have toG : ∀ F, IsFact k F → Refines (F + P) (k ::ₘ P) := by
    intro F hF
    have e := refines_add_right (refines_top F) P
    rwa [hF.2, Multiset.singleton_add] at e
  have down : ∀ H, IsFact (k * m) H → Refines H (k ::ₘ P) → ∃ F, IsFact k F ∧ H = F + P := by
    intro H hH hHG
    obtain ⟨F, rfl, hFk⟩ := ideal_shape hP hH.1 hHG
    exact ⟨F, ⟨fun x hx => hH.1 x (Multiset.mem_add.mpr (Or.inl hx)), hFk⟩, rfl⟩
  intro x y hx hy
  obtain ⟨⟨z, hz, hxz, hyz, hzu⟩, ⟨w, hw, hwx, hwy, hwu⟩⟩ :=
    h (x + P) (y + P) (liftF x hx) (liftF y hy)
  obtain ⟨z0, hz0, rfl⟩ := down z hz (hzu _ hG (toG x hx) (toG y hy))
  obtain ⟨w0, hw0, rfl⟩ := down w hw (refines_trans hwx (toG x hx))
  refine ⟨⟨z0, hz0, refines_cancel hx.1 P hP hxz, refines_cancel hy.1 P hP hyz,
      fun u hu hxu hyu => ?_⟩,
    ⟨w0, hw0, refines_cancel hw0.1 P hP hwx, refines_cancel hw0.1 P hP hwy,
      fun u hu hux huy => ?_⟩⟩
  · exact refines_cancel hz0.1 P hP
      (hzu _ (liftF u hu) (refines_add_right hxu P) (refines_add_right hyu P))
  · exact refines_cancel hu.1 P hP
      (hwu _ (liftF u hu) (refines_add_right hux P) (refines_add_right huy P))

/-! ## Assembly of the lattice direction -/

theorem lattice_of_noS {k : ℕ} (hk : 1 ≤ k) (h : ¬ ∃ s, InS s ∧ s ∣ k) : IsLatticeFact k := by
  rcases classify hk h with hsq | ⟨p, hp, hk'⟩ | ⟨p, q, hp, hq, hpq, hk'⟩
  · exact lattice_sf hk hsq
  · have h2 := hp.two_le
    rcases hk' with rfl | rfl | rfl
    · refine lattice_of_card_le3 (Z := Multiset.replicate 2 p)
        (le_trans (by norm_num) (Nat.pow_le_pow_left h2 2)) ?_ (Multiset.prod_replicate 2 p) (by simp)
      intro r hr
      rw [Multiset.eq_of_mem_replicate hr]
      exact hp
    · refine lattice_of_card_le3 (Z := Multiset.replicate 3 p)
        (le_trans (by norm_num) (Nat.pow_le_pow_left h2 3)) ?_ (Multiset.prod_replicate 3 p) (by simp)
      intro r hr
      rw [Multiset.eq_of_mem_replicate hr]
      exact hp
    · exact lattice_p4 hp
  · rcases hk' with rfl | rfl
    · refine lattice_of_card_le3 (Z := p ::ₘ p ::ₘ q ::ₘ 0)
        (le_trans (by norm_num) (Nat.mul_le_mul (Nat.pow_le_pow_left hp.two_le 2) hq.two_le))
        (by simp [hp, hq]) (by simp only [Multiset.prod_cons, Multiset.prod_zero]; ring) (by simp)
    · exact lattice_p2q2 hp hq hpq

end OMA.A317534Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a317534.main := by
  intro k hk
  constructor
  · intro hnot
    by_contra hno
    exact hnot (OMA.A317534Proof.lattice_of_noS hk hno)
  · rintro ⟨s, hs, hsk⟩ hlat
    exact OMA.A317534Proof.not_lattice_of_InS hs
      (OMA.A317534Proof.lattice_of_dvd (OMA.A317534Proof.InS_two_le hs) (by omega) hsk hlat)
