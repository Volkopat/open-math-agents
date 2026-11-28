import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H3_R1

-- Step Erdos1160.erdos_1160.variants.sum.R3.H1.R1.H3.R1.H2: hypothesis H2 of reduction Erdos1160.erdos_1160.variants.sum.R3.H1.R1.H3.R1
-- Credit: @theterabites
--
-- g n (groups of order n up to isomorphism) is at least the product of g over the prime-power
-- parts of n. Choosing one group of order p^e for each prime p gives the class of their direct
-- product, of order n. The map is injective: an isomorphism of such products sends each factor
-- (the elements killed by p^e, trivial at the other primes since the orders are coprime) onto
-- the corresponding factor. The classes of each order are finite (a class is determined by a
-- multiplication table on Fin m), so the counts compare as cardinalities.

open CategoryTheory Erdos1160

namespace OMA.E1160H2

/-- The isomorphism classes of finite groups of order `m`. -/
abbrev C (m : ℕ) : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
  Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G = m}

lemma g_eq (m : ℕ) : g m = (C m).ncard := rfl

/-- Two finite groups have the same class iff they are isomorphic as groups. -/
lemma mk_eq_iff {G H : FiniteGrp.{0}} :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) G = Quotient.mk _ H) ↔ Nonempty (G ≃* H) := by
  constructor
  · intro h
    obtain ⟨i⟩ := Quotient.exact h
    exact ⟨Iso.groupIsoToMulEquiv ((inducedFunctor FiniteGrp.toGrp).mapIso i)⟩
  · rintro ⟨e⟩
    exact Quotient.sound ⟨InducedCategory.isoMk e.toGrpIso⟩

/-- There are finitely many classes of each order: a class is determined by a multiplication
table on `Fin m`. -/
lemma C_finite (m : ℕ) : (C m).Finite := by
  classical
  have key : ∀ q : C m, ∃ t : Fin m → Fin m → Fin m, ∃ G : FiniteGrp.{0},
      Quotient.mk _ G = (q : Quotient (isIsomorphicSetoid FiniteGrp.{0})) ∧
      ∃ e : G ≃ Fin m, ∀ a b : G, e (a * b) = t (e a) (e b) := by
    rintro ⟨q, G, hG, rfl⟩
    let e : G ≃ Fin m := (Finite.equivFin G).trans (finCongr hG)
    exact ⟨fun x y => e (e.symm x * e.symm y), G, rfl, e, fun a b => by simp⟩
  choose t G hG e he using key
  have hinj : Function.Injective t := by
    intro q q' htt
    apply Subtype.ext
    rw [← hG q, ← hG q', mk_eq_iff]
    refine ⟨{ toEquiv := (e q).trans (e q').symm, map_mul' := ?_ }⟩
    intro a b
    apply (e q').injective
    change (e q') ((e q').symm ((e q) (a * b))) =
      (e q') ((e q').symm ((e q) a) * (e q').symm ((e q) b))
    rw [Equiv.apply_symm_apply, he q, he q', Equiv.apply_symm_apply, Equiv.apply_symm_apply, htt]
  have : Finite (C m) := Finite.of_injective t hinj
  exact Set.toFinite _

/-- In a product of finite groups of pairwise coprime orders, an element killed by the order of
the `i`-th factor is trivial outside `i`. -/
lemma trivial_outside {ι : Type} [DecidableEq ι] {X : ι → Type} [∀ i, Group (X i)]
    [∀ i, Finite (X i)] {N : ι → ℕ} (hN : ∀ i, Nat.card (X i) = N i)
    (hcop : ∀ i j, i ≠ j → Nat.Coprime (N i) (N j)) {i : ι} {y : ∀ j, X j}
    (hy : y ^ N i = 1) : ∀ j, j ≠ i → y j = 1 := by
  intro j hji
  have h1 : y j ^ N i = 1 := by
    have := congrFun hy j
    simpa using this
  have h2 : y j ^ N j = 1 := by
    rw [← hN j]; exact pow_card_eq_one'
  have d1 := orderOf_dvd_of_pow_eq_one h1
  have d2 := orderOf_dvd_of_pow_eq_one h2
  have hg := Nat.dvd_gcd d1 d2
  rw [Nat.Coprime.gcd_eq_one (hcop i j (Ne.symm hji))] at hg
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hg)

/-- An isomorphism of products of finite groups of pairwise coprime orders restricts to
isomorphisms of the factors. -/
lemma factor_iso {ι : Type} [DecidableEq ι] {A B : ι → Type} [∀ i, Group (A i)] [∀ i, Group (B i)]
    [∀ i, Finite (A i)] [∀ i, Finite (B i)] {N : ι → ℕ} (hA : ∀ i, Nat.card (A i) = N i)
    (hB : ∀ i, Nat.card (B i) = N i) (hcop : ∀ i j, i ≠ j → Nat.Coprime (N i) (N j))
    (ψ : (∀ i, A i) ≃* (∀ i, B i)) (i : ι) : Nonempty (A i ≃* B i) := by
  have single_pow {X : ι → Type} [∀ i, Group (X i)] [∀ i, Finite (X i)]
      (hX : ∀ i, Nat.card (X i) = N i) (a : X i) : (Pi.mulSingle i a : ∀ j, X j) ^ N i = 1 := by
    rw [← Pi.mulSingle_pow, ← hX i, pow_card_eq_one', Pi.mulSingle_one]
  have hf (a : A i) : ψ (Pi.mulSingle i a) = Pi.mulSingle i (ψ (Pi.mulSingle i a) i) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · rw [Pi.mulSingle_eq_of_ne hj]
      apply trivial_outside hB hcop _ j hj
      rw [← map_pow, single_pow hA, map_one]
  have hg (b : B i) : ψ.symm (Pi.mulSingle i b) = Pi.mulSingle i (ψ.symm (Pi.mulSingle i b) i) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · rw [Pi.mulSingle_eq_of_ne hj]
      apply trivial_outside hA hcop _ j hj
      rw [← map_pow, single_pow hB, map_one]
  refine ⟨{ toFun := fun a => ψ (Pi.mulSingle i a) i
            invFun := fun b => ψ.symm (Pi.mulSingle i b) i
            left_inv := ?_, right_inv := ?_, map_mul' := ?_ }⟩
  · intro a
    simp only
    rw [← hf a, MulEquiv.symm_apply_apply, Pi.mulSingle_eq_same]
  · intro b
    simp only
    rw [← hg b, MulEquiv.apply_symm_apply, Pi.mulSingle_eq_same]
  · intro a b
    simp only [Pi.mulSingle_mul, map_mul, Pi.mul_apply]

/-- A chosen representative of a class of order `m`. -/
noncomputable def rep {m : ℕ} (q : C m) : FiniteGrp.{0} := Classical.choose q.2

lemma rep_spec {m : ℕ} (q : C m) :
    Nat.card (rep q) = m ∧ Quotient.mk _ (rep q) = (q : Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
  Classical.choose_spec q.2

theorem product_lower (n : ℕ) (hn : 0 < n) :
    (∏ p ∈ n.primeFactors, g (p ^ n.factorization p)) ≤ g n := by
  classical
  let P := n.primeFactors
  let N : P → ℕ := fun p => (p : ℕ) ^ n.factorization p
  have hcop : ∀ p q : P, p ≠ q → Nat.Coprime (N p) (N q) := by
    intro p q hpq
    have hp := Nat.prime_of_mem_primeFactors p.2
    have hq := Nat.prime_of_mem_primeFactors q.2
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hq).mpr (fun h => hpq (Subtype.ext h)))
  -- the map from families of classes to classes of order n
  let prodGrp (c : ∀ p : P, C (N p)) : FiniteGrp.{0} := FiniteGrp.of (∀ p : P, rep (c p))
  have hcard (c : ∀ p : P, C (N p)) : Nat.card (prodGrp c) = n := by
    change Nat.card (∀ p : P, rep (c p)) = n
    rw [Nat.card_pi]
    simp only [fun p => (rep_spec (c p)).1]
    rw [Finset.prod_coe_sort n.primeFactors (fun p => p ^ n.factorization p)]
    conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn.ne']
    rw [Finsupp.prod, Nat.support_factorization]
  let Φ : (∀ p : P, C (N p)) → C n := fun c => ⟨Quotient.mk _ (prodGrp c), prodGrp c, hcard c, rfl⟩
  have hΦ : Function.Injective Φ := by
    intro c c' h
    have h' : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (prodGrp c) = Quotient.mk _ (prodGrp c') :=
      congrArg Subtype.val h
    obtain ⟨ψ⟩ := mk_eq_iff.mp h'
    funext p
    obtain ⟨e⟩ := factor_iso (A := fun p => rep (c p)) (B := fun p => rep (c' p)) (N := N)
      (fun p => (rep_spec (c p)).1) (fun p => (rep_spec (c' p)).1) hcop ψ p
    apply Subtype.ext
    rw [← (rep_spec (c p)).2, ← (rep_spec (c' p)).2, mk_eq_iff]
    exact ⟨e⟩
  have hfin : Finite (C n) := (C_finite n).to_subtype
  have hle := Nat.card_le_card_of_injective Φ hΦ
  rw [Nat.card_pi] at hle
  rw [g_eq, ← Nat.card_coe_set_eq]
  calc (∏ p ∈ n.primeFactors, g (p ^ n.factorization p))
      = ∏ p : P, Nat.card (C (N p)) := by
        rw [← Finset.prod_coe_sort n.primeFactors]
        rfl
    _ ≤ Nat.card (C n) := hle

end OMA.E1160H2

theorem OMA.solution : OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H3_R1.H2 :=
  fun n hn => OMA.E1160H2.product_lower n hn
