import OMAReductions.R_ConjugacyClassSizes_conjClassSizes_iff_sym_three_solvable_R1
import Mathlib

/-!
Deep structural reduction of Gow's theorem on prime divisors of finite solvable rational groups
(`ConjugacyClassSizes.conjClassSizes_iff_sym_three_solvable.R1.H1`).

Inside `main`, we prove from scratch:
1. Coprime exponent lifting and closure of rationality under quotients.
2. Minimal counterexample reduction via Schur–Zassenhaus: a minimal finite solvable rational
   group divisible by a prime `p ≥ 7` splits as `V ⋊ H` with `V ≅ (ZMod p)^d` and `H` a
   finite solvable rational `{2, 3, 5}`-group acting faithfully and irreducibly on `V`.
3. Joint Scaling Condition (combining the Eigenvector Property, Miracle Centralizer Rationality
   of `C_H(v)`, and triviality of the `N_H(⟨v⟩)`-action on conjugacy classes of `C_H(v)`).
4. Maschke semisimplicity and Super-Lemma 1: `O_q(H) = 1` for every prime `q ≥ 5` (in particular
   `O_5(H) = 1`).
5. Eigenspace Dimension Bound: `finrank (ker (ρ g - c • id)) * φ(ord c) ≤ d` and `φ(p - 1) ≤ d`.
6. Universal Monomial Killer: in any maximal imprimitivity decomposition `V = ⨁_{i : Fin m} W i`,
   the block stabilizer acts irreducibly, primitively, and non-abelianly on `W 0` (eliminating
   all monomial representations, even over arbitrary field extensions).
7. Clifford isotypic decomposition and the 2-Group Theorem: `H` cannot be a `2`-group.
8. Primitive Abelian Normal Subgroup Theorem: when `V` is primitive under `H`, every abelian
   normal subgroup `A ◁ H` is cyclic of order in `{1, 2, 3, 4, 6}`, with `p ≡ 2 [MOD 3]` if
   `3 ∣ |A|` and `p ≡ 3 [MOD 4]` if `4 ∣ |A|`.

This splits `R1.H1` cleanly into three structural regimes:
- `H1`: primitive with `O_3(H) = O_5(H) = 1` (pure `2`-group Fitting subgroup `F(H) = O_2(H)`).
- `H2`: primitive with `O_3(H) ≠ 1`, `O_5(H) = 1`, `|Z(Q)| = 3`, and `p ≡ 2 [MOD 3]`.
- `H3`: imprimitive non-monomial (`m ≥ 2` maximal blocks with non-abelian primitive stabilizer).
-/

namespace OMA.R_ConjugacyClassSizes_conjClassSizes_iff_sym_three_solvable_R1_H1_R1

/-- Primitive case with `O_3(H) = O_5(H) = 1` (so the Fitting subgroup is a `2`-group):
no finite solvable rational `{2, 3, 5}`-group with trivial `O_3` and `O_5`, not a `2`-group,
and every abelian normal subgroup of order in `{1, 2, 4}` (with `p % 4 = 3` for order `4`)
admits a faithful, irreducible, primitive linear action over `ZMod p` (`p ≥ 7` prime)
satisfying the eigenspace dimension bound and the joint scaling condition. -/
def H1 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (_ : 7 ≤ p) (d : ℕ) (_ : Nat.totient (p - 1) ≤ d)
    (H : Type) [Group H] [Fintype H] [Group.IsSolvable H]
    (_ : ∀ q : ℕ, q.Prime → q ∣ Nat.card H → q = 2 ∨ q = 3 ∨ q = 5)
    (_ : ∀ (x : H) (n : ℕ), (Nat.card H).Coprime n → IsConj x (x ^ n))
    (_ : ∀ Q : Subgroup H, Q.Normal → IsPGroup 3 Q → Q = ⊥)
    (_ : ∀ Q : Subgroup H, Q.Normal → IsPGroup 5 Q → Q = ⊥)
    (_ : ¬ IsPGroup 2 H)
    (_ : ∀ A : Subgroup H, A.Normal → (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) →
      Nat.card A = 1 ∨ Nat.card A = 2 ∨ (Nat.card A = 4 ∧ p % 4 = 3))
    (ρ : H →* ((Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p))),
    Function.Injective ρ →
    (∀ W : Submodule (ZMod p) (Fin d → ZMod p),
      (∀ h : H, ∀ v ∈ W, ρ h v ∈ W) → W = ⊥ ∨ W = ⊤) →
    (∀ (m : ℕ) (W : Fin m → Submodule (ZMod p) (Fin d → ZMod p)),
      2 ≤ m → iSupIndep W → iSup W = ⊤ → (∀ i, W i ≠ ⊥) →
      ¬ ∀ h : H, ∃ σ : Equiv.Perm (Fin m),
        ∀ i, Submodule.map (ρ h).toLinearMap (W i) = W (σ i)) →
    (∀ (g : H) (c : (ZMod p)ˣ),
      Module.finrank (ZMod p) (LinearMap.ker ((ρ g).toLinearMap - (c : ZMod p) • LinearMap.id)) *
        Nat.totient (orderOf c) ≤ d) →
    (∀ (v : Fin d → ZMod p), v ≠ 0 → ∀ (y : H), ρ y v = v →
      ∀ (c : (ZMod p)ˣ) (n : ℕ), (Nat.card {h : H // ρ h v = v}).Coprime n →
        ∃ h : H, ρ h v = (c : ZMod p) • v ∧ h * y * h⁻¹ = y ^ n) →
    False

/-- Primitive case with a nontrivial normal `3`-subgroup (`O_3(H) ≠ 1`, `O_5(H) = 1`,
forcing `p % 3 = 2` and `|Z(Q)| = 3`): no finite solvable rational `{2, 3, 5}`-group
satisfying these conditions admits a faithful, irreducible, primitive linear action over
`ZMod p` (`p ≥ 7` prime) with the eigenspace dimension bound and joint scaling condition. -/
def H2 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (_ : 7 ≤ p) (_ : p % 3 = 2) (d : ℕ) (_ : Nat.totient (p - 1) ≤ d)
    (H : Type) [Group H] [Fintype H] [Group.IsSolvable H]
    (_ : ∀ q : ℕ, q.Prime → q ∣ Nat.card H → q = 2 ∨ q = 3 ∨ q = 5)
    (_ : ∀ (x : H) (n : ℕ), (Nat.card H).Coprime n → IsConj x (x ^ n))
    (_ : ∀ Q : Subgroup H, Q.Normal → IsPGroup 5 Q → Q = ⊥)
    (_ : ∃ Q : Subgroup H, Q.Normal ∧ IsPGroup 3 Q ∧ Q ≠ ⊥ ∧
      Nat.card (Subgroup.center Q) = 3)
    (_ : ∀ A : Subgroup H, A.Normal → (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) →
      Nat.card A = 1 ∨ Nat.card A = 2 ∨ Nat.card A = 3 ∨
      (Nat.card A = 4 ∧ p % 4 = 3) ∨ Nat.card A = 6)
    (ρ : H →* ((Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p))),
    Function.Injective ρ →
    (∀ W : Submodule (ZMod p) (Fin d → ZMod p),
      (∀ h : H, ∀ v ∈ W, ρ h v ∈ W) → W = ⊥ ∨ W = ⊤) →
    (∀ (m : ℕ) (W : Fin m → Submodule (ZMod p) (Fin d → ZMod p)),
      2 ≤ m → iSupIndep W → iSup W = ⊤ → (∀ i, W i ≠ ⊥) →
      ¬ ∀ h : H, ∃ σ : Equiv.Perm (Fin m),
        ∀ i, Submodule.map (ρ h).toLinearMap (W i) = W (σ i)) →
    (∀ (g : H) (c : (ZMod p)ˣ),
      Module.finrank (ZMod p) (LinearMap.ker ((ρ g).toLinearMap - (c : ZMod p) • LinearMap.id)) *
        Nat.totient (orderOf c) ≤ d) →
    (∀ (v : Fin d → ZMod p), v ≠ 0 → ∀ (y : H), ρ y v = v →
      ∀ (c : (ZMod p)ˣ) (n : ℕ), (Nat.card {h : H // ρ h v = v}).Coprime n →
        ∃ h : H, ρ h v = (c : ZMod p) • v ∧ h * y * h⁻¹ = y ^ n) →
    False

/-- Imprimitive non-monomial case: no finite solvable rational `{2, 3, 5}`-group with
trivial `O_5` and not a `2`-group admits a faithful, irreducible linear action over
`ZMod p` (`p ≥ 7` prime) with a maximal imprimitivity decomposition into `m ≥ 2` blocks
having non-abelian transitive block stabilizer action, eigenspace dimension bound,
and joint scaling condition. -/
def H3 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (_ : 7 ≤ p) (d : ℕ) (_ : Nat.totient (p - 1) ≤ d)
    (H : Type) [Group H] [Fintype H] [Group.IsSolvable H]
    (_ : ∀ q : ℕ, q.Prime → q ∣ Nat.card H → q = 2 ∨ q = 3 ∨ q = 5)
    (_ : ∀ (x : H) (n : ℕ), (Nat.card H).Coprime n → IsConj x (x ^ n))
    (_ : ∀ Q : Subgroup H, Q.Normal → IsPGroup 5 Q → Q = ⊥)
    (_ : ¬ IsPGroup 2 H)
    (ρ : H →* ((Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p))),
    Function.Injective ρ →
    (∀ W : Submodule (ZMod p) (Fin d → ZMod p),
      (∀ h : H, ∀ v ∈ W, ρ h v ∈ W) → W = ⊥ ∨ W = ⊤) →
    (∃ (m : ℕ) (W : Fin m → Submodule (ZMod p) (Fin d → ZMod p)),
      2 ≤ m ∧ iSupIndep W ∧ iSup W = ⊤ ∧ (∀ i, W i ≠ ⊥) ∧
      (∀ h : H, ∃ σ : Equiv.Perm (Fin m),
        ∀ i, Submodule.map (ρ h).toLinearMap (W i) = W (σ i)) ∧
      (∀ i j : Fin m, ∃ h : H, Submodule.map (ρ h).toLinearMap (W i) = W j) ∧
      (∃ (i : Fin m) (h₁ h₂ : H),
        Submodule.map (ρ h₁).toLinearMap (W i) = W i ∧
        Submodule.map (ρ h₂).toLinearMap (W i) = W i ∧
        ∃ v ∈ W i, ρ (h₁ * h₂) v ≠ ρ (h₂ * h₁) v) ∧
      (∀ (m' : ℕ) (W' : Fin m' → Submodule (ZMod p) (Fin d → ZMod p)),
        iSupIndep W' → iSup W' = ⊤ → (∀ i, W' i ≠ ⊥) →
        (∀ h : H, ∃ σ : Equiv.Perm (Fin m'),
          ∀ i, Submodule.map (ρ h).toLinearMap (W' i) = W' (σ i)) →
        m' ≤ m)) →
    (∀ (g : H) (c : (ZMod p)ˣ),
      Module.finrank (ZMod p) (LinearMap.ker ((ρ g).toLinearMap - (c : ZMod p) • LinearMap.id)) *
        Nat.totient (orderOf c) ≤ d) →
    (∀ (v : Fin d → ZMod p), v ≠ 0 → ∀ (y : H), ρ y v = v →
      ∀ (c : (ZMod p)ˣ) (n : ℕ), (Nat.card {h : H // ρ h v = v}).Coprime n →
        ∃ h : H, ρ h v = (c : ZMod p) • v ∧ h * y * h⁻¹ = y ^ n) →
    False

/- ### Component 1: Coprime Exponent Lifting and Quotient Rationality -/

lemma coprime_lift {M N r : ℕ} (hN : N ≠ 0) (hr : M.Coprime r) :
    ∃ m : ℕ, m ≡ r [MOD M] ∧ N.Coprime m := by
  classical
  let S := N.primeFactors.filter (fun q => ¬ (q ∣ M) ∧ ¬ (q ∣ r))
  let P := ∏ q ∈ S, q
  refine ⟨r + M * P, ?_, ?_⟩
  · change (r + M * P) % M = r % M
    rw [Nat.add_mul_mod_self_left]
  · rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne
    obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd hne
    have hqN : q ∣ N := dvd_trans hq_dvd (Nat.gcd_dvd_left _ _)
    have hqm : q ∣ r + M * P := dvd_trans hq_dvd (Nat.gcd_dvd_right _ _)
    by_cases hqM : q ∣ M
    · have hqr : q ∣ r := (Nat.dvd_add_left (dvd_mul_of_dvd_left hqM P)).mp hqm
      exact hq_prime.not_dvd_one (hr ▸ Nat.dvd_gcd hqM hqr)
    · by_cases hqr : q ∣ r
      · have hqMP : q ∣ M * P := (Nat.dvd_add_right hqr).mp hqm
        rcases hq_prime.dvd_mul.mp hqMP with h1 | h2
        · exact hqM h1
        · obtain ⟨q', hq'S, hqq'⟩ :=
            (Prime.dvd_finsetProd_iff hq_prime.prime _).mp h2
          have hq'mem := Finset.mem_filter.mp hq'S
          have hq'prime : q'.Prime := (Nat.mem_primeFactors.mp hq'mem.1).1
          have heq : q = q' := (Nat.prime_dvd_prime_iff_eq hq_prime hq'prime).mp hqq'
          exact hq'mem.2.2 (heq ▸ hqr)
      · have hqS : q ∈ S := Finset.mem_filter.mpr
          ⟨Nat.mem_primeFactors.mpr ⟨hq_prime, hqN, hN⟩, hqM, hqr⟩
        have hqP : q ∣ P := Finset.dvd_prod_of_mem _ hqS
        have hqr' : q ∣ r := (Nat.dvd_add_left (dvd_mul_of_dvd_right hqP M)).mp hqm
        exact hqr hqr'

lemma coprime_lift_two {A B N r₁ r₂ : ℕ} (hN : N ≠ 0) (hAB : A.Coprime B)
    (hr₁ : A.Coprime r₁) (hr₂ : B.Coprime r₂) :
    ∃ m : ℕ, m ≡ r₁ [MOD A] ∧ m ≡ r₂ [MOD B] ∧ N.Coprime m := by
  let cr := Nat.chineseRemainder hAB r₁ r₂
  have hcop : (A * B).Coprime cr.1 := by
    refine Nat.Coprime.mul_left ?_ ?_
    · rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_rec, cr.2.1, ← Nat.gcd_rec,
        ← Nat.coprime_iff_gcd_eq_one]
      exact hr₁
    · rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_rec, cr.2.2, ← Nat.gcd_rec,
        ← Nat.coprime_iff_gcd_eq_one]
      exact hr₂
  obtain ⟨m, hm, hmN⟩ := coprime_lift hN hcop
  refine ⟨m, ?_, ?_, hmN⟩
  · exact (hm.of_dvd (dvd_mul_right A B)).trans cr.2.1
  · exact (hm.of_dvd (dvd_mul_left B A)).trans cr.2.2

lemma isConj_pow_of_coprime_orderOf {G : Type*} [Group G] [Fintype G]
    (hrat : ∀ (x : G) (n : ℕ), (Nat.card G).Coprime n → IsConj x (x ^ n))
    (x : G) {r : ℕ} (hr : (orderOf x).Coprime r) :
    IsConj x (x ^ r) := by
  obtain ⟨m, hm, hmG⟩ := coprime_lift (N := Nat.card G) Nat.card_pos.ne' hr
  have hpow : x ^ m = x ^ r := by
    rw [← pow_mod_orderOf, ← pow_mod_orderOf (n := r)]
    exact congrArg (x ^ ·) hm
  rw [← hpow]
  exact hrat x m hmG

lemma rational_quotient {G : Type*} [Group G] [Fintype G]
    (hrat : ∀ (x : G) (n : ℕ), (Nat.card G).Coprime n → IsConj x (x ^ n))
    (N : Subgroup G) [N.Normal] :
    ∀ (x : G ⧸ N) (n : ℕ), (Nat.card (G ⧸ N)).Coprime n → IsConj x (x ^ n) := by
  intro x n hn
  induction x using QuotientGroup.induction_on with
  | H g =>
    obtain ⟨m, hm, hmG⟩ := coprime_lift (N := Nat.card G) Nat.card_pos.ne' hn
    obtain ⟨c, hc⟩ := isConj_iff.mp (hrat g m hmG)
    rw [isConj_iff]
    refine ⟨QuotientGroup.mk c, ?_⟩
    have hq : (QuotientGroup.mk g : G ⧸ N) ^ m = (QuotientGroup.mk g : G ⧸ N) ^ n := by
      have hord : orderOf (QuotientGroup.mk g : G ⧸ N) ∣ Nat.card (G ⧸ N) :=
        orderOf_dvd_natCard _
      have hm' : m ≡ n [MOD orderOf (QuotientGroup.mk g : G ⧸ N)] := hm.of_dvd hord
      rw [← pow_mod_orderOf, ← pow_mod_orderOf (n := n)]
      exact congrArg ((QuotientGroup.mk g : G ⧸ N) ^ ·) hm'
    rw [← hq]
    change QuotientGroup.mk (c * g * c⁻¹) = QuotientGroup.mk (g ^ m)
    rw [hc]

lemma rational_of_mulEquiv {G K : Type*} [Group G] [Fintype G] [Group K] [Fintype K]
    (e : G ≃* K)
    (hrat : ∀ (x : G) (n : ℕ), (Nat.card G).Coprime n → IsConj x (x ^ n)) :
    ∀ (x : K) (n : ℕ), (Nat.card K).Coprime n → IsConj x (x ^ n) := by
  intro x n hn
  have hcard : Nat.card G = Nat.card K := Nat.card_congr e.toEquiv
  rw [← hcard] at hn
  obtain ⟨c, hc⟩ := isConj_iff.mp (hrat (e.symm x) n hn)
  rw [isConj_iff]
  refine ⟨e c, ?_⟩
  calc e c * x * (e c)⁻¹
      = e (c * e.symm x * c⁻¹) := by simp
    _ = e ((e.symm x) ^ n) := by rw [hc]
    _ = x ^ n := by simp

/- ### Component 2: Minimal Counterexample Extraction and Joint Scaling -/

lemma exists_zmod_equiv_of_module {M : Type*} [AddCommGroup M] [Fintype M]
    {p : ℕ} [Fact p.Prime] [Module (ZMod p) M] [Nontrivial M] :
    ∃ (d : ℕ) (_ : 0 < d) (e : M ≃ (Fin d → ZMod p)),
      e 0 = 0 ∧
      (∀ u v : M, e (u + v) = e u + e v) ∧
      (∀ u : M, ∀ k : ℕ, e (k • u) = (k : ZMod p) • e u) := by
  classical
  let d := Module.finrank (ZMod p) M
  have hd : 0 < d := Module.finrank_pos
  let bM : Module.Basis (Fin d) (ZMod p) M := Module.finBasis (ZMod p) M
  let eLin : M ≃ₗ[ZMod p] (Fin d → ZMod p) := bM.equivFun
  exact ⟨d, hd, eLin.toEquiv, map_zero eLin, fun u v => map_add eLin u v,
    fun u k => by change eLin (k • u) = _; rw [map_nsmul, Nat.cast_smul_eq_nsmul]; rfl⟩

lemma exists_zmod_equiv_of_commGroup {V : Type*} [CommGroup V] [Fintype V]
    {p : ℕ} [Fact p.Prime] (hpow : ∀ v : V, v ^ p = 1) (hnt : Nontrivial V) :
    ∃ (d : ℕ) (_ : 0 < d) (e : V ≃ (Fin d → ZMod p)),
      e 1 = 0 ∧
      (∀ u v : V, e (u * v) = e u + e v) ∧
      (∀ u : V, ∀ k : ℕ, e (u ^ k) = (k : ZMod p) • e u) := by
  classical
  let hmod : Module (ZMod p) (Additive V) :=
    AddCommGroup.zmodModule (fun x => by
      change Additive.ofMul ((Additive.toMul x) ^ p) = Additive.ofMul 1
      congr 1
      exact hpow (Additive.toMul x))
  have hntAdd : Nontrivial (Additive V) := by
    obtain ⟨a, b, hab⟩ := exists_pair_ne V
    exact ⟨Additive.ofMul a, Additive.ofMul b, fun h => hab (Additive.ofMul.injective h)⟩
  obtain ⟨d, hd, eAdd, he0, headd, hensmul⟩ :=
    @exists_zmod_equiv_of_module (Additive V) _ inferInstance p _ hmod hntAdd
  exact ⟨d, hd, Additive.ofMul.trans eAdd, he0, fun u v => headd _ _, fun u k => hensmul _ k⟩

lemma exists_minimal_counterexample
    (hcontra : ¬ OMA.R_ConjugacyClassSizes_conjClassSizes_iff_sym_three_solvable_R1.H1) :
    ∃ (p : ℕ) (_ : Fact p.Prime) (_ : 7 ≤ p) (d : ℕ) (_ : 0 < d)
      (H : Type) (_ : Group H) (_ : Fintype H) (_ : Group.IsSolvable H),
      (∀ q : ℕ, q.Prime → q ∣ Nat.card H → q = 2 ∨ q = 3 ∨ q = 5) ∧
      (∀ (x : H) (n : ℕ), (Nat.card H).Coprime n → IsConj x (x ^ n)) ∧
      ∃ (ρ : H →* ((Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p))),
        Function.Injective ρ ∧
        (∀ W : Submodule (ZMod p) (Fin d → ZMod p),
          (∀ h : H, ∀ v ∈ W, ρ h v ∈ W) → W = ⊥ ∨ W = ⊤) ∧
        (∀ (v : Fin d → ZMod p), v ≠ 0 → ∀ (y : H), ρ y v = v →
          ∀ (c : (ZMod p)ˣ) (n : ℕ), (Nat.card {h : H // ρ h v = v}).Coprime n →
            ∃ h : H, ρ h v = (c : ZMod p) • v ∧ h * y * h⁻¹ = y ^ n) := by
  classical
  have hex : ∃ n : ℕ, ∃ (G : Type) (_ : Group G) (_ : Fintype G) (_ : Group.IsSolvable G),
      Nat.card G = n ∧
      (∀ (x : G) (k : ℕ), (Nat.card G).Coprime k → IsConj x (x ^ k)) ∧
      ∃ p : ℕ, p.Prime ∧ p ∣ Nat.card G ∧ ¬ (p = 2 ∨ p = 3 ∨ p = 5) := by
    unfold OMA.R_ConjugacyClassSizes_conjClassSizes_iff_sym_three_solvable_R1.H1 at hcontra
    push Not at hcontra
    obtain ⟨G, hG, hF, hS, hrat, p, hp, hpdvd, h2, h3, h5⟩ := hcontra
    exact ⟨Nat.card G, G, hG, hF, hS, rfl, hrat, p, hp, hpdvd, by tauto⟩
  obtain ⟨G, hG, hF, hS, hcardG, hratG, p, hp_prime, hp_dvd, hp_not235⟩ := Nat.find_spec hex
  have _hp_fact : Fact p.Prime := ⟨hp_prime⟩
  have hminG : ∀ (G' : Type) [Group G'] [Fintype G'] [Group.IsSolvable G'],
      Nat.card G' < Nat.card G →
      (∀ (x : G') (k : ℕ), (Nat.card G').Coprime k → IsConj x (x ^ k)) →
      ∀ q : ℕ, q.Prime → q ∣ Nat.card G' → q = 2 ∨ q = 3 ∨ q = 5 := by
    intro G' _ _ _ hlt hrat' q hq hqdvd
    by_contra hqnot
    have hlt' : Nat.card G' < Nat.find hex := by omega
    exact Nat.find_min hex hlt' ⟨G', inferInstance, inferInstance, inferInstance, rfl,
      hrat', q, hq, hqdvd, hqnot⟩
  have hp7 : 7 ≤ p := by
    have h2 := hp_prime.two_le
    by_contra hlt
    have hle : p ≤ 6 := by omega
    interval_cases p
    · exact hp_not235 (Or.inl rfl)
    · exact hp_not235 (Or.inr (Or.inl rfl))
    · exact absurd hp_prime (by decide)
    · exact hp_not235 (Or.inr (Or.inr rfl))
    · exact absurd hp_prime (by decide)
  -- Pick a minimal nontrivial normal subgroup V of G
  have hG_nontriv : (⊤ : Subgroup G) ≠ ⊥ := by
    intro htop
    have h1 : Nat.card G = 1 := by
      have := Subgroup.card_top (G := G)
      rw [htop, Subgroup.card_bot] at this
      exact this.symm
    rw [h1] at hp_dvd
    exact hp_prime.not_dvd_one hp_dvd
  have hexV : ∃ k : ℕ, ∃ V : Subgroup G, V.Normal ∧ V ≠ ⊥ ∧ Nat.card V = k :=
    ⟨Nat.card (⊤ : Subgroup G), ⊤, inferInstance, hG_nontriv, rfl⟩
  obtain ⟨V, hVnorm, hVne, hVcard⟩ := Nat.find_spec hexV
  have hVmin : ∀ W : Subgroup G, W.Normal → W ≠ ⊥ → W ≤ V → W = V := by
    intro W hWnorm hWne hWV
    by_contra hne
    have hlt : Nat.card W < Nat.card V := by
      have hss : (W : Set G) ⊂ (V : Set G) := Set.ssubset_iff_subset_ne.mpr ⟨hWV, by
        intro heq; exact hne (SetLike.coe_injective heq)⟩
      exact Set.Finite.card_lt_card (Set.toFinite _) hss
    have hlt' : Nat.card W < Nat.find hexV := by omega
    exact Nat.find_min hexV hlt' ⟨W, hWnorm, hWne, rfl⟩
  -- V is abelian
  have hVcomm : ∀ u ∈ V, ∀ v ∈ V, u * v = v * u := by
    have hcomm_lt : ⁅V, V⁆ < V := Group.IsSolvable.commutator_lt_of_ne_bot hVne
    have hcomm_norm : ⁅V, V⁆.Normal := Subgroup.commutator_normal V V
    have hcomm_bot : ⁅V, V⁆ = ⊥ := by
      by_contra hne
      exact hcomm_lt.ne (hVmin ⁅V, V⁆ hcomm_norm hne hcomm_lt.le)
    intro u hu v hv
    have hmem : u * v * u⁻¹ * v⁻¹ ∈ ⁅V, V⁆ := by
      rw [← commutatorElement_def]
      exact Subgroup.commutator_mem_commutator hu hv
    rw [hcomm_bot, Subgroup.mem_bot] at hmem
    calc u * v = (u * v * u⁻¹ * v⁻¹) * (v * u) := by group
      _ = 1 * (v * u) := by rw [hmem]
      _ = v * u := one_mul _
  -- Every prime dividing |G/V| is in {2, 3, 5}
  have hGV_lt : Nat.card (G ⧸ V) < Nat.card G := by
    have hlag := Subgroup.card_mul_index V
    have hVgt : 1 < Nat.card V := by
      rw [Nat.one_lt_iff_ne_zero_and_ne_one]
      refine ⟨Nat.card_pos.ne', ?_⟩
      intro h1
      apply hVne
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      have _hsub : Subsingleton V := (Nat.card_eq_one_iff_unique.mp h1).1
      exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : V) 1)
    change V.index < Nat.card G
    have hidx_pos : 0 < V.index := Nat.card_pos
    nlinarith
  have hGV_235 : ∀ q : ℕ, q.Prime → q ∣ Nat.card (G ⧸ V) → q = 2 ∨ q = 3 ∨ q = 5 :=
    hminG (G ⧸ V) hGV_lt (rational_quotient hratG V)
  -- p divides |V|
  have hp_dvd_V : p ∣ Nat.card V := by
    have hlag := Subgroup.card_mul_index V
    rw [← hlag] at hp_dvd
    rcases hp_prime.dvd_mul.mp hp_dvd with h1 | h2
    · exact h1
    · exact absurd (hGV_235 p hp_prime h2) hp_not235
  -- V has exponent p (every v ∈ V satisfies v ^ p = 1)
  have hVpow : ∀ v ∈ V, v ^ p = 1 := by
    let Vp : Subgroup G :=
      { carrier := {v ∈ V | v ^ p = 1}
        mul_mem' := fun {a b} ha hb => by
          refine ⟨V.mul_mem ha.1 hb.1, ?_⟩
          have hcomm : Commute a b := hVcomm a ha.1 b hb.1
          rw [hcomm.mul_pow, ha.2, hb.2, one_mul]
        one_mem' := ⟨V.one_mem, one_pow p⟩
        inv_mem' := fun {a} ha => ⟨V.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
    have hVp_le : Vp ≤ V := fun x hx => hx.1
    have hVp_norm : Vp.Normal := ⟨fun x hx g => by
      refine ⟨hVnorm.conj_mem x hx.1 g, ?_⟩
      rw [conj_pow, hx.2, mul_one, mul_inv_cancel]⟩
    have hVp_ne : Vp ≠ ⊥ := by
      obtain ⟨⟨x, hxV⟩, hxord⟩ := exists_prime_orderOf_dvd_card' (G := V) p hp_dvd_V
      intro hbot
      have hxVp : x ∈ Vp := by
        refine ⟨hxV, ?_⟩
        have h1 : (⟨x, hxV⟩ : V) ^ p = 1 := by rw [← hxord, pow_orderOf_eq_one]
        exact congrArg Subtype.val h1
      rw [hbot, Subgroup.mem_bot] at hxVp
      have hx1 : (⟨x, hxV⟩ : V) = 1 := Subtype.ext hxVp
      rw [hx1, orderOf_one] at hxord
      exact hp_prime.ne_one hxord.symm
    have hVp_eq : Vp = V := hVmin Vp hVp_norm hVp_ne hVp_le
    intro v hv
    rw [← hVp_eq] at hv
    exact hv.2
  -- |V| is a power of p, hence coprime to V.index = |G/V|
  have hV_pgroup : IsPGroup p V := by
    intro ⟨v, hv⟩
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simpa using hVpow v hv
  have hcop_V_idx : (Nat.card V).Coprime V.index := by
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne
    obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd hne
    have hqV : q ∣ Nat.card V := dvd_trans hq_dvd (Nat.gcd_dvd_left _ _)
    have hqI : q ∣ Nat.card (G ⧸ V) := dvd_trans hq_dvd (Nat.gcd_dvd_right _ _)
    obtain ⟨k, hk⟩ := hV_pgroup.exists_card_eq
    rw [hk] at hqV
    have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hq_prime hp_prime).mp
      (hq_prime.dvd_of_dvd_pow hqV)
    exact hp_not235 (hGV_235 p hp_prime (hqp ▸ hqI))
  -- Schur-Zassenhaus: complement H of V in G
  obtain ⟨H, hVH⟩ := Subgroup.exists_right_complement'_of_coprime hcop_V_idx
  -- H ≃* G ⧸ V
  have hH_equiv : Nonempty (H ≃* (G ⧸ V)) := by
    let f : H →* G ⧸ V := (QuotientGroup.mk' V).comp H.subtype
    have hf_inj : Function.Injective f := by
      rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
      intro ⟨h, hh⟩ hmem
      change QuotientGroup.mk h = 1 at hmem
      rw [QuotientGroup.eq_one_iff] at hmem
      have hdisj : V ⊓ H = ⊥ := hVH.disjoint.eq_bot
      have hbot : h ∈ (⊥ : Subgroup G) := hdisj ▸ ⟨hmem, hh⟩
      exact Subtype.ext (Subgroup.mem_bot.mp hbot)
    have hf_surj : Function.Surjective f := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H g =>
        obtain ⟨⟨⟨v, hv⟩, ⟨h, hh⟩⟩, hgh⟩ := hVH.2 g
        change v * h = g at hgh
        refine ⟨⟨h, hh⟩, ?_⟩
        change QuotientGroup.mk h = QuotientGroup.mk g
        rw [← hgh, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff v).mpr hv, one_mul]
    exact ⟨MulEquiv.ofBijective f ⟨hf_inj, hf_surj⟩⟩
  obtain ⟨eH⟩ := hH_equiv
  have hH_card : Nat.card H = Nat.card (G ⧸ V) := Nat.card_congr eH.toEquiv
  have hH_235 : ∀ q : ℕ, q.Prime → q ∣ Nat.card H → q = 2 ∨ q = 3 ∨ q = 5 := by
    intro q hq hqdvd
    exact hGV_235 q hq (hH_card ▸ hqdvd)
  have hH_rat : ∀ (x : H) (n : ℕ), (Nat.card H).Coprime n → IsConj x (x ^ n) :=
    rational_of_mulEquiv eH.symm (rational_quotient hratG V)
  -- Conjugation action of H on V is faithful
  have hH_faith : ∀ h : H, (∀ v ∈ V, (h : G) * v * (h : G)⁻¹ = v) → h = 1 := by
    let K : Subgroup G :=
      { carrier := {h ∈ H | ∀ v ∈ V, h * v * h⁻¹ = v}
        mul_mem' := fun {a b} ha hb => ⟨H.mul_mem ha.1 hb.1, fun v hv => by
          calc a * b * v * (a * b)⁻¹ = a * (b * v * b⁻¹) * a⁻¹ := by group
            _ = a * v * a⁻¹ := by rw [hb.2 v hv]
            _ = v := ha.2 v hv⟩
        one_mem' := ⟨H.one_mem, fun v _ => by group⟩
        inv_mem' := fun {a} ha => ⟨H.inv_mem ha.1, fun v hv => by
          have h1 := ha.2 v hv
          calc a⁻¹ * v * (a⁻¹)⁻¹ = a⁻¹ * (a * v * a⁻¹) * a := by rw [h1, inv_inv]
            _ = v := by group⟩ }
    have hK_le_H : K ≤ H := fun x hx => hx.1
    have hK_norm : K.Normal := ⟨fun k hk g => by
      obtain ⟨⟨⟨v, hv⟩, ⟨h, hh⟩⟩, hgh⟩ := hVH.2 g
      change v * h = g at hgh
      rw [← hgh]
      have hhk_comm : ∀ u ∈ V, (h * k * h⁻¹) * u * (h * k * h⁻¹)⁻¹ = u := by
        intro u hu
        have hu' : h⁻¹ * u * h ∈ V := by
          simpa [inv_inv] using hVnorm.conj_mem u hu h⁻¹
        calc (h * k * h⁻¹) * u * (h * k * h⁻¹)⁻¹
            = h * (k * (h⁻¹ * u * h) * k⁻¹) * h⁻¹ := by group
          _ = h * (h⁻¹ * u * h) * h⁻¹ := by rw [hk.2 _ hu']
          _ = u := by group
      have hconj : (v * h) * k * (v * h)⁻¹ = h * k * h⁻¹ := by
        have h1 := hhk_comm v hv
        have h1' : v * (h * k * h⁻¹) = (h * k * h⁻¹) * v := by
          calc v * (h * k * h⁻¹) = ((h * k * h⁻¹) * v * (h * k * h⁻¹)⁻¹) * (h * k * h⁻¹) := by
                rw [h1]
            _ = (h * k * h⁻¹) * v := by group
        calc (v * h) * k * (v * h)⁻¹ = (v * (h * k * h⁻¹)) * v⁻¹ := by group
          _ = ((h * k * h⁻¹) * v) * v⁻¹ := by rw [h1']
          _ = h * k * h⁻¹ := by group
      rw [hconj]
      exact ⟨H.mul_mem (H.mul_mem hh hk.1) (H.inv_mem hh), hhk_comm⟩⟩
    have hK_bot : K = ⊥ := by
      by_contra hKne
      have hGK_lt : Nat.card (G ⧸ K) < Nat.card G := by
        have hlag := Subgroup.card_mul_index K
        have hKgt : 1 < Nat.card K := by
          rw [Nat.one_lt_iff_ne_zero_and_ne_one]
          refine ⟨Nat.card_pos.ne', ?_⟩
          intro h1
          apply hKne
          rw [Subgroup.eq_bot_iff_forall]
          intro x hx
          have _hsub : Subsingleton K := (Nat.card_eq_one_iff_unique.mp h1).1
          exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : K) 1)
        change K.index < Nat.card G
        have hidx_pos : 0 < K.index := Nat.card_pos
        nlinarith
      have hVK_disj : V ⊓ K = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        intro x ⟨hxV, hxK⟩
        have hbot : x ∈ (⊥ : Subgroup G) := hVH.disjoint.eq_bot ▸ ⟨hxV, hK_le_H hxK⟩
        exact Subgroup.mem_bot.mp hbot
      have hV_dvd_GK : Nat.card V ∣ Nat.card (G ⧸ K) := by
        let φ : V →* G ⧸ K := (QuotientGroup.mk' K).comp V.subtype
        have hφ_inj : Function.Injective φ := by
          rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
          intro ⟨v, hv⟩ hmem
          change QuotientGroup.mk v = 1 at hmem
          rw [QuotientGroup.eq_one_iff] at hmem
          have hbot : v ∈ (⊥ : Subgroup G) := hVK_disj ▸ ⟨hv, hmem⟩
          exact Subtype.ext (Subgroup.mem_bot.mp hbot)
        have hcard_range : Nat.card φ.range = Nat.card V :=
          Nat.card_congr (Equiv.ofBijective φ.rangeRestrict
            ⟨fun a b h => hφ_inj (congrArg Subtype.val h), φ.rangeRestrict_surjective⟩).symm
        rw [← hcard_range]
        exact Subgroup.card_subgroup_dvd_card φ.range
      exact hp_not235 (hminG (G ⧸ K) hGK_lt (rational_quotient hratG K) p hp_prime
        (dvd_trans hp_dvd_V hV_dvd_GK))
    intro ⟨h, hh⟩ hcomm
    have hmem : h ∈ K := ⟨hh, hcomm⟩
    rw [hK_bot, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  -- Identify V with (Fin d → ZMod p) via helper (cleanly avoiding AddCommGroup diamonds)
  let hV_commGroup : CommGroup V :=
    { (inferInstance : Group V) with
      mul_comm := fun a b => Subtype.ext (hVcomm a.1 a.2 b.1 b.2) }
  have hV_nt : Nontrivial V := by
    rw [nontrivial_iff]
    have hne : ∃ v ∈ V, v ≠ 1 := by
      by_contra hall
      push Not at hall
      exact hVne ((Subgroup.eq_bot_iff_forall V).mpr hall)
    obtain ⟨v, hv, hv1⟩ := hne
    exact ⟨⟨v, hv⟩, 1, fun h => hv1 (congrArg Subtype.val h)⟩
  obtain ⟨d, hd_pos, eV, heV1, heVmul, heVpow⟩ :=
    @exists_zmod_equiv_of_commGroup V hV_commGroup inferInstance p _hp_fact
      (fun x => Subtype.ext (hVpow x.1 x.2)) hV_nt
  have heVinv : ∀ x : V, eV x⁻¹ = -(eV x) := fun x =>
    eq_neg_of_add_eq_zero_left (by rw [← heVmul, inv_mul_cancel, heV1])
  -- Construct ρ : H →* ((Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p))
  let ρ : H →* ((Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)) :=
    { toFun := fun h =>
        let f : (Fin d → ZMod p) →+ (Fin d → ZMod p) :=
          { toFun := fun v => eV ⟨(h : G) * (eV.symm v : G) * (h : G)⁻¹,
              hVnorm.conj_mem _ (eV.symm v).2 h⟩
            map_zero' := by
              have h0 : eV.symm 0 = 1 := eV.injective (by simp [heV1])
              have h1 : (⟨(h : G) * (eV.symm 0 : G) * (h : G)⁻¹,
                  hVnorm.conj_mem _ (eV.symm 0).2 h⟩ : V) = 1 := by
                apply Subtype.ext; rw [h0]; change (h : G) * 1 * (h : G)⁻¹ = 1; group
              rw [h1, heV1]
            map_add' := fun u v => by
              have hadd : eV.symm (u + v) = eV.symm u * eV.symm v :=
                eV.injective (by rw [heVmul, eV.apply_symm_apply, eV.apply_symm_apply,
                  eV.apply_symm_apply])
              have h1 : (⟨(h : G) * (eV.symm (u + v) : G) * (h : G)⁻¹,
                  hVnorm.conj_mem _ (eV.symm (u + v)).2 h⟩ : V) =
                ⟨(h : G) * (eV.symm u : G) * (h : G)⁻¹, hVnorm.conj_mem _ (eV.symm u).2 h⟩ *
                ⟨(h : G) * (eV.symm v : G) * (h : G)⁻¹, hVnorm.conj_mem _ (eV.symm v).2 h⟩ := by
                apply Subtype.ext; rw [hadd]; simp only [Subgroup.coe_mul]; group
              rw [h1, heVmul] }
        let g : (Fin d → ZMod p) →+ (Fin d → ZMod p) :=
          { toFun := fun v => eV ⟨(h : G)⁻¹ * (eV.symm v : G) * ((h : G)⁻¹)⁻¹,
              hVnorm.conj_mem _ (eV.symm v).2 (h : G)⁻¹⟩
            map_zero' := by
              have h0 : eV.symm 0 = 1 := eV.injective (by simp [heV1])
              have h1 : (⟨(h : G)⁻¹ * (eV.symm 0 : G) * ((h : G)⁻¹)⁻¹,
                  hVnorm.conj_mem _ (eV.symm 0).2 (h : G)⁻¹⟩ : V) = 1 := by
                apply Subtype.ext; rw [h0]; change (h : G)⁻¹ * 1 * ((h : G)⁻¹)⁻¹ = 1; group
              rw [h1, heV1]
            map_add' := fun u v => by
              have hadd : eV.symm (u + v) = eV.symm u * eV.symm v :=
                eV.injective (by rw [heVmul, eV.apply_symm_apply, eV.apply_symm_apply,
                  eV.apply_symm_apply])
              have h1 : (⟨(h : G)⁻¹ * (eV.symm (u + v) : G) * ((h : G)⁻¹)⁻¹,
                  hVnorm.conj_mem _ (eV.symm (u + v)).2 (h : G)⁻¹⟩ : V) =
                ⟨(h : G)⁻¹ * (eV.symm u : G) * ((h : G)⁻¹)⁻¹,
                  hVnorm.conj_mem _ (eV.symm u).2 (h : G)⁻¹⟩ *
                ⟨(h : G)⁻¹ * (eV.symm v : G) * ((h : G)⁻¹)⁻¹,
                  hVnorm.conj_mem _ (eV.symm v).2 (h : G)⁻¹⟩ := by
                apply Subtype.ext; rw [hadd]; simp only [Subgroup.coe_mul]; group
              rw [h1, heVmul] }
        LinearEquiv.ofLinearMap (f.toZModLinearMap p) (g.toZModLinearMap p)
          (LinearMap.ext fun v => by
            change eV ⟨(h : G) * (eV.symm (g v) : G) * (h : G)⁻¹,
                hVnorm.conj_mem _ (eV.symm (g v)).2 h⟩ = v
            have hgv : (eV.symm (g v) : G) = (h : G)⁻¹ * (eV.symm v : G) * ((h : G)⁻¹)⁻¹ :=
              congrArg Subtype.val (eV.symm_apply_apply
                (⟨(h : G)⁻¹ * (eV.symm v : G) * ((h : G)⁻¹)⁻¹,
                  hVnorm.conj_mem _ (eV.symm v).2 (h : G)⁻¹⟩ : V))
            have h1 : (⟨(h : G) * (eV.symm (g v) : G) * (h : G)⁻¹,
                hVnorm.conj_mem _ (eV.symm (g v)).2 h⟩ : V) = eV.symm v := by
              apply Subtype.ext
              change (h : G) * (eV.symm (g v) : G) * (h : G)⁻¹ = (eV.symm v : G)
              rw [hgv]; group
            exact (congrArg eV h1).trans (eV.apply_symm_apply v))
          (LinearMap.ext fun v => by
            change eV ⟨(h : G)⁻¹ * (eV.symm (f v) : G) * ((h : G)⁻¹)⁻¹,
                hVnorm.conj_mem _ (eV.symm (f v)).2 (h : G)⁻¹⟩ = v
            have hfv : (eV.symm (f v) : G) = (h : G) * (eV.symm v : G) * (h : G)⁻¹ :=
              congrArg Subtype.val (eV.symm_apply_apply
                (⟨(h : G) * (eV.symm v : G) * (h : G)⁻¹,
                  hVnorm.conj_mem _ (eV.symm v).2 h⟩ : V))
            have h1 : (⟨(h : G)⁻¹ * (eV.symm (f v) : G) * ((h : G)⁻¹)⁻¹,
                hVnorm.conj_mem _ (eV.symm (f v)).2 (h : G)⁻¹⟩ : V) = eV.symm v := by
              apply Subtype.ext
              change (h : G)⁻¹ * (eV.symm (f v) : G) * ((h : G)⁻¹)⁻¹ = (eV.symm v : G)
              rw [hfv]; group
            exact (congrArg eV h1).trans (eV.apply_symm_apply v))
      map_one' := LinearEquiv.ext fun v => by
        change eV ⟨((1 : H) : G) * (eV.symm v : G) * ((1 : H) : G)⁻¹, _⟩ = v
        have h1 : (⟨((1 : H) : G) * (eV.symm v : G) * ((1 : H) : G)⁻¹,
            hVnorm.conj_mem _ (eV.symm v).2 (1 : H)⟩ : V) = eV.symm v := by
          apply Subtype.ext; simp
        rw [h1, eV.apply_symm_apply]
      map_mul' := fun h₁ h₂ => LinearEquiv.ext fun v => by
        change eV ⟨((h₁ : G) * (h₂ : G)) * (eV.symm v : G) * ((h₁ : G) * (h₂ : G))⁻¹, _⟩ =
          eV ⟨(h₁ : G) * (eV.symm (eV ⟨(h₂ : G) * (eV.symm v : G) * (h₂ : G)⁻¹, _⟩) : G) *
            (h₁ : G)⁻¹, _⟩
        congr 1
        apply Subtype.ext
        change ((h₁ : G) * (h₂ : G)) * (eV.symm v : G) * ((h₁ : G) * (h₂ : G))⁻¹ =
          (h₁ : G) * (eV.symm (eV ⟨(h₂ : G) * (eV.symm v : G) * (h₂ : G)⁻¹,
            hVnorm.conj_mem _ (eV.symm v).2 h₂⟩) : G) * (h₁ : G)⁻¹
        have h2 : (eV.symm (eV ⟨(h₂ : G) * (eV.symm v : G) * (h₂ : G)⁻¹,
            hVnorm.conj_mem _ (eV.symm v).2 h₂⟩) : G) =
            (h₂ : G) * (eV.symm v : G) * (h₂ : G)⁻¹ :=
          congrArg Subtype.val (eV.symm_apply_apply
            (⟨(h₂ : G) * (eV.symm v : G) * (h₂ : G)⁻¹, hVnorm.conj_mem _ (eV.symm v).2 h₂⟩ : V))
        rw [h2]; group }
  have hρ_apply : ∀ (h : H) (x : V),
      ρ h (eV x) = eV ⟨(h : G) * (x : G) * (h : G)⁻¹, hVnorm.conj_mem x.1 x.2 h⟩ := fun h x => by
    change eV ⟨(h : G) * (eV.symm (eV x) : G) * (h : G)⁻¹, _⟩ = _
    congr 1; apply Subtype.ext; rw [eV.symm_apply_apply]
  -- Prove faithfulness of ρ
  have hρ_inj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro h hh
    apply hH_faith h
    intro v hv
    have heq : ρ h (eV ⟨v, hv⟩) = eV ⟨v, hv⟩ := by
      have h1 : ρ h = 1 := hh
      rw [h1]; rfl
    rw [hρ_apply] at heq
    exact congrArg Subtype.val (eV.injective heq)
  -- Prove irreducibility of ρ
  have hρ_irred : ∀ W : Submodule (ZMod p) (Fin d → ZMod p),
      (∀ h : H, ∀ v ∈ W, ρ h v ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    let W' : Subgroup G :=
      { carrier := {x : G | ∃ hx : x ∈ V, eV ⟨x, hx⟩ ∈ W}
        mul_mem' := fun {a b} ⟨ha, haW⟩ ⟨hb, hbW⟩ => by
          refine ⟨V.mul_mem ha hb, ?_⟩
          have h1 : (⟨a * b, V.mul_mem ha hb⟩ : V) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
          rw [h1, heVmul]
          exact W.add_mem haW hbW
        one_mem' := ⟨V.one_mem, by
          have h1 : (⟨1, V.one_mem⟩ : V) = 1 := rfl
          rw [h1, heV1]; exact W.zero_mem⟩
        inv_mem' := fun {a} ⟨ha, haW⟩ => by
          refine ⟨V.inv_mem ha, ?_⟩
          have h1 : (⟨a⁻¹, V.inv_mem ha⟩ : V) = (⟨a, ha⟩ : V)⁻¹ := rfl
          rw [h1, heVinv]
          exact W.neg_mem haW }
    have hW'_le : W' ≤ V := fun x hx => hx.1
    have hW'_norm : W'.Normal := by
      constructor
      intro x hx g
      obtain ⟨hxV, hxW⟩ := hx
      obtain ⟨⟨⟨v, hv⟩, ⟨h, hh⟩⟩, hgh⟩ := hVH.2 g
      change v * h = g at hgh
      rw [← hgh]
      have hconj : (v * h) * x * (v * h)⁻¹ = h * x * h⁻¹ := by
        have hx' : h * x * h⁻¹ ∈ V := hVnorm.conj_mem x hxV h
        calc (v * h) * x * (v * h)⁻¹ = v * (h * x * h⁻¹) * v⁻¹ := by group
          _ = (h * x * h⁻¹) * v * v⁻¹ := by rw [hVcomm v hv _ hx']
          _ = h * x * h⁻¹ := by group
      rw [hconj]
      refine ⟨hVnorm.conj_mem x hxV h, ?_⟩
      have hact := hW ⟨h, hh⟩ (eV ⟨x, hxV⟩) hxW
      rwa [hρ_apply] at hact
    by_cases hW'_bot : W' = ⊥
    · left
      rw [Submodule.eq_bot_iff]
      intro v hv
      have hxW' : (eV.symm v : G) ∈ W' := ⟨(eV.symm v).2, by simpa using hv⟩
      rw [hW'_bot, Subgroup.mem_bot] at hxW'
      have hx1 : eV.symm v = 1 := Subtype.ext hxW'
      calc v = eV (eV.symm v) := (eV.apply_symm_apply v).symm
        _ = eV 1 := by rw [hx1]
        _ = 0 := heV1
    · right
      have hW'_eq : W' = V := hVmin W' hW'_norm hW'_bot hW'_le
      rw [Submodule.eq_top_iff']
      intro v
      have hxW' : (eV.symm v : G) ∈ W' := by rw [hW'_eq]; exact (eV.symm v).2
      obtain ⟨hxV, hxW⟩ := hxW'
      have heq : (⟨(eV.symm v : G), hxV⟩ : V) = eV.symm v := rfl
      rw [heq, eV.apply_symm_apply] at hxW
      exact hxW
  -- Prove the Joint Scaling Condition
  have hjoint : ∀ (v : Fin d → ZMod p), v ≠ 0 → ∀ (y : H), ρ y v = v →
      ∀ (c : (ZMod p)ˣ) (n : ℕ), (Nat.card {h : H // ρ h v = v}).Coprime n →
        ∃ h : H, ρ h v = (c : ZMod p) • v ∧ h * y * h⁻¹ = y ^ n := by
    intro v hv0 y hy c n hn
    let x : V := eV.symm v
    have hxv : eV x = v := eV.apply_symm_apply v
    have hx_ne1 : (x : G) ≠ 1 := by
      intro h1
      apply hv0
      rw [← hxv, show x = 1 from Subtype.ext h1, heV1]
    have hx_ord : orderOf (x : G) = p := by
      have hp1 : (x : G) ^ p = 1 := hVpow x.1 x.2
      have hdvd : orderOf (x : G) ∣ p := orderOf_dvd_of_pow_eq_one hp1
      rcases (Nat.dvd_prime hp_prime).mp hdvd with h1 | hp'
      · exact absurd (orderOf_eq_one_iff.mp h1) hx_ne1
      · exact hp'
    -- x and y commute in G
    have hxy_comm : (x : G) * (y : G) = (y : G) * (x : G) := by
      rw [← hxv, hρ_apply] at hy
      have hconj : (y : G) * (x : G) * (y : G)⁻¹ = (x : G) :=
        congrArg Subtype.val (eV.injective hy)
      calc (x : G) * (y : G) = ((y : G) * (x : G) * (y : G)⁻¹) * (y : G) := by rw [hconj]
        _ = (y : G) * (x : G) := by group
    -- Subgroup C_H(v) has order dividing |H|
    let Cv : Subgroup H :=
      { carrier := {h : H | ρ h v = v}
        mul_mem' := fun {a b} ha hb => by
          change ρ (a * b) v = v
          rw [map_mul]
          exact (congrArg (ρ a) hb).trans ha
        one_mem' := by simp
        inv_mem' := fun {a} ha => by
          have : ρ a⁻¹ (ρ a v) = ρ a⁻¹ v := congrArg (ρ a⁻¹) ha
          simpa [← map_mul] using this.symm }
    have hCv_card : Nat.card Cv = Nat.card {h : H // ρ h v = v} := rfl
    have hy_mem : y ∈ Cv := hy
    have hCv_dvd_H : Nat.card Cv ∣ Nat.card H := Subgroup.card_subgroup_dvd_card Cv
    have hp_cop_H : p.Coprime (Nat.card H) := by
      rw [Nat.Prime.coprime_iff_not_dvd hp_prime]
      intro hdvd
      exact hp_not235 (hH_235 p hp_prime hdvd)
    have hp_cop_Cv : p.Coprime (Nat.card Cv) := hp_cop_H.coprime_dvd_right hCv_dvd_H
    have hp_cop_c : p.Coprime (c : ZMod p).val := by
      rw [Nat.Prime.coprime_iff_not_dvd hp_prime]
      intro hdvd
      have h0 : ((c : ZMod p).val : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
      rw [ZMod.natCast_zmod_val] at h0
      exact Units.ne_zero c h0
    -- Lift (c.val, n) modulo (p, |Cv|) to m coprime to |G|
    obtain ⟨m, hmp, hmCv, hmG⟩ := coprime_lift_two (N := Nat.card G) Nat.card_pos.ne'
      hp_cop_Cv hp_cop_c (hCv_card ▸ hn)
    have hxm : (x : G) ^ m = (x : G) ^ (c : ZMod p).val := by
      rw [← pow_mod_orderOf, ← pow_mod_orderOf (n := (c : ZMod p).val), hx_ord]
      exact congrArg ((x : G) ^ ·) hmp
    have hym : y ^ m = y ^ n := by
      have hy_ord : orderOf (⟨y, hy_mem⟩ : Cv) ∣ Nat.card Cv := orderOf_dvd_natCard _
      have hm' : m ≡ n [MOD orderOf (⟨y, hy_mem⟩ : Cv)] := hmCv.of_dvd hy_ord
      have h1 : (⟨y, hy_mem⟩ : Cv) ^ m = (⟨y, hy_mem⟩ : Cv) ^ n := by
        rw [← pow_mod_orderOf, ← pow_mod_orderOf (n := n)]
        exact congrArg ((⟨y, hy_mem⟩ : Cv) ^ ·) hm'
      exact congrArg Subtype.val h1
    have hxym : ((x : G) * (y : G)) ^ m = (x : G) ^ (c : ZMod p).val * (y : G) ^ n := by
      have hcomm : Commute (x : G) (y : G) := hxy_comm
      rw [hcomm.mul_pow, hxm]
      congr 1
      exact congrArg Subtype.val hym
    -- Apply rationality of G to x * y with exponent m
    obtain ⟨g, hg⟩ := isConj_iff.mp (hratG ((x : G) * (y : G)) m hmG)
    rw [hxym] at hg
    -- Raise to orderOf y to isolate x
    have hy_ord_cop : p.Coprime (orderOf (y : G)) := by
      have hdvd : orderOf (y : G) ∣ Nat.card H := by
        rw [Subgroup.orderOf_coe]
        exact orderOf_dvd_natCard y
      exact hp_cop_H.coprime_dvd_right hdvd
    have hpow_oy : g * ((x : G) ^ orderOf (y : G)) * g⁻¹ =
        ((x : G) ^ (c : ZMod p).val) ^ orderOf (y : G) := by
      have hcomm : Commute (x : G) (y : G) := hxy_comm
      have hcomm_n : Commute ((x : G) ^ (c : ZMod p).val) ((y : G) ^ n) :=
        hcomm.pow_pow _ _
      have hy_pow1 : ((y : G) ^ n) ^ orderOf (y : G) = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
      calc g * ((x : G) ^ orderOf (y : G)) * g⁻¹
          = g * (((x : G) * (y : G)) ^ orderOf (y : G)) * g⁻¹ := by
              rw [hcomm.mul_pow, pow_orderOf_eq_one, mul_one]
        _ = (g * ((x : G) * (y : G)) * g⁻¹) ^ orderOf (y : G) := by rw [conj_pow]
        _ = ((x : G) ^ (c : ZMod p).val * (y : G) ^ n) ^ orderOf (y : G) := by rw [hg]
        _ = ((x : G) ^ (c : ZMod p).val) ^ orderOf (y : G) *
              ((y : G) ^ n) ^ orderOf (y : G) := hcomm_n.mul_pow _
        _ = ((x : G) ^ (c : ZMod p).val) ^ orderOf (y : G) := by rw [hy_pow1, mul_one]
    -- Invert orderOf y modulo p to recover g * x * g⁻¹ = x ^ c.val
    let a := (orderOf (y : G) : ZMod p)⁻¹.val
    have ha_mod : orderOf (y : G) * a ≡ 1 [MOD p] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      push_cast
      rw [ZMod.natCast_zmod_val]
      have hne0 : (orderOf (y : G) : ZMod p) ≠ 0 := by
        intro h0
        have hdvd : p ∣ orderOf (y : G) := (ZMod.natCast_eq_zero_iff _ _).mp h0
        exact hp_prime.not_dvd_one (hy_ord_cop ▸ Nat.dvd_gcd dvd_rfl hdvd)
      exact mul_inv_cancel₀ hne0
    have hgx : g * (x : G) * g⁻¹ = (x : G) ^ (c : ZMod p).val := by
      have h1 : (g * ((x : G) ^ orderOf (y : G)) * g⁻¹) ^ a =
          (((x : G) ^ (c : ZMod p).val) ^ orderOf (y : G)) ^ a := congrArg (· ^ a) hpow_oy
      rw [conj_pow, ← pow_mul, ← pow_mul] at h1
      have hx1 : (x : G) ^ (orderOf (y : G) * a) = (x : G) := by
        rw [← pow_mod_orderOf, hx_ord, show orderOf (y : G) * a % p = 1 % p from ha_mod,
          ← hx_ord, pow_mod_orderOf, pow_one]
      have hx2 : ((x : G) ^ (c : ZMod p).val) ^ (orderOf (y : G) * a) =
          (x : G) ^ (c : ZMod p).val := by
        rw [← pow_mul, mul_comm (c : ZMod p).val, pow_mul, hx1]
      rw [hx1, hx2] at h1
      exact h1
    -- Split g = u * h with u ∈ V, h ∈ H
    obtain ⟨⟨⟨u, hu⟩, h⟩, hgh⟩ := hVH.2 g
    change u * (h : G) = g at hgh
    rw [← hgh] at hgx hg
    refine ⟨h, ?_, ?_⟩
    · -- ρ h v = c • v
      have hhx : (h : G) * (x : G) * (h : G)⁻¹ = (x : G) ^ (c : ZMod p).val := by
        calc (h : G) * (x : G) * (h : G)⁻¹
            = u⁻¹ * ((u * (h : G)) * (x : G) * (u * (h : G))⁻¹) * u := by group
          _ = u⁻¹ * ((x : G) ^ (c : ZMod p).val) * u := by rw [hgx]
          _ = u⁻¹ * (u * (x : G) ^ (c : ZMod p).val) := by
                rw [mul_assoc, hVcomm _ (V.pow_mem x.2 _) u hu]
          _ = (x : G) ^ (c : ZMod p).val := by group
      have hconj : (⟨(h : G) * (x : G) * (h : G)⁻¹, hVnorm.conj_mem x.1 x.2 h⟩ : V) =
          x ^ (c : ZMod p).val := Subtype.ext hhx
      calc ρ h v = ρ h (eV x) := by rw [hxv]
        _ = eV ⟨(h : G) * (x : G) * (h : G)⁻¹, hVnorm.conj_mem x.1 x.2 h⟩ := hρ_apply h x
        _ = eV (x ^ (c : ZMod p).val) := by rw [hconj]
        _ = ((c : ZMod p).val : ZMod p) • eV x := heVpow x _
        _ = (c : ZMod p) • v := by rw [ZMod.natCast_zmod_val, hxv]
    · -- h * y * h⁻¹ = y ^ n via projection modulo V
      have hmodV : QuotientGroup.mk' V ((h : G) * (y : G) * (h : G)⁻¹) =
          QuotientGroup.mk' V ((y : G) ^ n) := by
        have h1 := congrArg (QuotientGroup.mk' V) hg
        have hu1 : QuotientGroup.mk' V u = 1 := (QuotientGroup.eq_one_iff u).mpr hu
        have hx1 : QuotientGroup.mk' V (x : G) = 1 := (QuotientGroup.eq_one_iff (x : G)).mpr x.2
        simp only [map_mul, map_inv, map_pow, hu1, hx1, one_mul, one_pow] at h1
        exact h1
      have hdiff : ((h : G) * (y : G) * (h : G)⁻¹) * ((y : G) ^ n)⁻¹ ∈ V := by
        have h1 : QuotientGroup.mk' V (((h : G) * (y : G) * (h : G)⁻¹) * ((y : G) ^ n)⁻¹) = 1 := by
          rw [map_mul, map_inv, hmodV, mul_inv_cancel]
        exact (QuotientGroup.eq_one_iff _).mp h1
      have hdiffH : ((h : G) * (y : G) * (h : G)⁻¹) * ((y : G) ^ n)⁻¹ ∈ H :=
        H.mul_mem (H.mul_mem (H.mul_mem h.2 y.2) (H.inv_mem h.2)) (H.inv_mem (H.pow_mem y.2 n))
      have hbot : ((h : G) * (y : G) * (h : G)⁻¹) * ((y : G) ^ n)⁻¹ ∈ (⊥ : Subgroup G) :=
        hVH.disjoint.eq_bot ▸ ⟨hdiff, hdiffH⟩
      rw [Subgroup.mem_bot, mul_inv_eq_one] at hbot
      exact Subtype.ext (by simpa using hbot)
  exact ⟨p, ⟨hp_prime⟩, hp7, d, hd_pos, H, inferInstance, inferInstance, inferInstance,
    hH_235, hH_rat, ρ, hρ_inj, hρ_irred, hjoint⟩

/- ### Component 3: Maschke Semisimplicity and Super-Lemma 1 (`O_q(H) = 1` for prime `q ≥ 5`) -/

lemma no_normal_prime_subgroup_of_ge_five {R : Type*} [Group R] [Fintype R]
    (hrat : ∀ (x : R) (n : ℕ), (Nat.card R).Coprime n → IsConj x (x ^ n))
    (q : ℕ) (hq : q.Prime) (hq5 : 5 ≤ q)
    (L : Subgroup R) (hLnorm : L.Normal) (hLcard : Nat.card L = q) : False := by
  classical
  have _hq_fact : Fact q.Prime := ⟨hq⟩
  obtain ⟨⟨x, hxL⟩, hxord⟩ := exists_prime_orderOf_dvd_card' (G := L) q (hLcard ▸ dvd_rfl)
  have hxordR : orderOf x = q := (Subgroup.orderOf_coe (⟨x, hxL⟩ : L)).trans hxord
  -- L is generated by x (since |zpowers x| = q = |L|)
  have hzpow : Subgroup.zpowers x = L := by
    have hle : Subgroup.zpowers x ≤ L := Subgroup.zpowers_le.mpr hxL
    have hcard_eq : Nat.card (Subgroup.zpowers x) = Nat.card L := by
      rw [Nat.card_zpowers, hxordR, hLcard]
    exact Subgroup.eq_of_le_of_card_ge hle hcard_eq.ge
  -- Every g ∈ R conjugates x to x ^ k for a unique k : ZMod q
  have hconj_ex : ∀ g : R, ∃ k : ZMod q, g * x * g⁻¹ = x ^ k.val := by
    intro g
    have hmem : g * x * g⁻¹ ∈ Subgroup.zpowers x := hzpow ▸ hLnorm.conj_mem x hxL g
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine ⟨(m : ZMod q), ?_⟩
    rw [← hm, ← zpow_natCast]
    have hdvd : (orderOf x : ℤ) ∣ ((m : ZMod q).val : ℤ) - m := by
      rw [hxordR, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
      simp
    obtain ⟨t, ht⟩ := hdvd
    have hmeq : ((m : ZMod q).val : ℤ) = m + (orderOf x : ℤ) * t := by linarith
    rw [hmeq, zpow_add, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow, mul_one]
  -- Uniqueness of k : ZMod q
  have hpow_inj : ∀ a b : ZMod q, x ^ a.val = x ^ b.val → a = b := by
    intro a b hab
    have hmod : a.val ≡ b.val [MOD orderOf x] := pow_eq_pow_iff_modEq.mp hab
    rw [hxordR] at hmod
    have hcast : (a.val : ZMod q) = (b.val : ZMod q) := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
    simpa using hcast
  -- Choose α : R → ZMod q such that g * x * g⁻¹ = x ^ (α g).val
  choose α hα using hconj_ex
  have hα_mul : ∀ g₁ g₂ : R, α (g₁ * g₂) = α g₁ * α g₂ := by
    intro g₁ g₂
    apply hpow_inj
    have h1 : (g₁ * g₂) * x * (g₁ * g₂)⁻¹ = g₁ * (g₂ * x * g₂⁻¹) * g₁⁻¹ := by group
    rw [hα (g₁ * g₂), hα g₂, ← conj_pow, hα g₁, ← pow_mul] at h1
    have h2 : x ^ ((α g₁ * α g₂).val) = x ^ ((α g₁).val * (α g₂).val) := by
      rw [← pow_mod_orderOf, ← pow_mod_orderOf (n := (α g₁).val * (α g₂).val), hxordR]
      congr 1
      rw [ZMod.val_mul]
      exact Nat.mod_mod _ _
    exact h1.trans h2.symm
  -- Find g with g * x * g⁻¹ = x ^ 2, so α g = 2
  have hcop2 : (orderOf x).Coprime 2 := by
    rw [hxordR, Nat.Prime.coprime_iff_not_dvd hq]
    intro hdvd
    have hle := Nat.le_of_dvd (by decide) hdvd
    omega
  obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_pow_of_coprime_orderOf hrat x hcop2)
  have hαg : α g = (2 : ZMod q) := by
    apply hpow_inj
    rw [← hα g, hg]
    have h2lt : 2 < q := by omega
    rw [ZMod.val_ofNat_of_lt h2lt]
  -- Find h with h * g * h⁻¹ = g ^ (|R| - 1) = g⁻¹
  have hR_pos : 0 < Nat.card R := Nat.card_pos
  have hcop_sub : (Nat.card R).Coprime (Nat.card R - 1) := by
    cases hR : Nat.card R with
    | zero => omega
    | succ k =>
      change Nat.gcd (k + 1) k = 1
      rw [Nat.gcd_comm, Nat.gcd_rec]
      simp
  obtain ⟨h, hh⟩ := isConj_iff.mp (hrat g (Nat.card R - 1) hcop_sub)
  have hg_inv : g ^ (Nat.card R - 1) = g⁻¹ := by
    have hpow : g ^ Nat.card R = 1 := by rw [Nat.card_eq_fintype_card]; exact pow_card_eq_one
    have h1 : g ^ (Nat.card R - 1) * g = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel hR_pos, hpow]
    exact eq_inv_of_mul_eq_one_left h1
  rw [hg_inv] at hh
  -- Apply α to h * g * h⁻¹ = g⁻¹
  have hα1 : α 1 = 1 := by
    apply hpow_inj
    rw [← hα 1, ZMod.val_one]
    group
  have hα_comm : α (h * g * h⁻¹) = α g := by
    have hinv : α h * α h⁻¹ = 1 := by rw [← hα_mul, mul_inv_cancel, hα1]
    rw [hα_mul, hα_mul, mul_comm (α h) (α g), mul_assoc, hinv, mul_one]
  have hα_sq : α g * α g = 1 := by
    calc α g * α g = α (h * g * h⁻¹) * α g := by rw [hα_comm]
      _ = α g⁻¹ * α g := by rw [hh]
      _ = α (g⁻¹ * g) := (hα_mul _ _).symm
      _ = 1 := by rw [inv_mul_cancel, hα1]
  rw [hαg] at hα_sq
  have h3zero : (3 : ZMod q) = 0 := by
    have : (2 : ZMod q) * 2 - 1 = 0 := sub_eq_zero.mpr hα_sq
    norm_num at this
    exact this
  have hqdvd3 : q ∣ 3 := (ZMod.natCast_eq_zero_iff 3 q).mp (by simpa using h3zero)
  have hle3 : q ≤ 3 := Nat.le_of_dvd (by decide) hqdvd3
  omega

lemma maschke_complement {p : ℕ} [Fact p.Prime]
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    {A : Type*} [Group A] [Fintype A] (hpA : ¬ (p ∣ Nat.card A))
    (φ : A →* (V ≃ₗ[ZMod p] V))
    (U : Submodule (ZMod p) V) (hU : ∀ a : A, ∀ u ∈ U, φ a u ∈ U) :
    ∃ U' : Submodule (ZMod p) V, (∀ a : A, ∀ v ∈ U', φ a v ∈ U') ∧ IsCompl U U' := by
  classical
  obtain ⟨π, hπ⟩ := U.exists_isCompl
  let P0 : V →ₗ[ZMod p] V := U.subtype.comp (Submodule.projectionOnto U π hπ)
  have hP0_mem : ∀ v : V, P0 v ∈ U := fun v => (Submodule.projectionOnto U π hπ v).2
  have hP0_id : ∀ u ∈ U, P0 u = u := fun u hu => by
    change ((Submodule.projectionOnto U π hπ (⟨u, hu⟩ : U) : U) : V) = u
    rw [Submodule.projectionOnto_apply_left hπ ⟨u, hu⟩]
  let c : ZMod p := (Nat.card A : ZMod p)⁻¹
  have hc_ne : (Nat.card A : ZMod p) ≠ 0 := by
    intro h0; exact hpA ((ZMod.natCast_eq_zero_iff _ _).mp h0)
  let P : V →ₗ[ZMod p] V :=
    c • ∑ a : A, (φ a).toLinearMap.comp (P0.comp (φ a⁻¹).toLinearMap)
  have hP_mem : ∀ v : V, P v ∈ U := by
    intro v
    apply U.smul_mem
    simp only [LinearMap.sum_apply]
    exact U.sum_mem (fun a _ => hU a _ (hP0_mem _))
  have hP_id : ∀ u ∈ U, P u = u := by
    intro u hu
    simp only [P, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe]
    have hterm : ∀ a : A, φ a (P0 (φ a⁻¹ u)) = u := by
      intro a
      rw [hP0_id _ (hU a⁻¹ u hu)]
      have h1 : φ a (φ a⁻¹ u) = φ (a * a⁻¹) u := by rw [map_mul]; rfl
      rw [h1, mul_inv_cancel, map_one]; rfl
    simp_rw [hterm]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
      ← Nat.cast_smul_eq_nsmul (ZMod p), smul_smul, inv_mul_cancel₀ hc_ne, one_smul]
  have hP_comm : ∀ (b : A) (v : V), P (φ b v) = φ b (P v) := by
    intro b v
    simp only [P, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, map_smul, map_sum]
    congr 1
    refine Fintype.sum_equiv (Equiv.mulLeft b⁻¹) _ _ (fun a => ?_)
    change φ a (P0 (φ a⁻¹ (φ b v))) = φ b (φ (b⁻¹ * a) (P0 (φ (b⁻¹ * a)⁻¹ v)))
    have h3 : φ (b⁻¹ * a)⁻¹ v = φ a⁻¹ (φ b v) := by
      have hm : (b⁻¹ * a)⁻¹ = a⁻¹ * b := by group
      rw [hm, map_mul]; rfl
    rw [h3]
    have h4 : φ b (φ (b⁻¹ * a) (P0 (φ a⁻¹ (φ b v)))) = φ a (P0 (φ a⁻¹ (φ b v))) := by
      have hm : b * (b⁻¹ * a) = a := by group
      calc φ b (φ (b⁻¹ * a) (P0 (φ a⁻¹ (φ b v))))
          = (φ b * φ (b⁻¹ * a)) (P0 (φ a⁻¹ (φ b v))) := rfl
        _ = φ (b * (b⁻¹ * a)) (P0 (φ a⁻¹ (φ b v))) := by rw [← map_mul]
        _ = φ a (P0 (φ a⁻¹ (φ b v))) := by rw [hm]
    exact h4.symm
  refine ⟨LinearMap.ker P, ?_, ?_⟩
  · intro a v hv
    rw [LinearMap.mem_ker] at hv ⊢
    rw [hP_comm a v, hv, map_zero]
  · rw [isCompl_iff]
    refine ⟨disjoint_iff.mpr ?_, codisjoint_iff.mpr ?_⟩
    · rw [Submodule.eq_bot_iff]
      intro v ⟨hvU, hvker⟩
      have hPv : P v = 0 := hvker
      rwa [hP_id v hvU] at hPv
    · rw [Submodule.eq_top_iff']
      intro v
      have hdecomp : v = P v + (v - P v) := by abel
      rw [hdecomp]
      refine Submodule.add_mem_sup (hP_mem v) ?_
      rw [LinearMap.mem_ker, map_sub, hP_id (P v) (hP_mem v), sub_self]

lemma maschke_irred_decomp {p : ℕ} [Fact p.Prime]
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    {A : Type*} [Group A] [Fintype A] (hpA : ¬ (p ∣ Nat.card A))
    (φ : A →* (V ≃ₗ[ZMod p] V)) :
    ∀ (M : Submodule (ZMod p) V), (∀ a : A, ∀ v ∈ M, φ a v ∈ M) →
      ∃ (t : ℕ) (W : Fin t → Submodule (ZMod p) V),
        iSupIndep W ∧ iSup W = M ∧
        (∀ i, W i ≠ ⊥) ∧
        (∀ i, ∀ a : A, ∀ v ∈ W i, φ a v ∈ W i) ∧
        (∀ i, ∀ U : Submodule (ZMod p) V, U ≤ W i →
          (∀ a : A, ∀ v ∈ U, φ a v ∈ U) → U = ⊥ ∨ U = W i) := by
  classical
  have hstrong : ∀ n : ℕ, ∀ M : Submodule (ZMod p) V, Module.finrank (ZMod p) M = n →
      (∀ a : A, ∀ v ∈ M, φ a v ∈ M) →
      ∃ (t : ℕ) (W : Fin t → Submodule (ZMod p) V),
        iSupIndep W ∧ iSup W = M ∧
        (∀ i, W i ≠ ⊥) ∧
        (∀ i, ∀ a : A, ∀ v ∈ W i, φ a v ∈ W i) ∧
        (∀ i, ∀ U : Submodule (ZMod p) V, U ≤ W i →
          (∀ a : A, ∀ v ∈ U, φ a v ∈ U) → U = ⊥ ∨ U = W i) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro M hMfin hM
      by_cases hMbot : M = ⊥
      · refine ⟨0, Fin.elim0, ?_, ?_, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
        · exact iSupIndep_subsingleton _
        · simp [hMbot]
      · by_cases hirr : ∀ U : Submodule (ZMod p) V, U ≤ M →
            (∀ a : A, ∀ v ∈ U, φ a v ∈ U) → U = ⊥ ∨ U = M
        · refine ⟨1, fun _ => M, iSupIndep_subsingleton _, by simp, fun _ => hMbot,
            fun _ => hM, fun _ => hirr⟩
        · push Not at hirr
          obtain ⟨U, hUM, hUinv, hUne, hUneM⟩ := hirr
          let φM : A →* (M ≃ₗ[ZMod p] M) :=
            { toFun := fun a =>
                LinearEquiv.ofLinearMap
                  ((φ a).toLinearMap.restrict (fun x hx => hM a x hx))
                  ((φ a⁻¹).toLinearMap.restrict (fun x hx => hM a⁻¹ x hx))
                  (LinearMap.ext fun ⟨x, hx⟩ => Subtype.ext (by
                    change φ a (φ a⁻¹ x) = x
                    have h1 : φ a (φ a⁻¹ x) = φ (a * a⁻¹) x := by rw [map_mul]; rfl
                    rw [h1, mul_inv_cancel, map_one]; rfl))
                  (LinearMap.ext fun ⟨x, hx⟩ => Subtype.ext (by
                    change φ a⁻¹ (φ a x) = x
                    have h1 : φ a⁻¹ (φ a x) = φ (a⁻¹ * a) x := by rw [map_mul]; rfl
                    rw [h1, inv_mul_cancel, map_one]; rfl))
              map_one' := LinearEquiv.ext fun ⟨x, hx⟩ => Subtype.ext (by
                change φ 1 x = x; rw [map_one]; rfl)
              map_mul' := fun a b => LinearEquiv.ext fun ⟨x, hx⟩ => Subtype.ext (by
                change φ (a * b) x = φ a (φ b x); rw [map_mul]; rfl) }
          let UM : Submodule (ZMod p) M := U.comap M.subtype
          have hUM_inv : ∀ a : A, ∀ u ∈ UM, φM a u ∈ UM := fun a ⟨x, hx⟩ hxU => hUinv a x hxU
          obtain ⟨U'M, hU'M_inv, hcompl⟩ := maschke_complement hpA φM UM hUM_inv
          let U' : Submodule (ZMod p) V := U'M.map M.subtype
          have hU'M_le : U' ≤ M := Submodule.map_subtype_le M U'M
          have hU'inv : ∀ a : A, ∀ v ∈ U', φ a v ∈ U' := by
            intro a v hv
            obtain ⟨⟨x, hxM⟩, hxU', rfl⟩ := Submodule.mem_map.mp hv
            exact Submodule.mem_map.mpr ⟨φM a ⟨x, hxM⟩, hU'M_inv a ⟨x, hxM⟩ hxU', rfl⟩
          have hdisj : Disjoint U U' := by
            rw [Submodule.disjoint_def]
            intro x hxU hxU'
            obtain ⟨⟨y, hyM⟩, hyU', rfl⟩ := Submodule.mem_map.mp hxU'
            have hyUM : (⟨y, hyM⟩ : M) ∈ UM := hxU
            have h0 : (⟨y, hyM⟩ : M) = 0 := Submodule.disjoint_def.mp hcompl.disjoint _ hyUM hyU'
            exact congrArg Subtype.val h0
          have hsup : U ⊔ U' = M := by
            apply le_antisymm (sup_le hUM hU'M_le)
            intro x hxM
            have htop : (⟨x, hxM⟩ : M) ∈ UM ⊔ U'M := by
              rw [hcompl.codisjoint.eq_top]; trivial
            obtain ⟨u, hu, u', hu', hadd⟩ := Submodule.mem_sup.mp htop
            have hx_eq : x = (u : V) + (u' : V) := (congrArg Subtype.val hadd).symm
            rw [hx_eq]
            exact Submodule.add_mem_sup hu (Submodule.mem_map.mpr ⟨u', hu', rfl⟩)
          have hU'_ne : U' ≠ ⊥ := by
            intro hbot
            rw [hbot, sup_bot_eq] at hsup
            exact hUneM hsup
          have hfin_add : Module.finrank (ZMod p) U + Module.finrank (ZMod p) U' = n := by
            have h1 := Submodule.finrank_sup_add_finrank_inf_eq U U'
            rw [hsup, hdisj.eq_bot, finrank_bot, add_zero, hMfin] at h1
            exact h1.symm
          have hfinU_pos : 0 < Module.finrank (ZMod p) U := by
            obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hUne
            have _hnt : Nontrivial U := ⟨⟨⟨u, hu⟩, 0, fun h => hu0 (congrArg Subtype.val h)⟩⟩
            exact Module.finrank_pos
          have hfinU'_pos : 0 < Module.finrank (ZMod p) U' := by
            obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU'_ne
            have _hnt : Nontrivial U' := ⟨⟨⟨u, hu⟩, 0, fun h => hu0 (congrArg Subtype.val h)⟩⟩
            exact Module.finrank_pos
          obtain ⟨t₁, W₁, hind₁, hsup₁, hne₁, hinv₁, hirr₁⟩ :=
            ih (Module.finrank (ZMod p) U) (by omega) U rfl hUinv
          obtain ⟨t₂, W₂, hind₂, hsup₂, hne₂, hinv₂, hirr₂⟩ :=
            ih (Module.finrank (ZMod p) U') (by omega) U' rfl hU'inv
          let W : Fin (t₁ + t₂) → Submodule (ZMod p) V := Fin.append W₁ W₂
          refine ⟨t₁ + t₂, W, ?_, ?_, ?_, ?_, ?_⟩
          · -- iSupIndep (Fin.append W₁ W₂)
            intro i
            refine Fin.addCases (fun i₁ => ?_) (fun i₂ => ?_) i
            · have hle : ⨆ (j : Fin (t₁ + t₂)) (_ : j ≠ Fin.castAdd t₂ i₁), W j ≤
                  (⨆ (j₁ : Fin t₁) (_ : j₁ ≠ i₁), W₁ j₁) ⊔ U' := by
                refine iSup₂_le (fun j => ?_)
                refine Fin.addCases (fun j₁ hj => ?_) (fun j₂ _ => ?_) j
                · have hne : j₁ ≠ i₁ := fun heq => hj (congrArg (Fin.castAdd t₂) heq)
                  have hW1' : W (Fin.castAdd t₂ j₁) = W₁ j₁ := by simp [W]
                  rw [hW1']
                  exact le_trans (le_iSup₂ (f := fun j₁ (_ : j₁ ≠ i₁) => W₁ j₁) j₁ hne) le_sup_left
                · refine le_trans ?_ le_sup_right
                  rw [← hsup₂]
                  simpa [W] using le_iSup W₂ j₂
              have hW1 : W (Fin.castAdd t₂ i₁) = W₁ i₁ := by simp [W]
              rw [hW1]
              refine Disjoint.mono_right hle ?_
              rw [Submodule.disjoint_def]
              intro x hx1 hx2
              obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hx2
              have hyU : y ∈ U := by
                rw [← hsup₁]
                exact (iSup₂_le fun j₁ _ => le_iSup W₁ j₁) hy
              have hxU : x ∈ U := hsup₁ ▸ (le_iSup W₁ i₁ hx1)
              have hz_eq : z = x - y := by rw [← hyz]; abel
              have hzU : z ∈ U := hz_eq ▸ U.sub_mem hxU hyU
              have hz0 : z = 0 := Submodule.disjoint_def.mp hdisj z hzU hz
              rw [hz0, add_zero] at hyz
              rw [hyz] at hy
              exact Submodule.disjoint_def.mp (hind₁ i₁) x hx1 hy
            · have hle : ⨆ (j : Fin (t₁ + t₂)) (_ : j ≠ Fin.natAdd t₁ i₂), W j ≤
                  U ⊔ (⨆ (j₂ : Fin t₂) (_ : j₂ ≠ i₂), W₂ j₂) := by
                refine iSup₂_le (fun j => ?_)
                refine Fin.addCases (fun j₁ _ => ?_) (fun j₂ hj => ?_) j
                · refine le_trans ?_ le_sup_left
                  rw [← hsup₁]
                  simpa [W] using le_iSup W₁ j₁
                · have hne : j₂ ≠ i₂ := fun heq => hj (congrArg (Fin.natAdd t₁) heq)
                  have hW2' : W (Fin.natAdd t₁ j₂) = W₂ j₂ := by simp [W]
                  rw [hW2']
                  exact le_trans (le_iSup₂ (f := fun j₂ (_ : j₂ ≠ i₂) => W₂ j₂) j₂ hne) le_sup_right
              have hW2 : W (Fin.natAdd t₁ i₂) = W₂ i₂ := by simp [W]
              rw [hW2]
              refine Disjoint.mono_right hle ?_
              rw [Submodule.disjoint_def]
              intro x hx1 hx2
              obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hx2
              have hzU' : z ∈ U' := by
                rw [← hsup₂]
                exact (iSup₂_le fun j₂ _ => le_iSup W₂ j₂) hz
              have hxU' : x ∈ U' := hsup₂ ▸ (le_iSup W₂ i₂ hx1)
              have hy_eq : y = x - z := by rw [← hyz]; abel
              have hyU' : y ∈ U' := hy_eq ▸ U'.sub_mem hxU' hzU'
              have hy0 : y = 0 := Submodule.disjoint_def.mp hdisj y hy hyU'
              rw [hy0, zero_add] at hyz
              rw [hyz] at hz
              exact Submodule.disjoint_def.mp (hind₂ i₂) x hx1 hz
          · rw [← hsup, ← hsup₁, ← hsup₂]
            apply le_antisymm
            · refine iSup_le (fun j => ?_)
              refine Fin.addCases (fun j₁ => ?_) (fun j₂ => ?_) j
              · simpa [W] using le_trans (le_iSup W₁ j₁) le_sup_left
              · simpa [W] using le_trans (le_iSup W₂ j₂) le_sup_right
            · refine sup_le (iSup_le fun j₁ => ?_) (iSup_le fun j₂ => ?_)
              · have h := le_iSup W (Fin.castAdd t₂ j₁)
                simpa [W] using h
              · have h := le_iSup W (Fin.natAdd t₁ j₂)
                simpa [W] using h
          · intro i
            refine Fin.addCases (fun i₁ => ?_) (fun i₂ => ?_) i
            · simp [W, hne₁]
            · simp [W, hne₂]
          · intro i
            refine Fin.addCases (fun i₁ => ?_) (fun i₂ => ?_) i
            · simpa [W] using hinv₁ i₁
            · simpa [W] using hinv₂ i₂
          · intro i
            refine Fin.addCases (fun i₁ => ?_) (fun i₂ => ?_) i
            · simpa [W] using hirr₁ i₁
            · simpa [W] using hirr₂ i₂
  intro M hM
  exact hstrong (Module.finrank (ZMod p) M) M rfl hM

lemma abelian_irred_stabilizer_and_quotient_cyclic {p : ℕ} [Fact p.Prime]
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    {A : Type*} [CommGroup A] [Fintype A]
    (φ : A →* (V ≃ₗ[ZMod p] V))
    (W : Submodule (ZMod p) V) (hWne : W ≠ ⊥)
    (hWinv : ∀ a : A, ∀ v ∈ W, φ a v ∈ W)
    (hWirr : ∀ U : Submodule (ZMod p) V, U ≤ W →
      (∀ a : A, ∀ v ∈ U, φ a v ∈ U) → U = ⊥ ∨ U = W)
    (K : Subgroup A) (hK : ∀ a : A, a ∈ K ↔ ∀ w ∈ W, φ a w = w) :
    (∀ w ∈ W, w ≠ 0 → ∀ a : A, φ a w = w → a ∈ K) ∧ IsCyclic (A ⧸ K) := by
  classical
  refine ⟨?_, ?_⟩
  · intro w hw hw0 a haw
    rw [hK]
    let U : Submodule (ZMod p) V := W ⊓ LinearMap.ker ((φ a).toLinearMap - LinearMap.id)
    have hUle : U ≤ W := inf_le_left
    have hUinv : ∀ b : A, ∀ u ∈ U, φ b u ∈ U := by
      intro b u ⟨huW, huker⟩
      refine ⟨hWinv b u huW, ?_⟩
      have h1 : φ a u - u = 0 := huker
      have hau : φ a u = u := sub_eq_zero.mp h1
      change φ a (φ b u) - φ b u = 0
      rw [sub_eq_zero]
      calc φ a (φ b u) = φ (a * b) u := by rw [map_mul]; rfl
        _ = φ (b * a) u := by rw [mul_comm]
        _ = φ b (φ a u) := by rw [map_mul]; rfl
        _ = φ b u := by rw [hau]
    have hwU : w ∈ U := ⟨hw, show φ a w - w = 0 from sub_eq_zero.mpr haw⟩
    have hUne : U ≠ ⊥ := fun hbot => hw0 (by simpa [hbot] using hwU)
    have hUW : U = W := (hWirr U hUle hUinv).resolve_left hUne
    intro x hx
    have hxU : x ∈ U := hUW ▸ hx
    exact sub_eq_zero.mp (show φ a x - x = 0 from hxU.2)
  · -- A ⧸ K embeds into the multiplicative monoid of the commutative integral domain E ⊆ End(W)
    let ψ : A →* Module.End (ZMod p) W :=
      { toFun := fun a => (φ a).toLinearMap.restrict (fun x hx => hWinv a x hx)
        map_one' := by ext ⟨x, hx⟩; simp
        map_mul' := fun a b => by ext ⟨x, hx⟩; simp }
    let E : Subring (Module.End (ZMod p) W) :=
      Subring.closure (Set.range (fun a : A => ψ a))
    have hE_comm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
      intro x hx
      refine Subring.closure_induction (p := fun x _ => ∀ y ∈ E, x * y = y * x)
        (fun x hxS y hy => ?_) (fun y _ => by simp) (fun y _ => by simp)
        (fun x₁ x₂ _ _ ih₁ ih₂ y hy => by rw [add_mul, mul_add, ih₁ y hy, ih₂ y hy])
        (fun x₁ _ ih₁ y hy => by rw [neg_mul, mul_neg, ih₁ y hy])
        (fun x₁ x₂ _ _ ih₁ ih₂ y hy => by rw [mul_assoc, ih₂ y hy, ← mul_assoc, ih₁ y hy, mul_assoc])
        hx
      obtain ⟨a, rfl⟩ := hxS
      refine Subring.closure_induction (p := fun y _ => ψ a * y = y * ψ a)
        (fun y hyS => ?_) (by simp) (by simp)
        (fun y₁ y₂ _ _ ih₁ ih₂ => by rw [mul_add, add_mul, ih₁, ih₂])
        (fun y₁ _ ih₁ => by rw [mul_neg, neg_mul, ih₁])
        (fun y₁ y₂ _ _ ih₁ ih₂ => by rw [← mul_assoc, ih₁, mul_assoc, ih₂, ← mul_assoc])
        hy
      obtain ⟨b, rfl⟩ := hyS
      rw [← map_mul, ← map_mul, mul_comm a b]
    -- Every nonzero f ∈ E is injective on W (Schur's lemma)
    have hE_inj : ∀ f ∈ E, f ≠ 0 → Function.Injective f := by
      intro f hf hf0
      rw [← LinearMap.ker_eq_bot]
      let U : Submodule (ZMod p) V := (LinearMap.ker f).map W.subtype
      have hUle : U ≤ W := Submodule.map_subtype_le W _
      have hUinv : ∀ a : A, ∀ u ∈ U, φ a u ∈ U := by
        intro a u hu
        obtain ⟨x, hxker, rfl⟩ := Submodule.mem_map.mp hu
        refine Submodule.mem_map.mpr ⟨ψ a x, ?_, rfl⟩
        rw [LinearMap.mem_ker] at hxker ⊢
        have hcomm : f * ψ a = ψ a * f := hE_comm f hf (ψ a) (Subring.subset_closure ⟨a, rfl⟩)
        change (f * ψ a) x = 0
        rw [hcomm]
        change ψ a (f x) = 0
        rw [hxker, map_zero]
      rcases hWirr U hUle hUinv with hbot | htop
      · rw [Submodule.eq_bot_iff]
        intro x hx
        have hmem : (x : V) ∈ U := Submodule.mem_map.mpr ⟨x, hx, rfl⟩
        have hx0 : (x : V) = 0 := by simpa [hbot] using hmem
        exact Subtype.ext hx0
      · exfalso
        apply hf0
        refine LinearMap.ext fun x => ?_
        have hmem : (x : V) ∈ U := by rw [htop]; exact x.2
        obtain ⟨y, hyker, hyx⟩ := Submodule.mem_map.mp hmem
        have hxy : y = x := Subtype.ext hyx
        rw [← hxy]
        exact LinearMap.mem_ker.mp hyker
    let _hE_commRing : CommRing E :=
      { (inferInstance : Ring E) with
        mul_comm := fun x y => Subtype.ext (hE_comm x.1 x.2 y.1 y.2) }
    have _hE_nt : Nontrivial E := by
      rw [nontrivial_iff]
      refine ⟨1, 0, ?_⟩
      intro h10
      have h10' : (1 : Module.End (ZMod p) W) = 0 := congrArg Subtype.val h10
      obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
      have h := congrArg (fun f : Module.End (ZMod p) W => f ⟨w, hwW⟩) h10'
      exact hw0 (congrArg Subtype.val h)
    have _hE_nzd : NoZeroDivisors E :=
      { eq_zero_or_eq_zero_of_mul_eq_zero := fun {x y} hxy => by
          by_cases hx : x = 0
          · exact Or.inl hx
          · right
            have hx0 : (x : Module.End (ZMod p) W) ≠ 0 := fun h => hx (Subtype.ext h)
            have hinj := hE_inj x.1 x.2 hx0
            refine Subtype.ext (LinearMap.ext fun w => hinj ?_)
            have h1 : x.1 (y.1 w) = 0 := by
              have h' : (x.1 * y.1) w = 0 := by
                have hmul : x.1 * y.1 = ((x * y : E) : Module.End (ZMod p) W) := rfl
                rw [hmul, hxy]
                rfl
              exact h'
            simpa using h1 }
    have _hE_domain : IsDomain E := NoZeroDivisors.to_isDomain E
    let ψE : A →* E :=
      { toFun := fun a => ⟨ψ a, Subring.subset_closure ⟨a, rfl⟩⟩
        map_one' := Subtype.ext (map_one ψ)
        map_mul' := fun a b => Subtype.ext (map_mul ψ a b) }
    have hK_le_ker : K ≤ ψE.ker := by
      intro a ha
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      ext ⟨w, hw⟩
      exact (hK a).mp ha w hw
    let fQ : A ⧸ K →* E := QuotientGroup.lift K ψE hK_le_ker
    have hfQ_inj : Function.Injective fQ := by
      rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
      intro q hq
      induction q using QuotientGroup.induction_on with
      | H a =>
        rw [QuotientGroup.eq_one_iff, hK]
        intro w hw
        have h1 : ψ a ⟨w, hw⟩ = ⟨w, hw⟩ := by
          have h' : fQ (QuotientGroup.mk a) = 1 := hq
          have h'' : (ψE a : Module.End (ZMod p) W) = 1 := congrArg Subtype.val h'
          exact congrArg (fun g : Module.End (ZMod p) W => g ⟨w, hw⟩) h''
        exact congrArg Subtype.val h1
    exact isCyclic_of_injective_ringHom fQ hfQ_inj

lemma no_normal_pGroup_ge_five {p d : ℕ} [Fact p.Prime]
    {H : Type*} [Group H] [Fintype H]
    (hHrat : ∀ (x : H) (n : ℕ), (Nat.card H).Coprime n → IsConj x (x ^ n))
    (hpH : ¬ (p ∣ Nat.card H))
    (ρ : H →* ((Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)))
    (hfaith : Function.Injective ρ)
    (hcent : ∀ (v : Fin d → ZMod p), v ≠ 0 → ∀ (y : H), ρ y v = v →
      ∀ (n : ℕ), (Nat.card {h : H // ρ h v = v}).Coprime n →
        ∃ h : H, ρ h v = v ∧ h * y * h⁻¹ = y ^ n)
    (q : ℕ) (hq : q.Prime) (hq5 : 5 ≤ q)
    (Q : Subgroup H) (hQnorm : Q.Normal) (hQp : IsPGroup q Q) : Q = ⊥ := by
  classical
  by_contra hQne
  have _hq_fact : Fact q.Prime := ⟨hq⟩
  have _hQnt : Nontrivial Q := by
    rw [nontrivial_iff]
    obtain ⟨x, hxQ, hx1⟩ : ∃ x ∈ Q, x ≠ 1 := by
      by_contra hall; push Not at hall
      exact hQne ((Subgroup.eq_bot_iff_forall Q).mpr hall)
    exact ⟨⟨x, hxQ⟩, 1, fun h => hx1 (congrArg Subtype.val h)⟩
  -- A = Ω_1(Z(Q)) is a nontrivial elementary abelian q-group normal in H
  have hZne : Nontrivial (Subgroup.center Q) := hQp.center_nontrivial
  have hZp : IsPGroup q (Subgroup.center Q) := hQp.to_subgroup (Subgroup.center Q)
  obtain ⟨k, hk_pos, hk_card⟩ := hZp.nontrivial_iff_card.mp hZne
  have hq_dvd_Z : q ∣ Nat.card (Subgroup.center Q) := by
    rw [hk_card]; exact dvd_pow_self q hk_pos.ne'
  let A : Subgroup H :=
    { carrier := {a : H | ∃ ha : a ∈ Q, (⟨a, ha⟩ : Q) ∈ Subgroup.center Q ∧ a ^ q = 1}
      mul_mem' := fun {a b} ⟨haQ, haZ, hap⟩ ⟨hbQ, hbZ, hbp⟩ => by
        refine ⟨Q.mul_mem haQ hbQ, Subgroup.mul_mem _ haZ hbZ, ?_⟩
        have hcomm : Commute a b := by
          have := Subgroup.mem_center_iff.mp haZ ⟨b, hbQ⟩
          exact (congrArg Subtype.val this).symm
        rw [hcomm.mul_pow, hap, hbp, one_mul]
      one_mem' := ⟨Q.one_mem, Subgroup.one_mem _, one_pow q⟩
      inv_mem' := fun {a} ⟨haQ, haZ, hap⟩ =>
        ⟨Q.inv_mem haQ, Subgroup.inv_mem _ haZ, by rw [inv_pow, hap, inv_one]⟩ }
  have hAnorm : A.Normal := ⟨fun a ⟨haQ, haZ, hap⟩ g => by
    refine ⟨hQnorm.conj_mem a haQ g, ?_, by rw [conj_pow, hap, mul_one, mul_inv_cancel]⟩
    rw [Subgroup.mem_center_iff]
    intro ⟨y, hyQ⟩
    apply Subtype.ext
    have hy' : g⁻¹ * y * g ∈ Q := by simpa [inv_inv] using hQnorm.conj_mem y hyQ g⁻¹
    have hcomm : (g⁻¹ * y * g) * a = a * (g⁻¹ * y * g) :=
      congrArg Subtype.val (Subgroup.mem_center_iff.mp haZ ⟨g⁻¹ * y * g, hy'⟩)
    change y * (g * a * g⁻¹) = (g * a * g⁻¹) * y
    calc y * (g * a * g⁻¹) = g * ((g⁻¹ * y * g) * a) * g⁻¹ := by group
      _ = g * (a * (g⁻¹ * y * g)) * g⁻¹ := by rw [hcomm]
      _ = (g * a * g⁻¹) * y := by group⟩
  have hAcomm : ∀ a b : A, a * b = b * a := fun ⟨a, haQ, haZ, _⟩ ⟨b, hbQ, _, _⟩ =>
    Subtype.ext (congrArg Subtype.val (Subgroup.mem_center_iff.mp haZ ⟨b, hbQ⟩)).symm
  have hApow : ∀ a : A, a ^ q = 1 := fun ⟨a, _, _, hap⟩ => Subtype.ext hap
  have hAne : A ≠ ⊥ := by
    obtain ⟨⟨⟨a, haQ⟩, haZ⟩, haord⟩ :=
      exists_prime_orderOf_dvd_card' (G := Subgroup.center Q) q hq_dvd_Z
    intro hbot
    have haA : a ∈ A := by
      refine ⟨haQ, haZ, ?_⟩
      have h1 : (⟨⟨a, haQ⟩, haZ⟩ : Subgroup.center Q) ^ q = 1 := by
        rw [← haord, pow_orderOf_eq_one]
      exact congrArg (fun z : Subgroup.center Q => (z.1 : H)) h1
    rw [hbot, Subgroup.mem_bot] at haA
    have ha1 : (⟨⟨a, haQ⟩, haZ⟩ : Subgroup.center Q) = 1 := Subtype.ext (Subtype.ext haA)
    rw [ha1, orderOf_one] at haord
    exact hq.ne_one haord.symm
  -- Give A its CommGroup structure for quotient operations
  let hA_commGroup : CommGroup A := { (inferInstance : Group A) with mul_comm := hAcomm }
  -- Decompose V into irreducible ZMod p [A]-submodules via Maschke
  have hpA : ¬ (p ∣ Nat.card A) := fun hdvd =>
    hpH (dvd_trans hdvd (Subgroup.card_subgroup_dvd_card A))
  let ρA : A →* ((Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)) := ρ.comp A.subtype
  obtain ⟨t, W, hWind, hWsup, hWne, hWinv, hWirr⟩ :=
    maschke_irred_decomp hpA ρA ⊤ (fun _ _ _ => trivial)
  -- For each i : Fin t, define K i = ker(A → GL(W i))
  let K : Fin t → Subgroup A := fun i =>
    { carrier := {a : A | ∀ w ∈ W i, ρA a w = w}
      mul_mem' := fun {a b} ha hb w hw => by simp [map_mul, hb w hw, ha w hw]
      one_mem' := fun w _ => by simp
      inv_mem' := fun {a} ha w hw => by
        have := congrArg (ρA a⁻¹) (ha w hw)
        simpa [← map_mul] using this.symm }
  have hK_stab : ∀ i : Fin t, ∀ w ∈ W i, w ≠ 0 → ∀ a : A, ρA a w = w → a ∈ K i := fun i =>
    (@abelian_irred_stabilizer_and_quotient_cyclic p _ (Fin d → ZMod p) _ _ _ A hA_commGroup _
      ρA (W i) (hWne i) (hWinv i) (hWirr i) (K i) (fun _ => Iff.rfl)).1
  -- The intersection of all K i is ⊥ (by faithfulness of ρ)
  have hK_inf : (⨅ i : Fin t, K i) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro a ha
    rw [Subgroup.mem_iInf] at ha
    have hρa : ρ (a : H) = 1 := by
      refine LinearEquiv.ext fun v => ?_
      change ρ (a : H) v = v
      have hv : v ∈ iSup W := by rw [hWsup]; trivial
      refine Submodule.iSup_induction (motive := fun x => ρ (a : H) x = x) W hv
        (fun i x hx => ha i x hx) (map_zero _) (fun x y hx hy => by rw [map_add, hx, hy])
    exact Subtype.ext (hfaith (hρa.trans (map_one ρ).symm))
  -- Choose a minimal finset I ⊆ Finset.univ with ⋂_{i ∈ I} K i = ⊥
  have hexI : ∃ s : ℕ, ∃ I : Finset (Fin t), I.card = s ∧ (⨅ i ∈ I, K i) = ⊥ :=
    ⟨t, Finset.univ, Finset.card_fin t, by simpa using hK_inf⟩
  obtain ⟨I, hIcard, hIinf⟩ := Nat.find_spec hexI
  have hI_nonempty : I.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    rw [hempty] at hIinf
    simp only [Finset.notMem_empty, iInf_false, iInf_top] at hIinf
    apply hAne
    rw [Subgroup.eq_bot_iff_forall]
    intro a ha
    have : (⟨a, ha⟩ : A) ∈ (⊥ : Subgroup A) := hIinf ▸ trivial
    exact congrArg Subtype.val (Subgroup.mem_bot.mp this)
  obtain ⟨i₀, hi₀I⟩ := hI_nonempty
  let J := I.erase i₀
  let L : Subgroup A := ⨅ i ∈ J, K i
  have hLne : L ≠ ⊥ := by
    intro hbot
    have hlt : J.card < Nat.find hexI := by
      rw [← hIcard]; exact Finset.card_erase_lt_of_mem hi₀I
    exact Nat.find_min hexI hlt ⟨J, rfl, hbot⟩
  have hL_inter : L ⊓ K i₀ = ⊥ := by
    apply le_antisymm _ bot_le
    rw [← hIinf]
    refine le_iInf (fun i => le_iInf (fun hiI => ?_))
    by_cases hi : i = i₀
    · subst hi; exact inf_le_right
    · exact le_trans inf_le_left (iInf₂_le i (Finset.mem_erase.mpr ⟨hi, hiI⟩))
  -- L embeds into A ⧸ K i₀, which is cyclic of exponent dividing q, so |L| = q
  have hLcard : Nat.card L = q := by
    have _hKi₀_norm : (K i₀).Normal :=
      ⟨fun k hk a => by rw [hAcomm a k]; simpa [mul_assoc] using hk⟩
    let φL : L →* A ⧸ K i₀ := (QuotientGroup.mk' (K i₀)).comp L.subtype
    have hφL_inj : Function.Injective φL := by
      rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
      intro ⟨a, haL⟩ haK
      change QuotientGroup.mk a = 1 at haK
      rw [QuotientGroup.eq_one_iff] at haK
      have hbot : a ∈ (⊥ : Subgroup A) := hL_inter ▸ ⟨haL, haK⟩
      exact Subtype.ext (Subgroup.mem_bot.mp hbot)
    have hcard_le : Nat.card L ≤ Nat.card (A ⧸ K i₀) :=
      Nat.card_le_card_of_injective φL hφL_inj
    have _hQcyc : IsCyclic (A ⧸ K i₀) :=
      (@abelian_irred_stabilizer_and_quotient_cyclic p _ (Fin d → ZMod p) _ _ _ A hA_commGroup _
        ρA (W i₀) (hWne i₀) (hWinv i₀) (hWirr i₀) (K i₀) (fun _ => Iff.rfl)).2
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := A ⧸ K i₀)
    have hgq : g ^ q = 1 := by
      induction g using QuotientGroup.induction_on with
      | H a =>
        change QuotientGroup.mk (a ^ q) = 1
        rw [hApow a]; rfl
    have hcardQ_dvd : Nat.card (A ⧸ K i₀) ∣ q := by
      have hord : orderOf g = Nat.card (A ⧸ K i₀) := by
        rw [← Nat.card_zpowers]
        have htop : Subgroup.zpowers g = ⊤ := by
          rw [eq_top_iff]; intro x _
          exact hg x
        rw [htop, Subgroup.card_top]
      rw [← hord]
      exact orderOf_dvd_of_pow_eq_one hgq
    have hcardQ_le : Nat.card (A ⧸ K i₀) ≤ q := Nat.le_of_dvd hq.pos hcardQ_dvd
    obtain ⟨a, haL, ha1⟩ : ∃ a ∈ L, a ≠ 1 := by
      by_contra hall; push Not at hall
      exact hLne ((Subgroup.eq_bot_iff_forall L).mpr hall)
    have ha_ord : orderOf (⟨a, haL⟩ : L) = q := by
      have hdvd : orderOf (⟨a, haL⟩ : L) ∣ q :=
        orderOf_dvd_of_pow_eq_one (Subtype.ext (hApow a))
      rcases (Nat.dvd_prime hq).mp hdvd with h1 | hq'
      · exact absurd (congrArg Subtype.val (orderOf_eq_one_iff.mp h1)) ha1
      · exact hq'
    have hq_dvd_L : q ∣ Nat.card L := ha_ord ▸ orderOf_dvd_natCard (⟨a, haL⟩ : L)
    have hq_le_L : q ≤ Nat.card L := Nat.le_of_dvd Nat.card_pos hq_dvd_L
    omega
  -- Case split on whether J is empty
  by_cases hJ : J = ∅
  · have hLtop : L = ⊤ := by simp [L, hJ]
    have hAcard : Nat.card A = q := by
      rw [← hLcard, hLtop, Subgroup.card_top]
    exact no_normal_prime_subgroup_of_ge_five hHrat q hq hq5 A hAnorm hAcard
  · have hJne : J.Nonempty := Finset.nonempty_iff_ne_empty.mpr hJ
    have hw_ex : ∀ i : Fin t, ∃ w : Fin d → ZMod p, w ∈ W i ∧ w ≠ 0 := fun i =>
      Submodule.exists_mem_ne_zero_of_ne_bot (hWne i)
    choose w hwW hw0 using hw_ex
    let v : Fin d → ZMod p := ∑ i ∈ J, w i
    have hv_ne0 : v ≠ 0 := by
      obtain ⟨j₀, hj₀J⟩ := hJne
      intro hv0
      have hwj : w j₀ = -(∑ i ∈ J.erase j₀, w i) := by
        have hsum : w j₀ + ∑ i ∈ J.erase j₀, w i = 0 := by
          rw [Finset.add_sum_erase J w hj₀J]; exact hv0
        exact eq_neg_of_add_eq_zero_left hsum
      have hmem1 : w j₀ ∈ W j₀ := hwW j₀
      have hmem2 : w j₀ ∈ ⨆ (j : Fin t) (_ : j ≠ j₀), W j := by
        rw [hwj]
        apply Submodule.neg_mem
        apply Submodule.sum_mem
        intro i hi
        have hne : i ≠ j₀ := (Finset.mem_erase.mp hi).1
        exact le_iSup₂ (f := fun j (_ : j ≠ j₀) => W j) i hne (hwW i)
      exact hw0 j₀ (Submodule.disjoint_def.mp (hWind j₀) _ hmem1 hmem2)
    have hstab_A : ∀ a : A, ρA a v = v ↔ a ∈ L := by
      intro a
      constructor
      · intro hav
        rw [Subgroup.mem_iInf]
        intro j
        rw [Subgroup.mem_iInf]
        intro hjJ
        apply hK_stab j (w j) (hwW j) (hw0 j) a
        have hsum0 : ∑ i ∈ J, (ρA a (w i) - w i) = 0 := by
          rw [Finset.sum_sub_distrib, ← map_sum, hav, sub_self]
        have hdiff_eq : ρA a (w j) - w j = -(∑ i ∈ J.erase j, (ρA a (w i) - w i)) := by
          have h1 : (ρA a (w j) - w j) + ∑ i ∈ J.erase j, (ρA a (w i) - w i) = 0 := by
            rw [Finset.add_sum_erase J (fun i => ρA a (w i) - w i) hjJ]; exact hsum0
          exact eq_neg_of_add_eq_zero_left h1
        have hmem1 : ρA a (w j) - w j ∈ W j :=
          (W j).sub_mem (hWinv j a (w j) (hwW j)) (hwW j)
        have hmem2 : ρA a (w j) - w j ∈ ⨆ (i : Fin t) (_ : i ≠ j), W i := by
          rw [hdiff_eq]
          apply Submodule.neg_mem
          apply Submodule.sum_mem
          intro i hi
          have hne : i ≠ j := (Finset.mem_erase.mp hi).1
          exact le_iSup₂ (f := fun i (_ : i ≠ j) => W i) i hne
            ((W i).sub_mem (hWinv i a (w i) (hwW i)) (hwW i))
        have h0 : ρA a (w j) - w j = 0 :=
          Submodule.disjoint_def.mp (hWind j) _ hmem1 hmem2
        exact sub_eq_zero.mp h0
      · intro haL
        rw [map_sum]
        refine Finset.sum_congr rfl (fun j hjJ => ?_)
        have haj : a ∈ K j := (Subgroup.mem_iInf.mp ((Subgroup.mem_iInf.mp haL) j)) hjJ
        exact haj (w j) (hwW j)
    let Cv : Subgroup H :=
      { carrier := {h : H | ρ h v = v}
        mul_mem' := fun {a b} ha hb => by
          change ρ (a * b) v = v
          rw [map_mul]
          exact (congrArg (ρ a) hb).trans ha
        one_mem' := by simp
        inv_mem' := fun {a} ha => by
          have : ρ a⁻¹ (ρ a v) = ρ a⁻¹ v := congrArg (ρ a⁻¹) ha
          simpa [← map_mul] using this.symm }
    have hCv_rat : ∀ (x : Cv) (n : ℕ), (Nat.card Cv).Coprime n → IsConj x (x ^ n) := by
      intro ⟨y, hy⟩ n hn
      obtain ⟨h, hhCv, hconj⟩ := hcent v hv_ne0 y hy n hn
      rw [isConj_iff]
      exact ⟨⟨h, hhCv⟩, Subtype.ext hconj⟩
    let L' : Subgroup Cv :=
      { carrier := {x : Cv | (x : H) ∈ A}
        mul_mem' := fun {a b} ha hb => A.mul_mem ha hb
        one_mem' := A.one_mem
        inv_mem' := fun {a} ha => A.inv_mem ha }
    have hL'_norm : L'.Normal := ⟨fun x hx g => hAnorm.conj_mem (x : H) hx (g : H)⟩
    have hL'_card : Nat.card L' = q := by
      rw [← hLcard]
      refine Nat.card_congr ?_
      exact
        { toFun := fun ⟨⟨x, hxCv⟩, hxA⟩ => ⟨⟨x, hxA⟩, (hstab_A ⟨x, hxA⟩).mp hxCv⟩
          invFun := fun ⟨⟨x, hxA⟩, hxL⟩ => ⟨⟨x, (hstab_A ⟨x, hxA⟩).mpr hxL⟩, hxA⟩
          left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
          right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl }
    exact no_normal_prime_subgroup_of_ge_five hCv_rat q hq hq5 L' hL'_norm hL'_card

/- ### Component 4: Eigenspace Dimension Bound -/

lemma sum_finrank_le_of_iSupIndep {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] [Fintype ι] [DecidableEq ι]
    (F : ι → Submodule K V) (hind : iSupIndep F) :
    ∑ i : ι, Module.finrank K (F i) ≤ Module.finrank K V := by
  have hfin : ∀ s : Finset ι,
      ∑ i ∈ s, Module.finrank K (F i) = Module.finrank K (⨆ i ∈ s, F i : Submodule K V) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have hbot : (⨆ i ∈ (∅ : Finset ι), F i : Submodule K V) = ⊥ := by simp
      rw [Finset.sum_empty, hbot, finrank_bot]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, ih]
      have hsup : (⨆ i ∈ insert a s, F i : Submodule K V) = F a ⊔ ⨆ i ∈ s, F i := by
        apply le_antisymm
        · refine iSup₂_le (fun i hi => ?_)
          rcases Finset.mem_insert.mp hi with rfl | his
          · exact le_sup_left
          · exact le_trans (le_iSup₂ (f := fun j (_ : j ∈ s) => F j) i his) le_sup_right
        · refine sup_le (le_iSup₂ (f := fun j (_ : j ∈ insert a s) => F j) a (Finset.mem_insert_self a s))
            (iSup₂_le (fun i hi => le_iSup₂ (f := fun j (_ : j ∈ insert a s) => F j) i
              (Finset.mem_insert_of_mem hi)))
      have hdisj : Disjoint (F a) (⨆ i ∈ s, F i) := by
        refine Disjoint.mono_right ?_ (hind a)
        refine iSup₂_le (fun j hj => ?_)
        have hne : j ≠ a := fun heq => ha (heq ▸ hj)
        exact le_iSup₂ (f := fun j (_ : j ≠ a) => F j) j hne
      have hadd := Submodule.finrank_sup_add_finrank_inf_eq (F a) (⨆ i ∈ s, F i)
      rw [hdisj.eq_bot, finrank_bot, add_zero, ← hsup] at hadd
      exact hadd.symm
  rw [hfin Finset.univ]
  exact Submodule.finrank_le _

lemma eigenspace_dim_bound {p d : ℕ} [Fact p.Prime]
    {H : Type*} [Group H] [Fintype H]
    (hHrat : ∀ (x : H) (n : ℕ), (Nat.card H).Coprime n → IsConj x (x ^ n))
    (ρ : H →* ((Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)))
    (g : H) (c : (ZMod p)ˣ) :
    Module.finrank (ZMod p) (LinearMap.ker ((ρ g).toLinearMap - (c : ZMod p) • LinearMap.id)) *
      Nat.totient (orderOf c) ≤ d := by
  classical
  let E : ZMod p → Submodule (ZMod p) (Fin d → ZMod p) :=
    fun μ => Module.End.eigenspace (ρ g).toLinearMap μ
  have hEc_eq : LinearMap.ker ((ρ g).toLinearMap - (c : ZMod p) • LinearMap.id) = E (c : ZMod p) := by
    ext v
    simp [E, sub_eq_zero]
  rw [hEc_eq]
  by_cases hbot : E (c : ZMod p) = ⊥
  · rw [hbot, finrank_bot, zero_mul]; exact Nat.zero_le d
  · obtain ⟨v₀, hv₀E, hv₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    have hv₀_eig : ρ g v₀ = (c : ZMod p) • v₀ := Module.End.mem_eigenspace_iff.mp hv₀E
    have hpow_eig : ∀ (v : Fin d → ZMod p) (k : ℕ),
        ρ g v = (c : ZMod p) • v → ρ (g ^ k) v = ((c : ZMod p) ^ k) • v := by
      intro v k hv
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', map_mul]
        change ρ g (ρ (g ^ k) v) = _
        rw [ih, map_smul, hv, smul_smul, ← pow_succ]
    -- orderOf c divides orderOf g
    have hord_dvd : orderOf c ∣ orderOf g := by
      apply orderOf_dvd_of_pow_eq_one
      apply Units.ext
      push_cast
      have h1 : v₀ = ((c : ZMod p) ^ orderOf g) • v₀ := by
        calc v₀ = ρ 1 v₀ := by simp
          _ = ρ (g ^ orderOf g) v₀ := by rw [pow_orderOf_eq_one]
          _ = ((c : ZMod p) ^ orderOf g) • v₀ := hpow_eig v₀ (orderOf g) hv₀_eig
      have h2 : ((c : ZMod p) ^ orderOf g - 1) • v₀ = 0 := by
        rw [sub_smul, one_smul, ← h1, sub_self]
      rcases smul_eq_zero.mp h2 with hzero | hv0
      · exact sub_eq_zero.mp hzero
      · exact absurd hv0 hv₀ne
    let m := orderOf c
    have hm_pos : 0 < m := orderOf_pos c
    have : NeZero m := ⟨hm_pos.ne'⟩
    -- Every u ∈ (ZMod m)ˣ gives an eigenspace of dimension ≥ finrank (E c)
    have hle_eig : ∀ u : (ZMod m)ˣ,
        Module.finrank (ZMod p) (E (c : ZMod p)) ≤
        Module.finrank (ZMod p) (E ((c : ZMod p) ^ (u : ZMod m).val)) := by
      intro u
      have hu_cop : m.Coprime (u : ZMod m).val := (ZMod.val_coe_unit_coprime u).symm
      obtain ⟨k, hkm, hkg⟩ := coprime_lift (N := orderOf g) (orderOf_pos g).ne' hu_cop
      obtain ⟨h, hh⟩ := isConj_iff.mp (isConj_pow_of_coprime_orderOf hHrat g hkg)
      have hck : (c : ZMod p) ^ k = (c : ZMod p) ^ (u : ZMod m).val := by
        have h1 : c ^ k = c ^ (u : ZMod m).val := by
          rw [← pow_mod_orderOf, ← pow_mod_orderOf (n := (u : ZMod m).val)]
          exact congrArg (c ^ ·) hkm
        exact_mod_cast congrArg Units.val h1
      -- Map E (c) injectively into E (c ^ u.val) via ρ h⁻¹
      have hmaps : ∀ v ∈ E (c : ZMod p), ρ h⁻¹ v ∈ E ((c : ZMod p) ^ (u : ZMod m).val) := by
        intro v hv
        rw [Module.End.mem_eigenspace_iff]
        have hgv : ρ g v = (c : ZMod p) • v := Module.End.mem_eigenspace_iff.mp hv
        have hg_conj : g * h⁻¹ = h⁻¹ * g ^ k := by
          calc g * h⁻¹ = h⁻¹ * (h * g * h⁻¹) := by group
            _ = h⁻¹ * g ^ k := by rw [hh]
        calc (ρ g).toLinearMap (ρ h⁻¹ v) = ρ (g * h⁻¹) v := by rw [map_mul]; rfl
          _ = ρ (h⁻¹ * g ^ k) v := by rw [hg_conj]
          _ = ρ h⁻¹ (ρ (g ^ k) v) := by rw [map_mul]; rfl
          _ = ρ h⁻¹ (((c : ZMod p) ^ k) • v) := by rw [hpow_eig v k hgv]
          _ = ((c : ZMod p) ^ (u : ZMod m).val) • ρ h⁻¹ v := by rw [map_smul, hck]
      let f : E (c : ZMod p) →ₗ[ZMod p] E ((c : ZMod p) ^ (u : ZMod m).val) :=
        { toFun := fun v => ⟨ρ h⁻¹ v.1, hmaps v.1 v.2⟩
          map_add' := fun x y => Subtype.ext (map_add (ρ h⁻¹) x.1 y.1)
          map_smul' := fun r x => Subtype.ext (map_smul (ρ h⁻¹) r x.1) }
      have hf_inj : Function.Injective f := fun x y hxy =>
        Subtype.ext ((ρ h⁻¹).injective (congrArg Subtype.val hxy))
      exact LinearMap.finrank_le_finrank_of_injective hf_inj
    -- Distinct u ∈ (ZMod m)ˣ produce distinct eigenvalues c ^ u.val
    let eigVal : (ZMod m)ˣ → ZMod p := fun u => (c : ZMod p) ^ (u : ZMod m).val
    have heigVal_inj : Function.Injective eigVal := by
      intro u₁ u₂ heq
      have h1 : c ^ (u₁ : ZMod m).val = c ^ (u₂ : ZMod m).val := by
        apply Units.ext; push_cast; exact heq
      have hmod : (u₁ : ZMod m).val ≡ (u₂ : ZMod m).val [MOD m] := pow_eq_pow_iff_modEq.mp h1
      have hcast : ((u₁ : ZMod m).val : ZMod m) = ((u₂ : ZMod m).val : ZMod m) :=
        (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at hcast
      exact Units.ext hcast
    have hind : iSupIndep (fun u : (ZMod m)ˣ => E (eigVal u)) :=
      (Module.End.eigenspaces_iSupIndep (ρ g).toLinearMap).comp heigVal_inj
    have hsum_le : ∑ u : (ZMod m)ˣ, Module.finrank (ZMod p) (E (eigVal u)) ≤ d := by
      have h1 := sum_finrank_le_of_iSupIndep (fun u : (ZMod m)ˣ => E (eigVal u)) hind
      simpa [Module.finrank_fin_fun] using h1
    have hcard_u : Fintype.card (ZMod m)ˣ = Nat.totient m := ZMod.card_units_eq_totient m
    calc Module.finrank (ZMod p) (E (c : ZMod p)) * Nat.totient m
        = Fintype.card (ZMod m)ˣ * Module.finrank (ZMod p) (E (c : ZMod p)) := by
            rw [hcard_u, mul_comm]
      _ = ∑ _ : (ZMod m)ˣ, Module.finrank (ZMod p) (E (c : ZMod p)) := by
            rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
      _ ≤ ∑ u : (ZMod m)ˣ, Module.finrank (ZMod p) (E (eigVal u)) :=
            Finset.sum_le_sum (fun u _ => hle_eig u)
      _ ≤ d := hsum_le

lemma totient_le_dim {p d : ℕ} [Fact p.Prime] (hd : 0 < d)
    {H : Type*} [Group H] [Fintype H]
    (hHrat : ∀ (x : H) (n : ℕ), (Nat.card H).Coprime n → IsConj x (x ^ n))
    (ρ : H →* ((Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)))
    (heig : ∀ (v : Fin d → ZMod p), v ≠ 0 → ∀ (c : (ZMod p)ˣ), ∃ h : H, ρ h v = (c : ZMod p) • v) :
    Nat.totient (p - 1) ≤ d := by
  classical
  obtain ⟨c, hc⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hc_ord : orderOf c = p - 1 := by
    rw [← Nat.card_zpowers]
    have htop : Subgroup.zpowers c = ⊤ := by
      rw [eq_top_iff]; intro x _; exact hc x
    rw [htop, Subgroup.card_top, Nat.card_eq_fintype_card, ZMod.card_units p]
  let v₀ : Fin d → ZMod p := fun _ => 1
  have hv₀ : v₀ ≠ 0 := by
    intro h0
    have h1 : (1 : ZMod p) = 0 := congrFun h0 ⟨0, hd⟩
    exact one_ne_zero h1
  obtain ⟨g, hg⟩ := heig v₀ hv₀ c
  have hker_ne : LinearMap.ker ((ρ g).toLinearMap - (c : ZMod p) • LinearMap.id) ≠ ⊥ := by
    intro hbot
    have hv₀_mem : v₀ ∈ LinearMap.ker ((ρ g).toLinearMap - (c : ZMod p) • LinearMap.id) := by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        LinearEquiv.coe_coe, hg, sub_self]
    exact hv₀ (by simpa [hbot] using hv₀_mem)
  have hpos : 1 ≤ Module.finrank (ZMod p)
      (LinearMap.ker ((ρ g).toLinearMap - (c : ZMod p) • LinearMap.id)) := by
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker_ne
    have : Nontrivial (LinearMap.ker ((ρ g).toLinearMap - (c : ZMod p) • LinearMap.id)) :=
      ⟨⟨⟨w, hw⟩, 0, fun h => hw0 (congrArg Subtype.val h)⟩⟩
    exact Module.finrank_pos
  have hbd := eigenspace_dim_bound hHrat ρ g c
  rw [hc_ord] at hbd
  calc Nat.totient (p - 1) = 1 * Nat.totient (p - 1) := (one_mul _).symm
    _ ≤ Module.finrank (ZMod p)
          (LinearMap.ker ((ρ g).toLinearMap - (c : ZMod p) • LinearMap.id)) *
          Nat.totient (p - 1) := Nat.mul_le_mul_right _ hpos
    _ ≤ d := hbd

/- ### Component 5: Maximal Imprimitivity Decomposition and Universal Monomial Killer -/

lemma exists_maximal_imprimitivity {p d : ℕ} [Fact p.Prime] (hd : 0 < d)
    {H : Type*} [Group H] [Fintype H]
    (ρ : H →* ((Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)))
    (hirred : ∀ W : Submodule (ZMod p) (Fin d → ZMod p),
      (∀ h : H, ∀ v ∈ W, ρ h v ∈ W) → W = ⊥ ∨ W = ⊤) :
    ∃ (m : ℕ) (W : Fin m → Submodule (ZMod p) (Fin d → ZMod p)),
      1 ≤ m ∧ iSupIndep W ∧ iSup W = ⊤ ∧ (∀ i, W i ≠ ⊥) ∧
      (∀ h : H, ∃ σ : Equiv.Perm (Fin m),
        ∀ i, Submodule.map (ρ h).toLinearMap (W i) = W (σ i)) ∧
      (∀ i j : Fin m, ∃ h : H, Submodule.map (ρ h).toLinearMap (W i) = W j) ∧
      (∀ (m' : ℕ) (W' : Fin m' → Submodule (ZMod p) (Fin d → ZMod p)),
        iSupIndep W' → iSup W' = ⊤ → (∀ i, W' i ≠ ⊥) →
        (∀ h : H, ∃ σ : Equiv.Perm (Fin m'),
          ∀ i, Submodule.map (ρ h).toLinearMap (W' i) = W' (σ i)) →
        m' ≤ m) := by
  classical
  let Good : ℕ → Prop := fun m =>
    ∃ W : Fin m → Submodule (ZMod p) (Fin d → ZMod p),
      iSupIndep W ∧ iSup W = ⊤ ∧ (∀ i, W i ≠ ⊥) ∧
      (∀ h : H, ∃ σ : Equiv.Perm (Fin m),
        ∀ i, Submodule.map (ρ h).toLinearMap (W i) = W (σ i))
  have hGood_le : ∀ m, Good m → m ≤ d := by
    intro m ⟨W, hWind, _, hWne, _⟩
    have h1 := hWind.subtype_ne_bot_le_finrank
    have hcard : Fintype.card {i : Fin m // W i ≠ ⊥} = m := by
      have heq : Fintype.card {i : Fin m // W i ≠ ⊥} = Fintype.card (Fin m) :=
        Fintype.card_congr
          { toFun := fun x => x.1
            invFun := fun i => ⟨i, hWne i⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
      simpa using heq
    simpa [hcard, Module.finrank_fin_fun] using h1
  have hGood1 : Good 1 := by
    refine ⟨fun _ => ⊤, iSupIndep_subsingleton _, by simp, fun _ => ?_, fun h => ⟨1, fun _ => ?_⟩⟩
    · intro hbot
      have hv0 : (fun _ : Fin d => (1 : ZMod p)) ∈ (⊥ : Submodule (ZMod p) (Fin d → ZMod p)) := by
        rw [← hbot]; trivial
      have hv0_eq : (fun _ : Fin d => (1 : ZMod p)) = 0 := by simpa using hv0
      exact one_ne_zero (congrFun hv0_eq ⟨0, hd⟩)
    · rw [Submodule.map_top, LinearEquiv.range]
  let S := (Finset.range (d + 1)).filter Good
  have h1S : 1 ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hGood1⟩
  let m := S.max' ⟨1, h1S⟩
  have hmS : m ∈ S := Finset.max'_mem S ⟨1, h1S⟩
  have hm_ge1 : 1 ≤ m := Finset.le_max' S 1 h1S
  have hm_good : Good m := (Finset.mem_filter.mp hmS).2
  have hm_max : ∀ m', Good m' → m' ≤ m := fun m' hm' =>
    Finset.le_max' S m' (Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hGood_le m' hm')), hm'⟩)
  obtain ⟨W, hWind, hWsup, hWne, hWperm⟩ := hm_good
  -- Prove transitivity of H on {W i}
  have htrans : ∀ i j : Fin m, ∃ h : H, Submodule.map (ρ h).toLinearMap (W i) = W j := by
    have horbit : ∀ i₀ j : Fin m, ∃ h : H, Submodule.map (ρ h).toLinearMap (W i₀) = W j := by
      intro i₀
      let O : Set (Fin m) := {j : Fin m | ∃ h : H, Submodule.map (ρ h).toLinearMap (W i₀) = W j}
      let U : Submodule (ZMod p) (Fin d → ZMod p) := ⨆ j ∈ O, W j
      have hi₀O : i₀ ∈ O := ⟨1, by simp⟩
      have hU_ne : U ≠ ⊥ := by
        intro hbot
        apply hWne i₀
        apply le_antisymm _ bot_le
        rw [← hbot]
        exact le_iSup₂ (f := fun j (_ : j ∈ O) => W j) i₀ hi₀O
      have hU_inv : ∀ h : H, ∀ v ∈ U, ρ h v ∈ U := by
        intro h v hv
        obtain ⟨σ, hσ⟩ := hWperm h
        have hstep : Submodule.map (ρ h).toLinearMap U ≤ U := by
          simp only [U, Submodule.map_iSup]
          refine iSup₂_le (fun j hj => ?_)
          obtain ⟨g, hg⟩ := hj
          have hσjO : σ j ∈ O := by
            refine ⟨h * g, ?_⟩
            have hcomp : (ρ (h * g)).toLinearMap = (ρ h).toLinearMap.comp (ρ g).toLinearMap := by
              ext x; simp
            rw [hcomp, Submodule.map_comp, hg, hσ j]
          rw [hσ j]
          exact le_iSup₂ (f := fun k (_ : k ∈ O) => W k) (σ j) hσjO
        exact hstep (Submodule.mem_map_of_mem hv)
      have hU_top : U = ⊤ := (hirred U hU_inv).resolve_left hU_ne
      intro j
      by_contra hjO
      have hle : W j ≤ ⨆ (k : Fin m) (_ : k ≠ j), W k := by
        calc W j ≤ ⊤ := le_top
          _ = U := hU_top.symm
          _ ≤ ⨆ (k : Fin m) (_ : k ≠ j), W k := by
              refine iSup₂_le (fun k hkO => ?_)
              have hne : k ≠ j := fun heq => hjO (heq ▸ hkO)
              exact le_iSup₂ (f := fun k (_ : k ≠ j) => W k) k hne
      have hbot : W j = ⊥ := Disjoint.eq_bot_of_le (hWind j) hle
      exact hWne j hbot
    exact horbit
  exact ⟨m, W, hm_ge1, hWind, hWsup, hWne, hWperm, htrans,
    fun m' W' h1 h2 h3 h4 => hm_max m' ⟨W', h1, h2, h3, h4⟩⟩

lemma q_part_of_eigenvector {p d : ℕ} [Fact p.Prime]
    {H : Type*} [Group H] [Fintype H]
    (ρ : H →* ((Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)))
    {q s : ℕ} (hq : q.Prime)
    {v : Fin d → ZMod p} {lam : (ZMod p)ˣ} (hlam : orderOf lam = q ^ s)
    {g : H} (hg : ρ g v = (lam : ZMod p) • v) :
    ∃ g' : H, (∃ a : ℕ, orderOf g' = q ^ a) ∧ ρ g' v = (lam : ZMod p) • v := by
  classical
  have hpow : ∀ k : ℕ, ρ (g ^ k) v = ((lam : ZMod p) ^ k) • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', map_mul]
      change ρ g (ρ (g ^ k) v) = _
      rw [ih, map_smul, hg, smul_smul, ← pow_succ]
  let n := orderOf g
  have hn_pos : 0 < n := orderOf_pos g
  let a := n.factorization q
  let u := n / q ^ a
  have hqa_dvd : q ^ a ∣ n := Nat.ordProj_dvd n q
  have hn_eq : q ^ a * u = n := Nat.mul_div_cancel' hqa_dvd
  have hqu_cop : q.Coprime u := by
    rw [Nat.Prime.coprime_iff_not_dvd hq]
    intro hdvd
    have h1 : q ^ (a + 1) ∣ n := by
      rw [pow_succ, ← hn_eq]
      exact mul_dvd_mul_left (q ^ a) hdvd
    have hle := Nat.Prime.pow_dvd_iff_le_factorization hq hn_pos.ne' |>.mp h1
    omega
  have hqs_cop : (q ^ s).Coprime u := hqu_cop.pow_left s
  -- Pick k with u * k ≡ 1 [MOD q ^ s]
  have : NeZero (q ^ s) := ⟨(pow_pos hq.pos s).ne'⟩
  let u_unit : (ZMod (q ^ s))ˣ := ZMod.unitOfCoprime u hqs_cop.symm
  let k := (u_unit⁻¹ : (ZMod (q ^ s))ˣ).val.val
  have huk_mod : u * k ≡ 1 [MOD q ^ s] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    have hk_cast : (k : ZMod (q ^ s)) = ((u_unit⁻¹ : (ZMod (q ^ s))ˣ) : ZMod (q ^ s)) :=
      ZMod.natCast_zmod_val _
    have hu_cast : (u : ZMod (q ^ s)) = (u_unit : ZMod (q ^ s)) :=
      (ZMod.coe_unitOfCoprime u hqs_cop.symm).symm
    rw [hk_cast, hu_cast, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  refine ⟨g ^ (u * k), ?_, ?_⟩
  · have hord_dvd : orderOf (g ^ (u * k)) ∣ q ^ a := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← pow_mul, show u * k * q ^ a = n * k by rw [← hn_eq]; ring, pow_mul,
        pow_orderOf_eq_one, one_pow]
    obtain ⟨b, _, hb⟩ := (Nat.dvd_prime_pow hq).mp hord_dvd
    exact ⟨b, hb⟩
  · rw [hpow]
    have hlam_pow : lam ^ (u * k) = lam := by
      rw [← pow_mod_orderOf, hlam, show u * k % q ^ s = 1 % q ^ s from huk_mod,
        ← hlam, pow_mod_orderOf, pow_one]
    have hcast : (lam : ZMod p) ^ (u * k) = (lam : ZMod p) := by
      exact_mod_cast congrArg Units.val hlam_pow
    rw [hcast]

lemma pGroup_perm_fixedPoints_modEq_aux {q m : ℕ} [Fact q.Prime] {G : Type*} [Group G] [Fintype G]
    [MulAction G (Fin m)] (hG : IsPGroup q G) :
    m ≡ (Finset.univ.filter (fun i : Fin m => ∀ g : G, g • i = i)).card [MOD q] := by
  classical
  have hmod : Nat.card (Fin m) ≡ Nat.card (MulAction.fixedPoints G (Fin m)) [MOD q] :=
    hG.card_modEq_card_fixedPoints (Fin m)
  have hcard_m : Nat.card (Fin m) = m := by simp
  have hcard_fix : Nat.card (MulAction.fixedPoints G (Fin m)) =
      (Finset.univ.filter (fun i : Fin m => ∀ g : G, g • i = i)).card := by
    rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr
      { toFun := fun ⟨i, hi⟩ => ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun g => hi g⟩⟩
        invFun := fun ⟨i, hi⟩ => ⟨i, fun g => (Finset.mem_filter.mp hi).2 g⟩
        left_inv := fun ⟨_, _⟩ => rfl
        right_inv := fun ⟨_, _⟩ => rfl }
  rwa [hcard_m, hcard_fix] at hmod

lemma pGroup_perm_fixedPoints_modEq {q m : ℕ} [Fact q.Prime] {G : Type*} [Group G] [Fintype G]
    (hG : IsPGroup q G) (f : G →* Equiv.Perm (Fin m)) :
    m ≡ (Finset.univ.filter (fun i : Fin m => ∀ g : G, f g i = i)).card [MOD q] := by
  let act : MulAction G (Fin m) :=
    { smul := fun g i => f g i
      one_smul := fun i => by change f 1 i = i; rw [map_one]; rfl
      mul_smul := fun g₁ g₂ i => by change f (g₁ * g₂) i = f g₁ (f g₂ i); rw [map_mul]; rfl }
  exact @pGroup_perm_fixedPoints_modEq_aux q m _ G _ _ act hG

lemma universal_monomial_killer {p d : ℕ} [Fact p.Prime] (hp7 : 7 ≤ p)
    {H : Type*} [Group H] [Fintype H]
    (hHrat : ∀ (x : H) (n : ℕ), (Nat.card H).Coprime n → IsConj x (x ^ n))
    (ρ : H →* ((Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)))
    (heig : ∀ (v : Fin d → ZMod p), v ≠ 0 → ∀ (c : (ZMod p)ˣ), ∃ h : H, ρ h v = (c : ZMod p) • v)
    (m : ℕ) (hm : 1 ≤ m)
    (W : Fin m → Submodule (ZMod p) (Fin d → ZMod p))
    (hWind : iSupIndep W) (hWne : ∀ i, W i ≠ ⊥)
    (hWperm : ∀ h : H, ∃ σ : Equiv.Perm (Fin m),
      ∀ i, Submodule.map (ρ h).toLinearMap (W i) = W (σ i))
    (htrans : ∀ i j : Fin m, ∃ h : H, Submodule.map (ρ h).toLinearMap (W i) = W j) :
    ∃ (i : Fin m) (h₁ h₂ : H),
      Submodule.map (ρ h₁).toLinearMap (W i) = W i ∧
      Submodule.map (ρ h₂).toLinearMap (W i) = W i ∧
      ∃ v ∈ W i, ρ (h₁ * h₂) v ≠ ρ (h₂ * h₁) v := by
  classical
  let i₀ : Fin m := ⟨0, hm⟩
  by_contra hcomm_all
  push Not at hcomm_all
  have hH0_comm : ∀ h₁ h₂ : H,
      Submodule.map (ρ h₁).toLinearMap (W i₀) = W i₀ →
      Submodule.map (ρ h₂).toLinearMap (W i₀) = W i₀ →
      ∀ v ∈ W i₀, ρ (h₁ * h₂) v = ρ (h₂ * h₁) v := hcomm_all i₀
  -- Injectivity of W
  have hW_inj : Function.Injective W := by
    intro i j hij
    by_contra hne
    have hdisj : Disjoint (W i) (W j) := hWind.pairwiseDisjoint hne
    rw [hij, disjoint_self] at hdisj
    exact hWne j hdisj
  choose σ hσ using hWperm
  have hσ_mul : ∀ g₁ g₂ : H, σ (g₁ * g₂) = σ g₁ * σ g₂ := by
    intro g₁ g₂
    refine Equiv.ext fun i => hW_inj ?_
    have hcomp : (ρ (g₁ * g₂)).toLinearMap = (ρ g₁).toLinearMap.comp (ρ g₂).toLinearMap := by
      ext x; simp
    rw [← hσ (g₁ * g₂) i, hcomp, Submodule.map_comp, hσ g₂ i, hσ g₁ (σ g₂ i)]
    rfl
  have hσ_one : σ 1 = 1 :=
    Equiv.ext fun i => hW_inj (by simpa using (hσ 1 i).symm)
  have hσ_inv : ∀ g : H, σ g⁻¹ = (σ g)⁻¹ := fun g =>
    eq_inv_of_mul_eq_one_left (by rw [← hσ_mul, inv_mul_cancel, hσ_one])
  have hσ_pow : ∀ (g : H) (k : ℕ), σ (g ^ k) = (σ g) ^ k := by
    intro g k
    induction k with
    | zero => simpa using hσ_one
    | succ k ih => rw [pow_succ, pow_succ, hσ_mul, ih]
  -- Coset representatives t : Fin m → H and base vector u₀ ∈ W i₀ \ {0}
  choose t ht using fun i : Fin m => htrans i₀ i
  obtain ⟨u₀, hu₀W, hu₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hWne i₀)
  let e : Fin m → Fin d → ZMod p := fun i => ρ (t i) u₀
  have heW : ∀ i : Fin m, e i ∈ W i := fun i => by
    rw [← ht i]; exact Submodule.mem_map_of_mem hu₀W
  have he_ne : ∀ i : Fin m, e i ≠ 0 := fun i h0 =>
    hu₀ne ((ρ (t i)).injective (h0.trans (map_zero (ρ (t i))).symm))
  -- Block cocycle c g i = (t (σ g i))⁻¹ * g * t i ∈ Stab_H(W i₀)
  let c : H → Fin m → H := fun g i => (t (σ g i))⁻¹ * g * t i
  have hc_stab : ∀ (g : H) (i : Fin m), Submodule.map (ρ (c g i)).toLinearMap (W i₀) = W i₀ := by
    intro g i
    have h1 : Submodule.map (ρ (g * t i)).toLinearMap (W i₀) = W (σ g i) := by
      have hcomp : (ρ (g * t i)).toLinearMap = (ρ g).toLinearMap.comp (ρ (t i)).toLinearMap := by
        ext x; simp
      rw [hcomp, Submodule.map_comp, ht i, hσ g i]
    have h2 : Submodule.map (ρ (t (σ g i))⁻¹).toLinearMap (W (σ g i)) = W i₀ := by
      have hcomp : (ρ ((t (σ g i))⁻¹ * t (σ g i))).toLinearMap =
          (ρ (t (σ g i))⁻¹).toLinearMap.comp (ρ (t (σ g i))).toLinearMap := by
        ext x; simp
      calc Submodule.map (ρ (t (σ g i))⁻¹).toLinearMap (W (σ g i))
          = Submodule.map ((ρ (t (σ g i))⁻¹).toLinearMap.comp (ρ (t (σ g i))).toLinearMap)
              (W i₀) := by rw [Submodule.map_comp, ht (σ g i)]
        _ = Submodule.map (ρ ((t (σ g i))⁻¹ * t (σ g i))).toLinearMap (W i₀) := by rw [← hcomp]
        _ = W i₀ := by rw [inv_mul_cancel]; simp
    have hcomp : (ρ (c g i)).toLinearMap =
        (ρ (t (σ g i))⁻¹).toLinearMap.comp (ρ (g * t i)).toLinearMap := by
      ext x; simp [c, mul_assoc]
    rw [hcomp, Submodule.map_comp, h1, h2]
  have hact_e : ∀ (g : H) (i : Fin m), ρ g (e i) = ρ (t (σ g i)) (ρ (c g i) u₀) := fun g i => by
    have hm' : g * t i = t (σ g i) * c g i := by simp [c, mul_assoc]
    calc ρ g (e i) = ρ (g * t i) u₀ := by simp [e, map_mul]
      _ = ρ (t (σ g i) * c g i) u₀ := by rw [hm']
      _ = ρ (t (σ g i)) (ρ (c g i) u₀) := by simp [map_mul]
  -- Fixed-point evaluation multiset E_mult g is conjugacy invariant in H!
  let E_mult : H → Multiset (Fin d → ZMod p) := fun g =>
    (Finset.univ.filter (fun i : Fin m => σ g i = i)).val.map (fun i => ρ (c g i) u₀)
  have hE_conj : ∀ y g : H, E_mult (y * g * y⁻¹) = E_mult g := by
    intro y g
    let S₁ := Finset.univ.filter (fun j : Fin m => σ (y * g * y⁻¹) j = j)
    let S₂ := Finset.univ.filter (fun i : Fin m => σ g i = i)
    have hbij : S₁ = S₂.map (σ y).toEmbedding := by
      ext j
      simp only [S₁, S₂, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
        Equiv.toEmbedding_apply]
      constructor
      · intro hj
        refine ⟨(σ y)⁻¹ j, ?_, (σ y).apply_symm_apply j⟩
        rw [hσ_mul, hσ_mul, hσ_inv] at hj
        have h1 : σ y (σ g ((σ y)⁻¹ j)) = j := hj
        have h2 := congrArg (fun x => (σ y)⁻¹ x) h1
        simpa using h2
      · rintro ⟨i, hi, rfl⟩
        rw [hσ_mul, hσ_mul, hσ_inv]
        change σ y (σ g ((σ y)⁻¹ (σ y i))) = σ y i
        simp [hi]
    change S₁.val.map (fun j => ρ (c (y * g * y⁻¹) j) u₀) = S₂.val.map (fun i => ρ (c g i) u₀)
    rw [hbij, Finset.map_val, Multiset.map_map]
    refine Multiset.map_congr rfl (fun i hi => ?_)
    have hi_fix : σ g i = i := (Finset.mem_filter.mp (Finset.mem_val.mp hi)).2
    have hj_fix : σ (y * g * y⁻¹) (σ y i) = σ y i := by
      rw [hσ_mul, hσ_mul, hσ_inv]
      change σ y (σ g ((σ y)⁻¹ (σ y i))) = σ y i
      simp [hi_fix]
    have hc_conj : c (y * g * y⁻¹) (σ y i) = c y i * c g i * (c y i)⁻¹ := by
      simp only [c, hj_fix, hi_fix]
      group
    change ρ (c (y * g * y⁻¹) (σ y i)) u₀ = ρ (c g i) u₀
    rw [hc_conj]
    have hcomm1 := hH0_comm (c y i) (c g i) (hc_stab y i) (hc_stab g i)
    have hinv_stab : Submodule.map (ρ (c y i)⁻¹).toLinearMap (W i₀) = W i₀ := by
      have hcomp : (ρ ((c y i)⁻¹ * c y i)).toLinearMap =
          (ρ (c y i)⁻¹).toLinearMap.comp (ρ (c y i)).toLinearMap := by ext x; simp
      calc Submodule.map (ρ (c y i)⁻¹).toLinearMap (W i₀)
          = Submodule.map ((ρ (c y i)⁻¹).toLinearMap.comp (ρ (c y i)).toLinearMap) (W i₀) := by
              rw [Submodule.map_comp, hc_stab y i]
        _ = Submodule.map (ρ ((c y i)⁻¹ * c y i)).toLinearMap (W i₀) := by rw [← hcomp]
        _ = W i₀ := by rw [inv_mul_cancel]; simp
    have hu_inv : ρ (c y i)⁻¹ u₀ ∈ W i₀ := by
      rw [← hinv_stab]; exact Submodule.mem_map_of_mem hu₀W
    calc ρ (c y i * c g i * (c y i)⁻¹) u₀
        = ρ (c y i * c g i) (ρ (c y i)⁻¹ u₀) := by simp [map_mul]
      _ = ρ (c g i * c y i) (ρ (c y i)⁻¹ u₀) := hcomm1 _ hu_inv
      _ = ρ (c g i) (ρ (c y i * (c y i)⁻¹) u₀) := by simp [map_mul]
      _ = ρ (c g i) u₀ := by rw [mul_inv_cancel]; simp
  -- Component extraction for eigenvectors supported on a subset S ⊆ univ
  have heig_comp : ∀ (S : Finset (Fin m)) (g : H) (lam : (ZMod p)ˣ),
      ρ g (∑ i ∈ S, e i) = (lam : ZMod p) • (∑ i ∈ S, e i) →
      (∀ i : Fin m, σ g i ∈ S ↔ i ∈ S) ∧
      (∀ i ∈ S, σ g i = i → ρ (c g i) u₀ = (lam : ZMod p) • u₀) := by
    intro S g lam hgv
    -- Rewrite LHS as ∑ j ∈ S.map (σ g), w j where w j ∈ W j
    have hlhs : ρ g (∑ i ∈ S, e i) = ∑ i ∈ S, ρ (t (σ g i)) (ρ (c g i) u₀) := by
      rw [map_sum]
      exact Finset.sum_congr rfl (fun i _ => hact_e g i)
    have hcoeff : ∀ j : Fin m,
        (if (σ g)⁻¹ j ∈ S then ρ (t j) (ρ (c g ((σ g)⁻¹ j)) u₀) else 0) =
        (if j ∈ S then (lam : ZMod p) • e j else 0) := by
      intro j
      -- Sum of differences over all k : Fin m equals 0
      let diff : Fin m → Fin d → ZMod p := fun k =>
        (if (σ g)⁻¹ k ∈ S then ρ (t k) (ρ (c g ((σ g)⁻¹ k)) u₀) else 0) -
        (if k ∈ S then (lam : ZMod p) • e k else 0)
      have hdiffW : ∀ k : Fin m, diff k ∈ W k := by
        intro k
        apply (W k).sub_mem
        · split_ifs with hk
          · have h1 : ρ (c g ((σ g)⁻¹ k)) u₀ ∈ W i₀ := by
              rw [← hc_stab g ((σ g)⁻¹ k)]; exact Submodule.mem_map_of_mem hu₀W
            rw [← ht k]; exact Submodule.mem_map_of_mem h1
          · exact (W k).zero_mem
        · split_ifs with hk
          · exact (W k).smul_mem _ (heW k)
          · exact (W k).zero_mem
      have hsum_diff : ∑ k : Fin m, diff k = 0 := by
        rw [Finset.sum_sub_distrib]
        have h1 : ∑ k : Fin m,
            (if (σ g)⁻¹ k ∈ S then ρ (t k) (ρ (c g ((σ g)⁻¹ k)) u₀) else 0) =
            ∑ i ∈ S, ρ (t (σ g i)) (ρ (c g i) u₀) := by
          rw [← Finset.sum_filter]
          refine Finset.sum_bij (fun k _ => (σ g)⁻¹ k)
            (fun k hk => (Finset.mem_filter.mp hk).2)
            (fun k₁ _ k₂ _ h => (σ g)⁻¹.injective h)
            (fun i hi => ⟨σ g i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hi⟩,
              by simp⟩)
            (fun k _ => by simp)
        have h2 : ∑ k : Fin m, (if k ∈ S then (lam : ZMod p) • e k else 0) =
            (lam : ZMod p) • ∑ i ∈ S, e i := by
          rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.smul_sum]
        rw [h1, h2, ← hlhs, hgv, sub_self]
      have hdiff_eq : diff j = -(∑ k ∈ Finset.univ.erase j, diff k) := by
        have h := hsum_diff
        rw [← Finset.add_sum_erase Finset.univ diff (Finset.mem_univ j)] at h
        exact eq_neg_of_add_eq_zero_left h
      have hmem2 : diff j ∈ ⨆ (k : Fin m) (_ : k ≠ j), W k := by
        rw [hdiff_eq]
        apply Submodule.neg_mem
        apply Submodule.sum_mem
        intro k hk
        have hne : k ≠ j := (Finset.mem_erase.mp hk).1
        exact le_iSup₂ (f := fun k (_ : k ≠ j) => W k) k hne (hdiffW k)
      exact sub_eq_zero.mp (Submodule.disjoint_def.mp (hWind j) _ (hdiffW j) hmem2)
    refine ⟨?_, ?_⟩
    · intro i
      have h := hcoeff (σ g i)
      have hinv_self : (σ g)⁻¹ (σ g i) = i := by simp
      rw [hinv_self] at h
      constructor
      · intro hσi
        by_contra hi
        rw [if_neg hi, if_pos hσi] at h
        have h0 : (lam : ZMod p) • e (σ g i) = 0 := h.symm
        rcases smul_eq_zero.mp h0 with hlam0 | he0
        · exact Units.ne_zero lam hlam0
        · exact he_ne (σ g i) he0
      · intro hi
        by_contra hσi
        rw [if_pos hi, if_neg hσi] at h
        have h1 : ρ (c g i) u₀ = 0 := (ρ (t (σ g i))).injective (h.trans (map_zero _).symm)
        have h0 : u₀ = 0 := (ρ (c g i)).injective (h1.trans (map_zero _).symm)
        exact hu₀ne h0
    · intro i hi hfix
      have h := hcoeff i
      have hsymm : (σ g)⁻¹ i = i := by
        have h1 := congrArg (fun x => (σ g)⁻¹ x) hfix
        simpa using h1.symm
      rw [hsymm, if_pos hi, if_pos hi] at h
      apply (ρ (t i)).injective
      calc ρ (t i) (ρ (c g i) u₀) = (lam : ZMod p) • e i := h
        _ = (lam : ZMod p) • ρ (t i) u₀ := rfl
        _ = ρ (t i) ((lam : ZMod p) • u₀) := (map_smul _ _ _).symm
  -- Helper: q-element fixed points and powers
  have hfix_pow : ∀ (g : H) (q a r : ℕ), q.Prime → orderOf g = q ^ a → q.Coprime r →
      (∀ i : Fin m, σ (g ^ r) i = i ↔ σ g i = i) ∧
      (∀ i : Fin m, σ g i = i → c (g ^ r) i = (c g i) ^ r) := by
    intro g q a r hq hord hqr
    have hfix_iff : ∀ i : Fin m, σ (g ^ r) i = i ↔ σ g i = i := by
      intro i
      constructor
      · intro hgr
        have : NeZero (q ^ a) := ⟨(pow_pos hq.pos a).ne'⟩
        have hcop : (q ^ a).Coprime r := hqr.pow_left a
        let r_unit : (ZMod (q ^ a))ˣ := ZMod.unitOfCoprime r hcop.symm
        let s := (r_unit⁻¹ : (ZMod (q ^ a))ˣ).val.val
        have hrs : r * s ≡ 1 [MOD q ^ a] := by
          rw [← ZMod.natCast_eq_natCast_iff]
          push_cast
          have hs_cast : (s : ZMod (q ^ a)) = ((r_unit⁻¹ : (ZMod (q ^ a))ˣ) : ZMod (q ^ a)) :=
            ZMod.natCast_zmod_val _
          have hr_cast : (r : ZMod (q ^ a)) = (r_unit : ZMod (q ^ a)) :=
            (ZMod.coe_unitOfCoprime r hcop.symm).symm
          rw [hs_cast, hr_cast, ← Units.val_mul, mul_inv_cancel, Units.val_one]
        have hgp : g ^ (r * s) = g := by
          rw [← pow_mod_orderOf, hord, show r * s % q ^ a = 1 % q ^ a from hrs,
            ← hord, pow_mod_orderOf, pow_one]
        have hstep : ∀ k : ℕ, σ ((g ^ r) ^ k) i = i := by
          intro k
          induction k with
          | zero => simp [hσ_one]
          | succ k ih =>
            rw [pow_succ', hσ_mul]
            change σ (g ^ r) (σ ((g ^ r) ^ k) i) = i
            rw [ih, hgr]
        have h := hstep s
        rwa [← pow_mul, hgp] at h
      · intro hg
        have hstep : ∀ k : ℕ, σ (g ^ k) i = i := by
          intro k
          induction k with
          | zero => simp [hσ_one]
          | succ k ih =>
            rw [pow_succ', hσ_mul]
            change σ g (σ (g ^ k) i) = i
            rw [ih, hg]
        exact hstep r
    refine ⟨hfix_iff, fun i hi => ?_⟩
    have hfi : σ (g ^ r) i = i := (hfix_iff i).mpr hi
    simp only [c, hi, hfi]
    have hconj_r : ∀ k : ℕ, ((t i)⁻¹ * g * t i) ^ k = (t i)⁻¹ * g ^ k * t i := by
      intro k
      induction k with
      | zero => group
      | succ k ih =>
        rw [pow_succ, ih, pow_succ]
        group
    exact (hconj_r r).symm
  -- Helper: number of fixed points of a q-element g on Fin m is ≡ m [MOD q]
  have hfix_mod : ∀ (g : H) (q a : ℕ), q.Prime → orderOf g = q ^ a →
      m ≡ (Finset.univ.filter (fun i : Fin m => σ g i = i)).card [MOD q] := by
    intro g q a hq hord
    have hq_fact : Fact q.Prime := ⟨hq⟩
    let Gq := Subgroup.zpowers g
    have hGq_p : IsPGroup q Gq := by
      rw [IsPGroup.iff_card]
      exact ⟨a, by rw [Nat.card_zpowers, hord]⟩
    let fGq : Gq →* Equiv.Perm (Fin m) :=
      { toFun := fun x => σ (x : H)
        map_one' := hσ_one
        map_mul' := fun x y => hσ_mul (x : H) (y : H) }
    have hmod := @pGroup_perm_fixedPoints_modEq q m hq_fact Gq _ _ hGq_p fGq
    have hfilt : Finset.univ.filter (fun i : Fin m => ∀ x : Gq, fGq x i = i) =
        Finset.univ.filter (fun i : Fin m => σ g i = i) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hall; exact hall ⟨g, Subgroup.mem_zpowers g⟩
      · intro hgi ⟨x, hx⟩
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        change σ (g ^ k) i = i
        have hstep : ∀ n : ℕ, σ (g ^ n) i = i := by
          intro n
          induction n with
          | zero => simp [hσ_one]
          | succ n ih =>
            rw [pow_succ', hσ_mul]
            change σ g (σ (g ^ n) i) = i
            rw [ih, hgi]
        have hg_inv : σ g⁻¹ i = i := by
          rw [hσ_inv]
          exact (Equiv.symm_apply_eq (σ g)).mpr hgi.symm
        cases k with
        | ofNat n => simpa using hstep n
        | negSucc n =>
          have hinv_step : ∀ n : ℕ, σ ((g⁻¹) ^ n) i = i := by
            intro n
            induction n with
            | zero => simp [hσ_one]
            | succ n ih =>
              rw [pow_succ', hσ_mul]
              change σ g⁻¹ (σ ((g⁻¹) ^ n) i) = i
              rw [ih, hg_inv]
          simpa [zpow_negSucc, inv_pow] using hinv_step (n + 1)
    rwa [hfilt] at hmod
  -- Helper: given (q, s, lam) with orderOf lam = q^s and q ∣ m? First prove q ∣ m via v₀!
  have hq_dvd_m : ∀ (q s r : ℕ) (lam : (ZMod p)ˣ),
      q.Prime → orderOf lam = q ^ s → q.Coprime r → lam ^ r ≠ lam → q ∣ m := by
    intro q s r lam hq hlam hqr hlam_ne
    let v₀ : Fin d → ZMod p := ∑ i : Fin m, e i
    have hv₀_ne : v₀ ≠ 0 := by
      intro h0
      have h1 : e i₀ = -(∑ i ∈ Finset.univ.erase i₀, e i) := by
        have hsum : e i₀ + ∑ i ∈ Finset.univ.erase i₀, e i = 0 := by
          rw [Finset.add_sum_erase Finset.univ e (Finset.mem_univ i₀)]; exact h0
        exact eq_neg_of_add_eq_zero_left hsum
      have hmem2 : e i₀ ∈ ⨆ (i : Fin m) (_ : i ≠ i₀), W i := by
        rw [h1]
        apply Submodule.neg_mem
        apply Submodule.sum_mem
        intro i hi
        exact le_iSup₂ (f := fun j (_ : j ≠ i₀) => W j) i (Finset.mem_erase.mp hi).1 (heW i)
      exact he_ne i₀ (Submodule.disjoint_def.mp (hWind i₀) _ (heW i₀) hmem2)
    obtain ⟨g, hg⟩ := heig v₀ hv₀_ne lam
    obtain ⟨g', ⟨a, ha⟩, hg'⟩ := q_part_of_eigenvector ρ hq hlam hg
    have hcomp := (heig_comp Finset.univ g' lam hg').2
    have hfix_empty : Finset.univ.filter (fun i : Fin m => σ g' i = i) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro i hi
      have hfi : σ g' i = i := (Finset.mem_filter.mp hi).2
      have hcop : (orderOf g').Coprime r := ha ▸ hqr.pow_left a
      obtain ⟨y, hy⟩ := isConj_iff.mp (isConj_pow_of_coprime_orderOf hHrat g' hcop)
      have hEmult : E_mult (g' ^ r) = E_mult g' := by rw [← hy, hE_conj]
      have hmem : (lam : ZMod p) • u₀ ∈ E_mult g' := by
        refine Multiset.mem_map.mpr ⟨i, Finset.mem_val.mpr hi, hcomp i (Finset.mem_univ i) hfi⟩
      rw [← hEmult] at hmem
      obtain ⟨j, hj, hjval⟩ := Multiset.mem_map.mp hmem
      have hfj_r : σ (g' ^ r) j = j := (Finset.mem_filter.mp (Finset.mem_val.mp hj)).2
      have hfj : σ g' j = j := ((hfix_pow g' q a r hq ha hqr).1 j).mp hfj_r
      have hcj : c (g' ^ r) j = (c g' j) ^ r := (hfix_pow g' q a r hq ha hqr).2 j hfj
      have hpow_c : ∀ k : ℕ, ρ ((c g' j) ^ k) u₀ = ((lam : ZMod p) ^ k) • u₀ := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          rw [pow_succ', map_mul]
          change ρ (c g' j) (ρ ((c g' j) ^ k) u₀) = _
          rw [ih, map_smul, hcomp j (Finset.mem_univ j) hfj, smul_smul, ← pow_succ]
      rw [hcj, hpow_c r] at hjval
      have hsub : ((lam : ZMod p) ^ r - (lam : ZMod p)) • u₀ = 0 := by
        rw [sub_smul, hjval, sub_self]
      rcases smul_eq_zero.mp hsub with h0 | hu0
      · exact hlam_ne (Units.ext (by push_cast; exact sub_eq_zero.mp h0))
      · exact hu₀ne hu0
    have hmod := hfix_mod g' q a hq ha
    rw [hfix_empty, Finset.card_empty] at hmod
    exact Nat.dvd_of_mod_eq_zero hmod
  -- Helper: construct element of given order dividing p - 1 in (ZMod p)ˣ
  have hex_unit_ord : ∀ k : ℕ, k ∣ p - 1 → ∃ lam : (ZMod p)ˣ, orderOf lam = k := by
    intro k hk
    obtain ⟨gen, hgen⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
    have hgen_ord : orderOf gen = p - 1 := by
      rw [← Nat.card_zpowers]
      have htop : Subgroup.zpowers gen = ⊤ := by rw [eq_top_iff]; intro x _; exact hgen x
      rw [htop, Subgroup.card_top, Nat.card_eq_fintype_card, ZMod.card_units p]
    obtain ⟨b, hb⟩ := hk
    have hk_pos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · simp at hb; omega
      · exact hpos
    have hb_pos : 0 < b := by
      rcases Nat.eq_zero_or_pos b with rfl | hpos
      · simp at hb; omega
      · exact hpos
    refine ⟨gen ^ b, ?_⟩
    have hgcd : (k * b).gcd b = b := Nat.gcd_eq_right (dvd_mul_left b k)
    rw [orderOf_pow, hgen_ord, hb, hgcd, Nat.mul_div_cancel k hb_pos]
  -- Case split on whether p - 1 has an odd prime divisor q ≥ 3, or is a power of 2 (so 8 ∣ p - 1)
  by_cases hodd : ∃ q : ℕ, q.Prime ∧ 3 ≤ q ∧ q ∣ p - 1
  · obtain ⟨q, hq, hq3, hq_dvd⟩ := hodd
    obtain ⟨lam, hlam⟩ := hex_unit_ord q hq_dvd
    have hlam_s : orderOf lam = q ^ 1 := by simpa using hlam
    have hqr : q.Coprime (q - 1) := by
      cases hq' : q with
      | zero => omega
      | succ k =>
        change Nat.gcd (k + 1) k = 1
        rw [Nat.gcd_comm, Nat.gcd_rec]; simp
    have hlam_ne : lam ^ (q - 1) ≠ lam := by
      intro heq
      have hmod : q - 1 ≡ 1 [MOD orderOf lam] := pow_eq_pow_iff_modEq.mp (by simpa using heq)
      rw [hlam] at hmod
      have h1 : (q - 1) % q = q - 1 := Nat.mod_eq_of_lt (by omega)
      have h2 : 1 % q = 1 := Nat.mod_eq_of_lt (by omega)
      change (q - 1) % q = 1 % q at hmod
      rw [h1, h2] at hmod
      omega
    have hqm : q ∣ m := hq_dvd_m q 1 (q - 1) lam hq hlam_s hqr hlam_ne
    have hm2 : 2 ≤ m := le_trans (by omega) (Nat.le_of_dvd (by omega) hqm)
    -- Step B on v₁ = ∑ i ∈ univ.erase i₀, e i
    let S₁ := Finset.univ.erase i₀
    have hS₁_ne : S₁.Nonempty := by
      have hcard : S₁.card = m - 1 := by simp [S₁]
      exact Finset.card_pos.mp (by omega)
    let v₁ : Fin d → ZMod p := ∑ i ∈ S₁, e i
    have hv₁_ne : v₁ ≠ 0 := by
      obtain ⟨j₁, hj₁⟩ := hS₁_ne
      intro h0
      have h1 : e j₁ = -(∑ i ∈ S₁.erase j₁, e i) := by
        have hsum : e j₁ + ∑ i ∈ S₁.erase j₁, e i = 0 := by
          rw [Finset.add_sum_erase S₁ e hj₁]; exact h0
        exact eq_neg_of_add_eq_zero_left hsum
      have hmem2 : e j₁ ∈ ⨆ (i : Fin m) (_ : i ≠ j₁), W i := by
        rw [h1]
        apply Submodule.neg_mem
        apply Submodule.sum_mem
        intro i hi
        exact le_iSup₂ (f := fun j (_ : j ≠ j₁) => W j) i (Finset.mem_erase.mp hi).1 (heW i)
      exact he_ne j₁ (Submodule.disjoint_def.mp (hWind j₁) _ (heW j₁) hmem2)
    obtain ⟨g₁, hg₁⟩ := heig v₁ hv₁_ne lam
    obtain ⟨g₁', ⟨a, ha⟩, hg₁'⟩ := q_part_of_eigenvector ρ hq hlam_s hg₁
    have hcomp₁ := heig_comp S₁ g₁' lam hg₁'
    have hfix_i₀ : σ g₁' i₀ = i₀ := by
      have h := (hcomp₁.1 i₀).not.mpr (Finset.notMem_erase i₀ Finset.univ)
      by_contra hne
      exact h (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩)
    let F := S₁.filter (fun i : Fin m => σ g₁' i = i)
    have hfix_split : Finset.univ.filter (fun i : Fin m => σ g₁' i = i) = insert i₀ F := by
      ext i
      simp only [F, S₁, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_erase]
      constructor
      · intro hi
        by_cases h : i = i₀
        · exact Or.inl h
        · exact Or.inr ⟨⟨h, trivial⟩, hi⟩
      · rintro (rfl | ⟨_, hi⟩)
        · exact hfix_i₀
        · exact hi
    have hi₀_notF : i₀ ∉ F := fun h => (Finset.mem_erase.mp (Finset.mem_filter.mp h).1).1 rfl
    have hF_mod : q ∣ F.card + 1 := by
      have hmod := hfix_mod g₁' q a hq ha
      rw [hfix_split, Finset.card_insert_of_notMem hi₀_notF] at hmod
      exact Nat.modEq_zero_iff_dvd.mp ((hmod.symm).trans (Nat.modEq_zero_iff_dvd.mpr hqm))
    have hF_ge2 : 2 ≤ F.card := by
      have hpos : 0 < F.card + 1 := Nat.succ_pos _
      have hle := Nat.le_of_dvd hpos hF_mod
      omega
    -- Compare counts of (lam ^ (q - 1)) • u₀ in E_mult g₁' = E_mult (g₁' ^ (q - 1))
    let r := q - 1
    have hcop : (orderOf g₁').Coprime r := ha ▸ hqr.pow_left a
    obtain ⟨y, hy⟩ := isConj_iff.mp (isConj_pow_of_coprime_orderOf hHrat g₁' hcop)
    have hEmult : E_mult (g₁' ^ r) = E_mult g₁' := by rw [← hy, hE_conj]
    let target : Fin d → ZMod p := ((lam : ZMod p) ^ r) • u₀
    have htarget_ne : target ≠ (lam : ZMod p) • u₀ := by
      intro heq
      change ((lam : ZMod p) ^ r) • u₀ = (lam : ZMod p) • u₀ at heq
      have hsub : ((lam : ZMod p) ^ r - (lam : ZMod p)) • u₀ = 0 := by
        rw [sub_smul, heq, sub_self]
      rcases smul_eq_zero.mp hsub with h0 | hu0
      · exact hlam_ne (Units.ext (by push_cast; exact sub_eq_zero.mp h0))
      · exact hu₀ne hu0
    have hcount_le1 : Multiset.count target (E_mult g₁') ≤ 1 := by
      change Multiset.count target
        ((Finset.univ.filter (fun i : Fin m => σ g₁' i = i)).val.map (fun i => ρ (c g₁' i) u₀)) ≤ 1
      rw [hfix_split, Finset.insert_val_of_notMem hi₀_notF, Multiset.map_cons, Multiset.count_cons]
      have hzero : Multiset.count target (F.val.map (fun i => ρ (c g₁' i) u₀)) = 0 := by
        rw [Multiset.count_eq_zero]
        intro hmem
        obtain ⟨i, hiF, hival⟩ := Multiset.mem_map.mp hmem
        have hiS : i ∈ S₁ := (Finset.mem_filter.mp (Finset.mem_val.mp hiF)).1
        have hifi : σ g₁' i = i := (Finset.mem_filter.mp (Finset.mem_val.mp hiF)).2
        rw [hcomp₁.2 i hiS hifi] at hival
        exact htarget_ne hival.symm
      rw [hzero]
      split_ifs <;> omega
    have hcount_ge : F.card ≤ Multiset.count target (E_mult (g₁' ^ r)) := by
      have hfix_r : Finset.univ.filter (fun i : Fin m => σ (g₁' ^ r) i = i) =
          Finset.univ.filter (fun i : Fin m => σ g₁' i = i) := by
        ext i; simp [(hfix_pow g₁' q a r hq ha hqr).1 i]
      change F.card ≤ Multiset.count target
        ((Finset.univ.filter (fun i : Fin m => σ (g₁' ^ r) i = i)).val.map
          (fun i => ρ (c (g₁' ^ r) i) u₀))
      rw [hfix_r, hfix_split, Finset.insert_val_of_notMem hi₀_notF, Multiset.map_cons,
        Multiset.count_cons]
      have hmap_const : F.val.map (fun i => ρ (c (g₁' ^ r) i) u₀) =
          Multiset.replicate F.card target := by
        have hpoint : ∀ i ∈ F.val, ρ (c (g₁' ^ r) i) u₀ = target := by
          intro i hiF
          have hiS : i ∈ S₁ := (Finset.mem_filter.mp (Finset.mem_val.mp hiF)).1
          have hifi : σ g₁' i = i := (Finset.mem_filter.mp (Finset.mem_val.mp hiF)).2
          rw [(hfix_pow g₁' q a r hq ha hqr).2 i hifi]
          have hpow_c : ∀ k : ℕ, ρ ((c g₁' i) ^ k) u₀ = ((lam : ZMod p) ^ k) • u₀ := by
            intro k
            induction k with
            | zero => simp
            | succ k ih =>
              rw [pow_succ', map_mul]
              change ρ (c g₁' i) (ρ ((c g₁' i) ^ k) u₀) = _
              rw [ih, map_smul, hcomp₁.2 i hiS hifi, smul_smul, ← pow_succ]
          exact hpow_c r
        rw [Multiset.map_congr rfl hpoint, Multiset.map_const', Finset.card_def]
      rw [hmap_const, Multiset.count_replicate_self]
      omega
    rw [hEmult] at hcount_ge
    omega
  · -- No odd prime divides p - 1, so p - 1 = 2 ^ k ≥ 6 implies 8 ∣ p - 1
    push Not at hodd
    have h8_dvd : 8 ∣ p - 1 := by
      have hpow2 : ∃ k : ℕ, p - 1 = 2 ^ k := by
        refine ⟨(p - 1).factorization 2, ?_⟩
        by_contra hne
        have hpos : 0 < p - 1 := by omega
        have hdvd : 2 ^ ((p - 1).factorization 2) ∣ p - 1 := Nat.ordProj_dvd (p - 1) 2
        let u := (p - 1) / 2 ^ ((p - 1).factorization 2)
        have hu_eq : 2 ^ ((p - 1).factorization 2) * u = p - 1 := Nat.mul_div_cancel' hdvd
        have hu_ne1 : u ≠ 1 := by intro h1; rw [h1, mul_one] at hu_eq; exact hne hu_eq.symm
        obtain ⟨q, hq, hqu⟩ := Nat.exists_prime_and_dvd hu_ne1
        have hq_dvd : q ∣ p - 1 := dvd_trans hqu (hu_eq ▸ dvd_mul_left u _)
        have hq_ne2 : q ≠ 2 := by
          intro h2
          subst h2
          have h1 : 2 ^ ((p - 1).factorization 2 + 1) ∣ p - 1 := by
            calc 2 ^ ((p - 1).factorization 2 + 1)
                = 2 ^ ((p - 1).factorization 2) * 2 := pow_succ _ _
              _ ∣ 2 ^ ((p - 1).factorization 2) * u := mul_dvd_mul_left _ hqu
              _ = p - 1 := hu_eq
          have hle := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hpos.ne').mp h1
          omega
        have hq3 : 3 ≤ q := by have := hq.two_le; omega
        exact hodd q hq hq3 hq_dvd
      obtain ⟨k, hk⟩ := hpow2
      have hk3 : 3 ≤ k := by
        by_contra hlt
        have hle : k ≤ 2 := by omega
        interval_cases k <;> omega
      rw [hk]
      exact pow_dvd_pow 2 hk3
    obtain ⟨lam, hlam⟩ := hex_unit_ord 8 h8_dvd
    have hlam_s : orderOf lam = 2 ^ 3 := by simpa using hlam
    have hlam_ne3 : lam ^ 3 ≠ lam := by
      intro heq
      have hmod : 3 ≡ 1 [MOD orderOf lam] := pow_eq_pow_iff_modEq.mp (by simpa using heq)
      rw [hlam] at hmod
      change 3 % 8 = 1 % 8 at hmod
      omega
    have hlam_ne5 : lam ^ 5 ≠ lam := by
      intro heq
      have hmod : 5 ≡ 1 [MOD orderOf lam] := pow_eq_pow_iff_modEq.mp (by simpa using heq)
      rw [hlam] at hmod
      change 5 % 8 = 1 % 8 at hmod
      omega
    have hlam_35 : lam ^ 3 ≠ lam ^ 5 := by
      intro heq
      have hmod : 3 ≡ 5 [MOD orderOf lam] := pow_eq_pow_iff_modEq.mp heq
      rw [hlam] at hmod
      change 3 % 8 = 5 % 8 at hmod
      omega
    have h2m : 2 ∣ m := hq_dvd_m 2 3 3 lam Nat.prime_two hlam_s (by decide) hlam_ne3
    have hm2 : 2 ≤ m := Nat.le_of_dvd (by omega) h2m
    -- Step B on v₁ = ∑ i ∈ univ.erase i₀, e i
    let S₁ := Finset.univ.erase i₀
    have hS₁_ne : S₁.Nonempty := by
      have hcard : S₁.card = m - 1 := by simp [S₁]
      exact Finset.card_pos.mp (by omega)
    let v₁ : Fin d → ZMod p := ∑ i ∈ S₁, e i
    have hv₁_ne : v₁ ≠ 0 := by
      obtain ⟨j₁, hj₁⟩ := hS₁_ne
      intro h0
      have h1 : e j₁ = -(∑ i ∈ S₁.erase j₁, e i) := by
        have hsum : e j₁ + ∑ i ∈ S₁.erase j₁, e i = 0 := by
          rw [Finset.add_sum_erase S₁ e hj₁]; exact h0
        exact eq_neg_of_add_eq_zero_left hsum
      have hmem2 : e j₁ ∈ ⨆ (i : Fin m) (_ : i ≠ j₁), W i := by
        rw [h1]
        apply Submodule.neg_mem
        apply Submodule.sum_mem
        intro i hi
        exact le_iSup₂ (f := fun j (_ : j ≠ j₁) => W j) i (Finset.mem_erase.mp hi).1 (heW i)
      exact he_ne j₁ (Submodule.disjoint_def.mp (hWind j₁) _ (heW j₁) hmem2)
    obtain ⟨g₁, hg₁⟩ := heig v₁ hv₁_ne lam
    obtain ⟨g₁', ⟨a, ha⟩, hg₁'⟩ := q_part_of_eigenvector ρ Nat.prime_two hlam_s hg₁
    have hcomp₁ := heig_comp S₁ g₁' lam hg₁'
    have hfix_i₀ : σ g₁' i₀ = i₀ := by
      have h := (hcomp₁.1 i₀).not.mpr (Finset.notMem_erase i₀ Finset.univ)
      by_contra hne
      exact h (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩)
    let F := S₁.filter (fun i : Fin m => σ g₁' i = i)
    have hfix_split : Finset.univ.filter (fun i : Fin m => σ g₁' i = i) = insert i₀ F := by
      ext i
      simp only [F, S₁, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_erase]
      constructor
      · intro hi
        by_cases h : i = i₀
        · exact Or.inl h
        · exact Or.inr ⟨⟨h, trivial⟩, hi⟩
      · rintro (rfl | ⟨_, hi⟩)
        · exact hfix_i₀
        · exact hi
    have hi₀_notF : i₀ ∉ F := fun h => (Finset.mem_erase.mp (Finset.mem_filter.mp h).1).1 rfl
    have hF_mod : 2 ∣ F.card + 1 := by
      have hmod := hfix_mod g₁' 2 a Nat.prime_two ha
      rw [hfix_split, Finset.card_insert_of_notMem hi₀_notF] at hmod
      exact Nat.modEq_zero_iff_dvd.mp ((hmod.symm).trans (Nat.modEq_zero_iff_dvd.mpr h2m))
    have hF_nonempty : F.Nonempty := by
      have hpos : 0 < F.card := by
        have hle := Nat.le_of_dvd (Nat.succ_pos _) hF_mod
        omega
      exact Finset.card_pos.mp hpos
    obtain ⟨j₀, hj₀F⟩ := hF_nonempty
    have hj₀S : j₀ ∈ S₁ := (Finset.mem_filter.mp hj₀F).1
    have hj₀fix : σ g₁' j₀ = j₀ := (Finset.mem_filter.mp hj₀F).2
    -- Every element of E_mult g₁' is either lam • u₀ or ρ (c g₁' i₀) u₀
    have hmem_two : ∀ x ∈ E_mult g₁', x = (lam : ZMod p) • u₀ ∨ x = ρ (c g₁' i₀) u₀ := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hx
      have hi' : i ∈ insert i₀ F := hfix_split ▸ Finset.mem_val.mp hi
      rcases Finset.mem_insert.mp hi' with rfl | hiF
      · exact Or.inr rfl
      · left
        exact hcomp₁.2 i (Finset.mem_filter.mp hiF).1 (Finset.mem_filter.mp hiF).2
    -- Both (lam^3) • u₀ and (lam^5) • u₀ lie in E_mult g₁'
    have hmem_pow : ∀ r : ℕ, (2 : ℕ).Coprime r → ((lam : ZMod p) ^ r) • u₀ ∈ E_mult g₁' := by
      intro r hr
      have hcop : (orderOf g₁').Coprime r := ha ▸ hr.pow_left a
      obtain ⟨y, hy⟩ := isConj_iff.mp (isConj_pow_of_coprime_orderOf hHrat g₁' hcop)
      have hEmult : E_mult (g₁' ^ r) = E_mult g₁' := by rw [← hy, hE_conj]
      rw [← hEmult]
      have hj₀r : σ (g₁' ^ r) j₀ = j₀ := ((hfix_pow g₁' 2 a r Nat.prime_two ha hr).1 j₀).mpr hj₀fix
      refine Multiset.mem_map.mpr ⟨j₀, Finset.mem_val.mpr
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj₀r⟩), ?_⟩
      rw [(hfix_pow g₁' 2 a r Nat.prime_two ha hr).2 j₀ hj₀fix]
      have hpow_c : ∀ k : ℕ, ρ ((c g₁' j₀) ^ k) u₀ = ((lam : ZMod p) ^ k) • u₀ := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          rw [pow_succ', map_mul]
          change ρ (c g₁' j₀) (ρ ((c g₁' j₀) ^ k) u₀) = _
          rw [ih, map_smul, hcomp₁.2 j₀ hj₀S hj₀fix, smul_smul, ← pow_succ]
      exact hpow_c r
    have h3eq : ((lam : ZMod p) ^ 3) • u₀ = ρ (c g₁' i₀) u₀ := by
      rcases hmem_two _ (hmem_pow 3 (by decide)) with hbad | hok
      · exfalso
        have hsub : ((lam : ZMod p) ^ 3 - (lam : ZMod p)) • u₀ = 0 := by
          rw [sub_smul, hbad, sub_self]
        rcases smul_eq_zero.mp hsub with h0 | hu0
        · exact hlam_ne3 (Units.ext (by push_cast; exact sub_eq_zero.mp h0))
        · exact hu₀ne hu0
      · exact hok
    have h5eq : ((lam : ZMod p) ^ 5) • u₀ = ρ (c g₁' i₀) u₀ := by
      rcases hmem_two _ (hmem_pow 5 (by decide)) with hbad | hok
      · exfalso
        have hsub : ((lam : ZMod p) ^ 5 - (lam : ZMod p)) • u₀ = 0 := by
          rw [sub_smul, hbad, sub_self]
        rcases smul_eq_zero.mp hsub with h0 | hu0
        · exact hlam_ne5 (Units.ext (by push_cast; exact sub_eq_zero.mp h0))
        · exact hu₀ne hu0
      · exact hok
    have h35 : ((lam : ZMod p) ^ 3 - (lam : ZMod p) ^ 5) • u₀ = 0 := by
      rw [sub_smul, h3eq, h5eq, sub_self]
    rcases smul_eq_zero.mp h35 with h0 | hu0
    · exact hlam_35 (Units.ext (by push_cast; exact sub_eq_zero.mp h0))
    · exact hu₀ne hu0

/- ### Component 6: Clifford Isotypic Decomposition and Block-Stabilizer Primitivity -/

lemma block_stabilizer_irred_primitive {p d : ℕ} [Fact p.Prime]
    {H : Type*} [Group H] [Fintype H] (hpH : ¬ (p ∣ Nat.card H))
    (ρ : H →* ((Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)))
    (m : ℕ) (hm : 1 ≤ m)
    (W : Fin m → Submodule (ZMod p) (Fin d → ZMod p))
    (hWind : iSupIndep W) (hWsup : iSup W = ⊤) (_hWne : ∀ i, W i ≠ ⊥)
    (hWperm : ∀ h : H, ∃ σ : Equiv.Perm (Fin m),
      ∀ i, Submodule.map (ρ h).toLinearMap (W i) = W (σ i))
    (htrans : ∀ i j : Fin m, ∃ h : H, Submodule.map (ρ h).toLinearMap (W i) = W j)
    (hmax : ∀ (m' : ℕ) (W' : Fin m' → Submodule (ZMod p) (Fin d → ZMod p)),
      iSupIndep W' → iSup W' = ⊤ → (∀ i, W' i ≠ ⊥) →
      (∀ h : H, ∃ σ : Equiv.Perm (Fin m'),
        ∀ i, Submodule.map (ρ h).toLinearMap (W' i) = W' (σ i)) →
      m' ≤ m) :
    let i₀ : Fin m := ⟨0, hm⟩
    let H₀ : Subgroup H :=
      { carrier := {h : H | Submodule.map (ρ h).toLinearMap (W i₀) = W i₀}
        mul_mem' := fun {a b} ha hb => by
          change Submodule.map (ρ (a * b)).toLinearMap (W i₀) = W i₀
          have hcomp : (ρ (a * b)).toLinearMap = (ρ a).toLinearMap.comp (ρ b).toLinearMap := by
            ext x; simp
          rw [hcomp, Submodule.map_comp, hb, ha]
        one_mem' := by simp
        inv_mem' := fun {a} ha => by
          change Submodule.map (ρ a⁻¹).toLinearMap (W i₀) = W i₀
          have hcomp : (ρ (a⁻¹ * a)).toLinearMap = (ρ a⁻¹).toLinearMap.comp (ρ a).toLinearMap := by
            ext x; simp
          calc Submodule.map (ρ a⁻¹).toLinearMap (W i₀)
              = Submodule.map ((ρ a⁻¹).toLinearMap.comp (ρ a).toLinearMap) (W i₀) := by
                  rw [Submodule.map_comp, ha]
            _ = Submodule.map (ρ (a⁻¹ * a)).toLinearMap (W i₀) := by rw [← hcomp]
            _ = W i₀ := by rw [inv_mul_cancel]; simp }
    (∀ U : Submodule (ZMod p) (Fin d → ZMod p), U ≤ W i₀ →
      (∀ h : H₀, ∀ v ∈ U, ρ (h : H) v ∈ U) → U = ⊥ ∨ U = W i₀) ∧
    (∀ (r : ℕ) (U : Fin r → Submodule (ZMod p) (Fin d → ZMod p)),
      2 ≤ r → iSupIndep U → iSup U = W i₀ → (∀ a, U a ≠ ⊥) →
      ¬ ∀ h : H₀, ∃ τ : Equiv.Perm (Fin r),
        ∀ a, Submodule.map (ρ (h : H)).toLinearMap (U a) = U (τ a)) := by
  classical
  let i₀ : Fin m := ⟨0, hm⟩
  let H₀ : Subgroup H :=
    { carrier := {h : H | Submodule.map (ρ h).toLinearMap (W i₀) = W i₀}
      mul_mem' := fun {a b} ha hb => by
        change Submodule.map (ρ (a * b)).toLinearMap (W i₀) = W i₀
        have hcomp : (ρ (a * b)).toLinearMap = (ρ a).toLinearMap.comp (ρ b).toLinearMap := by
          ext x; simp
        rw [hcomp, Submodule.map_comp, hb, ha]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        change Submodule.map (ρ a⁻¹).toLinearMap (W i₀) = W i₀
        have hcomp : (ρ (a⁻¹ * a)).toLinearMap = (ρ a⁻¹).toLinearMap.comp (ρ a).toLinearMap := by
          ext x; simp
        calc Submodule.map (ρ a⁻¹).toLinearMap (W i₀)
            = Submodule.map ((ρ a⁻¹).toLinearMap.comp (ρ a).toLinearMap) (W i₀) := by
                rw [Submodule.map_comp, ha]
          _ = Submodule.map (ρ (a⁻¹ * a)).toLinearMap (W i₀) := by rw [← hcomp]
          _ = W i₀ := by rw [inv_mul_cancel]; simp }
  -- Helper: transporting any r-block imprimitivity decomposition of W i₀ yields an (m * r)-block decomposition of V
  have hrefine : ∀ (r : ℕ) (U : Fin r → Submodule (ZMod p) (Fin d → ZMod p)),
      2 ≤ r → iSupIndep U → iSup U = W i₀ → (∀ a, U a ≠ ⊥) →
      (∀ h : H₀, ∃ τ : Equiv.Perm (Fin r),
        ∀ a, Submodule.map (ρ (h : H)).toLinearMap (U a) = U (τ a)) → False := by
    intro r U hr2 hUind hUsup hUne hUperm
    choose t ht using fun i : Fin m => htrans i₀ i
    choose σ hσ using hWperm
    -- Define W' on Fin (m * r) via finProdFinEquiv
    let W' : Fin (m * r) → Submodule (ZMod p) (Fin d → ZMod p) := fun k =>
      let ia := finProdFinEquiv.symm k
      Submodule.map (ρ (t ia.1)).toLinearMap (U ia.2)
    have hW'_app : ∀ (i : Fin m) (a : Fin r),
        W' (finProdFinEquiv (i, a)) = Submodule.map (ρ (t i)).toLinearMap (U a) := fun i a => by
      simp only [W', Equiv.symm_apply_apply]
    have hW'_le_W : ∀ k : Fin (m * r), W' k ≤ W (finProdFinEquiv.symm k).1 := by
      intro k
      let ia := finProdFinEquiv.symm k
      change Submodule.map (ρ (t ia.1)).toLinearMap (U ia.2) ≤ W ia.1
      rw [← ht ia.1]
      exact Submodule.map_mono (hUsup ▸ le_iSup U ia.2)
    have hW'_ind : iSupIndep W' := by
      intro k
      obtain ⟨⟨i, a⟩, rfl⟩ : ∃ ia : Fin m × Fin r, finProdFinEquiv ia = k :=
        ⟨finProdFinEquiv.symm k, finProdFinEquiv.apply_symm_apply k⟩
      rw [hW'_app i a]
      have hsplit : ⨆ (l : Fin (m * r)) (_ : l ≠ finProdFinEquiv (i, a)), W' l ≤
          Submodule.map (ρ (t i)).toLinearMap (⨆ (b : Fin r) (_ : b ≠ a), U b) ⊔
          ⨆ (j : Fin m) (_ : j ≠ i), W j := by
        refine iSup₂_le (fun l hl => ?_)
        obtain ⟨⟨j, b⟩, rfl⟩ : ∃ jb : Fin m × Fin r, finProdFinEquiv jb = l :=
          ⟨finProdFinEquiv.symm l, finProdFinEquiv.apply_symm_apply l⟩
        by_cases hji : j = i
        · subst hji
          have hba : b ≠ a := fun heq => hl (congrArg finProdFinEquiv (Prod.ext rfl heq))
          rw [hW'_app j b]
          refine le_trans ?_ le_sup_left
          exact Submodule.map_mono (le_iSup₂ (f := fun b (_ : b ≠ a) => U b) b hba)
        · refine le_trans ?_ le_sup_right
          have hle := hW'_le_W (finProdFinEquiv (j, b))
          simp only [Equiv.symm_apply_apply] at hle
          exact le_trans hle (le_iSup₂ (f := fun j (_ : j ≠ i) => W j) j hji)
      refine Disjoint.mono_right hsplit ?_
      rw [Submodule.disjoint_def]
      intro x hx1 hx2
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hx2
      have hxW : x ∈ W i := by
        rw [← ht i]; exact Submodule.map_mono (hUsup ▸ le_iSup U a) hx1
      have hyW : y ∈ W i := by
        rw [← ht i]
        exact Submodule.map_mono (iSup₂_le fun b _ => hUsup ▸ le_iSup U b) hy
      have hz_eq : z = x - y := by rw [← hyz]; abel
      have hzW : z ∈ W i := hz_eq ▸ (W i).sub_mem hxW hyW
      have hz0 : z = 0 := Submodule.disjoint_def.mp (hWind i) z hzW hz
      rw [hz0, add_zero] at hyz
      rw [hyz] at hy
      obtain ⟨u₁, hu₁, rfl⟩ := Submodule.mem_map.mp hx1
      obtain ⟨u₂, hu₂, h2eq⟩ := Submodule.mem_map.mp hy
      have hu_eq : u₁ = u₂ := (ρ (t i)).injective h2eq.symm
      rw [hu_eq] at hu₁
      have hu20 : u₂ = 0 := Submodule.disjoint_def.mp (hUind a) u₂ hu₁ hu₂
      rw [hu_eq, hu20, map_zero]
    have hW'_sup : iSup W' = ⊤ := by
      rw [← hWsup]
      apply le_antisymm
      · refine iSup_le (fun k => le_trans (hW'_le_W k) (le_iSup W _))
      · refine iSup_le (fun i => ?_)
        rw [← ht i, ← hUsup, Submodule.map_iSup]
        refine iSup_le (fun a => ?_)
        rw [← hW'_app i a]
        exact le_iSup W' (finProdFinEquiv (i, a))
    have hW'_ne : ∀ k : Fin (m * r), W' k ≠ ⊥ := by
      intro k hbot
      let ia := finProdFinEquiv.symm k
      obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hUne ia.2)
      have hmem : ρ (t ia.1) u ∈ W' k := Submodule.mem_map_of_mem huU
      have h0 : ρ (t ia.1) u = 0 := by simpa [hbot] using hmem
      exact hu0 ((ρ (t ia.1)).injective (h0.trans (map_zero _).symm))
    have hW'_perm : ∀ h : H, ∃ π : Equiv.Perm (Fin (m * r)),
        ∀ k, Submodule.map (ρ h).toLinearMap (W' k) = W' (π k) := by
      intro h
      -- For each i : Fin m, c i = (t (σ h i))⁻¹ * h * t i ∈ H₀
      have hc_mem : ∀ i : Fin m, (t (σ h i))⁻¹ * h * t i ∈ H₀ := by
        intro i
        change Submodule.map (ρ ((t (σ h i))⁻¹ * h * t i)).toLinearMap (W i₀) = W i₀
        have h1 : Submodule.map (ρ (h * t i)).toLinearMap (W i₀) = W (σ h i) := by
          have hcomp : (ρ (h * t i)).toLinearMap = (ρ h).toLinearMap.comp (ρ (t i)).toLinearMap := by
            ext x; simp
          rw [hcomp, Submodule.map_comp, ht i, hσ h i]
        have h2 : Submodule.map (ρ (t (σ h i))⁻¹).toLinearMap (W (σ h i)) = W i₀ := by
          have hcomp : (ρ ((t (σ h i))⁻¹ * t (σ h i))).toLinearMap =
              (ρ (t (σ h i))⁻¹).toLinearMap.comp (ρ (t (σ h i))).toLinearMap := by ext x; simp
          calc Submodule.map (ρ (t (σ h i))⁻¹).toLinearMap (W (σ h i))
              = Submodule.map ((ρ (t (σ h i))⁻¹).toLinearMap.comp (ρ (t (σ h i))).toLinearMap)
                  (W i₀) := by rw [Submodule.map_comp, ht (σ h i)]
            _ = Submodule.map (ρ ((t (σ h i))⁻¹ * t (σ h i))).toLinearMap (W i₀) := by rw [← hcomp]
            _ = W i₀ := by rw [inv_mul_cancel]; simp
        have hcomp : (ρ ((t (σ h i))⁻¹ * h * t i)).toLinearMap =
            (ρ (t (σ h i))⁻¹).toLinearMap.comp (ρ (h * t i)).toLinearMap := by
          ext x; simp [mul_assoc]
        rw [hcomp, Submodule.map_comp, h1, h2]
      choose τ hτ using fun i : Fin m => hUperm ⟨(t (σ h i))⁻¹ * h * t i, hc_mem i⟩
      let eProd : Equiv.Perm (Fin m × Fin r) :=
        { toFun := fun ia => (σ h ia.1, τ ia.1 ia.2)
          invFun := fun jb => ((σ h)⁻¹ jb.1, (τ ((σ h)⁻¹ jb.1))⁻¹ jb.2)
          left_inv := fun ⟨i, a⟩ => by simp
          right_inv := fun ⟨j, b⟩ => by simp }
      refine ⟨finProdFinEquiv.symm.trans (eProd.trans finProdFinEquiv), fun k => ?_⟩
      obtain ⟨⟨i, a⟩, rfl⟩ : ∃ ia : Fin m × Fin r, finProdFinEquiv ia = k :=
        ⟨finProdFinEquiv.symm k, finProdFinEquiv.apply_symm_apply k⟩
      simp only [Equiv.trans_apply, Equiv.symm_apply_apply, eProd, Equiv.coe_fn_mk]
      rw [hW'_app i a, hW'_app (σ h i) (τ i a)]
      have hmul : h * t i = t (σ h i) * ((t (σ h i))⁻¹ * h * t i) := by group
      have hcomp1 : (ρ h).toLinearMap.comp (ρ (t i)).toLinearMap = (ρ (h * t i)).toLinearMap := by
        ext x; simp
      have hcomp2 : (ρ (t (σ h i))).toLinearMap.comp (ρ ((t (σ h i))⁻¹ * h * t i)).toLinearMap =
          (ρ (t (σ h i) * ((t (σ h i))⁻¹ * h * t i))).toLinearMap := by ext x; simp
      rw [← Submodule.map_comp, hcomp1, hmul, ← hcomp2, Submodule.map_comp, hτ i a]
    have hle := hmax (m * r) W' hW'_ind hW'_sup hW'_ne hW'_perm
    nlinarith
  refine ⟨?_, fun r U hr2 hUind hUsup hUne hUperm => hrefine r U hr2 hUind hUsup hUne hUperm⟩
  -- Prove irreducibility of H₀ on W i₀ via Maschke + hrefine (r = 2)
  intro U hUle hUinv
  by_contra hnot
  push Not at hnot
  obtain ⟨hUne, hUneW⟩ := hnot
  have hpH₀ : ¬ (p ∣ Nat.card H₀) := fun hdvd =>
    hpH (dvd_trans hdvd (Subgroup.card_subgroup_dvd_card H₀))
  have hH₀_mem : ∀ (h : H₀) (v : Fin d → ZMod p), v ∈ W i₀ → ρ (h : H) v ∈ W i₀ := fun h v hv => by
    rw [← h.2]; exact Submodule.mem_map_of_mem hv
  let φ₀ : H₀ →* ((W i₀) ≃ₗ[ZMod p] (W i₀)) :=
    { toFun := fun h =>
        LinearEquiv.ofLinearMap
          ((ρ (h : H)).toLinearMap.restrict (fun x hx => hH₀_mem h x hx))
          ((ρ ((h⁻¹ : H₀) : H)).toLinearMap.restrict (fun x hx => hH₀_mem h⁻¹ x hx))
          (LinearMap.ext fun ⟨x, hx⟩ => Subtype.ext (by
            change ρ (h : H) (ρ (h : H)⁻¹ x) = x
            have h1 : ρ (h : H) (ρ (h : H)⁻¹ x) = ρ ((h : H) * (h : H)⁻¹) x := by rw [map_mul]; rfl
            rw [h1, mul_inv_cancel, map_one]; rfl))
          (LinearMap.ext fun ⟨x, hx⟩ => Subtype.ext (by
            change ρ (h : H)⁻¹ (ρ (h : H) x) = x
            have h1 : ρ (h : H)⁻¹ (ρ (h : H) x) = ρ ((h : H)⁻¹ * (h : H)) x := by rw [map_mul]; rfl
            rw [h1, inv_mul_cancel, map_one]; rfl))
      map_one' := LinearEquiv.ext fun ⟨x, hx⟩ => Subtype.ext (by
        change ρ 1 x = x; rw [map_one]; rfl)
      map_mul' := fun a b => LinearEquiv.ext fun ⟨x, hx⟩ => Subtype.ext (by
        change ρ ((a : H) * (b : H)) x = ρ (a : H) (ρ (b : H) x); rw [map_mul]; rfl) }
  let UW : Submodule (ZMod p) (W i₀) := U.comap (W i₀).subtype
  have hUW_inv : ∀ h : H₀, ∀ u ∈ UW, φ₀ h u ∈ UW := fun h ⟨x, hx⟩ hxU => hUinv h x hxU
  obtain ⟨U'W, hU'W_inv, hcompl⟩ := maschke_complement hpH₀ φ₀ UW hUW_inv
  let U' : Submodule (ZMod p) (Fin d → ZMod p) := U'W.map (W i₀).subtype
  have hU'_le : U' ≤ W i₀ := Submodule.map_subtype_le (W i₀) U'W
  have hU'_inv : ∀ h : H₀, ∀ v ∈ U', ρ (h : H) v ∈ U' := by
    intro h v hv
    obtain ⟨⟨x, hxW⟩, hxU', rfl⟩ := Submodule.mem_map.mp hv
    exact Submodule.mem_map.mpr ⟨φ₀ h ⟨x, hxW⟩, hU'W_inv h ⟨x, hxW⟩ hxU', rfl⟩
  have hdisj : Disjoint U U' := by
    rw [Submodule.disjoint_def]
    intro x hxU hxU'
    obtain ⟨⟨y, hyW⟩, hyU', rfl⟩ := Submodule.mem_map.mp hxU'
    have h0 : (⟨y, hyW⟩ : W i₀) = 0 := Submodule.disjoint_def.mp hcompl.disjoint _ hxU hyU'
    exact congrArg Subtype.val h0
  have hsup : U ⊔ U' = W i₀ := by
    apply le_antisymm (sup_le hUle hU'_le)
    intro x hxW
    have htop : (⟨x, hxW⟩ : W i₀) ∈ UW ⊔ U'W := by rw [hcompl.codisjoint.eq_top]; trivial
    obtain ⟨u, hu, u', hu', hadd⟩ := Submodule.mem_sup.mp htop
    have hx_eq : x = (u : Fin d → ZMod p) + (u' : Fin d → ZMod p) := (congrArg Subtype.val hadd).symm
    rw [hx_eq]
    exact Submodule.add_mem_sup hu (Submodule.mem_map.mpr ⟨u', hu', rfl⟩)
  have hU'_ne : U' ≠ ⊥ := by
    intro hbot; rw [hbot, sup_bot_eq] at hsup; exact hUneW hsup
  let pairU : Fin 2 → Submodule (ZMod p) (Fin d → ZMod p) := ![U, U']
  have hpair_ind : iSupIndep pairU := by
    intro a
    fin_cases a
    · have hle : ⨆ (j : Fin 2) (_ : j ≠ 0), pairU j ≤ U' := by
        refine iSup₂_le (fun j hj => ?_)
        fin_cases j
        · exact absurd rfl hj
        · exact le_rfl
      exact Disjoint.mono_right hle hdisj
    · have hle : ⨆ (j : Fin 2) (_ : j ≠ 1), pairU j ≤ U := by
        refine iSup₂_le (fun j hj => ?_)
        fin_cases j
        · exact le_rfl
        · exact absurd rfl hj
      exact Disjoint.mono_right hle hdisj.symm
  have hpair_sup : iSup pairU = W i₀ := by
    rw [← hsup]
    apply le_antisymm
    · refine iSup_le (fun j => ?_)
      fin_cases j
      · exact le_sup_left
      · exact le_sup_right
    · exact sup_le (le_iSup pairU 0) (le_iSup pairU 1)
  have hpair_ne : ∀ a : Fin 2, pairU a ≠ ⊥ := fun a => by
    fin_cases a
    · exact hUne
    · exact hU'_ne
  have hpair_perm : ∀ h : H₀, ∃ τ : Equiv.Perm (Fin 2),
      ∀ a, Submodule.map (ρ (h : H)).toLinearMap (pairU a) = pairU (τ a) := by
    intro h
    refine ⟨1, fun a => ?_⟩
    have hmap_eq : ∀ S : Submodule (ZMod p) (Fin d → ZMod p),
        (∀ g : H₀, ∀ v ∈ S, ρ (g : H) v ∈ S) →
        Submodule.map (ρ (h : H)).toLinearMap S = S := by
      intro S hSinv
      apply le_antisymm
      · rintro _ ⟨v, hv, rfl⟩; exact hSinv h v hv
      · intro v hv
        refine ⟨ρ (h : H)⁻¹ v, hSinv h⁻¹ v hv, ?_⟩
        change ρ (h : H) (ρ (h : H)⁻¹ v) = v
        have h1 : ρ (h : H) (ρ (h : H)⁻¹ v) = ρ ((h : H) * (h : H)⁻¹) v := by rw [map_mul]; rfl
        rw [h1, mul_inv_cancel, map_one]; rfl
    fin_cases a
    · exact hmap_eq U hUinv
    · exact hmap_eq U' hU'_inv
  exact hrefine 2 pairU le_rfl hpair_ind hpair_sup hpair_ne hpair_perm

lemma clifford_homog_of_primitive {p : ℕ} [Fact p.Prime]
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V] [Nontrivial V]
    {P : Type*} [Group P] [Fintype P] (hpP : ¬ (p ∣ Nat.card P))
    (φ : P →* (V ≃ₗ[ZMod p] V)) (hfaith : Function.Injective φ)
    (hprim : ∀ (r : ℕ) (U : Fin r → Submodule (ZMod p) V),
      2 ≤ r → iSupIndep U → iSup U = ⊤ → (∀ a, U a ≠ ⊥) →
      ¬ ∀ g : P, ∃ τ : Equiv.Perm (Fin r),
        ∀ a, Submodule.map (φ g).toLinearMap (U a) = U (τ a))
    (A : Subgroup P) (hAnorm : A.Normal) (hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    IsCyclic A ∧
    ∃ (U₀ : Submodule (ZMod p) V), U₀ ≠ ⊥ ∧
      (∀ a : A, ∀ v ∈ U₀, φ (a : P) v ∈ U₀) ∧
      (∀ S : Submodule (ZMod p) V, S ≤ U₀ →
        (∀ a : A, ∀ v ∈ S, φ (a : P) v ∈ S) → S = ⊥ ∨ S = U₀) ∧
      (∀ a : A, (∀ v ∈ U₀, φ (a : P) v = v) → a = 1) ∧
      (∀ (a : A) (f : Polynomial (ZMod p)),
        (∀ v ∈ U₀, Polynomial.aeval (φ (a : P)).toLinearMap f v = 0) →
        Polynomial.aeval (φ (a : P)).toLinearMap f = 0) := by
  classical
  have hpA : ¬ (p ∣ Nat.card A) := fun hdvd =>
    hpP (dvd_trans hdvd (Subgroup.card_subgroup_dvd_card A))
  let φA : A →* (V ≃ₗ[ZMod p] V) := φ.comp A.subtype
  obtain ⟨t, U, hUind, hUsup, hUne, hUinv, hUirr⟩ :=
    maschke_irred_decomp hpA φA ⊤ (fun _ _ _ => trivial)
  have ht_pos : 0 < t := by
    by_contra h0
    have ht0 : t = 0 := by omega
    subst ht0
    have htop_bot : (⊤ : Submodule (ZMod p) V) = ⊥ := by
      rw [← hUsup]; simp
    obtain ⟨x, y, hxy⟩ := exists_pair_ne V
    have hx : x = 0 := by simpa [htop_bot] using (Submodule.mem_top : x ∈ (⊤ : Submodule (ZMod p) V))
    have hy : y = 0 := by simpa [htop_bot] using (Submodule.mem_top : y ∈ (⊤ : Submodule (ZMod p) V))
    exact hxy (hx.trans hy.symm)
  -- Equivariant isomorphism relation between A-invariant submodules
  let AIso : Submodule (ZMod p) V → Submodule (ZMod p) V → Prop := fun S₁ S₂ =>
    ∃ e : S₁ ≃ₗ[ZMod p] S₂, ∀ (a : A) (x : S₁), (e x : V) ∈ S₂ ∧
      ∀ hx' : φ (a : P) x.1 ∈ S₁, (e ⟨φ (a : P) x.1, hx'⟩ : V) = φ (a : P) (e x).1
  have hAIso_refl : ∀ S, AIso S S := fun S =>
    ⟨LinearEquiv.refl (ZMod p) S, fun _ x => ⟨x.2, fun _ => rfl⟩⟩
  have hAIso_symm : ∀ {S₁ S₂}, (∀ a : A, ∀ v ∈ S₁, φ (a : P) v ∈ S₁) →
      (∀ a : A, ∀ v ∈ S₂, φ (a : P) v ∈ S₂) → AIso S₁ S₂ → AIso S₂ S₁ := by
    intro S₁ S₂ hS₁ hS₂ ⟨e, he⟩
    refine ⟨e.symm, fun a y => ⟨(e.symm y).2, fun hy' => ?_⟩⟩
    have h1 := (he a (e.symm y)).2 (hS₁ a (e.symm y).1 (e.symm y).2)
    have h2 : e ⟨φ (a : P) (e.symm y).1, hS₁ a (e.symm y).1 (e.symm y).2⟩ =
        ⟨φ (a : P) y.1, hy'⟩ := Subtype.ext (by rw [h1, e.apply_symm_apply])
    have h3 := congrArg e.symm h2
    rw [e.symm_apply_apply] at h3
    exact (congrArg Subtype.val h3).symm
  have hAIso_trans : ∀ {S₁ S₂ S₃}, (∀ a : A, ∀ v ∈ S₂, φ (a : P) v ∈ S₂) →
      AIso S₁ S₂ → AIso S₂ S₃ → AIso S₁ S₃ := by
    intro S₁ S₂ S₃ hS₂ ⟨e₁, he₁⟩ ⟨e₂, he₂⟩
    refine ⟨e₁.trans e₂, fun a x => ⟨(e₂ (e₁ x)).2, fun hx' => ?_⟩⟩
    have h1 := (he₁ a x).2 hx'
    have h2 : e₁ ⟨φ (a : P) x.1, hx'⟩ = ⟨φ (a : P) (e₁ x).1, hS₂ a (e₁ x).1 (e₁ x).2⟩ :=
      Subtype.ext h1
    change (e₂ (e₁ ⟨φ (a : P) x.1, hx'⟩) : V) = φ (a : P) (e₂ (e₁ x)).1
    rw [h2]
    exact (he₂ a (e₁ x)).2 (hS₂ a (e₁ x).1 (e₁ x).2)
  -- Schur's lemma: any nonzero A-equivariant linear map between irreducibles yields AIso
  have hSchur : ∀ (S₁ S₂ : Submodule (ZMod p) V)
      (hS₁ : ∀ a : A, ∀ v ∈ S₁, φ (a : P) v ∈ S₁) (_hS₂ : ∀ a : A, ∀ v ∈ S₂, φ (a : P) v ∈ S₂),
      (∀ T ≤ S₁, (∀ a : A, ∀ v ∈ T, φ (a : P) v ∈ T) → T = ⊥ ∨ T = S₁) →
      (∀ T ≤ S₂, (∀ a : A, ∀ v ∈ T, φ (a : P) v ∈ T) → T = ⊥ ∨ T = S₂) →
      ∀ (f : S₁ →ₗ[ZMod p] S₂), f ≠ 0 →
        (∀ (a : A) (x : S₁), (f ⟨φ (a : P) x.1, hS₁ a x.1 x.2⟩ : V) = φ (a : P) (f x).1) →
        AIso S₁ S₂ := by
    intro S₁ S₂ hS₁ hS₂ hIrr₁ hIrr₂ f hf0 hf_eq
    have hf_inj : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot]
      let K : Submodule (ZMod p) V := (LinearMap.ker f).map S₁.subtype
      have hKinv : ∀ a : A, ∀ v ∈ K, φ (a : P) v ∈ K := by
        intro a v hv
        obtain ⟨x, hxker, rfl⟩ := Submodule.mem_map.mp hv
        refine Submodule.mem_map.mpr ⟨⟨φ (a : P) x.1, hS₁ a x.1 x.2⟩, ?_, rfl⟩
        rw [LinearMap.mem_ker] at hxker ⊢
        apply Subtype.ext
        rw [hf_eq a x, hxker]; simp
      rcases hIrr₁ K (Submodule.map_subtype_le S₁ _) hKinv with hbot | htop
      · rw [Submodule.eq_bot_iff]
        intro x hx
        have hmem : (x : V) ∈ K := Submodule.mem_map.mpr ⟨x, hx, rfl⟩
        exact Subtype.ext (by simpa [hbot] using hmem)
      · exfalso; apply hf0
        refine LinearMap.ext fun x => ?_
        have hmem : (x : V) ∈ K := by rw [htop]; exact x.2
        obtain ⟨y, hyker, hyx⟩ := Submodule.mem_map.mp hmem
        have hxy : y = x := Subtype.ext hyx
        rw [← hxy]; exact LinearMap.mem_ker.mp hyker
    have hf_surj : Function.Surjective f := by
      let R : Submodule (ZMod p) V := (LinearMap.range f).map S₂.subtype
      have hRinv : ∀ a : A, ∀ v ∈ R, φ (a : P) v ∈ R := by
        intro a v hv
        obtain ⟨_, ⟨x, rfl⟩, rfl⟩ := Submodule.mem_map.mp hv
        refine Submodule.mem_map.mpr ⟨f ⟨φ (a : P) x.1, hS₁ a x.1 x.2⟩, ⟨_, rfl⟩, hf_eq a x⟩
      have hRne : R ≠ ⊥ := by
        intro hbot; apply hf0
        refine LinearMap.ext fun x => ?_
        have hmem : (f x : V) ∈ R := Submodule.mem_map.mpr ⟨f x, ⟨x, rfl⟩, rfl⟩
        exact Subtype.ext (by simpa [hbot] using hmem)
      have hRtop : R = S₂ := (hIrr₂ R (Submodule.map_subtype_le S₂ _) hRinv).resolve_left hRne
      intro y
      have hmem : (y : V) ∈ R := by rw [hRtop]; exact y.2
      obtain ⟨_, ⟨x, rfl⟩, hyx⟩ := Submodule.mem_map.mp hmem
      exact ⟨x, Subtype.ext hyx⟩
    exact ⟨LinearEquiv.ofBijective f ⟨hf_inj, hf_surj⟩,
      fun a x => ⟨(f x).2, fun _ => hf_eq a x⟩⟩
  -- For any irreducible A-submodule S', S' lies in the sum of all U j with AIso (U j) S'
  have hS'_le_isotypic : ∀ S' : Submodule (ZMod p) V,
      (∀ a : A, ∀ v ∈ S', φ (a : P) v ∈ S') →
      (∀ T ≤ S', (∀ a : A, ∀ v ∈ T, φ (a : P) v ∈ T) → T = ⊥ ∨ T = S') →
      S' ≤ ⨆ (j : Fin t) (_ : AIso (U j) S'), U j := by
    intro S' hS'inv hS'irr
    -- For each j : Fin t, build A-equivariant projection π_j : V →ₗ[ZMod p] U j
    have hcompl : ∀ j : Fin t, IsCompl (U j) (⨆ (k : Fin t) (_ : k ≠ j), U k) := by
      intro j
      rw [isCompl_iff]
      refine ⟨hUind j, codisjoint_iff.mpr ?_⟩
      rw [← hUsup]
      refine le_antisymm (sup_le (le_iSup U j) (iSup₂_le fun k _ => le_iSup U k)) (iSup_le fun k => ?_)
      by_cases hkj : k = j
      · subst hkj; exact le_sup_left
      · exact le_trans (le_iSup₂ (f := fun k (_ : k ≠ j) => U k) k hkj) le_sup_right
    let π : ∀ j : Fin t, V →ₗ[ZMod p] U j := fun j =>
      Submodule.projectionOnto (U j) (⨆ (k : Fin t) (_ : k ≠ j), U k) (hcompl j)
    have hπ_eq : ∀ (j : Fin t) (a : A) (v : V), (π j (φ (a : P) v) : V) = φ (a : P) (π j v).1 := by
      intro j a v
      have hmem : v ∈ U j ⊔ ⨆ (k : Fin t) (_ : k ≠ j), U k := by
        rw [(hcompl j).codisjoint.eq_top]; trivial
      obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hmem
      have hu' : φ (a : P) u ∈ U j := hUinv j a u hu
      have hw' : φ (a : P) w ∈ ⨆ (k : Fin t) (_ : k ≠ j), U k := by
        have hstep : Submodule.map (φ (a : P)).toLinearMap (⨆ (k : Fin t) (_ : k ≠ j), U k) ≤
            ⨆ (k : Fin t) (_ : k ≠ j), U k := by
          simp only [Submodule.map_iSup]
          refine iSup₂_le (fun k hk => le_trans ?_ (le_iSup₂ (f := fun k (_ : k ≠ j) => U k) k hk))
          rintro _ ⟨z, hz, rfl⟩; exact hUinv k a z hz
        exact hstep (Submodule.mem_map_of_mem hw)
      have h1 : (π j (u + w) : V) = u := by
        change ((Submodule.projectionOnto _ _ (hcompl j) (u + w) : U j) : V) = u
        rw [map_add, Submodule.projectionOnto_apply_left (hcompl j) ⟨u, hu⟩,
          Submodule.projectionOnto_apply_right (hcompl j) ⟨w, hw⟩, add_zero]
      have h2 : (π j (φ (a : P) (u + w)) : V) = φ (a : P) u := by
        rw [map_add]
        change ((Submodule.projectionOnto _ _ (hcompl j) (φ (a : P) u + φ (a : P) w) : U j) : V) = _
        rw [map_add, Submodule.projectionOnto_apply_left (hcompl j) ⟨φ (a : P) u, hu'⟩,
          Submodule.projectionOnto_apply_right (hcompl j) ⟨φ (a : P) w, hw'⟩, add_zero]
      rw [h1, h2]
    have hsum_π : ∀ v : V, ∑ j : Fin t, (π j v : V) = v := by
      intro v
      have hv : v ∈ iSup U := by rw [hUsup]; trivial
      refine Submodule.iSup_induction (motive := fun x => ∑ j : Fin t, (π j x : V) = x) U hv
        (fun i x hx => ?_) (by simp) (fun x y hx hy => by
          simp only [map_add, Submodule.coe_add, Finset.sum_add_distrib, hx, hy])
      rw [Finset.sum_eq_single i]
      · exact congrArg Subtype.val (Submodule.projectionOnto_apply_left (hcompl i) ⟨x, hx⟩)
      · intro j _ hji
        have hx' : x ∈ ⨆ (k : Fin t) (_ : k ≠ j), U k :=
          le_iSup₂ (f := fun k (_ : k ≠ j) => U k) i hji.symm hx
        exact congrArg Subtype.val (Submodule.projectionOnto_apply_right (hcompl j) ⟨x, hx'⟩)
      · intro hi; exact absurd (Finset.mem_univ i) hi
    intro v hvS'
    rw [← hsum_π v]
    refine Submodule.sum_mem _ (fun j _ => ?_)
    by_cases hiso : AIso (U j) S'
    · exact le_iSup₂ (f := fun j (_ : AIso (U j) S') => U j) j hiso (π j v).2
    · have hzero : (π j).comp S'.subtype = 0 := by
        by_contra hne
        have h1 : AIso S' (U j) :=
          hSchur S' (U j) hS'inv (hUinv j) hS'irr (hUirr j) ((π j).comp S'.subtype) hne
            (fun a x => hπ_eq j a x.1)
        exact hiso (hAIso_symm hS'inv (hUinv j) h1)
      have hv0 : (π j v : V) = 0 := by
        have h := congrArg (fun f : S' →ₗ[ZMod p] U j => (f ⟨v, hvS'⟩ : V)) hzero
        exact h
      rw [hv0]
      exact Submodule.zero_mem _
  -- Group Fin t into equivalence classes under AIso (U i) (U j)
  let r_rel : Fin t → Fin t → Prop := fun i j => AIso (U i) (U j)
  have hr_equiv : Equivalence r_rel :=
    ⟨fun i => hAIso_refl (U i),
     fun {i j} h => hAIso_symm (hUinv i) (hUinv j) h,
     fun {i j k} h1 h2 => hAIso_trans (hUinv j) h1 h2⟩
  let s_setoid : Setoid (Fin t) := ⟨r_rel, hr_equiv⟩
  let Q := Quotient s_setoid
  let r := Fintype.card Q
  let eQ : Fin r ≃ Q := (Fintype.equivFin Q).symm
  let cls : Fin t → Fin r := fun i => eQ.symm (Quotient.mk s_setoid i)
  let IsoComp : Fin r → Submodule (ZMod p) V := fun c => ⨆ (i : Fin t) (_ : cls i = c), U i
  have hIso_ind : iSupIndep IsoComp := by
    intro c
    rw [Submodule.disjoint_def]
    intro x hx1 hx2
    -- Project onto U i for every i with cls i = c? Easier: show x ∈ ⨆ i (cls i = c) ∩ ⨆ i (cls i ≠ c) = ⊥
    have hle2 : ⨆ (c' : Fin r) (_ : c' ≠ c), IsoComp c' ≤ ⨆ (j : Fin t) (_ : cls j ≠ c), U j := by
      refine iSup₂_le (fun c' hc' => iSup₂_le (fun j hj => ?_))
      exact le_iSup₂ (f := fun j (_ : cls j ≠ c) => U j) j (hj.symm ▸ hc')
    have hx2' : x ∈ ⨆ (j : Fin t) (_ : cls j ≠ c), U j := hle2 hx2
    -- Prove by induction on S : Finset (Fin t) that disjoint subsets have disjoint sups
    have hdisj_sub : ∀ S : Finset (Fin t),
        Disjoint (⨆ i ∈ S, U i) (⨆ (j : Fin t) (_ : j ∉ S), U j) := by
      intro S
      induction S using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        have hsup : (⨆ i ∈ insert a s, U i : Submodule (ZMod p) V) = U a ⊔ ⨆ i ∈ s, U i := by
          apply le_antisymm
          · refine iSup₂_le (fun i hi => ?_)
            rcases Finset.mem_insert.mp hi with rfl | his
            · exact le_sup_left
            · exact le_trans (le_iSup₂ (f := fun i (_ : i ∈ s) => U i) i his) le_sup_right
          · exact sup_le (le_iSup₂ (f := fun i (_ : i ∈ insert a s) => U i) a (Finset.mem_insert_self a s))
              (iSup₂_le (fun i hi => le_iSup₂ (f := fun i (_ : i ∈ insert a s) => U i) i
                (Finset.mem_insert_of_mem hi)))
        rw [hsup, Submodule.disjoint_def]
        intro v hv1 hv2
        obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hv1
        have hw' : u + w - u ∈ ⨆ (j : Fin t) (_ : j ≠ a), U j := by
          have hw_le : (⨆ i ∈ s, U i : Submodule (ZMod p) V) ≤ ⨆ (j : Fin t) (_ : j ≠ a), U j :=
            iSup₂_le (fun i hi => le_iSup₂ (f := fun j (_ : j ≠ a) => U j) i (fun h => ha (h ▸ hi)))
          simpa using hw_le hw
        have hv2_le : u + w ∈ ⨆ (j : Fin t) (_ : j ≠ a), U j :=
          (iSup₂_le (fun j hj => le_iSup₂ (f := fun j (_ : j ≠ a) => U j) j
            (fun h => hj (h ▸ Finset.mem_insert_self a s)))) hv2
        have hu_in : u ∈ ⨆ (j : Fin t) (_ : j ≠ a), U j := by
          have : u = (u + w) - (u + w - u) := by abel
          rw [this]
          exact Submodule.sub_mem _ hv2_le hw'
        have hu0 : u = 0 := Submodule.disjoint_def.mp (hUind a) u hu hu_in
        rw [hu0, zero_add] at hv2 ⊢
        have hv2_s : w ∈ ⨆ (j : Fin t) (_ : j ∉ s), U j :=
          (iSup₂_le (fun j hj => le_iSup₂ (f := fun j (_ : j ∉ s) => U j) j
            (fun hs => hj (Finset.mem_insert_of_mem hs)))) hv2
        exact Submodule.disjoint_def.mp ih w hw hv2_s
    let Sc : Finset (Fin t) := Finset.univ.filter (fun i => cls i = c)
    have hx1' : x ∈ ⨆ i ∈ Sc, U i := by
      have hle : IsoComp c ≤ ⨆ i ∈ Sc, U i :=
        iSup₂_le (fun i hi => le_iSup₂ (f := fun i (_ : i ∈ Sc) => U i) i
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩))
      exact hle hx1
    have hx2'' : x ∈ ⨆ (j : Fin t) (_ : j ∉ Sc), U j := by
      have hle : (⨆ (j : Fin t) (_ : cls j ≠ c), U j) ≤ ⨆ (j : Fin t) (_ : j ∉ Sc), U j :=
        iSup₂_le (fun j hj => le_iSup₂ (f := fun j (_ : j ∉ Sc) => U j) j
          (fun hm => hj (Finset.mem_filter.mp hm).2))
      exact hle hx2'
    exact Submodule.disjoint_def.mp (hdisj_sub Sc) x hx1' hx2''
  have hIso_sup : iSup IsoComp = ⊤ := by
    rw [← hUsup]
    apply le_antisymm
    · exact iSup_le (fun c => iSup₂_le (fun i _ => le_iSup U i))
    · exact iSup_le (fun i => le_trans (le_iSup₂ (f := fun j (_ : cls j = cls i) => U j) i rfl)
        (le_iSup IsoComp (cls i)))
  have hIso_ne : ∀ c : Fin r, IsoComp c ≠ ⊥ := by
    intro c hbot
    obtain ⟨i, hi⟩ := Quotient.exists_rep (eQ c)
    have hci : cls i = c := by simp [cls, hi]
    apply hUne i
    apply le_antisymm _ bot_le
    rw [← hbot]
    exact le_iSup₂ (f := fun j (_ : cls j = c) => U j) i hci
  -- P permutes the isotypic components {IsoComp c}
  have hIso_perm : ∀ g : P, ∃ τ : Equiv.Perm (Fin r),
      ∀ c, Submodule.map (φ g).toLinearMap (IsoComp c) = IsoComp (τ c) := by
    -- Helper: φ g maps any irreducible A-submodule U i to an irreducible A-submodule
    have hconj_irred : ∀ (g : P) (i : Fin t),
        (∀ a : A, ∀ v ∈ Submodule.map (φ g).toLinearMap (U i),
          φ (a : P) v ∈ Submodule.map (φ g).toLinearMap (U i)) ∧
        (∀ T ≤ Submodule.map (φ g).toLinearMap (U i),
          (∀ a : A, ∀ v ∈ T, φ (a : P) v ∈ T) → T = ⊥ ∨ T = Submodule.map (φ g).toLinearMap (U i)) := by
      intro g i
      refine ⟨?_, ?_⟩
      · rintro a _ ⟨v, hv, rfl⟩
        have ha' : g⁻¹ * (a : P) * g ∈ A := by simpa [inv_inv] using hAnorm.conj_mem a.1 a.2 g⁻¹
        refine ⟨φ (g⁻¹ * (a : P) * g) v, hUinv i ⟨_, ha'⟩ v hv, ?_⟩
        change φ g (φ (g⁻¹ * (a : P) * g) v) = φ (a : P) (φ g v)
        have hm : g * (g⁻¹ * (a : P) * g) = (a : P) * g := by group
        calc φ g (φ (g⁻¹ * (a : P) * g) v) = (φ g * φ (g⁻¹ * (a : P) * g)) v := rfl
          _ = φ (g * (g⁻¹ * (a : P) * g)) v := by rw [← map_mul]
          _ = φ ((a : P) * g) v := by rw [hm]
          _ = (φ (a : P) * φ g) v := by rw [map_mul]
          _ = φ (a : P) (φ g v) := rfl
      · intro T hTle hTinv
        let T' : Submodule (ZMod p) V := Submodule.map (φ g⁻¹).toLinearMap T
        have hT'le : T' ≤ U i := by
          rintro _ ⟨w, hw, rfl⟩
          obtain ⟨u, hu, huw⟩ := Submodule.mem_map.mp (hTle hw)
          have h1 : φ g⁻¹ w = u := by
            rw [← huw]
            change (φ g⁻¹ * φ g) u = u
            rw [← map_mul, inv_mul_cancel, map_one]; rfl
          exact h1 ▸ hu
        have hT'inv : ∀ a : A, ∀ v ∈ T', φ (a : P) v ∈ T' := by
          rintro a _ ⟨w, hw, rfl⟩
          have ha' : g * (a : P) * g⁻¹ ∈ A := hAnorm.conj_mem a.1 a.2 g
          refine ⟨φ (g * (a : P) * g⁻¹) w, hTinv ⟨_, ha'⟩ w hw, ?_⟩
          change φ g⁻¹ (φ (g * (a : P) * g⁻¹) w) = φ (a : P) (φ g⁻¹ w)
          have hm : g⁻¹ * (g * (a : P) * g⁻¹) = (a : P) * g⁻¹ := by group
          calc φ g⁻¹ (φ (g * (a : P) * g⁻¹) w) = (φ g⁻¹ * φ (g * (a : P) * g⁻¹)) w := rfl
            _ = φ (g⁻¹ * (g * (a : P) * g⁻¹)) w := by rw [← map_mul]
            _ = φ ((a : P) * g⁻¹) w := by rw [hm]
            _ = (φ (a : P) * φ g⁻¹) w := by rw [map_mul]
            _ = φ (a : P) (φ g⁻¹ w) := rfl
        have hback : Submodule.map (φ g).toLinearMap T' = T := by
          rw [← Submodule.map_comp]
          have hid : (φ g).toLinearMap.comp (φ g⁻¹).toLinearMap = LinearMap.id := by
            ext z; change (φ g * φ g⁻¹) z = z
            rw [← map_mul, mul_inv_cancel, map_one]; rfl
          rw [hid, Submodule.map_id]
        rcases hUirr i T' hT'le hT'inv with hbot | htop
        · left; rw [← hback, hbot, Submodule.map_bot]
        · right; rw [← hback, htop]
    -- φ g preserves AIso
    have hconj_iso : ∀ (g : P) (i j : Fin t), AIso (U i) (U j) →
        AIso (Submodule.map (φ g).toLinearMap (U i)) (Submodule.map (φ g).toLinearMap (U j)) := by
      intro g i j ⟨e, he⟩
      let mapI : U i ≃ₗ[ZMod p] Submodule.map (φ g).toLinearMap (U i) :=
        LinearEquiv.ofBijective
          (((φ g).toLinearMap.comp (U i).subtype).codRestrict
            (Submodule.map (φ g).toLinearMap (U i)) (fun x => Submodule.mem_map_of_mem x.2))
          ⟨fun x y h => Subtype.ext ((φ g).injective (congrArg Subtype.val h)),
           fun ⟨_, hy⟩ => by obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy; exact ⟨⟨x, hx⟩, rfl⟩⟩
      let mapJ : U j ≃ₗ[ZMod p] Submodule.map (φ g).toLinearMap (U j) :=
        LinearEquiv.ofBijective
          (((φ g).toLinearMap.comp (U j).subtype).codRestrict
            (Submodule.map (φ g).toLinearMap (U j)) (fun x => Submodule.mem_map_of_mem x.2))
          ⟨fun x y h => Subtype.ext ((φ g).injective (congrArg Subtype.val h)),
           fun ⟨_, hy⟩ => by obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy; exact ⟨⟨x, hx⟩, rfl⟩⟩
      refine ⟨mapI.symm.trans (e.trans mapJ), fun a y => ⟨(mapJ (e (mapI.symm y))).2, fun hy' => ?_⟩⟩
      obtain ⟨x, hx⟩ : ∃ x : U i, mapI x = y := ⟨mapI.symm y, mapI.apply_symm_apply y⟩
      subst hx
      have ha' : g⁻¹ * (a : P) * g ∈ A := by simpa [inv_inv] using hAnorm.conj_mem a.1 a.2 g⁻¹
      have h1 : mapI.symm ⟨φ (a : P) (mapI x).1, hy'⟩ =
          ⟨φ (g⁻¹ * (a : P) * g) x.1, hUinv i ⟨_, ha'⟩ x.1 x.2⟩ := by
        apply mapI.injective
        rw [mapI.apply_symm_apply]
        apply Subtype.ext
        change φ (a : P) (φ g x.1) = φ g (φ (g⁻¹ * (a : P) * g) x.1)
        have hm : (a : P) * g = g * (g⁻¹ * (a : P) * g) := by group
        calc φ (a : P) (φ g x.1) = (φ (a : P) * φ g) x.1 := rfl
          _ = φ ((a : P) * g) x.1 := by rw [← map_mul]
          _ = φ (g * (g⁻¹ * (a : P) * g)) x.1 := by rw [hm]
          _ = (φ g * φ (g⁻¹ * (a : P) * g)) x.1 := by rw [map_mul]
          _ = φ g (φ (g⁻¹ * (a : P) * g) x.1) := rfl
      change (mapJ (e (mapI.symm ⟨φ (a : P) (mapI x).1, hy'⟩)) : V) =
        φ (a : P) (mapJ (e (mapI.symm (mapI x)))).1
      rw [h1, mapI.symm_apply_apply]
      change φ g (e ⟨φ (g⁻¹ * (a : P) * g) x.1, hUinv i ⟨_, ha'⟩ x.1 x.2⟩).1 = φ (a : P) (φ g (e x).1)
      rw [(he ⟨_, ha'⟩ x).2 (hUinv i ⟨_, ha'⟩ x.1 x.2)]
      have hm : g * (g⁻¹ * (a : P) * g) = (a : P) * g := by group
      calc φ g (φ (g⁻¹ * (a : P) * g) (e x).1) = (φ g * φ (g⁻¹ * (a : P) * g)) (e x).1 := rfl
        _ = φ (g * (g⁻¹ * (a : P) * g)) (e x).1 := by rw [← map_mul]
        _ = φ ((a : P) * g) (e x).1 := by rw [hm]
        _ = (φ (a : P) * φ g) (e x).1 := by rw [map_mul]
        _ = φ (a : P) (φ g (e x).1) := rfl
    -- Every map (φ g) (U i) is isomorphic to some U k (since map (φ g) (U i) ≠ ⊥ and lies in isotypic sum!)
    have hex_match : ∀ (g : P) (i : Fin t), ∃ k : Fin t, AIso (U k) (Submodule.map (φ g).toLinearMap (U i)) := by
      intro g i
      have hle := hS'_le_isotypic (Submodule.map (φ g).toLinearMap (U i))
        (hconj_irred g i).1 (hconj_irred g i).2
      by_contra hall
      push Not at hall
      have hbot : (⨆ (j : Fin t) (_ : AIso (U j) (Submodule.map (φ g).toLinearMap (U i))), U j) = ⊥ := by
        simp [hall]
      rw [hbot] at hle
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hUne i)
      have hmem : φ g v ∈ (⊥ : Submodule (ZMod p) V) := hle (Submodule.mem_map_of_mem hv)
      exact hv0 ((φ g).injective ((by simpa using hmem : φ g v = 0).trans (map_zero _).symm))
    -- For each g : P and c : Fin r, define τ_fn g c : Fin r such that map (φ g) (IsoComp c) ≤ IsoComp (τ_fn g c)
    have hmap_le : ∀ (g : P) (c : Fin r), ∃ c' : Fin r,
        Submodule.map (φ g).toLinearMap (IsoComp c) ≤ IsoComp c' := by
      intro g c
      obtain ⟨i₀, hi₀⟩ := Quotient.exists_rep (eQ c)
      have hci₀ : cls i₀ = c := by simp [cls, hi₀]
      obtain ⟨k₀, hk₀⟩ := hex_match g i₀
      refine ⟨cls k₀, ?_⟩
      simp only [IsoComp, Submodule.map_iSup]
      refine iSup₂_le (fun i hi => ?_)
      have hi_iso : AIso (U i₀) (U i) := Quotient.exact (by
        have h1 : eQ (cls i₀) = eQ (cls i) := by rw [hci₀, hi]
        simpa [cls] using h1)
      have hg_iso : AIso (Submodule.map (φ g).toLinearMap (U i₀))
          (Submodule.map (φ g).toLinearMap (U i)) := hconj_iso g i₀ i hi_iso
      have hle := hS'_le_isotypic (Submodule.map (φ g).toLinearMap (U i))
        (hconj_irred g i).1 (hconj_irred g i).2
      refine le_trans hle (iSup₂_le fun j hj => ?_)
      have hjk₀ : AIso (U j) (U k₀) :=
        hAIso_trans (hconj_irred g i₀).1
          (hAIso_trans (hconj_irred g i).1 hj (hAIso_symm (hconj_irred g i₀).1 (hconj_irred g i).1 hg_iso))
          (hAIso_symm (hUinv k₀) (hconj_irred g i₀).1 hk₀)
      have hcls_eq : cls j = cls k₀ := by
        simp only [cls]
        exact congrArg eQ.symm (Quotient.sound hjk₀)
      exact le_iSup₂ (f := fun j (_ : cls j = cls k₀) => U j) j hcls_eq
    intro g
    choose τf hτf using hmap_le g
    choose τb hτb using hmap_le g⁻¹
    have hleft : ∀ c : Fin r, τb (τf c) = c := by
      intro c
      have hle : IsoComp c ≤ IsoComp (τb (τf c)) := by
        have h1 := Submodule.map_mono (f := (φ g⁻¹).toLinearMap) (hτf c)
        rw [← Submodule.map_comp] at h1
        have hid : (φ g⁻¹).toLinearMap.comp (φ g).toLinearMap = LinearMap.id := by
          ext z; change φ g⁻¹ (φ g z) = z
          have hm : φ g⁻¹ (φ g z) = φ (g⁻¹ * g) z := by rw [map_mul]; rfl
          rw [hm, inv_mul_cancel, map_one]; rfl
        rw [hid, Submodule.map_id] at h1
        exact le_trans h1 (hτb (τf c))
      by_contra hne
      have hdisj := hIso_ind.pairwiseDisjoint (Ne.symm hne)
      exact hIso_ne c (Disjoint.eq_bot_of_le hdisj hle)
    have hright : ∀ c : Fin r, τf (τb c) = c := by
      intro c
      have hle : IsoComp c ≤ IsoComp (τf (τb c)) := by
        have h1 := Submodule.map_mono (f := (φ g).toLinearMap) (hτb c)
        rw [← Submodule.map_comp] at h1
        have hid : (φ g).toLinearMap.comp (φ g⁻¹).toLinearMap = LinearMap.id := by
          ext z; change φ g (φ g⁻¹ z) = z
          have hm : φ g (φ g⁻¹ z) = φ (g * g⁻¹) z := by rw [map_mul]; rfl
          rw [hm, mul_inv_cancel, map_one]; rfl
        rw [hid, Submodule.map_id] at h1
        exact le_trans h1 (hτf (τb c))
      by_contra hne
      have hdisj := hIso_ind.pairwiseDisjoint (Ne.symm hne)
      exact hIso_ne c (Disjoint.eq_bot_of_le hdisj hle)
    refine ⟨⟨τf, τb, hleft, hright⟩, fun c => ?_⟩
    apply le_antisymm (hτf c)
    have h1 := Submodule.map_mono (f := (φ g).toLinearMap) (hτb (τf c))
    rw [hleft c] at h1
    have h2 : Submodule.map (φ g).toLinearMap (Submodule.map (φ g⁻¹).toLinearMap (IsoComp (τf c))) =
        IsoComp (τf c) := by
      rw [← Submodule.map_comp]
      have hid : (φ g).toLinearMap.comp (φ g⁻¹).toLinearMap = LinearMap.id := by
        ext z; change φ g (φ g⁻¹ z) = z
        have hm : φ g (φ g⁻¹ z) = φ (g * g⁻¹) z := by rw [map_mul]; rfl
        rw [hm, mul_inv_cancel, map_one]; rfl
      rw [hid, Submodule.map_id]
    rwa [h2] at h1
  -- By primitivity of V under P, r = 1, so all U i are A-isomorphic to U₀ = U ⟨0, ht_pos⟩!
  have hr_le1 : r ≤ 1 := by
    by_contra hgt
    exact hprim r IsoComp (by omega) hIso_ind hIso_sup hIso_ne hIso_perm
  let i₀ : Fin t := ⟨0, ht_pos⟩
  have hall_iso : ∀ i : Fin t, AIso (U i₀) (U i) := by
    intro i
    have hcls : cls i₀ = cls i := by
      apply Fin.ext
      have h1 := (cls i₀).isLt
      have h2 := (cls i).isLt
      omega
    have hq : Quotient.mk s_setoid i₀ = Quotient.mk s_setoid i := by
      have h := congrArg eQ hcls
      simpa [cls] using h
    exact Quotient.exact hq
  -- Deduce faithfulness of A on U i₀, IsCyclic A, and polynomial annihilation
  have hfaith_U₀ : ∀ a : A, (∀ v ∈ U i₀, φ (a : P) v = v) → a = 1 := by
    intro a ha
    have hφa : φ (a : P) = 1 := by
      refine LinearEquiv.ext fun v => ?_
      change φ (a : P) v = v
      have hv : v ∈ iSup U := by rw [hUsup]; trivial
      refine Submodule.iSup_induction (motive := fun x => φ (a : P) x = x) U hv
        (fun i x hx => ?_) (map_zero _) (fun x y hx hy => by rw [map_add, hx, hy])
      obtain ⟨e, he⟩ := hall_iso i
      obtain ⟨u, hu⟩ : ∃ u : U i₀, e u = ⟨x, hx⟩ := ⟨e.symm ⟨x, hx⟩, e.apply_symm_apply _⟩
      have h1 := (he a u).2 (hUinv i₀ a u.1 u.2)
      have hu_fix : (⟨φ (a : P) u.1, hUinv i₀ a u.1 u.2⟩ : U i₀) = u := Subtype.ext (ha u.1 u.2)
      rw [hu_fix, hu] at h1
      exact h1.symm
    exact Subtype.ext (hfaith (hφa.trans (map_one φ).symm))
  have hA_cyc : IsCyclic A := by
    let hA_commGroup : CommGroup A :=
      { (inferInstance : Group A) with mul_comm := fun x y => Subtype.ext (hAcomm x.1 x.2 y.1 y.2) }
    have hK_bot : ∀ a : A, a ∈ (⊥ : Subgroup A) ↔ ∀ w ∈ U i₀, φA a w = w := fun a =>
      ⟨fun h w _ => by rw [Subgroup.mem_bot.mp h, map_one]; rfl,
       fun hw => Subgroup.mem_bot.mpr (hfaith_U₀ a hw)⟩
    have hQcyc := (@abelian_irred_stabilizer_and_quotient_cyclic p _ V _ _ _ A hA_commGroup _
      φA (U i₀) (hUne i₀) (hUinv i₀) (hUirr i₀) ⊥ hK_bot).2
    let eA : A ≃* A ⧸ (⊥ : Subgroup A) := (QuotientGroup.quotientBot (G := A)).symm
    obtain ⟨g, hg⟩ := @IsCyclic.exists_generator (A ⧸ (⊥ : Subgroup A)) _ hQcyc
    refine ⟨⟨eA.symm g, fun x => ?_⟩⟩
    obtain ⟨k, hk⟩ := hg (eA x)
    refine ⟨k, ?_⟩
    apply eA.injective
    change eA (eA.symm g ^ k) = eA x
    rw [map_zpow, eA.apply_symm_apply]
    exact hk
  have hpoly : ∀ (a : A) (f : Polynomial (ZMod p)),
      (∀ v ∈ U i₀, Polynomial.aeval (φ (a : P)).toLinearMap f v = 0) →
      Polynomial.aeval (φ (a : P)).toLinearMap f = 0 := by
    intro a f hf
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ iSup U := by rw [hUsup]; trivial
    refine Submodule.iSup_induction
      (motive := fun x => Polynomial.aeval (φ (a : P)).toLinearMap f x = 0) U hv
      (fun i x hx => ?_) (map_zero _) (fun x y hx hy => by rw [map_add, hx, hy, add_zero])
    obtain ⟨e, he⟩ := hall_iso i
    obtain ⟨u, hu⟩ : ∃ u : U i₀, e u = ⟨x, hx⟩ := ⟨e.symm ⟨x, hx⟩, e.apply_symm_apply _⟩
    have hpow_mem : ∀ (k : ℕ) (w : U i₀), ((φ (a : P)).toLinearMap ^ k) w.1 ∈ U i₀ := by
      intro k
      induction k with
      | zero => intro w; exact w.2
      | succ k ih => intro w; rw [pow_succ']; exact hUinv i₀ a _ (ih w)
    have hpow_inter : ∀ (k : ℕ) (w : U i₀),
        ((φ (a : P)).toLinearMap ^ k) (e w).1 = (e ⟨((φ (a : P)).toLinearMap ^ k) w.1, hpow_mem k w⟩ : V) := by
      intro k
      induction k with
      | zero => intro w; rfl
      | succ k ih =>
        intro w
        have hlhs : ((φ (a : P)).toLinearMap ^ (k + 1)) (e w).1 =
            φ (a : P) (((φ (a : P)).toLinearMap ^ k) (e w).1) := by rw [pow_succ']; rfl
        have hrhs : (⟨((φ (a : P)).toLinearMap ^ (k + 1)) w.1, hpow_mem (k + 1) w⟩ : U i₀) =
            ⟨φ (a : P) (((φ (a : P)).toLinearMap ^ k) w.1), hUinv i₀ a _ (hpow_mem k w)⟩ :=
          Subtype.ext (by
            change ((φ (a : P)).toLinearMap ^ (k + 1)) w.1 = φ (a : P) (((φ (a : P)).toLinearMap ^ k) w.1)
            rw [pow_succ']; rfl)
        rw [hlhs, ih w, hrhs]
        exact ((he a _).2 (hUinv i₀ a _ (hpow_mem k w))).symm
    have hpoly_inter : ∀ g : Polynomial (ZMod p),
        (∀ w : U i₀, Polynomial.aeval (φ (a : P)).toLinearMap g w.1 ∈ U i₀) ∧
        (∀ w : U i₀, ∀ hmem : Polynomial.aeval (φ (a : P)).toLinearMap g w.1 ∈ U i₀,
          Polynomial.aeval (φ (a : P)).toLinearMap g (e w).1 =
          (e ⟨Polynomial.aeval (φ (a : P)).toLinearMap g w.1, hmem⟩ : V)) := by
      intro g
      induction g using Polynomial.induction_on' with
      | add g₁ g₂ ih₁ ih₂ =>
        refine ⟨fun w => by
          rw [map_add, LinearMap.add_apply]; exact (U i₀).add_mem (ih₁.1 w) (ih₂.1 w),
          fun w hmem => by
            have h1 : (⟨Polynomial.aeval (φ (a : P)).toLinearMap (g₁ + g₂) w.1, hmem⟩ : U i₀) =
                ⟨Polynomial.aeval (φ (a : P)).toLinearMap g₁ w.1, ih₁.1 w⟩ +
                ⟨Polynomial.aeval (φ (a : P)).toLinearMap g₂ w.1, ih₂.1 w⟩ :=
              Subtype.ext (by
                change Polynomial.aeval (φ (a : P)).toLinearMap (g₁ + g₂) w.1 = _
                rw [map_add]; rfl)
            rw [h1, map_add, map_add, LinearMap.add_apply, Submodule.coe_add,
              ih₁.2 w (ih₁.1 w), ih₂.2 w (ih₂.1 w)]⟩
      | monomial n c =>
        have hmon_apply : ∀ z : V,
            Polynomial.aeval (φ (a : P)).toLinearMap (Polynomial.monomial n c) z =
            c • ((φ (a : P)).toLinearMap ^ n) z := fun z => by
          rw [Polynomial.aeval_monomial]
          change (algebraMap (ZMod p) (Module.End (ZMod p) V) c * ((φ (a : P)).toLinearMap ^ n)) z = _
          simp [Algebra.algebraMap_eq_smul_one]
        refine ⟨fun w => by
          rw [hmon_apply]; exact (U i₀).smul_mem c (hpow_mem n w),
          fun w hmem => by
            have h1 : (⟨Polynomial.aeval (φ (a : P)).toLinearMap (Polynomial.monomial n c) w.1,
                hmem⟩ : U i₀) =
                c • (⟨((φ (a : P)).toLinearMap ^ n) w.1, hpow_mem n w⟩ : U i₀) :=
              Subtype.ext (by
                change Polynomial.aeval (φ (a : P)).toLinearMap (Polynomial.monomial n c) w.1 = _
                exact hmon_apply w.1)
            rw [h1, map_smul, Submodule.coe_smul_of_tower, hmon_apply, hpow_inter n w]⟩
    have hstep := (hpoly_inter f).2 u ((hpoly_inter f).1 u)
    have hxu : (e u : V) = x := congrArg Subtype.val hu
    rw [hxu] at hstep
    rw [hstep]
    have h0 : (⟨Polynomial.aeval (φ (a : P)).toLinearMap f u.1, (hpoly_inter f).1 u⟩ : U i₀) = 0 :=
      Subtype.ext (hf u.1 u.2)
    rw [h0, map_zero]; rfl
  exact ⟨hA_cyc, U i₀, hUne i₀, hUinv i₀, hUirr i₀, hfaith_U₀, hpoly⟩

/- ### Component 7: Primitive 2-Group Theorem and Full 2-Group Theorem (`¬ IsPGroup 2 H`) -/

lemma zpow_eq_pow_mod {G : Type*} [Group G] (x : G) {n : ℕ} (hn : 0 < n) (hx : x ^ n = 1) (m : ℤ) :
    ∃ j : ℕ, j < n ∧ x ^ m = x ^ j := by
  have hpos : (0 : ℤ) < n := by exact_mod_cast hn
  let r : ℤ := m % (n : ℤ)
  have hr0 : 0 ≤ r := Int.emod_nonneg m hpos.ne'
  have hrlt : r < n := Int.emod_lt_of_pos m hpos
  have hr_eq : (r.toNat : ℤ) = r := Int.toNat_of_nonneg hr0
  refine ⟨r.toNat, by omega, ?_⟩
  have hdiv : m = (n : ℤ) * (m / (n : ℤ)) + (r.toNat : ℤ) := by
    have h1 : (n : ℤ) * (m / (n : ℤ)) + r = m := Int.mul_ediv_add_emod m (n : ℤ)
    linarith
  calc x ^ m = x ^ ((n : ℤ) * (m / (n : ℤ)) + (r.toNat : ℤ)) := by conv_lhs => rw [hdiv]
    _ = (x ^ (n : ℤ)) ^ (m / (n : ℤ)) * x ^ (r.toNat : ℤ) := by rw [zpow_add, zpow_mul]
    _ = (x ^ n) ^ (m / (n : ℤ)) * x ^ r.toNat := by rw [zpow_natCast, zpow_natCast]
    _ = x ^ r.toNat := by rw [hx, one_zpow, one_mul]

lemma primitive_two_group_abelian {p : ℕ} [Fact p.Prime] (hp7 : 7 ≤ p)
    (ι : ZMod p) (hι : ι ^ 2 = -1)
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V] [Nontrivial V]
    {P : Type*} [Group P] [Fintype P] (hP2 : IsPGroup 2 P)
    (φ : P →* (V ≃ₗ[ZMod p] V)) (hfaith : Function.Injective φ)
    (hirred : ∀ W : Submodule (ZMod p) V, (∀ g : P, ∀ v ∈ W, φ g v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hprim : ∀ (r : ℕ) (U : Fin r → Submodule (ZMod p) V),
      2 ≤ r → iSupIndep U → iSup U = ⊤ → (∀ a, U a ≠ ⊥) →
      ¬ ∀ g : P, ∃ τ : Equiv.Perm (Fin r),
        ∀ a, Submodule.map (φ g).toLinearMap (U a) = U (τ a)) :
    ∀ x y : P, x * y = y * x := by
  classical
  have hp_prime : p.Prime := Fact.out
  have hpP : ¬ (p ∣ Nat.card P) := by
    obtain ⟨k, hk⟩ := hP2.exists_card_eq
    intro hdvd
    rw [hk] at hdvd
    have h2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp_prime Nat.prime_two).mp
      (hp_prime.dvd_of_dvd_pow hdvd)
    omega
  -- Choose a maximal abelian normal subgroup A of P
  let AbNorm : Subgroup P → Prop := fun A => A.Normal ∧ ∀ x ∈ A, ∀ y ∈ A, x * y = y * x
  have hex_max : ∃ n : ℕ, ∃ A : Subgroup P, AbNorm A ∧ Nat.card A = n :=
    ⟨1, ⊥, ⟨inferInstance, fun x hx y hy => by rw [Subgroup.mem_bot.mp hx, Subgroup.mem_bot.mp hy]⟩,
      Subgroup.card_bot⟩
  let S := (Finset.range (Nat.card P + 1)).filter (fun n => ∃ A : Subgroup P, AbNorm A ∧ Nat.card A = n)
  have h1S : 1 ∈ S := Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le Nat.card_pos), ⊥,
      ⟨inferInstance, fun x hx y hy => by rw [Subgroup.mem_bot.mp hx, Subgroup.mem_bot.mp hy]⟩,
      Subgroup.card_bot⟩
  let n₀ := S.max' ⟨1, h1S⟩
  obtain ⟨A, ⟨hAnorm, hAcomm⟩, hAcard⟩ := (Finset.mem_filter.mp (Finset.max'_mem S ⟨1, h1S⟩)).2
  have hAmax : ∀ B : Subgroup P, AbNorm B → Nat.card B ≤ Nat.card A := by
    intro B hB
    have hle : Nat.card B ≤ Nat.card P := Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card B)
    have hmem : Nat.card B ∈ S := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hle), B, hB, rfl⟩
    rw [hAcard]
    exact Finset.le_max' S (Nat.card B) hmem
  -- If A = ⊤, then P is abelian!
  by_cases hAtop : A = ⊤
  · intro x y; exact hAcomm x (hAtop ▸ trivial) y (hAtop ▸ trivial)
  exfalso
  -- A is cyclic by Clifford's theorem
  have hAcyc : IsCyclic A := (clifford_homog_of_primitive hpP φ hfaith hprim A hAnorm hAcomm).1
  -- Step 1: Every element a ∈ A of order 4 lies in the center of P
  have hord4_center : ∀ a ∈ A, orderOf a = 4 → ∀ g : P, g * a * g⁻¹ = a := by
    intro a ha ha4
    have ha2_ne1 : a ^ 2 ≠ 1 := by
      intro h1
      have hdvd : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one h1
      rw [ha4] at hdvd
      omega
    have ha4_1 : a ^ 4 = 1 := by rw [← ha4, pow_orderOf_eq_one]
    -- a^2 is the unique element of order 2 in cyclic normal A, hence central in P
    have ha2_cent : ∀ g : P, g * a ^ 2 * g⁻¹ = a ^ 2 := by
      intro g
      have hconjA : g * a ^ 2 * g⁻¹ ∈ A := hAnorm.conj_mem (a ^ 2) (A.pow_mem ha 2) g
      have hsq1 : (⟨g * a ^ 2 * g⁻¹, hconjA⟩ : A) ^ 2 = 1 := by
        apply Subtype.ext; change (g * a ^ 2 * g⁻¹) ^ 2 = 1
        rw [conj_pow, ← pow_mul, ha4_1]; group
      have hne1 : (⟨g * a ^ 2 * g⁻¹, hconjA⟩ : A) ≠ 1 := by
        intro h1; apply ha2_ne1
        have h' : g * a ^ 2 * g⁻¹ = 1 := congrArg Subtype.val h1
        calc a ^ 2 = g⁻¹ * (g * a ^ 2 * g⁻¹) * g := by group
          _ = g⁻¹ * 1 * g := by rw [h']
          _ = 1 := by group
      -- In cyclic 2-group A, there is at most one element of order 2
      obtain ⟨gen, hgen⟩ := IsCyclic.exists_generator (α := A)
      have hA_p : IsPGroup 2 A := hP2.to_subgroup A
      obtain ⟨k, hk⟩ := hA_p.exists_card_eq
      have hgen_ord : orderOf gen = 2 ^ k := by
        rw [← Nat.card_zpowers, show Subgroup.zpowers gen = ⊤ from by
          rw [eq_top_iff]; intro x _; exact hgen x, Subgroup.card_top, hk]
      have huniq2 : ∀ y : A, y ^ 2 = 1 → y ≠ 1 → y = gen ^ (2 ^ (k - 1)) := by
        intro y hy2 hy1
        obtain ⟨m, rfl⟩ := hgen y
        have h2k_pos : 1 ≤ k := by
          rcases Nat.eq_zero_or_pos k with rfl | hpos
          · exfalso; apply hy1
            have : Nat.card A = 1 := by simpa using hk
            have : Subsingleton A := (Nat.card_eq_one_iff_unique.mp this).1
            exact Subsingleton.elim _ 1
          · exact hpos
        have hord_y : orderOf (gen ^ m) = 2 := by
          have hdvd : orderOf (gen ^ m) ∣ 2 := orderOf_dvd_of_pow_eq_one hy2
          rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
          · exact absurd (orderOf_eq_one_iff.mp h1) hy1
          · exact h2
        obtain ⟨r, hr_lt, hpow_eq⟩ :=
          zpow_eq_pow_mod gen (pow_pos (by decide) k) (hgen_ord ▸ pow_orderOf_eq_one gen) m
        dsimp only at hy2 hy1 ⊢
        rw [hpow_eq] at hy2 hy1 ⊢
        have h2r : 2 ^ k ∣ 2 * r := by
          rw [← hgen_ord, orderOf_dvd_iff_pow_eq_one, mul_comm, pow_mul, hy2]
        have hr_ne0 : r ≠ 0 := by intro h0; subst h0; exact hy1 (pow_zero gen)
        have hpow_split : 2 ^ k = 2 * 2 ^ (k - 1) := by
          conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ, mul_comm]
        rw [hpow_split] at h2r
        have hdvd_r : 2 ^ (k - 1) ∣ r := (Nat.mul_dvd_mul_iff_left (by decide)).mp h2r
        obtain ⟨q, hq⟩ := hdvd_r
        have hq_eq : q = 1 := by
          have hlt : 2 ^ (k - 1) * q < 2 ^ (k - 1) * 2 := by
            rw [← hq, mul_comm, ← hpow_split]; exact hr_lt
          have hlt2 : q < 2 := Nat.lt_of_mul_lt_mul_left hlt
          rcases Nat.eq_zero_or_pos q with rfl | hqpos
          · simp at hq; exact absurd hq hr_ne0
          · omega
        subst hq_eq
        rw [hq, mul_one]
      have h1 := huniq2 ⟨g * a ^ 2 * g⁻¹, hconjA⟩ hsq1 hne1
      have ha2_sq1 : (⟨a ^ 2, A.pow_mem ha 2⟩ : A) ^ 2 = 1 :=
        Subtype.ext (by change (a ^ 2) ^ 2 = 1; rw [← pow_mul]; exact ha4_1)
      have h2 := huniq2 ⟨a ^ 2, A.pow_mem ha 2⟩ ha2_sq1 (fun h => ha2_ne1 (congrArg Subtype.val h))
      exact congrArg Subtype.val (h1.trans h2.symm)
    -- Therefore φ (a^2) = -id on V
    have hφa2 : ∀ v : V, φ (a ^ 2) v = -v := by
      let K : Submodule (ZMod p) V := LinearMap.ker ((φ (a ^ 2)).toLinearMap - LinearMap.id)
      have hKinv : ∀ g : P, ∀ v ∈ K, φ g v ∈ K := by
        intro g v hv
        have hv' : φ (a ^ 2) v = v := sub_eq_zero.mp hv
        change φ (a ^ 2) (φ g v) - φ g v = 0
        rw [sub_eq_zero]
        have hm : a ^ 2 * g = g * a ^ 2 := by
          calc a ^ 2 * g = (g * a ^ 2 * g⁻¹) * g := by rw [ha2_cent g]
            _ = g * a ^ 2 := by group
        calc φ (a ^ 2) (φ g v) = φ (a ^ 2 * g) v := by rw [map_mul]; rfl
          _ = φ (g * a ^ 2) v := by rw [hm]
          _ = φ g (φ (a ^ 2) v) := by rw [map_mul]; rfl
          _ = φ g v := by rw [hv']
      have hK_ne_top : K ≠ ⊤ := by
        intro htop
        apply ha2_ne1
        apply hfaith
        refine LinearEquiv.ext fun v => ?_
        have hv : v ∈ K := by rw [htop]; trivial
        change φ (a ^ 2) v - v = 0 at hv
        rw [map_one]
        exact sub_eq_zero.mp hv
      have hK_bot : K = ⊥ := (hirred K hKinv).resolve_right hK_ne_top
      intro v
      have hmem : φ (a ^ 2) v + v ∈ K := by
        change φ (a ^ 2) (φ (a ^ 2) v + v) - (φ (a ^ 2) v + v) = 0
        rw [map_add]
        have hsq : φ (a ^ 2) (φ (a ^ 2) v) = v := by
          have hm : φ (a ^ 2) (φ (a ^ 2) v) = φ (a ^ 4) v := by
            rw [show a ^ 4 = a ^ 2 * a ^ 2 by group, map_mul]; rfl
          rw [hm, ha4_1, map_one]; rfl
        rw [hsq]; abel
      have h0 : φ (a ^ 2) v + v = 0 := by simpa [hK_bot] using hmem
      exact eq_neg_of_add_eq_zero_left h0
    -- Split V = E_ι(a) ⊕ E_{-ι}(a)
    let E₁ : Submodule (ZMod p) V := LinearMap.ker ((φ a).toLinearMap - ι • LinearMap.id)
    let E₂ : Submodule (ZMod p) V := LinearMap.ker ((φ a).toLinearMap - (-ι) • LinearMap.id)
    have hι_ne0 : ι ≠ 0 := by intro h0; rw [h0] at hι; norm_num at hι
    have h2ι_ne0 : (2 : ZMod p) * ι ≠ 0 := by
      have h2ne : (2 : ZMod p) ≠ 0 := by
        intro h0
        have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h0)
        have hle := Nat.le_of_dvd (by decide) hdvd
        omega
      exact mul_ne_zero h2ne hι_ne0
    have hdisj : Disjoint E₁ E₂ := by
      rw [Submodule.disjoint_def]
      intro v hv1 hv2
      have h1 : φ a v = ι • v := sub_eq_zero.mp hv1
      have h2 : φ a v = (-ι) • v := sub_eq_zero.mp hv2
      have h3 : ((2 : ZMod p) * ι) • v = 0 := by
        have hsub : (ι - (-ι)) • v = 0 := by rw [sub_smul, ← h1, ← h2, sub_self]
        rwa [show ι - (-ι) = (2 : ZMod p) * ι by ring] at hsub
      exact (smul_eq_zero.mp h3).resolve_left h2ι_ne0
    have hsup : E₁ ⊔ E₂ = ⊤ := by
      rw [Submodule.eq_top_iff']
      intro v
      let c := ((2 : ZMod p) * ι)⁻¹
      let v₁ : V := c • (φ a v + ι • v)
      let v₂ : V := (-c) • (φ a v - ι • v)
      have haa : φ a (φ a v) = -v := by
        have hm : φ a (φ a v) = φ (a ^ 2) v := by rw [pow_two, map_mul]; rfl
        rw [hm, hφa2 v]
      have hι2 : ι * ι = -1 := by rw [← pow_two, hι]
      have hv1 : v₁ ∈ E₁ := by
        change φ a v₁ - ι • v₁ = 0
        rw [sub_eq_zero]
        calc φ a v₁ = c • (φ a (φ a v) + ι • φ a v) := by
                simp only [v₁, map_smul, map_add]
          _ = (-c) • v + (c * ι) • φ a v := by
                rw [haa, smul_add, smul_neg, neg_smul, smul_smul]
          _ = (ι * c) • φ a v + (ι * (c * ι)) • v := by
                have h1 : ι * (c * ι) = -c := by calc ι * (c * ι) = c * (ι * ι) := by ring
                  _ = c * (-1) := by rw [hι2]
                  _ = -c := by ring
                rw [mul_comm ι c, h1, add_comm]
          _ = ι • v₁ := by
                simp only [v₁, smul_add, smul_smul]
      have hv2 : v₂ ∈ E₂ := by
        change φ a v₂ - (-ι) • v₂ = 0
        rw [sub_eq_zero]
        calc φ a v₂ = (-c) • (φ a (φ a v) - ι • φ a v) := by
                simp only [v₂, map_smul, map_sub]
          _ = c • v + (c * ι) • φ a v := by
                rw [haa, smul_sub, smul_neg, neg_smul, neg_neg, smul_smul, neg_mul, neg_smul, sub_neg_eq_add]
          _ = ((-ι) * (-c)) • φ a v - ((-ι) * ((-c) * ι)) • v := by
                have h1 : (-ι) * (-c) = c * ι := by ring
                have h2 : (-ι) * ((-c) * ι) = -c := by calc (-ι) * ((-c) * ι) = c * (ι * ι) := by ring
                  _ = c * (-1) := by rw [hι2]
                  _ = -c := by ring
                rw [h1, h2, neg_smul, sub_neg_eq_add, add_comm]
          _ = (-ι) • v₂ := by
                simp only [v₂, smul_sub, smul_smul]
      have hadd : v₁ + v₂ = v := by
        calc v₁ + v₂ = (c • φ a v + (c * ι) • v) + (-(c • φ a v) + (c * ι) • v) := by
                simp only [v₁, v₂, smul_add, smul_sub, smul_smul, neg_mul, neg_smul, sub_neg_eq_add]
          _ = (c * ι + c * ι) • v := by rw [add_smul]; abel
          _ = (c * ((2 : ZMod p) * ι)) • v := by congr 1; ring
          _ = v := by rw [inv_mul_cancel₀ h2ι_ne0, one_smul]
      rw [← hadd]
      exact Submodule.add_mem_sup hv1 hv2
    -- Every g ∈ P conjugates a to a or a⁻¹ (only 2 elements of order 4 in cyclic A)
    have hconj_a : ∀ g : P, g * a * g⁻¹ = a ∨ g * a * g⁻¹ = a⁻¹ := by
      intro g
      have hmemA : g * a * g⁻¹ ∈ A := hAnorm.conj_mem a ha g
      have hsq : (g * a * g⁻¹) ^ 2 = a ^ 2 := by rw [conj_pow, ha2_cent g]
      have hprod : (g * a * g⁻¹ * a⁻¹) ^ 2 = 1 := by
        have hcomm : Commute (g * a * g⁻¹) a⁻¹ := hAcomm _ hmemA _ (A.inv_mem ha)
        rw [hcomm.mul_pow, hsq, inv_pow, mul_inv_cancel]
      -- In cyclic A, every element of square 1 is 1 or a^2
      have hsq_cases : ∀ y ∈ A, y ^ 2 = 1 → y = 1 ∨ y = a ^ 2 := by
        intro y hy hy2
        by_cases hy1 : y = 1
        · exact Or.inl hy1
        · right
          obtain ⟨gen, hgen⟩ := IsCyclic.exists_generator (α := A)
          have hA_p : IsPGroup 2 A := hP2.to_subgroup A
          obtain ⟨k, hk⟩ := hA_p.exists_card_eq
          have hgen_ord : orderOf gen = 2 ^ k := by
            rw [← Nat.card_zpowers, show Subgroup.zpowers gen = ⊤ from by
              rw [eq_top_iff]; intro x _; exact hgen x, Subgroup.card_top, hk]
          have huniq2 : ∀ w : A, w ^ 2 = 1 → w ≠ 1 → w = gen ^ (2 ^ (k - 1)) := by
            intro w hw2 hw1
            obtain ⟨m, rfl⟩ := hgen w
            have h2k_pos : 1 ≤ k := by
              rcases Nat.eq_zero_or_pos k with rfl | hpos
              · exfalso; apply hw1
                have : Nat.card A = 1 := by simpa using hk
                have : Subsingleton A := (Nat.card_eq_one_iff_unique.mp this).1
                exact Subsingleton.elim _ 1
              · exact hpos
            obtain ⟨r, hr_lt, hpow_eq⟩ :=
              zpow_eq_pow_mod gen (pow_pos (by decide) k) (hgen_ord ▸ pow_orderOf_eq_one gen) m
            dsimp only at hw2 hw1 ⊢
            rw [hpow_eq] at hw2 hw1 ⊢
            have h2r : 2 ^ k ∣ 2 * r := by
              rw [← hgen_ord, orderOf_dvd_iff_pow_eq_one, mul_comm, pow_mul, hw2]
            have hr_ne0 : r ≠ 0 := by intro h0; subst h0; exact hw1 (pow_zero gen)
            have hpow_split : 2 ^ k = 2 * 2 ^ (k - 1) := by
              conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ, mul_comm]
            rw [hpow_split] at h2r
            obtain ⟨q, hq⟩ := (Nat.mul_dvd_mul_iff_left (by decide)).mp h2r
            have hq_eq : q = 1 := by
              have hlt : 2 ^ (k - 1) * q < 2 ^ (k - 1) * 2 := by
                rw [← hq, mul_comm, ← hpow_split]; exact hr_lt
              have hlt2 : q < 2 := Nat.lt_of_mul_lt_mul_left hlt
              rcases Nat.eq_zero_or_pos q with rfl | hqpos
              · simp at hq; exact absurd hq hr_ne0
              · omega
            subst hq_eq; rw [hq, mul_one]
          have h1 := huniq2 ⟨y, hy⟩ (Subtype.ext hy2) (fun h => hy1 (congrArg Subtype.val h))
          have ha2_sq1 : (⟨a ^ 2, A.pow_mem ha 2⟩ : A) ^ 2 = 1 :=
            Subtype.ext (by change (a ^ 2) ^ 2 = 1; rw [← pow_mul]; exact ha4_1)
          have h2 := huniq2 ⟨a ^ 2, A.pow_mem ha 2⟩ ha2_sq1
            (fun h => ha2_ne1 (congrArg Subtype.val h))
          exact congrArg Subtype.val (h1.trans h2.symm)
      rcases hsq_cases (g * a * g⁻¹ * a⁻¹) (A.mul_mem hmemA (A.inv_mem ha)) hprod with h1 | h2
      · left; exact mul_inv_eq_one.mp h1
      · right
        calc g * a * g⁻¹ = (g * a * g⁻¹ * a⁻¹) * a := by group
          _ = a ^ 2 * a := by rw [h2]
          _ = a ^ 4 * a⁻¹ := by group
          _ = 1 * a⁻¹ := by rw [ha4_1]
          _ = a⁻¹ := one_mul _
    -- Hence P permutes {E₁, E₂}, so by primitivity E₁ = ⊥ or E₂ = ⊥!
    have hE_or : E₁ = ⊥ ∨ E₂ = ⊥ := by
      by_contra hboth
      push Not at hboth
      obtain ⟨hE1_ne, hE2_ne⟩ := hboth
      let pairE : Fin 2 → Submodule (ZMod p) V := ![E₁, E₂]
      have hpair_ind : iSupIndep pairE := by
        intro j
        fin_cases j
        · refine Disjoint.mono_right (iSup₂_le fun k hk => ?_) hdisj
          fin_cases k
          · exact absurd rfl hk
          · exact le_rfl
        · refine Disjoint.mono_right (iSup₂_le fun k hk => ?_) hdisj.symm
          fin_cases k
          · exact le_rfl
          · exact absurd rfl hk
      have hpair_sup : iSup pairE = ⊤ := by
        rw [← hsup]
        apply le_antisymm
        · exact iSup_le (fun j => by fin_cases j <;> [exact le_sup_left; exact le_sup_right])
        · exact sup_le (le_iSup pairE 0) (le_iSup pairE 1)
      have hpair_ne : ∀ j : Fin 2, pairE j ≠ ⊥ := fun j => by
        fin_cases j <;> assumption
      have hpair_perm : ∀ g : P, ∃ τ : Equiv.Perm (Fin 2),
          ∀ j, Submodule.map (φ g).toLinearMap (pairE j) = pairE (τ j) := by
        intro g
        have hmap_eig : ∀ (μ₁ μ₂ : ZMod p),
            (∀ v : V, φ a (φ g v) = μ₂ • φ g v → φ a v = μ₁ • v) →
            (∀ v : V, φ a v = μ₁ • v → φ a (φ g v) = μ₂ • φ g v) →
            Submodule.map (φ g).toLinearMap (LinearMap.ker ((φ a).toLinearMap - μ₁ • LinearMap.id)) =
              LinearMap.ker ((φ a).toLinearMap - μ₂ • LinearMap.id) := by
          intro μ₁ μ₂ hrev hfwd
          apply le_antisymm
          · rintro _ ⟨v, hv, rfl⟩
            exact sub_eq_zero.mpr (hfwd v (sub_eq_zero.mp hv))
          · intro w hw
            refine ⟨φ g⁻¹ w, ?_, ?_⟩
            · apply sub_eq_zero.mpr
              apply hrev (φ g⁻¹ w)
              have hg1 : φ g (φ g⁻¹ w) = w := by
                have hm : φ g (φ g⁻¹ w) = φ (g * g⁻¹) w := by rw [map_mul]; rfl
                rw [hm, mul_inv_cancel, map_one]; rfl
              rw [hg1]
              exact sub_eq_zero.mp hw
            · change φ g (φ g⁻¹ w) = w
              have hm : φ g (φ g⁻¹ w) = φ (g * g⁻¹) w := by rw [map_mul]; rfl
              rw [hm, mul_inv_cancel, map_one]; rfl
        have hφainv : ∀ v : V, φ a⁻¹ v = -(φ a v) := by
          intro v
          have h1 : φ a (φ a⁻¹ v) = v := by
            have hm : φ a (φ a⁻¹ v) = φ (a * a⁻¹) v := by rw [map_mul]; rfl
            rw [hm, mul_inv_cancel, map_one]; rfl
          have h2 : φ a (-(φ a v)) = v := by
            rw [map_neg]
            have hm : φ a (φ a v) = φ (a ^ 2) v := by rw [pow_two, map_mul]; rfl
            rw [hm, hφa2 v, neg_neg]
          exact (φ a).injective (h1.trans h2.symm)
        rcases hconj_a g⁻¹ with hsame | hswap
        · refine ⟨1, fun j => ?_⟩
          have hcomm : a * g = g * a := by
            calc a * g = g * (g⁻¹ * a * (g⁻¹)⁻¹) := by group
              _ = g * a := by rw [hsame]
          have hiff : ∀ (μ : ZMod p) (v : V), φ a (φ g v) = μ • φ g v ↔ φ a v = μ • v := by
            intro μ v
            have hlhs : φ a (φ g v) = φ g (φ a v) := by
              calc φ a (φ g v) = φ (a * g) v := by rw [map_mul]; rfl
                _ = φ (g * a) v := by rw [hcomm]
                _ = φ g (φ a v) := by rw [map_mul]; rfl
            rw [hlhs, ← map_smul]
            exact (φ g).injective.eq_iff
          fin_cases j
          · exact hmap_eig ι ι (fun v => (hiff ι v).mp) (fun v => (hiff ι v).mpr)
          · exact hmap_eig (-ι) (-ι) (fun v => (hiff (-ι) v).mp) (fun v => (hiff (-ι) v).mpr)
        · refine ⟨Equiv.swap 0 1, fun j => ?_⟩
          have hanti : a * g = g * a⁻¹ := by
            calc a * g = g * (g⁻¹ * a * (g⁻¹)⁻¹) := by group
              _ = g * a⁻¹ := by rw [hswap]
          have hiff : ∀ (μ : ZMod p) (v : V), φ a (φ g v) = (-μ) • φ g v ↔ φ a v = μ • v := by
            intro μ v
            have hlhs : φ a (φ g v) = -(φ g (φ a v)) := by
              calc φ a (φ g v) = φ (a * g) v := by rw [map_mul]; rfl
                _ = φ (g * a⁻¹) v := by rw [hanti]
                _ = φ g (φ a⁻¹ v) := by rw [map_mul]; rfl
                _ = φ g (-(φ a v)) := by rw [hφainv]
                _ = -(φ g (φ a v)) := map_neg _ _
            rw [hlhs, neg_smul, ← map_smul, neg_inj]
            exact (φ g).injective.eq_iff
          fin_cases j
          · exact hmap_eig ι (-ι) (fun v => (hiff ι v).mp) (fun v => (hiff ι v).mpr)
          · have h1 := hiff (-ι)
            simp only [neg_neg] at h1
            exact hmap_eig (-ι) ι (fun v => (h1 v).mp) (fun v => (h1 v).mpr)
      exact hprim 2 pairE le_rfl hpair_ind hpair_sup hpair_ne hpair_perm
    -- Therefore φ a is a scalar (±ι • id), hence a is central in P!
    intro g
    apply hfaith
    refine LinearEquiv.ext fun v => ?_
    rcases hE_or with hE1 | hE2
    · have hE2top : E₂ = ⊤ := by rwa [hE1, bot_sup_eq] at hsup
      have hsc : ∀ w : V, φ a w = (-ι) • w := fun w =>
        sub_eq_zero.mp (show w ∈ E₂ from by rw [hE2top]; trivial)
      calc φ (g * a * g⁻¹) v = φ g (φ a (φ g⁻¹ v)) := by simp [map_mul]
        _ = φ g ((-ι) • φ g⁻¹ v) := by rw [hsc]
        _ = (-ι) • φ g (φ g⁻¹ v) := map_smul _ _ _
        _ = (-ι) • v := by
            have hm : φ g (φ g⁻¹ v) = φ (g * g⁻¹) v := by rw [map_mul]; rfl
            rw [hm, mul_inv_cancel, map_one]; rfl
        _ = φ a v := (hsc v).symm
    · have hE1top : E₁ = ⊤ := by rwa [hE2, sup_bot_eq] at hsup
      have hsc : ∀ w : V, φ a w = ι • w := fun w =>
        sub_eq_zero.mp (show w ∈ E₁ from by rw [hE1top]; trivial)
      calc φ (g * a * g⁻¹) v = φ g (φ a (φ g⁻¹ v)) := by simp [map_mul]
        _ = φ g (ι • φ g⁻¹ v) := by rw [hsc]
        _ = ι • φ g (φ g⁻¹ v) := map_smul _ _ _
        _ = ι • v := by
            have hm : φ g (φ g⁻¹ v) = φ (g * g⁻¹) v := by rw [map_mul]; rfl
            rw [hm, mul_inv_cancel, map_one]; rfl
        _ = φ a v := (hsc v).symm
  -- Step 2: Construct normal subgroup B ◁ P containing A with |B / A| = 2
  have hQ_nt : Nontrivial (P ⧸ A) := by
    rw [nontrivial_iff]
    obtain ⟨g, hg⟩ : ∃ g : P, g ∉ A := by
      by_contra hall; push Not at hall
      exact hAtop (eq_top_iff.mpr fun x _ => hall x)
    exact ⟨QuotientGroup.mk g, 1, fun h => hg ((QuotientGroup.eq_one_iff g).mp h)⟩
  have hQ_2 : IsPGroup 2 (P ⧸ A) := hP2.to_quotient A
  have hZQ_nt : Nontrivial (Subgroup.center (P ⧸ A)) := hQ_2.center_nontrivial
  have hZQ_2 : IsPGroup 2 (Subgroup.center (P ⧸ A)) := hQ_2.to_subgroup (Subgroup.center (P ⧸ A))
  obtain ⟨kZ, hkZ_pos, hkZ_card⟩ := hZQ_2.nontrivial_iff_card.mp hZQ_nt
  have h2_dvd_Z : 2 ∣ Nat.card (Subgroup.center (P ⧸ A)) := by
    rw [hkZ_card]; exact dvd_pow_self 2 hkZ_pos.ne'
  obtain ⟨⟨g_bar, hg_barZ⟩, hg_bar_ord⟩ :=
    exists_prime_orderOf_dvd_card' (G := Subgroup.center (P ⧸ A)) 2 h2_dvd_Z
  have hg_bar_ordQ : orderOf g_bar = 2 :=
    (Subgroup.orderOf_coe (⟨g_bar, hg_barZ⟩ : Subgroup.center (P ⧸ A))).trans hg_bar_ord
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g_bar
  let B : Subgroup P := (Subgroup.zpowers (QuotientGroup.mk g : P ⧸ A)).comap (QuotientGroup.mk' A)
  have hA_le_B : A ≤ B := fun x hx => by
    change QuotientGroup.mk x ∈ Subgroup.zpowers (QuotientGroup.mk g : P ⧸ A)
    rw [(QuotientGroup.eq_one_iff x).mpr hx]
    exact Subgroup.one_mem _
  have hg_mem_B : g ∈ B := Subgroup.mem_zpowers (QuotientGroup.mk g : P ⧸ A)
  have hg_not_A : g ∉ A := by
    intro hgA
    have h1 : (QuotientGroup.mk g : P ⧸ A) = 1 := (QuotientGroup.eq_one_iff g).mpr hgA
    rw [h1, orderOf_one] at hg_bar_ordQ
    omega
  have hg2_mem_A : g ^ 2 ∈ A := by
    rw [← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk g : P ⧸ A) ^ 2 = 1
    rw [← hg_bar_ordQ, pow_orderOf_eq_one]
  have hB_norm : B.Normal := by
    have hz_norm : (Subgroup.zpowers (QuotientGroup.mk g : P ⧸ A)).Normal :=
      ⟨fun y hy q => by
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        have hcomm : Commute q (QuotientGroup.mk g : P ⧸ A) :=
          Subgroup.mem_center_iff.mp hg_barZ q
        have hcomm_m : q * (QuotientGroup.mk g : P ⧸ A) ^ m = (QuotientGroup.mk g : P ⧸ A) ^ m * q :=
          Commute.zpow_right hcomm m
        have heq : q * (QuotientGroup.mk g : P ⧸ A) ^ m * q⁻¹ = (QuotientGroup.mk g : P ⧸ A) ^ m := by
          calc q * (QuotientGroup.mk g : P ⧸ A) ^ m * q⁻¹
              = (QuotientGroup.mk g : P ⧸ A) ^ m * q * q⁻¹ := by rw [hcomm_m]
            _ = (QuotientGroup.mk g : P ⧸ A) ^ m := by group
        rw [heq]
        exact Subgroup.mem_zpowers_iff.mpr ⟨m, rfl⟩⟩
    exact Subgroup.Normal.comap hz_norm (QuotientGroup.mk' A)
  -- Every element of B is either in A or of the form g * a with a ∈ A
  have hB_cases : ∀ y ∈ B, y ∈ A ∨ ∃ a ∈ A, y = g * a := by
    intro y hy
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hy
    change (QuotientGroup.mk g : P ⧸ A) ^ m = QuotientGroup.mk y at hm
    have hpow2 : (QuotientGroup.mk g : P ⧸ A) ^ 2 = 1 := by rw [← hg_bar_ordQ, pow_orderOf_eq_one]
    obtain ⟨r, hr_lt, hmod2⟩ := zpow_eq_pow_mod (QuotientGroup.mk g : P ⧸ A) (by decide) hpow2 m
    rw [hmod2] at hm
    have h01 : r = 0 ∨ r = 1 := by omega
    rcases h01 with rfl | rfl
    · left
      rw [pow_zero] at hm
      exact (QuotientGroup.eq_one_iff y).mp hm.symm
    · right
      rw [pow_one] at hm
      have hmem : g⁻¹ * y ∈ A := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← hm, inv_mul_cancel]
      exact ⟨g⁻¹ * y, hmem, by group⟩
  -- B is strictly larger than A, hence NOT abelian by maximality of A!
  have hB_not_comm : ¬ ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    intro hBcomm
    have hle := hAmax B ⟨hB_norm, hBcomm⟩
    have hlt : Nat.card A < Nat.card B := by
      have hss : (A : Set P) ⊂ (B : Set P) := Set.ssubset_iff_subset_ne.mpr
        ⟨hA_le_B, fun heq => hg_not_A (by change g ∈ (A : Set P); rw [heq]; exact hg_mem_B)⟩
      exact Set.Finite.card_lt_card (Set.toFinite _) hss
    omega
  -- Step 3: Analyze conjugation of generator x of cyclic A by g
  obtain ⟨⟨x, hxA⟩, hxgen⟩ := IsCyclic.exists_generator (α := A)
  have hA_2 : IsPGroup 2 A := hP2.to_subgroup A
  obtain ⟨k, hk_card⟩ := hA_2.exists_card_eq
  have hx_ord : orderOf x = 2 ^ k := by
    have h1 : orderOf (⟨x, hxA⟩ : A) = 2 ^ k := by
      rw [← Nat.card_zpowers, show Subgroup.zpowers (⟨x, hxA⟩ : A) = ⊤ from by
        rw [eq_top_iff]; intro y _; exact hxgen y, Subgroup.card_top, hk_card]
    exact (Subgroup.orderOf_coe (⟨x, hxA⟩ : A)).trans h1
  have hA_pow : ∀ y ∈ A, ∃ j : ℕ, j < 2 ^ k ∧ y = x ^ j := by
    intro y hy
    obtain ⟨m, hm⟩ := hxgen ⟨y, hy⟩
    have hy_eq : y = x ^ m := (congrArg Subtype.val hm).symm
    obtain ⟨j, hj_lt, hpow⟩ :=
      zpow_eq_pow_mod x (pow_pos (by decide) k) (hx_ord ▸ pow_orderOf_eq_one x) m
    exact ⟨j, hj_lt, hy_eq.trans hpow⟩
  -- g does NOT commute with x (else B is abelian!)
  have hgx_ne : g * x * g⁻¹ ≠ x := by
    intro hgx
    apply hB_not_comm
    have hgx_comm : g * x = x * g := by calc g * x = (g * x * g⁻¹) * g := by group
      _ = x * g := by rw [hgx]
    have hga_comm : ∀ a ∈ A, g * a = a * g := by
      intro a ha
      obtain ⟨j, _, rfl⟩ := hA_pow a ha
      exact (Commute.pow_right hgx_comm j)
    intro u hu v hv
    rcases hB_cases u hu with huA | ⟨a, haA, rfl⟩
    · rcases hB_cases v hv with hvA | ⟨b, hbA, rfl⟩
      · exact hAcomm u huA v hvA
      · calc u * (g * b) = (u * g) * b := by group
          _ = (g * u) * b := by rw [(hga_comm u huA).symm]
          _ = g * (u * b) := by group
          _ = g * (b * u) := by rw [hAcomm u huA b hbA]
          _ = g * b * u := by group
    · rcases hB_cases v hv with hvA | ⟨b, hbA, rfl⟩
      · calc (g * a) * v = g * (a * v) := by group
          _ = g * (v * a) := by rw [hAcomm a haA v hvA]
          _ = (g * v) * a := by group
          _ = (v * g) * a := by rw [hga_comm v hvA]
          _ = v * (g * a) := by group
      · calc (g * a) * (g * b) = g * (a * g) * b := by group
          _ = g * (g * a) * b := by rw [(hga_comm a haA).symm]
          _ = g * g * (a * b) := by group
          _ = g * g * (b * a) := by rw [hAcomm a haA b hbA]
          _ = g * (g * b) * a := by group
          _ = g * (b * g) * a := by rw [hga_comm b hbA]
          _ = (g * b) * (g * a) := by group
  -- Write g * x * g⁻¹ = x ^ r with r < 2 ^ k
  obtain ⟨r, hr_lt, hgx_r⟩ := hA_pow (g * x * g⁻¹) (hAnorm.conj_mem x hxA g)
  have hr_ne1 : r ≠ 1 := by intro h1; subst h1; rw [pow_one] at hgx_r; exact hgx_ne hgx_r
  have hk_ge2 : 2 ≤ k := by
    by_contra hlt
    have hle : k ≤ 1 := by omega
    interval_cases k
    · have : r = 0 := by omega
      subst this
      have hx1 : x = 1 := orderOf_eq_one_iff.mp (by simpa using hx_ord)
      rw [hx1] at hgx_ne; simp at hgx_ne
    · have : r = 0 ∨ r = 1 := by omega
      rcases this with rfl | h1
      · rw [pow_zero] at hgx_r
        have hx1 : x = 1 := by
          calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
            _ = g⁻¹ * 1 * g := by rw [hgx_r]
            _ = 1 := by group
        rw [hx1, orderOf_one] at hx_ord; omega
      · exact hr_ne1 h1
  -- a = x ^ (2 ^ (k - 2)) has order 4, so g * a * g⁻¹ = a, giving 4 ∣ (r - 1)
  let a4 : P := x ^ (2 ^ (k - 2))
  have ha4_ord : orderOf a4 = 4 := by
    have hdvd : 2 ^ (k - 2) ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
    rw [orderOf_pow, hx_ord, Nat.gcd_eq_right hdvd]
    have hsplit : 2 ^ k = 2 ^ (k - 2) * 4 := by
      calc 2 ^ k = 2 ^ ((k - 2) + 2) := by congr 1; omega
        _ = 2 ^ (k - 2) * 2 ^ 2 := pow_add 2 _ 2
        _ = 2 ^ (k - 2) * 4 := rfl
    rw [hsplit, Nat.mul_div_cancel_left 4 (pow_pos (by decide) _)]
  have hga4 : g * a4 * g⁻¹ = a4 := hord4_center a4 (A.pow_mem hxA _) ha4_ord g
  have h4_dvd : 4 ∣ r - 1 := by
    have hpow : x ^ (r * 2 ^ (k - 2)) = x ^ (2 ^ (k - 2)) := by
      calc x ^ (r * 2 ^ (k - 2)) = (x ^ r) ^ (2 ^ (k - 2)) := pow_mul x r _
        _ = (g * x * g⁻¹) ^ (2 ^ (k - 2)) := by rw [← hgx_r]
        _ = g * a4 * g⁻¹ := conj_pow
        _ = a4 := hga4
    have hmod : r * 2 ^ (k - 2) ≡ 2 ^ (k - 2) [MOD 2 ^ k] := by
      rw [← hx_ord]; exact pow_eq_pow_iff_modEq.mp hpow
    have hr_pos : 1 ≤ r := by
      rcases Nat.eq_zero_or_pos r with rfl | hpos
      · rw [pow_zero] at hgx_r
        have hx1 : x = 1 := by
          calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
            _ = g⁻¹ * 1 * g := by rw [hgx_r]
            _ = 1 := by group
        rw [hx1, orderOf_one] at hx_ord
        have h4 : 4 ≤ 2 ^ k := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk_ge2
        omega
      · exact hpos
    have hsub : 2 ^ k ∣ (r - 1) * 2 ^ (k - 2) := by
      have hge : 2 ^ (k - 2) ≤ r * 2 ^ (k - 2) := Nat.le_mul_of_pos_left _ hr_pos
      have hdvd := (Nat.modEq_iff_dvd' hge).mp hmod.symm
      rwa [show r * 2 ^ (k - 2) - 2 ^ (k - 2) = (r - 1) * 2 ^ (k - 2) by
        rw [Nat.sub_mul, one_mul]] at hdvd
    have hsplit : 2 ^ k = 4 * 2 ^ (k - 2) := by
      calc 2 ^ k = 2 ^ (2 + (k - 2)) := by congr 1; omega
        _ = 4 * 2 ^ (k - 2) := by rw [pow_add]; rfl
    rw [hsplit] at hsub
    exact (Nat.mul_dvd_mul_iff_right (pow_pos (by decide) _)).mp hsub
  have hr_pos : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with rfl | hpos
    · rw [pow_zero] at hgx_r
      have hx1 : x = 1 := by
        calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
          _ = g⁻¹ * 1 * g := by rw [hgx_r]
          _ = 1 := by group
      rw [hx1, orderOf_one] at hx_ord
      have h4 : 4 ≤ 2 ^ k := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk_ge2
      omega
    · exact hpos
  -- Also g^2 ∈ A commutes with x, so 2^k ∣ r^2 - 1 = (r - 1)(r + 1), hence 2^(k-1) ∣ (r - 1)
  have h2k_dvd_sq : 2 ^ k ∣ (r - 1) * (r + 1) := by
    have hg2x : g ^ 2 * x * (g ^ 2)⁻¹ = x := by
      have hcomm := hAcomm (g ^ 2) hg2_mem_A x hxA
      calc g ^ 2 * x * (g ^ 2)⁻¹ = x * g ^ 2 * (g ^ 2)⁻¹ := by rw [hcomm]
        _ = x := by group
    have hxr2 : x ^ (r * r) = x ^ 1 := by
      calc x ^ (r * r) = (x ^ r) ^ r := pow_mul x r r
        _ = (g * x * g⁻¹) ^ r := by rw [← hgx_r]
        _ = g * (x ^ r) * g⁻¹ := conj_pow
        _ = g * (g * x * g⁻¹) * g⁻¹ := by rw [← hgx_r]
        _ = g ^ 2 * x * (g ^ 2)⁻¹ := by rw [pow_two]; group
        _ = x := hg2x
        _ = x ^ 1 := (pow_one x).symm
    have hmod : r * r ≡ 1 [MOD 2 ^ k] := by rw [← hx_ord]; exact pow_eq_pow_iff_modEq.mp hxr2
    have hrr : 1 ≤ r * r := Nat.mul_pos hr_pos hr_pos
    have hdvd := (Nat.modEq_iff_dvd' hrr).mp hmod.symm
    have hfac : r * r - 1 = (r - 1) * (r + 1) := by
      zify [hr_pos, hrr]; ring
    rwa [hfac] at hdvd
  have h2km1_dvd : 2 ^ (k - 1) ∣ r - 1 := by
    obtain ⟨q, hq⟩ := h4_dvd
    have hr1_eq : r + 1 = 2 * (2 * q + 1) := by omega
    rw [hr1_eq] at h2k_dvd_sq
    have hsplit : 2 ^ k = 2 * 2 ^ (k - 1) := by
      conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ, mul_comm]
    rw [hsplit] at h2k_dvd_sq
    have hstep : 2 ^ (k - 1) ∣ (r - 1) * (2 * q + 1) := by
      have h1 : 2 * 2 ^ (k - 1) ∣ 2 * ((r - 1) * (2 * q + 1)) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using h2k_dvd_sq
      exact (Nat.mul_dvd_mul_iff_left (by decide)).mp h1
    have hcop : (2 ^ (k - 1)).Coprime (2 * q + 1) := by
      apply Nat.Coprime.pow_left
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
      omega
    exact hcop.dvd_of_dvd_mul_right hstep
  have hk_ge3 : 3 ≤ k := by
    by_contra hlt
    have hk2 : k = 2 := by omega
    subst hk2
    obtain ⟨q, hq⟩ := h4_dvd
    omega
  have hr_eq : r = 1 + 2 ^ (k - 1) := by
    obtain ⟨q, hq⟩ := h2km1_dvd
    have hq_pos : 0 < q := by
      rcases Nat.eq_zero_or_pos q with rfl | hpos
      · omega
      · exact hpos
    have hq_le1 : q ≤ 1 := by
      have hsplit : 2 ^ k = 2 * 2 ^ (k - 1) := by
        conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ, mul_comm]
      have hpos : 0 < 2 ^ (k - 1) := pow_pos (by decide) _
      have hlt2 : 2 ^ (k - 1) * q < 2 * 2 ^ (k - 1) := by omega
      nlinarith
    have hq1 : q = 1 := by omega
    rw [hq1, mul_one] at hq
    omega
  -- Let z = x ^ (2 ^ (k - 1)) (central of order 2); then g * x * g⁻¹ = x * z!
  let z : P := x ^ (2 ^ (k - 1))
  have hz_eq_a4sq : z = a4 ^ 2 := by
    change x ^ (2 ^ (k - 1)) = (x ^ (2 ^ (k - 2))) ^ 2
    rw [← pow_mul]
    congr 1
    rw [show k - 1 = (k - 2) + 1 by omega, pow_succ]
  have hz_sq : z ^ 2 = 1 := by
    rw [hz_eq_a4sq, ← pow_mul, show 2 * 2 = 4 by rfl, ← ha4_ord, pow_orderOf_eq_one]
  have hz_ne1 : z ≠ 1 := by
    intro h1
    rw [hz_eq_a4sq] at h1
    have hdvd : orderOf a4 ∣ 2 := orderOf_dvd_of_pow_eq_one h1
    rw [ha4_ord] at hdvd; omega
  have hz_cent : ∀ h : P, h * z * h⁻¹ = z := fun h => by
    rw [hz_eq_a4sq, ← conj_pow, hord4_center a4 (A.pow_mem hxA _) ha4_ord h]
  have hgx_z : g * x * g⁻¹ = x * z := by
    rw [hgx_r, hr_eq, pow_add, pow_one]
  -- Step 4: Find c ∈ B \ A with c ^ 2 = 1 and c * x * c⁻¹ = x * z
  obtain ⟨t, _, hg2_t⟩ := hA_pow (g ^ 2) hg2_mem_A
  have hgx_pow : ∀ n : ℕ, g * x ^ n * g⁻¹ = x ^ n * z ^ n := by
    intro n
    have hcomm : Commute x z := hAcomm x hxA z (A.pow_mem hxA _)
    calc g * x ^ n * g⁻¹ = (g * x * g⁻¹) ^ n := conj_pow.symm
      _ = (x * z) ^ n := by rw [hgx_z]
      _ = x ^ n * z ^ n := hcomm.mul_pow n
  have ht_even : 2 ∣ t := by
    have h1 : x ^ t * z ^ t = x ^ t := by
      calc x ^ t * z ^ t = g * x ^ t * g⁻¹ := (hgx_pow t).symm
        _ = g * g ^ 2 * g⁻¹ := by rw [← hg2_t]
        _ = g ^ 2 := by group
        _ = x ^ t := hg2_t
    have hzt1 : z ^ t = 1 := mul_left_cancel (h1.trans (mul_one _).symm)
    have hord_z : orderOf z = 2 := by
      have hdvd : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one hz_sq
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
      · exact absurd (orderOf_eq_one_iff.mp h1) hz_ne1
      · exact h2
    rw [← hord_z]; exact orderOf_dvd_of_pow_eq_one hzt1
  obtain ⟨m, rfl⟩ := ht_even
  let b : P := g * (x ^ m)⁻¹
  have hb_sq : b ^ 2 = z ^ m := by
    have h1 : g * (x ^ m)⁻¹ * g⁻¹ = (x ^ m)⁻¹ * (z ^ m)⁻¹ := by
      calc g * (x ^ m)⁻¹ * g⁻¹ = (g * x ^ m * g⁻¹)⁻¹ := by group
        _ = (x ^ m * z ^ m)⁻¹ := by rw [hgx_pow m]
        _ = (z ^ m)⁻¹ * (x ^ m)⁻¹ := mul_inv_rev _ _
        _ = (x ^ m)⁻¹ * (z ^ m)⁻¹ := hAcomm _ (A.inv_mem (A.pow_mem (A.pow_mem hxA _) _)) _
              (A.inv_mem (A.pow_mem hxA _))
    have hzm_inv : (z ^ m)⁻¹ = z ^ m := by
      apply inv_eq_of_mul_eq_one_right
      rw [← pow_add, ← two_mul, pow_mul, hz_sq, one_pow]
    calc b ^ 2 = g * (x ^ m)⁻¹ * (g * (x ^ m)⁻¹) := pow_two b
      _ = (g * (x ^ m)⁻¹ * g⁻¹) * g ^ 2 * (x ^ m)⁻¹ := by group
      _ = ((x ^ m)⁻¹ * (z ^ m)⁻¹) * x ^ (2 * m) * (x ^ m)⁻¹ := by rw [h1, hg2_t]
      _ = ((x ^ m)⁻¹ * z ^ m) * (x ^ m * x ^ m) * (x ^ m)⁻¹ := by
          rw [hzm_inv, show x ^ (2 * m) = x ^ m * x ^ m by rw [two_mul, pow_add]]
      _ = (x ^ m)⁻¹ * x ^ m * (x ^ m * (x ^ m)⁻¹) * z ^ m := by
          have hc1 : z ^ m * x ^ m = x ^ m * z ^ m :=
            hAcomm _ (A.pow_mem (A.pow_mem hxA _) _) _ (A.pow_mem hxA _)
          calc ((x ^ m)⁻¹ * z ^ m) * (x ^ m * x ^ m) * (x ^ m)⁻¹
              = (x ^ m)⁻¹ * (z ^ m * x ^ m) * x ^ m * (x ^ m)⁻¹ := by group
            _ = (x ^ m)⁻¹ * (x ^ m * z ^ m) * x ^ m * (x ^ m)⁻¹ := by rw [hc1]
            _ = (x ^ m)⁻¹ * x ^ m * (z ^ m * x ^ m) * (x ^ m)⁻¹ := by group
            _ = (x ^ m)⁻¹ * x ^ m * (x ^ m * z ^ m) * (x ^ m)⁻¹ := by rw [hc1]
            _ = (x ^ m)⁻¹ * x ^ m * x ^ m * (z ^ m * (x ^ m)⁻¹) := by group
            _ = (x ^ m)⁻¹ * x ^ m * x ^ m * ((x ^ m)⁻¹ * z ^ m) := by
                  rw [hAcomm _ (A.pow_mem (A.pow_mem hxA _) _) _ (A.inv_mem (A.pow_mem hxA _))]
            _ = (x ^ m)⁻¹ * x ^ m * (x ^ m * (x ^ m)⁻¹) * z ^ m := by group
      _ = z ^ m := by group
  have hex_c : ∃ c : P, c ∈ B ∧ c ∉ A ∧ c ^ 2 = 1 ∧ c * x * c⁻¹ = x * z := by
    have hzm_cases : z ^ m = 1 ∨ z ^ m = z := by
      have hmod : m % 2 = 0 ∨ m % 2 = 1 := by omega
      have hpow : z ^ m = z ^ (m % 2) := by
        conv_lhs => rw [← Nat.div_add_mod m 2, pow_add, pow_mul, hz_sq, one_pow, one_mul]
      rw [hpow]
      rcases hmod with h0 | h1
      · left; rw [h0, pow_zero]
      · right; rw [h1, pow_one]
    have hb_mem_B : b ∈ B := B.mul_mem hg_mem_B (hA_le_B (A.inv_mem (A.pow_mem hxA m)))
    have hb_not_A : b ∉ A := by
      intro hbA
      have hgA : g ∈ A := by
        have h : g = b * x ^ m := by simp [b]
        rw [h]; exact A.mul_mem hbA (A.pow_mem hxA m)
      exact hg_not_A hgA
    have hbx : b * x * b⁻¹ = x * z := by
      have hc : (x ^ m)⁻¹ * x * ((x ^ m)⁻¹)⁻¹ = x := by
        have h1 := hAcomm (x ^ m)⁻¹ (A.inv_mem (A.pow_mem hxA m)) x hxA
        calc (x ^ m)⁻¹ * x * ((x ^ m)⁻¹)⁻¹ = x * (x ^ m)⁻¹ * ((x ^ m)⁻¹)⁻¹ := by rw [h1]
          _ = x := by group
      calc b * x * b⁻¹ = g * ((x ^ m)⁻¹ * x * ((x ^ m)⁻¹)⁻¹) * g⁻¹ := by simp [b]; group
        _ = g * x * g⁻¹ := by rw [hc]
        _ = x * z := hgx_z
    rcases hzm_cases with hzm1 | hzmz
    · exact ⟨b, hb_mem_B, hb_not_A, hb_sq.trans hzm1, hbx⟩
    · refine ⟨a4 * b, B.mul_mem (hA_le_B (A.pow_mem hxA _)) hb_mem_B, ?_, ?_, ?_⟩
      · intro habA
        have hbA : b ∈ A := by
          have : b = a4⁻¹ * (a4 * b) := by group
          rw [this]; exact A.mul_mem (A.inv_mem (A.pow_mem hxA _)) habA
        exact hb_not_A hbA
      · have hcomm : Commute a4 b := by
          have h1 := hord4_center a4 (A.pow_mem hxA _) ha4_ord b
          calc a4 * b = (b * a4 * b⁻¹) * b := by rw [h1]
            _ = b * a4 := by group
        rw [hcomm.mul_pow, ← hz_eq_a4sq, hb_sq, hzmz, ← pow_two, hz_sq]
      · have hc : a4 * (x * z) * a4⁻¹ = x * z := by
          have h1 := hAcomm a4 (A.pow_mem hxA _) (x * z) (A.mul_mem hxA (A.pow_mem hxA _))
          calc a4 * (x * z) * a4⁻¹ = (x * z) * a4 * a4⁻¹ := by rw [h1]
            _ = x * z := by group
        calc (a4 * b) * x * (a4 * b)⁻¹ = a4 * (b * x * b⁻¹) * a4⁻¹ := by group
          _ = a4 * (x * z) * a4⁻¹ := by rw [hbx]
          _ = x * z := hc
  obtain ⟨c, hcB, hc_notA, hc2, hcx⟩ := hex_c
  -- Step 5: E = {y ∈ B | y ^ 2 = 1} equals {1, z, c, c * z}, a non-cyclic abelian normal subgroup of P!
  have hE_char : ∀ y ∈ B, y ^ 2 = 1 ↔ y = 1 ∨ y = z ∨ y = c ∨ y = c * z := by
    intro y hyB
    constructor
    · intro hy2
      rcases hB_cases y hyB with hyA | ⟨a, haA, rfl⟩
      · obtain ⟨j, hj_lt, rfl⟩ := hA_pow y hyA
        have h2j : 2 ^ k ∣ 2 * j := by
          rw [← hx_ord, orderOf_dvd_iff_pow_eq_one, mul_comm, pow_mul, hy2]
        have hsplit : 2 ^ k = 2 * 2 ^ (k - 1) := by
          conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ, mul_comm]
        rw [hsplit] at h2j
        obtain ⟨q, hq⟩ := (Nat.mul_dvd_mul_iff_left (by decide)).mp h2j
        have hq01 : q = 0 ∨ q = 1 := by
          have hlt : 2 ^ (k - 1) * q < 2 ^ (k - 1) * 2 := by
            rw [← hq, mul_comm, ← hsplit]; exact hj_lt
          have hlt2 : q < 2 := Nat.lt_of_mul_lt_mul_left hlt
          omega
        rcases hq01 with rfl | rfl
        · left; simp [hq]
        · right; left; simp [hq, z]
      · -- Write g * a = c * x ^ j for some j < 2 ^ k
        have hcg_A : c⁻¹ * (g * a) ∈ A := by
          rcases hB_cases c hcB with hcA | ⟨a', ha'A, hc_eq⟩
          · exact absurd hcA hc_notA
          · rw [hc_eq]
            have h1 : (g * a')⁻¹ * (g * a) = a'⁻¹ * a := by group
            rw [h1]; exact A.mul_mem (A.inv_mem ha'A) haA
        obtain ⟨j, hj_lt, hj_eq⟩ := hA_pow (c⁻¹ * (g * a)) hcg_A
        have hga_eq : g * a = c * x ^ j := by rw [← hj_eq]; group
        rw [hga_eq] at hy2 ⊢
        have hcx_pow : c * x ^ j * c⁻¹ = x ^ j * z ^ j := by
          have hcomm : Commute x z := hAcomm x hxA z (A.pow_mem hxA _)
          calc c * x ^ j * c⁻¹ = (c * x * c⁻¹) ^ j := conj_pow.symm
            _ = (x * z) ^ j := by rw [hcx]
            _ = x ^ j * z ^ j := hcomm.mul_pow j
        have hsq_eq : (c * x ^ j) ^ 2 = x ^ (j * (2 + 2 ^ (k - 1))) := by
          have hcomm : Commute (x ^ j) (z ^ j) :=
            hAcomm _ (A.pow_mem hxA _) _ (A.pow_mem (A.pow_mem hxA _) _)
          calc (c * x ^ j) ^ 2 = (c * x ^ j * c⁻¹) * c ^ 2 * x ^ j := by rw [pow_two]; group
            _ = (x ^ j * z ^ j) * 1 * x ^ j := by rw [hcx_pow, hc2]
            _ = x ^ j * x ^ j * z ^ j := by rw [mul_one, mul_assoc, hcomm.symm, ← mul_assoc]
            _ = x ^ (j * 2) * x ^ (j * 2 ^ (k - 1)) := by
                rw [← pow_add, show j + j = j * 2 by ring]
                congr 1; simp only [z, ← pow_mul, mul_comm]
            _ = x ^ (j * (2 + 2 ^ (k - 1))) := by rw [← pow_add, mul_add]
        rw [hsq_eq] at hy2
        have hdvd : 2 ^ k ∣ j * (2 + 2 ^ (k - 1)) := by
          rw [← hx_ord, orderOf_dvd_iff_pow_eq_one]; exact hy2
        have hsplit1 : 2 + 2 ^ (k - 1) = 2 * (1 + 2 ^ (k - 2)) := by
          have h1 : 2 ^ (k - 1) = 2 * 2 ^ (k - 2) := by
            conv_lhs => rw [show k - 1 = (k - 2) + 1 by omega, pow_succ, mul_comm]
          omega
        have hsplit2 : 2 ^ k = 2 * 2 ^ (k - 1) := by
          conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ, mul_comm]
        rw [hsplit1, hsplit2] at hdvd
        have hstep : 2 ^ (k - 1) ∣ j * (1 + 2 ^ (k - 2)) := by
          have h1 : 2 * 2 ^ (k - 1) ∣ 2 * (j * (1 + 2 ^ (k - 2))) := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using hdvd
          exact (Nat.mul_dvd_mul_iff_left (by decide)).mp h1
        have hcop : (2 ^ (k - 1)).Coprime (1 + 2 ^ (k - 2)) := by
          apply Nat.Coprime.pow_left
          rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
          have hev : 2 ∣ 2 ^ (k - 2) := dvd_pow_self 2 (by omega)
          omega
        obtain ⟨q, hq⟩ := hcop.dvd_of_dvd_mul_right hstep
        have hq01 : q = 0 ∨ q = 1 := by
          have hlt : 2 ^ (k - 1) * q < 2 ^ (k - 1) * 2 := by
            rw [← hq, mul_comm, ← hsplit2]; exact hj_lt
          have hlt2 : q < 2 := Nat.lt_of_mul_lt_mul_left hlt
          omega
        rcases hq01 with rfl | rfl
        · right; right; left; simp [hq]
        · right; right; right; simp [hq, z]
    · rintro (rfl | rfl | rfl | rfl)
      · exact one_pow 2
      · exact hz_sq
      · exact hc2
      · have hcomm : Commute c z := by
          calc c * z = (c * z * c⁻¹) * c := by group
            _ = z * c := by rw [hz_cent c]
        rw [hcomm.mul_pow, hc2, hz_sq, one_mul]
  have hcz_comm : c * z = z * c := by
    calc c * z = (c * z * c⁻¹) * c := by group
      _ = z * c := by rw [hz_cent c]
  have hE_comm_pair : ∀ {u v : P}, u ∈ B → u ^ 2 = 1 → v ∈ B → v ^ 2 = 1 → u * v = v * u := by
    intro u v huB hu2 hvB hv2
    have hform : ∀ w ∈ B, w ^ 2 = 1 → ∃ i j : ℕ, w = c ^ i * z ^ j := fun w hwB hw2 => by
      rcases (hE_char w hwB).mp hw2 with rfl | rfl | rfl | rfl
      · exact ⟨0, 0, by simp⟩
      · exact ⟨0, 1, by simp⟩
      · exact ⟨1, 0, by simp⟩
      · exact ⟨1, 1, by simp⟩
    obtain ⟨i₁, j₁, rfl⟩ := hform u huB hu2
    obtain ⟨i₂, j₂, rfl⟩ := hform v hvB hv2
    have hc : Commute (c ^ i₁) (z ^ j₂) := (show Commute c z from hcz_comm).pow_pow i₁ j₂
    have hc2 : Commute (z ^ j₁) (c ^ i₂) := (show Commute z c from hcz_comm.symm).pow_pow j₁ i₂
    calc (c ^ i₁ * z ^ j₁) * (c ^ i₂ * z ^ j₂)
        = c ^ i₁ * (z ^ j₁ * c ^ i₂) * z ^ j₂ := by group
      _ = c ^ i₁ * (c ^ i₂ * z ^ j₁) * z ^ j₂ := by rw [hc2]
      _ = c ^ (i₁ + i₂) * z ^ (j₁ + j₂) := by rw [← mul_assoc, ← pow_add, mul_assoc, ← pow_add]
      _ = c ^ (i₂ + i₁) * z ^ (j₂ + j₁) := by rw [add_comm i₁ i₂, add_comm j₁ j₂]
      _ = c ^ i₂ * (c ^ i₁ * z ^ j₂) * z ^ j₁ := by rw [pow_add, pow_add]; group
      _ = c ^ i₂ * (z ^ j₂ * c ^ i₁) * z ^ j₁ := by rw [hc]
      _ = (c ^ i₂ * z ^ j₂) * (c ^ i₁ * z ^ j₁) := by group
  let E : Subgroup P :=
    { carrier := {y ∈ B | y ^ 2 = 1}
      mul_mem' := fun {u v} ⟨huB, hu2⟩ ⟨hvB, hv2⟩ => by
        refine ⟨B.mul_mem huB hvB, ?_⟩
        have hcomm : Commute u v := hE_comm_pair huB hu2 hvB hv2
        rw [hcomm.mul_pow, hu2, hv2, one_mul]
      one_mem' := ⟨B.one_mem, one_pow 2⟩
      inv_mem' := fun {u} ⟨huB, hu2⟩ => ⟨B.inv_mem huB, by rw [inv_pow, hu2, inv_one]⟩ }
  have hEnorm : E.Normal := by
    constructor
    intro u hu h
    obtain ⟨huB, hu2⟩ := hu
    exact ⟨hB_norm.conj_mem u huB h, by rw [conj_pow, hu2, mul_one, mul_inv_cancel]⟩
  have hEcomm : ∀ u ∈ E, ∀ v ∈ E, u * v = v * u := fun _ hu _ hv =>
    hE_comm_pair hu.1 hu.2 hv.1 hv.2
  have hEcyc : IsCyclic E := (clifford_homog_of_primitive hpP φ hfaith hprim E hEnorm hEcomm).1
  -- Yet E has 4 distinct elements 1, z, c, c * z, all satisfying u ^ 2 = 1, so E is NOT cyclic!
  obtain ⟨⟨e, heE⟩, hegen⟩ := IsCyclic.exists_generator (α := E)
  have he2 : (⟨e, heE⟩ : E) ^ 2 = 1 := Subtype.ext heE.2
  have hE_le2 : ∀ y : E, y = 1 ∨ y = ⟨e, heE⟩ := by
    intro y
    obtain ⟨n, rfl⟩ := hegen y
    obtain ⟨j, hj_lt, hpow⟩ := zpow_eq_pow_mod (⟨e, heE⟩ : E) (by decide) he2 n
    dsimp only
    rw [hpow]
    have h01 : j = 0 ∨ j = 1 := by omega
    rcases h01 with rfl | rfl
    · left; rw [pow_zero]
    · right; rw [pow_one]
  have hzE : z ∈ E := ⟨hA_le_B (A.pow_mem hxA _), hz_sq⟩
  have hcE : c ∈ E := ⟨hcB, hc2⟩
  have hcz_ne : c ≠ z := fun h => hc_notA (h ▸ A.pow_mem hxA _)
  have hc_ne1 : c ≠ 1 := fun h => hc_notA (h ▸ A.one_mem)
  rcases hE_le2 ⟨z, hzE⟩ with hz1 | hze
  · exact hz_ne1 (congrArg Subtype.val hz1)
  · rcases hE_le2 ⟨c, hcE⟩ with hc1 | hce
    · exact hc_ne1 (congrArg Subtype.val hc1)
    · exact hcz_ne (congrArg Subtype.val (hce.trans hze.symm))

lemma not_isPGroup_two {p d : ℕ} [Fact p.Prime] (hp7 : 7 ≤ p) (hd : 0 < d)
    {H : Type*} [Group H] [Fintype H] (hpH : ¬ (p ∣ Nat.card H))
    (hHrat : ∀ (x : H) (n : ℕ), (Nat.card H).Coprime n → IsConj x (x ^ n))
    (ρ : H →* ((Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)))
    (hirred : ∀ W : Submodule (ZMod p) (Fin d → ZMod p),
      (∀ h : H, ∀ v ∈ W, ρ h v ∈ W) → W = ⊥ ∨ W = ⊤)
    (heig : ∀ (v : Fin d → ZMod p), v ≠ 0 → ∀ (c : (ZMod p)ˣ), ∃ h : H, ρ h v = (c : ZMod p) • v) :
    ¬ IsPGroup 2 H := by
  classical
  intro hH2
  -- Step 1: p - 1 divides |H|, so p - 1 is a power of 2 ≥ 6, hence 4 ∣ p - 1 and ∃ ι, ι^2 = -1
  let v₀ : Fin d → ZMod p := fun _ => 1
  have hv₀ : v₀ ≠ 0 := fun h0 => one_ne_zero (congrFun h0 ⟨0, hd⟩)
  let N : Subgroup H :=
    { carrier := {h : H | ∃ c : (ZMod p)ˣ, ρ h v₀ = (c : ZMod p) • v₀}
      mul_mem' := fun {a b} ⟨ca, ha⟩ ⟨cb, hb⟩ =>
        ⟨ca * cb, by
          simp only [map_mul]
          change ρ a (ρ b v₀) = _
          rw [hb, map_smul, ha, smul_smul]
          push_cast
          rw [mul_comm]⟩
      one_mem' := ⟨1, by simp⟩
      inv_mem' := fun {a} ⟨ca, ha⟩ => ⟨ca⁻¹, by
        apply (ρ a).injective
        have hm : ρ a (ρ a⁻¹ v₀) = v₀ := by
          have : ρ a (ρ a⁻¹ v₀) = ρ (a * a⁻¹) v₀ := by rw [map_mul]; rfl
          rw [this, mul_inv_cancel, map_one]; rfl
        rw [hm, map_smul, ha, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]⟩ }
  have hscal_uniq : ∀ (c₁ c₂ : (ZMod p)ˣ), (c₁ : ZMod p) • v₀ = (c₂ : ZMod p) • v₀ → c₁ = c₂ := by
    intro c₁ c₂ h
    have h1 : ((c₁ : ZMod p) - (c₂ : ZMod p)) • v₀ = 0 := by rw [sub_smul, h, sub_self]
    exact Units.ext (sub_eq_zero.mp ((smul_eq_zero.mp h1).resolve_right hv₀))
  choose scal hscal using fun x : N => x.2
  let ψ : N →* (ZMod p)ˣ :=
    { toFun := scal
      map_one' := hscal_uniq _ 1 (by rw [← hscal 1]; simp)
      map_mul' := fun a b => hscal_uniq _ _ (by
        rw [← hscal (a * b)]
        change ρ ((a : H) * (b : H)) v₀ = _
        rw [map_mul]
        change ρ (a : H) (ρ (b : H) v₀) = _
        rw [hscal b, map_smul, hscal a, smul_smul]
        push_cast; rw [mul_comm]) }
  have hψ_surj : Function.Surjective ψ := fun c => by
    obtain ⟨h, hh⟩ := heig v₀ hv₀ c
    exact ⟨⟨h, ⟨c, hh⟩⟩, hscal_uniq _ c (by
      change (scal ⟨h, ⟨c, hh⟩⟩ : ZMod p) • v₀ = _
      rw [← hscal ⟨h, ⟨c, hh⟩⟩]; exact hh)⟩
  have hpm1_dvd_H : p - 1 ∣ Nat.card H := by
    have h1 : Nat.card (ZMod p)ˣ ∣ Nat.card N := by
      have hcard_q : Nat.card (N ⧸ ψ.ker) = Nat.card (ZMod p)ˣ :=
        Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψ_surj).toEquiv
      rw [← hcard_q]
      have hlag := Subgroup.card_mul_index ψ.ker
      exact ⟨Nat.card ψ.ker, by rw [mul_comm]; exact hlag.symm⟩
    have hcard_u : Nat.card (ZMod p)ˣ = p - 1 := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units p]
    rw [← hcard_u]
    exact dvd_trans h1 (Subgroup.card_subgroup_dvd_card N)
  have h4_dvd : 4 ∣ p - 1 := by
    obtain ⟨k, hk⟩ := hH2.exists_card_eq
    rw [hk] at hpm1_dvd_H
    obtain ⟨a, _, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hpm1_dvd_H
    have ha2 : 2 ≤ a := by
      by_contra hlt
      have hle : a ≤ 1 := by omega
      interval_cases a <;> omega
    rw [ha]; exact pow_dvd_pow 2 ha2
  -- Extract ι ∈ ZMod p with ι^2 = -1
  obtain ⟨gen, hgen⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hgen_ord : orderOf gen = p - 1 := by
    rw [← Nat.card_zpowers, show Subgroup.zpowers gen = ⊤ from by
      rw [eq_top_iff]; intro x _; exact hgen x, Subgroup.card_top, Nat.card_eq_fintype_card,
      ZMod.card_units p]
  obtain ⟨b, hb⟩ := h4_dvd
  have hb_pos : 0 < b := by rcases Nat.eq_zero_or_pos b with rfl | hpos <;> [omega; exact hpos]
  let u4 : (ZMod p)ˣ := gen ^ b
  have hu4_ord : orderOf u4 = 4 := by
    have hgcd : (4 * b).gcd b = b := Nat.gcd_eq_right (dvd_mul_left b 4)
    rw [orderOf_pow, hgen_ord, hb, hgcd, Nat.mul_div_cancel 4 hb_pos]
  have hι : (u4 : ZMod p) ^ 2 = -1 := by
    have h4 : (u4 : ZMod p) ^ 4 = 1 := by
      have h : u4 ^ 4 = 1 := by rw [← hu4_ord, pow_orderOf_eq_one]
      have h' := congrArg Units.val h
      simpa using h'
    have hne1 : (u4 : ZMod p) ^ 2 ≠ 1 := by
      intro h1
      have hu2 : u4 ^ 2 = 1 := Units.ext (by push_cast; exact h1)
      have hdvd : orderOf u4 ∣ 2 := orderOf_dvd_of_pow_eq_one hu2
      rw [hu4_ord] at hdvd; omega
    have hfac : ((u4 : ZMod p) ^ 2 - 1) * ((u4 : ZMod p) ^ 2 + 1) = 0 := by
      calc ((u4 : ZMod p) ^ 2 - 1) * ((u4 : ZMod p) ^ 2 + 1)
          = (u4 : ZMod p) ^ 4 - 1 := by ring
        _ = 0 := by rw [h4, sub_self]
    rcases mul_eq_zero.mp hfac with h1 | h2
    · exact absurd (sub_eq_zero.mp h1) hne1
    · exact eq_neg_of_add_eq_zero_left h2
  -- Step 2: Maximal imprimitivity decomposition + Universal Monomial Killer vs Primitive 2-Group Theorem
  obtain ⟨m, W, hm1, hWind, hWsup, hWne, hWperm, htrans, hmax⟩ :=
    exists_maximal_imprimitivity hd ρ hirred
  have hstab := block_stabilizer_irred_primitive hpH ρ m hm1 W hWind hWsup hWne hWperm htrans hmax
  let i₀ : Fin m := ⟨0, hm1⟩
  let H₀ : Subgroup H :=
    { carrier := {h : H | Submodule.map (ρ h).toLinearMap (W i₀) = W i₀}
      mul_mem' := fun {a b} ha hb => by
        change Submodule.map (ρ (a * b)).toLinearMap (W i₀) = W i₀
        have hcomp : (ρ (a * b)).toLinearMap = (ρ a).toLinearMap.comp (ρ b).toLinearMap := by
          ext x; simp
        rw [hcomp, Submodule.map_comp, hb, ha]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        change Submodule.map (ρ a⁻¹).toLinearMap (W i₀) = W i₀
        have hcomp : (ρ (a⁻¹ * a)).toLinearMap = (ρ a⁻¹).toLinearMap.comp (ρ a).toLinearMap := by
          ext x; simp
        calc Submodule.map (ρ a⁻¹).toLinearMap (W i₀)
            = Submodule.map ((ρ a⁻¹).toLinearMap.comp (ρ a).toLinearMap) (W i₀) := by
                rw [Submodule.map_comp, ha]
          _ = Submodule.map (ρ (a⁻¹ * a)).toLinearMap (W i₀) := by rw [← hcomp]
          _ = W i₀ := by rw [inv_mul_cancel]; simp }
  -- Restrict ρ to H₀ acting on W i₀, then quotient by kernel K₀ to get faithful primitive 2-group P!
  have hH₀_mem : ∀ (h : H₀) (v : Fin d → ZMod p), v ∈ W i₀ → ρ (h : H) v ∈ W i₀ := fun h v hv => by
    rw [← h.2]; exact Submodule.mem_map_of_mem hv
  let φ₀ : H₀ →* ((W i₀) ≃ₗ[ZMod p] (W i₀)) :=
    { toFun := fun h =>
        LinearEquiv.ofLinearMap
          ((ρ (h : H)).toLinearMap.restrict (fun x hx => hH₀_mem h x hx))
          ((ρ ((h⁻¹ : H₀) : H)).toLinearMap.restrict (fun x hx => hH₀_mem h⁻¹ x hx))
          (LinearMap.ext fun ⟨x, hx⟩ => Subtype.ext (by
            change ρ (h : H) (ρ (h : H)⁻¹ x) = x
            have h1 : ρ (h : H) (ρ (h : H)⁻¹ x) = ρ ((h : H) * (h : H)⁻¹) x := by rw [map_mul]; rfl
            rw [h1, mul_inv_cancel, map_one]; rfl))
          (LinearMap.ext fun ⟨x, hx⟩ => Subtype.ext (by
            change ρ (h : H)⁻¹ (ρ (h : H) x) = x
            have h1 : ρ (h : H)⁻¹ (ρ (h : H) x) = ρ ((h : H)⁻¹ * (h : H)) x := by rw [map_mul]; rfl
            rw [h1, inv_mul_cancel, map_one]; rfl))
      map_one' := LinearEquiv.ext fun ⟨x, hx⟩ => Subtype.ext (by
        change ρ 1 x = x; rw [map_one]; rfl)
      map_mul' := fun a b => LinearEquiv.ext fun ⟨x, hx⟩ => Subtype.ext (by
        change ρ ((a : H) * (b : H)) x = ρ (a : H) (ρ (b : H) x); rw [map_mul]; rfl) }
  let P := H₀ ⧸ φ₀.ker
  have hP2 : IsPGroup 2 P := (hH2.to_subgroup H₀).to_quotient φ₀.ker
  let φP : P →* ((W i₀) ≃ₗ[ZMod p] (W i₀)) := QuotientGroup.lift φ₀.ker φ₀ le_rfl
  have hφP_inj : Function.Injective φP := by
    intro x y hxy
    refine QuotientGroup.induction_on x (fun a => QuotientGroup.induction_on y (fun b h => ?_)) hxy
    rw [QuotientGroup.eq]
    show a⁻¹ * b ∈ φ₀.ker
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    have hab : φ₀ a = φ₀ b := h
    rw [hab, inv_mul_cancel]
  have hW₀_nt : Nontrivial (W i₀) := by
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hWne i₀)
    exact ⟨⟨⟨v, hv⟩, 0, fun h => hv0 (congrArg Subtype.val h)⟩⟩
  have hP_irred : ∀ U : Submodule (ZMod p) (W i₀), (∀ g : P, ∀ v ∈ U, φP g v ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    let U' : Submodule (ZMod p) (Fin d → ZMod p) := U.map (W i₀).subtype
    have hU'inv : ∀ h : H₀, ∀ v ∈ U', ρ (h : H) v ∈ U' := by
      rintro h _ ⟨x, hx, rfl⟩
      exact Submodule.mem_map.mpr ⟨φ₀ h x, hU (QuotientGroup.mk h) x hx, rfl⟩
    rcases hstab.1 U' (Submodule.map_subtype_le (W i₀) U) hU'inv with hbot | htop
    · left
      rw [Submodule.eq_bot_iff]
      intro x hx
      have hmem : (x : Fin d → ZMod p) ∈ U' := Submodule.mem_map.mpr ⟨x, hx, rfl⟩
      exact Subtype.ext (by simpa [hbot] using hmem)
    · right
      rw [Submodule.eq_top_iff']
      intro x
      have hmem : (x : Fin d → ZMod p) ∈ U' := by rw [htop]; exact x.2
      obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp hmem
      have hxy : y = x := Subtype.ext hyx
      exact hxy ▸ hy
  have hP_prim : ∀ (r : ℕ) (U : Fin r → Submodule (ZMod p) (W i₀)),
      2 ≤ r → iSupIndep U → iSup U = ⊤ → (∀ a, U a ≠ ⊥) →
      ¬ ∀ g : P, ∃ τ : Equiv.Perm (Fin r),
        ∀ a, Submodule.map (φP g).toLinearMap (U a) = U (τ a) := by
    intro r U hr2 hUind hUsup hUne hUperm
    let U' : Fin r → Submodule (ZMod p) (Fin d → ZMod p) := fun a => (U a).map (W i₀).subtype
    have hU'ind : iSupIndep U' := by
      intro a
      rw [Submodule.disjoint_def]
      intro x hx1 hx2
      obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hx1
      have hle : (⨆ (b : Fin r) (_ : b ≠ a), U' b) ≤ (⨆ (b : Fin r) (_ : b ≠ a), U b).map (W i₀).subtype := by
        simp only [Submodule.map_iSup]
        exact iSup₂_le (fun b hb => le_iSup₂ (f := fun b (_ : b ≠ a) => (U b).map (W i₀).subtype) b hb)
      obtain ⟨w, hw, hwu⟩ := Submodule.mem_map.mp (hle hx2)
      have heq : w = u := Subtype.ext hwu
      rw [heq] at hw
      exact congrArg Subtype.val (Submodule.disjoint_def.mp (hUind a) u hu hw)
    have hU'sup : iSup U' = W i₀ := by
      have h1 : iSup U' = (iSup U).map (W i₀).subtype := by simp [U', Submodule.map_iSup]
      rw [h1, hUsup, Submodule.map_top, Submodule.range_subtype]
    have hU'ne : ∀ a : Fin r, U' a ≠ ⊥ := by
      intro a hbot
      obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hUne a)
      have hmem : (u : Fin d → ZMod p) ∈ U' a := Submodule.mem_map.mpr ⟨u, hu, rfl⟩
      exact hu0 (Subtype.ext (by simpa [hbot] using hmem))
    have hU'perm : ∀ h : H₀, ∃ τ : Equiv.Perm (Fin r),
        ∀ a, Submodule.map (ρ (h : H)).toLinearMap (U' a) = U' (τ a) := by
      intro h
      obtain ⟨τ, hτ⟩ := hUperm (QuotientGroup.mk h)
      refine ⟨τ, fun a => ?_⟩
      have h1 : Submodule.map (ρ (h : H)).toLinearMap (U' a) =
          (Submodule.map (φ₀ h).toLinearMap (U a)).map (W i₀).subtype := by
        ext v
        simp only [U', Submodule.mem_map]
        constructor
        · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
          exact ⟨φ₀ h x, ⟨x, hx, rfl⟩, rfl⟩
        · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
          exact ⟨x.1, ⟨x, hx, rfl⟩, rfl⟩
      rw [h1]
      exact congrArg (Submodule.map (W i₀).subtype) (hτ a)
    exact hstab.2 r U' hr2 hU'ind hU'sup hU'ne hU'perm
  have hP_comm := primitive_two_group_abelian hp7 (u4 : ZMod p) hι hP2 φP hφP_inj hP_irred hP_prim
  -- Contradiction with Universal Monomial Killer (block stabilizer acts non-abelianly on W i₀!)
  obtain ⟨i, h₁, h₂, hh₁, hh₂, v, hv, hne⟩ :=
    universal_monomial_killer hp7 hHrat ρ heig m hm1 W hWind hWne hWperm htrans
  obtain ⟨t, ht⟩ := htrans i₀ i
  have ht_inv : Submodule.map (ρ t⁻¹).toLinearMap (W i) = W i₀ := by
    have hcomp : (ρ (t⁻¹ * t)).toLinearMap = (ρ t⁻¹).toLinearMap.comp (ρ t).toLinearMap := by
      ext x; simp
    calc Submodule.map (ρ t⁻¹).toLinearMap (W i)
        = Submodule.map ((ρ t⁻¹).toLinearMap.comp (ρ t).toLinearMap) (W i₀) := by
            rw [Submodule.map_comp, ht]
      _ = Submodule.map (ρ (t⁻¹ * t)).toLinearMap (W i₀) := by rw [← hcomp]
      _ = W i₀ := by rw [inv_mul_cancel]; simp
  have hconj_stab : ∀ h : H, Submodule.map (ρ h).toLinearMap (W i) = W i → t⁻¹ * h * t ∈ H₀ := by
    intro h hh
    change Submodule.map (ρ (t⁻¹ * h * t)).toLinearMap (W i₀) = W i₀
    have h1 : (ρ (t⁻¹ * h * t)).toLinearMap =
        (ρ t⁻¹).toLinearMap.comp ((ρ h).toLinearMap.comp (ρ t).toLinearMap) := by
      ext x; simp [mul_assoc]
    rw [h1, Submodule.map_comp, Submodule.map_comp, ht, hh, ht_inv]
  let g₁ : H₀ := ⟨t⁻¹ * h₁ * t, hconj_stab h₁ hh₁⟩
  let g₂ : H₀ := ⟨t⁻¹ * h₂ * t, hconj_stab h₂ hh₂⟩
  have hcomm_g : φ₀ (g₁ * g₂) = φ₀ (g₂ * g₁) := by
    have hq : QuotientGroup.mk (g₁ * g₂) = (QuotientGroup.mk (g₂ * g₁) : P) := by
      change (QuotientGroup.mk g₁ : P) * QuotientGroup.mk g₂ =
        QuotientGroup.mk g₂ * QuotientGroup.mk g₁
      exact hP_comm _ _
    exact congrArg φP hq
  have hw_mem : ρ t⁻¹ v ∈ W i₀ := by rw [← ht_inv]; exact Submodule.mem_map_of_mem hv
  have h1 := congrArg (fun f : (W i₀) ≃ₗ[ZMod p] (W i₀) => (f ⟨ρ t⁻¹ v, hw_mem⟩ : Fin d → ZMod p)) hcomm_g
  change ρ ((t⁻¹ * h₁ * t) * (t⁻¹ * h₂ * t)) (ρ t⁻¹ v) =
    ρ ((t⁻¹ * h₂ * t) * (t⁻¹ * h₁ * t)) (ρ t⁻¹ v) at h1
  have hl : (t⁻¹ * h₁ * t) * (t⁻¹ * h₂ * t) * t⁻¹ = t⁻¹ * (h₁ * h₂) := by group
  have hr : (t⁻¹ * h₂ * t) * (t⁻¹ * h₁ * t) * t⁻¹ = t⁻¹ * (h₂ * h₁) := by group
  have h2 : ρ t⁻¹ (ρ (h₁ * h₂) v) = ρ t⁻¹ (ρ (h₂ * h₁) v) := by
    calc ρ t⁻¹ (ρ (h₁ * h₂) v) = ρ (t⁻¹ * (h₁ * h₂)) v := by rw [map_mul ρ t⁻¹ (h₁ * h₂)]; rfl
      _ = ρ ((t⁻¹ * h₁ * t) * (t⁻¹ * h₂ * t) * t⁻¹) v := by rw [hl]
      _ = ρ ((t⁻¹ * h₁ * t) * (t⁻¹ * h₂ * t)) (ρ t⁻¹ v) := by
            rw [map_mul ρ ((t⁻¹ * h₁ * t) * (t⁻¹ * h₂ * t)) t⁻¹]; rfl
      _ = ρ ((t⁻¹ * h₂ * t) * (t⁻¹ * h₁ * t)) (ρ t⁻¹ v) := h1
      _ = ρ ((t⁻¹ * h₂ * t) * (t⁻¹ * h₁ * t) * t⁻¹) v := by
            rw [map_mul ρ ((t⁻¹ * h₂ * t) * (t⁻¹ * h₁ * t)) t⁻¹]; rfl
      _ = ρ (t⁻¹ * (h₂ * h₁)) v := by rw [hr]
      _ = ρ t⁻¹ (ρ (h₂ * h₁) v) := by rw [map_mul ρ t⁻¹ (h₂ * h₁)]; rfl
  exact hne ((ρ t⁻¹).injective h2)

/- ### Component 8: Primitive Abelian Normal Subgroup Theorem and Main Reduction -/

lemma frobenius_roots_of_minpoly {p : ℕ} [Fact p.Prime]
    {E : Type*} [CommRing E] [IsDomain E] [Fintype E] [Algebra (ZMod p) E]
    (α β : E) (hβ : Polynomial.aeval β (minpoly (ZMod p) α) = 0) :
    ∃ j : ℕ, β = α ^ (p ^ j) := by
  classical
  have hp_prime : p.Prime := Fact.out
  let _hField : Field E := Fintype.fieldOfDomain E
  have _hCharP : CharP E p :=
    charP_of_injective_algebraMap (RingHom.injective (algebraMap (ZMod p) E)) p
  have _hExpChar : ExpChar E p := ExpChar.prime hp_prime
  let k := Module.finrank (ZMod p) E
  have hk_pos : 0 < k := Module.finrank_pos
  have hcardE : Fintype.card E = p ^ k := by
    rw [Module.card_eq_pow_finrank (K := ZMod p) (V := E), ZMod.card]
  have hpow_k : α ^ (p ^ k) = α := by
    rw [← hcardE]; exact FiniteField.pow_card α
  let O : Finset E := Finset.univ.image (fun j : Fin k => α ^ (p ^ j.val))
  have hfrob_inj : Function.Injective (fun x : E => x ^ p) := fun _ _ h => frobenius_inj E p h
  have hO_frob : O.image (fun x : E => x ^ p) = O := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
      rw [← pow_mul, ← pow_succ]
      by_cases hj : j.val + 1 < k
      · exact Finset.mem_image.mpr ⟨⟨j.val + 1, hj⟩, Finset.mem_univ _, rfl⟩
      · have heq : j.val + 1 = k := by omega
        rw [heq, hpow_k]
        exact Finset.mem_image.mpr ⟨⟨0, hk_pos⟩, Finset.mem_univ _, by simp⟩
    · rw [Finset.card_image_of_injective O hfrob_inj]
  -- Polynomial g = ∏ x ∈ O, (X - C x) has all coefficients fixed by x ↦ x^p, hence in ZMod p!
  let g : Polynomial E := ∏ x ∈ O, (Polynomial.X - Polynomial.C x)
  have hg_frob : g.map (frobenius E p) = g := by
    simp only [g, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    change ∏ x ∈ O, (Polynomial.X - Polynomial.C (x ^ p)) = ∏ x ∈ O, (Polynomial.X - Polynomial.C x)
    rw [← Finset.prod_image (f := fun x : E => Polynomial.X - Polynomial.C x)
      (fun _ _ _ _ h => hfrob_inj h), hO_frob]
  -- Every c ∈ E with c ^ p = c lies in the range of algebraMap (ZMod p) E
  have hfixed_in_Fp : ∀ c : E, c ^ p = c → ∃ t : ZMod p, algebraMap (ZMod p) E t = c := by
    let P_frob : Polynomial E := Polynomial.X ^ p - Polynomial.X
    have hP_ne0 : P_frob ≠ 0 := by
      intro h0
      have hcoeff : P_frob.coeff p = 0 := by rw [h0]; simp
      have h1 : P_frob.coeff p = 1 := by
        simp [P_frob, Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_X,
          hp_prime.ne_one.symm]
      exact one_ne_zero (h1.symm.trans hcoeff)
    have hdeg : P_frob.natDegree ≤ p := by
      refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
      · exact Polynomial.natDegree_X_pow_le p
      · exact le_trans Polynomial.natDegree_X_le hp_prime.one_le
    let Fp_img : Finset E := Finset.univ.image (algebraMap (ZMod p) E)
    have hFp_card : Fp_img.card = p := by
      rw [Finset.card_image_of_injective _ (RingHom.injective (algebraMap (ZMod p) E)),
        Finset.card_univ, ZMod.card]
    have hFp_sub : Fp_img ⊆ P_frob.roots.toFinset := by
      intro x hx
      obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hx
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hP_ne0, Polynomial.IsRoot.def]
      simp only [P_frob, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        ← map_pow, ZMod.pow_card, sub_self]
    have hroots_le : P_frob.roots.toFinset.card ≤ p :=
      le_trans (Multiset.toFinset_card_le _) (le_trans (Polynomial.card_roots' P_frob) hdeg)
    have heq_sets : Fp_img = P_frob.roots.toFinset :=
      Finset.eq_of_subset_of_card_le hFp_sub (hFp_card.symm ▸ hroots_le)
    intro c hc
    have hc_root : c ∈ P_frob.roots.toFinset := by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hP_ne0, Polynomial.IsRoot.def]
      simp [P_frob, hc]
    rw [← heq_sets] at hc_root
    obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hc_root
    exact ⟨t, ht⟩
  have hcoeff_in : ∀ n : ℕ, ∃ t : ZMod p, algebraMap (ZMod p) E t = g.coeff n := by
    intro n
    apply hfixed_in_Fp (g.coeff n)
    have h := congrArg (fun q : Polynomial E => q.coeff n) hg_frob
    rw [Polynomial.coeff_map] at h
    exact h
  choose t_coeff ht_coeff using hcoeff_in
  let g₀ : Polynomial (ZMod p) := ∑ n ∈ g.support, Polynomial.monomial n (t_coeff n)
  have hg₀_map : g₀.map (algebraMap (ZMod p) E) = g := by
    ext n
    rw [Polynomial.coeff_map]
    simp only [g₀, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    by_cases hn : n ∈ g.support
    · rw [Finset.sum_eq_single n]
      · simp [ht_coeff n]
      · intro b _ hbn; simp [hbn]
      · intro h; exact absurd hn h
    · rw [Finset.sum_eq_zero (fun b hb => by simp [show b ≠ n from fun h => hn (h ▸ hb)])]
      rw [map_zero]
      exact (Polynomial.notMem_support_iff.mp hn).symm
  have hg₀_eval : Polynomial.aeval α g₀ = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hg₀_map]
    simp only [g, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact Finset.prod_eq_zero (Finset.mem_image.mpr ⟨⟨0, hk_pos⟩, Finset.mem_univ _, by simp⟩)
      (sub_self α)
  have hdvd : minpoly (ZMod p) α ∣ g₀ := minpoly.dvd (ZMod p) α hg₀_eval
  obtain ⟨q, hq⟩ := hdvd
  have hg_β : Polynomial.eval β g = 0 := by
    rw [← hg₀_map, ← Polynomial.eval₂_eq_eval_map, ← Polynomial.aeval_def, hq, map_mul, hβ, zero_mul]
  simp only [g, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hg_β
  obtain ⟨x, hxO, hx0⟩ := Finset.prod_eq_zero_iff.mp hg_β
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hxO
  exact ⟨j.val, sub_eq_zero.mp hx0⟩

lemma totient_le_two_cases {n : ℕ} (hn : 0 < n) (hφ : Nat.totient n ≤ 2) :
    n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6 := by
  have hle6 : n ≤ 6 := by
    by_contra hgt
    have hn7 : 7 ≤ n := by omega
    by_cases h5 : ∃ q : ℕ, q.Prime ∧ 5 ≤ q ∧ q ∣ n
    · obtain ⟨q, hq, hq5, hqn⟩ := h5
      have hdvd : Nat.totient q ∣ Nat.totient n := Nat.totient_dvd_of_dvd hqn
      have hpos : 0 < Nat.totient n := Nat.totient_pos.mpr hn
      have hle := Nat.le_of_dvd hpos hdvd
      rw [Nat.totient_prime hq] at hle
      omega
    · push Not at h5
      -- Only primes 2 and 3 can divide n
      have hpow23 : n = 2 ^ (n.factorization 2) * 3 ^ (n.factorization 3) := by
        let a := n.factorization 2
        let b := n.factorization 3
        have h2a : 2 ^ a ∣ n := Nat.ordProj_dvd n 2
        have h3b : 3 ^ b ∣ n := Nat.ordProj_dvd n 3
        have hcop : (2 ^ a).Coprime (3 ^ b) :=
          (Nat.Coprime.pow_left a (Nat.Coprime.pow_right b (by decide)))
        have hprod : 2 ^ a * 3 ^ b ∣ n := hcop.mul_dvd_of_dvd_of_dvd h2a h3b
        let u := n / (2 ^ a * 3 ^ b)
        have hu_eq : 2 ^ a * 3 ^ b * u = n := Nat.mul_div_cancel' hprod
        have hu1 : u = 1 := by
          by_contra hne1
          obtain ⟨q, hq, hqu⟩ := Nat.exists_prime_and_dvd hne1
          have hqn : q ∣ n := dvd_trans hqu (hu_eq ▸ dvd_mul_left u _)
          have hq_le4 : q ≤ 4 := by
            by_contra hq5; exact h5 q hq (by omega) hqn
          have hq2 := hq.two_le
          interval_cases q
          · have h1 : 2 ^ (a + 1) ∣ n := by
              calc 2 ^ (a + 1) = 2 ^ a * 2 := pow_succ 2 a
                _ ∣ 2 ^ a * u := mul_dvd_mul_left _ hqu
                _ ∣ 2 ^ a * u * 3 ^ b := dvd_mul_right _ _
                _ = n := by rw [← hu_eq]; ring
            have hle := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hn.ne').mp h1
            omega
          · have h1 : 3 ^ (b + 1) ∣ n := by
              calc 3 ^ (b + 1) = 3 ^ b * 3 := pow_succ 3 b
                _ ∣ 3 ^ b * u := mul_dvd_mul_left _ hqu
                _ ∣ 3 ^ b * u * 2 ^ a := dvd_mul_right _ _
                _ = n := by rw [← hu_eq]; ring
            have hle := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hn.ne').mp h1
            omega
          · exact absurd hq (by decide)
        rw [hu1, mul_one] at hu_eq
        exact hu_eq.symm
      have hφ_pos : 0 < Nat.totient n := Nat.totient_pos.mpr hn
      have ha_le2 : n.factorization 2 ≤ 2 := by
        by_contra hgt3
        have h8 : 8 ∣ n := by
          rw [hpow23]; exact dvd_mul_of_dvd_left (pow_dvd_pow 2 (show 3 ≤ n.factorization 2 by omega)) _
        have hle := Nat.le_of_dvd hφ_pos (Nat.totient_dvd_of_dvd h8)
        have : Nat.totient 8 = 4 := by decide
        omega
      have hb_le1 : n.factorization 3 ≤ 1 := by
        by_contra hgt2
        have h9 : 9 ∣ n := by
          rw [hpow23]; exact dvd_mul_of_dvd_right (pow_dvd_pow 3 (show 2 ≤ n.factorization 3 by omega)) _
        have hle := Nat.le_of_dvd hφ_pos (Nat.totient_dvd_of_dvd h9)
        have : Nat.totient 9 = 6 := by decide
        omega
      have ha_eq : n.factorization 2 = 0 ∨ n.factorization 2 = 1 ∨ n.factorization 2 = 2 := by omega
      have hb_eq : n.factorization 3 = 0 ∨ n.factorization 3 = 1 := by omega
      rcases ha_eq with h1 | h1 | h1 <;> rcases hb_eq with h2 | h2
      all_goals rw [h1, h2] at hpow23
      all_goals norm_num at hpow23
      all_goals try omega
      -- Remaining case: n = 12, φ(12) = 4 > 2
      rw [hpow23] at hφ
      have : Nat.totient 12 = 4 := by decide
      omega
  interval_cases n
  · left; rfl
  · right; left; rfl
  · right; right; left; rfl
  · right; right; right; left; rfl
  · exfalso
    have : Nat.totient 5 = 4 := by decide
    omega
  · right; right; right; right; rfl

lemma abelian_normal_order_of_primitive {p d : ℕ} [Fact p.Prime] (_hp7 : 7 ≤ p) (hd : 0 < d)
    {H : Type*} [Group H] [Fintype H] (hpH : ¬ (p ∣ Nat.card H))
    (hHrat : ∀ (x : H) (n : ℕ), (Nat.card H).Coprime n → IsConj x (x ^ n))
    (ρ : H →* ((Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)))
    (hfaith : Function.Injective ρ)
    (hprim : ∀ (r : ℕ) (U : Fin r → Submodule (ZMod p) (Fin d → ZMod p)),
      2 ≤ r → iSupIndep U → iSup U = ⊤ → (∀ a, U a ≠ ⊥) →
      ¬ ∀ g : H, ∃ τ : Equiv.Perm (Fin r),
        ∀ a, Submodule.map (ρ g).toLinearMap (U a) = U (τ a))
    (A : Subgroup H) (hAnorm : A.Normal) (hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    (Nat.card A = 1 ∨ Nat.card A = 2 ∨ Nat.card A = 3 ∨ Nat.card A = 4 ∨ Nat.card A = 6) ∧
    (3 ∣ Nat.card A → p % 3 = 2) ∧ (4 ∣ Nat.card A → p % 4 = 3) := by
  classical
  have hVnt : Nontrivial (Fin d → ZMod p) :=
    ⟨⟨fun _ => 1, 0, fun h => one_ne_zero (congrFun h ⟨0, hd⟩)⟩⟩
  obtain ⟨hAcyc, U₀, hU₀ne, hU₀inv, hU₀irr, hfaith_U₀, hpoly_U₀⟩ :=
    clifford_homog_of_primitive hpH ρ hfaith hprim A hAnorm hAcomm
  let n := Nat.card A
  change (n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6) ∧ (3 ∣ n → p % 3 = 2) ∧ (4 ∣ n → p % 4 = 3)
  have hn_pos : 0 < n := Nat.card_pos
  by_cases hn1 : n = 1
  · refine ⟨Or.inl hn1, fun h3 => by rw [hn1] at h3; omega, fun h4 => by rw [hn1] at h4; omega⟩
  have hn2 : 2 ≤ n := by omega
  have : NeZero n := ⟨hn_pos.ne'⟩
  have : Fact (1 < n) := ⟨by omega⟩
  -- Generator a of cyclic A has order n
  obtain ⟨⟨a, haA⟩, hagen⟩ := IsCyclic.exists_generator (α := A)
  have ha_ord : orderOf a = n := by
    have h1 : orderOf (⟨a, haA⟩ : A) = n := by
      rw [← Nat.card_zpowers, show Subgroup.zpowers (⟨a, haA⟩ : A) = ⊤ from by
        rw [eq_top_iff]; intro y _; exact hagen y, Subgroup.card_top]
    exact (Subgroup.orderOf_coe (⟨a, haA⟩ : A)).trans h1
  have hzpow : Subgroup.zpowers a = A := by
    have hle : Subgroup.zpowers a ≤ A := Subgroup.zpowers_le.mpr haA
    have hcard_eq : Nat.card (Subgroup.zpowers a) = Nat.card A := by rw [Nat.card_zpowers, ha_ord]
    exact Subgroup.eq_of_le_of_card_ge hle hcard_eq.ge
  -- Step 1: Every unit u ∈ (ZMod n)ˣ satisfies u ^ 2 = 1 (via rationality of H!)
  have hconj_ex : ∀ g : H, ∃ k : ZMod n, g * a * g⁻¹ = a ^ k.val := by
    intro g
    have hmem : g * a * g⁻¹ ∈ Subgroup.zpowers a := hzpow ▸ hAnorm.conj_mem a haA g
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine ⟨(m : ZMod n), ?_⟩
    rw [← hm, ← zpow_natCast]
    have hdvd : (orderOf a : ℤ) ∣ ((m : ZMod n).val : ℤ) - m := by
      rw [ha_ord, ← ZMod.intCast_zmod_eq_zero_iff_dvd]; simp
    obtain ⟨t, ht⟩ := hdvd
    have hmeq : ((m : ZMod n).val : ℤ) = m + (orderOf a : ℤ) * t := by linarith
    rw [hmeq, zpow_add, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow, mul_one]
  have hpow_inj : ∀ u v : ZMod n, a ^ u.val = a ^ v.val → u = v := by
    intro u v huv
    have hmod : u.val ≡ v.val [MOD orderOf a] := pow_eq_pow_iff_modEq.mp huv
    rw [ha_ord] at hmod
    simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
  choose α hα using hconj_ex
  have hα_mul : ∀ g₁ g₂ : H, α (g₁ * g₂) = α g₁ * α g₂ := by
    intro g₁ g₂
    apply hpow_inj
    have h1 : (g₁ * g₂) * a * (g₁ * g₂)⁻¹ = g₁ * (g₂ * a * g₂⁻¹) * g₁⁻¹ := by group
    rw [hα (g₁ * g₂), hα g₂, ← conj_pow, hα g₁, ← pow_mul] at h1
    have h2 : a ^ ((α g₁ * α g₂).val) = a ^ ((α g₁).val * (α g₂).val) := by
      rw [← pow_mod_orderOf, ← pow_mod_orderOf (n := (α g₁).val * (α g₂).val), ha_ord]
      congr 1; rw [ZMod.val_mul]; exact Nat.mod_mod _ _
    exact h1.trans h2.symm
  have hα1 : α 1 = 1 := by
    apply hpow_inj; rw [← hα 1, ZMod.val_one]; group
  have hu_sq : ∀ u : (ZMod n)ˣ, (u : ZMod n) ^ 2 = 1 := by
    intro u
    have hcop : (orderOf a).Coprime (u : ZMod n).val := by
      rw [ha_ord]; exact (ZMod.val_coe_unit_coprime u).symm
    obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_pow_of_coprime_orderOf hHrat a hcop)
    have hαg : α g = (u : ZMod n) := hpow_inj _ _ ((hα g).symm.trans hg)
    have hH_pos : 0 < Nat.card H := Nat.card_pos
    have hcop_sub : (Nat.card H).Coprime (Nat.card H - 1) := by
      cases hH : Nat.card H with
      | zero => omega
      | succ k =>
        change Nat.gcd (k + 1) k = 1
        rw [Nat.gcd_comm, Nat.gcd_rec]; simp
    obtain ⟨h, hh⟩ := isConj_iff.mp (hHrat g (Nat.card H - 1) hcop_sub)
    have hg_inv : g ^ (Nat.card H - 1) = g⁻¹ := by
      have hpow : g ^ Nat.card H = 1 := by rw [Nat.card_eq_fintype_card]; exact pow_card_eq_one
      exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, Nat.sub_add_cancel hH_pos, hpow])
    rw [hg_inv] at hh
    have hα_comm : α (h * g * h⁻¹) = α g := by
      have hinv : α h * α h⁻¹ = 1 := by rw [← hα_mul, mul_inv_cancel, hα1]
      rw [hα_mul, hα_mul, mul_comm (α h) (α g), mul_assoc, hinv, mul_one]
    calc (u : ZMod n) ^ 2 = α g * α g := by rw [hαg, pow_two]
      _ = α (h * g * h⁻¹) * α g := by rw [hα_comm]
      _ = α g⁻¹ * α g := by rw [hh]
      _ = α (g⁻¹ * g) := (hα_mul _ _).symm
      _ = 1 := by rw [inv_mul_cancel, hα1]
  -- Step 2: Build the finite field E = Algebra.adjoin (ZMod p) {ρ a|_{U₀}} ⊆ End(U₀)
  let ψa : Module.End (ZMod p) U₀ := (ρ a).toLinearMap.restrict (fun x hx => hU₀inv ⟨a, haA⟩ x hx)
  let E : Subalgebra (ZMod p) (Module.End (ZMod p) U₀) := Algebra.adjoin (ZMod p) {ψa}
  have hE_comm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    intro x hx
    refine Algebra.adjoin_induction (p := fun x _ => ∀ y ∈ E, x * y = y * x)
      (fun x hxS y hy => ?_)
      (fun r y _ => Algebra.commutes r y)
      (fun x₁ x₂ _ _ ih₁ ih₂ y hy => by rw [add_mul, mul_add, ih₁ y hy, ih₂ y hy])
      (fun x₁ x₂ _ _ ih₁ ih₂ y hy => by rw [mul_assoc, ih₂ y hy, ← mul_assoc, ih₁ y hy, mul_assoc])
      hx
    rw [Set.mem_singleton_iff.mp hxS]
    refine Algebra.adjoin_induction (p := fun y _ => ψa * y = y * ψa)
      (fun y hyS => by rw [Set.mem_singleton_iff.mp hyS])
      (fun r => (Algebra.commutes r ψa).symm)
      (fun y₁ y₂ _ _ ih₁ ih₂ => by rw [mul_add, add_mul, ih₁, ih₂])
      (fun y₁ y₂ _ _ ih₁ ih₂ => by rw [← mul_assoc, ih₁, mul_assoc, ih₂, ← mul_assoc])
      hy
  -- Every nonzero f ∈ E commutes with A (since A = ⟨a⟩) hence is injective on irreducible U₀!
  have hE_inj : ∀ f ∈ E, f ≠ 0 → Function.Injective f := by
    intro f hf hf0
    rw [← LinearMap.ker_eq_bot]
    let K : Submodule (ZMod p) (Fin d → ZMod p) := (LinearMap.ker f).map U₀.subtype
    have hKinv : ∀ b : A, ∀ v ∈ K, ρ (b : H) v ∈ K := by
      intro b v hv
      obtain ⟨x, hxker, rfl⟩ := Submodule.mem_map.mp hv
      have hcomm_a : f * ψa = ψa * f := hE_comm f hf ψa (Algebra.subset_adjoin rfl)
      obtain ⟨j, _, hj⟩ : ∃ j : ℕ, j < n ∧ (b : H) = a ^ j := by
        obtain ⟨m, hm⟩ := hagen b
        have hb_eq : (b : H) = a ^ m := (congrArg Subtype.val hm).symm
        obtain ⟨j, hj_lt, hpow⟩ :=
          zpow_eq_pow_mod a hn_pos (ha_ord ▸ pow_orderOf_eq_one a) m
        exact ⟨j, hj_lt, hb_eq.trans hpow⟩
      have hcomm_pow : f * ψa ^ j = ψa ^ j * f := Commute.pow_right hcomm_a j
      have hψpow : ∀ (k : ℕ) (w : U₀), ((ψa ^ k) w : Fin d → ZMod p) = ρ (a ^ k) w.1 := by
        intro k
        induction k with
        | zero => intro w; simp [pow_zero]
        | succ k ih =>
          intro w
          rw [pow_succ', pow_succ']
          change ρ a ((ψa ^ k) w).1 = ρ (a * a ^ k) w.1
          rw [ih w, map_mul]; rfl
      refine Submodule.mem_map.mpr ⟨(ψa ^ j) x, ?_, by
        change ((ψa ^ j) x : Fin d → ZMod p) = ρ (b : H) x.1
        rw [hψpow j x, ← hj]⟩
      rw [LinearMap.mem_ker] at hxker ⊢
      change (f * ψa ^ j) x = 0
      rw [hcomm_pow]
      change (ψa ^ j) (f x) = 0
      rw [hxker, map_zero]
    rcases hU₀irr K (Submodule.map_subtype_le U₀ _) hKinv with hbot | htop
    · rw [Submodule.eq_bot_iff]
      intro x hx
      have hmem : (x : Fin d → ZMod p) ∈ K := Submodule.mem_map.mpr ⟨x, hx, rfl⟩
      exact Subtype.ext (by simpa [hbot] using hmem)
    · exfalso; apply hf0
      refine LinearMap.ext fun x => ?_
      have hmem : (x : Fin d → ZMod p) ∈ K := by rw [htop]; exact x.2
      obtain ⟨y, hyker, hyx⟩ := Submodule.mem_map.mp hmem
      have hxy : y = x := Subtype.ext hyx
      rw [← hxy]; exact LinearMap.mem_ker.mp hyker
  let hE_commRing : CommRing E :=
    { (inferInstance : Ring E) with
      mul_comm := fun x y => Subtype.ext (hE_comm x.1 x.2 y.1 y.2) }
  have hE_nt : Nontrivial E := by
    rw [nontrivial_iff]
    refine ⟨1, 0, fun h10 => ?_⟩
    have h10' : (1 : Module.End (ZMod p) U₀) = 0 := congrArg Subtype.val h10
    obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU₀ne
    exact hw0 (congrArg Subtype.val (congrArg (fun f : Module.End (ZMod p) U₀ => f ⟨w, hwW⟩) h10'))
  have hE_nzd : NoZeroDivisors E :=
    { eq_zero_or_eq_zero_of_mul_eq_zero := fun {x y} hxy => by
        by_cases hx : x = 0
        · exact Or.inl hx
        · right
          have hx0 : (x : Module.End (ZMod p) U₀) ≠ 0 := fun h => hx (Subtype.ext h)
          have hinj := hE_inj x.1 x.2 hx0
          refine Subtype.ext (LinearMap.ext fun w => hinj ?_)
          have h1 : x.1 (y.1 w) = 0 := by
            have hmul : x.1 * y.1 = ((x * y : E) : Module.End (ZMod p) U₀) := rfl
            change (x.1 * y.1) w = 0
            rw [hmul, hxy]; rfl
          simpa using h1 }
  have hE_domain : IsDomain E := NoZeroDivisors.to_isDomain E
  have hE_fin : Finite E :=
    @Subtype.finite (Module.End (ZMod p) U₀)
      (Finite.of_injective DFunLike.coe DFunLike.coe_injective) (· ∈ E)
  let hE_fintype : Fintype E := @Fintype.ofFinite E hE_fin
  -- Step 3: Every u ∈ (ZMod n)ˣ is a power of (p : ZMod n) via Frobenius roots of minpoly!
  let α₀ : E := ⟨ψa, Algebra.subset_adjoin rfl⟩
  let f : Polynomial (ZMod p) := minpoly (ZMod p) α₀
  have hf_U₀ : ∀ v ∈ U₀, Polynomial.aeval (ρ a).toLinearMap f v = 0 := by
    have hα_root : Polynomial.aeval α₀ f = 0 := minpoly.aeval (ZMod p) α₀
    have hval : Polynomial.aeval ψa f = 0 := by
      have h := congrArg Subtype.val hα_root
      simpa [α₀, ← Polynomial.aeval_algHom_apply E.val α₀ f] using h
    have hrestrict : ∀ (g : Polynomial (ZMod p)) (w : U₀),
        Polynomial.aeval (ρ a).toLinearMap g w.1 = (Polynomial.aeval ψa g w : Fin d → ZMod p) := by
      intro g
      induction g using Polynomial.induction_on' with
      | add g₁ g₂ ih₁ ih₂ =>
        intro w; simp only [map_add, LinearMap.add_apply, Submodule.coe_add, ih₁ w, ih₂ w]
      | monomial k c =>
        intro w
        have hpow : ∀ m : ℕ, ((ρ a).toLinearMap ^ m) w.1 = ((ψa ^ m) w : Fin d → ZMod p) := by
          intro m
          induction m with
          | zero => rfl
          | succ m ihm =>
            rw [pow_succ', pow_succ']
            change ρ a (((ρ a).toLinearMap ^ m) w.1) = ρ a ((ψa ^ m) w).1
            rw [ihm]
        simp only [Polynomial.aeval_monomial]
        change c • ((ρ a).toLinearMap ^ k) w.1 = c • ((ψa ^ k) w : Fin d → ZMod p)
        rw [hpow k]
    intro v hv
    rw [hrestrict f ⟨v, hv⟩, hval]; rfl
  have hf_V : Polynomial.aeval (ρ a).toLinearMap f = 0 := hpoly_U₀ ⟨a, haA⟩ f hf_U₀
  have hu_pow_p : ∀ u : (ZMod n)ˣ, ∃ j : ℕ, (u : ZMod n) = (p : ZMod n) ^ j := by
    intro u
    have hcop : (orderOf a).Coprime (u : ZMod n).val := by
      rw [ha_ord]; exact (ZMod.val_coe_unit_coprime u).symm
    obtain ⟨h, hh⟩ := isConj_iff.mp (isConj_pow_of_coprime_orderOf hHrat a hcop)
    -- Conjugate aeval (ρ a) f = 0 by ρ h to get aeval (ρ (a ^ u.val)) f = 0
    have hf_powV : Polynomial.aeval (ρ (a ^ (u : ZMod n).val)).toLinearMap f = 0 := by
      have hconj_poly : ∀ g : Polynomial (ZMod p),
          Polynomial.aeval (ρ (a ^ (u : ZMod n).val)).toLinearMap g =
          (ρ h).toLinearMap.comp ((Polynomial.aeval (ρ a).toLinearMap g).comp (ρ h⁻¹).toLinearMap) := by
        intro g
        induction g using Polynomial.induction_on' with
        | add g₁ g₂ ih₁ ih₂ =>
          rw [map_add, map_add, ih₁, ih₂]
          refine LinearMap.ext fun v => ?_; simp
        | monomial k c =>
          have hpow : ∀ m : ℕ, (ρ (a ^ (u : ZMod n).val)).toLinearMap ^ m =
              (ρ h).toLinearMap.comp (((ρ a).toLinearMap ^ m).comp (ρ h⁻¹).toLinearMap) := by
            intro m
            induction m with
            | zero =>
              refine LinearMap.ext fun v => ?_
              change v = ρ h (ρ h⁻¹ v)
              have hm : ρ h (ρ h⁻¹ v) = ρ (h * h⁻¹) v := by rw [map_mul]; rfl
              rw [hm, mul_inv_cancel, map_one]; rfl
            | succ m ihm =>
              rw [pow_succ', pow_succ', ihm]
              refine LinearMap.ext fun v => ?_
              change ρ (a ^ (u : ZMod n).val) (ρ h (((ρ a).toLinearMap ^ m) (ρ h⁻¹ v))) =
                ρ h (ρ a (((ρ a).toLinearMap ^ m) (ρ h⁻¹ v)))
              rw [← hh]
              have hm : h * a * h⁻¹ * h = h * a := by group
              calc ρ (h * a * h⁻¹) (ρ h (((ρ a).toLinearMap ^ m) (ρ h⁻¹ v)))
                  = (ρ (h * a * h⁻¹) * ρ h) (((ρ a).toLinearMap ^ m) (ρ h⁻¹ v)) := rfl
                _ = ρ (h * a * h⁻¹ * h) (((ρ a).toLinearMap ^ m) (ρ h⁻¹ v)) := by rw [← map_mul]
                _ = ρ (h * a) (((ρ a).toLinearMap ^ m) (ρ h⁻¹ v)) := by rw [hm]
                _ = (ρ h * ρ a) (((ρ a).toLinearMap ^ m) (ρ h⁻¹ v)) := by rw [map_mul]
                _ = ρ h (ρ a (((ρ a).toLinearMap ^ m) (ρ h⁻¹ v))) := rfl
          refine LinearMap.ext fun v => ?_
          simp only [Polynomial.aeval_monomial, LinearMap.comp_apply, LinearEquiv.coe_coe]
          change c • ((ρ (a ^ (u : ZMod n).val)).toLinearMap ^ k) v =
            ρ h (c • ((ρ a).toLinearMap ^ k) (ρ h⁻¹ v))
          rw [hpow k, map_smul]; rfl
      rw [hconj_poly f, hf_V]; simp
    -- Restrict back to E to get aeval (α₀ ^ u.val) f = 0
    have hf_αu : Polynomial.aeval (α₀ ^ (u : ZMod n).val) f = 0 := by
      apply Subtype.ext
      change E.val (Polynomial.aeval (α₀ ^ (u : ZMod n).val) f) = 0
      rw [← Polynomial.aeval_algHom_apply]
      refine LinearMap.ext fun w => Subtype.ext ?_
      have hval_pow : E.val (α₀ ^ (u : ZMod n).val) = ψa ^ (u : ZMod n).val :=
        map_pow E.val α₀ _
      rw [hval_pow]
      have hrestrict : ∀ (g : Polynomial (ZMod p)),
          ((Polynomial.aeval (ψa ^ (u : ZMod n).val) g) w : Fin d → ZMod p) =
          Polynomial.aeval (ρ (a ^ (u : ZMod n).val)).toLinearMap g w.1 := by
        intro g
        induction g using Polynomial.induction_on' with
        | add g₁ g₂ ih₁ ih₂ =>
          simp only [map_add, LinearMap.add_apply, Submodule.coe_add, ih₁, ih₂]
        | monomial k c =>
          have hpow : ∀ m : ℕ, (((ψa ^ (u : ZMod n).val) ^ m) w : Fin d → ZMod p) =
              ((ρ (a ^ (u : ZMod n).val)).toLinearMap ^ m) w.1 := by
            intro m
            have hψpow : ∀ r : ℕ, ((ψa ^ r) w : Fin d → ZMod p) = ρ (a ^ r) w.1 := by
              intro r
              induction r with
              | zero => simp [pow_zero]
              | succ r ihr =>
                rw [pow_succ', pow_succ']
                change ρ a ((ψa ^ r) w).1 = ρ (a * a ^ r) w.1
                rw [ihr, map_mul]; rfl
            have hρpow : ∀ r : ℕ, ((ρ (a ^ (u : ZMod n).val)).toLinearMap ^ r) w.1 =
                ρ ((a ^ (u : ZMod n).val) ^ r) w.1 := by
              intro r
              induction r with
              | zero => simp [pow_zero]
              | succ r ihr =>
                rw [pow_succ', pow_succ']
                change ρ (a ^ (u : ZMod n).val) (((ρ (a ^ (u : ZMod n).val)).toLinearMap ^ r) w.1) =
                  ρ (a ^ (u : ZMod n).val * (a ^ (u : ZMod n).val) ^ r) w.1
                rw [ihr, map_mul]; rfl
            rw [← pow_mul, hψpow, hρpow, ← pow_mul]
          simp only [Polynomial.aeval_monomial]
          change c • (((ψa ^ (u : ZMod n).val) ^ k) w : Fin d → ZMod p) =
            c • ((ρ (a ^ (u : ZMod n).val)).toLinearMap ^ k) w.1
          rw [hpow k]
      rw [hrestrict f, hf_powV]; rfl
    obtain ⟨j, hj⟩ :=
      @frobenius_roots_of_minpoly p _ E hE_commRing hE_domain hE_fintype E.algebra
        α₀ (α₀ ^ (u : ZMod n).val) hf_αu
    refine ⟨j, ?_⟩
    have hψ_eq : ψa ^ (u : ZMod n).val = ψa ^ (p ^ j) := by
      have h := congrArg Subtype.val hj
      simpa [α₀] using h
    have hpow_a : a ^ (u : ZMod n).val = a ^ (p ^ j) := by
      have hdiff : (⟨a ^ (u : ZMod n).val, A.pow_mem haA _⟩ : A) *
          (⟨a ^ (p ^ j), A.pow_mem haA _⟩ : A)⁻¹ = 1 := by
        apply hfaith_U₀
        intro v hv
        have hψpow : ∀ r : ℕ, ∀ w : U₀, ((ψa ^ r) w : Fin d → ZMod p) = ρ (a ^ r) w.1 := by
          intro r
          induction r with
          | zero => intro w; simp [pow_zero]
          | succ r ihr =>
            intro w
            rw [pow_succ', pow_succ']
            change ρ a ((ψa ^ r) w).1 = ρ (a * a ^ r) w.1
            rw [ihr w, map_mul]; rfl
        have h1 : ρ (a ^ (u : ZMod n).val) v = ρ (a ^ (p ^ j)) v := by
          have h := congrArg (fun g : Module.End (ZMod p) U₀ => (g ⟨v, hv⟩ : Fin d → ZMod p)) hψ_eq
          rwa [hψpow, hψpow] at h
        change ρ (a ^ (u : ZMod n).val * (a ^ (p ^ j))⁻¹) v = v
        rw [map_mul]
        change ρ (a ^ (u : ZMod n).val) (ρ (a ^ (p ^ j))⁻¹ v) = v
        apply (ρ (a ^ (p ^ j))).injective
        have hcomm : a ^ (p ^ j) * (a ^ (u : ZMod n).val * (a ^ (p ^ j))⁻¹) = a ^ (u : ZMod n).val := by
          have hc := hAcomm (a ^ (p ^ j)) (A.pow_mem haA _) (a ^ (u : ZMod n).val) (A.pow_mem haA _)
          calc a ^ (p ^ j) * (a ^ (u : ZMod n).val * (a ^ (p ^ j))⁻¹)
              = (a ^ (u : ZMod n).val * a ^ (p ^ j)) * (a ^ (p ^ j))⁻¹ := by rw [← mul_assoc, hc]
            _ = a ^ (u : ZMod n).val := by group
        calc ρ (a ^ (p ^ j)) (ρ (a ^ (u : ZMod n).val) (ρ (a ^ (p ^ j))⁻¹ v))
            = ρ (a ^ (p ^ j) * (a ^ (u : ZMod n).val * (a ^ (p ^ j))⁻¹)) v := by
                simp [map_mul]
          _ = ρ (a ^ (u : ZMod n).val) v := by rw [hcomm]
          _ = ρ (a ^ (p ^ j)) v := h1
      exact mul_inv_eq_one.mp (congrArg Subtype.val hdiff)
    have hmod : (u : ZMod n).val ≡ p ^ j [MOD n] := by
      have h1 := pow_eq_pow_iff_modEq.mp hpow_a
      rwa [ha_ord] at h1
    have hcast : ((u : ZMod n).val : ZMod n) = ((p ^ j : ℕ) : ZMod n) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
    simpa using hcast
  -- Step 4: Since (p : ZMod n) ∈ (ZMod n)ˣ has square 1, |(ZMod n)ˣ| ≤ 2, so φ(n) ≤ 2!
  have hp_cop_n : p.Coprime n := by
    rw [Nat.Prime.coprime_iff_not_dvd Fact.out]
    intro hdvd
    exact hpH (dvd_trans hdvd (Subgroup.card_subgroup_dvd_card A))
  let p_unit : (ZMod n)ˣ := ZMod.unitOfCoprime p hp_cop_n
  have hp_sq : (p : ZMod n) ^ 2 = 1 := by
    have h1 := hu_sq p_unit
    rwa [ZMod.coe_unitOfCoprime] at h1
  have hu_two : ∀ u : (ZMod n)ˣ, (u : ZMod n) = 1 ∨ (u : ZMod n) = (p : ZMod n) := by
    intro u
    obtain ⟨j, hj⟩ := hu_pow_p u
    have hpow : (p : ZMod n) ^ j = (p : ZMod n) ^ (j % 2) := by
      conv_lhs => rw [← Nat.div_add_mod j 2, pow_add, pow_mul, hp_sq, one_pow, one_mul]
    rw [hpow] at hj
    have h01 : j % 2 = 0 ∨ j % 2 = 1 := by omega
    rcases h01 with h0 | h1
    · left; rw [hj, h0, pow_zero]
    · right; rw [hj, h1, pow_one]
  have hφ_le2 : Nat.totient n ≤ 2 := by
    rw [← ZMod.card_units_eq_totient n]
    have hsub : (Finset.univ : Finset (ZMod n)ˣ) ⊆ {1, p_unit} := by
      intro u _
      rw [Finset.mem_insert, Finset.mem_singleton]
      rcases hu_two u with h1 | hp'
      · left; exact Units.ext h1
      · right; exact Units.ext (by rwa [ZMod.coe_unitOfCoprime])
    calc Fintype.card (ZMod n)ˣ = (Finset.univ : Finset (ZMod n)ˣ).card := rfl
      _ ≤ ({1, p_unit} : Finset (ZMod n)ˣ).card := Finset.card_le_card hsub
      _ ≤ 2 := Finset.card_le_two
  refine ⟨totient_le_two_cases hn_pos hφ_le2, ?_, ?_⟩
  · -- If 3 ∣ n, then (-1 : ZMod n) ≠ 1 forces (p : ZMod n) = -1, hence p % 3 = 2
    intro h3
    have hneg_ne1 : (-1 : ZMod n) ≠ 1 := by
      intro h1
      have h2 : (2 : ZMod n) = 0 := by
        have : (1 : ZMod n) - (-1) = 0 := sub_eq_zero.mpr h1.symm
        simpa [sub_neg_eq_add, one_add_one_eq_two] using this
      have hn_dvd2 : n ∣ 2 := (ZMod.natCast_eq_zero_iff 2 n).mp (by simpa using h2)
      have h3_dvd2 : 3 ∣ 2 := dvd_trans h3 hn_dvd2
      omega
    have hneg_eq_p : (-1 : ZMod n) = (p : ZMod n) := by
      rcases hu_two (-1 : (ZMod n)ˣ) with h1 | hp'
      · exact absurd h1 hneg_ne1
      · exact hp'
    have h1 : ((p + 1 : ℕ) : ZMod n) = 0 := by
      push_cast; rw [← hneg_eq_p, neg_add_cancel]
    have h3_dvd : 3 ∣ p + 1 := dvd_trans h3 ((ZMod.natCast_eq_zero_iff (p + 1) n).mp h1)
    omega
  · -- If 4 ∣ n, then (-1 : ZMod n) ≠ 1 forces (p : ZMod n) = -1, hence p % 4 = 3
    intro h4
    have hneg_ne1 : (-1 : ZMod n) ≠ 1 := by
      intro h1
      have h2 : (2 : ZMod n) = 0 := by
        have : (1 : ZMod n) - (-1) = 0 := sub_eq_zero.mpr h1.symm
        simpa [sub_neg_eq_add, one_add_one_eq_two] using this
      have hn_dvd2 : n ∣ 2 := (ZMod.natCast_eq_zero_iff 2 n).mp (by simpa using h2)
      have h4_dvd2 : 4 ∣ 2 := dvd_trans h4 hn_dvd2
      omega
    have hneg_eq_p : (-1 : ZMod n) = (p : ZMod n) := by
      rcases hu_two (-1 : (ZMod n)ˣ) with h1 | hp'
      · exact absurd h1 hneg_ne1
      · exact hp'
    have h1 : ((p + 1 : ℕ) : ZMod n) = 0 := by
      push_cast; rw [← hneg_eq_p, neg_add_cancel]
    have h4_dvd : 4 ∣ p + 1 := dvd_trans h4 ((ZMod.natCast_eq_zero_iff (p + 1) n).mp h1)
    omega

theorem main : H1 → H2 → H3 →
    OMA.R_ConjugacyClassSizes_conjClassSizes_iff_sym_three_solvable_R1.H1 := by
  intro h1 h2 h3
  by_contra hcontra
  obtain ⟨p, hp_fact, hp7, d, hd, H, hGrp, hFin, hSolv, hH235, hHrat, ρ, hfaith, hirred, hjoint⟩ :=
    exists_minimal_counterexample hcontra
  have hp_prime : p.Prime := hp_fact.out
  have hpH : ¬ (p ∣ Nat.card H) := by
    intro hdvd
    rcases hH235 p hp_prime hdvd with rfl | rfl | rfl <;> omega
  have heig : ∀ (v : Fin d → ZMod p), v ≠ 0 → ∀ (c : (ZMod p)ˣ),
      ∃ h : H, ρ h v = (c : ZMod p) • v := fun v hv c => by
    obtain ⟨h, hh, _⟩ := hjoint v hv 1 (by simp) c 1 (Nat.coprime_one_right _)
    exact ⟨h, hh⟩
  have hcent : ∀ (v : Fin d → ZMod p), v ≠ 0 → ∀ (y : H), ρ y v = v →
      ∀ (n : ℕ), (Nat.card {h : H // ρ h v = v}).Coprime n →
        ∃ h : H, ρ h v = v ∧ h * y * h⁻¹ = y ^ n := fun v hv y hy n hn => by
    obtain ⟨h, hh, hconj⟩ := hjoint v hv y hy 1 n hn
    exact ⟨h, by simpa using hh, hconj⟩
  have hO5 : ∀ Q : Subgroup H, Q.Normal → IsPGroup 5 Q → Q = ⊥ :=
    fun Q hQn hQp => no_normal_pGroup_ge_five hHrat hpH ρ hfaith hcent 5 (by decide) le_rfl Q hQn hQp
  have heig_bd : ∀ (g : H) (c : (ZMod p)ˣ),
      Module.finrank (ZMod p) (LinearMap.ker ((ρ g).toLinearMap - (c : ZMod p) • LinearMap.id)) *
        Nat.totient (orderOf c) ≤ d :=
    fun g c => eigenspace_dim_bound hHrat ρ g c
  have htot_le : Nat.totient (p - 1) ≤ d := totient_le_dim hd hHrat ρ heig
  have hnot2 : ¬ IsPGroup 2 H := not_isPGroup_two hp7 hd hpH hHrat ρ hirred heig
  obtain ⟨m, W, hm1, hWind, hWsup, hWne, hWperm, htrans, hmax⟩ :=
    exists_maximal_imprimitivity hd ρ hirred
  by_cases hm2 : 2 ≤ m
  · -- Imprimitive non-monomial case -> H3
    have hnonab := universal_monomial_killer hp7 hHrat ρ heig m hm1 W hWind hWne hWperm htrans
    exact h3 p hp7 d htot_le H hH235 hHrat hO5 hnot2 ρ hfaith hirred
      ⟨m, W, hm2, hWind, hWsup, hWne, hWperm, htrans, hnonab, hmax⟩ heig_bd hjoint
  · -- Primitive case (m = 1)
    have hm_eq1 : m = 1 := by omega
    have hprim : ∀ (m' : ℕ) (W' : Fin m' → Submodule (ZMod p) (Fin d → ZMod p)),
        2 ≤ m' → iSupIndep W' → iSup W' = ⊤ → (∀ i, W' i ≠ ⊥) →
        ¬ ∀ h : H, ∃ σ : Equiv.Perm (Fin m'),
          ∀ i, Submodule.map (ρ h).toLinearMap (W' i) = W' (σ i) := by
      intro m' W' hm'2 h1 h2 h3 h4
      have hle := hmax m' W' h1 h2 h3 h4
      omega
    have hab_ord := abelian_normal_order_of_primitive hp7 hd hpH hHrat ρ hfaith hprim
    by_cases hO3 : ∀ Q : Subgroup H, Q.Normal → IsPGroup 3 Q → Q = ⊥
    · -- O_3(H) = 1 and O_5(H) = 1 -> H1
      have hA124 : ∀ A : Subgroup H, A.Normal → (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) →
          Nat.card A = 1 ∨ Nat.card A = 2 ∨ (Nat.card A = 4 ∧ p % 4 = 3) := by
        intro A hAnorm hAcomm
        have hinfo := hab_ord A hAnorm hAcomm
        have hno3 : ¬ (3 ∣ Nat.card A) := by
          intro h3dvd
          have : Fact (Nat.Prime 3) := ⟨by decide⟩
          let A3 : Subgroup H :=
            { carrier := {x ∈ A | x ^ 3 = 1}
              mul_mem' := fun {a b} ⟨haA, ha3⟩ ⟨hbA, hb3⟩ =>
                ⟨A.mul_mem haA hbA, by rw [(show Commute a b from hAcomm a haA b hbA).mul_pow, ha3, hb3, one_mul]⟩
              one_mem' := ⟨A.one_mem, one_pow 3⟩
              inv_mem' := fun {a} ⟨haA, ha3⟩ => ⟨A.inv_mem haA, by rw [inv_pow, ha3, inv_one]⟩ }
          have hA3_norm : A3.Normal := ⟨fun x ⟨hxA, hx3⟩ g =>
            ⟨hAnorm.conj_mem x hxA g, by rw [conj_pow, hx3, mul_one, mul_inv_cancel]⟩⟩
          have hA3_p : IsPGroup 3 A3 := fun ⟨x, _, hx3⟩ => ⟨1, Subtype.ext (by simpa using hx3)⟩
          have hA3_bot : A3 = ⊥ := hO3 A3 hA3_norm hA3_p
          obtain ⟨⟨x, hxA⟩, hxord⟩ := exists_prime_orderOf_dvd_card' (G := A) 3 h3dvd
          have hx3 : x ^ 3 = 1 := by
            have h : (⟨x, hxA⟩ : A) ^ 3 = 1 := by rw [← hxord, pow_orderOf_eq_one]
            exact congrArg Subtype.val h
          have hxA3 : x ∈ A3 := ⟨hxA, hx3⟩
          rw [hA3_bot, Subgroup.mem_bot] at hxA3
          have hx1 : (⟨x, hxA⟩ : A) = 1 := Subtype.ext hxA3
          rw [hx1, orderOf_one] at hxord; omega
        rcases hinfo.1 with h1 | h2 | h3 | h4 | h6
        · exact Or.inl h1
        · exact Or.inr (Or.inl h2)
        · exact absurd (h3 ▸ dvd_rfl) hno3
        · exact Or.inr (Or.inr ⟨h4, hinfo.2.2 (h4 ▸ dvd_rfl)⟩)
        · exact absurd (h6 ▸ (by decide : 3 ∣ 6)) hno3
      exact h1 p hp7 d htot_le H hH235 hHrat hO3 hO5 hnot2 hA124 ρ hfaith hirred hprim heig_bd hjoint
    · -- O_3(H) ≠ 1 -> H2 (forces |Z(Q)| = 3 and p % 3 = 2)
      push Not at hO3
      obtain ⟨Q, hQnorm, hQ3, hQne⟩ := hO3
      have : Fact (Nat.Prime 3) := ⟨by decide⟩
      have : Nontrivial Q := by
        rw [nontrivial_iff]
        obtain ⟨x, hxQ, hx1⟩ : ∃ x ∈ Q, x ≠ 1 := by
          by_contra hall; push Not at hall
          exact hQne ((Subgroup.eq_bot_iff_forall Q).mpr hall)
        exact ⟨⟨x, hxQ⟩, 1, fun h => hx1 (congrArg Subtype.val h)⟩
      let ZQ_H : Subgroup H := (Subgroup.center Q).map Q.subtype
      have hZQ_norm : ZQ_H.Normal := ⟨fun x hx g => by
        obtain ⟨⟨y, hyQ⟩, hyZ, rfl⟩ := Subgroup.mem_map.mp hx
        refine Subgroup.mem_map.mpr ⟨⟨g * y * g⁻¹, hQnorm.conj_mem y hyQ g⟩, ?_, rfl⟩
        rw [Subgroup.mem_center_iff]
        intro ⟨z, hzQ⟩
        apply Subtype.ext
        have hz' : g⁻¹ * z * g ∈ Q := by simpa [inv_inv] using hQnorm.conj_mem z hzQ g⁻¹
        have hcomm : (g⁻¹ * z * g) * y = y * (g⁻¹ * z * g) :=
          congrArg Subtype.val (Subgroup.mem_center_iff.mp hyZ ⟨g⁻¹ * z * g, hz'⟩)
        change z * (g * y * g⁻¹) = (g * y * g⁻¹) * z
        calc z * (g * y * g⁻¹) = g * ((g⁻¹ * z * g) * y) * g⁻¹ := by group
          _ = g * (y * (g⁻¹ * z * g)) * g⁻¹ := by rw [hcomm]
          _ = (g * y * g⁻¹) * z := by group⟩
      have hZQ_comm : ∀ x ∈ ZQ_H, ∀ y ∈ ZQ_H, x * y = y * x := by
        rintro _ ⟨⟨x, hxQ⟩, hxZ, rfl⟩ _ ⟨⟨y, hyQ⟩, _, rfl⟩
        exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hxZ ⟨y, hyQ⟩)).symm
      have hZQ_card_eq : Nat.card ZQ_H = Nat.card (Subgroup.center Q) := by
        let f : Subgroup.center Q → ZQ_H := fun y => ⟨(y.1 : H), Subgroup.mem_map.mpr ⟨y.1, y.2, rfl⟩⟩
        have hf_bij : Function.Bijective f :=
          ⟨fun a b h => Subtype.ext (Subtype.ext (congrArg (Subtype.val : ZQ_H → H) h)),
           fun ⟨x, hx⟩ => by obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx; exact ⟨⟨y, hy⟩, rfl⟩⟩
        exact (Nat.card_congr (Equiv.ofBijective f hf_bij)).symm
      have hZQ_nt : Nontrivial (Subgroup.center Q) := hQ3.center_nontrivial
      have hZQ_3 : IsPGroup 3 (Subgroup.center Q) := hQ3.to_subgroup (Subgroup.center Q)
      obtain ⟨kZ, hkZ_pos, hkZ_card⟩ := hZQ_3.nontrivial_iff_card.mp hZQ_nt
      have h3_dvd_ZQ : 3 ∣ Nat.card ZQ_H := by
        rw [hZQ_card_eq, hkZ_card]; exact dvd_pow_self 3 hkZ_pos.ne'
      have hZQ_info := hab_ord ZQ_H hZQ_norm hZQ_comm
      have hp_mod3 : p % 3 = 2 := hZQ_info.2.1 h3_dvd_ZQ
      have hZQ_card3 : Nat.card (Subgroup.center Q) = 3 := by
        rw [← hZQ_card_eq]
        have hpow3 : Nat.card ZQ_H = 3 ^ kZ := hZQ_card_eq.trans hkZ_card
        rcases hZQ_info.1 with h1 | h2 | h3 | h4 | h6
        · rw [h1] at h3_dvd_ZQ; omega
        · rw [h2] at h3_dvd_ZQ; omega
        · exact h3
        · rw [h4] at h3_dvd_ZQ; omega
        · rw [h6] at hpow3
          have h2dvd : 2 ∣ 3 ^ kZ := hpow3 ▸ (by decide : 2 ∣ 6)
          have h23 : 2 = 3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two Nat.prime_three).mp
            (Nat.prime_two.dvd_of_dvd_pow h2dvd)
          omega
      have hA_info : ∀ A : Subgroup H, A.Normal → (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) →
          Nat.card A = 1 ∨ Nat.card A = 2 ∨ Nat.card A = 3 ∨
          (Nat.card A = 4 ∧ p % 4 = 3) ∨ Nat.card A = 6 := by
        intro A hAnorm hAcomm
        have hinfo := hab_ord A hAnorm hAcomm
        rcases hinfo.1 with h1 | h2 | h3 | h4 | h6
        · exact Or.inl h1
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr (Or.inl h3))
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h4, hinfo.2.2 (h4 ▸ dvd_rfl)⟩)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr h6)))
      exact h2 p hp7 hp_mod3 d htot_le H hH235 hHrat hO5
        ⟨Q, hQnorm, hQ3, hQne, hZQ_card3⟩ hA_info ρ hfaith hirred hprim heig_bd hjoint

end OMA.R_ConjugacyClassSizes_conjClassSizes_iff_sym_three_solvable_R1_H1_R1
