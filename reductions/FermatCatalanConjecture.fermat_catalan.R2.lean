import FormalConjectures.Wikipedia.FermatCatalanConjecture

/-! Fourth-power extraction reduces the problem to finitely many fixed diagonal quartic equations. -/

namespace OMA.R_FermatCatalanConjecture_fermat_catalan_R2

def H1 : Prop :=
  ∀ D E F : ℕ, 0 < D → 0 < E → 0 < F →
    {t : ℕ × ℕ × ℕ | 0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2 ∧ t.1.Coprime t.2.1 ∧
      D * t.1 ^ 4 + E * t.2.1 ^ 4 = F * t.2.2 ^ 4}.Finite

def H2 : Prop :=
  ∃ S : Finset ℕ, ∀ f ∈ FermatCatalanConjecture.FermatCatalanSet', ∀ p ∉ S,
    4 ∣ (f 0 ^ f 3).factorization p ∧ 4 ∣ (f 1 ^ f 4).factorization p ∧
    4 ∣ (f 2 ^ f 5).factorization p

lemma support_of_finite (finite : FermatCatalanConjecture.FermatCatalanSet.Finite) : H2 := by
  classical
  let factors (t : ℕ × ℕ × ℕ) := (t.1.primeFactors ∪ t.2.1.primeFactors) ∪ t.2.2.primeFactors
  refine ⟨finite.toFinset.biUnion factors, ?_⟩
  intro f hf p outside
  let t := (f 0 ^ f 3, f 1 ^ f 4, f 2 ^ f 5)
  have mem : t ∈ finite.toFinset := finite.mem_toFinset.mpr ⟨f,hf,rfl⟩
  have absent : p ∉ factors t := fun hp => outside (Finset.mem_biUnion.mpr ⟨t,mem,hp⟩)
  simp only [factors, Finset.mem_union, not_or, t] at absent
  have div {n : ℕ} (hp : p ∉ n.primeFactors) : 4 ∣ n.factorization p := by
    rw [← Nat.support_factorization] at hp
    rw [Finsupp.notMem_support_iff.mp hp]
    exact dvd_zero _
  exact ⟨div absent.1.1, div absent.1.2, div absent.2⟩

lemma extract_fourth (S : Finset ℕ) {n : ℕ} (positive : 0 < n)
    (outside : ∀ p ∉ S, 4 ∣ n.factorization p) :
    ∃ d u : ℕ, 0 < d ∧ d ≤ ∏ p ∈ S, (p + 1) ^ 3 ∧ 0 < u ∧ n = d * u ^ 4 := by
  let primes := n.primeFactors
  let remainder := fun p => p ^ (n.factorization p % 4)
  let quotient := fun p => p ^ (n.factorization p / 4)
  have cut : ∏ p ∈ primes ∩ S, remainder p = ∏ p ∈ primes, remainder p := by
    apply Finset.prod_subset Finset.inter_subset_left
    intro p hp missing
    have away : p ∉ S := fun h => missing (Finset.mem_inter.mpr ⟨hp,h⟩)
    simp [remainder, Nat.mod_eq_zero_of_dvd (outside p away)]
  have bound : ∏ p ∈ primes ∩ S, remainder p ≤ ∏ p ∈ S, (p + 1) ^ 3 := by
    calc
      _ ≤ ∏ p ∈ primes ∩ S, (p + 1) ^ 3 := by
        apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
        intro p _
        have rem_lt := Nat.mod_lt (n.factorization p) (by decide : 0 < 4)
        exact (Nat.pow_le_pow_left (Nat.le_succ p) _).trans
          (Nat.pow_le_pow_right (Nat.succ_pos p) (by omega : n.factorization p % 4 ≤ 3))
      _ ≤ _ := Finset.prod_le_prod_of_subset_of_one_le' Finset.inter_subset_right
        (fun p _ _ => Nat.succ_le_of_lt (pow_pos (Nat.succ_pos p) 3))
  have primes_pos (p) (hp : p ∈ primes) : 0 < p := (Nat.prime_of_mem_primeFactors hp).pos
  refine ⟨∏ p ∈ primes, remainder p, ∏ p ∈ primes, quotient p,
    Finset.prod_pos (fun p hp => pow_pos (primes_pos p hp) _), cut ▸ bound,
    Finset.prod_pos (fun p hp => pow_pos (primes_pos p hp) _), ?_⟩
  calc
    n = ∏ p ∈ primes, p ^ n.factorization p := Nat.prod_primeFactors_pow_factorization positive.ne'
    _ = ∏ p ∈ primes, remainder p * quotient p ^ 4 := by
      apply Finset.prod_congr rfl
      intro p _
      dsimp [remainder, quotient]
      rw [← pow_mul, ← pow_add, Nat.mul_comm (n.factorization p / 4) 4, Nat.mod_add_div]
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_pow]

theorem main : H1 → H2 → type_of% @FermatCatalanConjecture.fermat_catalan := by
  rintro quartics ⟨S,supported⟩
  let bound := ∏ p ∈ S, (p + 1) ^ 3
  let interval : Set ℕ := Set.Ioc 0 bound
  let box := interval ×ˢ (interval ×ˢ interval)
  let roots (g : ℕ × ℕ × ℕ) := {t : ℕ × ℕ × ℕ |
    0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2 ∧ t.1.Coprime t.2.1 ∧
      g.1 * t.1 ^ 4 + g.2.1 * t.2.1 ^ 4 = g.2.2 * t.2.2 ^ 4}
  let values (g t : ℕ × ℕ × ℕ) := (g.1 * t.1 ^ 4, g.2.1 * t.2.1 ^ 4, g.2.2 * t.2.2 ^ 4)
  have finiteInterval : interval.Finite := Set.finite_Ioc _ _
  have finiteBox : box.Finite := finiteInterval.prod (finiteInterval.prod finiteInterval)
  have finite : (⋃ g ∈ box, values g '' roots g).Finite := by
    apply finiteBox.biUnion
    intro g hg
    exact (quartics _ _ _ hg.1.1 hg.2.1.1 hg.2.2.1).image _
  apply finite.subset
  rintro _ ⟨f,hf,rfl⟩
  obtain ⟨D,x,hD,bD,hx,eqx⟩ :=
    extract_fourth S (pow_pos (hf.1 0) (f 3)) (fun p hp => (supported f hf p hp).1)
  obtain ⟨E,y,hE,bE,hy,eqy⟩ :=
    extract_fourth S (pow_pos (hf.1 1) (f 4)) (fun p hp => (supported f hf p hp).2.1)
  obtain ⟨F,z,hF,bF,hz,eqz⟩ :=
    extract_fourth S (pow_pos (hf.1 2) (f 5)) (fun p hp => (supported f hf p hp).2.2)
  have divisor {a d v : ℕ} (h : v = d * a ^ 4) : a ∣ v :=
    h ▸ (dvd_pow_self a (by decide : 4 ≠ 0)).trans (dvd_mul_left _ _)
  have cop : (f 0).Coprime (f 1) := hf.2.1 (by simp) (by simp) (by decide)
  have xy : x.Coprime y := (cop.pow (f 3) (f 4)).of_dvd (divisor eqx) (divisor eqy)
  have eqn := hf.2.2.1
  rw [eqx, eqy, eqz] at eqn
  exact Set.mem_iUnion₂.mpr ⟨(D,E,F), ⟨⟨hD,bD⟩,⟨hE,bE⟩,⟨hF,bF⟩⟩,
    (x,y,z), ⟨hx,hy,hz,xy,eqn⟩, by simp only [values, eqx, eqy, eqz]⟩

end OMA.R_FermatCatalanConjecture_fermat_catalan_R2
