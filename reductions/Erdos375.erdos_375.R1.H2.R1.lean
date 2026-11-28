import OMAReductions.R_Erdos375_erdos_375_R1

/-! Minimum Hall obstructions in Grimm's medium-block regime. Distinct indices
force every supporting prime below the local diameter. A valuation argument
produces an entry dividing the product of the maximal local primary powers
for exactly these primes. The square lower bound eliminates supports of size
zero, one and two. -/

namespace OMA.R_Erdos375_erdos_375_R1_H2_R1
open Finset

/-- A common divisor of two distinct entries is at most their enclosing interval's diameter. -/
private theorem shared_le {d n u v a D : ℕ} (hne : u≠v) (hu : a ≤ u) (hu' : u ≤ a+D)
    (hv : a ≤ v) (hv' : v ≤ a+D) (h1 : d ∣ n+u+1) (h2 : d ∣ n+v+1) : d ≤ D := by
  rcases lt_or_gt_of_ne hne with h|h
  · have hd : d ∣ v-u := by convert Nat.dvd_sub h2 h1 using 1; omega
    have := Nat.le_of_dvd (by omega : 0<v-u) hd
    omega
  · have hd : d ∣ u-v := by convert Nat.dvd_sub h1 h2 using 1; omega
    have := Nat.le_of_dvd (by omega : 0<u-v) hd
    omega

/-- A minimum-cardinality deficient family has no prime occurring at a single index. -/
private theorem trimmed {k : ℕ} (F : Fin k → Finset ℕ)
    (bad : ∃ J : Finset (Fin k), (J.biUnion F).card < J.card) :
    ∃ J : Finset (Fin k), (J.biUnion F).card < J.card ∧
      ∀ p ∈ J.biUnion F, ∃ i ∈ J, ∃ j ∈ J, i≠j ∧ p ∈ F i ∧ p ∈ F j := by
  classical
  let C := (univ : Finset (Finset (Fin k))).filter fun J => (J.biUnion F).card < J.card
  obtain ⟨J₀,h₀⟩ := bad
  obtain ⟨J,hJ,hmin⟩ := exists_min_image C card ⟨J₀,mem_filter.mpr ⟨mem_univ _,h₀⟩⟩
  have hbad := (mem_filter.mp hJ).2
  refine ⟨J,hbad,?_⟩
  intro p hp
  obtain ⟨i,hi,hp'⟩ := mem_biUnion.mp hp
  by_contra h
  have sub : (J.erase i).biUnion F ⊆ (J.biUnion F).erase p := by
    intro q hq
    obtain ⟨j,hj,hq⟩ := mem_biUnion.mp hq
    obtain ⟨hne,hj⟩ := mem_erase.mp hj
    refine mem_erase.mpr ⟨?_,mem_biUnion.mpr ⟨j,hj,hq⟩⟩
    rintro rfl
    exact h ⟨i,hi,j,hj,hne.symm,hp',hq⟩
  have le := card_le_card sub
  rw [card_erase_of_mem hp] at le
  have hc : J.erase i ∈ C := by
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    rw [card_erase_of_mem hi]
    have hp0 := card_pos.mpr ⟨p,hp⟩
    omega
  have hm := hmin _ hc
  rw [card_erase_of_mem hi] at hm
  have := card_pos.mpr ⟨i,hi⟩
  omega

/-- Assign each prime to an index of maximal valuation, as in the parent reduction.
At an unassigned index every primary factor divides an actual difference. Retain
only the primes of this obstruction, and their local diameter, in the product. -/
private theorem local_divisor {k n a D : ℕ} (J : Finset (Fin k))
    (box : ∀ i ∈ J, a ≤ i.val ∧ i.val ≤ a+D)
    (bad : (J.biUnion (fun i => (n+i.val+1).primeFactors)).card < J.card) :
    ∃ i ∈ J, n+i.val+1 ∣ ∏ p ∈ J.biUnion (fun i => (n+i.val+1).primeFactors), p^(Nat.log p D) := by
  classical
  let P := J.biUnion (fun i => (n+i.val+1).primeFactors)
  have hJ : J.Nonempty := card_pos.mp (by omega)
  have : Nonempty (Fin k) := ⟨hJ.choose⟩
  have peaks (p : ℕ) : ∃ j ∈ J, ∀ i ∈ J, (n+i.val+1).factorization p ≤ (n+j.val+1).factorization p :=
    exists_max_image J _ hJ
  choose g hg hmax using peaks
  have hlt : (P.image g).card < J.card := card_image_le.trans_lt bad
  obtain ⟨i,hi,hfree⟩ := exists_mem_notMem_of_card_lt_card hlt
  refine ⟨i,hi,?_⟩
  let m := n+i.val+1
  have hsub : m.primeFactors ⊆ P := fun p hp => mem_biUnion.mpr ⟨i,hi,hp⟩
  have hpow (p : ℕ) (hp : p ∈ m.primeFactors) : p^m.factorization p ∣ p^(Nat.log p D) := by
    have hne : i ≠ g p := fun h => hfree (mem_image.mpr ⟨p,hsub hp,h.symm⟩)
    have hd := (Nat.pow_dvd_pow p (hmax p i hi)).trans (Nat.ordProj_dvd _ p)
    obtain ⟨hl,hu⟩ := box i hi
    obtain ⟨hl',hu'⟩ := box (g p) (hg p)
    exact Nat.pow_dvd_pow p (Nat.le_log_of_pow_le (Nat.prime_of_mem_primeFactors hp).one_lt
      (shared_le (fun h => hne (Fin.ext h)) hl hu hl' hu' (Nat.ordProj_dvd m p) hd))
  change m ∣ ∏ p ∈ P, p^(Nat.log p D)
  calc
    m = ∏ p ∈ m.primeFactors, p^m.factorization p := Nat.prod_primeFactors_pow_factorization (by dsimp [m]; omega)
    _ ∣ ∏ p ∈ m.primeFactors, p^(Nat.log p D) := prod_dvd_prod_of_dvd _ _ hpow
    _ ∣ _ := prod_dvd_prod_of_subset _ _ _ hsub

/-- Clusters supported on three primes. It suffices to check a subinterval only if it contains
an entry dividing the product of the indicated prime powers. -/
def H1 : Prop := ∀ n ≥ 1, ∀ k, k*k ≤ n → n < (Icc 1 (k-1)).lcm id →
    (∀ i < k, ¬(n+i+1).Prime) → ∀ a D : ℕ, a+D<k → ∀ P : Finset ℕ,
    P.card = 3 → (∀ p ∈ P, p.Prime ∧ p≤D) →
    (∃ j ∈ Icc a (a+D), n+j+1 ∣ ∏ p ∈ P, p^(Nat.log p D)) →
    ((Icc a (a+D)).filter (fun j => (n+j+1).primeFactors ⊆ P)).card ≤ P.card

/-- Clusters supported on four or more primes. It suffices to check a subinterval only if it contains
an entry dividing the product of the indicated prime powers. -/
def H2 : Prop := ∀ n ≥ 1, ∀ k, k*k ≤ n → n < (Icc 1 (k-1)).lcm id →
    (∀ i < k, ¬(n+i+1).Prime) → ∀ a D : ℕ, a+D<k → ∀ P : Finset ℕ,
    3 < P.card → (∀ p ∈ P, p.Prime ∧ p≤D) →
    (∃ j ∈ Icc a (a+D), n+j+1 ∣ ∏ p ∈ P, p^(Nat.log p D)) →
    ((Icc a (a+D)).filter (fun j => (n+j+1).primeFactors ⊆ P)).card ≤ P.card

theorem main : H1 → H2 → OMA.R_Erdos375_erdos_375_R1.H2 := by
  classical
  intro three many n hn k hk hlcm hcomp
  let F (i : Fin k) := (n+i.val+1).primeFactors
  suffices h : ∃ p : Fin k → ℕ, p.Injective ∧ ∀ i, p i ∈ F i by
    obtain ⟨p,hp,hmem⟩ := h
    exact ⟨p,hp,fun i => ⟨Nat.prime_of_mem_primeFactors (hmem i),Nat.dvd_of_mem_primeFactors (hmem i)⟩⟩
  apply (all_card_le_biUnion_card_iff_exists_injective F).mp
  by_contra! bad
  obtain ⟨J,hdef,hrep⟩ := trimmed F bad
  have hJ : J.Nonempty := card_pos.mp (by omega)
  let P := J.biUnion F
  let a := (J.min' hJ).val
  let b := (J.max' hJ).val
  let D := b-a
  have hab : a ≤ b := J.min'_le _ (J.max'_mem hJ)
  have hb : b < k := (J.max' hJ).isLt
  have hD : a+D < k := by dsimp [D]; omega
  have hkpos : 0<k := by omega
  have box (i : Fin k) (hi : i∈J) : a ≤ i.val ∧ i.val ≤ a+D := by
    have h1 : a ≤ i.val := J.min'_le _ hi
    have h2 : i.val ≤ b := J.le_max' _ hi
    dsimp [D]; omega
  have hP (p : ℕ) (hp : p∈P) : p.Prime ∧ p ≤ D := by
    obtain ⟨i,hi,j,hj,hij,hip,hjp⟩ := hrep p hp
    exact ⟨Nat.prime_of_mem_primeFactors hip,
      shared_le (fun h => hij (Fin.ext h)) (box i hi).1 (box i hi).2 (box j hj).1 (box j hj).2
        (Nat.dvd_of_mem_primeFactors hip) (Nat.dvd_of_mem_primeFactors hjp)⟩
  obtain ⟨i,hi,hd⟩ := local_divisor (n := n) J box hdef
  change n+i.val+1 ∣ ∏ p ∈ P, p^(Nat.log p D) at hd
  have hcard : 3 ≤ P.card := by
    by_contra! hsmall
    have hpos : 0 < ∏ p ∈ P, p^(Nat.log p D) :=
      Finset.prod_pos fun p hp => pow_pos (hP p hp).1.pos _
    have hbnd : ∏ p ∈ P, p^(Nat.log p D) ≤ k^P.card := by
      apply prod_le_pow_card
      intro p hp
      by_cases he : D=0
      · simp [he]; omega
      · exact (Nat.pow_log_le_self p he).trans (by omega)
    have hbnd2 := (Nat.le_of_dvd hpos hd).trans (hbnd.trans (Nat.pow_le_pow_right hkpos (show P.card ≤ 2 by omega)))
    rw [pow_two] at hbnd2
    omega
  have anchor : ∃ j ∈ Icc a (a+D), n+j+1 ∣ ∏ p ∈ P, p^(Nat.log p D) :=
    ⟨i.val,mem_Icc.mpr (box i hi),hd⟩
  let T := (Icc a (a+D)).filter (fun j => (n+j+1).primeFactors ⊆ P)
  have cover : J.image Fin.val ⊆ T := by
    intro j hj
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hj
    exact mem_filter.mpr ⟨mem_Icc.mpr (box i hi),fun p hp => mem_biUnion.mpr ⟨i,hi,hp⟩⟩
  have hle := card_le_card cover
  rw [card_image_of_injective _ Fin.val_injective] at hle
  have upper : T.card ≤ P.card := by
    rcases eq_or_lt_of_le hcard with h | h
    · exact three n hn k hk hlcm hcomp a D hD P h.symm hP anchor
    · exact many n hn k hk hlcm hcomp a D hD P h hP anchor
  change P.card < J.card at hdef
  omega

end OMA.R_Erdos375_erdos_375_R1_H2_R1
