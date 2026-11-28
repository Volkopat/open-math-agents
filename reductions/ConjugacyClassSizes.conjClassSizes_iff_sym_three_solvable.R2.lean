import FormalConjectures.Paper.ConjugacyClassSizes

/-!
# Reduction of the `S₃`-conjecture for solvable groups

Target: `ConjugacyClassSizes.conjClassSizes_iff_sym_three_solvable`, i.e. every nontrivial finite
solvable group whose conjugacy classes have pairwise distinct sizes (an *ah-group*) is isomorphic
to `S₃` (Zhang 1994; Knörr–Lempken–Thielcke 1995).

The four hypotheses are

* `H1` : Gow's theorem (1976): the order of a finite solvable rational group is divisible only
  by the primes `2`, `3`, `5`.
* `H2`, `H3`, `H4` : the residual *small centraliser* statements of the Zhang /
  Knörr–Lempken–Thielcke proofs, for a minimal counterexample only: a solvable ah-group of order
  `2ᵃ3ᵇ5ᶜ` divisible by `3600`, all of whose smaller solvable ah-groups are trivial or `S₃`, has
  no element whose centraliser has order `6` or `10` (`H2`), `8` (`H3`), `9` (`H4`).

Everything else is proved here: rationality and local anti-homogeneity of ah-groups, the endgame
for a centraliser of order two, the weights form of the class equation, the cases `|G| = 2ᵃ3ᵇ`
and `|G| ∣ 2ᵃpᵇ`, a nilpotent derived subgroup, centralisers of order `3`, `4`, `5`, the fibre
lemma, and the strong induction which combines them (`main`).
-/

namespace OMA.R_ConjugacyClassSizes_conjClassSizes_iff_sym_three_solvable_R2

open ConjugacyClassSizes

section Basic

variable {G : Type*} [Group G]

/-- Orbit–stabiliser for conjugacy classes: `|g^G| · |C_G(g)| = |G|`. -/
theorem conjClassCard_mk_mul_card_centralizer (g : G) :
    conjClassCard (ConjClasses.mk g) * Nat.card (Subgroup.centralizer ({g} : Set G)) =
      Nat.card G := by
  rw [conjClassCard, Subgroup.nat_card_centralizer_nat_card_stabilizer,
    ← ConjAct.orbit_eq_carrier_conjClasses,
    Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (ConjAct G) g),
    ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
  exact Nat.card_congr ConjAct.toConjAct.symm.toEquiv

/-- In a group with pairwise distinct class sizes, two elements whose centralisers have the same
order are conjugate. -/
theorem isConj_of_card_centralizer_eq [Fintype G] (h : HasDistinctConjClassSizes G) {x y : G}
    (hxy : Nat.card (Subgroup.centralizer ({x} : Set G)) =
      Nat.card (Subgroup.centralizer ({y} : Set G))) : IsConj x y := by
  rw [← ConjClasses.mk_eq_mk_iff_isConj]
  apply h
  have hx := conjClassCard_mk_mul_card_centralizer x
  have hy := conjClassCard_mk_mul_card_centralizer y
  have hpos : 0 < Nat.card (Subgroup.centralizer ({y} : Set G)) := Nat.card_pos
  rw [hxy] at hx
  exact Nat.eq_of_mul_eq_mul_right hpos (hx.trans hy.symm)

/-- Elements generating the same cyclic subgroup have the same centraliser. -/
theorem centralizer_singleton_eq_of_zpowers_eq {x y : G}
    (hxy : Subgroup.zpowers x = Subgroup.zpowers y) :
    Subgroup.centralizer ({x} : Set G) = Subgroup.centralizer {y} := by
  rw [← Subgroup.centralizer_closure {x}, ← Subgroup.centralizer_closure {y},
    ← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure, hxy]

/-- Elements generating the same cyclic subgroup are conjugate. -/
theorem isConj_of_zpowers_eq [Fintype G] (h : HasDistinctConjClassSizes G) {x y : G}
    (hxy : Subgroup.zpowers x = Subgroup.zpowers y) : IsConj x y :=
  isConj_of_card_centralizer_eq h (by rw [centralizer_singleton_eq_of_zpowers_eq hxy])

/-- Every element is conjugate to its inverse. -/
theorem isConj_inv [Fintype G] (h : HasDistinctConjClassSizes G) (x : G) : IsConj x x⁻¹ :=
  isConj_of_zpowers_eq h Subgroup.zpowers_inv.symm

/-- Rationality: every element is conjugate to each of its powers generating the same cyclic
subgroup. -/
theorem isConj_pow_of_coprime [Fintype G] (h : HasDistinctConjClassSizes G) (x : G) {k : ℕ}
    (hk : k.Coprime (orderOf x)) : IsConj x (x ^ k) := by
  apply isConj_of_zpowers_eq h
  apply le_antisymm
  · obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hk
    rw [Subgroup.zpowers_le]
    have := Subgroup.npow_mem_zpowers (x ^ k) m
    rwa [hm] at this
  · rw [Subgroup.zpowers_le]
    exact Subgroup.npow_mem_zpowers x k

theorem commute_of_sq_commute_of_odd {c x : G} (hodd : Odd (orderOf c))
    (hc : Commute (c ^ 2) x) : Commute c x := by
  obtain ⟨m, hm⟩ := hodd
  have : c = (c ^ 2) ^ (m + 1) := by
    rw [← pow_mul, show 2 * (m + 1) = orderOf c + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [this]
  exact hc.pow_left _

/-- An element of odd order which is inverted by an element of odd order is trivial. -/
theorem eq_one_of_odd_of_conj_eq_inv {c x : G} (hc : Odd (orderOf c)) (hx : Odd (orderOf x))
    (hcx : c * x * c⁻¹ = x⁻¹) : x = 1 := by
  have h2 : Commute (c ^ 2) x := by
    have : c ^ 2 * x * (c ^ 2)⁻¹ = x := by
      have : c ^ 2 * x * (c ^ 2)⁻¹ = c * (c * x * c⁻¹) * c⁻¹ := by
        rw [pow_two]; group
      rw [this, hcx]
      have : c * x⁻¹ * c⁻¹ = (c * x * c⁻¹)⁻¹ := by group
      rw [this, hcx, inv_inv]
    exact mul_inv_eq_iff_eq_mul.mp this
  have h1 : Commute c x := commute_of_sq_commute_of_odd hc h2
  have hxx : x = x⁻¹ := by
    rw [← hcx, h1.eq, mul_inv_cancel_right]
  have hsq : x ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [hxx]
    exact mul_inv_cancel x
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  have : orderOf x = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact h1
    · rw [h2] at hx; exact absurd hx (by decide)
  exact orderOf_eq_one_iff.mp this

/-- Every nontrivial finite group in which each element is conjugate to its inverse has even order. -/
theorem two_dvd_card_of_all_real [Nontrivial G] (hr : ∀ x : G, IsConj x x⁻¹) : 2 ∣ Nat.card G := by
  by_contra hodd
  have hoddG : Odd (Nat.card G) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)
  obtain ⟨x, hx⟩ := exists_ne (1 : G)
  obtain ⟨c, hc⟩ := isConj_iff.mp (hr x)
  exact hx (eq_one_of_odd_of_conj_eq_inv (hoddG.of_dvd_nat (orderOf_dvd_natCard c))
    (hoddG.of_dvd_nat (orderOf_dvd_natCard x)) hc)

/-- A nontrivial group with pairwise distinct class sizes has even order. -/
theorem two_dvd_card [Fintype G] (h : HasDistinctConjClassSizes G) [Nontrivial G] : 2 ∣ Nat.card G :=
  two_dvd_card_of_all_real (isConj_inv h)

end Basic

section Local

variable {G : Type*} [Group G]

/-- The centraliser of a product of two commuting elements of coprime orders is the intersection
of the two centralisers. -/
theorem centralizer_mul_of_commute_of_coprime {x y : G} (hc : Commute x y)
    (hco : (orderOf x).Coprime (orderOf y)) :
    Subgroup.centralizer ({x * y} : Set G) =
      Subgroup.centralizer {x} ⊓ Subgroup.centralizer {y} := by
  obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime hco.symm
  obtain ⟨l, hl⟩ := exists_pow_eq_self_of_coprime hco
  have hx : ((x * y) ^ orderOf y) ^ k = x := by
    rw [hc.mul_pow, pow_orderOf_eq_one, mul_one, hk]
  have hy : ((x * y) ^ orderOf x) ^ l = y := by
    rw [hc.mul_pow, pow_orderOf_eq_one, one_mul, hl]
  ext g
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hg
    have hg' : Commute g (x * y) := hg
    exact ⟨hx ▸ ((hg'.pow_right _).pow_right _).eq, hy ▸ ((hg'.pow_right _).pow_right _).eq⟩
  · rintro ⟨h1, h2⟩
    exact (Commute.mul_right h1 h2 : Commute g (x * y)).eq

/-- **Local anti-homogeneity.** Let `x` commute with `y` and `y'`, whose orders are coprime to the
order of `x`.  If `C(x) ∩ C(y)` and `C(x) ∩ C(y')` have the same order, then `y` and `y'` are
conjugate under the centraliser of `x`. -/
theorem exists_conj_of_card_centralizer_inf_eq [Fintype G] (h : HasDistinctConjClassSizes G)
    {x y y' : G} (hxy : Commute x y) (hxy' : Commute x y')
    (hco : (orderOf x).Coprime (orderOf y)) (hco' : (orderOf x).Coprime (orderOf y'))
    (hcard : Nat.card ↥(Subgroup.centralizer {x} ⊓ Subgroup.centralizer {y}) =
      Nat.card ↥(Subgroup.centralizer {x} ⊓ Subgroup.centralizer {y'})) :
    ∃ c : G, c * x = x * c ∧ c * y * c⁻¹ = y' := by
  have hconj : IsConj (x * y) (x * y') := isConj_of_card_centralizer_eq h (by
    rw [centralizer_mul_of_commute_of_coprime hxy hco,
      centralizer_mul_of_commute_of_coprime hxy' hco', hcard])
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  have hpow : c * (x * y) ^ (orderOf y * orderOf y') * c⁻¹ =
      (x * y') ^ (orderOf y * orderOf y') := by
    rw [← hc, conj_pow]
  have e1 : (x * y) ^ (orderOf y * orderOf y') = x ^ (orderOf y * orderOf y') := by
    rw [hxy.mul_pow, pow_mul y, pow_orderOf_eq_one, one_pow, mul_one]
  have e2 : (x * y') ^ (orderOf y * orderOf y') = x ^ (orderOf y * orderOf y') := by
    rw [hxy'.mul_pow, mul_comm (orderOf y), pow_mul y', pow_orderOf_eq_one, one_pow, mul_one]
  rw [e1, e2] at hpow
  have hco2 : (orderOf y * orderOf y').Coprime (orderOf x) :=
    Nat.Coprime.mul_left hco.symm hco'.symm
  obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime hco2
  have hcx : Commute c (x ^ (orderOf y * orderOf y')) := mul_inv_eq_iff_eq_mul.mp hpow
  have hcx' : Commute c x := hk ▸ hcx.pow_right k
  refine ⟨c, hcx'.eq, ?_⟩
  have h1 : c * y * c⁻¹ = (c * x * c⁻¹)⁻¹ * (c * (x * y) * c⁻¹) := by group
  have h2 : c * x * c⁻¹ = x := by rw [hcx'.eq]; group
  rw [h1, hc, h2]; group

end Local

section Endgame

variable {G : Type*} [Group G]

/-- In a subgroup of order two, every element is trivial or equal to a given nontrivial one. -/
theorem eq_one_or_eq_of_mem_of_card_eq_two {H : Subgroup G} (hH : Nat.card H = 2) {g x : G}
    (hg : g ∈ H) (hg1 : g ≠ 1) (hx : x ∈ H) : x = 1 ∨ x = g := by
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : H)).mp hH
  by_cases hx1 : x = 1
  · exact Or.inl hx1
  · right
    have h1 : (⟨x, hx⟩ : H) = y := hy _ (fun h => hx1 (congrArg Subtype.val h))
    have h2 : (⟨g, hg⟩ : H) = y := hy _ (fun h => hg1 (congrArg Subtype.val h))
    exact congrArg Subtype.val (h1.trans h2.symm)

/-- A nontrivial group with pairwise distinct class sizes does not have order two. -/
theorem card_ne_two [Fintype G] (h : HasDistinctConjClassSizes G) [Nontrivial G] :
    Nat.card G ≠ 2 := by
  intro h2
  obtain ⟨x, hx⟩ := exists_ne (1 : G)
  have hZ : Subgroup.center G = ⊥ := trivial_center_of_hasDistinctConjClassSizes h
  have hall : ∀ y : G, y = 1 ∨ y = x := by
    intro y
    have htop : Nat.card (⊤ : Subgroup G) = 2 := by rw [Subgroup.card_top, h2]
    exact eq_one_or_eq_of_mem_of_card_eq_two htop (Subgroup.mem_top x) hx (Subgroup.mem_top y)
  have hxZ : x ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro y
    rcases hall y with rfl | rfl
    · simp
    · rfl
  rw [hZ, Subgroup.mem_bot] at hxZ
  exact hx hxZ

/-- **Endgame.** If some element of a nontrivial group with pairwise distinct class sizes has a
centraliser of order `2`, then the group is isomorphic to `S₃`. -/
theorem nonempty_mulEquiv_perm_three_of_card_centralizer_eq_two [Fintype G]
    (h : HasDistinctConjClassSizes G) [Nontrivial G] {g : G}
    (hg : Nat.card (Subgroup.centralizer ({g} : Set G)) = 2) :
    Nonempty (G ≃* Equiv.Perm (Fin 3)) := by
  classical
  have hZ : Subgroup.center G = ⊥ := trivial_center_of_hasDistinctConjClassSizes h
  -- Step 1: `g ≠ 1`.
  have hg1 : g ≠ 1 := by
    rintro rfl
    have : Subgroup.centralizer ({1} : Set G) = ⊤ := by
      rw [Subgroup.centralizer_eq_top_iff_subset]; simp
    rw [this, Subgroup.card_top] at hg
    exact card_ne_two h hg
  -- Step 2: `C_G(g) = ⟨g⟩` has two elements `1, g`.
  have hgC : g ∈ Subgroup.centralizer ({g} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hC : ∀ x : G, x * g = g * x → x = 1 ∨ x = g := fun x hx =>
    eq_one_or_eq_of_mem_of_card_eq_two hg hgC hg1 (Subgroup.mem_centralizer_singleton_iff.mpr hx)
  have hgg : g * g = 1 := by
    rcases hC (g * g) (by group) with h1 | h2
    · exact h1
    · exact absurd (mul_eq_left.mp h2) hg1
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_left hgg
  have hzle : Subgroup.zpowers g ≤ Subgroup.centralizer ({g} : Set G) :=
    Subgroup.zpowers_le.mpr hgC
  have hord : orderOf g = 2 := by
    have hdvd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, hgg])
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact absurd (orderOf_eq_one_iff.mp h1) hg1
    · exact h2
  have hCeq : Subgroup.zpowers g = Subgroup.centralizer ({g} : Set G) :=
    Subgroup.eq_of_le_of_card_ge hzle (by rw [hg, Nat.card_zpowers, hord])
  -- Step 3: `⟨g⟩` is a Sylow `2`-subgroup.
  have hpg : IsPGroup 2 (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  obtain ⟨P, hP⟩ := IsPGroup.exists_le_sylow hpg
  have hgP : g ∈ (P : Subgroup G) := hP (Subgroup.mem_zpowers g)
  have hPle : (P : Subgroup G) ≤ Subgroup.centralizer ({g} : Set G) := by
    have hnt : Nontrivial (P : Subgroup G) :=
      ⟨⟨⟨g, hgP⟩, 1, fun h => hg1 (congrArg Subtype.val h)⟩⟩
    have hcnt : Nontrivial (Subgroup.center (P : Subgroup G)) := P.isPGroup'.center_nontrivial
    obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center (P : Subgroup G))
    have hzg : ((z : (P : Subgroup G)) : G) = g := by
      have hcomm : (z : (P : Subgroup G)) * ⟨g, hgP⟩ = ⟨g, hgP⟩ * z :=
        (Subgroup.mem_center_iff.mp z.2 ⟨g, hgP⟩).symm
      have hcomm' : ((z : (P : Subgroup G)) : G) * g = g * z := congrArg Subtype.val hcomm
      rcases hC _ hcomm' with h1 | h2
      · exact absurd (Subtype.ext (Subtype.ext h1)) hz
      · exact h2
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_center_iff.mp z.2 ⟨x, hx⟩
    have := congrArg Subtype.val this
    simpa [hzg] using this
  have hPeq : (P : Subgroup G) = Subgroup.zpowers g := le_antisymm (hCeq ▸ hPle) hP
  have hPmem : ∀ x : G, x ∈ (P : Subgroup G) → x = 1 ∨ x = g := fun x hx =>
    hC x (Subgroup.mem_centralizer_singleton_iff.mp (hPle hx))
  have hPcard : Nat.card (P : Subgroup G) = 2 := by rw [hPeq, Nat.card_zpowers, hord]
  -- Step 4: Burnside's transfer theorem gives a normal complement `K`.
  have hNC : Subgroup.normalizer (P : Set G) ≤ Subgroup.centralizer (P : Set G) := by
    intro n hn
    have hn' := (Subgroup.mem_normalizer_iff.mp hn g).mp hgP
    have hng : n * g = g * n := by
      rcases hPmem _ hn' with h1 | h2
      · exfalso
        apply hg1
        have : g = n⁻¹ * (n * g * n⁻¹) * n := by group
        rw [this, h1]; group
      · calc n * g = n * g * n⁻¹ * n := by group
          _ = g * n := by rw [h2]
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    rcases hPmem p hp with rfl | rfl
    · simp
    · exact hng.symm
  set K : Subgroup G := (MonoidHom.transferSylow P hNC).ker with hKdef
  have hK : K.IsComplement' (P : Subgroup G) := MonoidHom.ker_transferSylow_isComplement' P hNC
  have hdisj : ∀ x : G, x ∈ K → x ∈ (P : Subgroup G) → x = 1 := fun x hxK hxP =>
    Subgroup.disjoint_def.mp hK.disjoint hxK hxP
  have hdecomp : ∀ x : G, ∃ k ∈ K, x = k ∨ x = k * g := by
    intro x
    obtain ⟨⟨k, p⟩, hkp⟩ := hK.2 x
    refine ⟨k.1, k.2, ?_⟩
    rcases hPmem p.1 p.2 with h1 | h2
    · left; rw [← hkp]; simp [h1]
    · right; rw [← hkp]; simp [h2]
  -- Step 5: conjugation by `g` is a fixed-point-free involution of `K`.
  let φ : MulAut K := MulAut.conjNormal g
  have hφ : ∀ k : K, ((φ k : K) : G) = g * k * g⁻¹ := fun k => MulAut.conjNormal_apply g k
  have hfpf : MonoidHom.FixedPointFree φ := by
    intro k hk
    have h1 : g * (k : G) * g⁻¹ = k := by rw [← hφ k, hk]
    have h2 : (k : G) * g = g * k := by
      calc (k : G) * g = g * (k : G) * g⁻¹ * g := by rw [h1]
        _ = g * k := by group
    have h3 : (k : G) ∈ (P : Subgroup G) := by
      rw [hPeq, hCeq]; exact Subgroup.mem_centralizer_singleton_iff.mpr h2
    exact Subtype.ext (hdisj _ k.2 h3)
  have hinv : Function.Involutive φ := by
    intro k
    apply Subtype.ext
    rw [hφ, hφ, hginv]
    calc g * (g * (k : G) * g) * g = (g * g) * k * (g * g) := by group
      _ = k := by rw [hgg]; simp
  have hφinv : ∀ k : K, g * (k : G) * g⁻¹ = (k : G)⁻¹ := by
    intro k
    have := congrFun (MonoidHom.FixedPointFree.coe_eq_inv_of_involutive hfpf hinv) k
    rw [← hφ k, this]; rfl
  have hKcomm : ∀ a b : G, a ∈ K → b ∈ K → a * b = b * a := by
    intro a b ha hb
    have := MonoidHom.FixedPointFree.commute_all_of_involutive hfpf hinv ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this.eq
  -- Step 6: conjugates of an element of `K` are the element or its inverse.
  have hconj : ∀ k : G, k ∈ K → ∀ c : G, c * k * c⁻¹ = k ∨ c * k * c⁻¹ = k⁻¹ := by
    intro k hk c
    obtain ⟨k₀, hk₀, hc | hc⟩ := hdecomp c
    · left
      rw [hc, hKcomm k₀ k hk₀ hk]; group
    · right
      have h1 : g * k * g⁻¹ = k⁻¹ := hφinv ⟨k, hk⟩
      have h2 : k₀ * k⁻¹ = k⁻¹ * k₀ := hKcomm k₀ k⁻¹ hk₀ (K.inv_mem hk)
      calc c * k * c⁻¹ = k₀ * (g * k * g⁻¹) * k₀⁻¹ := by rw [hc]; group
        _ = k₀ * k⁻¹ * k₀⁻¹ := by rw [h1]
        _ = k⁻¹ := by rw [h2]; group
  -- Step 7: the centraliser of a nontrivial element of `K` is `K`.
  have hcentK : ∀ k : G, k ∈ K → k ≠ 1 → Subgroup.centralizer ({k} : Set G) = K := by
    intro k hk hk1
    ext x
    rw [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hx
      obtain ⟨k₀, hk₀, hc | hc⟩ := hdecomp x
      · rw [hc]; exact hk₀
      · exfalso
        apply hk1
        have h1 : g * k * g⁻¹ = k⁻¹ := hφinv ⟨k, hk⟩
        have h2 : k₀ * k = k * k₀ := hKcomm k₀ k hk₀ hk
        have h3 : g * k = k * g := by
          have : k₀ * g * k = k * (k₀ * g) := by rw [← hc]; exact hx
          have : k₀ * (g * k) = k₀ * (k * g) := by
            calc k₀ * (g * k) = k₀ * g * k := by group
              _ = k * (k₀ * g) := this
              _ = (k * k₀) * g := by group
              _ = (k₀ * k) * g := by rw [h2]
              _ = k₀ * (k * g) := by group
          exact mul_left_cancel this
        have h4 : (⟨k, hk⟩ : K) = 1 := hfpf ⟨k, hk⟩ (by
          apply Subtype.ext
          rw [hφ]
          calc g * k * g⁻¹ = k * g * g⁻¹ := by rw [h3]
            _ = k := by group)
        exact congrArg Subtype.val h4
    · intro hx
      exact hKcomm x k hx hk
  -- Step 8: `K = {1, k, k⁻¹}` for any nontrivial `k ∈ K`.
  have hKne : ∃ k : G, k ∈ K ∧ k ≠ 1 := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have hK1 : Nat.card K = 1 := by
      have : K = ⊥ := (Subgroup.eq_bot_iff_forall K).mpr hcon
      rw [this, Subgroup.card_bot]
    have := hK.card_mul_card
    rw [hK1, hPcard] at this
    exact card_ne_two h this.symm
  obtain ⟨k, hk, hk1⟩ := hKne
  have hkinv : k⁻¹ ≠ k := by
    intro hkk
    apply hk1
    have h4 : (⟨k, hk⟩ : K) = 1 := hfpf ⟨k, hk⟩ (by
      apply Subtype.ext
      rw [hφ, hφinv ⟨k, hk⟩]
      exact hkk)
    exact congrArg Subtype.val h4
  have hKset : ∀ x : G, x ∈ K → x = 1 ∨ x = k ∨ x = k⁻¹ := by
    intro x hx
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · right
      have hconjkx : IsConj k x := isConj_of_card_centralizer_eq h (by
        rw [hcentK k hk hk1, hcentK x hx hx1])
      obtain ⟨c, hc⟩ := isConj_iff.mp hconjkx
      rcases hconj k hk c with h1 | h2
      · left; rw [← hc, h1]
      · right; rw [← hc, h2]
  have hKcard : Nat.card K = 3 := by
    have hset : (K : Set G) = {1, k, k⁻¹} := by
      ext x
      simp only [SetLike.mem_coe, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · exact hKset x
      · rintro (rfl | rfl | rfl)
        · exact K.one_mem
        · exact hk
        · exact K.inv_mem hk
    have : Nat.card K = (K : Set G).ncard := (Nat.card_coe_set_eq (K : Set G))
    rw [this, Set.ncard_eq_three]
    exact ⟨1, k, k⁻¹, fun h => hk1 h.symm, fun h => hk1 (inv_eq_one.mp h.symm),
      fun h => hkinv h.symm, hset⟩
  have hGcard : Nat.card G = 6 := by
    rw [← hK.card_mul_card, hKcard, hPcard]
  -- Step 9: the action on the three cosets of `P` gives the isomorphism.
  let f : G →* Equiv.Perm (G ⧸ (P : Subgroup G)) := MulAction.toPermHom G (G ⧸ (P : Subgroup G))
  have hfinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.normalCore_eq_ker, Subgroup.eq_bot_iff_forall]
    intro x hx
    by_contra hx1
    have hxg : x = g := (hPmem x (Subgroup.normalCore_le _ hx)).resolve_left hx1
    apply hg1
    have hgZ : g ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro c
      have hnc : c * g * c⁻¹ ∈ (P : Subgroup G).normalCore :=
        (Subgroup.normalCore_normal (P : Subgroup G)).conj_mem g (hxg ▸ hx) c
      rcases hPmem _ (Subgroup.normalCore_le _ hnc) with h1 | h2
      · exfalso
        apply hg1
        have : g = c⁻¹ * (c * g * c⁻¹) * c := by group
        rw [this, h1]; group
      · calc c * g = c * g * c⁻¹ * c := by group
          _ = g * c := by rw [h2]
    rw [hZ, Subgroup.mem_bot] at hgZ
    exact hgZ
  have hquot : Nat.card (G ⧸ (P : Subgroup G)) = 3 := by
    rw [← Subgroup.index_eq_card, hK.index_eq_card, hKcard]
  have hfbij : Function.Bijective f := by
    apply hfinj.bijective_of_nat_card_le
    rw [Nat.card_perm, hquot, hGcard]
    decide
  exact ⟨(MulEquiv.ofBijective f hfbij).trans (Finite.equivFinOfCardEq hquot).permCongrHom⟩

/-- If a Sylow `2`-subgroup `P = {1, g}` has order two, Burnside's transfer theorem provides a
normal complement `K`, and every element of `G` lies in `K` or in `K g`. -/
theorem exists_normal_complement_of_sylow_card_two [Finite G] (P : Sylow 2 G)
    (hP : Nat.card (P : Subgroup G) = 2) {g : G} (hg : g ∈ (P : Subgroup G)) (hg1 : g ≠ 1) :
    ∃ K : Subgroup G, K.Normal ∧ K.IsComplement' (P : Subgroup G) ∧
      ∀ x : G, ∃ k ∈ K, x = k ∨ x = k * g := by
  have hPmem : ∀ x : G, x ∈ (P : Subgroup G) → x = 1 ∨ x = g := fun x hx =>
    eq_one_or_eq_of_mem_of_card_eq_two hP hg hg1 hx
  have hNC : Subgroup.normalizer (P : Set G) ≤ Subgroup.centralizer (P : Set G) := by
    intro n hn
    have hn' := (Subgroup.mem_normalizer_iff.mp hn g).mp hg
    have hng : n * g = g * n := by
      rcases hPmem _ hn' with h1 | h2
      · exfalso
        apply hg1
        have : g = n⁻¹ * (n * g * n⁻¹) * n := by group
        rw [this, h1]; group
      · calc n * g = n * g * n⁻¹ * n := by group
          _ = g * n := by rw [h2]
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    rcases hPmem p hp with rfl | rfl
    · simp
    · exact hng.symm
  have hK : (MonoidHom.transferSylow P hNC).ker.IsComplement' (P : Subgroup G) :=
    MonoidHom.ker_transferSylow_isComplement' P hNC
  refine ⟨(MonoidHom.transferSylow P hNC).ker, inferInstance, hK, ?_⟩
  intro x
  obtain ⟨⟨k, p⟩, hkp⟩ := hK.2 x
  refine ⟨k.1, k.2, ?_⟩
  rcases hPmem p.1 p.2 with h1 | h2
  · left; rw [← hkp]; simp [h1]
  · right; rw [← hkp]; simp [h2]

/-- A finite real group of order twice an odd number has a centralizer of order two. -/
theorem exists_card_centralizer_eq_two_of_all_real_of_not_four_dvd [Fintype G] [Nontrivial G]
    (hr : ∀ x : G, IsConj x x⁻¹) (h4 : ¬ 4 ∣ Nat.card G) :
    ∃ g : G, Nat.card (Subgroup.centralizer ({g} : Set G)) = 2 := by
  classical
  have h2 : 2 ∣ Nat.card G := two_dvd_card_of_all_real hr
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have ht1 : t ≠ 1 := by
    intro h1; rw [h1, orderOf_one] at ht; exact absurd ht (by decide)
  have htt : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left htt
  have hpt : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  obtain ⟨P, hP⟩ := IsPGroup.exists_le_sylow hpt
  have htP : t ∈ (P : Subgroup G) := hP (Subgroup.mem_zpowers t)
  -- the Sylow `2`-subgroup has order two
  have hPcard : Nat.card (P : Subgroup G) = 2 := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp P.isPGroup'
    have hle : 2 ≤ Nat.card (P : Subgroup G) := by
      have := Subgroup.card_le_of_le hP
      rwa [Nat.card_zpowers, ht] at this
    have hdvd : Nat.card (P : Subgroup G) ∣ Nat.card G := Subgroup.card_subgroup_dvd_card _
    rw [hn] at hle hdvd ⊢
    match n, hle, hdvd with
    | 0, hle, _ => simp at hle
    | 1, _, _ => rfl
    | (m + 2), _, hdvd =>
      exfalso
      apply h4
      exact Dvd.dvd.trans ⟨2 ^ m, by ring⟩ hdvd
  obtain ⟨K, hKn, hK, hdecomp⟩ := exists_normal_complement_of_sylow_card_two P hPcard htP ht1
  -- `K` has odd order
  have hKodd : Odd (Nat.card K) := by
    have hmul := hK.card_mul_card
    rw [hPcard] at hmul
    rcases Nat.even_or_odd (Nat.card K) with he | ho
    · exfalso
      apply h4
      obtain ⟨r, hr⟩ := he
      exact ⟨r, by rw [← hmul, hr]; ring⟩
    · exact ho
  have hordK : ∀ k : G, k ∈ K → Odd (orderOf k) := by
    intro k hk
    have : orderOf k ∣ Nat.card K := by
      have := orderOf_dvd_natCard (⟨k, hk⟩ : K)
      rwa [Subgroup.orderOf_mk] at this
    exact hKodd.of_dvd_nat this
  -- an element of `K` commuting with `t` is trivial
  have hfix : ∀ k : G, k ∈ K → k * t = t * k → k = 1 := by
    intro k hk hkt
    have hm := hordK k hk
    obtain ⟨c, hc⟩ := isConj_iff.mp (hr (t * k))
    obtain ⟨j, hj⟩ := hm
    have hcomm : Commute t k := hkt.symm
    have hpow : (t * k) ^ orderOf k = t := by
      rw [hcomm.mul_pow, pow_orderOf_eq_one, mul_one, hj, pow_succ, pow_mul, pow_two, htt,
        one_pow, one_mul]
    have hct : c * t * c⁻¹ = t := by
      have : c * (t * k) ^ orderOf k * c⁻¹ = (c * (t * k) * c⁻¹) ^ orderOf k := by
        rw [conj_pow]
      rw [hpow, hc, inv_pow, hpow, htinv] at this
      exact this
    have hck : c * k * c⁻¹ = k⁻¹ := by
      have h1 : c * k * c⁻¹ = (c * t * c⁻¹)⁻¹ * (c * (t * k) * c⁻¹) := by group
      rw [h1, hct, hc, htinv, mul_inv_rev, htinv]
      calc t * (k⁻¹ * t) = t * (t * k)⁻¹ := by rw [mul_inv_rev, htinv]
        _ = t * (k * t)⁻¹ := by rw [hkt]
        _ = t * (t * k⁻¹) := by rw [mul_inv_rev, htinv]
        _ = (t * t) * k⁻¹ := by group
        _ = k⁻¹ := by rw [htt, one_mul]
    obtain ⟨k₁, hk₁, hck₁ | hck₁⟩ := hdecomp c
    · rw [hck₁] at hck
      exact eq_one_of_odd_of_conj_eq_inv (hordK k₁ hk₁) (hordK k hk) hck
    · have hck' : k₁ * k * k₁⁻¹ = k⁻¹ := by
        rw [← hck, hck₁]
        calc k₁ * k * k₁⁻¹ = k₁ * (t * k * t⁻¹) * k₁⁻¹ := by
              rw [← hkt]; group
          _ = k₁ * t * k * (k₁ * t)⁻¹ := by group
      exact eq_one_of_odd_of_conj_eq_inv (hordK k₁ hk₁) (hordK k hk) hck'
  -- hence `C_G(t) = ⟨t⟩`
  refine ⟨t, ?_⟩
  have hle : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.zpowers t := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    obtain ⟨k, hk, hxk | hxk⟩ := hdecomp x
    · have : k = 1 := hfix k hk (hxk ▸ hx)
      rw [hxk, this]; exact Subgroup.one_mem _
    · have hkt : k * t = t * k := by
        have h1 : k = x * t := by rw [hxk, mul_assoc, htt, mul_one]
        rw [h1, mul_assoc, htt, mul_one, ← mul_assoc, ← hx, mul_assoc, htt, mul_one]
      have : k = 1 := hfix k hk hkt
      rw [hxk, this, one_mul]; exact Subgroup.mem_zpowers t
  have hge : Subgroup.zpowers t ≤ Subgroup.centralizer ({t} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  rw [le_antisymm hle hge, Nat.card_zpowers, ht]

/-- If `4 ∤ |G|`, then some involution has a centraliser of order two. -/
theorem exists_card_centralizer_eq_two_of_not_four_dvd [Fintype G]
    (h : HasDistinctConjClassSizes G) [Nontrivial G] (h4 : ¬ 4 ∣ Nat.card G) :
    ∃ g : G, Nat.card (Subgroup.centralizer ({g} : Set G)) = 2 :=
  exists_card_centralizer_eq_two_of_all_real_of_not_four_dvd (isConj_inv h) h4

/-- **Reduction I.** A nontrivial finite group with pairwise distinct conjugacy class sizes whose
order is not divisible by `4` is isomorphic to `S₃`.  (No solvability hypothesis is needed.) -/
theorem nonempty_mulEquiv_perm_three_of_not_four_dvd [Fintype G]
    (h : HasDistinctConjClassSizes G) [Nontrivial G] (h4 : ¬ 4 ∣ Nat.card G) :
    Nonempty (G ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨g, hg⟩ := exists_card_centralizer_eq_two_of_not_four_dvd h h4
  exact nonempty_mulEquiv_perm_three_of_card_centralizer_eq_two h hg

/-- A nontrivial group with pairwise distinct class sizes which has an abelian subgroup of index
two is isomorphic to `S₃`. -/
theorem nonempty_mulEquiv_perm_three_of_abelian_index_two [Fintype G]
    (h : HasDistinctConjClassSizes G) [Nontrivial G] (A : Subgroup G) (hA : A.index = 2)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) : Nonempty (G ≃* Equiv.Perm (Fin 3)) := by
  classical
  have hZ : Subgroup.center G = ⊥ := trivial_center_of_hasDistinctConjClassSizes h
  have hmul : Nat.card A * 2 = Nat.card G := by rw [← hA]; exact A.card_mul_index
  -- the centraliser of a nontrivial element of `A` is `A`
  have hcent : ∀ a : G, a ∈ A → a ≠ 1 → Subgroup.centralizer ({a} : Set G) = A := by
    intro a ha ha1
    have hle : A ≤ Subgroup.centralizer ({a} : Set G) := fun b hb =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hcomm b hb a ha)
    by_contra hne
    apply ha1
    have htop : Subgroup.centralizer ({a} : Set G) = ⊤ := by
      have hidx : (Subgroup.centralizer ({a} : Set G)).index ∣ A.index :=
        Subgroup.index_dvd_of_le hle
      rw [hA] at hidx
      rcases (Nat.dvd_prime Nat.prime_two).mp hidx with h1 | h2
      · exact Subgroup.index_eq_one.mp h1
      · exfalso
        apply hne
        symm
        apply Subgroup.eq_of_le_of_card_ge hle
        have h3 := (Subgroup.centralizer ({a} : Set G)).card_mul_index
        rw [h2] at h3
        omega
    have haZ : a ∈ Subgroup.center G := by
      have := Subgroup.centralizer_eq_top_iff_subset.mp htop
      exact this (Set.mem_singleton a)
    rwa [hZ, Subgroup.mem_bot] at haZ
  -- hence all nontrivial elements of `A` are conjugate, and a class has at most two elements
  have hclass : ∀ a : G, a ∈ A → a ≠ 1 →
      conjClassCard (ConjClasses.mk a) = 2 := by
    intro a ha ha1
    have h1 := conjClassCard_mk_mul_card_centralizer a
    rw [hcent a ha ha1, ← hmul] at h1
    have hpos : 0 < Nat.card A := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h1, mul_comm])
  have hcard3 : Nat.card A ≤ 3 := by
    by_cases hex : ∃ a : G, a ∈ A ∧ a ≠ 1
    · obtain ⟨a, ha, ha1⟩ := hex
      -- `A ∖ {1}` is contained in the conjugacy class of `a`, which has two elements
      have hsub : (A : Set G) ⊆ insert 1 (ConjClasses.mk a).carrier := by
        intro b hb
        by_cases hb1 : b = 1
        · exact Or.inl hb1
        · right
          rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]
          exact isConj_of_card_centralizer_eq h (by rw [hcent b hb hb1, hcent a ha ha1])
      have hfin : (insert 1 (ConjClasses.mk a).carrier : Set G).Finite := Set.toFinite _
      have h1 : (A : Set G).ncard ≤ (insert 1 (ConjClasses.mk a).carrier : Set G).ncard :=
        Set.ncard_le_ncard hsub hfin
      have h2 : (insert 1 (ConjClasses.mk a).carrier : Set G).ncard ≤
          (ConjClasses.mk a).carrier.ncard + 1 := Set.ncard_insert_le _ _
      have h3 : (ConjClasses.mk a).carrier.ncard = 2 := by
        rw [← Nat.card_coe_set_eq]; exact hclass a ha ha1
      have h4 : Nat.card A = (A : Set G).ncard := Nat.card_coe_set_eq (A : Set G)
      omega
    · simp only [not_exists, not_and, not_not] at hex
      have : A = ⊥ := (Subgroup.eq_bot_iff_forall A).mpr hex
      rw [this, Subgroup.card_bot]
      omega
  apply nonempty_mulEquiv_perm_three_of_not_four_dvd h
  intro h4
  have hne2 := card_ne_two h
  have hpos : 0 < Nat.card A := Nat.card_pos
  have hA2 : Nat.card A ≠ 2 := by
    intro h2
    -- a subgroup of order two has an element `a ≠ 1` with `a⁻¹ = a`, whose class has one element
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := A) 2 (by rw [h2])
    have ha1 : (a : G) ≠ 1 := by
      intro h1
      have : a = 1 := Subtype.ext h1
      rw [this, orderOf_one] at ha
      exact absurd ha (by decide)
    have hall : ∀ b : G, b ∈ A → b = 1 ∨ b = a := fun b hb =>
      eq_one_or_eq_of_mem_of_card_eq_two h2 a.2 ha1 hb
    have hnorm : ∀ c : G, c * (a : G) * c⁻¹ = a := by
      intro c
      have hAn : A.Normal := Subgroup.normal_of_index_eq_two hA
      have hmem : c * (a : G) * c⁻¹ ∈ A := hAn.conj_mem a a.2 c
      rcases hall _ hmem with h1 | h2
      · exfalso
        apply ha1
        have : (a : G) = c⁻¹ * (c * (a : G) * c⁻¹) * c := by group
        rw [this, h1]; group
      · exact h2
    have haZ : (a : G) ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro c
      calc c * (a : G) = c * (a : G) * c⁻¹ * c := by group
        _ = a * c := by rw [hnorm c]
    rw [hZ, Subgroup.mem_bot] at haZ
    exact ha1 haZ
  obtain ⟨r, hr⟩ := h4
  omega

end Endgame

section Weights

open Finset


theorem geom_two (A : ℕ) : ∑ i ∈ range (A + 1), 2 ^ i + 1 = 2 ^ (A + 1) := by
  induction A with
  | zero => simp
  | succ n ih => rw [sum_range_succ]; omega

theorem geom_three (B : ℕ) : 2 * ∑ i ∈ range (B + 1), 3 ^ i + 1 = 3 ^ (B + 1) := by
  induction B with
  | zero => simp
  | succ n ih => rw [sum_range_succ]; omega

theorem geom_five (C : ℕ) : 4 * ∑ i ∈ range (C + 1), 5 ^ i + 1 = 5 ^ (C + 1) := by
  induction C with
  | zero => simp
  | succ n ih => rw [sum_range_succ]; omega

theorem sigma_bound (A B C : ℕ) :
    4 * ArithmeticFunction.sigma 1 (2 ^ A * 3 ^ B * 5 ^ C) < 15 * (2 ^ A * 3 ^ B * 5 ^ C) := by
  have h23 : (2 ^ A).Coprime (3 ^ B) := Nat.Coprime.pow _ _ (by norm_num)
  have h235 : (2 ^ A * 3 ^ B).Coprime (5 ^ C) :=
    Nat.Coprime.mul_left (Nat.Coprime.pow _ _ (by norm_num)) (Nat.Coprime.pow _ _ (by norm_num))
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime h235,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime h23,
    ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two,
    ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_three,
    ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_five]
  have e2 := geom_two A
  have e3 := geom_three B
  have e5 := geom_five C
  set s2 := ∑ i ∈ range (A + 1), 2 ^ i
  set s3 := ∑ i ∈ range (B + 1), 3 ^ i
  set s5 := ∑ i ∈ range (C + 1), 5 ^ i
  have p2 : 0 < 2 ^ A := by positivity
  have p3 : 0 < 3 ^ B := by positivity
  have p5 : 0 < 5 ^ C := by positivity
  have f2 : s2 < 2 * 2 ^ A := by rw [pow_succ] at e2; omega
  have f3 : 2 * s3 < 3 * 3 ^ B := by rw [pow_succ] at e3; omega
  have f5 : 4 * s5 < 5 * 5 ^ C := by rw [pow_succ] at e5; omega
  have g1 : s2 * (2 * s3) < (2 * 2 ^ A) * (3 * 3 ^ B) := Nat.mul_lt_mul'' f2 f3
  have g2 : s2 * (2 * s3) * (4 * s5) < (2 * 2 ^ A) * (3 * 3 ^ B) * (5 * 5 ^ C) :=
    Nat.mul_lt_mul'' g1 f5
  nlinarith [g2]

/-- `∑_{d ∣ N} 1/d = σ(N)/N`. -/
theorem sum_inv_divisors (N : ℕ) (hN : N ≠ 0) :
    ∑ d ∈ N.divisors, (1 : ℚ) / d = (ArithmeticFunction.sigma 1 N : ℚ) / N := by
  have hN' : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  rw [ArithmeticFunction.sigma_one_apply, Nat.cast_sum, ← Nat.sum_div_divisors N (fun d => (d : ℚ)),
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  have hd' := Nat.dvd_of_mem_divisors hd
  have hd0 : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_of_mem_divisors hd).ne'
  rw [Nat.cast_div hd' hd0]
  field_simp

/-- The key numerical estimate of the "weights" argument: the reciprocals of the divisors
`d ≥ 12` of a `{2,3,5}`-number sum to less than `1`. -/
theorem sum_inv_divisors_ge_twelve_lt_one (a b c : ℕ) :
    ∑ d ∈ Finset.filter (fun d : ℕ => 12 ≤ d) (2 ^ a * 3 ^ b * 5 ^ c).divisors,
      (1 : ℚ) / (d : ℚ) < 1 := by
  set n := 2 ^ a * 3 ^ b * 5 ^ c with hn
  set N := 2 ^ (a + 3) * 3 ^ (b + 2) * 5 ^ (c + 1) with hNdef
  have hN0 : N ≠ 0 := by positivity
  have hnN : n ∣ N := ⟨360, by rw [hn, hNdef]; ring⟩
  have h360 : 360 ∣ N := ⟨n, by rw [hn, hNdef]; ring⟩
  have hsub : n.divisors.filter (12 ≤ ·) ⊆ N.divisors.filter (12 ≤ ·) :=
    Finset.filter_subset_filter _ (Nat.divisors_subset_of_dvd hN0 hnN)
  have h1 : ∑ d ∈ n.divisors.filter (12 ≤ ·), (1 : ℚ) / d ≤
      ∑ d ∈ N.divisors.filter (12 ≤ ·), (1 : ℚ) / d :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  have h2 := Finset.sum_filter_add_sum_filter_not N.divisors (12 ≤ ·) (fun d => (1 : ℚ) / d)
  have h3 : ∑ d ∈ N.divisors, (1 : ℚ) / d < 15 / 4 := by
    rw [sum_inv_divisors N hN0, div_lt_div_iff₀ (by positivity) (by norm_num)]
    have := sigma_bound (a + 3) (b + 2) (c + 1)
    have h' : ((4 * ArithmeticFunction.sigma 1 N : ℕ) : ℚ) < ((15 * N : ℕ) : ℚ) := by
      exact_mod_cast this
    push_cast at h'
    linarith
  have hT : ({1, 2, 3, 4, 5, 6, 8, 9, 10} : Finset ℕ) ⊆ N.divisors.filter (fun d => ¬ 12 ≤ d) := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rw [Finset.mem_filter, Nat.mem_divisors]
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨⟨Dvd.dvd.trans (by norm_num) h360, hN0⟩, by norm_num⟩
  have h4 : ∑ d ∈ ({1, 2, 3, 4, 5, 6, 8, 9, 10} : Finset ℕ), (1 : ℚ) / d ≤
      ∑ d ∈ N.divisors.filter (fun d => ¬ 12 ≤ d), (1 : ℚ) / d :=
    Finset.sum_le_sum_of_subset_of_nonneg hT (fun _ _ _ => by positivity)
  have h5 : ∑ d ∈ ({1, 2, 3, 4, 5, 6, 8, 9, 10} : Finset ℕ), (1 : ℚ) / d = 1003 / 360 := by
    norm_num [Finset.sum_insert]
  linarith

theorem not_dvd_smooth {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) (h5 : p ≠ 5)
    (a b c : ℕ) : ¬ p ∣ 2 ^ a * 3 ^ b * 5 ^ c := by
  intro h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
    · exact h3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h))
  · exact h5 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp (hp.dvd_of_dvd_pow h))

variable {G : Type*} [Group G]

/-- The class equation in "weights" form: the reciprocals of the centraliser orders of a set of
class representatives sum to `1`.  Here the centraliser order of a class `c` is written as
`|G| / |c|`. -/
theorem sum_one_div_card_div_conjClassCard [Fintype G] [Fintype (ConjClasses G)] :
    ∑ c : ConjClasses G, (1 : ℚ) / ((Nat.card G / conjClassCard c : ℕ) : ℚ) = 1 := by
  have hGpos : 0 < Nat.card G := Nat.card_pos
  have hG0 : (Nat.card G : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hGpos.ne'
  have hdvd : ∀ c : ConjClasses G, conjClassCard c ∣ Nat.card G ∧ 0 < conjClassCard c := by
    intro c
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
    have := conjClassCard_mk_mul_card_centralizer g
    refine ⟨⟨_, this.symm⟩, ?_⟩
    rcases Nat.eq_zero_or_pos (conjClassCard (ConjClasses.mk g)) with h0 | hp
    · rw [h0, zero_mul] at this; omega
    · exact hp
  have hterm : ∀ c : ConjClasses G,
      (1 : ℚ) / ((Nat.card G / conjClassCard c : ℕ) : ℚ) = (conjClassCard c : ℚ) / Nat.card G := by
    intro c
    obtain ⟨hd, hp⟩ := hdvd c
    have hc0 : (conjClassCard c : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
    rw [Nat.cast_div hd hc0]
    field_simp
  simp_rw [hterm]
  rw [← Finset.sum_div, div_eq_one_iff_eq hG0, ← Nat.cast_sum]
  congr 1
  rw [← Group.sum_card_conj_classes_eq_card G, finsum_eq_sum_of_fintype]
  apply Finset.sum_congr rfl
  intro c _
  exact Nat.card_coe_set_eq c.carrier

/-- **Reduction II (the "weights" skeleton of the Zhang / Knörr–Lempken–Thielcke proofs).**
Let `G` be a nontrivial finite group with pairwise distinct class sizes.  If `|G|` is a
`{2,3,5}`-number (for solvable `G` this is Gow's theorem on rational groups) and no element of
`G` has a centraliser of order `3, 4, 5, 6, 8, 9` or `10`, then `G ≅ S₃`. -/
theorem nonempty_mulEquiv_perm_three_of_smooth_of_no_small_centralizer [Fintype G]
    (h : HasDistinctConjClassSizes G) [Nontrivial G]
    (hsmooth : ∃ a b c : ℕ, Nat.card G = 2 ^ a * 3 ^ b * 5 ^ c)
    (hsmall : ∀ g : G, ∀ m ∈ ({3, 4, 5, 6, 8, 9, 10} : Finset ℕ),
      Nat.card (Subgroup.centralizer ({g} : Set G)) ≠ m) :
    Nonempty (G ≃* Equiv.Perm (Fin 3)) := by
  classical
  by_cases h2 : ∃ g : G, Nat.card (Subgroup.centralizer ({g} : Set G)) = 2
  · obtain ⟨g, hg⟩ := h2
    exact nonempty_mulEquiv_perm_three_of_card_centralizer_eq_two h hg
  exfalso
  obtain ⟨a, b, c, hn⟩ := hsmooth
  have hGpos : 0 < Nat.card G := Nat.card_pos
  let κ : ConjClasses G → ℕ := fun cl => Nat.card G / conjClassCard cl
  have hκmk : ∀ g : G, κ (ConjClasses.mk g) = Nat.card (Subgroup.centralizer ({g} : Set G)) := by
    intro g
    have hmul := conjClassCard_mk_mul_card_centralizer g
    have hpos : 0 < conjClassCard (ConjClasses.mk g) := by
      rcases Nat.eq_zero_or_pos (conjClassCard (ConjClasses.mk g)) with h0 | hp
      · rw [h0, zero_mul] at hmul; omega
      · exact hp
    exact Nat.div_eq_of_eq_mul_right hpos hmul.symm
  -- every centraliser order is at least `12` and divides `|G|`
  have hκ12 : ∀ cl : ConjClasses G, κ cl ∈ Finset.filter (fun d : ℕ => 12 ≤ d) (Nat.card G).divisors := by
    intro cl
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective cl
    rw [hκmk g]
    set m := Nat.card (Subgroup.centralizer ({g} : Set G)) with hm
    have hdvd : m ∣ Nat.card G := Subgroup.card_subgroup_dvd_card _
    have h0 : m ≠ 0 := (Nat.card_pos).ne'
    have h1 : m ≠ 1 := by
      intro h1
      have hbot : Subgroup.centralizer ({g} : Set G) = ⊥ := Subgroup.card_eq_one.mp h1
      have hg1 : g = 1 := by
        have : g ∈ Subgroup.centralizer ({g} : Set G) :=
          Subgroup.mem_centralizer_singleton_iff.mpr rfl
        rwa [hbot, Subgroup.mem_bot] at this
      have htop : Subgroup.centralizer ({g} : Set G) = ⊤ := by
        rw [hg1, Subgroup.centralizer_eq_top_iff_subset]; simp
      exact bot_ne_top (hbot.symm.trans htop)
    have h2' : m ≠ 2 := fun h => h2 ⟨g, h⟩
    have h7 : m ≠ 7 := by
      intro h7
      rw [h7, hn] at hdvd
      exact not_dvd_smooth (by norm_num) (by norm_num) (by norm_num) (by norm_num) a b c hdvd
    have h11 : m ≠ 11 := by
      intro h11
      rw [h11, hn] at hdvd
      exact not_dvd_smooth (by norm_num) (by norm_num) (by norm_num) (by norm_num) a b c hdvd
    have h3 := hsmall g 3 (by simp)
    have h4 := hsmall g 4 (by simp)
    have h5 := hsmall g 5 (by simp)
    have h6 := hsmall g 6 (by simp)
    have h8 := hsmall g 8 (by simp)
    have h9 := hsmall g 9 (by simp)
    have h10 := hsmall g 10 (by simp)
    rw [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨hdvd, hGpos.ne'⟩, by omega⟩
  -- distinct classes have distinct centraliser orders
  have hκinj : Function.Injective κ := by
    intro c₁ c₂ hc
    obtain ⟨g₁, rfl⟩ := ConjClasses.mk_surjective c₁
    obtain ⟨g₂, rfl⟩ := ConjClasses.mk_surjective c₂
    rw [ConjClasses.mk_eq_mk_iff_isConj]
    exact isConj_of_card_centralizer_eq h (by rw [← hκmk g₁, ← hκmk g₂]; exact hc)
  have hsum : ∑ cl : ConjClasses G, (1 : ℚ) / ((κ cl : ℕ) : ℚ) = 1 :=
    sum_one_div_card_div_conjClassCard
  have hle : ∑ cl : ConjClasses G, (1 : ℚ) / ((κ cl : ℕ) : ℚ) ≤
      ∑ d ∈ Finset.filter (fun d : ℕ => 12 ≤ d) (Nat.card G).divisors, (1 : ℚ) / (d : ℚ) := by
    rw [← Finset.sum_image (f := fun d : ℕ => (1 : ℚ) / (d : ℚ)) (s := Finset.univ) (g := κ)
      hκinj.injOn]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro d hd
      obtain ⟨cl, -, rfl⟩ := Finset.mem_image.mp hd
      exact hκ12 cl
    · intro _ _ _
      positivity
  have hlt := sum_inv_divisors_ge_twelve_lt_one a b c
  rw [← hn] at hlt
  linarith

end Weights

section Final

/-- **Reduction I**, in the shape of the target statement (and without solvability): every
nontrivial finite group with pairwise distinct class sizes and order not divisible by `4` is
isomorphic to `S₃`. -/
theorem solution_of_not_four_dvd :
    ∀ (G : Type) [Group G] [Fintype G] [Nontrivial G],
      ConjugacyClassSizes.HasDistinctConjClassSizes (G := G) → ¬ 4 ∣ Nat.card G →
      Nonempty (G ≃* Equiv.Perm (Fin 3)) :=
  fun _ _ _ _ h h4 => nonempty_mulEquiv_perm_three_of_not_four_dvd h h4

/-- The target statement follows by strong induction on `|G|` once `4 ∤ |G|` is known for every
nontrivial solvable ah-group `G` all of whose smaller solvable ah-groups are trivial or `S₃`. -/
theorem solution_of_inductiveOrderClaim
    (hkey : ∀ (G : Type) [Group G] [Fintype G] [Group.IsSolvable G] [Nontrivial G],
      ConjugacyClassSizes.HasDistinctConjClassSizes (G := G) →
      (∀ (K : Type) [Group K] [Fintype K] [Group.IsSolvable K] [Nontrivial K],
      Nat.card K < Nat.card G → ConjugacyClassSizes.HasDistinctConjClassSizes (G := K) →
      Nonempty (K ≃* Equiv.Perm (Fin 3))) →
      ¬ 4 ∣ Nat.card G) :
    ∀ (G : Type) [Group G] [Fintype G] [Group.IsSolvable G] [Nontrivial G],
      ConjugacyClassSizes.HasDistinctConjClassSizes (G := G) →
      Nonempty (G ≃* Equiv.Perm (Fin 3)) := by
  have main : ∀ n : ℕ, ∀ (K : Type) [Group K] [Fintype K] [Group.IsSolvable K] [Nontrivial K],
      Nat.card K < n → ConjugacyClassSizes.HasDistinctConjClassSizes (G := K) →
      Nonempty (K ≃* Equiv.Perm (Fin 3)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro H _ _ _ _ hlt h
      exact nonempty_mulEquiv_perm_three_of_not_four_dvd h (hkey H h (ih _ hlt))
  intro G _ _ _ _ h
  exact main (Nat.card G + 1) G (Nat.lt_succ_self _) h

end Final

section

section Fibre

variable {G : Type*} [Group G] [Fintype G]

/-- Sizes of the classes above one quotient class add up to its size times the kernel size. -/
private theorem sum_classes_above (N : Subgroup G) [N.Normal] (q : ConjClasses (G ⧸ N))
    (s : Finset (ConjClasses G))
    (hs : ∀ c, c ∈ s ↔ ConjClasses.map (QuotientGroup.mk' N) c = q) :
    ∑ c ∈ s, conjClassCard c = Nat.card N * conjClassCard q := by
  classical
  have hpre : ConjClasses.mk ⁻¹' (s : Set (ConjClasses G)) =
      QuotientGroup.mk ⁻¹' q.carrier := by
    ext x
    simp only [Set.mem_preimage, Finset.mem_coe, hs,
      ConjClasses.mem_carrier_iff_mk_eq]
    rfl
  calc
    _ = ∑ c ∈ s, Nat.card {a : G // ConjClasses.mk a = c} := by
      simp only [conjClassCard, ConjClasses.carrier_eq_preimage_mk]
      rfl
    _ = Nat.card (ConjClasses.mk ⁻¹' (s : Set (ConjClasses G))) :=
      (Finset.card_preimage_eq_sum_card_image_eq (fun _ _ => Set.toFinite _)).symm
    _ = _ := by rw [hpre]; exact QuotientGroup.card_preimage_mk N q.carrier

/-- In a quotient with a normal p-group kernel, the classes above a quotient element whose
centralizer is a p-group have sizes equal to the quotient class size times powers of p. -/
private theorem class_above_size (N : Subgroup G) [N.Normal] {p : ℕ} [hp : Fact p.Prime]
    {n m : ℕ} (hN : Nat.card N = p ^ n) (x : G ⧸ N)
    (hx : Nat.card (Subgroup.centralizer ({x} : Set (G ⧸ N))) = p ^ m)
    (c : ConjClasses G) (hc : ConjClasses.map (QuotientGroup.mk' N) c = ConjClasses.mk x) :
    ∃ k : ℕ, conjClassCard c = conjClassCard (ConjClasses.mk x) * p ^ k := by
  classical
  obtain ⟨y, rfl⟩ := c.exists_rep
  let f := QuotientGroup.mk' N
  change ConjClasses.mk (f y) = ConjClasses.mk x at hc
  let C := Subgroup.centralizer ({y} : Set G)
  let Q := Subgroup.centralizer ({f y} : Set (G ⧸ N))
  have hQ : Nat.card Q = p ^ m := by
    have h₁ := conjClassCard_mk_mul_card_centralizer (f y)
    have h₂ := conjClassCard_mk_mul_card_centralizer x
    rw [hc] at h₁
    have : 0 < conjClassCard (ConjClasses.mk x) := by
      let : Nonempty (ConjClasses.mk x).carrier := ⟨⟨x, ConjClasses.mem_carrier_mk⟩⟩
      exact Nat.card_pos
    exact (Nat.eq_of_mul_eq_mul_left this (h₁.trans h₂.symm)).trans hx
  have hle : C ≤ Q.comap f := by
    intro z hz
    change f z ∈ Subgroup.centralizer ({f y} : Set (G ⧸ N))
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by
      simpa only [map_mul] using congrArg f (Subgroup.mem_centralizer_singleton_iff.mp hz))
  have hD : Nat.card (Q.comap f) = Nat.card N * Nat.card Q :=
    QuotientGroup.card_preimage_mk N (Q : Set (G ⧸ N))
  obtain ⟨d, hd⟩ := Subgroup.card_dvd_of_le hle
  have hdvd : d ∣ p ^ (n + m) := by
    rw [pow_add, ← hN, ← hQ, ← hD, hd]
    exact dvd_mul_left _ _
  obtain ⟨k, -, rfl⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd
  refine ⟨k, Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := C)) ?_⟩
  calc
    _ = Nat.card G := conjClassCard_mk_mul_card_centralizer y
    _ = Nat.card (G ⧸ N) * Nat.card N := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    _ = (conjClassCard (ConjClasses.mk (f y)) * Nat.card Q) * Nat.card N := by
      rw [conjClassCard_mk_mul_card_centralizer]
    _ = conjClassCard (ConjClasses.mk x) * (Nat.card N * Nat.card Q) := by rw [hc]; ac_rfl
    _ = _ := by rw [← hD, hd]; ac_rfl

/-- If the kernel and quotient centralizer are p-groups, the entire preimage of the
quotient conjugacy class is one conjugacy class, with unchanged centralizer order. -/
theorem quotient_fibre_of_isPGroup (h : HasDistinctConjClassSizes G) (N : Subgroup G) [N.Normal]
    {p : ℕ} [hp : Fact p.Prime] (hN : IsPGroup p N) (x : G)
    (hQ : IsPGroup p (Subgroup.centralizer ({QuotientGroup.mk' N x} : Set (G ⧸ N)))) :
    (∀ y : G, IsConj (QuotientGroup.mk' N y) (QuotientGroup.mk' N x) → IsConj y x) ∧
    Nat.card (Subgroup.centralizer ({x} : Set G)) =
      Nat.card (Subgroup.centralizer ({QuotientGroup.mk' N x} : Set (G ⧸ N))) := by
  classical
  let f := QuotientGroup.mk' N
  let q := ConjClasses.mk (f x)
  let s := Finset.univ.filter (fun c => ConjClasses.map f c = q)
  have hmem {c : ConjClasses G} : c ∈ s ↔ ConjClasses.map f c = q := by simp [s]
  obtain ⟨n, hn⟩ := hN.exists_card_eq
  obtain ⟨m, hm⟩ := hQ.exists_card_eq
  have hex (c : ConjClasses G) (hc : c ∈ s) : ∃ k, conjClassCard c = conjClassCard q * p ^ k :=
    class_above_size N hn (f x) hm c (hmem.mp hc)
  let k (c : ConjClasses G) : ℕ := if hc : c ∈ s then (hex c hc).choose else 0
  have hk c (hc : c ∈ s) : conjClassCard c = conjClassCard q * p ^ k c := by
    simpa only [k, dif_pos hc] using (hex c hc).choose_spec
  have hinj : Set.InjOn k s := by
    intro a ha b hb hab
    exact h (by rw [hk a ha, hk b hb, hab])
  have hpos : 0 < conjClassCard q := by
    let : Nonempty q.carrier := ⟨⟨f x, ConjClasses.mem_carrier_mk⟩⟩
    exact Nat.card_pos
  have hsum : ∑ i ∈ s.image k, p ^ i = p ^ n := by
    rw [Finset.sum_image hinj]
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [Finset.mul_sum, ← hn, mul_comm (conjClassCard q)]
    exact (Finset.sum_congr rfl fun c hc => (hk c hc).symm).trans (sum_classes_above N q s fun _ => hmem)
  have himage : s.image k = {n} := by
    apply Finset.geomSum_injective hp.out.two_le
    simpa using hsum
  have heq c (hc : c ∈ s) : k c = n := by
    have := Finset.mem_image_of_mem k hc
    simpa only [himage, Finset.mem_singleton] using this
  have hcx : ConjClasses.mk x ∈ s := hmem.mpr rfl
  refine ⟨fun y hy => ?_, ?_⟩
  · apply ConjClasses.mk_eq_mk_iff_isConj.mp
    have hcy : ConjClasses.mk y ∈ s := hmem.mpr (ConjClasses.mk_eq_mk_iff_isConj.mpr hy)
    apply hinj hcy hcx
    rw [heq _ hcy, heq _ hcx]
  · have hc := hk _ hcx
    rw [heq _ hcx, ← hn] at hc
    apply Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hpos (Nat.card_pos (α := N)))
    calc
      _ = Nat.card G := by rw [← hc]; exact conjClassCard_mk_mul_card_centralizer x
      _ = Nat.card (G ⧸ N) * Nat.card N := Subgroup.card_eq_card_quotient_mul_card_subgroup N
      _ = _ := by
        rw [← conjClassCard_mk_mul_card_centralizer (f x)]
        change (conjClassCard q * _) * _ = (conjClassCard q * _) * _
        ac_rfl

/-- A self-centralizing cyclic p-subgroup in the quotient of an ah-group rules out any
nontrivial normal p-group kernel. The centralizer of a lift maps bijectively to the quotient
centralizer, but its conjugation action on a nontrivial kernel would have a nonidentity fixed
point. -/
theorem eq_bot_of_self_centralizing_quotient_zpowers
    (h : HasDistinctConjClassSizes G) (N : Subgroup G) [N.Normal]
    {p : ℕ} [Fact p.Prime] (hN : IsPGroup p N) (q : G ⧸ N)
    (hq : IsPGroup p (Subgroup.zpowers q))
    (hcyc : Subgroup.centralizer ({q} : Set (G ⧸ N)) = Subgroup.zpowers q) : N = ⊥ := by
  classical
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
  let f := QuotientGroup.mk' N
  let C := Subgroup.centralizer ({x} : Set G)
  let Q := Subgroup.centralizer ({f x} : Set (G ⧸ N))
  have hpQ : IsPGroup p Q := by
    change IsPGroup p (Subgroup.centralizer ({QuotientGroup.mk' N x} : Set (G ⧸ N)))
    rw [hcyc]
    exact hq
  have hcard : Nat.card C = Nat.card Q := (quotient_fibre_of_isPGroup h N hN x hpQ).2
  obtain ⟨m, hm⟩ := hpQ.exists_card_eq
  have hpC : IsPGroup p C := IsPGroup.of_card (hcard.trans hm)
  have hx : x ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  let F : C →* Q := (f.comp C.subtype).codRestrict Q fun z =>
    Subgroup.mem_centralizer_singleton_iff.mpr (by
      simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply, map_mul] using
        congrArg f (Subgroup.mem_centralizer_singleton_iff.mp z.2))
  have hsurj : Function.Surjective F := by
    intro z
    have hz := z.property
    change (z : G ⧸ N) ∈ Subgroup.centralizer ({f x} : Set (G ⧸ N)) at hz
    rw [hcyc] at hz
    obtain ⟨i, hi⟩ := hz
    refine ⟨⟨x ^ i, C.zpow_mem hx i⟩, Subtype.ext ?_⟩
    change f (x ^ i) = _
    rwa [map_zpow]
  have hinj := (hsurj.bijective_of_nat_card_le hcard.le).injective
  rcases hN.card_eq_or_dvd with hone | hdvd
  · exact Subgroup.card_eq_one.mp hone
  let : MulAction C N := MulAction.compHom N ((MulAut.conjNormal (H := N)).comp C.subtype)
  have hfix : (1 : N) ∈ MulAction.fixedPoints C N := by
    intro z
    change MulAut.conjNormal (z : G) (1 : N) = 1
    exact map_one _
  obtain ⟨b, hb, hne⟩ := hpC.exists_fixed_point_of_prime_dvd_card_of_fixed_point N hdvd hfix
  have hbc : (b : G) ∈ C := by
    have he := congrArg Subtype.val (hb (⟨x, hx⟩ : C))
    change x * (b : G) * x⁻¹ = b at he
    exact Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he).symm
  have hFb : F ⟨b, hbc⟩ = 1 := Subtype.ext ((QuotientGroup.eq_one_iff (N := N) _).mpr b.2)
  have hb1 : (⟨b, hbc⟩ : C) = 1 := hinj (hFb.trans F.map_one.symm)
  exact False.elim (hne (Subtype.ext (congrArg Subtype.val hb1).symm))

/-- If a subgroup killed in a quotient centralizes a prime-order element of a rational group,
some quotient element has order divisible by p − 1. Conjugate to the power corresponding to
a generator of the units modulo p. -/
theorem exists_quotient_order_multiple_prime_sub_one (h : HasDistinctConjClassSizes G)
    (N : Subgroup G) [N.Normal] {p : ℕ} [hp : Fact p.Prime] {z : G} (hz : orderOf z = p)
    (hcent : N ≤ Subgroup.centralizer ({z} : Set G)) :
    ∃ q : G ⧸ N, p - 1 ∣ orderOf q := by
  classical
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hp.out] at hu
  let r := (u : ZMod p).val
  have hcop : r.Coprime (orderOf z) := hz ▸ ZMod.val_coe_unit_coprime u
  obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_pow_of_coprime h z hcop)
  have iter (i : ℕ) : g ^ i * z * (g ^ i)⁻¹ = z ^ (r ^ i) := by
    induction i with
    | zero => simp
    | succ i ih =>
      calc
        _ = g ^ i * (g * z * g⁻¹) * (g ^ i)⁻¹ := by rw [pow_succ]; group
        _ = (g ^ i * z * (g ^ i)⁻¹) ^ r := by rw [hg, conj_pow]
        _ = _ := by rw [ih, ← pow_mul, pow_succ]
  let q := QuotientGroup.mk' N g
  refine ⟨q, ?_⟩
  have hgN : g ^ orderOf q ∈ N := (QuotientGroup.eq_one_iff _).mp (by
    change QuotientGroup.mk' N (g ^ orderOf q) = 1
    rw [map_pow]
    exact pow_orderOf_eq_one q)
  have hcomm := Subgroup.mem_centralizer_singleton_iff.mp (hcent hgN)
  have he : z ^ (r ^ orderOf q) = z ^ (1 : ℕ) := by
    rw [← iter, hcomm, mul_inv_cancel_right, pow_one]
  have hmod := pow_eq_pow_iff_modEq.mp he
  rw [hz] at hmod
  rw [← hu]
  apply orderOf_dvd_of_pow_eq_one
  apply Units.ext
  simpa only [Nat.cast_pow, r, ZMod.natCast_zmod_val, Nat.cast_one, Units.val_pow_eq_pow_val,
    Units.val_one] using ((ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod)

/-- A nontrivial normal p-subgroup forces an element of order divisible by p − 1 in the
quotient. Apply the preceding result to a prime-order element in its center. -/
theorem exists_quotient_order_multiple_of_normal_pGroup (h : HasDistinctConjClassSizes G)
    (N : Subgroup G) [N.Normal] {p : ℕ} [hp : Fact p.Prime] (hN : IsPGroup p N) (hne : N ≠ ⊥) :
    ∃ q : G ⧸ N, p - 1 ∣ orderOf q := by
  have := N.nontrivial_iff_ne_bot.mpr hne
  have := hN.center_nontrivial
  have hpZ := hN.to_subgroup (Subgroup.center N)
  obtain ⟨a, ha, hcard⟩ := hpZ.nontrivial_iff_card.mp inferInstance
  have hd : p ∣ Nat.card (Subgroup.center N) := by
    rw [hcard]
    exact dvd_pow_self p ha.ne'
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hd
  apply exists_quotient_order_multiple_prime_sub_one h N (z := ((z : N) : G))
  · simpa only [Subgroup.orderOf_coe] using hz
  · intro b hb
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp z.property (⟨b,hb⟩ : N))

/-- A quotient by a normal 2-subgroup can detect a centralizer of order two. -/
theorem nonempty_mulEquiv_perm_three_of_quotient_centralizer_two [Nontrivial G]
    (h : HasDistinctConjClassSizes G) (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
    (t : G ⧸ N) (ht : Nat.card (Subgroup.centralizer ({t} : Set (G ⧸ N))) = 2) :
    Nonempty (G ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N t
  have hQ := IsPGroup.of_card (p := 2) (n := 1) (ht.trans (pow_one 2).symm)
  exact nonempty_mulEquiv_perm_three_of_card_centralizer_eq_two h
    ((quotient_fibre_of_isPGroup h N hN x hQ).2.trans ht)

/-- Reduction I also holds after dividing out an arbitrary normal 2-subgroup. The kernel
must itself be trivial, since a nontrivial real quotient already has even order. -/
theorem quotient_by_twoGroup_of_not_four_dvd [Nontrivial G]
    (h : HasDistinctConjClassSizes G) (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
    (h4 : ¬ 4 ∣ Nat.card (G ⧸ N)) : N = ⊥ ∧ Nonempty (G ≃* Equiv.Perm (Fin 3)) := by
  classical
  let : Fintype (G ⧸ N) := Fintype.ofFinite _
  let f := QuotientGroup.mk' N
  have hr (q : G ⧸ N) : IsConj q q⁻¹ := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
    simpa only [map_inv] using f.map_isConj (isConj_inv h x)
  have hprod := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have : Nontrivial (G ⧸ N) := by
    by_contra htriv
    have := not_nontrivial_iff_subsingleton.mp htriv
    obtain ⟨n, hn⟩ := hN.exists_card_eq
    have hpG : IsPGroup 2 G := IsPGroup.of_card (n := n) (by
      simpa only [Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩, one_mul, hn]
        using hprod)
    exact hpG.bot_lt_center.ne' (trivial_center_of_hasDistinctConjClassSizes h)
  obtain ⟨t, ht⟩ := exists_card_centralizer_eq_two_of_all_real_of_not_four_dvd hr h4
  obtain ⟨e⟩ := nonempty_mulEquiv_perm_three_of_quotient_centralizer_two h N hN t ht
  refine ⟨?_, ⟨e⟩⟩
  rcases hN.card_eq_or_dvd with hn | hn
  · exact Subgroup.card_eq_one.mp hn
  · have hq := two_dvd_card_of_all_real hr
    have hdiv := Nat.mul_dvd_mul hq hn
    rw [← hprod, Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin] at hdiv
    exact False.elim ((by decide : ¬ 2 * 2 ∣ Nat.factorial 3) hdiv)

/-- A finite nontrivial ah-group cannot be a proper extension of S₃ by a normal 2-subgroup. -/
theorem eq_bot_of_isTwoGroup_of_quotient_perm_three [Nontrivial G]
    (h : HasDistinctConjClassSizes G) (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
    (e : (G ⧸ N) ≃* Equiv.Perm (Fin 3)) : N = ⊥ :=
  (quotient_by_twoGroup_of_not_four_dvd h N hN (by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]; decide)).1

/-- No nontrivial normal p-subgroup of an ah-group can have quotient S₃. For p = 3
the quotient has a self-centralizing subgroup of order three. For p ≥ 5 the required
multiple of p − 1 exceeds all element orders in S₃. -/
theorem eq_bot_of_isPGroup_of_quotient_perm_three [Nontrivial G]
    (h : HasDistinctConjClassSizes G) (N : Subgroup G) [N.Normal] {p : ℕ} [hp : Fact p.Prime]
    (hN : IsPGroup p N) (e : (G ⧸ N) ≃* Equiv.Perm (Fin 3)) : N = ⊥ := by
  by_cases hp2 : p = 2
  · subst p
    exact eq_bot_of_isTwoGroup_of_quotient_perm_three h N hN e
  by_cases hp3 : p = 3
  · subst p
    obtain ⟨t, ht, hc⟩ : ∃ t : Equiv.Perm (Fin 3), t ^ 3 = 1 ∧
        ∀ y, y * t = t * y → y = 1 ∨ y = t ∨ y = t ^ 2 := by decide
    obtain ⟨q, rfl⟩ := e.surjective t
    have hq : q ^ 3 = 1 := e.injective (by simpa only [map_pow, map_one] using ht)
    apply eq_bot_of_self_centralizing_quotient_zpowers h N hN q
    · apply IsPGroup.of_card_dvd_pow (n := 1)
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_dvd_of_pow_eq_one hq
    · apply le_antisymm _ (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
      intro y hy
      have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hy
      rcases hc (e y) (by simpa only [map_mul] using congrArg e hcomm) with h1 | h2 | h3
      · rw [e.injective (h1.trans e.map_one.symm)]
        exact Subgroup.one_mem _
      · rw [e.injective h2]
        exact Subgroup.mem_zpowers q
      · rw [e.injective (h3.trans (map_pow e q 2).symm)]
        exact Subgroup.npow_mem_zpowers q 2
  by_contra hne
  obtain ⟨q, hq⟩ := exists_quotient_order_multiple_of_normal_pGroup h N hN hne
  have h5 : 5 ≤ p := by
    by_contra! hl
    have := hp.out
    interval_cases p <;> norm_num at *
  have hle := Nat.le_of_dvd (orderOf_pos q) hq
  have hbnd (t : Equiv.Perm (Fin 3)) : t ^ 2 = 1 ∨ t ^ 3 = 1 := by decide +revert
  rw [← e.orderOf_eq q] at hle
  rcases hbnd (e q) with h2 | h3
  · have := orderOf_le_of_pow_eq_one (by decide : 0 < 2) h2
    omega
  · have := orderOf_le_of_pow_eq_one (by decide : 0 < 3) h3
    omega

end Fibre

end

section

section Derived
open scoped IsMulCommutative

variable {G : Type*} [Group G] [Fintype G]

/-- In a real group every square lies in the commutator subgroup. -/
theorem sq_mem_commutator (h : HasDistinctConjClassSizes G) (g : G) :
    g ^ 2 ∈ commutator G := by
  have e := isConj_iff_eq.mp (Abelianization.of.map_isConj (isConj_inv h g))
  rw [← Abelianization.ker_of, MonoidHom.mem_ker, pow_two, map_mul]
  exact mul_eq_one_iff_eq_inv.mpr (by simpa using e)

private theorem derived_conj_sq (h : HasDistinctConjClassSizes G)
    {A : Subgroup G} [A.Normal] (hc : commutator G ≤ Subgroup.centralizer (A : Set G))
    (g : G) (a : A) :
    MulAut.conjNormal g (MulAut.conjNormal g a) = a := by
  apply Subtype.ext
  have he := (Subgroup.mem_centralizer_iff.mp (hc (sq_mem_commutator h g))) a a.2
  change g * (g * (a : G) * g⁻¹) * g⁻¹ = a
  calc _ = g ^ 2 * a * (g ^ 2)⁻¹ := by rw [pow_two]; group
       _ = a := by rw [← he]; group

private theorem derived_conj_comm (h : HasDistinctConjClassSizes G)
    {A : Subgroup G} [A.Normal] (hc : commutator G ≤ Subgroup.centralizer (A : Set G))
    (g k : G) (a : A) :
    MulAut.conjNormal g (MulAut.conjNormal k a) =
      MulAut.conjNormal k (MulAut.conjNormal g a) := by
  have e := derived_conj_sq h hc (g * k) (MulAut.conjNormal k (MulAut.conjNormal g a))
  simp only [map_mul, MulAut.mul_apply, derived_conj_sq h hc] at e
  exact e

omit [Group G] [Fintype G] in
private theorem exists_common_fixed_involution {A : Type*} [CommGroup A]
    (f : G → MulAut A)
    (hs : ∀ g x, f g (f g x) = x) (hc : ∀ g k x, f g (f k x) = f k (f g x))
    (x : A) (hx : x ≠ 1) (hx2 : x ^ 2 = 1) (s : Finset G) :
    ∃ y : A, y ≠ 1 ∧ y ^ 2 = 1 ∧ ∀ g ∈ s, f g y = y := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨x, hx, hx2, by simp⟩
  | @insert g s _ ih =>
    obtain ⟨y, hy, hy2, hfix⟩ := ih
    by_cases he : f g y = y
    · exact ⟨y, hy, hy2, by simpa [he] using hfix⟩
    · refine ⟨y * f g y, ?_, ?_, ?_⟩
      · intro hprod
        apply he
        calc f g y = y * (y * f g y) := by rw [← mul_assoc, ← pow_two, hy2, one_mul]
             _ = y := by rw [hprod, mul_one]
      · rw [mul_pow, ← map_pow, hy2, map_one, one_mul]
      · intro k hk
        rw [map_mul]
        rcases Finset.mem_insert.mp hk with rfl | hk
        · rw [hs, mul_comm]
        · rw [hc k g, hfix k hk]

/-- A normal abelian subgroup centralized by the commutator subgroup has exponent
dividing three in a finite group with distinct conjugacy class sizes. -/
theorem cube_eq_one_of_derived_centralizes (h : HasDistinctConjClassSizes G)
    (A : Subgroup G) [A.Normal] [IsMulCommutative A]
    (hc : commutator G ≤ Subgroup.centralizer (A : Set G)) (a : A) : a ^ 3 = 1 := by
  classical
  let f : G →* MulAut A := MulAut.conjNormal
  have hs : ∀ g x, f g (f g x) = x := derived_conj_sq h hc
  have hcomm : ∀ g k x, f g (f k x) = f k (f g x) := derived_conj_comm h hc
  have hodd : Odd (orderOf a) := by
    by_contra hn
    obtain ⟨n, hn⟩ := Nat.not_odd_iff_even.mp hn
    have hnpos : 0 < n := by have := orderOf_pos a; omega
    have ha : (a ^ n) ^ 2 = 1 := by
      rw [← pow_mul, show n * 2 = orderOf a by omega, pow_orderOf_eq_one]
    have han : a ^ n ≠ 1 := fun e => (Nat.not_dvd_of_pos_of_lt hnpos (by omega : n < orderOf a))
      (orderOf_dvd_of_pow_eq_one e)
    obtain ⟨y, hy, _, hfix⟩ :=
      exists_common_fixed_involution (G := G) f hs hcomm _ han ha Finset.univ
    have hcenter : (y : G) ∈ Subgroup.center G := by
      apply Subgroup.mem_center_iff.mpr
      intro g
      exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val (hfix g (Finset.mem_univ _)))
    rw [trivial_center_of_hasDistinctConjClassSizes h] at hcenter
    exact hy (Subtype.ext hcenter)
  have hpow := isConj_pow_of_coprime h (a : G) (k := 2) (by
    rw [Subgroup.orderOf_coe]; exact Nat.coprime_two_left.mpr hodd)
  obtain ⟨g, hg⟩ := isConj_iff.mp hpow
  have he : f g a = a ^ 2 := Subtype.ext hg
  have hfour := hs g a
  rw [he, map_pow, he, ← pow_mul] at hfour
  exact mul_right_cancel (b := a) (calc a ^ 3 * a = a ^ 4 := (pow_succ a 3).symm
                                       _ = 1 * a := by simpa using hfour)

omit [Group G] in
private theorem exists_eigen_outside {A : Type*} [CommGroup A]
    (f : G → MulAut A)
    (hs : ∀ g x, f g (f g x) = x) (hc : ∀ g k x, f g (f k x) = f k (f g x))
    (h3 : ∀ a : A, a ^ 3 = 1) (B : Subgroup A) (x : A) (hx : x ∉ B) :
    ∃ y : A, y ∉ B ∧ ∀ g, f g y = y ∨ f g y = y⁻¹ := by
  classical
  suffices ∀ s : Finset G, ∃ y : A, y ∉ B ∧ ∀ g ∈ s, f g y = y ∨ f g y = y⁻¹ by
    obtain ⟨y, hy, he⟩ := this Finset.univ
    exact ⟨y, hy, fun g => he g (Finset.mem_univ _)⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨x, hx, by simp⟩
  | @insert g s _ ih =>
    obtain ⟨y, hy, he⟩ := ih
    let z := f g y
    have hz : f g z = y := hs g y
    by_cases hb : y * z ∈ B
    · have hout : y * z⁻¹ ∉ B := by
        intro hin
        have hsq : y ^ 2 ∈ B := by
          convert B.mul_mem hb hin using 1
          simp [pow_two, mul_mul_mul_comm]
        have hinv : y ^ 2 = y⁻¹ :=
          mul_eq_one_iff_eq_inv.mp (by simpa only [← pow_succ] using h3 y)
        exact hy (B.inv_mem_iff.mp (hinv ▸ hsq))
      refine ⟨_, hout, fun k hk => ?_⟩
      rcases Finset.mem_insert.mp hk with rfl | hk
      · right
        rw [map_mul, map_inv, hz, mul_inv_rev, inv_inv]
      · have hkz : f k z = f g (f k y) := hc k g y
        rcases he k hk with h | h
        · left; simp only [map_mul, map_inv, hkz, h]; rfl
        · right; simp only [map_mul, map_inv, hkz, h, inv_inv, mul_inv_rev]; exact mul_comm _ _
    · refine ⟨_, hb, fun k hk => ?_⟩
      rcases Finset.mem_insert.mp hk with rfl | hk
      · left; rw [map_mul, hz, mul_comm]
      · have hkz : f k z = f g (f k y) := hc k g y
        rcases he k hk with h | h
        · left; simp only [map_mul, hkz, h]; rfl
        · right; simp only [map_mul, hkz, h, map_inv, mul_inv_rev]; exact mul_comm _ _

private theorem class_card_two_of_conj_eq_self_or_inv (h : HasDistinctConjClassSizes G)
    (x : G) (hx : x ≠ x⁻¹) (he : ∀ g : G, g * x * g⁻¹ = x ∨ g * x * g⁻¹ = x⁻¹) :
    conjClassCard (ConjClasses.mk x) = 2 := by
  have hset : (ConjClasses.mk x).carrier = {x, x⁻¹} := by
    ext y
    change IsConj x y ↔ y = x ∨ y = x⁻¹
    constructor
    · rintro ⟨c, hc⟩
      have heq : (↑c : G) * x * (↑c : G)⁻¹ = y := mul_inv_eq_iff_eq_mul.mpr hc
      simpa only [heq] using he c
    · rintro (rfl | rfl)
      · exact IsConj.refl _
      · exact isConj_inv h _
  rw [conjClassCard, hset, Nat.card_coe_set_eq, Set.ncard_pair hx]

/-- An abelian normal subgroup centralized by the derived subgroup has order at most three. -/
theorem card_le_three_of_derived_centralizes (h : HasDistinctConjClassSizes G)
    (A : Subgroup G) [A.Normal] [IsMulCommutative A]
    (hc : commutator G ≤ Subgroup.centralizer (A : Set G)) : Nat.card A ≤ 3 := by
  classical
  let f : G →* MulAut A := MulAut.conjNormal
  have h3 := cube_eq_one_of_derived_centralizes h A hc
  have ex := exists_eigen_outside (G := G) (A := A) f (derived_conj_sq h hc)
    (derived_conj_comm h hc) h3
  have pairCard (a : A) (ha : a ≠ 1) (he : ∀ g, f g a = a ∨ f g a = a⁻¹) :
      conjClassCard (ConjClasses.mk (a : G)) = 2 := by
    apply class_card_two_of_conj_eq_self_or_inv h
    · intro e
      have h2 : a * a = 1 := mul_eq_one_iff_eq_inv.mpr (Subtype.ext e)
      exact ha (by simpa only [pow_succ, pow_zero, h2, one_mul] using h3 a)
    · intro g
      exact (he g).imp (congrArg Subtype.val) (congrArg Subtype.val)
  by_cases hA : ∀ a : A, a = 1
  · have : Subsingleton A := ⟨fun a b => (hA a).trans (hA b).symm⟩
    rw [Nat.card_eq_one_iff_unique.mpr ⟨‹Subsingleton A›, inferInstance⟩]; decide
  obtain ⟨x, hx⟩ := not_forall.mp hA
  obtain ⟨z, hz, he⟩ := ex ⊥ x hx
  have htop : Subgroup.zpowers z = ⊤ := by
    apply top_unique
    intro a _
    by_contra hmem
    obtain ⟨w, hw, hwe⟩ := ex (Subgroup.zpowers z) a hmem
    have hw1 : w ≠ 1 := fun e => hw (e ▸ Subgroup.one_mem _)
    have hconj := ConjClasses.mk_eq_mk_iff_isConj.mp (h ((pairCard z hz he).trans
      (pairCard w hw1 hwe).symm))
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    have hgw : f g z = w := Subtype.ext hg
    rcases (hgw ▸ he g) with e | e
    · exact hw (e ▸ Subgroup.mem_zpowers z)
    · apply hw
      rw [e]
      exact (Subgroup.zpowers z).inv_mem (Subgroup.mem_zpowers _)
  have ho : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one (h3 z)
  rw [← Nat.card_zpowers, htop, Subgroup.card_top] at ho
  exact Nat.le_of_dvd (by decide) ho

/-- The centralizer of the derived subgroup is abelian in a centerless group. -/
private theorem commutator_centralizer_commutative (h : HasDistinctConjClassSizes G) :
    IsMulCommutative (Subgroup.centralizer (commutator G : Set G)) := by
  have hc := commutator_centralizer_commutator_le_center G
  rw [trivial_center_of_hasDistinctConjClassSizes h] at hc
  exact Subgroup.le_centralizer_iff_isMulCommutative.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (le_bot_iff.mp hc))

/-- The centralizer of the derived subgroup of an ah-group has at most three elements. -/
theorem card_centralizer_commutator_le_three (h : HasDistinctConjClassSizes G) :
    Nat.card (Subgroup.centralizer (commutator G : Set G)) ≤ 3 := by
  have := commutator_centralizer_commutative h
  exact card_le_three_of_derived_centralizes h _ (Subgroup.le_centralizer_iff.mpr le_rfl)

/-- The conjecture for groups with abelian commutator subgroup. -/
theorem nonempty_mulEquiv_perm_three_of_abelian_commutator [Nontrivial G]
    (h : HasDistinctConjClassSizes G) [IsMulCommutative (commutator G)] :
    Nonempty (G ≃* Equiv.Perm (Fin 3)) := by
  classical
  let D := commutator G
  let C := Subgroup.centralizer (D : Set G)
  let f : G →* MulAut D := MulAut.conjNormal
  have hker : f.ker = C := by
    ext g
    change f g = 1 ↔ g ∈ Subgroup.centralizer (D : Set G)
    constructor
    · intro he
      apply Subgroup.mem_centralizer_iff.mpr
      intro x hx
      have eqn := congrArg (fun u : MulAut D => ((u ⟨x, hx⟩ : D) : G)) he
      exact (mul_inv_eq_iff_eq_mul.mp eqn).symm
    · intro hg
      ext a
      change g * (a : G) * g⁻¹ = a
      exact mul_inv_eq_iff_eq_mul.mpr ((Subgroup.mem_centralizer_iff.mp hg) a a.2).symm
  have hC : IsMulCommutative C := commutator_centralizer_commutative h
  have hCne : C ≠ ⊤ := by
    intro e
    have he : Subgroup.center G = ⊤ := by
      apply top_unique
      intro x _
      apply Subgroup.mem_center_iff.mpr
      intro y
      exact congrArg Subtype.val (mul_comm (⟨y, e ▸ Subgroup.mem_top y⟩ : C)
        ⟨x, e ▸ Subgroup.mem_top x⟩)
    exact bot_ne_top ((trivial_center_of_hasDistinctConjClassSizes h).symm.trans he)
  have hD : Nat.card D ≤ 3 :=
    card_le_three_of_derived_centralizes h D (Subgroup.le_centralizer_iff_isMulCommutative.mpr
      (inferInstanceAs (IsMulCommutative (commutator G))))
  have hDn : 1 < Nat.card D := by
    apply D.one_lt_card_iff_ne_bot.mpr
    intro e
    apply hCne
    simp [C, e]
  have h23 : Nat.card D = 2 ∨ Nat.card D = 3 := by omega
  have : IsCyclic D := h23.elim (fun e => isCyclic_of_prime_card e)
    (fun e => isCyclic_of_prime_card e)
  have hindex : C.index ≤ 2 := calc
    C.index = Nat.card f.range := hker ▸ Subgroup.index_ker f
    _ ≤ Nat.card (MulAut D) := Nat.card_le_card_of_injective _ Subtype.val_injective
    _ = (Nat.card D).totient := IsCyclic.card_mulAut D
    _ ≤ 2 := by rcases h23 with e | e <;> rw [e] <;> decide
  have hi : C.index ≠ 1 := fun e => hCne (Subgroup.index_eq_one.mp e)
  have hp : 0 < C.index := Nat.card_pos (α := G ⧸ C)
  apply nonempty_mulEquiv_perm_three_of_abelian_index_two h C (by omega)
  intro a ha b hb
  exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : C) ⟨b, hb⟩)

end Derived

end

section

private theorem card_centralizer_subgroup {G : Type*} [Group G] (H : Subgroup G) (y : H) :
    Nat.card (Subgroup.centralizer ({y} : Set H)) =
      Nat.card ↥(H ⊓ Subgroup.centralizer ({(y : G)} : Set G)) := by
  apply Nat.card_congr
  exact
    { toFun := fun z => ⟨z.1.1, z.1.2, Subgroup.mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp z.2))⟩
      invFun := fun z => ⟨⟨z.1, z.property.1⟩, Subgroup.mem_centralizer_singleton_iff.mpr
          (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp z.property.2))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- Two elements of the centralizer whose orders are coprime to that of `x` are conjugate
in the centralizer whenever their centralizers there have the same size. -/
theorem isConj_in_centralizer_of_coprime {G : Type*} [Group G] [Fintype G]
    (h : HasDistinctConjClassSizes G) {x : G} {y z : Subgroup.centralizer ({x} : Set G)}
    (hy : (orderOf x).Coprime (orderOf y)) (hz : (orderOf x).Coprime (orderOf z))
    (hc : Nat.card (Subgroup.centralizer {y}) = Nat.card (Subgroup.centralizer {z})) :
    IsConj y z := by
  have hxy := (Subgroup.mem_centralizer_singleton_iff.mp y.2).symm
  have hxz := (Subgroup.mem_centralizer_singleton_iff.mp z.2).symm
  rw [card_centralizer_subgroup, card_centralizer_subgroup] at hc
  rw [Subgroup.orderOf_mk] at hy hz
  obtain ⟨c, hcx, hcy⟩ := exists_conj_of_card_centralizer_inf_eq h hxy hxz hy hz hc
  exact isConj_iff.mpr ⟨⟨c, Subgroup.mem_centralizer_singleton_iff.mpr hcx⟩, Subtype.ext hcy⟩

private theorem card_centralizer_equiv {C D : Type*} [Group C] [Group D] (e : C ≃* D) (y : C) :
    Nat.card (Subgroup.centralizer {y}) = Nat.card (Subgroup.centralizer {e y}) := by
  apply Nat.card_congr
  apply e.toEquiv.subtypeEquiv
  intro c
  simp only [Subgroup.mem_centralizer_singleton_iff]
  change c * y = y * c ↔ e c * e y = e y * e c
  rw [← map_mul, ← map_mul, e.injective.eq_iff]

private theorem card_centralizer_one_prod {A B : Type*} [Group A] [Group B] (b : B) :
    Nat.card (Subgroup.centralizer ({(1,b)} : Set (A × B))) =
      Nat.card A * Nat.card (Subgroup.centralizer {b}) := by
  have h : Subgroup.centralizer ({(1,b)} : Set (A × B)) = (⊤ : Subgroup A).prod
      (Subgroup.centralizer {b}) := by
    ext v
    rw [Subgroup.mem_prod]
    simp [Subgroup.mem_centralizer_singleton_iff, Prod.ext_iff]
  rw [h, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, Subgroup.card_top]

/-- A direct factor of the centralizer of `x` whose order is coprime to the order of
`x` inherits distinct conjugacy class sizes. -/
theorem hasDistinctConjClassSizes_centralizer_factor {G A B : Type*}
    [Group G] [Fintype G] [Group A] [Group B] [Fintype B]
    (h : HasDistinctConjClassSizes G) {x : G}
    (e : A × B ≃* Subgroup.centralizer ({x} : Set G))
    (hco : (orderOf x).Coprime (Nat.card B)) : HasDistinctConjClassSizes B := by
  classical
  intro u v huv
  obtain ⟨a, rfl⟩ := Quotient.exists_rep u
  obtain ⟨b, rfl⟩ := Quotient.exists_rep v
  change conjClassCard (ConjClasses.mk a) = conjClassCard (ConjClasses.mk b) at huv
  change ConjClasses.mk a = ConjClasses.mk b
  have ha := conjClassCard_mk_mul_card_centralizer a
  have hb := conjClassCard_mk_mul_card_centralizer b
  rw [huv] at ha
  have hab := Nat.eq_of_mul_eq_mul_left (show 0 < conjClassCard (ConjClasses.mk b) by
    change 0 < Nat.card _
    have : Nonempty (ConjClasses.mk b).carrier := ⟨⟨b, ConjClasses.mem_carrier_iff_mk_eq.mpr rfl⟩⟩
    exact Nat.card_pos) (ha.trans hb.symm)
  have hcop (t : B) : (orderOf x).Coprime (orderOf (e (1,t))) := by
    rw [e.orderOf_eq, Prod.orderOf, orderOf_one, Nat.lcm_one_left]
    exact hco.coprime_dvd_right (orderOf_dvd_natCard t)
  have hcard (t : B) : Nat.card (Subgroup.centralizer {e (1,t)}) =
      Nat.card A * Nat.card (Subgroup.centralizer {t}) :=
    (card_centralizer_equiv e (1,t)).symm.trans (card_centralizer_one_prod t)
  have hc := isConj_in_centralizer_of_coprime h (hcop a) (hcop b) (by rw [hcard, hcard, hab])
  obtain ⟨w, hw⟩ := isConj_iff.mp hc
  have hw' := congrArg (fun c => (e.symm c).2) hw
  simp only [map_mul, map_inv, MulEquiv.symm_apply_apply, Prod.snd_mul, Prod.snd_inv] at hw'
  exact ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨(e.symm w).2, hw'⟩)

/-- Inversion pairs the members of every conjugacy class which is closed under inversion
and does not consist of elements of order dividing two. -/
theorem two_dvd_conjClassCard_of_isConj_inv {G : Type*} [Group G] [Fintype G] {x : G}
    (hr : IsConj x x⁻¹) (hx : x ^ 2 ≠ 1) : 2 ∣ conjClassCard (ConjClasses.mk x) := by
  classical
  let C := (ConjClasses.mk x).carrier
  let f (y : C) : C := ⟨(y : G)⁻¹, by
    obtain ⟨c, hc⟩ := isConj_iff.mp (show IsConj x (y : G) from y.2)
    have hy : IsConj x⁻¹ (y : G)⁻¹ := isConj_iff.mpr ⟨c, by rw [← hc]; group⟩
    exact hr.trans hy⟩
  let σ : Equiv.Perm C := Function.Involutive.toPerm f (fun y => Subtype.ext (inv_inv y.1))
  have hσ : σ ^ 2 ^ 1 = 1 := by
    ext y
    exact inv_inv y.1
  change 2 ∣ Nat.card C
  rw [Nat.card_eq_fintype_card]
  by_contra ho
  obtain ⟨y, hy⟩ := Equiv.Perm.exists_fixed_point_of_prime ho hσ
  have hy' : (y.1 : G)⁻¹ = y.1 := congrArg Subtype.val hy
  have hyy : (y.1 : G) ^ 2 = 1 := by simpa only [pow_two, hy'] using (inv_mul_cancel y.1)
  apply hx
  apply isConj_one_left.mp
  simpa only [hyy] using IsConj.pow 2 (show IsConj x y.1 from y.2)

/-- A non-involution in an ah-group uses less than the full 2-part of the group order. -/
theorem two_mul_orderOf_dvd_card {G : Type*} [Group G] [Fintype G]
    (h : HasDistinctConjClassSizes G) {x : G} (hx : x ^ 2 ≠ 1) : 2 * orderOf x ∣ Nat.card G := by
  have h2 := two_dvd_conjClassCard_of_isConj_inv (isConj_inv h x) hx
  let y : Subgroup.centralizer ({x} : Set G) := ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have ho : orderOf x ∣ Nat.card (Subgroup.centralizer ({x} : Set G)) :=
    by
      rw [← show orderOf y = orderOf x from Subgroup.orderOf_mk _ _]
      exact orderOf_dvd_natCard y
  rw [← conjClassCard_mk_mul_card_centralizer x]
  exact Nat.mul_dvd_mul h2 ho

/-- If a Sylow 2-subgroup of an ah-group is cyclic, it has order at most two. -/
theorem card_sylow_two_le_two_of_isCyclic {G : Type*} [Group G] [Fintype G]
    (h : HasDistinctConjClassSizes G) (P : Sylow 2 G) [IsCyclic P] :
    Nat.card P ≤ 2 := by
  obtain ⟨x, hx⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := P)
  have hx' : orderOf (x.1 : G) = Nat.card P := (orderOf_injective P.1.subtype Subtype.val_injective x).trans hx
  by_contra! hlarge
  have hx2 : (x.1 : G) ^ 2 ≠ 1 := by
    intro hh
    exact (Nat.not_dvd_of_pos_of_lt (by decide) (hx' ▸ hlarge)) (orderOf_dvd_of_pow_eq_one hh)
  have hd := two_mul_orderOf_dvd_card h hx2
  rw [hx', ← P.1.index_mul_card] at hd
  exact P.not_dvd_index ((Nat.dvd_of_mul_dvd_mul_right Nat.card_pos hd))

/-- The conjecture holds for a group with a cyclic Sylow 2-subgroup, independently of solvability. -/
theorem nonempty_mulEquiv_perm_three_of_cyclic_sylow_two {G : Type*} [Group G] [Fintype G]
    [Nontrivial G] (h : HasDistinctConjClassSizes G) (P : Sylow 2 G) [IsCyclic P] :
    Nonempty (G ≃* Equiv.Perm (Fin 3)) := by
  have hle := card_sylow_two_le_two_of_isCyclic h P
  have hpos : 0 < Nat.card P := Nat.card_pos
  apply nonempty_mulEquiv_perm_three_of_not_four_dvd h
  intro h4
  rw [← P.1.index_mul_card] at h4
  have hi := P.not_dvd_index
  rcases (show Nat.card P = 1 ∨ Nat.card P = 2 by omega) with h1 | h2
  · rw [show Nat.card P.1 = 1 from h1, mul_one] at h4
    exact hi (dvd_trans (by decide : 2 ∣ 4) h4)
  · rw [show Nat.card P.1 = 2 from h2] at h4
    exact hi (Nat.dvd_of_mul_dvd_mul_right (by decide : 0 < 2) h4)


/-- If the subgroup generated by `x` is Hall in its centralizer, a complement inherits
distinct conjugacy class sizes from the ambient group. -/
theorem exists_ah_complement_in_centralizer {G : Type*} [Group G] [Fintype G]
    (h : HasDistinctConjClassSizes G) {x : G} {m : ℕ}
    (hc : Nat.card (Subgroup.centralizer ({x} : Set G)) = orderOf x * m)
    (hco : (orderOf x).Coprime m) :
    ∃ B : Subgroup (Subgroup.centralizer ({x} : Set G)), Nat.card B = m ∧
      @HasDistinctConjClassSizes B _ (Fintype.ofFinite B) := by
  classical
  let C := Subgroup.centralizer ({x} : Set G)
  let z : C := ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  let Z := Subgroup.zpowers z
  have hZ : Nat.card Z = orderOf x := by rw [Nat.card_zpowers, Subgroup.orderOf_mk]
  have hcent : Z ≤ Subgroup.center C := Subgroup.zpowers_le.mpr (by
    apply Subgroup.mem_center_iff.mpr
    intro c
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp c.2))
  have : Z.Normal := ⟨fun a ha c => by
    have hca := Subgroup.mem_center_iff.mp (hcent ha) c
    rwa [hca, mul_inv_cancel_right]⟩
  have hidx : Z.index = m := Nat.eq_of_mul_eq_mul_left (orderOf_pos x) (by
    rw [← hZ, Z.card_mul_index, hZ]; exact hc)
  obtain ⟨B, hB⟩ := Subgroup.exists_right_complement'_of_coprime
    (N := Z) (by rwa [hZ, hidx])
  have hBm := hB.symm.index_eq_card.symm.trans hidx
  refine ⟨B, hBm, ?_⟩
  let f : Z × B →* C := Z.subtype.noncommCoprod B.subtype
    (fun a b => (Subgroup.mem_center_iff.mp (hcent a.2) b.1).symm)
  exact @hasDistinctConjClassSizes_centralizer_factor G Z B _ _ _ _ (Fintype.ofFinite B) h x
    (MulEquiv.ofBijective f hB)
    (hBm ▸ hco)

/-- In a minimal counterexample, whenever a nonidentity element generates a Hall subgroup
of its centralizer, its index there is one or six. -/
theorem centralizer_hall_index_eq_one_or_six {G : Type} [Group G] [Fintype G] [Group.IsSolvable G]
    (h : HasDistinctConjClassSizes G) (ih : (∀ (K : Type) [Group K] [Fintype K] [Group.IsSolvable K] [Nontrivial K],
        Nat.card K < Nat.card G → ConjugacyClassSizes.HasDistinctConjClassSizes (G := K) →
        Nonempty (K ≃* Equiv.Perm (Fin 3)))) {x : G} (hx : x ≠ 1)
    {m : ℕ} (hc : Nat.card (Subgroup.centralizer ({x} : Set G)) = orderOf x * m)
    (hco : (orderOf x).Coprime m) : m = 1 ∨ m = 6 := by
  obtain ⟨B, hBm, hB⟩ := exists_ah_complement_in_centralizer h hc hco
  classical
  let _ := Fintype.ofFinite B
  by_cases hm : m = 1
  · exact Or.inl hm
  have hmpos : 0 < m := hBm ▸ Nat.card_pos
  have : Nontrivial B := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hox : 1 < orderOf x := by
    have ho := orderOf_pos x
    have hn := mt orderOf_eq_one_iff.mp hx
    omega
  have hlt : Nat.card B < Nat.card G := by
    have hle := (Subgroup.centralizer ({x} : Set G)).card_le_card_group
    rw [hc] at hle
    rw [hBm]
    exact lt_of_lt_of_le (lt_mul_of_one_lt_left hmpos hox) hle
  obtain ⟨e⟩ := ih B hlt hB
  right
  rw [← hBm, Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
  decide


/-- Every element centralized by a Sylow 2-subgroup has order dividing two. -/
theorem sq_eq_one_of_sylow_two_le_centralizer {G : Type*} [Group G] [Fintype G]
    (h : HasDistinctConjClassSizes G) (P : Sylow 2 G) {x : G}
    (hx : P.1 ≤ Subgroup.centralizer ({x} : Set G)) : x ^ 2 = 1 := by
  by_contra hn
  have h2 := two_dvd_conjClassCard_of_isConj_inv (isConj_inv h x) hn
  have hd := Nat.mul_dvd_mul h2 (Subgroup.card_dvd_of_le hx)
  rw [conjClassCard_mk_mul_card_centralizer, ← P.1.index_mul_card] at hd
  exact P.not_dvd_index (Nat.dvd_of_mul_dvd_mul_right Nat.card_pos hd)

/-- In particular, every abelian Sylow 2-subgroup of an ah-group has exponent at most two. -/
theorem sq_eq_one_of_mem_abelian_sylow_two {G : Type*} [Group G] [Fintype G]
    (h : HasDistinctConjClassSizes G) (P : Sylow 2 G) [IsMulCommutative P] (x : P) :
    x ^ 2 = 1 := by
  apply Subtype.ext
  apply sq_eq_one_of_sylow_two_le_centralizer h P
  intro y hy
  exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val (mul_comm' (⟨y,hy⟩ : P) x))


/-- If a prime occurs only once in the order of a minimal counterexample, the centralizer
of an element of that prime order has order either `p` or `6*p`. The second alternative
requires `p` to be coprime to six. -/
theorem card_centralizer_of_prime_order_of_sq_not_dvd {G : Type} [Group G] [Fintype G]
    [Group.IsSolvable G] (h : HasDistinctConjClassSizes G) (ih : (∀ (K : Type) [Group K] [Fintype K] [Group.IsSolvable K] [Nontrivial K],
        Nat.card K < Nat.card G → ConjugacyClassSizes.HasDistinctConjClassSizes (G := K) →
        Nonempty (K ≃* Equiv.Perm (Fin 3))))
    {p : ℕ} (hp : p.Prime) {x : G} (hx : orderOf x = p) (hsq : ¬p ^ 2 ∣ Nat.card G) :
    Nat.card (Subgroup.centralizer ({x} : Set G)) = p ∨
      p.Coprime 6 ∧ Nat.card (Subgroup.centralizer ({x} : Set G)) = p * 6 := by
  let C := Subgroup.centralizer ({x} : Set G)
  let z : C := ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hz : orderOf z = p := (Subgroup.orderOf_mk _ _).trans hx
  obtain ⟨m, hm⟩ := hz ▸ orderOf_dvd_natCard z
  have hco : p.Coprime m := hp.coprime_iff_not_dvd.mpr (by
    intro hd
    apply hsq
    apply dvd_trans _ C.card_subgroup_dvd_card
    rw [hm, pow_two]
    exact Nat.mul_dvd_mul_left p hd)
  have hx1 : x ≠ 1 := by rintro rfl; simp_all [hp.ne_one.symm]
  rcases centralizer_hall_index_eq_one_or_six h ih hx1 (hx ▸ hm) (hx ▸ hco) with rfl | rfl
  · left
    simpa using hm
  · exact Or.inr ⟨hco, hm⟩

/-- In the induction step a cyclic Sylow subgroup of order three is self-centralizing. -/
theorem card_centralizer_eq_three_of_not_nine_dvd {G : Type} [Group G] [Fintype G]
    [Group.IsSolvable G] (h : HasDistinctConjClassSizes G) (ih : (∀ (K : Type) [Group K] [Fintype K] [Group.IsSolvable K] [Nontrivial K],
        Nat.card K < Nat.card G → ConjugacyClassSizes.HasDistinctConjClassSizes (G := K) →
        Nonempty (K ≃* Equiv.Perm (Fin 3))))
    {x : G} (hx : orderOf x = 3) (h9 : ¬9 ∣ Nat.card G) :
    Nat.card (Subgroup.centralizer ({x} : Set G)) = 3 :=
  (card_centralizer_of_prime_order_of_sq_not_dvd h ih Nat.prime_three hx h9).resolve_right
    (fun h => (by decide : ¬Nat.Coprime 3 6) h.1)

end

section

section PrimeMultiplicity

variable {G : Type*} [Group G] [Fintype G]

/-- If an odd-order element maps into a normal cyclic subgroup, its image has
order dividing three. Conjugation induces commuting automorphisms on that subgroup. -/
theorem orderOf_image_dvd_three {Q : Type*} [Group Q]
    (h : HasDistinctConjClassSizes G) (f : G →* Q) (B : Subgroup Q) [B.Normal] [IsCyclic B]
    {x : G} (hx : (2 : ℕ).Coprime (orderOf x)) (hxB : f x ∈ B) :
    orderOf (f x) ∣ 3 := by
  let u : B := ⟨f x, hxB⟩
  let act : G →* MulAut B := MulAut.conjNormal.comp f
  let e := IsCyclic.mulAutMulEquiv B
  let φ := e.toMonoidHom.comp act
  obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_pow_of_coprime h x hx)
  have hgu : act g u = u ^ 2 := by
    apply Subtype.ext
    change f g * f x * (f g)⁻¹ = (f x) ^ 2
    simpa using congrArg f hg
  obtain ⟨t, ht⟩ := isConj_iff.mp (isConj_inv h g)
  have hr : φ g = (φ g)⁻¹ := by
    simpa [mul_comm] using congrArg φ ht
  have ha : act g * act g = 1 := by
    apply e.injective
    change e (act g * act g) = e 1
    rw [map_mul, map_one]
    change φ g * φ g = 1
    nth_rw 2 [hr]
    exact mul_inv_cancel _
  have h4 : u ^ 2 * u ^ 2 = u := by
    have ht' : (act g * act g) u = u := by rw [ha]; rfl
    rw [MulAut.mul_apply, hgu, map_pow, hgu, pow_two (u ^ 2)] at ht'
    exact ht'
  have h3 : u ^ 3 = 1 := by
    have he : u ^ 3 * u = 1 * u := by
      simpa only [← pow_succ, ← pow_add, one_mul] using h4
    exact mul_right_cancel he
  exact orderOf_dvd_of_pow_eq_one (congrArg Subtype.val h3)

/-- A prime at least five dividing the order of a solvable ah-group occurs at least twice. -/
theorem prime_sq_dvd_card_of_five_le [Group.IsSolvable G] (h : HasDistinctConjClassSizes G)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hd : p ∣ Nat.card G) : p ^ 2 ∣ Nat.card G := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  by_contra hsq
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := G) p (by simpa only [← Nat.card_eq_fintype_card] using hd)
  have hx1 : x ≠ 1 := fun hh => hp.ne_one (by simpa only [hh, orderOf_one] using hx.symm)
  apply not_isSolvable_of_mem_derivedSeries hx1 _ inferInstance
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    let D := derivedSeries G i
    let K := derivedSeries G (i+1)
    let f := QuotientGroup.mk' K
    let A := D.map f
    have : A.Normal := (derivedSeries_normal G i).map f (QuotientGroup.mk'_surjective K)
    have : IsMulCommutative A := by
      apply Subgroup.commutator_self_eq_bot_iff.mp
      change ⁅D.map f, D.map f⁆ = ⊥
      rw [← Subgroup.map_commutator, Subgroup.map_eq_bot_iff]
      exact le_of_eq (by rw [QuotientGroup.ker_mk']; rfl)
    let u : A := ⟨f x, ⟨x, ih, rfl⟩⟩
    by_contra hn
    have hfx : f x ≠ 1 := fun he => hn ((QuotientGroup.eq_one_iff x).mp he)
    have hu : orderOf (f x) = p := (hp.eq_one_or_self_of_dvd _
      (hx ▸ orderOf_map_dvd f x)).resolve_left (fun he => hfx (orderOf_eq_one_iff.mp he))
    have hu' : orderOf u = p := (Subgroup.orderOf_coe u).symm.trans hu
    have hpg : IsPGroup p (Subgroup.zpowers u) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu', pow_one])
    obtain ⟨P, hP⟩ := hpg.exists_le_sylow
    let : (P : Subgroup A).Characteristic := P.characteristic_of_normal (Subgroup.normal_of_isMulCommutative _)
    let B := (P : Subgroup A).map A.subtype
    have hPcard : Nat.card (P : Subgroup A) = p := by
      obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
      have hk2 : ¬ 2 ≤ k := fun hge => hsq <| (Nat.pow_dvd_pow p hge).trans <| hk ▸
        ((P : Subgroup A).card_subgroup_dvd_card.trans <| A.card_subgroup_dvd_card.trans
          K.card_quotient_dvd_card)
      have huP : p ∣ Nat.card (P : Subgroup A) := by
        simpa only [Nat.card_zpowers, hu'] using Subgroup.card_dvd_of_le hP
      rcases k with _ | k
      · rw [hk, pow_zero, Nat.dvd_one] at huP
        exact (hp.ne_one huP).elim
      · have : k = 0 := by omega
        simpa [this] using hk
    have : IsCyclic B := isCyclic_of_card_dvd_prime (p := p) (by
      rw [show Nat.card B = _ from Subgroup.card_map_of_injective A.subtype_injective, hPcard])
    have hodd : (2 : ℕ).Coprime p := (hp.coprime_iff_not_dvd.mpr
      (fun hh => by have := Nat.le_of_dvd (by decide : 0 < 2) hh; omega)).symm
    have hm := orderOf_image_dvd_three h f B (hx ▸ hodd) (show f x ∈ B from
      ⟨u, hP (Subgroup.mem_zpowers u), rfl⟩)
    rw [hu] at hm
    have := Nat.le_of_dvd (by decide : 0 < 3) hm
    omega

/-- An element whose centralizer has prime order lies in a Sylow subgroup of that order. -/
theorem exists_sylow_card_of_prime_centralizer {p : ℕ} (hp : p.Prime) {g : G}
    (hg : g ≠ 1) (hc : Nat.card (Subgroup.centralizer ({g} : Set G)) = p) :
    ∃ P : Sylow p G, Nat.card (P : Subgroup G) = p := by
  let : Fact p.Prime := ⟨hp⟩
  let C := Subgroup.centralizer ({g} : Set G)
  have hgC : g ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have generated {y : G} (hy : y ∈ C) (hne : y ≠ 1) : Subgroup.zpowers y = C := by
    have hle := Subgroup.zpowers_le.mpr hy
    have hord : orderOf y = p := (hp.eq_one_or_self_of_dvd _
      (by simpa only [Nat.card_zpowers, C, hc] using Subgroup.card_dvd_of_le hle)).resolve_left
        (fun h1 => hne (orderOf_eq_one_iff.mp h1))
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, hord]; exact hc.le)
  have hC : IsPGroup p C := IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hc)
  obtain ⟨P, hP⟩ := hC.exists_le_sylow
  have hgP := hP hgC
  have : Nontrivial (P : Subgroup G) :=
    ⟨⟨⟨g, hgP⟩, 1, fun he => hg (congrArg Subtype.val he)⟩⟩
  have : Nontrivial (Subgroup.center (P : Subgroup G)) := P.isPGroup'.center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center (P : Subgroup G))
  have hzc : ∀ t ∈ (P : Subgroup G), t * (z : G) = (z : G) * t := by
    intro t ht
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨t, ht⟩)
  have heq := generated (Subgroup.mem_centralizer_singleton_iff.mpr (hzc g hgP).symm)
    (fun he => hz (Subtype.ext (Subtype.ext he)))
  have hPle : (P : Subgroup G) ≤ C := by
    intro t ht
    have hgZ : g ∈ Subgroup.zpowers (z : G) := heq ▸ hgC
    obtain ⟨k, hk⟩ := hgZ
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (hk ▸ (show Commute t (z : G) from hzc t ht).zpow_right k)
  exact ⟨P, (congrArg (fun S : Subgroup G => Nat.card S) (le_antisymm hPle hP)).trans hc⟩

/-- No prime at least five can occur as a centralizer order in a solvable ah-group. -/
theorem card_centralizer_ne_prime_of_five_le [Group.IsSolvable G]
    (h : HasDistinctConjClassSizes G) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (g : G) :
    Nat.card (Subgroup.centralizer ({g} : Set G)) ≠ p := by
  intro hc
  let : Fact p.Prime := ⟨hp⟩
  have hdiv : p ∣ Nat.card G := hc ▸ (Subgroup.centralizer ({g} : Set G)).card_subgroup_dvd_card
  have hs := prime_sq_dvd_card_of_five_le h hp hp5 hdiv
  have hnd : ¬ p ^ 2 ∣ p := fun hh => by
    have := Nat.le_of_dvd hp.pos hh
    nlinarith
  by_cases hg : g = 1
  · subst g
    have ht : Subgroup.centralizer ({1} : Set G) = ⊤ := by
      rw [Subgroup.centralizer_eq_top_iff_subset]; simp
    rw [ht, Subgroup.card_top] at hc
    exact hnd (hc ▸ hs)
  · obtain ⟨P, hP⟩ := exists_sylow_card_of_prime_centralizer hp hg hc
    have hbig : p ^ 2 ∣ Nat.card (P : Subgroup G) := P.pow_dvd_card_of_pow_dvd_card hs
    rw [hP] at hbig
    exact hnd hbig

end PrimeMultiplicity

end

section

/-- A group of order six in which an element of order three is real acts faithfully
on three cosets and is the full symmetric group on them. -/
theorem nonempty_mulEquiv_perm_three_of_card_six_of_real_three {Q : Type*} [Group Q] [Finite Q]
    (hQ : Nat.card Q = 6) {z : Q} (hz : orderOf z = 3) (hr : IsConj z z⁻¹) :
    Nonempty (Q ≃* Equiv.Perm (Fin 3)) := by
  classical
  let := Fintype.ofFinite Q
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card (G := Q) 2 (by
    rw [← Nat.card_eq_fintype_card, hQ]; decide)
  let H := Subgroup.zpowers t
  have hH : Nat.card H = 2 := (Nat.card_zpowers t).trans ht
  have hcos : Nat.card (Q ⧸ H) = 3 := by
    have h := H.card_eq_card_quotient_mul_card_subgroup
    rw [hQ, hH] at h
    omega
  let f := MulAction.toPermHom Q (Q ⧸ H)
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.normalCore_eq_ker]
    by_contra hne
    have hdiv : Nat.card H.normalCore ∣ 2 := hH ▸ Subgroup.card_dvd_of_le H.normalCore_le
    have hcard : Nat.card H.normalCore = 2 := (Nat.dvd_prime Nat.prime_two).mp hdiv |>.resolve_left
      (fun h1 => hne (Subgroup.card_eq_one.mp h1))
    have heq : H.normalCore = H := Subgroup.eq_of_le_of_card_ge H.normalCore_le (by omega)
    have : H.Normal := heq ▸ H.normalCore_normal
    let q := QuotientGroup.mk' H
    have : IsCyclic (Q ⧸ H) := isCyclic_of_card_dvd_prime (p := 3) (by rw [hcos])
    let := IsCyclic.commGroup (α := Q ⧸ H)
    obtain ⟨c, hc⟩ := isConj_iff.mp hr
    have hreal : q z = (q z)⁻¹ := by simpa [mul_comm] using congrArg q hc
    have h2 : (q z) ^ 2 = 1 := by rw [pow_two]; nth_rw 2 [hreal]; exact mul_inv_cancel _
    have h3 : orderOf (q z) ∣ 3 := hz ▸ orderOf_map_dvd q z
    have h1 : orderOf (q z) = 1 := by
      have hh := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) h3
      exact Nat.dvd_one.mp (show orderOf (q z) ∣ 1 from hh)
    have hzH := (QuotientGroup.eq_one_iff z).mp (orderOf_eq_one_iff.mp h1)
    have hd := orderOf_dvd_natCard (⟨z, hzH⟩ : H)
    rw [← Subgroup.orderOf_coe, hH] at hd
    exact (by decide : ¬ 3 ∣ 2) (hz ▸ hd)
  have hbij : Function.Bijective f := by
    apply hinj.bijective_of_nat_card_le
    rw [Nat.card_perm, hcos, hQ]; decide
  exact ⟨(MulEquiv.ofBijective f hbij).trans (Finite.equivFinOfCardEq hcos).permCongrHom⟩

end

section

/-- In a nontrivial solvable real group a Sylow 2-subgroup cannot be contained in the derived
group. Otherwise the nontrivial real abelianization would have odd order. -/
private theorem sylow_two_not_le_commutator {G : Type*} [Group G] [Fintype G]
    [Group.IsSolvable G] [Nontrivial G] (h : HasDistinctConjClassSizes G) (P : Sylow 2 G) :
    ¬ (P : Subgroup G) ≤ commutator G := by
  intro hle
  have : Nontrivial (G ⧸ commutator G) := by
    by_contra hn
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial G).ne
      (QuotientGroup.subgroup_eq_top_of_subsingleton _ (not_nontrivial_iff_subsingleton.mp hn))
  have hd : 2 ∣ Nat.card (G ⧸ commutator G) := by
    apply two_dvd_card_of_all_real
    intro q
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (commutator G) q
    simpa only [map_inv] using (QuotientGroup.mk' (commutator G)).map_isConj (isConj_inv h z)
  exact P.not_dvd_index (hd.trans (Subgroup.index_dvd_of_le hle))

/-- For a Sylow 2-subgroup of order four in a nontrivial solvable ah-group the normalizer
centralizes the Sylow subgroup. Its intersection with the derived subgroup has at most two
elements, so conjugation fixes this intersection and its square fixes the Sylow subgroup.
The normalizer has odd relative index over the abelian Sylow subgroup. -/
theorem normalizer_le_centralizer_of_sylow_card_four {G : Type*} [Group G] [Fintype G]
    [Group.IsSolvable G] [Nontrivial G] (h : HasDistinctConjClassSizes G)
    (P : Sylow 2 G) (hP : Nat.card P = 4) :
    Subgroup.normalizer (P : Set G) ≤ Subgroup.centralizer (P : Set G) := by
  classical
  let R := (P : Subgroup G) ⊓ commutator G
  have hr : R ≤ (P : Subgroup G) := inf_le_left
  have hrlt : Nat.card R < 4 := by
    by_contra! hge
    have he := Subgroup.eq_of_le_of_card_ge hr (hP.trans_le hge)
    exact sylow_two_not_le_commutator h P (he ▸ (inf_le_right : R ≤ commutator G))
  have hr12 : Nat.card R = 1 ∨ Nat.card R = 2 := by
    have hd : Nat.card R ∣ 4 := (Subgroup.card_dvd_of_le hr).trans hP.dvd
    have hpos : 0 < Nat.card R := Nat.card_pos
    have hn := Nat.dvd_prime_pow Nat.prime_two (m := 2) (i := Nat.card R)
    obtain ⟨k, hk, h⟩ := hn.mp hd
    interval_cases k <;> simp_all
  intro g hg
  let C := Subgroup.centralizer (P : Set G)
  have hmc : IsMulCommutative P := IsPGroup.isMulCommutative_of_card_eq_prime_sq
    (p := 2) (by simpa using hP)
  have hpc : (P : Subgroup G) ≤ C := Subgroup.le_centralizer _
  have hnorm : ∀ z ∈ R, g * z * g⁻¹ ∈ R := by
    intro z hz
    exact ⟨(Subgroup.mem_normalizer_iff.mp hg _).mp hz.1,
      (inferInstance : (commutator G).Normal).conj_mem z hz.2 g⟩
  have hfix (z : G) (hz : z ∈ R) : g * z * g⁻¹ = z := by
    by_cases hz1 : z = 1
    · simp [hz1]
    rcases hr12 with hbot | htwo
    · exact False.elim (hz1 (by simpa [Subgroup.card_eq_one.mp hbot] using hz))
    refine (eq_one_or_eq_of_mem_of_card_eq_two htwo hz hz1 (hnorm z hz)).resolve_left ?_
    intro hc
    apply hz1
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
         _ = 1 := by rw [hc]; group
  have hsq (z : G) (hz : z ∈ R) : z * z = 1 := by
    rcases hr12 with hbot | htwo
    · have h1 : z = 1 := by simpa [Subgroup.card_eq_one.mp hbot] using hz
      simp [h1]
    · have hpow := pow_card_eq_one' (x := (⟨z,hz⟩ : R))
      rw [htwo, pow_two] at hpow
      exact congrArg Subtype.val hpow
  have h2 : g ^ 2 ∈ C := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro x hx
    let d := g * x * g⁻¹ * x⁻¹
    have hd : d ∈ R := ⟨P.mul_mem ((Subgroup.mem_normalizer_iff.mp hg _).mp hx) (P.inv_mem hx),
      Subgroup.commutator_mem_commutator (H₁ := ⊤) (H₂ := ⊤) (Subgroup.mem_top _) (Subgroup.mem_top _)⟩
    have hact : g * x * g⁻¹ = d * x := by dsimp [d]; group
    have hc : g ^ 2 * x * (g ^ 2)⁻¹ = x := by
      calc
        _ = g * (g * x * g⁻¹) * g⁻¹ := by rw [pow_two]; group
        _ = (g * d * g⁻¹) * (g * x * g⁻¹) := by nth_rw 1 [hact]; group
        _ = d * (d * x) := by rw [hfix _ hd, hact]
        _ = x := by rw [← mul_assoc, hsq _ hd, one_mul]
    exact (mul_inv_eq_iff_eq_mul.mp hc).symm
  let M := Subgroup.normalizer (P : Set G)
  let j := (P : Subgroup G).relIndex M
  have hj : Odd j := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp
    (fun hd => P.not_dvd_index (hd.trans (Subgroup.relIndex_dvd_index_of_le P.le_normalizer))))
  have : ((P : Subgroup G).subgroupOf M).Normal := (P : Subgroup G).normal_in_normalizer
  have hjmem : g ^ j ∈ C := hpc (((P : Subgroup G).subgroupOf M).pow_index_mem (⟨g,hg⟩ : M))
  obtain ⟨k, hk⟩ := hj
  rw [hk, pow_succ, pow_mul] at hjmem
  exact (C.mul_mem_cancel_left (C.pow_mem h2 k)).mp hjmem

end

section

section Klein
variable {G : Type*} [Group G] [Fintype G]

private theorem four_elem_basis {T : Type*} [Group T] [Finite T] (hT : Nat.card T = 4)
    (hsq : ∀ a : T, a ^ 2 = 1) {t : T} (ht : t ≠ 1) :
    ∃ s : T, ∀ a : T, a = 1 ∨ a = t ∨ a = s ∨ a = s * t := by
  classical
  let _ := Fintype.ofFinite T
  have hsize : Fintype.card T = 4 := Nat.card_eq_fintype_card.symm.trans hT
  obtain ⟨s, hs⟩ : ∃ s : T, s ∉ ({1,t} : Finset T) := by
    by_contra! h
    have : ({1,t} : Finset T) = Finset.univ := Finset.eq_univ_iff_forall.mpr h
    have hh := congrArg Finset.card this
    simp [ht.symm, hsize] at hh
  have hs1 : s ≠ 1 := fun e => hs (by simp [e])
  have hst : s ≠ t := fun e => hs (by simp [e])
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hsq t)
  have hprod1 : s * t ≠ 1 := fun e => hst ((eq_inv_of_mul_eq_one_left e).trans htinv)
  have hprodt : s * t ≠ t := fun e => hs1 (mul_eq_right.mp e)
  have hprods : s * t ≠ s := fun e => ht (mul_eq_left.mp e)
  have huniv : ({1,t,s,s*t} : Finset T) = Finset.univ := by
    apply Finset.eq_univ_of_card
    simp [hsize, ht.symm, hs1.symm, hst.symm, hprod1.symm, hprodt.symm, hprods.symm]
  refine ⟨s, fun a => ?_⟩
  have hh : a ∈ ({1,t,s,s*t} : Finset T) := huniv ▸ Finset.mem_univ a
  simpa using hh

omit [Fintype G] in
private theorem split_subgroup_card {P K H : Subgroup G} (hs : K.IsComplement' P)
    (hp : P ≤ H) : Nat.card H = Nat.card ↥(K ⊓ H) * Nat.card P := by
  let f (v : ↥(K ⊓ H) × P) : H := ⟨v.1.1 * v.2.1, H.mul_mem v.1.2.2 (hp v.2.2)⟩
  have hsur : Function.Surjective f := by
    rintro ⟨c,hc⟩
    obtain ⟨⟨k,p⟩,hkp⟩ := hs.2 c
    change k.1 * p.1 = c at hkp
    have hkH : (k : G) ∈ H := (H.mul_mem_cancel_right (hp p.2)).mp (by rw [hkp]; exact hc)
    exact ⟨(⟨k.1, k.2, hkH⟩,p), Subtype.ext hkp⟩
  have hinj : Function.Injective f := by
    rintro ⟨a,p⟩ ⟨b,q⟩ he
    have he' : ((⟨a.1,a.2.1⟩ : K),p) = ((⟨b.1,b.2.1⟩ : K),q) := hs.1 (congrArg Subtype.val he)
    exact Prod.ext (Subtype.ext (congrArg (fun v : K × P => v.1.1) he')) (congrArg (fun v : K × P => v.2) he')
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hinj,hsur⟩), Nat.card_prod]

omit [Fintype G] in
private theorem one_of_sq_of_mem_odd {K : Subgroup G} (ho : ¬2 ∣ Nat.card K)
    {d : G} (hd : d ∈ K) (hs : d ^ 2 = 1) : d = 1 := by
  have he := (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hs)
  apply orderOf_eq_one_iff.mp
  exact he.resolve_right (fun h2 => ho (h2 ▸ (Subgroup.orderOf_mk _ hd) ▸
    orderOf_dvd_natCard (⟨d,hd⟩ : K)))

private theorem centralizer_kernel_card_cases (h : HasDistinctConjClassSizes G) (P : Sylow 2 G)
    (hP : Nat.card P = 4) (K : Subgroup G) [K.Normal] (hs : K.IsComplement' P.1)
    {t : P} (ht : t ≠ 1) :
    Nat.card ↥(K ⊓ Subgroup.centralizer ({(t : G)} : Set G)) = 1 ∨
    Nat.card ↥(K ⊓ Subgroup.centralizer ({(t : G)} : Set G)) = 3 := by
  classical
  have : IsMulCommutative P := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hP
  have hsq := sq_eq_one_of_mem_abelian_sylow_two h P
  obtain ⟨s, hbasis⟩ := four_elem_basis hP hsq ht
  let C := Subgroup.centralizer ({(t : G)} : Set G)
  let D := K ⊓ C
  have ho : ¬2 ∣ Nat.card K := hs.index_eq_card ▸ P.not_dvd_index
  have hPcom (a b : P) : Commute (a.1 : G) b.1 := congrArg Subtype.val (mul_comm' a b)
  have hPle : P.1 ≤ C := fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr
    (hPcom ⟨a,ha⟩ t)
  have hs2 : (s.1 : G) * s.1 = 1 := congrArg Subtype.val (show s*s = 1 by simpa [pow_two] using hsq s)
  have hsinv : (s.1 : G)⁻¹ = s.1 := inv_eq_of_mul_eq_one_left hs2
  let f : D →* D :=
    { toFun := fun d => ⟨s.1 * d.1 * s.1⁻¹, (inferInstance : K.Normal).conj_mem _ d.2.1 _,
        C.mul_mem (C.mul_mem (hPle s.2) d.2.2) (C.inv_mem (hPle s.2))⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by change _ * (_ * _) * _ = (_ * _ * _) * (_ * _ * _); group) }
  have hf (d : D) : (f d).1 = s.1 * d.1 * s.1⁻¹ := rfl
  have hinv : Function.Involutive f := fun d => Subtype.ext (by
    rw [hf, hf, hsinv]
    calc _ = (s.1 * s.1) * d.1 * (s.1 * s.1) := by group
         _ = d.1 := by simp [hs2])
  have hfpf : MonoidHom.FixedPointFree f := by
    intro d hd
    have hsd : Commute s.1 d.1 := mul_inv_eq_iff_eq_mul.mp ((hf d).symm.trans (congrArg Subtype.val hd))
    have htd : Commute t.1 d.1 := (Subgroup.mem_centralizer_singleton_iff.mp d.2.2).symm
    apply Subtype.ext
    apply one_of_sq_of_mem_odd ho d.2.1
    apply sq_eq_one_of_sylow_two_le_centralizer h P
    intro p hp
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases hbasis ⟨p,hp⟩ with h1 | h1 | h1 | h1
    · have := congrArg Subtype.val h1
      simp [show p = 1 from this]
    · rw [show p = t.1 from congrArg Subtype.val h1]; exact htd
    · rw [show p = s.1 from congrArg Subtype.val h1]; exact hsd
    · rw [show p = s.1 * t.1 from congrArg Subtype.val h1]; exact hsd.mul_left htd
  have hdinv (d : D) : s.1 * d.1 * s.1⁻¹ = d.1⁻¹ := by
    exact congrArg Subtype.val (congrFun (MonoidHom.FixedPointFree.coe_eq_inv_of_involutive hfpf hinv) d)
  have hdc (a b : D) : Commute a.1 b.1 := congrArg Subtype.val
    (MonoidHom.FixedPointFree.commute_all_of_involutive hfpf hinv a b).eq
  have hconj (c : C) : (∀ d : D, c.1 * d.1 * c.1⁻¹ = d.1) ∨
      (∀ d : D, c.1 * d.1 * c.1⁻¹ = d.1⁻¹) := by
    obtain ⟨⟨k,p⟩,hkp⟩ := hs.2 c.1
    change k.1 * p.1 = c.1 at hkp
    have hkC : k.1 ∈ C := (C.mul_mem_cancel_right (hPle p.2)).mp (by rw [hkp]; exact c.2)
    let a : D := ⟨k.1, k.2, hkC⟩
    have hkc (d : D) : k.1 * d.1 * k.1⁻¹ = d.1 := mul_inv_eq_iff_eq_mul.mpr (hdc a d)
    have hkc' (d : D) : k.1 * d.1⁻¹ * k.1⁻¹ = d.1⁻¹ := hkc d⁻¹
    have htc (d : D) : t.1 * d.1 * t.1⁻¹ = d.1 := by
      rw [(Subgroup.mem_centralizer_singleton_iff.mp d.2.2).symm]; simp
    have kg (d : D) : c.1 * d.1 * c.1⁻¹ = k.1 * (p.1 * d.1 * p.1⁻¹) * k.1⁻¹ := by rw [← hkp]; group
    rcases hbasis p with rfl | rfl | rfl | rfl
    · left; intro d; simpa [kg] using hkc d
    · left; intro d; rw [kg, htc, hkc]
    · right; intro d; rw [kg, hdinv, hkc']
    · right; intro d
      rw [kg]
      have hst : (s * t).1 * d.1 * (s * t).1⁻¹ = s.1 * (t.1 * d.1 * t.1⁻¹) * s.1⁻¹ := by
        change (s.1 * t.1) * _ * (s.1 * t.1)⁻¹ = _; group
      rw [hst, htc, hdinv, hkc']
  have hneinv {d : D} (hd : d ≠ 1) : d.1 ≠ d.1⁻¹ := by
    intro he
    apply hd
    apply Subtype.ext
    apply one_of_sq_of_mem_odd ho d.2.1
    rw [pow_two]
    simpa only [← he] using mul_inv_cancel d.1
  let i (d : D) : C := ⟨d.1, d.2.2⟩
  have hfun {a b : D} (ha : a ≠ 1) (hb : b ≠ 1) :
      Subgroup.centralizer ({i a} : Set C) ≤ Subgroup.centralizer {i b} := by
    intro c hc
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    apply mul_inv_eq_iff_eq_mul.mp
    rcases hconj c with hfix | hinvert
    · exact hfix b
    · exfalso
      have hca : c.1 * a.1 = a.1 * c.1 :=
        congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hc)
      exact hneinv ha ((mul_inv_eq_iff_eq_mul.mpr hca).symm.trans (hinvert a))
  have horder (d : D) : (orderOf (t : G)).Coprime (orderOf (i d)) := by
    have ht2 : (t.1 : G) ^ 2 = 1 := congrArg Subtype.val (hsq t)
    apply Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one ht2)
    apply Nat.prime_two.coprime_iff_not_dvd.mpr
    intro he
    apply ho
    rw [show orderOf (i d) = orderOf d.1 from Subgroup.orderOf_mk ..] at he
    exact he.trans ((Subgroup.orderOf_coe (⟨d.1,d.2.1⟩ : K)) ▸ orderOf_dvd_natCard (⟨d.1,d.2.1⟩ : K))
  by_cases htr : Subsingleton D
  · left; exact Nat.card_eq_one_iff_unique.mpr ⟨htr, inferInstance⟩
  have : Nontrivial D := not_subsingleton_iff_nontrivial.mp htr
  obtain ⟨a,ha⟩ := exists_ne (1 : D)
  have hal (d : D) : d = 1 ∨ d = a ∨ d = a⁻¹ := by
    by_cases hd : d = 1
    · exact Or.inl hd
    have he := le_antisymm (hfun ha hd) (hfun hd ha)
    obtain ⟨c,hc⟩ := isConj_iff.mp (isConj_in_centralizer_of_coprime h (horder a) (horder d)
      (congrArg Nat.card (congrArg (fun H : Subgroup C => ↥H) he)))
    have hc' : c.1 * a.1 * c.1⁻¹ = d.1 := congrArg Subtype.val hc
    rcases hconj c with hfix | hinv
    · exact Or.inr (Or.inl (Subtype.ext (hc'.symm.trans (hfix a))))
    · exact Or.inr (Or.inr (Subtype.ext (hc'.symm.trans (hinv a))))
  right
  change Nat.card D = 3
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ,
    show (Finset.univ : Finset D) = {1,a,a⁻¹} by ext d; simpa using hal d]
  have hai : a ≠ a⁻¹ := fun hh => hneinv ha (congrArg Subtype.val hh)
  simp [ha.symm, hai, ha]

/-- A normal odd-order complement to a Sylow subgroup of order four is incompatible with
distinct conjugacy class sizes. -/
theorem false_of_sylow_card_four_of_odd_complement (h : HasDistinctConjClassSizes G)
    (P : Sylow 2 G) (hP : Nat.card P = 4) (K : Subgroup G) [K.Normal] (hs : K.IsComplement' P.1) :
    False := by
  classical
  have : IsMulCommutative P := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hP
  let f (t : P) := Nat.card (Subgroup.centralizer ({(t : G)} : Set G))
  have hinj : Function.Injective f := by
    intro t u he
    obtain ⟨c,hc⟩ := isConj_iff.mp (isConj_of_card_centralizer_eq h he)
    let e := hs.symm.QuotientMulEquiv
    let π := e.toMonoidHom.comp (QuotientGroup.mk' K)
    have hπ (t : P) : π t.1 = t := e.apply_symm_apply t
    have heq := congrArg π hc
    simp only [map_mul, map_inv, hπ] at heq
    rwa [mul_comm' (π c) t, mul_inv_cancel_right] at heq
  let T := (Finset.univ : Finset P).erase 1
  have hsub : T.image f ⊆ ({4,12} : Finset ℕ) := by
    intro n hn
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hn
    have ht1 := (Finset.mem_erase.mp ht).1
    have hle : P.1 ≤ Subgroup.centralizer ({(t : G)} : Set G) := fun p hp =>
      Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val (mul_comm' (⟨p,hp⟩ : P) t))
    have hc := split_subgroup_card hs hle
    change Nat.card (Subgroup.centralizer ({(t : G)} : Set G)) ∈ _
    rw [hc, hP]
    rcases centralizer_kernel_card_cases h P hP K hs ht1 with h1 | h3
    · rw [h1]; decide
    · rw [h3]; decide
  have he := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj, Finset.card_erase_of_mem (Finset.mem_univ 1),
    Finset.card_univ, ← Nat.card_eq_fintype_card] at he
  change Nat.card P.1 - 1 ≤ _ at he
  rw [hP] at he
  simp at he


/-- A finite nontrivial solvable ah-group has no Sylow 2-subgroup of order four. -/
theorem card_sylow_two_ne_four [Group.IsSolvable G] [Nontrivial G]
    (h : HasDistinctConjClassSizes G) (P : Sylow 2 G) : Nat.card P ≠ 4 := by
  intro hP
  have hN := normalizer_le_centralizer_of_sylow_card_four h P hP
  exact false_of_sylow_card_four_of_odd_complement h P hP _
    (MonoidHom.ker_transferSylow_isComplement' P hN)

/-- The conjecture holds whenever eight does not divide the group order. -/
theorem nonempty_mulEquiv_perm_three_of_not_eight_dvd [Group.IsSolvable G] [Nontrivial G]
    (h : HasDistinctConjClassSizes G) (h8 : ¬8 ∣ Nat.card G) :
    Nonempty (G ≃* Equiv.Perm (Fin 3)) := by
  apply nonempty_mulEquiv_perm_three_of_not_four_dvd h
  intro h4
  let P : Sylow 2 G := Classical.arbitrary _
  obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
  have hlo : 2 ≤ k :=
    (Nat.pow_dvd_pow_iff_le_right (by decide : 1 < 2)).mp (hk ▸ P.pow_dvd_card_of_pow_dvd_card
      (n := 2) h4)
  have hhi : k < 3 := by
    by_contra! hh
    apply h8
    exact dvd_trans (show 2 ^ 3 ∣ Nat.card P by rw [hk]; exact pow_dvd_pow _ hh)
      P.1.card_subgroup_dvd_card
  exact card_sylow_two_ne_four h P (by rw [hk, show k = 2 by omega]; decide)

end Klein

end

section

private theorem central_prime_order_in_pi {ι : Type*} {M : ι → Type*} [∀ j, Group (M j)]
    (i : ι) {p : ℕ} (x : M i) (hx : x ∈ Subgroup.center (M i)) (ho : orderOf x = p) :
    ∃ y ∈ Subgroup.center (∀ j, M j), orderOf y = p := by
  classical
  let f := MonoidHom.mulSingle M i
  refine ⟨f x, ?_, (orderOf_injective f (fun _ _ e => ?_) x).trans ho⟩
  · apply Subgroup.mem_center_iff.mpr
    intro g
    ext j
    by_cases he : i = j
    · subst j
      simpa [f] using Subgroup.mem_center_iff.mp hx (g i)
    · simp [f, Pi.mulSingle_eq_of_ne (Ne.symm he), Pi.mul_apply]
  · simpa [f] using congrFun e i

/-- Each prime divisor of a finite nilpotent group occurs as the order of a central element. -/
theorem exists_prime_order_in_center_of_nilpotent {K : Type*} [Group K] [Finite K]
    [Group.IsNilpotent K] (p : ℕ) [hp : Fact p.Prime] (hd : p ∣ Nat.card K) :
    ∃ z ∈ Subgroup.center K, orderOf z = p := by
  classical
  let i : (Nat.card K).primeFactors := ⟨p, Nat.mem_primeFactors.mpr ⟨hp.out, hd, Nat.card_pos.ne'⟩⟩
  let P : Sylow (i : ℕ) K := default
  have hn : Nontrivial P := P.1.nontrivial_iff_ne_bot.mpr (P.ne_bot_of_dvd_card hd)
  have hz := P.isPGroup'.center_nontrivial
  have hpZ := P.isPGroup'.to_subgroup (Subgroup.center P)
  obtain ⟨n, hn, hcard⟩ := hpZ.nontrivial_iff_card.mp hz
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p (hcard ▸ dvd_pow_self p hn.ne')
  obtain ⟨z', hc', ho'⟩ := central_prime_order_in_pi (M := fun (S : Sylow (i : ℕ) K) => ↥S)
    P (z : P) z.2 ((Subgroup.orderOf_coe z).trans hz)
  obtain ⟨w, hw, hwo⟩ := central_prime_order_in_pi
    (M := fun (k : (Nat.card K).primeFactors) => (∀ S : Sylow (k : ℕ) K, ↥S))
    i z' hc' ho'
  obtain ⟨e⟩ := (Group.isNilpotent_of_finite_tfae (G := K)).out 0 4 (by rfl) (by rfl)
    |>.mp ‹Group.IsNilpotent K›
  refine ⟨e w, ?_, (orderOf_injective e.toMonoidHom e.injective w).trans hwo⟩
  apply Subgroup.mem_center_iff.mpr
  intro y
  obtain ⟨v, rfl⟩ := e.surjective y
  simpa only [map_mul] using congrArg e (Subgroup.mem_center_iff.mp hw v)

/-- In an ah-group, a nilpotent derived subgroup must be a 3-group. -/
theorem isThreeGroup_commutator_of_nilpotent {G : Type*} [Group G] [Fintype G]
    [Group.IsNilpotent (commutator G)] (h : HasDistinctConjClassSizes G) :
    IsPGroup 3 (commutator G) := by
  let D := commutator G
  let C := Subgroup.centralizer (D : Set G)
  have hc : IsMulCommutative C := by
    have hh := commutator_centralizer_commutator_le_center G
    rw [trivial_center_of_hasDistinctConjClassSizes h] at hh
    exact Subgroup.le_centralizer_iff_isMulCommutative.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (le_bot_iff.mp hh))
  have hprime (p : ℕ) (hp : p.Prime) (hd : p ∣ Nat.card D) : p = 3 := by
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨z, hz, ho⟩ := exists_prime_order_in_center_of_nilpotent p hd
    have hzC : (z : G) ∈ C := by
      apply Subgroup.mem_centralizer_iff.mpr
      intro x hx
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz (⟨x, hx⟩ : D))
    have h3 := cube_eq_one_of_derived_centralizes h C (Subgroup.le_centralizer_iff.mpr le_rfl)
      ⟨z, hzC⟩
    have hdvd := orderOf_dvd_of_pow_eq_one h3
    simpa only [Subgroup.orderOf_mk, Subgroup.orderOf_coe, ho, Nat.prime_dvd_prime_iff_eq hp
      Nat.prime_three] using hdvd
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 3 D))
  have hi : P.index = 1 := by
    by_contra he
    obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd he
    have eqp := hprime p hp (hd.trans P.1.index_dvd_card)
    exact P.not_dvd_index (eqp ▸ hd)
  have htop : (P : Subgroup D) = ⊤ := Subgroup.index_eq_one.mp hi
  exact (P.isPGroup'.of_surjective P.1.subtype (by
    intro x; exact ⟨⟨x, htop ▸ Subgroup.mem_top x⟩, rfl⟩))

section Count
open Finset

variable {G : Type*} [Group G] [Fintype G]

private theorem sum_class_sizes_le_sigma (h : HasDistinctConjClassSizes G)
    (s : Finset (ConjClasses G)) (n : ℕ) (hn : n ≠ 0)
    (hd : ∀ c ∈ s, conjClassCard c ∣ n) :
    ∑ c ∈ s, conjClassCard c ≤ ArithmeticFunction.sigma 1 n := by
  classical
  rw [ArithmeticFunction.sigma_one_apply]
  calc
    _ = ∑ i ∈ s.image conjClassCard, i :=
      (Finset.sum_image (f := id) (g := conjClassCard) h.injOn).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset (by
      intro i hi
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hi
      exact Nat.mem_divisors.mpr ⟨hd c hc, hn⟩)

private theorem class_size_of_involution_dvd {x : G} (hx : x ^ 2 = 1)
    (hD : IsPGroup 3 (commutator G)) {a b : ℕ}
    (hG : Nat.card G = 2 ^ a * 3 ^ b) : conjClassCard (ConjClasses.mk x) ∣ 3 ^ b := by
  have hxP : IsPGroup 2 (Subgroup.zpowers x) := isPGroup_iff_card_dvd_pow.mpr
    ⟨1, by simpa only [Nat.card_zpowers, pow_one] using orderOf_dvd_of_pow_eq_one hx⟩
  obtain ⟨P, hin⟩ := hxP.exists_le_sylow
  have hdj : Disjoint (P : Subgroup G) (commutator G) :=
    P.isPGroup'.disjoint_of_coprime hD (by decide)
  let f := (Abelianization.of (G := G)).comp P.1.subtype
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_one _).mpr
    intro z hz
    apply Subtype.ext
    apply Subgroup.disjoint_def.mp hdj z.2
    rw [← Abelianization.ker_of]; exact hz
  have hle : P.1 ≤ Subgroup.centralizer ({x} : Set G) := by
    intro y hy
    let u : P := ⟨x, hin (Subgroup.mem_zpowers x)⟩
    let v : P := ⟨y, hy⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (hf (show f (v * u) = f (u * v) by rw [map_mul, map_mul, mul_comm]))
  have hd : conjClassCard (ConjClasses.mk x) ∣ P.1.index := by
    have he := conjClassCard_mk_mul_card_centralizer x
    rw [← (Subgroup.centralizer ({x} : Set G)).index_mul_card] at he
    rw [Nat.eq_of_mul_eq_mul_right Nat.card_pos he]
    exact Subgroup.index_dvd_of_le hle
  apply hd.trans
  have hcop := Nat.prime_two.coprime_pow_of_not_dvd (m := a) P.not_dvd_index
  exact hcop.dvd_of_dvd_mul_left (hG ▸ P.1.index_dvd_card)

private theorem six_dvd_centralizer_of_mixed (h : HasDistinctConjClassSizes G)
    (hD : IsPGroup 3 (commutator G)) (x : G) (hx : x ∉ commutator G) (h2 : x ^ 2 ≠ 1) :
    6 ∣ Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  have hs := sq_mem_commutator h x
  have ho : orderOf (Abelianization.of x) = 2 := by
    have hsq : (Abelianization.of x) ^ 2 = 1 := by
      rw [← map_pow]; exact (Abelianization.ker_of G ▸ hs : _)
    have hne : Abelianization.of x ≠ 1 := by
      intro he
      exact hx ((Abelianization.ker_of G) ▸ he)
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hsq) with h1 | h1
    · exact False.elim (hne (orderOf_eq_one_iff.mp h1))
    · exact h1
  let z : commutator G := ⟨x ^ 2, hs⟩
  obtain ⟨n, hn⟩ := hD.exists_orderOf_eq_pow z
  have hne : n ≠ 0 := by
    rintro rfl
    exact h2 (congrArg Subtype.val (orderOf_eq_one_iff.mp hn))
  have hthree : 3 ∣ orderOf (x ^ 2) := by
    rw [← show orderOf z = orderOf (x ^ 2) from Subgroup.orderOf_mk _ _, hn]
    exact dvd_pow_self _ hne
  have hd : 6 ∣ orderOf x := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 2 3)
    (ho ▸ orderOf_map_dvd Abelianization.of x) (hthree.trans (orderOf_pow_dvd 2))
  apply hd.trans
  let u : Subgroup.centralizer ({x} : Set G) := ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  exact Subgroup.orderOf_coe u ▸ orderOf_dvd_natCard u

/-- Markel's class count when the derived subgroup is a 3-group. -/
theorem nonempty_mulEquiv_perm_three_of_threeGroup_commutator [Nontrivial G]
    (h : HasDistinctConjClassSizes G) (hD : IsPGroup 3 (commutator G)) :
    Nonempty (G ≃* Equiv.Perm (Fin 3)) := by
  classical
  let D := commutator G
  have hQ : IsPGroup 2 (Abelianization G) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective D q
    refine ⟨1, ?_⟩
    change (Abelianization.of x) ^ 2 = 1
    rw [← map_pow]
    change x ^ 2 ∈ Abelianization.of.ker
    rw [Abelianization.ker_of]; exact sq_mem_commutator h x
  obtain ⟨a, ha⟩ := hQ.exists_card_eq
  obtain ⟨b, hb⟩ := hD.exists_card_eq
  have hG : Nat.card G = 2 ^ a * 3 ^ b := D.index_mul_card.symm.trans (congrArg₂ (· * ·) ha hb)
  apply nonempty_mulEquiv_perm_three_of_not_four_dvd h
  intro h4
  have ha2 : 2 ≤ a := by
    by_contra! hn
    have hnodd : ¬ 2 ∣ 3 ^ b := fun e => (by decide : ¬ 2 ∣ 3) (Nat.prime_two.dvd_of_dvd_pow e)
    rw [hG] at h4
    interval_cases a
    · exact hnodd (dvd_trans (by decide : 2 ∣ 4) (by simpa using h4))
    · exact hnodd (Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 2) (by simpa using h4 : 2 * 2 ∣ 2 * 3 ^ b))
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le' ha2
  cases b with
  | zero =>
    have hbot := (commutator G).card_eq_one.mp hb
    have e := (commutator_eq_bot_iff_center_eq_top G).mp hbot
    exact bot_ne_top ((trivial_center_of_hasDistinctConjClassSizes h).symm.trans e)
  | succ b =>
    let rep (c : ConjClasses G) : G := (ConjClasses.mk_surjective c).choose
    have hrep (c : ConjClasses G) : ConjClasses.mk (rep c) = c := (ConjClasses.mk_surjective c).choose_spec
    let S := Finset.univ.filter (fun c => rep c ∈ D)
    let T := Finset.univ.filter (fun c => rep c ∉ D)
    let I := T.filter (fun c => rep c ^ 2 = 1)
    let M := T.filter (fun c => rep c ^ 2 ≠ 1)
    have sD : ∑ c ∈ S, conjClassCard c = Nat.card D := by
      have hpre : ConjClasses.mk ⁻¹' (S : Set (ConjClasses G)) = (D : Set G) := by
        ext x
        change ConjClasses.mk x ∈ S ↔ x ∈ D
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        have he := ConjClasses.mk_eq_mk_iff_isConj.mp (hrep (ConjClasses.mk x))
        exact ⟨fun hh => Group.conjugates_subset_normal (N := D) hh he,
          fun hh => Group.conjugates_subset_normal (N := D) hh he.symm⟩
      calc
        _ = ∑ c ∈ S, Nat.card {x : G // ConjClasses.mk x = c} := by
          simp only [conjClassCard, ConjClasses.carrier_eq_preimage_mk]; rfl
        _ = Nat.card (ConjClasses.mk ⁻¹' (S : Set (ConjClasses G))) :=
          (Finset.card_preimage_eq_sum_card_image_eq (fun _ _ => Set.toFinite _)).symm
        _ = _ := by rw [hpre]; rfl
    have sI := sum_class_sizes_le_sigma h I (3 ^ (b+1)) (by positivity) (by
      intro c hc
      rw [← hrep c]
      exact class_size_of_involution_dvd (Finset.mem_filter.mp hc).2 hD hG)
    have sM := sum_class_sizes_le_sigma h M (2 ^ (a+1) * 3 ^ b) (by positivity) (by
      intro c hc
      have hx := Finset.mem_filter.mp hc
      have hd := six_dvd_centralizer_of_mixed h hD (rep c) (Finset.mem_filter.mp hx.1).2 hx.2
      have he := conjClassCard_mk_mul_card_centralizer (rep c)
      rw [hrep, hG] at he
      obtain ⟨k, hk⟩ := hd
      refine ⟨k, ?_⟩
      rw [hk] at he
      simp only [pow_succ] at he ⊢
      nlinarith [he])
    have sAll : ∑ c : ConjClasses G, conjClassCard c = Nat.card G := by
      rw [← Group.sum_card_conj_classes_eq_card G, finsum_eq_sum_of_fintype]
      rfl
    have hst : (∑ c ∈ S, conjClassCard c) + ∑ c ∈ T, conjClassCard c = Nat.card G :=
      (Finset.sum_filter_add_sum_filter_not _ _ _).trans sAll
    have him : (∑ c ∈ I, conjClassCard c) + ∑ c ∈ M, conjClassCard c = ∑ c ∈ T, conjClassCard c :=
      Finset.sum_filter_add_sum_filter_not _ _ _
    rw [sD, ← him, hG] at hst
    change Nat.card (commutator G) + _ = _ at hst
    rw [hb] at hst
    rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
      (Nat.Coprime.pow _ _ (by decide : Nat.Coprime 2 3)),
      ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two,
      ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_three] at sM
    rw [ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_three] at sI
    have e3 := geom_three b
    have e3' := geom_three (b+1)
    have e2 := geom_two (a+1)
    have ha1 : 1 ≤ 2 ^ a := Nat.one_le_pow _ _ (by decide)
    simp only [pow_succ] at hst e3 e3' e2
    have hx := Nat.mul_le_mul_right (3 ^ b) ha1
    have e23 := congrArg (· * (∑ i ∈ range (b+1), 3 ^ i)) e2
    have e32 := congrArg (2 ^ a * 4 * ·) e3
    nlinarith only [hx, e23, e32, hst, sI, sM, e3, e3', ha1]

/-- Markel's theorem for finite nontrivial groups with nilpotent derived subgroup. -/
theorem nonempty_mulEquiv_perm_three_of_nilpotent_commutator [Nontrivial G]
    [Group.IsNilpotent (commutator G)] (h : HasDistinctConjClassSizes G) :
    Nonempty (G ≃* Equiv.Perm (Fin 3)) :=
  nonempty_mulEquiv_perm_three_of_threeGroup_commutator h (isThreeGroup_commutator_of_nilpotent h)

end Count

end

section

section ThreeQuot
variable {G : Type*} [Group G] [Fintype G]

/-- Centralizer cardinality cannot increase when passing to a quotient. -/
theorem card_centralizer_quotient_le (K : Subgroup G) [K.Normal] (x : G) :
    Nat.card (Subgroup.centralizer ({QuotientGroup.mk' K x} : Set (G ⧸ K))) ≤
      Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  let f := QuotientGroup.mk' K
  let a := ConjClasses.mk x
  let b := ConjClasses.mk (f x)
  have hs : a.carrier ⊆ QuotientGroup.mk ⁻¹' b.carrier := fun _ hy => f.map_isConj hy
  have hle : conjClassCard a ≤ Nat.card K * conjClassCard b := by
    unfold conjClassCard
    rw [← QuotientGroup.card_preimage_mk K b.carrier]
    exact Nat.card_le_card_of_injective (Set.inclusion hs) (Set.inclusion_injective hs)
  have hb : 0 < conjClassCard b := by
    let : Nonempty b.carrier := ⟨⟨f x, ConjClasses.mem_carrier_mk⟩⟩
    exact Nat.card_pos
  refine Nat.le_of_mul_le_mul_left (c := Nat.card K * conjClassCard b) ?_ (Nat.mul_pos Nat.card_pos hb)
  calc
    _ = Nat.card (G ⧸ K) * Nat.card K := by
      rw [Nat.mul_assoc, conjClassCard_mk_mul_card_centralizer, Nat.mul_comm]
    _ = Nat.card G := (Subgroup.card_eq_card_quotient_mul_card_subgroup K).symm
    _ = conjClassCard a * Nat.card (Subgroup.centralizer ({x} : Set G)) :=
      (conjClassCard_mk_mul_card_centralizer x).symm
    _ ≤ _ := Nat.mul_le_mul_right _ hle

/-- A lift with centralizer of order three survives in a quotient of order six.
Choose the last derived layer containing the element. Its image is abelian and normal,
and lies in the centralizer of the image, so it is cyclic of order three. -/
theorem exists_quotient_card_six_of_centralizer_three [Group.IsSolvable G] [Nontrivial G]
    (h : HasDistinctConjClassSizes G) (x : G)
    (hc : Nat.card (Subgroup.centralizer ({x} : Set G)) = 3) :
    ∃ (K : Subgroup G) (_ : K.Normal), Nat.card (G ⧸ K) = 6 ∧ orderOf (QuotientGroup.mk' K x) = 3 ∧
      (∀ b ∈ K, b * x = x * b → b = 1) := by
  classical
  have hx : x ≠ 1 := by
    rintro rfl
    have htop : Subgroup.centralizer ({1} : Set G) = ⊤ := by
      rw [Subgroup.centralizer_eq_top_iff_subset]; simp
    rw [htop, Subgroup.card_top] at hc
    have := two_dvd_card h
    omega
  have hxC : x ∈ Subgroup.centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hord : orderOf x = 3 := by
    have hd := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hxC)
    rw [Nat.card_zpowers, hc] at hd
    exact ((Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd).resolve_left (fun ho => hx (orderOf_eq_one_iff.mp ho))
  obtain ⟨i, hi, hni⟩ : ∃ i, x ∈ derivedSeries G i ∧ x ∉ derivedSeries G (i+1) := by
    by_contra! hall
    apply not_isSolvable_of_mem_derivedSeries hx _ inferInstance
    intro j
    induction j with
    | zero => simp
    | succ j hj => exact hall j hj
  let D := derivedSeries G i
  let K := derivedSeries G (i+1)
  let f := QuotientGroup.mk' K
  let u := f x
  let A := D.map f
  have : A.Normal := (derivedSeries_normal G i).map f (QuotientGroup.mk'_surjective K)
  have hcomm : IsMulCommutative A := by
    apply Subgroup.commutator_self_eq_bot_iff.mp
    change ⁅D.map f, D.map f⁆ = ⊥
    rw [← Subgroup.map_commutator, Subgroup.map_eq_bot_iff]
    exact le_of_eq (by rw [QuotientGroup.ker_mk']; rfl)
  have huA : u ∈ A := ⟨x, hi, rfl⟩
  have hu : orderOf u = 3 := by
    have hd := orderOf_map_dvd f x
    rw [hord] at hd
    exact ((Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd).resolve_left fun h1 =>
      hni ((QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp h1))
  let C := Subgroup.centralizer ({u} : Set (G ⧸ K))
  have hC : Nat.card C ≤ 3 := (card_centralizer_quotient_le K x).trans hc.le
  have hA : Nat.card A = 3 := by
    apply le_antisymm _ (by simpa only [Nat.card_zpowers, hu] using
      Subgroup.card_le_of_le (Subgroup.zpowers_le.mpr huA))
    refine (Subgroup.card_le_of_le (show A ≤ C from ?_)).trans hC
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hcomm.is_comm.comm (⟨y,hy⟩ : A) ⟨u,huA⟩))
  have : IsCyclic A := isCyclic_of_prime_card hA
  let act : (G ⧸ K) →* MulAut A := MulAut.conjNormal
  have hker : act.ker ≤ C := by
    intro b hb
    have he := congrArg (fun a : MulAut A => ((a ⟨u, huA⟩ : A) : G ⧸ K))
      (MonoidHom.mem_ker.mp hb)
    exact Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he)
  have hidx : act.ker.index ≤ 2 := calc
    _ = Nat.card act.range := Subgroup.index_ker act
    _ ≤ Nat.card (MulAut A) := Nat.card_le_card_of_injective _ Subtype.val_injective
    _ = (Nat.card A).totient := IsCyclic.card_mulAut A
    _ ≤ 2 := by rw [hA]; decide
  have hle : Nat.card (G ⧸ K) ≤ 6 := by
    rw [← act.ker.card_mul_index]
    exact Nat.mul_le_mul ((Subgroup.card_le_of_le hker).trans hC) hidx
  have : Nontrivial (G ⧸ K) := ⟨⟨u, 1, fun he => (by decide : (1 : ℕ) ≠ 3) (by simpa only [he, orderOf_one] using hu)⟩⟩
  have h2 : 2 ∣ Nat.card (G ⧸ K) := by
    apply two_dvd_card_of_all_real
    intro q
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective K q
    simpa only [map_inv] using f.map_isConj (isConj_inv h v)
  have h3 := orderOf_dvd_natCard u
  rw [hu] at h3
  have hpos : 0 < Nat.card (G ⧸ K) := Nat.card_pos
  refine ⟨K, inferInstance, by omega, hu, ?_⟩
  intro b hb he
  by_contra hbn
  have hbC := Subgroup.mem_centralizer_singleton_iff.mpr he
  have hgen : Subgroup.zpowers b = Subgroup.centralizer ({x} : Set G) := by
    have hleC := Subgroup.zpowers_le.mpr hbC
    apply Subgroup.eq_of_le_of_card_ge hleC
    have hd := Subgroup.card_dvd_of_le hleC
    rw [Nat.card_zpowers, hc] at hd ⊢
    exact (((Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd).resolve_left
      (fun ho => hbn (orderOf_eq_one_iff.mp ho))).ge
  exact hni ((Subgroup.zpowers_le.mpr hb) (hgen.symm ▸ hxC))

/-- A centralizer of order three yields an S₃ quotient whose kernel has order prime
to three. Conjugation by the given element is fixed-point-free on the kernel. -/
theorem exists_quotient_perm_three_of_centralizer_three [Group.IsSolvable G] [Nontrivial G]
    (h : HasDistinctConjClassSizes G) (x : G)
    (hc : Nat.card (Subgroup.centralizer ({x} : Set G)) = 3) :
    ∃ (K : Subgroup G) (_ : K.Normal), Nonempty ((G ⧸ K) ≃* Equiv.Perm (Fin 3)) ∧
      orderOf (QuotientGroup.mk' K x) = 3 ∧ ¬ 3 ∣ Nat.card K ∧
      MonoidHom.FixedPointFree (MulAut.conjNormal (H := K) x) := by
  obtain ⟨K, hK, h6, hu, hf⟩ := exists_quotient_card_six_of_centralizer_three h x hc
  let f := QuotientGroup.mk' K
  have hr : IsConj (f x) (f x)⁻¹ := by simpa only [map_inv] using f.map_isConj (isConj_inv h x)
  have hx : x ≠ 1 := fun he => (by decide : (1 : ℕ) ≠ 3) (by simpa only [he, map_one, orderOf_one] using hu)
  obtain ⟨P, hP⟩ := exists_sylow_card_of_prime_centralizer (by decide : Nat.Prime 3) hx hc
  refine ⟨K, hK, nonempty_mulEquiv_perm_three_of_card_six_of_real_three h6 hu hr, hu, ?_, ?_⟩
  · intro hd
    have h9 : 3 ^ 2 ∣ Nat.card G := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup K, h6]
      exact Nat.mul_dvd_mul (by decide : 3 ∣ 6) hd
    have hbad := P.pow_dvd_card_of_pow_dvd_card h9
    rw [hP] at hbad
    exact (by decide : ¬ 3 ^ 2 ∣ 3) hbad
  · intro b hb
    apply Subtype.ext
    exact hf _ b.2 ((mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hb)).symm)

end ThreeQuot

end

section

section FixedPointFreeThree

variable {K : Type*} [Group K] [Finite K]

/-- In a finite group with a fixed-point-free automorphism of period three, every
element commutes with every one of its conjugates. -/
private theorem commute_conj_of_fixedPointFree_three (a : MulAut K)
    (hf : MonoidHom.FixedPointFree a) (h3 : (a : K → K)^[3] = id) (x g : K) :
    Commute x (g * x * g⁻¹) := by
  have norm (v : K) : v * (a v * a (a v)) = 1 := by
    simpa [List.range_succ, Function.iterate_succ_apply] using hf.prod_pow_eq_one h3 v
  have abc (v : K) : a (a (a v)) = v := congrFun h3 v
  have comm (v : K) : Commute v (a v) := by
    have h := congrArg Inv.inv (norm v⁻¹)
    simp only [map_inv, mul_inv_rev, inv_inv, inv_one] at h
    have h' := norm (a (a v))
    simp only [abc] at h'
    change v * a v = a v * v
    apply mul_left_cancel (a := a (a v))
    calc a (a v) * (v * a v) = 1 := h'
      _ = a (a v) * (a v * v) := by simpa only [mul_assoc] using h.symm
  have twisted (v t : K) : Commute v (t * a v * t⁻¹) := by
    obtain ⟨d, hd⟩ := hf.commutatorMap_surjective t
    change d / a d = t at hd
    subst t
    have hc := (comm (d⁻¹ * v * d)).map (MulAut.conj d)
    simpa only [MulAut.conj_apply, map_mul, map_inv, div_eq_mul_inv, mul_inv_rev, inv_inv,
      mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left, mul_inv_cancel_right, mul_inv_cancel, inv_mul_cancel, mul_one] using hc
  have h1 := twisted x g
  have h2 : Commute x (g * a (a x) * g⁻¹) := by
    have hc := ((twisted (a (a x)) g⁻¹).map (MulAut.conj g)).symm
    simpa only [abc, MulAut.conj_apply, inv_inv, mul_assoc, mul_inv_cancel_left,
      mul_inv_cancel_right, mul_inv_cancel, inv_mul_cancel, mul_one] using hc
  have hx : x = (a x * a (a x))⁻¹ := eq_inv_of_mul_eq_one_left (norm x)
  have hg : g * x * g⁻¹ = ((g * a x * g⁻¹) * (g * a (a x) * g⁻¹))⁻¹ := by
    conv_lhs => rw [hx]
    group
  rw [hg]
  exact (h1.mul_right h2).inv_right

omit [Finite K] in
/-- For a finite group, the normal closure of a p-element commuting with all its
conjugates is a normal p-subgroup. -/
private theorem isPGroup_normalClosure_of_commute_conj {p : ℕ} {x : K} {n : ℕ}
    (hx : x ^ p ^ n = 1) (hc : ∀ u v : K, IsConj u v → Commute u v) :
    IsPGroup p (Subgroup.normalClosure ({x} : Set K)) := by
  let S := Group.conjugatesOfSet ({x} : Set K)
  let A := Subgroup.closure S
  have hxS {y : K} (hy : y ∈ S) : IsConj x y := by
    simpa only [S, Group.mem_conjugatesOfSet_iff, Set.mem_singleton_iff,
      exists_eq_left] using hy
  have : IsMulCommutative A := Subgroup.isMulCommutative_closure
    (fun y hy z hz => hc y z ((hxS hy).symm.trans (hxS hz)))
  intro y
  refine ⟨n, Subtype.ext ?_⟩
  change (y : K) ^ p ^ n = 1
  suffices all : ∀ z ∈ Subgroup.closure S, z ^ p ^ n = 1 from all y y.2
  intro v hv
  induction hv using Subgroup.closure_induction with
  | mem z hz =>
    obtain ⟨t, ht⟩ := isConj_iff.mp (hxS hz)
    rw [← ht, ← MulAut.conj_apply, ← map_pow, hx, map_one]
  | one => simp
  | mul z w hz hw ihz ihw =>
    have hc' : Commute z w := setLike_mul_comm (s := A) hz hw
    rw [hc'.mul_pow, ihz, ihw, one_mul]
  | inv z _ ih => rw [inv_pow, ih, inv_one]

/-- A finite group in which each element commutes with all its conjugates is nilpotent. -/
theorem isNilpotent_of_commute_conjugates (hc : ∀ x y : K, IsConj x y → Commute x y) :
    Group.IsNilpotent K := by
  apply ((Group.isNilpotent_of_finite_tfae (G := K)).out 3 0).mp
  intro p hp P
  constructor
  intro x hx t
  obtain ⟨n, hn⟩ := P.isPGroup' ⟨x, hx⟩
  have hpg := isPGroup_normalClosure_of_commute_conj (x := x) (p := p)
    (show x ^ p ^ n = 1 from congrArg Subtype.val hn) hc
  apply hpg.le_sylow_of_normal P
  exact (Subgroup.normalClosure_normal).conj_mem x (Subgroup.subset_normalClosure (Set.mem_singleton _)) t

/-- A finite group admitting a fixed-point-free automorphism of period three is nilpotent. -/
theorem isNilpotent_of_fixedPointFree_three (a : MulAut K)
    (hf : MonoidHom.FixedPointFree a) (h3 : (a : K → K)^[3] = id) : Group.IsNilpotent K := by
  apply isNilpotent_of_commute_conjugates
  intro x y hy
  obtain ⟨t, rfl⟩ := isConj_iff.mp hy
  exact commute_conj_of_fixedPointFree_three a hf h3 x t

end FixedPointFreeThree

section ThreeKernel

open ConjugacyClassSizes

variable {G : Type*} [Group G] [Fintype G] [Nontrivial G]

/-- If the quotient is symmetric of degree three, a nilpotent kernel of order
coprime to three must vanish. -/
theorem eq_bot_of_nilpotent_of_quotient_perm_three_of_not_three_dvd
    (h : HasDistinctConjClassSizes G) (N : Subgroup G) [N.Normal] [Group.IsNilpotent N]
    (hn3 : ¬ 3 ∣ Nat.card N) (e : (G ⧸ N) ≃* Equiv.Perm (Fin 3)) : N = ⊥ := by
  have hprime (p : ℕ) (hp : p.Prime) (hd : p ∣ Nat.card N) : p = 2 := by
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨z, hz, ho⟩ := exists_prime_order_in_center_of_nilpotent p hd
    obtain ⟨w, hw⟩ := exists_quotient_order_multiple_prime_sub_one h N
      ((Subgroup.orderOf_coe z).trans ho) (by
        intro t ht
        exact Subgroup.mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨t, ht⟩)))
    have hle := Nat.le_of_dvd (orderOf_pos w) hw
    rw [← e.orderOf_eq w] at hle
    have hb : (e w) ^ 2 = 1 ∨ (e w) ^ 3 = 1 :=
      (by decide : ∀ t : Equiv.Perm (Fin 3), t ^ 2 = 1 ∨ t ^ 3 = 1) _
    have h4 : p ≤ 4 := by
      rcases hb with h2 | h3
      · have := Nat.le_of_dvd (by decide : 0 < 2) (orderOf_dvd_of_pow_eq_one h2)
        omega
      · have := Nat.le_of_dvd (by decide : 0 < 3) (orderOf_dvd_of_pow_eq_one h3)
        omega
    have h2 := hp.two_le
    have hne3 : p ≠ 3 := fun he => hn3 (he ▸ hd)
    have hne4 : p ≠ 4 := fun he => (by decide : ¬ Nat.Prime 4) (he ▸ hp)
    omega
  let P : Sylow 2 N := default
  have hi : P.index = 1 := by
    by_contra he
    obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd he
    exact P.not_dvd_index (hprime p hp (hd.trans P.1.index_dvd_card) ▸ hd)
  have htop : (P : Subgroup N) = ⊤ := Subgroup.index_eq_one.mp hi
  have h2 : IsPGroup 2 N := P.isPGroup'.of_surjective P.1.subtype (by
    intro y; exact ⟨⟨y, htop ▸ Subgroup.mem_top y⟩, rfl⟩)
  exact eq_bot_of_isTwoGroup_of_quotient_perm_three h N h2 e

/-- A solvable ah-group with a centralizer of order three is the symmetric group
on three letters. -/
theorem nonempty_mulEquiv_perm_three_of_card_centralizer_eq_three [Group.IsSolvable G]
    (h : HasDistinctConjClassSizes G) {x : G}
    (hc : Nat.card (Subgroup.centralizer ({x} : Set G)) = 3) :
    Nonempty (G ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨K, hK, ⟨e⟩, ho, hn3, hf⟩ := exists_quotient_perm_three_of_centralizer_three h x hc
  have hxC : x ∈ Subgroup.centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have h3 : x ^ 3 = 1 := by
    have hpow := pow_card_eq_one' (x := (⟨x, hxC⟩ : Subgroup.centralizer ({x} : Set G)))
    rw [hc] at hpow
    exact congrArg Subtype.val hpow
  have : Group.IsNilpotent K := isNilpotent_of_fixedPointFree_three (MulAut.conjNormal x) hf (by
    funext z
    have he : (MulAut.conjNormal x : MulAut K) ^ 3 = 1 := by rw [← map_pow, h3, map_one]
    exact congrArg (fun a : MulAut K => a z) he)
  have hb := eq_bot_of_nilpotent_of_quotient_perm_three_of_not_three_dvd h K hn3 e
  let q := QuotientGroup.mk' K
  have hbij : Function.Bijective q := ⟨q.ker_eq_bot_iff.mp
    ((QuotientGroup.ker_mk' K).trans hb), QuotientGroup.mk'_surjective K⟩
  exact ⟨(MulEquiv.ofBijective q hbij).trans e⟩

end ThreeKernel

end

section

section NormalizerPowers

variable {G : Type*} [Group G] [Fintype G]

/-- Every automorphism of a cyclic subgroup of an ah-group is induced by conjugation
in its normalizer. -/
theorem normalizer_zpowers_surjective (h : HasDistinctConjClassSizes G) (x : G) :
    Function.Surjective (Subgroup.zpowers x).normalizerMonoidHom := by
  let A := Subgroup.zpowers x
  let a : A := ⟨x, Subgroup.mem_zpowers x⟩
  have gen (y : A) : ∃ i : ℤ, a ^ i = y := by
    obtain ⟨i, hi⟩ := y.2
    exact ⟨i, Subtype.ext hi⟩
  intro e
  let z : G := e a
  have hgen : Subgroup.zpowers z = A := by
    refine le_antisymm (Subgroup.zpowers_le.mpr (e a).2) ?_
    intro y hy
    obtain ⟨i, hi⟩ := gen (e.symm ⟨y,hy⟩)
    exact ⟨i, congrArg Subtype.val (show (e a) ^ i = ⟨y,hy⟩ by
      rw [← map_zpow, hi, e.apply_symm_apply])⟩
  obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_of_zpowers_eq h hgen.symm)
  have hgN : g ∈ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom = A
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (g * x * g⁻¹) = A
    rwa [hg]
  refine ⟨⟨g, hgN⟩, ?_⟩
  apply MulEquiv.ext
  intro y
  obtain ⟨i, rfl⟩ := gen y
  simp only [map_zpow]
  exact congrArg (fun b : A => b ^ i) (Subtype.ext hg)

/-- The totient of an element order divides the index of its generated subgroup. -/
theorem totient_orderOf_dvd_zpowers_index (h : HasDistinctConjClassSizes G) (x : G) :
    (orderOf x).totient ∣ (Subgroup.zpowers x).index := by
  let A := Subgroup.zpowers x
  let N := Subgroup.normalizer (A : Set G)
  let f := A.normalizerMonoidHom
  have hker : A.subgroupOf N ≤ f.ker := by
    change A.subgroupOf N ≤ A.normalizerMonoidHom.ker
    rw [Subgroup.normalizerMonoidHom_ker]
    intro y hy
    exact A.le_centralizer hy
  have hi : f.ker.index = (orderOf x).totient := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr (normalizer_zpowers_surjective h x),
      Subgroup.card_top, IsCyclic.card_mulAut, Nat.card_zpowers]
  rw [← hi]
  exact (Subgroup.index_dvd_of_le hker).trans (Subgroup.relIndex_dvd_index_of_le A.le_normalizer)

/-- Rationality forces the product of the element order and its totient to divide the
ambient group order. -/
theorem orderOf_mul_totient_dvd_card (h : HasDistinctConjClassSizes G) (x : G) :
    orderOf x * (orderOf x).totient ∣ Nat.card G := by
  rw [← (Subgroup.zpowers x).card_mul_index, Nat.card_zpowers]
  exact Nat.mul_dvd_mul_left _ (totient_orderOf_dvd_zpowers_index h x)

/-- An index-two cyclic subgroup of a Sylow 2-subgroup in an ah-group has order at most
four. In particular such a Sylow subgroup has order at most eight. -/
theorem card_sylow_two_le_eight_of_cyclic_index_two (h : HasDistinctConjClassSizes G)
    (P : Sylow 2 G) (A : Subgroup P) [IsCyclic A] (hi : A.index = 2) : Nat.card P ≤ 8 := by
  have hpc := A.card_mul_index
  rw [hi] at hpc
  obtain ⟨x, hx⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := A)
  obtain ⟨n, hn⟩ := (P.isPGroup'.to_subgroup A).exists_card_eq
  obtain _ | n := n
  · rw [← hpc, hn]; decide
  have hd := orderOf_mul_totient_dvd_card h (((x : P) : G))
  rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx, hn, Nat.totient_prime_pow_succ Nat.prime_two,
    show 2 - 1 = 1 by rfl, Nat.mul_one, ← pow_add] at hd
  have h := Nat.le_of_dvd (Nat.card_pos (α := P)) (P.pow_dvd_card_of_pow_dvd_card hd)
  rw [← hpc, hn, ← pow_succ] at h
  have hle : n+1+n ≤ n+1+1 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp h
  have : n ≤ 1 := by omega
  interval_cases n <;> rw [← hpc, hn] <;> decide

end NormalizerPowers

end

section

private theorem center_card_two_of_small_centralizer {P : Type*} [Group P] [Fintype P]
    (hp : IsPGroup 2 P) {x : P} (hP : 4 < Nat.card P)
    (hc : Nat.card (Subgroup.centralizer ({x} : Set P)) ≤ 4) :
    Nat.card (Subgroup.center P) = 2 := by
  let C := Subgroup.centralizer ({x} : Set P)
  have : Nontrivial P := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have htwo := (Subgroup.center P).one_lt_card_iff_ne_bot.mpr hp.bot_lt_center.ne'
  have hle : Subgroup.center P ≤ C := Subgroup.center_le_centralizer _
  have hlt : Nat.card (Subgroup.center P) < 4 := by
    by_contra! hZ
    have heq := Subgroup.eq_of_le_of_card_ge hle (hc.trans hZ)
    have hx : x ∈ Subgroup.center P := heq ▸ Subgroup.mem_centralizer_singleton_iff.mpr rfl
    have htop : C = ⊤ := Subgroup.centralizer_eq_top_iff_subset.mpr (Set.singleton_subset_iff.mpr hx)
    change Nat.card C ≤ 4 at hc
    rw [htop, Subgroup.card_top] at hc
    omega
  rcases (hp.to_subgroup (Subgroup.center P)).card_eq_or_dvd with h | h <;> omega

/-- Lift a cyclic normal subgroup through a center of order two. When its generator has
order at least four and divisible by four, every lift of that generator has doubled order. -/
private theorem lift_order_through_center_two {P : Type*} [Group P] [Fintype P]
    (hZ : Nat.card (Subgroup.center P) = 2) (a : P) {d : ℕ} (hd : 0 < d)
    (hq : orderOf (QuotientGroup.mk' (Subgroup.center P) a) = 4 * d)
    (hN : (Subgroup.zpowers (QuotientGroup.mk' (Subgroup.center P) a)).Normal) :
    orderOf a = 8*d := by
  let Z := Subgroup.center P
  let f := QuotientGroup.mk' Z
  let q := f a
  have hs (z : P) (hz : z ∈ Z) : z ^ 2 = 1 := by
    have he := pow_card_eq_one' (x := (⟨z,hz⟩ : Z))
    change Nat.card Z = 2 at hZ
    rw [hZ] at he
    exact congrArg Subtype.val he
  let w := a ^ (2*d)
  have hw : f w ≠ 1 := by
    intro hw
    change f (a ^ (2*d)) = 1 at hw
    rw [map_pow] at hw
    have hdiv := orderOf_dvd_of_pow_eq_one hw
    rw [show orderOf (f a) = 4*d from hq] at hdiv
    have := Nat.le_of_dvd (by omega : 0 < 2*d) hdiv
    omega
  have hn : a ^ (4*d) ≠ 1 := by
    intro ha
    have hw1 : w ≠ 1 := fun h => hw (h ▸ f.map_one)
    have hww : w ^ 2 = 1 := by
      change (a ^ (2*d)) ^ 2 = 1
      rw [← pow_mul, show 2*d*2 = 4*d by omega, ha]
    have hw2 : orderOf w = 2 := ((Nat.dvd_prime Nat.prime_two).mp
      (orderOf_dvd_of_pow_eq_one hww)).resolve_left (fun h => hw1 (orderOf_eq_one_iff.mp h))
    have hZmem : w ∈ Z := by
      apply Subgroup.mem_center_iff.mpr
      intro g
      have hmem := hN.conj_mem (f a) (Subgroup.mem_zpowers _) (f g)
      obtain ⟨j,hj⟩ := hmem
      change f a ^ j = f g * f a * (f g)⁻¹ at hj
      let z := (a ^ j)⁻¹ * (g * a * g⁻¹)
      have hz : z ∈ Z := (QuotientGroup.eq_one_iff _).mp (by
        change f ((a ^ j)⁻¹ * (g * a * g⁻¹)) = 1
        simp only [map_mul, map_inv, map_zpow, hj, inv_mul_cancel])
      have hact : g * a * g⁻¹ = a ^ j * z := by dsimp [z]; group
      have hcomm : Commute (a ^ j) z := Subgroup.mem_center_iff.mp hz _
      have he : g * w * g⁻¹ = w ^ j := by
        change g * a ^ (2*d) * g⁻¹ = (a ^ (2*d)) ^ j
        rw [← conj_pow, hact, hcomm.mul_pow, pow_mul z, hs z hz, one_pow, mul_one]
        rw [← zpow_natCast (a ^ j), ← zpow_mul, ← zpow_natCast a, ← zpow_mul, mul_comm]
      have he' : g * w * g⁻¹ ≠ 1 := by
        intro hh
        apply hw1
        calc w = g⁻¹ * (g * w * g⁻¹) * g := by group
             _ = 1 := by rw [hh]; group
      have hh := eq_one_or_eq_of_mem_of_card_eq_two
        (Nat.card_zpowers (a := w) |>.trans hw2) (Subgroup.mem_zpowers w) hw1
        (show g * w * g⁻¹ ∈ Subgroup.zpowers w from ⟨j, he.symm⟩)
      exact mul_inv_eq_iff_eq_mul.mp (hh.resolve_left he')
    exact hw ((QuotientGroup.eq_one_iff _).mpr hZmem)
  have ham : a ^ (4*d) ∈ Z := (QuotientGroup.eq_one_iff _).mp (by
    change f (a ^ (4*d)) = 1
    rw [map_pow, ← hq]
    exact pow_orderOf_eq_one _)
  have hal : orderOf a ∣ (4*d) * 2 := orderOf_dvd_of_pow_eq_one (by
    rw [pow_mul]; exact hs _ ham)
  have hqa := orderOf_map_dvd f a
  rw [show orderOf (f a) = 4*d from hq] at hqa
  obtain ⟨r,hr⟩ := hqa
  rw [hr] at hal
  have hr2 := Nat.dvd_of_mul_dvd_mul_left (by omega : 0 < 4*d) hal
  rcases (Nat.dvd_prime Nat.prime_two).mp hr2 with h | h
  · rw [h, mul_one] at hr
    exact False.elim (hn (hr ▸ pow_orderOf_eq_one a))
  · rw [hr, h]; omega

private theorem exists_order_four_of_card_eight {P : Type*} [Group P] [Fintype P]
    (hP : Nat.card P = 8) {x : P} (hc : Nat.card (Subgroup.centralizer ({x} : Set P)) ≤ 4) :
    ∃ a : P, orderOf a = 4 := by
  have hex : ∃ y : P, y ^ 2 ≠ 1 := by
    by_contra! hinv
    have hr (y : P) : y⁻¹ = y := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hinv y)
    have htop : Subgroup.centralizer ({x} : Set P) = ⊤ := top_unique fun y _ =>
      Subgroup.mem_centralizer_singleton_iff.mpr (by
        have he := hr (x*y)
        rwa [mul_inv_rev, hr y, hr x] at he)
    rw [htop, Subgroup.card_top, hP] at hc
    omega
  obtain ⟨y,hy⟩ := hex
  have hd := orderOf_dvd_natCard y
  rw [hP] at hd
  obtain ⟨i, hil, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := 3)).mp hd
  interval_cases i
  · have := pow_orderOf_eq_one y
    simp only [hi, pow_zero, pow_one] at this
    exact False.elim (hy (by simp [this]))
  · exact False.elim (hy (by simpa only [hi, pow_one] using pow_orderOf_eq_one y))
  · exact ⟨y, hi⟩
  · exact ⟨y^2, by rw [orderOf_pow,hi]; decide⟩

private theorem exists_half_order_of_small_centralizer (n : ℕ) :
    ∀ {P : Type*} [Group P] [Fintype P], IsPGroup 2 P → Nat.card P = 2 ^ (n+3) →
      ∀ x : P, Nat.card (Subgroup.centralizer ({x} : Set P)) ≤ 4 →
        ∃ a : P, orderOf a = 2 ^ (n+2) := by
  induction n with
  | zero =>
    intro P _ _ _ hP x hc
    exact exists_order_four_of_card_eight hP hc
  | succ n ih =>
    intro P _ _ hp hP x hc
    classical
    let Z := Subgroup.center P
    let f := QuotientGroup.mk' Z
    have hPgt : 4 < Nat.card P := by rw [hP]; exact Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega : 2 < n+1+3)
    have hZ : Nat.card Z = 2 := center_card_two_of_small_centralizer hp hPgt hc
    let : Fintype (P ⧸ Z) := Fintype.ofFinite _
    have hqcard : Nat.card (P ⧸ Z) = 2^(n+3) := by
      have he := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
      rw [hP, hZ, show n+1+3 = (n+3)+1 by omega, pow_succ] at he
      omega
    obtain ⟨q, hq⟩ := ih (hp.to_quotient Z) hqcard (f x) ((card_centralizer_quotient_le Z x).trans hc)
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective Z q
    have hA : (Subgroup.zpowers (f a)).index = 2 := by
      have he := (Subgroup.zpowers (f a)).card_mul_index
      rw [Nat.card_zpowers, hq, hqcard, show n+3 = (n+2)+1 by omega, pow_succ] at he
      exact Nat.eq_of_mul_eq_mul_left (by positivity) he
    have h4d : orderOf (f a) = 4 * 2^n := by rw [hq, pow_add]; ring
    refine ⟨a, ?_⟩
    have ha := lift_order_through_center_two hZ a (by positivity : 0 < 2^n) h4d
      (Subgroup.normal_of_index_eq_two hA)
    rw [ha, show n+1+2 = n+3 by omega, pow_add]; ring

/-- A Sylow two-subgroup containing an element of centralizer order at most four has order
at most eight in an ah-group. -/
theorem card_sylow_two_le_eight_of_small_centralizer {G : Type*} [Group G] [Fintype G]
    (h : HasDistinctConjClassSizes G) (P : Sylow 2 G) (x : P)
    (hc : Nat.card (Subgroup.centralizer ({x} : Set P)) ≤ 4) : Nat.card P ≤ 8 := by
  classical
  obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
  rcases n with _ | _ | _ | n
  · rw [hn]; decide
  · rw [hn]; decide
  · rw [hn]; decide
  obtain ⟨a, ha⟩ := exists_half_order_of_small_centralizer n P.isPGroup' hn x hc
  have hA : (Subgroup.zpowers a).index = 2 := by
    have he := (Subgroup.zpowers a).card_mul_index
    rw [Nat.card_zpowers, ha, hn, show n+3 = (n+2)+1 by omega, pow_succ] at he
    exact Nat.eq_of_mul_eq_mul_left (by positivity) he
  exact card_sylow_two_le_eight_of_cyclic_index_two h P _ hA

/-- An element with centralizer order four in an ah-group forces its Sylow two-subgroups
to have order at most eight. -/
theorem exists_sylow_two_card_le_eight_of_centralizer_four {G : Type*} [Group G] [Fintype G]
    (h : HasDistinctConjClassSizes G) {x : G}
    (hc : Nat.card (Subgroup.centralizer ({x} : Set G)) = 4) :
    ∃ P : Sylow 2 G, Nat.card P ≤ 8 := by
  classical
  have hx : x ∈ Subgroup.centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hpow : IsPGroup 2 (Subgroup.zpowers x) := IsPGroup.of_card_dvd_pow (n := 2)
    ((Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hx)).trans hc.dvd)
  obtain ⟨P, hp⟩ := hpow.exists_le_sylow
  let a : P := ⟨x, hp (Subgroup.mem_zpowers x)⟩
  have hsub : Nat.card (Subgroup.centralizer ({a} : Set P)) ≤ Nat.card (Subgroup.centralizer ({x} : Set G)) := by
    let f (c : Subgroup.centralizer ({a} : Set P)) : Subgroup.centralizer ({x} : Set G) :=
      ⟨c.1.1, Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
        (Subgroup.mem_centralizer_singleton_iff.mp c.2))⟩
    exact Nat.card_le_card_of_injective f fun _ _ he => Subtype.ext (Subtype.ext (congrArg (fun c : Subgroup.centralizer ({x} : Set G) => (c : G)) he))
  exact ⟨P, card_sylow_two_le_eight_of_small_centralizer h P a (hsub.trans hc.le)⟩

end

section

private theorem not_prime_card_ah {G : Type*} [Group G] [Fintype G]
    (h : HasDistinctConjClassSizes G) : ¬ (Nat.card G).Prime := by
  intro hp
  let p := Nat.card G
  have : Fact p.Prime := ⟨hp⟩
  have : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp hp.one_lt
  have hpg := IsPGroup.of_card (G := G) (p := p) (n := 1) (pow_one p).symm
  have hcent := hpg.center_nontrivial
  rw [trivial_center_of_hasDistinctConjClassSizes h] at hcent
  exact not_nontrivial_iff_subsingleton.mpr inferInstance hcent

/-- A nonidentity element with centralizer order the product of two distinct primes
generates its centralizer. -/
theorem orderOf_eq_of_card_centralizer_eq_mul_primes {G : Type*} [Group G] [Fintype G]
    (h : HasDistinctConjClassSizes G) {x : G} (hx : x ≠ 1) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hc : Nat.card (Subgroup.centralizer ({x} : Set G)) = p * q) : orderOf x = p * q := by
  let C := Subgroup.centralizer ({x} : Set G)
  let z : C := ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hz : orderOf z = orderOf x := Subgroup.orderOf_mk _ _
  have hd : orderOf x ∣ p * q := hc ▸ hz ▸ orderOf_dvd_natCard z
  have hco := (Nat.coprime_primes hp hq).mpr hpq
  have noPrime {m : ℕ} (hm : m.Prime) (hg : Nat.card C = orderOf x * m)
      (hco : (orderOf x).Coprime m) : False := by
    obtain ⟨B,hB,ha⟩ := exists_ah_complement_in_centralizer h hg hco
    let _ := Fintype.ofFinite B
    exact not_prime_card_ah ha (hB ▸ hm)
  obtain ⟨a,b,ha,hb,he⟩ := exists_dvd_and_dvd_of_dvd_mul hd
  rcases (Nat.dvd_prime hp).mp ha with rfl | rfl <;>
    rcases (Nat.dvd_prime hq).mp hb with rfl | rfl <;> try simp only [one_mul, mul_one] at he
  · exact (hx (orderOf_eq_one_iff.mp he)).elim
  · exact (noPrime hp (by rw [he]; exact hc.trans (mul_comm _ _)) (he ▸ hco.symm)).elim
  · exact (noPrime hq (by rw [he, hc]) (he ▸ hco)).elim
  · exact he

/-- In any finite group, if the square of a prime divides the group order, it divides
the centralizer order of each element of that prime order. -/
theorem prime_sq_dvd_centralizer_of_prime_sq_dvd {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {x : G} (hx : orderOf x = p) (hs : p ^ 2 ∣ Nat.card G) :
    p ^ 2 ∣ Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hpg := IsPGroup.of_card (G := Subgroup.zpowers x) (p := p) (n := 1) (by
    rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨P,hP⟩ := hpg.exists_le_sylow
  let z : P := ⟨x, hP (Subgroup.mem_zpowers x)⟩
  let D := Subgroup.centralizer ({z} : Set P)
  have hz : orderOf z = p := (Subgroup.orderOf_mk _ _).trans hx
  let f : D →* Subgroup.centralizer ({x} : Set G) :=
    { toFun := fun u => ⟨u.1.1, Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp u.2))⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Nat.card D ∣ Nat.card (Subgroup.centralizer ({x} : Set G)) :=
    Subgroup.card_dvd_of_injective f (fun _ _ e => Subtype.ext (Subtype.ext (congrArg (fun v : Subgroup.centralizer ({x} : Set G) => (v : G)) e)))
  by_contra hc
  obtain ⟨k,hk⟩ := (P.isPGroup'.to_subgroup D).exists_card_eq
  have hk2 : k < 2 := by
    by_contra! hge
    exact hc ((show p ^ 2 ∣ Nat.card D by rw [hk]; exact pow_dvd_pow p hge).trans hf)
  have hzD : z ∈ D := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hpd := orderOf_dvd_natCard (⟨z,hzD⟩ : D)
  rw [Subgroup.orderOf_mk, hz] at hpd
  have hk1 : k ≠ 0 := by rintro rfl; rw [hk, pow_zero, Nat.dvd_one] at hpd; exact hp.ne_one hpd
  have hD : Nat.card D = p := by rw [hk, show k = 1 by omega, pow_one]
  have hpP := P.pow_dvd_card_of_pow_dvd_card hs
  have hpos : 1 < p ^ 2 := by nlinarith [hp.one_lt]
  have : Nontrivial P := Finite.one_lt_card_iff_nontrivial.mp (hpos.trans_le (Nat.le_of_dvd Nat.card_pos hpP))
  have hzP := P.isPGroup'.center_nontrivial
  have hCZ : Subgroup.center P ≤ D := fun u hu => Subgroup.mem_centralizer_singleton_iff.mpr
    ((Subgroup.mem_center_iff.mp hu z).symm)
  have hzd := Subgroup.card_dvd_of_le hCZ
  rw [hD] at hzd
  have hzCard : Nat.card (Subgroup.center P) = p :=
    ((Nat.dvd_prime hp).mp hzd).resolve_left (fun he =>
      (not_nontrivial_iff_subsingleton.mpr (Nat.card_eq_one_iff_unique.mp he).1) hzP)
  have hZe : Subgroup.center P = D := Subgroup.eq_of_le_of_card_ge hCZ (by rw [hD, hzCard])
  have hzcent : z ∈ Subgroup.center P := hZe ▸ hzD
  have htop : D = ⊤ := top_unique fun a _ =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_center_iff.mp hzcent a)
  have he : Nat.card P = p := by simpa [htop] using hD
  have hle := Nat.le_of_dvd Nat.card_pos hpP
  rw [he] at hle
  exact (Nat.not_lt.mpr hle) (by nlinarith [hp.one_lt])


/-- If `x` generates its centralizer of order `p*q`, then the centralizer of its
`q`-component contains only one factor `p` in its order. -/
theorem prime_sq_not_dvd_centralizer_pow_of_semiprime {G : Type*} [Group G] [Fintype G]
    (h : HasDistinctConjClassSizes G) {x : G} (hx : x ≠ 1) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (hc : Nat.card (Subgroup.centralizer ({x} : Set G)) = p * q) :
    ¬p ^ 2 ∣ Nat.card (Subgroup.centralizer ({x ^ p} : Set G)) := by
  have hox := orderOf_eq_of_card_centralizer_eq_mul_primes h hx hp hq hne hc
  let C := Subgroup.centralizer ({x ^ p} : Set G)
  let z : C := ⟨x ^ q, Subgroup.mem_centralizer_singleton_iff.mpr ((Commute.refl x).pow_pow q p)⟩
  have hz : orderOf z = p := by
    rw [Subgroup.orderOf_mk, orderOf_pow_of_dvd hq.ne_zero (hox ▸ Nat.dvd_mul_left q p),
      hox, Nat.mul_div_cancel _ hq.pos]
  let D := Subgroup.centralizer ({z} : Set C)
  have hco := (Nat.coprime_primes hp hq).mpr hne
  have hgen : Nat.Coprime (p + q) (orderOf x) := by
    rw [hox, Nat.coprime_mul_iff_right]
    exact ⟨by simpa using hco.symm, by simpa using hco⟩
  obtain ⟨k,hk⟩ := exists_pow_eq_self_of_coprime (x := x) hgen
  let f : D →* Subgroup.centralizer ({x} : Set G) :=
    { toFun := fun u => ⟨u.1.1, by
        have hp' : Commute u.1.1 (x ^ p) := Subgroup.mem_centralizer_singleton_iff.mp u.1.2
        have hq' : Commute u.1.1 (x ^ q) :=
          congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp u.2)
        have hg := hp'.mul_right hq'
        rw [← pow_add] at hg
        exact Subgroup.mem_centralizer_singleton_iff.mpr (hk ▸ hg.pow_right k)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hd := Subgroup.card_dvd_of_injective f (fun _ _ e => Subtype.ext
    (Subtype.ext (congrArg (fun v : Subgroup.centralizer ({x} : Set G) => (v : G)) e)))
  intro hsq
  have he := (prime_sq_dvd_centralizer_of_prime_sq_dvd hp hz hsq).trans hd
  rw [hc, pow_two] at he
  exact hne ((Nat.prime_dvd_prime_iff_eq hp hq).mp (Nat.dvd_of_mul_dvd_mul_left hp.pos he))

end

section

/-- In an ah-group an element of order ten forces a factor of sixteen in the group order.
Conjugation cubing the element acts with order four and fixes its involution. -/
theorem sixteen_dvd_card_of_orderOf_eq_ten {G : Type*} [Group G] [Fintype G]
    (h : HasDistinctConjClassSizes G) {x : G} (hx : orderOf x = 10) : 16 ∣ Nat.card G := by
  classical
  let A := Subgroup.zpowers x
  let N := Subgroup.normalizer (A : Set G)
  let a : A := ⟨x, Subgroup.mem_zpowers x⟩
  have hgen : Subgroup.zpowers (x ^ 3) = A := by
    apply le_antisymm (Subgroup.zpowers_le.mpr (Subgroup.npow_mem_zpowers x 3))
    apply Subgroup.zpowers_le.mpr
    exact (mem_zpowers_pow_iff (g := x)).mpr (by rw [hx]; decide)
  obtain ⟨b,hb⟩ := isConj_iff.mp (isConj_of_zpowers_eq h hgen.symm)
  have hbN : b ∈ N := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change (Subgroup.zpowers x).map (MulAut.conj b).toMonoidHom = A
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (b * x * b⁻¹) = A
    rwa [hb]
  let D := Subgroup.centralizer ({b} : Set G) ⊓ N
  let f := A.normalizerMonoidHom.comp (Subgroup.inclusion (show D ≤ N from inf_le_right))
  let u : D := ⟨b, Subgroup.mem_centralizer_singleton_iff.mpr rfl, hbN⟩
  have hua : f u a = a ^ 3 := Subtype.ext hb
  have hf2 : (f u) ^ 2 ≠ 1 := by
    intro he
    have hu : f u (f u a) = a := by
      change ((f u) ^ 2) a = a
      rw [he]; rfl
    rw [hua, map_pow, hua, ← pow_mul] at hu
    have hx9 : x ^ 9 = x := congrArg Subtype.val hu
    have hx8 : x ^ 8 = 1 := mul_right_cancel (b := x) (by simpa only [← pow_succ, one_mul] using hx9)
    have hd := orderOf_dvd_of_pow_eq_one hx8
    rw [hx] at hd; omega
  have haf : Nat.card (MulAut A) = 4 := by rw [IsCyclic.card_mulAut, Nat.card_zpowers, hx]; decide
  have hfu : orderOf (f u) = 4 := by
    have hd := orderOf_dvd_natCard (f u)
    rw [haf] at hd
    have hn : ¬orderOf (f u) ∣ 2 := fun hh => hf2 (orderOf_dvd_iff_pow_eq_one.mp hh)
    have hp := orderOf_pos (f u)
    have hle := Nat.le_of_dvd (by decide : 0 < 4) hd
    interval_cases n : orderOf (f u) <;> omega
  have hr4 : 4 ∣ Nat.card f.range := by
    let v : f.range := ⟨f u, u, rfl⟩
    rw [← hfu, ← show orderOf v = orderOf (f u) from Subgroup.orderOf_mk _ _]
    exact orderOf_dvd_natCard v
  let t := x ^ 5
  have ht2 : orderOf t = 2 := by
    rw [orderOf_pow_of_dvd (by decide : (5 : ℕ) ≠ 0) (hx ▸ (by decide : 5 ∣ 10)), hx]
  have hbt : b * t * b⁻¹ = t := by
    have he := congrArg (fun v : G => v ^ 5) hb
    simp only [conj_pow, ← pow_mul] at he
    have h15 : x ^ (3 * 5) = x ^ 10 * x ^ 5 := (pow_add x 10 5)
    have hx10 : x ^ 10 = 1 := hx ▸ pow_orderOf_eq_one x
    simpa only [h15, hx10, one_mul] using he
  have htA : t ∈ A := Subgroup.npow_mem_zpowers x 5
  let v : D := ⟨t, Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hbt).symm,
    A.le_normalizer htA⟩
  have hv : v ∈ f.ker := by
    apply MonoidHom.mem_ker.mpr
    ext z
    change t * z.1 * t⁻¹ = z.1
    exact mul_inv_eq_iff_eq_mul.mpr (congrArg Subtype.val (mul_comm' (⟨t,htA⟩ : A) z))
  have hk2 : 2 ∣ Nat.card f.ker := by
    have he := orderOf_dvd_natCard (⟨v,hv⟩ : f.ker)
    rw [Subgroup.orderOf_mk, show orderOf v = orderOf t from Subgroup.orderOf_mk _ _, ht2] at he
    exact he
  have h8 := Nat.mul_dvd_mul hk2 hr4
  rw [← Subgroup.index_ker, f.ker.card_mul_index] at h8
  have hC8 := h8.trans (Subgroup.card_dvd_of_le (show D ≤ Subgroup.centralizer ({b} : Set G) from inf_le_left))
  have hb2 : b ^ 2 ≠ 1 := by
    intro he
    apply hf2
    rw [← map_pow]
    have hu2 : u ^ 2 = 1 := Subtype.ext he
    rw [hu2, map_one]
  have hc2 := two_dvd_conjClassCard_of_isConj_inv (isConj_inv h b) hb2
  rw [← conjClassCard_mk_mul_card_centralizer b]
  exact Nat.mul_dvd_mul hc2 hC8


/-- Centralizers of orders four and ten cannot both occur in a finite ah-group. -/
theorem card_centralizer_ne_ten_of_centralizer_four {G : Type*} [Group G] [Fintype G]
    (h : HasDistinctConjClassSizes G) {z : G}
    (h4 : Nat.card (Subgroup.centralizer ({z} : Set G)) = 4) (x : G) :
    Nat.card (Subgroup.centralizer ({x} : Set G)) ≠ 10 := by
  intro h10
  have hd4 : 4 ∣ Nat.card G := h4 ▸ (Subgroup.centralizer ({z} : Set G)).card_subgroup_dvd_card
  have hx : x ≠ 1 := by
    rintro rfl
    have ht : Subgroup.centralizer ({1} : Set G) = ⊤ := by
      rw [Subgroup.centralizer_eq_top_iff_subset]; simp
    rw [ht, Subgroup.card_top] at h10
    omega
  have ho := orderOf_eq_of_card_centralizer_eq_mul_primes h hx Nat.prime_two
    (by decide : Nat.Prime 5) (by decide) h10
  have h16 := sixteen_dvd_card_of_orderOf_eq_ten h ho
  obtain ⟨P,hP⟩ := exists_sylow_two_card_le_eight_of_centralizer_four h h4
  have hP16 := Nat.le_of_dvd Nat.card_pos (P.pow_dvd_card_of_pow_dvd_card (n := 4) h16)
  norm_num at hP16
  omega

end

section

/-- If all elements of order four in a solvable ah-group are conjugate, a Sylow subgroup
of order eight contains two distinct commuting involutions. -/
theorem exists_distinct_commuting_involutions_of_sylow_card_eight_of_order_four_fusion
    {G : Type*} [Group G] [Fintype G] [Group.IsSolvable G] [Nontrivial G]
    (h : HasDistinctConjClassSizes G) (P : Sylow 2 G) (hP : Nat.card P = 8)
    (hf : ∀ x y : G, orderOf x = 4 → orderOf y = 4 → IsConj x y) :
    ∃ s t : P, orderOf s = 2 ∧ orderOf t = 2 ∧ s ≠ t ∧ Commute s t := by
  classical
  have : Nontrivial P := Finite.one_lt_card_iff_nontrivial.mp (hP ▸ (by decide : 1 < 8))
  have hc := P.isPGroup'.center_nontrivial
  have h2 := (P.isPGroup'.to_subgroup (Subgroup.center P)).card_eq_or_dvd.resolve_left
    (fun he => (not_nontrivial_iff_subsingleton.mpr (Nat.card_eq_one_iff_unique.mp he).1) hc)
  obtain ⟨t0,ht0⟩ := exists_prime_orderOf_dvd_card' 2 h2
  let t := t0.1
  have ht : orderOf t = 2 := (Subgroup.orderOf_coe t0).trans ht0
  by_contra hno
  have hun {a : P} (ha : orderOf a = 2) : a = t := by
    by_contra hne
    exact hno ⟨a,t,ha,ht,hne,Subgroup.mem_center_iff.mp t0.2 a⟩
  have hfour {a : P} (h1 : a ≠ 1) (ht' : a ≠ t) : orderOf a = 4 := by
    have hd := orderOf_dvd_natCard a
    change orderOf a ∣ Nat.card P.1 at hd
    rw [hP] at hd
    have h8 : orderOf a ≠ 8 := by
      intro h8
      have : IsCyclic P := isCyclic_of_orderOf_eq_card a (h8.trans hP.symm)
      have hh := card_sylow_two_le_two_of_isCyclic h P
      omega
    have h2' : orderOf a ≠ 2 := fun he => ht' (hun he)
    have h1' : orderOf a ≠ 1 := fun he => h1 (orderOf_eq_one_iff.mp he)
    have hb := Nat.le_of_dvd (by decide : 0 < 8) hd
    interval_cases n : orderOf a <;> omega
  have huniv : (Finset.univ : Finset P).card = 8 := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hP
  obtain ⟨a, ha⟩ : ∃ a : P, a ∉ ({1,t} : Finset P) := by
    by_contra! hh
    have he := Finset.eq_univ_iff_forall.mpr hh
    have hb := (Finset.card_le_two (a := (1 : P)) (b := t))
    rw [he, huniv] at hb
    omega
  have ha4 : orderOf a = 4 := hfour (fun he => ha (by simp [he])) (fun he => ha (by simp [he]))
  obtain ⟨b,hb⟩ : ∃ b : P, b ∉ ({1,t,a⁻¹,a⁻¹*t} : Finset P) := by
    by_contra! hh
    have he := Finset.eq_univ_iff_forall.mpr hh
    have hle := (Finset.card_le_four (a := (1 : P)) (b := t) (c := a⁻¹) (d := a⁻¹*t))
    rw [he, huniv] at hle
    omega
  have hb4 : orderOf b = 4 := hfour (fun he => hb (by simp [he])) (fun he => hb (by simp [he]))
  have hab4 : orderOf (a*b) = 4 := by
    apply hfour
    · intro he
      exact hb (by simp [eq_inv_of_mul_eq_one_right he])
    · intro he
      have hh : b = a⁻¹ * t := by rw [← he]; group
      exact hb (by simp [hh])
  let f := Abelianization.of (G := G)
  have hsame {u v : P} (hu : orderOf u = 4) (hv : orderOf v = 4) :
      f (u : G) = f (v : G) := by
    obtain ⟨c,hc⟩ := isConj_iff.mp (hf u v ((Subgroup.orderOf_coe u).trans hu) ((Subgroup.orderOf_coe v).trans hv))
    have eqn := congrArg f hc
    simpa [mul_comm (f c) (f (u : G))] using eqn
  have ha1 : f (a : G) = 1 := by
    have he := hsame hab4 ha4
    change f (a.1 * b.1) = f a.1 at he
    rw [map_mul, hsame hb4 ha4] at he
    exact mul_eq_left.mp he
  have ht1 : f (t : G) = 1 := by
    have ho : orderOf (a^2) = 2 := by rw [orderOf_pow_of_dvd (by decide : 2 ≠ 0) (ha4 ▸ (by decide : 2 ∣ 4)), ha4]
    rw [← hun ho]
    change f ((a : G)^2) = 1
    rw [map_pow, ha1, one_pow]
  have hder : P.1 ≤ commutator G := by
    intro u hu
    rw [← Abelianization.ker_of]
    change u ∈ f.ker
    apply MonoidHom.mem_ker.mpr
    let w : P := ⟨u,hu⟩
    by_cases h1 : w = 1
    · rw [show u = 1 from congrArg Subtype.val h1, map_one]
    by_cases ht' : w = t
    · rw [show u = t.1 from congrArg Subtype.val ht']; exact ht1
    exact (hsame (hfour h1 ht') ha4).trans ha1
  have : Nontrivial (G ⧸ commutator G) := by
    by_contra hn
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial G).ne
      (QuotientGroup.subgroup_eq_top_of_subsingleton _ (not_nontrivial_iff_subsingleton.mp hn))
  have h2quot : 2 ∣ Nat.card (G ⧸ commutator G) := by
    apply two_dvd_card_of_all_real
    intro u
    obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective (commutator G) u
    simpa only [map_inv] using (QuotientGroup.mk' (commutator G)).map_isConj (isConj_inv h v)
  exact P.not_dvd_index (h2quot.trans (Subgroup.index_dvd_of_le hder))

end

section

section FiveSylow
variable {G : Type*} [Group G] [Fintype G]

/-- An order-four element has centralizer of order four unless sixteen divides the group order. -/
theorem card_centralizer_order_four_of_not_sixteen_dvd (h : HasDistinctConjClassSizes G)
    (hn : ¬16 ∣ Nat.card G) {a : G} (ha : orderOf a = 4) :
    Nat.card (Subgroup.centralizer ({a} : Set G)) = 4 := by
  classical
  let C := Subgroup.centralizer ({a} : Set G)
  have hc4 := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr
    (show a ∈ C from Subgroup.mem_centralizer_singleton_iff.mpr rfl))
  rw [Nat.card_zpowers, ha] at hc4
  obtain ⟨m, hm⟩ := hc4
  by_contra hne
  have hm1 : m ≠ 1 := fun he => hne (by simpa [he] using hm)
  obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hm1
  by_cases hp2 : p = 2
  · subst p
    have h8 : 8 ∣ Nat.card C := hm ▸ Nat.mul_dvd_mul_left 4 hpm
    have hr := two_dvd_conjClassCard_of_isConj_inv (isConj_inv h a) (fun he => by
      have ho := orderOf_dvd_of_pow_eq_one he
      rw [ha] at ho
      omega)
    exact hn (conjClassCard_mk_mul_card_centralizer a ▸ Nat.mul_dvd_mul hr h8)
  · let : Fact p.Prime := ⟨hp⟩
    obtain ⟨y,hy⟩ := exists_prime_orderOf_dvd_card' (G := C) p
      (hpm.trans (hm ▸ Nat.dvd_mul_left m 4))
    have hy' : orderOf (y : G) = p := (Subgroup.orderOf_coe y).trans hy
    have hco : (4 : ℕ).Coprime p := by
      exact ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)).pow_left 2
    have hprod : orderOf (a * (y : G)) = 4*p :=
      (Commute.orderOf_mul_eq_mul_orderOf_of_coprime
        (show Commute a (y : G) from (Subgroup.mem_centralizer_singleton_iff.mp y.2).symm)
        (by rwa [ha, hy'])).trans (by rw [ha,hy'])
    have hbound := orderOf_mul_totient_dvd_card h (a * (y : G))
    rw [hprod, Nat.totient_mul hco, Nat.totient_prime hp] at hbound
    obtain ⟨k, hk⟩ := hp.even_sub_one hp2
    apply hn
    apply Dvd.dvd.trans _ hbound
    exact ⟨p*k, by rw [hk, show Nat.totient 4 = 2 by decide]; ring⟩

theorem isConj_order_four_of_not_sixteen_dvd (h : HasDistinctConjClassSizes G)
    (hn : ¬16 ∣ Nat.card G) {a b : G} (ha : orderOf a = 4) (hb : orderOf b = 4) :
    IsConj a b := isConj_of_card_centralizer_eq h
  ((card_centralizer_order_four_of_not_sixteen_dvd h hn ha).trans
    (card_centralizer_order_four_of_not_sixteen_dvd h hn hb).symm)

private theorem eight_dvd_quotient_card_of_five_image (h : HasDistinctConjClassSizes G)
    (K : Subgroup G) [K.Normal] {x : G} (hx : orderOf x = 5)
    (hu : orderOf (QuotientGroup.mk' K x) = 5) : 8 ∣ Nat.card (G ⧸ K) := by
  classical
  let f := QuotientGroup.mk' K
  let q := f x
  obtain ⟨b, hb⟩ := isConj_iff.mp (isConj_pow_of_coprime h x (by rw [hx]; decide :
    (2 : ℕ).Coprime (orderOf x)))
  let c := f b
  have hact : c * q * c⁻¹ = q^2 := by simpa only [map_mul, map_inv, map_pow] using congrArg f hb
  have iter (i : ℕ) : c^i * q * (c^i)⁻¹ = q ^ (2 ^ i) := by
    induction i with
    | zero => simp
    | succ i ih =>
      calc
        _ = c^i * (c * q * c⁻¹) * (c^i)⁻¹ := by rw [pow_succ]; group
        _ = (c^i * q * (c^i)⁻¹)^2 := by rw [hact, conj_pow]
        _ = _ := by rw [ih, ← pow_mul, pow_succ]
  have he : q ^ (2^orderOf c) = q ^ (1 : ℕ) := by
    rw [← iter, pow_orderOf_eq_one]; simp
  have hm := pow_eq_pow_iff_modEq.mp he
  rw [show orderOf q = 5 from hu] at hm
  let v := ZMod.unitOfCoprime 2 (by decide : Nat.Coprime 2 5)
  have ho : orderOf v = 4 := orderOf_eq_prime_pow (p := 2) (n := 1) (by decide) (by decide)
  have hv : v^orderOf c = 1 := by
    apply Units.ext
    change (2 : ZMod 5) ^ orderOf c = 1
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using
      ((ZMod.natCast_eq_natCast_iff _ _ _).mpr hm)
  have hc4 := orderOf_dvd_of_pow_eq_one hv
  rw [ho] at hc4
  have hrc : IsConj c c⁻¹ := by simpa only [map_inv] using f.map_isConj (isConj_inv h b)
  have hrl := two_dvd_conjClassCard_of_isConj_inv hrc (fun he => by
    have hbad := hc4.trans (orderOf_dvd_of_pow_eq_one he)
    omega)
  have hC := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr
    (show c ∈ Subgroup.centralizer ({c} : Set (G ⧸ K)) from Subgroup.mem_centralizer_singleton_iff.mpr rfl))
  rw [Nat.card_zpowers] at hC
  exact conjClassCard_mk_mul_card_centralizer c ▸ Nat.mul_dvd_mul hrl (hc4.trans hC)

/-- A quotient cannot have an element of order ten if sixteen does not divide the
order of the original ah-group. -/
private theorem no_order_ten_quotient (h : HasDistinctConjClassSizes G) (hn : ¬16 ∣ Nat.card G)
    (K : Subgroup G) [K.Normal] (u : G ⧸ K) : orderOf u ≠ 10 := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K u
  intro hu
  have hd := orderOf_map_dvd (QuotientGroup.mk' K) x
  rw [hu] at hd
  exact hn (sixteen_dvd_card_of_orderOf_eq_ten h (orderOf_pow_orderOf_div (orderOf_pos x).ne' hd))

/-- In an abelian normal subgroup, an involution inverts every element of order dividing
five if the ambient group has no element of order ten. -/
private theorem involution_inverts_five {Q : Type*} [Group Q]
    (hn : ∀ q : Q, orderOf q ≠ 10) (A : Subgroup Q) [A.Normal] [IsMulCommutative A]
    (s : Q) (hs : orderOf s = 2) (v : A) (hv : v ^ 5 = 1) :
    MulAut.conjNormal s v = v⁻¹ := by
  let a : MulAut A := MulAut.conjNormal s
  let w := v * a v
  have h5 : w ^ 5 = 1 := by
    change (v * a v) ^ 5 = 1
    rw [(show Commute v (a v) from mul_comm' _ _).mul_pow, ← map_pow, hv, map_one, mul_one]
  have hwc : a w = w := by
    have ha2 : a (a v) = v := by
      change (((MulAut.conjNormal (H := A) s * MulAut.conjNormal s : MulAut A)) v) = v
      rw [← map_mul, ← pow_two, ← hs, pow_orderOf_eq_one, map_one]; rfl
    change a (v * a v) = v * a v
    rw [map_mul, ha2, mul_comm']
  by_contra hne
  have hw1 : w ≠ 1 := fun h => hne ((mul_eq_one_iff_inv_eq.mp h).symm)
  have ho : orderOf w = 5 := ((Nat.dvd_prime (by decide : Nat.Prime 5)).mp
    (orderOf_dvd_of_pow_eq_one h5)).resolve_left fun h => hw1 (orderOf_eq_one_iff.mp h)
  have hwo : orderOf (w : Q) = 5 := (Subgroup.orderOf_coe w).trans ho
  have hc : Commute s (w : Q) := mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hwc)
  apply hn (s * w)
  rw [Commute.orderOf_mul_eq_mul_orderOf_of_coprime hc (by rw [hs,hwo]; decide), hs, hwo]

/-- Two commuting distinct involutions cannot survive together in a section with a normal
abelian five-layer when the original group order has 2-part at most eight. -/
private theorem no_five_of_involution_pair (h : HasDistinctConjClassSizes G) [Group.IsSolvable G]
    (hn : ¬16 ∣ Nat.card G)
    (pair : 8 ∣ Nat.card G → ∃ s t : G, orderOf s = 2 ∧ orderOf t = 2 ∧ s ≠ t ∧ Commute s t) :
    ¬ 5 ∣ Nat.card G := by
  classical
  intro h5
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := G) 5 h5
  have hx1 : x ≠ 1 := fun he => (by decide : (1 : ℕ) ≠ 5) (by simpa only [he, orderOf_one] using hx)
  obtain ⟨i, hi, hni⟩ : ∃ i, x ∈ derivedSeries G i ∧ x ∉ derivedSeries G (i+1) := by
    by_contra! hall
    apply not_isSolvable_of_mem_derivedSeries hx1 _ inferInstance
    intro j
    induction j with
    | zero => simp
    | succ j hj => exact hall j hj
  let D := derivedSeries G i
  let K := derivedSeries G (i+1)
  let f := QuotientGroup.mk' K
  let u := f x
  let A := D.map f
  have : A.Normal := (derivedSeries_normal G i).map f (QuotientGroup.mk'_surjective K)
  have : IsMulCommutative A := by
    apply Subgroup.commutator_self_eq_bot_iff.mp
    change ⁅D.map f, D.map f⁆ = ⊥
    rw [← Subgroup.map_commutator, Subgroup.map_eq_bot_iff]
    exact le_of_eq (by rw [QuotientGroup.ker_mk']; rfl)
  have hu : orderOf u = 5 := by
    have hd := orderOf_map_dvd f x
    rw [hx] at hd
    exact ((Nat.dvd_prime (by decide : Nat.Prime 5)).mp hd).resolve_left fun he =>
      hni ((QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp he))
  let v : A := ⟨u, x, hi, rfl⟩
  have hv5 : v^5 = 1 := Subtype.ext (hu ▸ pow_orderOf_eq_one u)
  have h8 := eight_dvd_quotient_card_of_five_image h K hx hu
  obtain ⟨s,t,hs,ht,hne,hst⟩ := pair (h8.trans K.card_quotient_dvd_card)
  have hk : ¬2 ∣ Nat.card K := fun hd => hn
    (Subgroup.card_eq_card_quotient_mul_card_subgroup K ▸ Nat.mul_dvd_mul h8 hd)
  have him (y : G) (hy : orderOf y = 2) : orderOf (f y) = 2 := by
    have hd := orderOf_map_dvd f y
    rw [hy] at hd
    apply ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left
    intro ho
    have hyK : y ∈ K := (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp ho)
    have hbad := orderOf_dvd_natCard (⟨y,hyK⟩ : K)
    apply hk
    rwa [Subgroup.orderOf_mk, hy] at hbad
  have hst2 : orderOf (s*t) = 2 := by
    have hpow : (s*t)^2 = 1 := by
      rw [hst.mul_pow, ← hs, pow_orderOf_eq_one, hs, ← ht, pow_orderOf_eq_one, one_mul]
    refine ((Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hpow)).resolve_left ?_
    intro h1
    apply hne
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_left (by rw [← pow_two, ← ht, pow_orderOf_eq_one])
    exact (mul_eq_one_iff_eq_inv.mp (orderOf_eq_one_iff.mp h1)).trans hti
  have hinv (y : G) (hy : orderOf y = 2) : MulAut.conjNormal (f y) v = v⁻¹ :=
    involution_inverts_five (no_order_ten_quotient h hn K) A (f y) (him y hy) v hv5
  have hprod := hinv (s*t) hst2
  rw [map_mul, map_mul, MulAut.mul_apply, hinv t ht, map_inv, hinv s hs, inv_inv] at hprod
  have hv2 : v^2 = 1 := by
    rw [pow_two]
    exact mul_eq_one_iff_eq_inv.mpr hprod
  have hbad := orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hv2 : u^2 = 1)
  rw [hu] at hbad
  omega

/-- A prime factor five in a nontrivial solvable ah-group forces sixteen to divide its
order. An order-five derived layer cannot carry the fixed-point-free action of two distinct
commuting involutions. -/
theorem sixteen_dvd_card_of_five_dvd [Group.IsSolvable G] [Nontrivial G]
    (h : HasDistinctConjClassSizes G) (h5 : 5 ∣ Nat.card G) : 16 ∣ Nat.card G := by
  by_contra hn
  apply no_five_of_involution_pair h hn _ h5
  intro h8
  let P : Sylow 2 G := Classical.choice inferInstance
  obtain ⟨n, hP⟩ := P.isPGroup'.exists_card_eq
  have h8P := P.pow_dvd_card_of_pow_dvd_card (n := 3) h8
  rw [hP] at h8P
  have hlo : 3 ≤ n := (Nat.pow_dvd_pow_iff_le_right (by decide : 1 < 2)).mp h8P
  have hup : n < 4 := by
    by_contra! hh
    exact hn ((Nat.pow_dvd_pow 2 hh).trans
      (hP ▸ (P : Subgroup G).card_subgroup_dvd_card))
  have hcard : Nat.card P = 8 := by rw [hP, show n = 3 by omega]; decide
  obtain ⟨s,t,hs,ht,hne,hst⟩ := exists_distinct_commuting_involutions_of_sylow_card_eight_of_order_four_fusion
    h P hcard (fun _ _ => isConj_order_four_of_not_sixteen_dvd h hn)
  exact ⟨s,t,(Subgroup.orderOf_coe s).trans hs, (Subgroup.orderOf_coe t).trans ht,
    fun he => hne (Subtype.ext he), congrArg Subtype.val hst.eq⟩

end FiveSylow

end

section

/-- A nontrivial element of an abelian normal subgroup has fewer conjugates
than centralizing elements. -/
theorem conjClassCard_lt_card_centralizer_of_mem_abelian_normal
    {G : Type*} [Group G] [Finite G] (A : Subgroup G) [A.Normal] [IsMulCommutative A]
    {x : G} (hx : x ∈ A) (hne : x ≠ 1) :
    conjClassCard (ConjClasses.mk x) < Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  have hlt : conjClassCard (ConjClasses.mk x) < Nat.card A := by
    change Nat.card (ConjClasses.mk x).carrier < Nat.card (A : Set G)
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
    apply fun hs => Set.ncard_lt_ncard hs (Set.toFinite _)
    apply Set.ssubset_iff_exists.mpr
    constructor
    · intro y hy
      obtain ⟨g, rfl⟩ := isConj_iff.mp (show IsConj x y from hy)
      exact Subgroup.Normal.conj_mem inferInstance x hx g
    · exact ⟨1, A.one_mem, fun he => hne (isConj_one_right.mp (show IsConj x 1 from he).symm)⟩
  exact hlt.trans_le <| Subgroup.card_le_of_le (show A ≤ Subgroup.centralizer ({x} : Set G) from
    fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (setLike_mul_comm hy hx))

/-- The last derived subgroup containing an element gives a quotient in which the
element survives and belongs to an abelian normal subgroup. -/
private theorem exists_abelian_normal_layer {G : Type*} [Group G] [Group.IsSolvable G]
    {x : G} (hx : x ≠ 1) :
    ∃ (K : Subgroup G) (_ : K.Normal) (A : Subgroup (G ⧸ K)), A.Normal ∧
      IsMulCommutative A ∧ QuotientGroup.mk' K x ∈ A ∧ QuotientGroup.mk' K x ≠ 1 := by
  obtain ⟨i, hi, hni⟩ : ∃ i, x ∈ derivedSeries G i ∧ x ∉ derivedSeries G (i+1) := by
    by_contra! hall
    apply not_isSolvable_of_mem_derivedSeries hx _ inferInstance
    intro j
    induction j with
    | zero => simp
    | succ j hj => exact hall j hj
  let D := derivedSeries G i
  let K := derivedSeries G (i+1)
  let f := QuotientGroup.mk' K
  let A := D.map f
  have : A.Normal := (derivedSeries_normal G i).map f (QuotientGroup.mk'_surjective K)
  have : IsMulCommutative A := by
    apply Subgroup.commutator_self_eq_bot_iff.mp
    change ⁅D.map f, D.map f⁆ = ⊥
    rw [← Subgroup.map_commutator, Subgroup.map_eq_bot_iff]
    exact le_of_eq (by rw [QuotientGroup.ker_mk']; rfl)
  have hne : f x ≠ 1 := fun he => hni ((QuotientGroup.eq_one_iff _).mp he)
  exact ⟨K, inferInstance, A, inferInstance, inferInstance, ⟨x, hi, rfl⟩, hne⟩

/-- Every nonidentity element of a finite solvable group survives in a quotient
whose order is at most m(m−1), where m is its centralizer order in the original group. -/
theorem exists_small_quotient_of_centralizer {G : Type*} [Group G] [Fintype G] [Group.IsSolvable G]
    {x : G} (hx : x ≠ 1) :
    ∃ (K : Subgroup G) (_ : K.Normal), QuotientGroup.mk' K x ≠ 1 ∧
      Nat.card (G ⧸ K) ≤ (Nat.card (Subgroup.centralizer ({x} : Set G)) - 1) *
        Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  obtain ⟨K, hK, A, hA, hcomm, hxA, hne⟩ := exists_abelian_normal_layer hx
  let f := QuotientGroup.mk' K
  refine ⟨K, inferInstance, hne, ?_⟩
  have hlt := conjClassCard_lt_card_centralizer_of_mem_abelian_normal A (x := f x) hxA hne
  have hle := card_centralizer_quotient_le K x
  change Nat.card (Subgroup.centralizer ({f x} : Set (G ⧸ K))) ≤ _ at hle
  rw [← conjClassCard_mk_mul_card_centralizer (f x)]
  exact Nat.mul_le_mul (by omega) hle

/-- A centralizer of order nine forces a quotient of one of six specific orders in
which the element survives. Its image lies in a normal abelian subgroup of order three or nine. -/
theorem exists_quotient_of_centralizer_nine {G : Type*} [Group G] [Fintype G]
    [Group.IsSolvable G] [Nontrivial G] (h : HasDistinctConjClassSizes G) (x : G)
    (hc : Nat.card (Subgroup.centralizer ({x} : Set G)) = 9) :
    ∃ (K : Subgroup G) (_ : K.Normal) (B : Subgroup (G ⧸ K)), B.Normal ∧
      IsMulCommutative B ∧ QuotientGroup.mk' K x ∈ B ∧ orderOf (QuotientGroup.mk' K x) = 3 ∧
      (Nat.card B = 3 ∨ Nat.card B = 9) ∧
      Nat.card (G ⧸ K) ∈ ({6, 12, 18, 36, 54, 72} : Finset ℕ) := by
  classical
  have hx : x ≠ 1 := by
    rintro rfl
    have ht : Subgroup.centralizer ({1} : Set G) = ⊤ := by
      rw [Subgroup.centralizer_eq_top_iff_subset]; simp
    rw [ht, Subgroup.card_top] at hc
    have := two_dvd_card h
    omega
  have hx9 : orderOf x ∣ 9 := by
    have hxC : x ∈ Subgroup.centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr rfl
    simpa only [Nat.card_zpowers, hc] using Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hxC)
  obtain ⟨K, hK, A, hA, ha, hxA, hne⟩ := exists_abelian_normal_layer hx
  let f := QuotientGroup.mk' K
  let u : A := ⟨f x, hxA⟩
  have h9 : orderOf u ∣ 3 ^ 2 := (Subgroup.orderOf_coe u).symm ▸ (orderOf_map_dvd f x).trans hx9
  have hpu := IsPGroup.of_card_dvd_pow (p := 3) (G := Subgroup.zpowers u)
    (n := 2) (Nat.card_zpowers u ▸ h9)
  obtain ⟨P, hP⟩ := hpu.exists_le_sylow
  have : (P : Subgroup A).Characteristic := P.characteristic_of_normal (Subgroup.normal_of_isMulCommutative _)
  let B := (P : Subgroup A).map A.subtype
  have huB : f x ∈ B := ⟨u, hP (Subgroup.mem_zpowers u), rfl⟩
  have : IsMulCommutative B := inferInstanceAs (IsMulCommutative ((P : Subgroup A).map A.subtype))
  let C := Subgroup.centralizer ({f x} : Set (G ⧸ K))
  have hBC : B ≤ C := fun _ hy => Subgroup.mem_centralizer_singleton_iff.mpr (setLike_mul_comm hy huB)
  have hC : Nat.card C ≤ 9 := (card_centralizer_quotient_le K x).trans hc.le
  have hBCcard := Subgroup.card_dvd_of_le hBC
  have hBle := (Subgroup.card_le_of_le hBC).trans hC
  have hb1 : Nat.card B ≠ 1 := fun he => hne (Subgroup.mem_bot.mp (Subgroup.card_eq_one.mp he ▸ huB))
  have hB : Nat.card B = 3 ∨ Nat.card B = 9 := by
    obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
    have he : Nat.card B = 3 ^ k := (Subgroup.card_map_of_injective A.subtype_injective).trans hk
    have hlt : k < 3 := by
      by_contra! hn
      have hh := Nat.pow_le_pow_right (by decide : 0 < 3) hn
      rw [← he] at hh
      omega
    interval_cases k
    · exact (hb1 he).elim
    · exact Or.inl he
    · exact Or.inr he
  have horder : orderOf (f x) = 3 := by
    have hd := (orderOf_map_dvd f x).trans hx9
    change orderOf (f x) ∣ 3 ^ 2 at hd
    obtain ⟨k, hk, horder⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
    interval_cases k
    · exact (hne (orderOf_eq_one_iff.mp horder)).elim
    · exact horder
    · have hgen : Subgroup.zpowers (f x) = B :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr huB) (by
          rw [Nat.card_zpowers, horder]; exact hBle)
      have : IsCyclic B := hgen ▸ inferInstanceAs (IsCyclic (Subgroup.zpowers (f x)))
      have hcop := (show (2 : ℕ).Coprime 9 by decide).coprime_dvd_right hx9
      have hsmall := orderOf_image_dvd_three h f B hcop huB
      rw [horder] at hsmall
      exact ((by decide : ¬ 3 ^ 2 ∣ 3) hsmall).elim
  let cl := conjClassCard (ConjClasses.mk (f x))
  have heven : 2 ∣ cl := by
    apply two_dvd_conjClassCard_of_isConj_inv
    · simpa only [map_inv] using f.map_isConj (isConj_inv h x)
    · intro he
      have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one he) ((orderOf_map_dvd f x).trans hx9)
      exact hne (orderOf_eq_one_iff.mp (Nat.dvd_one.mp (show orderOf (f x) ∣ 1 from hd)))
  have horb : cl < Nat.card B := by
    change Nat.card (ConjClasses.mk (f x)).carrier < Nat.card (B : Set (G ⧸ K))
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
    apply fun hs => Set.ncard_lt_ncard hs (Set.toFinite _)
    apply Set.ssubset_iff_exists.mpr
    refine ⟨?_, 1, B.one_mem, fun he => hne (isConj_one_right.mp (show IsConj (f x) 1 from he).symm)⟩
    intro y hy
    obtain ⟨t, rfl⟩ := isConj_iff.mp (show IsConj (f x) y from hy)
    exact Subgroup.Normal.conj_mem inferInstance (f x) huB t
  have hpos : 0 < cl := by
    let : Nonempty (ConjClasses.mk (f x)).carrier := ⟨⟨f x, ConjClasses.mem_carrier_mk⟩⟩
    exact Nat.card_pos
  have hCpos : 0 < Nat.card C := Nat.card_pos
  refine ⟨K, hK, B, inferInstance, inferInstance, huB, horder, hB, ?_⟩
  rw [← conjClassCard_mk_mul_card_centralizer (f x)]
  change cl * Nat.card C ∈ _
  rcases hB with hb | hb
  · rw [hb] at hBCcard horb
    have hcl : cl = 2 := by omega
    rw [hcl]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · rw [hb] at hBCcard horb
    have hC9 : Nat.card C = 9 := by omega
    rw [hC9]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega

/-- No integer below 120 can be expressed as a sum of distinct divisors each at most a quarter of it. -/
private theorem sum_divisors_le_quarter_lt (n : ℕ) (hpos : 0 < n) (hn : n < 120) :
    ∑ d ∈ (Finset.range (n / 4 + 1)).filter (· ∣ n), d < n := by
  have key : ∀ i : Fin 120, 0 < i.val →
      ∑ d ∈ (Finset.range (i.val / 4 + 1)).filter (· ∣ i.val), d < i.val := by decide
  exact key ⟨n, hn⟩ hpos

/-- All nontrivial finite solvable ah-groups of order below 120 are S₃. -/
theorem nonempty_mulEquiv_perm_three_of_card_lt_120 {G : Type*} [Group G] [Fintype G]
    [Group.IsSolvable G] [Nontrivial G] (h : HasDistinctConjClassSizes G) (hn : Nat.card G < 120) :
    Nonempty (G ≃* Equiv.Perm (Fin 3)) := by
  classical
  by_contra hbad
  let n := Nat.card G
  let s := (Finset.range (n / 4 + 1)).filter (· ∣ n)
  let c := conjClassCard (G := G)
  have hmin (g : G) : 4 ≤ Nat.card (Subgroup.centralizer ({g} : Set G)) := by
    let C := Subgroup.centralizer ({g} : Set G)
    have hc : 0 < Nat.card C := Nat.card_pos
    have hc1 : Nat.card C ≠ 1 := by
      intro he
      have heq := Subgroup.card_eq_one.mp he
      have hg : g ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
      rw [heq, Subgroup.mem_bot] at hg
      have ht : C = ⊤ := by
        change Subgroup.centralizer ({g} : Set G) = ⊤
        rw [hg, Subgroup.centralizer_eq_top_iff_subset]; simp
      exact bot_ne_top (heq.symm.trans ht)
    have hc2 : Nat.card C ≠ 2 := fun he => hbad (nonempty_mulEquiv_perm_three_of_card_centralizer_eq_two h he)
    have hc3 : Nat.card C ≠ 3 := fun he => hbad (nonempty_mulEquiv_perm_three_of_card_centralizer_eq_three h he)
    change 4 ≤ Nat.card C
    omega
  have hsub : (Finset.univ.image c) ⊆ s := by
    intro d hd
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective a
    have he := conjClassCard_mk_mul_card_centralizer g
    have h4 := Nat.mul_le_mul_left (conjClassCard (ConjClasses.mk g)) (hmin g)
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_range.mpr
      change conjClassCard (ConjClasses.mk g) < Nat.card G / 4 + 1
      rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le (by decide)]
      exact h4.trans_eq he
    · exact ⟨_, he.symm⟩
  have hsum : ∑ a : ConjClasses G, c a = n := by
    rw [show n = Nat.card G from rfl, ← Group.sum_card_conj_classes_eq_card G, finsum_eq_sum_of_fintype]
    exact Finset.sum_congr rfl (fun a _ => Nat.card_coe_set_eq a.carrier)
  have hle : n ≤ ∑ d ∈ s, d := by
    rw [← hsum]
    calc
      _ = ∑ d ∈ Finset.univ.image c, d := (Finset.sum_image (f := fun d : ℕ => d) h.injOn).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset hsub
  exact (Nat.not_lt.mpr hle) (sum_divisors_le_quarter_lt n Nat.card_pos hn)

/-- A nontrivial element in an abelian normal subgroup with centralizer of size at most
eleven suffices to recognize S₃ in a finite solvable ah-group. -/
theorem nonempty_mulEquiv_perm_three_of_small_centralizer_in_abelian_normal
    {G : Type*} [Group G] [Fintype G] [Group.IsSolvable G] [Nontrivial G]
    (h : HasDistinctConjClassSizes G) (A : Subgroup G) [A.Normal] [IsMulCommutative A]
    {x : G} (hx : x ∈ A) (hx1 : x ≠ 1)
    (hm : Nat.card (Subgroup.centralizer ({x} : Set G)) ≤ 11) : Nonempty (G ≃* Equiv.Perm (Fin 3)) := by
  apply nonempty_mulEquiv_perm_three_of_card_lt_120 h
  rw [← conjClassCard_mk_mul_card_centralizer x]
  have hlt := conjClassCard_lt_card_centralizer_of_mem_abelian_normal A hx hx1
  exact lt_of_le_of_lt (Nat.mul_le_mul (show conjClassCard (ConjClasses.mk x) ≤ 10 from by omega) hm) (by decide)

end

section

/-- If passing to a quotient preserves a centralizer cardinality, the conjugacy class
is the full preimage of its image class. -/
theorem isConj_of_isConj_quotient_of_card_centralizer_eq {G : Type*} [Group G] [Finite G]
    (K : Subgroup G) [K.Normal] {x y : G}
    (he : Nat.card (Subgroup.centralizer ({QuotientGroup.mk' K x} : Set (G ⧸ K))) =
      Nat.card (Subgroup.centralizer ({x} : Set G)))
    (hy : IsConj (QuotientGroup.mk' K x) (QuotientGroup.mk' K y)) : IsConj x y := by
  let f := QuotientGroup.mk' K
  let S := (ConjClasses.mk x).carrier
  let T := (ConjClasses.mk (f x)).carrier
  have hsub : S ⊆ f ⁻¹' T := fun _ ha => f.map_isConj ha
  have hcard : Nat.card (f ⁻¹' T) = Nat.card S := by
    rw [show Nat.card (f ⁻¹' T) = Nat.card K * Nat.card T from QuotientGroup.card_preimage_mk K T]
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := Subgroup.centralizer ({x} : Set G)))
    calc
      Nat.card K * Nat.card T * Nat.card (Subgroup.centralizer ({x} : Set G)) =
          Nat.card K * (conjClassCard (ConjClasses.mk (f x)) *
            Nat.card (Subgroup.centralizer ({f x} : Set (G ⧸ K)))) := by rw [he, ← mul_assoc]; rfl
      _ = Nat.card G := by rw [conjClassCard_mk_mul_card_centralizer, mul_comm,
          ← K.card_eq_card_quotient_mul_card_subgroup]
      _ = _ := (conjClassCard_mk_mul_card_centralizer x).symm
  have hsame : S = f ⁻¹' T := Set.eq_of_subset_of_ncard_le hsub (by
    simpa only [← Nat.card_coe_set_eq] using hcard.le)
  exact (hsame ▸ (show y ∈ f ⁻¹' T from hy) : y ∈ S)

/-- A normal subgroup with a coset consisting entirely of elements whose cubes are one
is nilpotent. Each element of the subgroup commutes with all its conjugates. -/
theorem isNilpotent_of_coset_cube {G : Type*} [Group G] [Finite G] (K : Subgroup G) [K.Normal]
    (x : G) (h : ∀ k : K, ((k : G) * x) ^ 3 = 1) : Group.IsNilpotent K := by
  let a : MulAut K := MulAut.conjNormal x
  have hx3 : x ^ 3 = 1 := by simpa only [Subgroup.coe_one, one_mul] using h 1
  have norm (t v : K) : v * (MulAut.conjNormal ((t : G) * x) v *
      MulAut.conjNormal ((t : G) * x) (MulAut.conjNormal ((t : G) * x) v)) = 1 := by
    apply Subtype.ext
    let y := (t : G) * x
    have hy : y ^ 3 = 1 := h t
    have hv : ((v : G) * y) ^ 3 = 1 := by simpa only [y, ← mul_assoc, Subgroup.coe_mul] using h (v * t)
    change (v : G) * ((y * v * y⁻¹) * (y * (y * v * y⁻¹) * y⁻¹)) = 1
    calc _ = ((v : G) * y) ^ 3 * (y ^ 3)⁻¹ := by simp only [pow_succ, pow_zero, one_mul]; group
         _ = 1 := by rw [hv, hy, inv_one, one_mul]
  have comm (v t : K) : Commute v (t * a v * t⁻¹) := by
    let b : MulAut K := MulAut.conjNormal ((t : G) * x)
    have hn : v * (b v * b (b v)) = 1 := norm t v
    have hr := congrArg Inv.inv (norm t v⁻¹)
    change (v⁻¹ * (b v⁻¹ * b (b v⁻¹)))⁻¹ = 1⁻¹ at hr
    simp only [map_inv, mul_inv_rev, inv_inv, inv_one, mul_assoc] at hr
    have hcomm : v * b v = b v * v := by
      calc _ = (b (b v))⁻¹ := eq_inv_of_mul_eq_one_left (by simpa only [mul_assoc] using hn)
           _ = b v * v := (eq_inv_of_mul_eq_one_right hr).symm
    have he : b v = t * a v * t⁻¹ := by
      apply Subtype.ext
      change ((t : G) * x) * v * ((t : G) * x)⁻¹ = t * (x * v * x⁻¹) * (t : G)⁻¹
      group
    exact he ▸ hcomm
  have ha3 : a ^ 3 = 1 := by
    change (MulAut.conjNormal x : MulAut K) ^ 3 = 1
    rw [← map_pow, hx3, map_one]
  have htr (v : K) : a (a (a v)) = v := congrArg (fun b : MulAut K => b v) ha3
  apply isNilpotent_of_commute_conjugates
  intro v w hv
  obtain ⟨t, rfl⟩ := isConj_iff.mp hv
  have h1 := comm v t
  have h2 : Commute v (t * a (a v) * t⁻¹) := by
    have hh := ((comm (a (a v)) t⁻¹).map (MulAut.conj t)).symm
    simpa only [htr, MulAut.conj_apply, inv_inv, mul_assoc, mul_inv_cancel_left,
      mul_inv_cancel_right, mul_inv_cancel, inv_mul_cancel, mul_one] using hh
  have hn : v * (a v * a (a v)) = 1 := by
    simpa only [Subgroup.coe_one, one_mul, a] using norm 1 v
  have hg : t * v * t⁻¹ = ((t * a v * t⁻¹) * (t * a (a v) * t⁻¹))⁻¹ := by
    conv_lhs => rw [eq_inv_of_mul_eq_one_left hn]
    group
  rw [hg]
  exact (h1.mul_right h2).inv_right

/-- For a three-element, preservation of the centralizer order in a quotient
forces the kernel to be nilpotent. -/
theorem isNilpotent_of_card_centralizer_eq_of_cube {G : Type*} [Group G] [Finite G]
    (K : Subgroup G) [K.Normal] {x : G} (hx : x ^ 3 = 1)
    (he : Nat.card (Subgroup.centralizer ({QuotientGroup.mk' K x} : Set (G ⧸ K))) =
      Nat.card (Subgroup.centralizer ({x} : Set G))) : Group.IsNilpotent K := by
  apply isNilpotent_of_coset_cube K x
  intro t
  let q := QuotientGroup.mk' K
  have ht : q (t : G) = 1 := (QuotientGroup.eq_one_iff _).mpr t.2
  have hq : IsConj (q x) (q ((t : G) * x)) := by rw [map_mul, ht, one_mul]
  obtain ⟨u, hu⟩ := isConj_iff.mp (isConj_of_isConj_quotient_of_card_centralizer_eq K he hq)
  rw [← hu, ← MulAut.conj_apply, ← map_pow, hx, map_one]

/-- In the centralizer-nine case for an element of order three, all but the two
smallest candidate quotient orders have nilpotent kernel. -/
theorem exists_quotient_of_three_element_centralizer_nine {G : Type*} [Group G] [Fintype G]
    [Group.IsSolvable G] [Nontrivial G] (h : HasDistinctConjClassSizes G) {x : G}
    (hx : x ^ 3 = 1) (hc : Nat.card (Subgroup.centralizer ({x} : Set G)) = 9) :
    ∃ (K : Subgroup G) (_ : K.Normal) (B : Subgroup (G ⧸ K)), B.Normal ∧
      IsMulCommutative B ∧ QuotientGroup.mk' K x ∈ B ∧ (Nat.card B = 3 ∨ Nat.card B = 9) ∧
      orderOf (QuotientGroup.mk' K x) = 3 ∧ Nat.card (G ⧸ K) ∈ ({6, 12, 18, 36, 54, 72} : Finset ℕ) ∧
      (12 < Nat.card (G ⧸ K) → Group.IsNilpotent K) := by
  obtain ⟨K, hK, B, hBn, hBa, hu, horder, hB, hQ⟩ := exists_quotient_of_centralizer_nine h x hc
  refine ⟨K, hK, B, hBn, hBa, hu, hB, horder, hQ, ?_⟩
  intro hlarge
  let u := QuotientGroup.mk' K x
  let C := Subgroup.centralizer ({u} : Set (G ⧸ K))
  have hle : Nat.card C ≤ 9 := (card_centralizer_quotient_le K x).trans hc.le
  have hBC : B ≤ C := fun _ hy => Subgroup.mem_centralizer_singleton_iff.mpr (setLike_mul_comm hy hu)
  apply isNilpotent_of_card_centralizer_eq_of_cube K hx
  rw [hc]
  change Nat.card C = 9
  rcases hB with hb | hb
  · have hdiv := Subgroup.card_dvd_of_le hBC
    rw [hb] at hdiv
    have hs : (ConjClasses.mk u).carrier ⊆ (B : Set (G ⧸ K)) := by
      intro y hy
      obtain ⟨t, rfl⟩ := isConj_iff.mp (show IsConj u y from hy)
      exact hBn.conj_mem u hu t
    have hlt : conjClassCard (ConjClasses.mk u) < Nat.card B := by
      change Nat.card (ConjClasses.mk u).carrier < Nat.card (B : Set (G ⧸ K))
      rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
      apply fun hs => Set.ncard_lt_ncard hs (Set.toFinite _)
      apply (Set.ssubset_iff_of_subset hs).mpr
      refine ⟨1, B.one_mem, fun he => ?_⟩
      have h1 : u = 1 := isConj_one_right.mp (show IsConj u 1 from he).symm
      change orderOf u = 3 at horder
      rw [h1, orderOf_one] at horder
      contradiction
    rw [hb] at hlt
    have hbound : Nat.card (G ⧸ K) ≤ 2 * Nat.card C := by
      rw [← conjClassCard_mk_mul_card_centralizer u]
      exact Nat.mul_le_mul_right _ (by omega)
    omega
  · have := Subgroup.card_le_of_le hBC
    omega

end

section

private theorem smooth_order_of_bounded_primes (n : ℕ) (hn : n ≠ 0)
    (hs : ∀ p : ℕ, p.Prime → p ∣ n → p ≤ 5) :
    ∃ a b c : ℕ, n = 2 ^ a * 3 ^ b * 5 ^ c := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases he : n = 1
    · exact ⟨0,0,0,by simpa using he⟩
    obtain ⟨p, hp, m, hm⟩ := Nat.exists_prime_and_dvd he
    have hm0 : m ≠ 0 := by rintro rfl; simp_all
    have hlt : m < n := hm ▸ (lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hm0) hp.one_lt)
    have hmn : m ∣ n := hm ▸ dvd_mul_left _ _
    obtain ⟨a,b,c,h⟩ := ih m hlt hm0 (fun q hq hd => hs q hq (hd.trans hmn))
    have hp5 := hs p hp ⟨m, hm⟩
    have hp2 := hp.two_le
    interval_cases p
    · exact ⟨a+1,b,c,by rw [hm,h]; ring⟩
    · exact ⟨a,b+1,c,by rw [hm,h]; ring⟩
    · norm_num at hp
    · exact ⟨a,b,c+1,by rw [hm,h]; ring⟩


end

section

open ConjugacyClassSizes Finset

section PrimeWeights

variable {G : Type*} [Group G] [Fintype G]

omit [Fintype G] in
private theorem card_centralizer_ne_one [Nontrivial G] (x : G) :
    Nat.card (Subgroup.centralizer ({x} : Set G)) ≠ 1 := by
  intro e
  have hb := Subgroup.card_eq_one.mp e
  have hx : x ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  rw [hb, Subgroup.mem_bot] at hx
  rw [hx] at hb
  have ht : Subgroup.centralizer ({(1 : G)} : Set G) = ⊤ := by
    rw [Subgroup.centralizer_eq_top_iff_subset]; simp
  exact bot_ne_top (hb.symm.trans ht)

/-- Each forbidden centralizer order contributes its reciprocal in addition to the
class equation when bounding the sum over all divisors of a multiple of the group order. -/
theorem one_add_sum_forbidden_le (h : HasDistinctConjClassSizes G)
    {n : ℕ} (hn : n ≠ 0) (hd : Nat.card G ∣ n)
    (s : Finset ℕ) (hs : s ⊆ n.divisors)
    (hmiss : ∀ x : G, Nat.card (Subgroup.centralizer ({x} : Set G)) ∉ s) :
    1 + ∑ d ∈ s, (1 : ℚ) / d ≤ (ArithmeticFunction.sigma 1 n : ℚ) / n := by
  classical
  let κ (c : ConjClasses G) := Nat.card G / conjClassCard c
  have hk (x : G) : κ (ConjClasses.mk x) = Nat.card (Subgroup.centralizer ({x} : Set G)) := by
    have : Nonempty (ConjClasses.mk x).carrier := ⟨⟨x, IsConj.refl _⟩⟩
    apply Nat.div_eq_of_eq_mul_right (Nat.card_pos (α := (ConjClasses.mk x).carrier))
    exact (conjClassCard_mk_mul_card_centralizer x).symm
  have ki : Function.Injective κ := by
    intro c c' e
    obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective c
    obtain ⟨y, rfl⟩ := ConjClasses.mk_surjective c'
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_of_card_centralizer_eq h
      ((hk x).symm.trans (e.trans (hk y))))
  let t := Finset.univ.image κ
  have hx (k : ℕ) (k_mem : k ∈ t) :
      ∃ x : G, Nat.card (Subgroup.centralizer ({x} : Set G)) = k := by
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp k_mem
    obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective c
    exact ⟨x, (hk x).symm⟩
  have hdis : Disjoint t s := Finset.disjoint_left.mpr (by
    intro k hkt
    obtain ⟨x, rfl⟩ := hx k hkt
    exact hmiss x)
  have sub : t ∪ s ⊆ n.divisors := Finset.union_subset (by
    intro k hkt
    obtain ⟨x, rfl⟩ := hx k hkt
    exact Nat.mem_divisors.mpr ⟨(Subgroup.card_subgroup_dvd_card _).trans hd, hn⟩) hs
  have ht : ∑ k ∈ t, (1 : ℚ) / k = 1 := by
    dsimp only [t]
    rw [Finset.sum_image ki.injOn]
    exact sum_one_div_card_div_conjClassCard
  nth_rw 1 [← ht]
  rw [← Finset.sum_union hdis, ← sum_inv_divisors n hn]
  exact Finset.sum_le_sum_of_subset_of_nonneg sub (by intros; positivity)

private theorem sigma_two_large_prime {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (a b : ℕ) :
    2 * ArithmeticFunction.sigma 1 (2 ^ a * p ^ b) < 5 * (2 ^ a * p ^ b) := by
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (by omega)
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (hcop.pow _ _),
    ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two,
    ArithmeticFunction.sigma_one_apply_prime_pow hp]
  have hgeom (k : ℕ) : 4 * (∑ j ∈ range (k+1), p ^ j) < 5 * p ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [sum_range_succ, pow_succ]
      nlinarith [Nat.mul_le_mul_left (p ^ k) h5]
  have h2 := geom_two a
  rw [pow_succ] at h2
  have ht := Nat.mul_lt_mul_of_pos_left (hgeom b) (show 0 < 2 ^ a by positivity)
  have hu := congrArg (· * (∑ j ∈ range (b+1), p ^ j)) h2
  nlinarith only [ht, hu, Nat.zero_le (∑ j ∈ range (b+1), p ^ j)]

/-- At most two prime divisors, one of them at least five, are incompatible with a
nontrivial ah-group of order `2^a * p^b`. -/
theorem nonempty_mulEquiv_perm_three_of_order_two_large_prime [Nontrivial G]
    (h : HasDistinctConjClassSizes G) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (a b : ℕ) (hG : Nat.card G ∣ 2 ^ a * p ^ b) : Nonempty (G ≃* Equiv.Perm (Fin 3)) := by
  classical
  by_contra hn
  let n := 2 ^ (a + 1) * p ^ b
  have hnpos : 0 < n := Nat.mul_pos (by positivity) (pow_pos hp.pos _)
  have hd : Nat.card G ∣ n := hG.trans ⟨2, by dsimp [n]; ring⟩
  have h2n : 2 ∣ n := (two_dvd_card h).trans hd
  have hlow := one_add_sum_forbidden_le h hnpos.ne' hd {1, 2} (by
    intro d hd
    simp only [mem_insert, mem_singleton] at hd
    rcases hd with rfl | rfl
    · exact Nat.mem_divisors.mpr ⟨one_dvd _, hnpos.ne'⟩
    · exact Nat.mem_divisors.mpr ⟨h2n, hnpos.ne'⟩) (by
      intro x
      simp only [mem_insert, mem_singleton, not_or]
      exact ⟨card_centralizer_ne_one x, fun hx => hn (nonempty_mulEquiv_perm_three_of_card_centralizer_eq_two h hx)⟩)
  have hhigh := sigma_two_large_prime hp h5 (a+1) b
  change 2 * ArithmeticFunction.sigma 1 n < 5 * n at hhigh
  have hh : (2 : ℚ) * ArithmeticFunction.sigma 1 n < 5 * n := by exact_mod_cast hhigh
  norm_num [Finset.sum_insert] at hlow
  have low := (le_div_iff₀ (show 0 < (n : ℚ) by exact_mod_cast hnpos)).mp hlow
  linarith

/-- For a solvable `{2,3}`-group it suffices to rule out a centralizer of order four. -/
theorem nonempty_mulEquiv_perm_three_of_order_two_three_of_no_four [Nontrivial G]
    [Group.IsSolvable G] (h : HasDistinctConjClassSizes G) (a b : ℕ)
    (hG : Nat.card G = 2 ^ a * 3 ^ b)
    (h4 : ∀ x : G, Nat.card (Subgroup.centralizer ({x} : Set G)) ≠ 4) :
    Nonempty (G ≃* Equiv.Perm (Fin 3)) := by
  classical
  by_contra hn
  let n := 2 ^ (a + 2) * 3 ^ (b+1)
  have hnpos : 0 < n := by dsimp [n]; positivity
  have hd : Nat.card G ∣ n := ⟨12, by rw [hG]; dsimp [n]; ring⟩
  have h12 : 12 ∣ n := ⟨Nat.card G, by rw [hG]; dsimp [n]; ring⟩
  have hlow := one_add_sum_forbidden_le h hnpos.ne' hd {1, 2, 3, 4} (by
    intro d hd
    rw [Nat.mem_divisors]
    simp only [mem_insert, mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> exact ⟨dvd_trans (by decide) h12, hnpos.ne'⟩) (by
      intro x
      simp only [mem_insert, mem_singleton, not_or]
      exact ⟨card_centralizer_ne_one x,
        fun hx => hn (nonempty_mulEquiv_perm_three_of_card_centralizer_eq_two h hx),
        fun hx => hn (nonempty_mulEquiv_perm_three_of_card_centralizer_eq_three h hx), h4 x⟩)
  have hh : ArithmeticFunction.sigma 1 n < 3 * n := by
    dsimp [n]
    rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
        (Nat.Coprime.pow _ _ (by decide : Nat.Coprime 2 3)),
      ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two,
      ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_three]
    have e2 := geom_two (a+2)
    have e3 := geom_three (b+1)
    have u : ∑ j ∈ range (a+2+1), 2^j < 2 * 2^(a+2) := by
      rw [pow_succ _ (a+2)] at e2; omega
    have v : 2 * ∑ j ∈ range (b+1+1), 3^j < 3 * 3^(b+1) := by
      rw [pow_succ _ (b+1)] at e3; omega
    nlinarith only [Nat.mul_lt_mul'' u v]
  norm_num [Finset.sum_insert] at hlow
  have low := (le_div_iff₀ (show 0 < (n : ℚ) by exact_mod_cast hnpos)).mp hlow
  have high : (ArithmeticFunction.sigma 1 n : ℚ) < 3 * n := by exact_mod_cast hh
  linarith

/-- The class equation rules out a counterexample of order dividing `8 * 3^b`. -/
theorem nonempty_mulEquiv_perm_three_of_card_dvd_eight_mul_three_pow [Nontrivial G]
    [Group.IsSolvable G] (h : HasDistinctConjClassSizes G) (b : ℕ)
    (hG : Nat.card G ∣ 8 * 3 ^ b) : Nonempty (G ≃* Equiv.Perm (Fin 3)) := by
  classical
  by_contra hn
  let n := 8 * 3 ^ (b+1)
  have hnpos : 0 < n := by dsimp [n]; positivity
  have hd : Nat.card G ∣ n := hG.trans ⟨3, by dsimp [n]; ring⟩
  have h6 : 6 ∣ n := ⟨4 * 3 ^ b, by dsimp [n]; ring⟩
  have hlow := one_add_sum_forbidden_le h hnpos.ne' hd {1, 2, 3} (by
    intro d hd
    rw [Nat.mem_divisors]
    simp only [mem_insert, mem_singleton] at hd
    rcases hd with rfl | rfl | rfl <;> exact ⟨dvd_trans (by decide) h6, hnpos.ne'⟩) (by
      intro x
      simp only [mem_insert, mem_singleton, not_or]
      exact ⟨card_centralizer_ne_one x,
        fun hx => hn (nonempty_mulEquiv_perm_three_of_card_centralizer_eq_two h hx),
        fun hx => hn (nonempty_mulEquiv_perm_three_of_card_centralizer_eq_three h hx)⟩)
  have hhigh : 16 * ArithmeticFunction.sigma 1 n < 45 * n := by
    dsimp [n]
    rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
        ((show Nat.Coprime 8 3 by decide).pow_right _),
      ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_three,
      show ArithmeticFunction.sigma 1 8 = 15 by decide]
    have he := geom_three (b+1)
    rw [pow_succ _ (b+1)] at he
    omega
  norm_num [Finset.sum_insert] at hlow
  have low := (le_div_iff₀ (show 0 < (n : ℚ) by exact_mod_cast hnpos)).mp hlow
  have high : (16 : ℚ) * ArithmeticFunction.sigma 1 n < 45 * n := by exact_mod_cast hhigh
  linarith

/-- The solvable `{2,3}` case of the conjecture. -/
theorem nonempty_mulEquiv_perm_three_of_order_two_three [Group.IsSolvable G] [Nontrivial G]
    (h : HasDistinctConjClassSizes G) (a b : ℕ) (hG : Nat.card G = 2 ^ a * 3 ^ b) :
    Nonempty (G ≃* Equiv.Perm (Fin 3)) := by
  by_cases hc : ∃ x : G, Nat.card (Subgroup.centralizer ({x} : Set G)) = 4
  · obtain ⟨x, hx⟩ := hc
    obtain ⟨P, hP⟩ := exists_sylow_two_card_le_eight_of_centralizer_four h hx
    have hd := P.pow_dvd_card_of_pow_dvd_card (n := a) (hG ▸ dvd_mul_right _ _)
    have hle := (Nat.le_of_dvd Nat.card_pos hd).trans hP
    have ha : a ≤ 3 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hle
    apply nonempty_mulEquiv_perm_three_of_card_dvd_eight_mul_three_pow h b
    rw [hG]
    exact Nat.mul_dvd_mul (pow_dvd_pow 2 ha) (dvd_refl (3 ^ b))
  · exact nonempty_mulEquiv_perm_three_of_order_two_three_of_no_four h a b hG
      (fun x hx => hc ⟨x, hx⟩)

end PrimeWeights

end

section

open scoped IsMulCommutative

/-- The four cyclic-subgroup norm relations in an elementary abelian group of order
nine imply that multiplication by three annihilates its abelian module. -/
private theorem cube_eq_one_of_four_norms {A : Type*} [CommGroup A] (f g : MulAut A)
    (hc : Commute f g) (hg3 : g ^ 3 = 1)
    (hn : ∀ a ∈ ({f, g, f * g, f * g ^ 2} : Set (MulAut A)), ∀ v, v * a v * a (a v) = 1)
    (v : A) : v ^ 3 = 1 := by
  have comm (w : A) : g (f w) = f (g w) := congrArg (fun a : MulAut A => a w) hc.eq.symm
  have cube (w : A) : g (g (g w)) = w := congrArg (fun a : MulAut A => a w) hg3
  have fline (w : A) := hn f (by simp) w
  have diagonal := hn (f * g) (by simp) v
  have antidiag := hn (f * g ^ 2) (by simp) v
  simp only [MulAut.mul_apply, comm, pow_two, cube] at diagonal antidiag
  have prod_eq :
      (v * f v * f (f v)) * (v * g v * g (g v)) *
        (v * f (g v) * f (f (g (g v)))) * (v * f (g (g v)) * f (f (g v))) =
      v ^ 3 * (v * f v * f (f v)) *
        (g v * f (g v) * f (f (g v))) *
        (g (g v) * f (g (g v)) * f (f (g (g v)))) := by
    rw [pow_succ, pow_two]
    ac_rfl
  rw [fline, hn g (by simp), diagonal, antidiag, fline, fline] at prod_eq
  simpa only [one_mul, mul_one] using prod_eq.symm

/-- A regular quotient conjugacy class consisting of all eight nonidentity elements of
an abelian subgroup of order nine imposes four norm relations on the kernel center. -/
private theorem cube_center_of_regular_quotient {G : Type*} [Group G] [Finite G]
    (K : Subgroup G) [K.Normal] (B : Subgroup (G ⧸ K)) [IsMulCommutative B]
    {x : G} (hx : x ^ 3 = 1) (hb : Nat.card B = 9)
    (haB : QuotientGroup.mk' K x ∈ B) (ho : orderOf (QuotientGroup.mk' K x) = 3)
    (hreg : ∀ y ∈ B, y ≠ 1 → IsConj (QuotientGroup.mk' K x) y)
    (he : Nat.card (Subgroup.centralizer ({QuotientGroup.mk' K x} : Set (G ⧸ K))) =
      Nat.card (Subgroup.centralizer ({x} : Set G))) (z : Subgroup.center K) :
    z ^ 3 = 1 := by
  let q := QuotientGroup.mk' K
  let A := (Subgroup.center K).map K.subtype
  have : IsMulCommutative A := inferInstanceAs (IsMulCommutative ((Subgroup.center K).map K.subtype))
  let F : G →* MulAut A := MulAut.conjNormal
  have hK : K ≤ F.ker := by
    intro k hk
    apply MonoidHom.mem_ker.mpr
    ext y
    obtain ⟨w, hw, hew⟩ := y.2
    change k * (y : G) * k⁻¹ = y
    rw [← hew]
    rw [mul_inv_eq_iff_eq_mul]
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hw ⟨k, hk⟩)
  let ρ := QuotientGroup.lift K F hK
  have hnorm (y : G ⧸ K) (hy : y ∈ B) (hy1 : y ≠ 1) (v : A) :
      v * ρ y v * ρ y (ρ y v) = 1 := by
    obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective K y
    have ht := hreg _ hy hy1
    have cubes {w : G} (hw : IsConj (q x) (q w)) : w ^ 3 = 1 := by
      obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_of_isConj_quotient_of_card_centralizer_eq K he hw)
      rw [← hc, ← MulAut.conj_apply, ← map_pow, hx, map_one]
    have ht3 := cubes ht
    obtain ⟨w, _, hw⟩ := v.2
    have hqv : q (v : G) = 1 := (QuotientGroup.eq_one_iff _).mpr (hw ▸ w.2)
    have hvt : ((v : G) * t) ^ 3 = 1 := cubes (by rwa [map_mul, hqv, one_mul])
    apply Subtype.ext
    change (v : G) * (t * v * t⁻¹) * (t * (t * v * t⁻¹) * t⁻¹) = 1
    calc _ = ((v : G) * t) ^ 3 * (t ^ 3)⁻¹ := by simp only [pow_succ, pow_zero, one_mul]; group
         _ = 1 := by simp only [hvt, ht3, inv_one, one_mul]
  let a : B := ⟨q x, haB⟩
  have ha : orderOf a = 3 := (Subgroup.orderOf_coe a).symm.trans ho
  have hall (y : B) : y ^ 3 = 1 := by
    by_cases h1 : y = 1
    · simp [h1]
    have hcon := hreg (y : G ⧸ K) y.2 (fun he' => h1 (Subtype.ext he'))
    obtain ⟨c, hc⟩ := isConj_iff.mp hcon
    apply Subtype.ext
    change (y : G ⧸ K) ^ 3 = 1
    rw [← hc, ← MulAut.conj_apply, ← map_pow, ← ho, pow_orderOf_eq_one, map_one]
  obtain ⟨b, hb'⟩ : ∃ b : B, b ∉ Subgroup.zpowers a := by
    by_contra! hall'
    have hh := congrArg (fun S : Subgroup B => Nat.card S)
      ((Subgroup.eq_top_iff' _).mpr hall')
    rw [Nat.card_zpowers, Subgroup.card_top, ha, hb] at hh
    contradiction
  have h1 : a ≠ 1 := fun he' => (by decide : 1 ≠ 3) (by simpa only [he', orderOf_one] using ha)
  have h2 : b ≠ 1 := fun he' => hb' (he' ▸ (Subgroup.zpowers a).one_mem)
  have h3 : a * b ≠ 1 := by
    intro hprod
    have bh : b = a⁻¹ := eq_inv_of_mul_eq_one_right hprod
    exact hb' (bh ▸ (Subgroup.zpowers a).inv_mem (Subgroup.mem_zpowers a))
  have h4 : a * b ^ 2 ≠ 1 := by
    intro hprod
    have bh : b ^ 2 = a⁻¹ := eq_inv_of_mul_eq_one_right hprod
    have hb4 : (b ^ 2) ^ 2 = b := by
      rw [← pow_mul, show 2*2=3+1 from rfl, pow_succ, hall, one_mul]
    exact hb' (hb4 ▸ (Subgroup.zpowers a).pow_mem
      (bh ▸ (Subgroup.zpowers a).inv_mem (Subgroup.mem_zpowers a)) 2)
  let R := ρ.comp B.subtype
  let vz : A := ⟨((z : K) : G), ⟨(z : K), z.2, rfl⟩⟩
  have hz := cube_eq_one_of_four_norms (R a) (R b) ((show Commute a b from mul_comm' a b).map R)
    (by rw [← map_pow, hall, map_one]) (by
      intro t ht
      simp only [← map_mul, ← map_pow, Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with rfl | rfl | rfl | rfl
      · exact hnorm a a.2 (fun he' => h1 (Subtype.ext he'))
      · exact hnorm b b.2 (fun he' => h2 (Subtype.ext he'))
      · exact hnorm (a * b : B) (a * b).2 (fun he' => h3 (Subtype.ext he'))
      · exact hnorm (a * b ^ 2 : B) (a * b ^ 2).2 (fun he' => h4 (Subtype.ext he'))) vz
  exact Subtype.ext (Subtype.ext (congrArg (fun y : A => (y : G)) hz))

/-- A nontrivial five-part in the nilpotent kernel forces eight to divide the
order of the quotient, since a conjugator induces an automorphism of order four. -/
private theorem eight_dvd_quotient_of_five_dvd_nilpotent {G : Type*} [Group G] [Fintype G]
    (h : HasDistinctConjClassSizes G) (K : Subgroup G) [K.Normal] [Group.IsNilpotent K]
    (h5 : 5 ∣ Nat.card K) : 8 ∣ Nat.card (G ⧸ K) := by
  classical
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨z, hz, ho⟩ := exists_prime_order_in_center_of_nilpotent 5 h5
  obtain ⟨w, hw⟩ := exists_quotient_order_multiple_prime_sub_one h K
    ((Subgroup.orderOf_coe z).trans ho) (by
      intro t ht
      exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
        (Subgroup.mem_center_iff.mp hz ⟨t, ht⟩)))
  change 4 ∣ orderOf w at hw
  let C := Subgroup.centralizer ({w} : Set (G ⧸ K))
  have h4 : 4 ∣ Nat.card C := by
    have hd := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr
      (show w ∈ C from Subgroup.mem_centralizer_singleton_iff.mpr rfl))
    rw [Nat.card_zpowers] at hd
    exact hw.trans hd
  have hreal : IsConj w w⁻¹ := by
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective K w
    simpa only [map_inv] using (QuotientGroup.mk' K).map_isConj (isConj_inv h v)
  have h2 := two_dvd_conjClassCard_of_isConj_inv hreal
    (fun he => (by decide : ¬ 4 ∣ 2) (hw.trans (orderOf_dvd_of_pow_eq_one he)))
  rw [← conjClassCard_mk_mul_card_centralizer w]
  exact Nat.mul_dvd_mul h2 h4

/-- In a smooth counterexample, a three-element whose centralizer has order nine
survives in a quotient of order six or twelve. -/
theorem exists_quotient_six_or_twelve_of_three_element_centralizer_nine {G : Type*}
    [Group G] [Fintype G] [Group.IsSolvable G] [Nontrivial G] (h : HasDistinctConjClassSizes G)
    (hsmooth : ∃ a b c : ℕ, Nat.card G = 2 ^ a * 3 ^ b * 5 ^ c) {x : G} (hx : x ^ 3 = 1)
    (hc : Nat.card (Subgroup.centralizer ({x} : Set G)) = 9)
    (hbad : ¬ Nonempty (G ≃* Equiv.Perm (Fin 3))) :
    ∃ (K : Subgroup G) (_ : K.Normal), orderOf (QuotientGroup.mk' K x) = 3 ∧
      (Nat.card (G ⧸ K) = 6 ∨ Nat.card (G ⧸ K) = 12) := by
  classical
  obtain ⟨K, hK, B, hBn, hBa, hu, hb, horder, hQ, hn⟩ :=
    exists_quotient_of_three_element_centralizer_nine h hx hc
  refine ⟨K, hK, horder, ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hQ
  by_contra hnot
  have : Group.IsNilpotent K := hn (by omega)
  have h5G : 5 ∣ Nat.card G := by
    obtain ⟨a,b,c,he⟩ := hsmooth
    cases c with
    | zero => exact (hbad (nonempty_mulEquiv_perm_three_of_order_two_three h a b (by simpa using he))).elim
    | succ c => rw [he, pow_succ, ← mul_assoc]; exact dvd_mul_left _ _
  have h5K : 5 ∣ Nat.card K := by
    rw [K.card_eq_card_quotient_mul_card_subgroup] at h5G
    exact (Nat.prime_five.dvd_mul.mp h5G).resolve_left (by
      rcases hQ with H | H | H | H | H | H <;> rw [H] <;> decide)
  have h8 := eight_dvd_quotient_of_five_dvd_nilpotent h K h5K
  have h72 : Nat.card (G ⧸ K) = 72 := by omega
  let u := QuotientGroup.mk' K x
  let C := Subgroup.centralizer ({u} : Set (G ⧸ K))
  let S := (ConjClasses.mk u).carrier
  have hle : Nat.card C ≤ 9 := (card_centralizer_quotient_le K x).trans hc.le
  have hsub : S ⊆ (B : Set (G ⧸ K)) \ {1} := by
    intro y hy
    constructor
    · obtain ⟨t, rfl⟩ := isConj_iff.mp (show IsConj u y from hy)
      exact hBn.conj_mem _ hu t
    · intro hy1
      have huv : u = 1 := isConj_one_right.mp (show IsConj u 1 from (Set.mem_singleton_iff.mp hy1) ▸ hy).symm
      change orderOf u = 3 at horder
      rw [huv, orderOf_one] at horder
      contradiction
  have hncard : ((B : Set (G ⧸ K)) \ {1}).ncard = Nat.card B - 1 := by
    rw [Set.ncard_sdiff_singleton_of_mem B.one_mem]
    exact congrArg (· - 1) (Nat.card_coe_set_eq (B : Set (G ⧸ K))).symm
  have hcl : ∀ n : ℕ, Nat.card B = n → conjClassCard (ConjClasses.mk u) ≤ n - 1 := by
    intro n hnB
    rw [conjClassCard, Nat.card_coe_set_eq, ← hnB, ← hncard]
    exact Set.ncard_le_ncard hsub
  have hprod : conjClassCard (ConjClasses.mk u) * Nat.card C = 72 :=
    (conjClassCard_mk_mul_card_centralizer u).trans h72
  have hb9 : Nat.card B = 9 := hb.resolve_left (fun hb3 => by
    have hle' := Nat.mul_le_mul (hcl 3 hb3) hle
    rw [hprod] at hle'; contradiction)
  have heq8 : conjClassCard (ConjClasses.mk u) = 8 := by
    have hupper := hcl 9 hb9
    by_contra hne
    have hh := Nat.mul_le_mul (show conjClassCard (ConjClasses.mk u) ≤ 7 from by omega) hle
    rw [hprod] at hh
    contradiction
  have heqC : Nat.card C = 9 := by rw [heq8] at hprod; omega
  have reg : S = (B : Set (G ⧸ K)) \ {1} := by
    apply Set.eq_of_subset_of_ncard_le hsub
    rw [hncard, hb9, ← Nat.card_coe_set_eq S]
    exact heq8.ge
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨z, hz, hzo⟩ := exists_prime_order_in_center_of_nilpotent 5 h5K
  have hz3 := cube_center_of_regular_quotient K B hx hb9 hu horder
    (fun y hy hy1 => (reg ▸ (show y ∈ (B : Set _) \ {1} from ⟨hy, hy1⟩) : y ∈ S))
    (heqC.trans hc.symm) (⟨z, hz⟩ : Subgroup.center K)
  have hd := orderOf_dvd_of_pow_eq_one hz3
  rw [← Subgroup.orderOf_coe, hzo] at hd
  exact (by decide : ¬ 5 ∣ 3) hd

end

section

section Residual

variable {G : Type*} [Group G] [Fintype G] [Group.IsSolvable G] [Nontrivial G]

/-- If the group order is smooth and 3 divides it just once, the Hall complement
in a 3-element centralizer has order prime to 3 and divides a `{2,5}`-number. -/
private theorem nonempty_perm_three_of_three_exact (h : HasDistinctConjClassSizes G)
    (a b c : ℕ) (hG : Nat.card G = 2 ^ a * 3 ^ b * 5 ^ c)
    (hd : 3 ∣ Nat.card G) (h9 : ¬ 9 ∣ Nat.card G) : Nonempty (G ≃* Equiv.Perm (Fin 3)) := by
  classical
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 hd
  let C := Subgroup.centralizer ({x} : Set G)
  have hxC : x ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hxc : orderOf x ∣ Nat.card C := Subgroup.orderOf_mk x hxC ▸ orderOf_dvd_natCard (⟨x,hxC⟩ : C)
  obtain ⟨m, hm⟩ := hxc
  have hmG : orderOf x * m ∣ Nat.card G := hm ▸ C.card_subgroup_dvd_card
  have h3 : ¬ 3 ∣ m := fun e => h9 ((Nat.mul_dvd_mul (by rw [hx] : 3 ∣ orderOf x) e).trans hmG)
  have hcop := Nat.prime_three.coprime_iff_not_dvd.mpr h3
  obtain ⟨B, hB, hh⟩ := exists_ah_complement_in_centralizer h hm (hx ▸ hcop)
  have hm1 : m = 1 := by
    by_contra hn
    let _ := Fintype.ofFinite B
    have hpos : 0 < m := hB ▸ Nat.card_pos
    have : Nontrivial B := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    have hm' := (dvd_mul_left m (orderOf x)).trans hmG
    rw [hG, mul_right_comm, mul_comm _ (3 ^ b)] at hm'
    have hdiv := (hcop.symm.pow_right b).dvd_of_dvd_mul_left hm'
    obtain ⟨e⟩ := nonempty_mulEquiv_perm_three_of_order_two_large_prime hh
      (by decide : Nat.Prime 5) (by decide) a c (hB ▸ hdiv)
    have hm6 := hB.symm.trans (Nat.card_congr e.toEquiv)
    rw [Nat.card_perm, Nat.card_fin] at hm6
    exact h3 (hm6 ▸ (by decide : 3 ∣ 6))
  apply nonempty_mulEquiv_perm_three_of_card_centralizer_eq_three h (x := x)
  simpa [hx, hm1] using hm

/-- A smooth-order counterexample would have order divisible by 3600 and a
centralizer of order 6, 8, 9 or 10. -/
theorem smooth_counterexample_constraints (h : HasDistinctConjClassSizes G)
    (hs : ∃ a b c : ℕ, Nat.card G = 2 ^ a * 3 ^ b * 5 ^ c)
    (hn : ¬ Nonempty (G ≃* Equiv.Perm (Fin 3))) :
    3600 ∣ Nat.card G ∧ ∃ x : G,
      Nat.card (Subgroup.centralizer ({x} : Set G)) ∈ ({6,8,9,10} : Finset ℕ) := by
  obtain ⟨a,b,c,hG⟩ := hs
  have h5 : 5 ∣ Nat.card G := by
    by_cases hzero : c = 0
    · exact (hn (nonempty_mulEquiv_perm_three_of_order_two_three h a b
        (by simpa [hzero] using hG))).elim
    · exact (dvd_pow_self 5 hzero).trans (hG ▸ dvd_mul_left _ _)
  have h16 := sixteen_dvd_card_of_five_dvd h h5
  have h25 := prime_sq_dvd_card_of_five_le h (by decide : Nat.Prime 5) (by decide) h5
  have h3 : 3 ∣ Nat.card G := by
    by_cases hzero : b = 0
    · exact (hn (nonempty_mulEquiv_perm_three_of_order_two_large_prime h (by decide : Nat.Prime 5)
        (by decide) a c (by rw [hG, hzero]; simp))).elim
    · exact (dvd_pow_self 3 hzero).trans ((dvd_mul_left _ _).trans (hG ▸ dvd_mul_right _ _))
  have h9 : 9 ∣ Nat.card G := by
    by_contra he
    exact hn (nonempty_perm_three_of_three_exact h a b c hG h3 he)
  have h144 := (show Nat.Coprime 16 9 by decide).mul_dvd_of_dvd_of_dvd h16 h9
  have h3600 := (show Nat.Coprime 144 25 by decide).mul_dvd_of_dvd_of_dvd h144 h25
  refine ⟨h3600, ?_⟩
  by_contra! hall
  apply hn
  apply nonempty_mulEquiv_perm_three_of_smooth_of_no_small_centralizer h ⟨a,b,c,hG⟩
  intro x m hm e
  rw [← e] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h3 | h4 | h5 | h6 | h8 | h9 | h10
  · exact hn (nonempty_mulEquiv_perm_three_of_card_centralizer_eq_three h h3)
  · obtain ⟨P, hP⟩ := exists_sylow_two_card_le_eight_of_centralizer_four h h4
    have hd := P.pow_dvd_card_of_pow_dvd_card (n := 4) h16
    have hl := Nat.le_of_dvd Nat.card_pos hd
    omega
  · exact card_centralizer_ne_prime_of_five_le h Nat.prime_five (by decide) x h5
  · exact hall x (by simp [h6])
  · exact hall x (by simp [h8])
  · exact hall x (by simp [h9])
  · exact hall x (by simp [h10])

end Residual

/-- Gow's theorem: the order of a finite solvable rational group is divisible only by the primes
`2`, `3` and `5`. -/
def H1 : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] [Group.IsSolvable G],
    (∀ (x : G) (n : ℕ), (Nat.card G).Coprime n → IsConj x (x ^ n)) →
    ∀ p : ℕ, p.Prime → p ∣ Nat.card G → p = 2 ∨ p = 3 ∨ p = 5

/-- No centraliser of order `6` or `10` in a minimal counterexample of `{2,3,5}`-order. -/
def H2 : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] [Group.IsSolvable G] [Nontrivial G],
    ConjugacyClassSizes.HasDistinctConjClassSizes (G := G) →
    (∀ (K : Type) [Group K] [Fintype K] [Group.IsSolvable K] [Nontrivial K],
      Nat.card K < Nat.card G → ConjugacyClassSizes.HasDistinctConjClassSizes (G := K) →
      Nonempty (K ≃* Equiv.Perm (Fin 3))) →
    (∃ a b c : ℕ, Nat.card G = 2 ^ a * 3 ^ b * 5 ^ c) → 3600 ∣ Nat.card G →
    ∀ x : G, Nat.card (Subgroup.centralizer ({x} : Set G)) ≠ 6 ∧
      Nat.card (Subgroup.centralizer ({x} : Set G)) ≠ 10

/-- No centraliser of order `8` in a minimal counterexample of `{2,3,5}`-order. -/
def H3 : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] [Group.IsSolvable G] [Nontrivial G],
    ConjugacyClassSizes.HasDistinctConjClassSizes (G := G) →
    (∀ (K : Type) [Group K] [Fintype K] [Group.IsSolvable K] [Nontrivial K],
      Nat.card K < Nat.card G → ConjugacyClassSizes.HasDistinctConjClassSizes (G := K) →
      Nonempty (K ≃* Equiv.Perm (Fin 3))) →
    (∃ a b c : ℕ, Nat.card G = 2 ^ a * 3 ^ b * 5 ^ c) → 3600 ∣ Nat.card G →
    ∀ x : G, Nat.card (Subgroup.centralizer ({x} : Set G)) ≠ 8

/-- No centraliser of order `9` in a minimal counterexample of `{2,3,5}`-order. -/
def H4 : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] [Group.IsSolvable G] [Nontrivial G],
    ConjugacyClassSizes.HasDistinctConjClassSizes (G := G) →
    (∀ (K : Type) [Group K] [Fintype K] [Group.IsSolvable K] [Nontrivial K],
      Nat.card K < Nat.card G → ConjugacyClassSizes.HasDistinctConjClassSizes (G := K) →
      Nonempty (K ≃* Equiv.Perm (Fin 3))) →
    (∃ a b c : ℕ, Nat.card G = 2 ^ a * 3 ^ b * 5 ^ c) → 3600 ∣ Nat.card G →
    ∀ x : G, Nat.card (Subgroup.centralizer ({x} : Set G)) ≠ 9

theorem main : H1 → H2 → H3 → H4 → type_of% @ConjugacyClassSizes.conjClassSizes_iff_sym_three_solvable := by
  intro h1 h2 h3 h4
  apply solution_of_inductiveOrderClaim
  intro G _ _ _ _ h ih hfour
  have hrat : ∀ (x : G) (n : ℕ), (Nat.card G).Coprime n → IsConj x (x ^ n) := fun x n hn =>
    isConj_pow_of_coprime h x (hn.symm.coprime_dvd_right (orderOf_dvd_natCard x))
  have hs : ∃ a b c : ℕ, Nat.card G = 2 ^ a * 3 ^ b * 5 ^ c :=
    smooth_order_of_bounded_primes _ Nat.card_pos.ne' (fun p hp hd => by
      rcases h1 G hrat p hp hd with rfl | rfl | rfl <;> norm_num)
  have finish : Nonempty (G ≃* Equiv.Perm (Fin 3)) := by
    by_contra hn
    obtain ⟨hd, x, hx⟩ := smooth_counterexample_constraints h hs hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with e | e | e | e
    · exact (h2 G h ih hs hd x).1 e
    · exact h3 G h ih hs hd x e
    · exact h4 G h ih hs hd x e
    · exact (h2 G h ih hs hd x).2 e
  obtain ⟨e⟩ := finish
  rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin] at hfour
  exact (by decide : ¬ 4 ∣ 6) hfour

end

end OMA.R_ConjugacyClassSizes_conjClassSizes_iff_sym_three_solvable_R2
