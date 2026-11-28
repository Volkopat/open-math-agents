import OMAStatements.S_mo_415174

namespace Mo415174

section PowerEquiv

variable {G : Type} [Group G]

lemma conj_zpow_eq (a g : G) (n : ℤ) : (a * g * a⁻¹) ^ n = a * g ^ n * a⁻¹ :=
  (map_zpow (MulAut.conj a) g n).symm

lemma isConj_zpow {x y : G} (h : IsConj x y) (n : ℤ) : IsConj (x ^ n) (y ^ n) := by
  rw [isConj_iff] at h ⊢
  obtain ⟨a, rfl⟩ := h
  exact ⟨a, (conj_zpow_eq a x n).symm⟩

variable [Fintype G]

lemma zpow_eq_of_modEq {n₁ n₂ : ℤ} (h : n₁ ≡ n₂ [ZMOD (Fintype.card G : ℤ)]) (g : G) :
    g ^ n₁ = g ^ n₂ := by
  obtain ⟨t, ht⟩ := Int.modEq_iff_dvd.mp h
  have h2 : n₂ = n₁ + (Fintype.card G : ℤ) * t := by linarith
  rw [h2, zpow_add, zpow_mul, zpow_natCast, pow_card_eq_one, one_zpow, mul_one]

def powEquiv (n : ℤ) (hn : Int.gcd n (Fintype.card G : ℤ) = 1) : G ≃ G := by
  let m : ℤ := (Fintype.card G : ℤ)
  let k : ℤ := Int.gcdA n m
  have hbez : (1 : ℤ) = n * k + m * Int.gcdB n m := by
    have h := Int.gcd_eq_gcd_ab n m
    rw [hn] at h
    simpa using h
  have hnk : n * k ≡ 1 [ZMOD m] := by
    rw [Int.modEq_iff_dvd]
    exact ⟨Int.gcdB n m, by linarith⟩
  have hkn : k * n ≡ 1 [ZMOD m] := by
    simpa [mul_comm] using hnk
  exact
    { toFun := fun g => g ^ n
      invFun := fun g => g ^ k
      left_inv := fun g => by
        dsimp only
        rw [← zpow_mul, zpow_eq_of_modEq hnk, zpow_one]
      right_inv := fun g => by
        dsimp only
        rw [← zpow_mul, zpow_eq_of_modEq hkn, zpow_one] }

lemma powEquiv_apply (n : ℤ) (hn : Int.gcd n (Fintype.card G : ℤ) = 1) (g : G) :
    powEquiv n hn g = g ^ n := rfl

lemma powEquiv_symm_apply (n : ℤ) (hn : Int.gcd n (Fintype.card G : ℤ) = 1) (g : G) :
    (powEquiv n hn).symm g = g ^ (Int.gcdA n (Fintype.card G : ℤ)) := rfl

lemma isConj_powEquiv_symm_iff {n : ℤ} (hn : Int.gcd n (Fintype.card G : ℤ) = 1) (x y : G) :
    IsConj ((powEquiv n hn).symm x) y ↔ IsConj x (powEquiv n hn y) := by
  constructor
  · intro h
    have h' := isConj_zpow h n
    change IsConj (powEquiv n hn ((powEquiv n hn).symm x)) (powEquiv n hn y) at h'
    simpa using h'
  · intro h
    have h' := isConj_zpow h (Int.gcdA n (Fintype.card G : ℤ))
    change IsConj ((powEquiv n hn).symm x) ((powEquiv n hn).symm (powEquiv n hn y)) at h'
    simpa using h'

end PowerEquiv

section CenterChar

variable {R : Type*} [CommRing R] {G : Type}

lemma coeff_mapDomain_equiv (e : G ≃ G) (z : MonoidAlgebra R G) (x : G) :
    (MonoidAlgebra.mapDomain e z).coeff x = z.coeff (e.symm x) := by
  rw [MonoidAlgebra.coeff_mapDomain]
  have hx : x = e (e.symm x) := (e.apply_symm_apply x).symm
  conv_lhs => rw [hx]
  exact Finsupp.mapDomain_apply e.injective z.coeff (e.symm x)

variable [Group G] [Fintype G]

lemma coeff_mul_eq_sum (a b : MonoidAlgebra R G) (y : G) :
    (a * b).coeff y = ∑ g : G, a.coeff g * b.coeff (g⁻¹ * y) := by
  classical
  rw [MonoidAlgebra.coeff_mul]
  rw [Finsupp.sum_fintype _ _ (by intro g; simp)]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finsupp.sum_fintype _ _ (by intro h; simp)]
  have hiff : ∀ h : G, (g * h = y) ↔ (h = g⁻¹ * y) := fun h => by
    constructor
    · intro hh; rw [← hh, inv_mul_cancel_left]
    · intro hh; rw [hh, mul_inv_cancel_left]
  simp_rw [hiff]
  simp

lemma mem_center_iff_conj (z : MonoidAlgebra R G) :
    z ∈ Subring.center (MonoidAlgebra R G) ↔ ∀ a g : G, z.coeff (a * g * a⁻¹) = z.coeff g := by
  rw [Subring.mem_center_iff]
  constructor
  · intro hz a g
    have h := congrArg (fun f : MonoidAlgebra R G => f.coeff (a * g))
      (hz (MonoidAlgebra.single a (1 : R)))
    classical
    simp only [coeff_mul_eq_sum, MonoidAlgebra.coeff_single, Finsupp.single_apply] at h
    have hl : (∑ x : G, (if a = x then (1 : R) else 0) * z.coeff (x⁻¹ * (a * g))) = z.coeff g := by
      simp
    have hr : (∑ x : G, z.coeff x * (if a = x⁻¹ * (a * g) then (1 : R) else 0)) =
        z.coeff (a * g * a⁻¹) := by
      have hiff : ∀ x : G, (a = x⁻¹ * (a * g)) ↔ (x = a * g * a⁻¹) := fun x => by
        constructor
        · intro hx
          have hxa : x * a = a * g := calc
            x * a = x * (x⁻¹ * (a * g)) := congrArg (x * ·) hx
            _ = a * g := mul_inv_cancel_left x (a * g)
          exact eq_mul_inv_of_mul_eq hxa
        · intro hx
          rw [hx]
          group
      simp_rw [hiff]
      simp
    rw [hl, hr] at h
    exact h.symm
  · intro hz y
    apply MonoidAlgebra.ext
    ext x
    rw [coeff_mul_eq_sum, coeff_mul_eq_sum]
    let e : G ≃ G :=
      { toFun := fun g => x * g⁻¹
        invFun := fun h => h⁻¹ * x
        left_inv := fun g => by group
        right_inv := fun h => by group }
    conv_rhs =>
      rw [← Fintype.sum_equiv e (fun g => z.coeff (x * g⁻¹) * y.coeff g) _
        (fun g => by simp [e])]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [mul_comm]
    congr 1
    have hconj := hz g⁻¹ (x * g⁻¹)
    have heq : g⁻¹ * (x * g⁻¹) * (g⁻¹)⁻¹ = g⁻¹ * x := by group
    rw [heq] at hconj
    exact hconj

lemma center_eq_of_isConj {z : MonoidAlgebra R G} (hz : z ∈ Subring.center (MonoidAlgebra R G))
    {x y : G} (hxy : IsConj x y) : z.coeff x = z.coeff y := by
  rw [isConj_iff] at hxy
  obtain ⟨a, rfl⟩ := hxy
  exact ((mem_center_iff_conj z).mp hz a x).symm

lemma mapDomain_powEquiv_mem_center {n : ℤ} (hn : Int.gcd n (Fintype.card G : ℤ) = 1)
    {z : MonoidAlgebra R G} (hz : z ∈ Subring.center (MonoidAlgebra R G)) :
    MonoidAlgebra.mapDomain (fun g : G => g ^ n) z ∈ Subring.center (MonoidAlgebra R G) := by
  rw [mem_center_iff_conj] at hz ⊢
  intro a g
  change (MonoidAlgebra.mapDomain (powEquiv n hn) z).coeff (a * g * a⁻¹) =
    (MonoidAlgebra.mapDomain (powEquiv n hn) z).coeff g
  rw [coeff_mapDomain_equiv, coeff_mapDomain_equiv]
  simp only [powEquiv_symm_apply]
  rw [conj_zpow_eq]
  exact hz a _

lemma coeff_pow_eq_sum [DecidableEq G] (w : MonoidAlgebra R G) (k : ℕ) (y : G) :
    (w ^ k).coeff y =
      ∑ f : Fin k → G, if (List.ofFn f).prod = y then ∏ i : Fin k, w.coeff (f i) else 0 := by
  induction k generalizing y with
  | zero =>
    rw [pow_zero, MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, Finsupp.single_apply]
    rw [Fintype.sum_unique]
    simp
  | succ k ih =>
    rw [pow_succ', coeff_mul_eq_sum]
    simp_rw [ih, Finset.mul_sum, mul_ite, mul_zero]
    have hiff : ∀ (g : G) (f' : Fin k → G),
        ((List.ofFn f').prod = g⁻¹ * y) ↔ (g * (List.ofFn f').prod = y) := fun g f' => by
      constructor
      · intro h; rw [h, mul_inv_cancel_left]
      · intro h; rw [← h, inv_mul_cancel_left]
    simp_rw [hiff]
    rw [← Fintype.sum_prod_type']
    refine Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (k + 1) => G)) _ _ ?_
    intro ⟨g, f'⟩
    have hprod : (List.ofFn (Fin.consEquiv (fun _ : Fin (k + 1) => G) (g, f'))).prod =
        g * (List.ofFn f').prod := by
      rw [List.ofFn_succ, List.prod_cons]
      rfl
    have hfinprod :
        (∏ i : Fin (k + 1), w.coeff ((Fin.consEquiv (fun _ : Fin (k + 1) => G) (g, f')) i)) =
          w.coeff g * ∏ i : Fin k, w.coeff (f' i) := by
      rw [Fin.prod_univ_succ]
      rfl
    rw [hprod, hfinprod]

end CenterChar

section FrobeniusCenter

variable {G : Type}

def shift {p : ℕ} [NeZero p] (k : Fin p) (f : Fin p → G) : Fin p → G :=
  fun i => f (i + k)

lemma shift_zero {p : ℕ} [NeZero p] (f : Fin p → G) : shift 0 f = f := by
  funext i; simp [shift]

lemma shift_shift {p : ℕ} [NeZero p] (k₁ k₂ : Fin p) (f : Fin p → G) :
    shift k₁ (shift k₂ f) = shift (k₁ + k₂) f := by
  funext i; simp [shift, add_assoc]

lemma fin_val_nsmul {p : ℕ} [NeZero p] (m : ℕ) (d : Fin p) :
    (m • d).val = (m * d.val) % p := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [succ_nsmul, Fin.val_add, ih, add_mul, one_mul, Nat.mod_add_mod]

lemma shift_injective_of_nonconst {p : ℕ} [Fact p.Prime] {f : Fin p → G}
    (hnc : ∃ i j : Fin p, f i ≠ f j) :
    Function.Injective (fun k : Fin p => shift k f) := by
  have : NeZero p := NeZero.of_pos (Fact.out : p.Prime).pos
  intro k₁ k₂ hk
  by_contra hne
  let d : Fin p := k₂ - k₁
  have hd_ne : d ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hper : ∀ i : Fin p, f (i + d) = f i := by
    intro i
    have hi := congrFun hk (i - k₁)
    simp only [shift] at hi
    have h1 : i - k₁ + k₁ = i := sub_add_cancel i k₁
    have h2 : i - k₁ + k₂ = i + d := by
      simp only [d]
      abel
    rw [h1, h2] at hi
    exact hi.symm
  have hper_mul : ∀ (m : ℕ) (i : Fin p), f (i + m • d) = f i := by
    intro m
    induction m with
    | zero => intro i; simp
    | succ m ih =>
      intro i
      rw [succ_nsmul, ← add_assoc, hper, ih]
  have hd_zmod : (d.val : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    have hd_pos : 0 < d.val := Nat.pos_of_ne_zero (fun h => hd_ne (Fin.ext h))
    exact Nat.not_dvd_of_pos_of_lt hd_pos d.isLt
  have hconst : ∀ i : Fin p, f i = f 0 := by
    intro i
    let u : ZMod p := (i.val : ZMod p) * (d.val : ZMod p)⁻¹
    let m : ℕ := u.val
    have hm_zmod : ((m * d.val : ℕ) : ZMod p) = (i.val : ZMod p) := by
      push_cast
      have hu : (m : ZMod p) = u := ZMod.natCast_zmod_val u
      rw [hu]
      simp [u, hd_zmod]
    have hmd : m • d = i := by
      ext
      rw [fin_val_nsmul]
      have hval := congrArg ZMod.val hm_zmod
      rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt] at hval
      exact hval
    have := hper_mul m 0
    rw [zero_add, hmd] at this
    exact this
  obtain ⟨i, j, hij⟩ := hnc
  exact hij ((hconst i).trans (hconst j).symm)

variable [Group G]

lemma isConj_prod_ofFn_shift_one {p : ℕ} [NeZero p] (f : Fin p → G) :
    IsConj (List.ofFn f).prod (List.ofFn (shift 1 f)).prod := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne p)
  let l : List G := List.ofFn (fun j : Fin q => f j.succ)
  have hf : List.ofFn f = f 0 :: l := List.ofFn_succ
  have hrot : List.ofFn (shift 1 f) = l ++ [f 0] := by
    refine List.ext_getElem (by simp [l]) fun i hi₁ hi₂ => ?_
    rw [List.getElem_ofFn]
    simp only [shift]
    by_cases hq : i < q
    · rw [List.getElem_append_left (by simpa [l] using hq)]
      simp only [l, List.getElem_ofFn]
      congr 1
      ext
      simp [Fin.val_add, Nat.mod_eq_of_lt (show i + 1 < q + 1 by omega)]
    · have hiq : i = q := by simp [l] at hi₂; omega
      subst i
      rw [List.getElem_append_right (by simp [l])]
      simp only [l, List.length_ofFn, Nat.sub_self, List.getElem_singleton]
      congr 1
      ext
      simp [Fin.val_add]
  rw [hf, hrot, List.prod_cons, List.prod_append, List.prod_singleton, isConj_iff]
  exact ⟨(f 0)⁻¹, by group⟩

lemma isConj_prod_ofFn_shift {p : ℕ} [NeZero p] (k : Fin p) (f : Fin p → G) :
    IsConj (List.ofFn f).prod (List.ofFn (shift k f)).prod := by
  have hk : k.val • (1 : Fin p) = k := by
    ext
    rw [fin_val_nsmul]
    simp [Nat.mod_eq_of_lt k.isLt]
  rw [← hk]
  suffices ∀ (m : ℕ) (f : Fin p → G),
      IsConj (List.ofFn f).prod (List.ofFn (shift (m • (1 : Fin p)) f)).prod from
    this k.val f
  intro m
  induction m with
  | zero =>
    intro f
    rw [zero_nsmul, shift_zero]
  | succ m ih =>
    intro f
    have h1 := isConj_prod_ofFn_shift_one f
    have h2 := ih (shift 1 f)
    have h3 : shift (m • (1 : Fin p)) (shift 1 f) = shift ((m + 1) • (1 : Fin p)) f := by
      rw [shift_shift, succ_nsmul]
    rw [h3] at h2
    exact h1.trans h2

variable [Fintype G]

lemma center_pow_prime_eq_mapDomain {p : ℕ} [Fact p.Prime] (hp_gt : Fintype.card G < p)
    {w : MonoidAlgebra (ZMod p) G} (hw : w ∈ Subring.center (MonoidAlgebra (ZMod p) G)) :
    w ^ p = MonoidAlgebra.mapDomain (fun g : G => g ^ p) w := by
  classical
  have hp : p.Prime := Fact.out
  have : NeZero p := NeZero.of_pos hp.pos
  have hcop_nat : Nat.Coprime p (Fintype.card G) :=
    hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt Fintype.card_pos hp_gt)
  have hcop : Int.gcd (p : ℤ) (Fintype.card G : ℤ) = 1 := by
    simpa [Int.gcd_natCast_natCast] using hcop_nat
  let e : G ≃ G := powEquiv (p : ℤ) hcop
  have he_apply : ∀ g : G, e g = g ^ p := fun g => by
    simp [e, powEquiv_apply, zpow_natCast]
  apply MonoidAlgebra.ext
  ext x
  let C : Finset G := Finset.univ.filter (fun y : G => IsConj x y)
  have hxC : x ∈ C := Finset.mem_filter.mpr ⟨Finset.mem_univ x, IsConj.refl x⟩
  have hC_pos : 0 < C.card := Finset.card_pos.mpr ⟨x, hxC⟩
  have hC_lt : C.card < p := lt_of_le_of_lt (Finset.card_le_univ C) hp_gt
  have hC_ne : (C.card : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt hC_pos hC_lt
  have hwp_center : w ^ p ∈ Subring.center (MonoidAlgebra (ZMod p) G) :=
    Subring.pow_mem _ hw p
  have hlhs : (C.card : ZMod p) * (w ^ p).coeff x = ∑ y ∈ C, (w ^ p).coeff y := by
    rw [Finset.sum_congr rfl (fun y hy => by
      have hxy : IsConj x y := (Finset.mem_filter.mp hy).2
      exact (center_eq_of_isConj hwp_center hxy).symm)]
    simp
  let F : (Fin p → G) → ZMod p := fun f => ∏ i : Fin p, w.coeff (f i)
  let S : Finset (Fin p → G) := Finset.univ.filter (fun f => (List.ofFn f).prod ∈ C)
  have hsum_eq : ∑ y ∈ C, (w ^ p).coeff y = ∑ f ∈ S, F f := by
    simp_rw [coeff_pow_eq_sum]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq]
    rw [← Finset.sum_filter]
  let S_const : Finset (Fin p → G) := S.filter (fun f => ∀ i j : Fin p, f i = f j)
  let S_nc : Finset (Fin p → G) := S.filter (fun f => ¬ ∀ i j : Fin p, f i = f j)
  have hpart : ∑ f ∈ S, F f = (∑ f ∈ S_const, F f) + ∑ f ∈ S_nc, F f := by
    exact (Finset.sum_filter_add_sum_filter_not S (fun f => ∀ i j : Fin p, f i = f j) F).symm
  have hnc_zero : ∑ f ∈ S_nc, F f = 0 := by
    let orb : (Fin p → G) → Finset (Fin p → G) :=
      fun f => Finset.univ.image (fun k : Fin p => shift k f)
    have horb_self : ∀ f, f ∈ orb f := fun f =>
      Finset.mem_image.mpr ⟨0, Finset.mem_univ _, shift_zero f⟩
    have horb_eq : ∀ {f g}, g ∈ orb f → orb g = orb f := by
      intro f g hg
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hg
      ext h
      simp only [orb, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨j + k, (shift_shift j k f).symm⟩
      · rintro ⟨j, rfl⟩
        exact ⟨j - k, by rw [shift_shift, sub_add_cancel]⟩
    have hshift_Snc : ∀ {f}, f ∈ S_nc → ∀ k : Fin p, shift k f ∈ S_nc := by
      intro f hf k
      simp only [S_nc, S, C, Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
      refine ⟨hf.1.trans (isConj_prod_ofFn_shift k f), ?_⟩
      intro hconst
      apply hf.2
      intro i j
      have := hconst (i - k) (j - k)
      simpa [shift] using this
    have hF_shift : ∀ f (k : Fin p), F (shift k f) = F f := fun f k =>
      Fintype.prod_equiv (Equiv.addRight k) _ _ (fun _ => rfl)
    rw [← Finset.sum_fiberwise_of_maps_to (g := orb) (t := S_nc.image orb)
      (fun f hf => Finset.mem_image_of_mem orb hf) F]
    refine Finset.sum_eq_zero fun O hO => ?_
    obtain ⟨f₀, hf₀, rfl⟩ := Finset.mem_image.mp hO
    have hfiber : S_nc.filter (fun f => orb f = orb f₀) = orb f₀ := by
      ext f
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨_, hfeq⟩
        rw [← hfeq]
        exact horb_self f
      · intro hf
        obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hf
        exact ⟨hshift_Snc hf₀ k, horb_eq hf⟩
    rw [hfiber]
    have hconst_F : ∀ f ∈ orb f₀, F f = F f₀ := by
      intro f hf
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hf
      exact hF_shift f₀ k
    rw [Finset.sum_congr rfl hconst_F, Finset.sum_const, nsmul_eq_mul]
    have hnc0 : ∃ i j : Fin p, f₀ i ≠ f₀ j := by
      have := (Finset.mem_filter.mp hf₀).2
      push Not at this
      exact this
    have hcard : (orb f₀).card = p := by
      rw [Finset.card_image_of_injective _ (shift_injective_of_nonconst hnc0)]
      simp
    rw [hcard]
    simp
  have hconst_eq : ∑ f ∈ S_const, F f = (C.card : ZMod p) * w.coeff (e.symm x) := by
    let T : Finset G := Finset.univ.filter (fun g : G => e g ∈ C)
    have hbij : ∑ f ∈ S_const, F f = ∑ g ∈ T, (w.coeff g) ^ p := by
      symm
      refine Finset.sum_bij (fun g _ => fun _ : Fin p => g) ?_ ?_ ?_ ?_
      · intro g hg
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hg
        simp only [S_const, S, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨?_, fun _ _ => trivial⟩
        rw [List.ofFn_const, List.prod_replicate, ← he_apply g]
        exact hg
      · intro g₁ _ g₂ _ h
        exact congrFun h 0
      · intro f hf
        simp only [S_const, S, Finset.mem_filter, Finset.mem_univ, true_and] at hf
        refine ⟨f 0, ?_, ?_⟩
        · simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
          have hfeq : f = fun _ : Fin p => f 0 := funext (fun i => hf.2 i 0)
          rw [he_apply, ← List.prod_replicate, ← List.ofFn_const, ← hfeq]
          exact hf.1
        · funext i
          exact (hf.2 i 0).symm
      · intro g _
        simp [F]
    rw [hbij]
    simp_rw [ZMod.pow_card]
    have hT_eq : ∑ g ∈ T, w.coeff g = ∑ y ∈ C, w.coeff (e.symm y) := by
      refine Finset.sum_bij (fun g _ => e g) ?_ ?_ ?_ ?_
      · intro g hg
        exact (Finset.mem_filter.mp hg).2
      · intro g₁ _ g₂ _ h
        exact e.injective h
      · intro y hy
        refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.apply_symm_apply]
        exact hy
      · intro g _
        simp
    rw [hT_eq]
    have hconst_w : ∀ y ∈ C, w.coeff (e.symm y) = w.coeff (e.symm x) := by
      intro y hy
      have hxy : IsConj x y := (Finset.mem_filter.mp hy).2
      have hsymm : IsConj (e.symm x) (e.symm y) := by
        rw [isConj_powEquiv_symm_iff, Equiv.apply_symm_apply]
        exact hxy
      exact (center_eq_of_isConj hw hsymm).symm
    rw [Finset.sum_congr rfl hconst_w, Finset.sum_const, nsmul_eq_mul]
  have hfinal : (C.card : ZMod p) * (w ^ p).coeff x = (C.card : ZMod p) * w.coeff (e.symm x) := by
    rw [hlhs, hsum_eq, hpart, hnc_zero, add_zero, hconst_eq]
  have hcancel : (w ^ p).coeff x = w.coeff (e.symm x) := mul_left_cancel₀ hC_ne hfinal
  have hmap_eq : MonoidAlgebra.mapDomain (fun g : G => g ^ p) w =
      MonoidAlgebra.mapDomain e w := by
    congr 1
    funext g
    exact (he_apply g).symm
  rw [hmap_eq, coeff_mapDomain_equiv]
  exact hcancel

end FrobeniusCenter

section MainConstruction

variable {G : Type} [Group G] [Fintype G]

lemma mapDomain_pow_mul_center {n : ℤ} (hn : Int.gcd n (Fintype.card G : ℤ) = 1)
    {z₁ z₂ : MonoidAlgebra ℤ G}
    (hz₁ : z₁ ∈ Subring.center (MonoidAlgebra ℤ G))
    (hz₂ : z₂ ∈ Subring.center (MonoidAlgebra ℤ G)) :
    MonoidAlgebra.mapDomain (fun g : G => g ^ n) (z₁ * z₂) =
      MonoidAlgebra.mapDomain (fun g : G => g ^ n) z₁ *
        MonoidAlgebra.mapDomain (fun g : G => g ^ n) z₂ := by
  let m : ℕ := Fintype.card G
  have hm_pos : 0 < m := Fintype.card_pos
  have hm_ne : m ≠ 0 := hm_pos.ne'
  let a : ℕ := (n % (m : ℤ)).toNat
  have ha_cast : (a : ℤ) = n % (m : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg n (Nat.cast_ne_zero.mpr hm_ne))
  have ha_cop : a.Coprime m := by
    have h1 : Int.gcd (n % (m : ℤ)) (m : ℤ) = 1 := by
      rw [Int.gcd_emod]
      exact hn
    rw [← ha_cast, Int.gcd_natCast_natCast] at h1
    exact h1
  apply MonoidAlgebra.ext
  ext x
  set d : ℤ :=
    (MonoidAlgebra.mapDomain (fun g : G => g ^ n) (z₁ * z₂)).coeff x -
      (MonoidAlgebra.mapDomain (fun g : G => g ^ n) z₁ *
        MonoidAlgebra.mapDomain (fun g : G => g ^ n) z₂).coeff x with hd_def
  suffices hd : d = 0 by linarith
  by_contra hd_ne
  obtain ⟨p, hp_gt, hp_prime, hp_mod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max d.natAbs m) hm_ne ha_cop
  have : Fact p.Prime := ⟨hp_prime⟩
  have hp_gt_m : Fintype.card G < p := lt_of_le_of_lt (le_max_right _ _) hp_gt
  have hp_gt_d : d.natAbs < p := lt_of_le_of_lt (le_max_left _ _) hp_gt
  have hp_zmod : (p : ℤ) ≡ n [ZMOD (m : ℤ)] := by
    have h1 : (p : ℤ) ≡ (a : ℤ) [ZMOD (m : ℤ)] := Int.natCast_modEq_iff.mpr hp_mod
    have h2 : (a : ℤ) ≡ n [ZMOD (m : ℤ)] := by
      rw [ha_cast]
      exact Int.mod_modEq n (m : ℤ)
    exact h1.trans h2
  have hpow_eq : (fun g : G => g ^ n) = (fun g : G => g ^ p) := by
    funext g
    rw [← zpow_natCast]
    exact zpow_eq_of_modEq hp_zmod.symm g
  let red : MonoidAlgebra ℤ G →+* MonoidAlgebra (ZMod p) G :=
    MonoidAlgebra.mapRingHom G (Int.castRingHom (ZMod p))
  have hred_center : ∀ {z : MonoidAlgebra ℤ G}, z ∈ Subring.center (MonoidAlgebra ℤ G) →
      red z ∈ Subring.center (MonoidAlgebra (ZMod p) G) := by
    intro z hz
    rw [mem_center_iff_conj] at hz ⊢
    intro u g
    simp only [red, MonoidAlgebra.coeff_mapRingHom]
    rw [hz u g]
  have hcop_p : Int.gcd (p : ℤ) (Fintype.card G : ℤ) = 1 := by
    have := hp_prime.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt Fintype.card_pos hp_gt_m)
    simpa [Int.gcd_natCast_natCast] using this
  let ep : G ≃ G := powEquiv (p : ℤ) hcop_p
  have hep_eq : (fun g : G => g ^ p) = ep := by
    funext g; simp [ep, powEquiv_apply, zpow_natCast]
  have hred_map : ∀ z : MonoidAlgebra ℤ G,
      red (MonoidAlgebra.mapDomain (fun g : G => g ^ p) z) =
        MonoidAlgebra.mapDomain (fun g : G => g ^ p) (red z) := by
    intro z
    apply MonoidAlgebra.ext
    ext y
    rw [hep_eq]
    simp only [red, MonoidAlgebra.coeff_mapRingHom, coeff_mapDomain_equiv]
  have hw₁ : red z₁ ∈ Subring.center (MonoidAlgebra (ZMod p) G) := hred_center hz₁
  have hw₂ : red z₂ ∈ Subring.center (MonoidAlgebra (ZMod p) G) := hred_center hz₂
  have hw₁₂ : red z₁ * red z₂ ∈ Subring.center (MonoidAlgebra (ZMod p) G) :=
    Subring.mul_mem _ hw₁ hw₂
  have hcomm : Commute (red z₁) (red z₂) :=
    (Subring.mem_center_iff.mp hw₁ (red z₂)).symm
  have hred_eq :
      red (MonoidAlgebra.mapDomain (fun g : G => g ^ n) (z₁ * z₂)) =
        red (MonoidAlgebra.mapDomain (fun g : G => g ^ n) z₁ *
          MonoidAlgebra.mapDomain (fun g : G => g ^ n) z₂) := by
    rw [hpow_eq, map_mul, hred_map, hred_map, hred_map, map_mul]
    rw [← center_pow_prime_eq_mapDomain hp_gt_m hw₁₂,
        ← center_pow_prime_eq_mapDomain hp_gt_m hw₁,
        ← center_pow_prime_eq_mapDomain hp_gt_m hw₂]
    exact hcomm.mul_pow p
  have hcoeff_eq := congrArg (fun f : MonoidAlgebra (ZMod p) G => f.coeff x) hred_eq
  simp only [red, MonoidAlgebra.coeff_mapRingHom, Int.coe_castRingHom] at hcoeff_eq
  have hd_zero_mod : (d : ZMod p) = 0 := by
    rw [hd_def, Int.cast_sub, hcoeff_eq, sub_self]
  have hdvd : (p : ℤ) ∣ d := (ZMod.intCast_zmod_eq_zero_iff_dvd d p).mp hd_zero_mod
  have hdvd_nat : p ∣ d.natAbs := Int.natCast_dvd.mp hdvd
  have hle : p ≤ d.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hd_ne) hdvd_nat
  omega

noncomputable def centerAction (n : ℤ)
    (hn : Int.gcd n (Fintype.card G : ℤ) = 1) :
    OMA.S_mo_415174.IntegralCenter G ≃+* OMA.S_mo_415174.IntegralCenter G := by
  let e : G ≃ G := powEquiv n hn
  let k : ℤ := Int.gcdA n (Fintype.card G : ℤ)
  have hk_cop : Int.gcd k (Fintype.card G : ℤ) = 1 := by
    have hbez := Int.gcd_eq_gcd_ab n (Fintype.card G : ℤ)
    rw [hn, Nat.cast_one] at hbez
    have h1 : (1 : ℤ) = k * n + (Fintype.card G : ℤ) * Int.gcdB n (Fintype.card G : ℤ) := by
      dsimp only [k]
      linarith
    have hdvd : (Int.gcd k (Fintype.card G : ℤ) : ℤ) ∣ 1 := by
      rw [h1]
      exact dvd_add (dvd_mul_of_dvd_left (Int.gcd_dvd_left k _) n)
        (dvd_mul_of_dvd_left (Int.gcd_dvd_right k _) _)
    exact Int.ofNat_dvd_left.mp (by simpa using hdvd) |> Nat.eq_one_of_dvd_one
  have hleft : ∀ z : MonoidAlgebra ℤ G,
      MonoidAlgebra.mapDomain (fun g : G => g ^ k)
        (MonoidAlgebra.mapDomain (fun g : G => g ^ n) z) = z := by
    intro z
    apply MonoidAlgebra.ext
    ext x
    change (MonoidAlgebra.mapDomain e.symm (MonoidAlgebra.mapDomain e z)).coeff x = z.coeff x
    rw [coeff_mapDomain_equiv, coeff_mapDomain_equiv]
    simp
  have hright : ∀ z : MonoidAlgebra ℤ G,
      MonoidAlgebra.mapDomain (fun g : G => g ^ n)
        (MonoidAlgebra.mapDomain (fun g : G => g ^ k) z) = z := by
    intro z
    apply MonoidAlgebra.ext
    ext x
    change (MonoidAlgebra.mapDomain e (MonoidAlgebra.mapDomain e.symm z)).coeff x = z.coeff x
    rw [coeff_mapDomain_equiv, coeff_mapDomain_equiv]
    simp
  exact
    { toFun := fun z =>
        ⟨MonoidAlgebra.mapDomain (fun g : G => g ^ n) z.val,
          mapDomain_powEquiv_mem_center hn z.property⟩
      invFun := fun z =>
        ⟨MonoidAlgebra.mapDomain (fun g : G => g ^ k) z.val,
          mapDomain_powEquiv_mem_center hk_cop z.property⟩
      left_inv := fun z => Subtype.ext (hleft z.val)
      right_inv := fun z => Subtype.ext (hright z.val)
      map_mul' := fun z₁ z₂ => Subtype.ext (mapDomain_pow_mul_center hn z₁.property z₂.property)
      map_add' := fun z₁ z₂ => Subtype.ext (MonoidAlgebra.mapDomain_add _ z₁.val z₂.val) }

noncomputable def conjClassSum (u : G) : OMA.S_mo_415174.IntegralCenter G := by
  classical
  refine ⟨∑ x ∈ Finset.univ.filter (fun x : G => IsConj u x),
    MonoidAlgebra.single x (1 : ℤ), ?_⟩
  rw [mem_center_iff_conj]
  intro a y
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    MonoidAlgebra.coeff_single, Finsupp.single_apply, Finset.sum_ite_eq',
    Finset.mem_filter, Finset.mem_univ, true_and]
  have hiff : IsConj u (a * y * a⁻¹) ↔ IsConj u y := by
    constructor
    · intro h
      exact h.trans (isConj_iff.mpr ⟨a⁻¹, by group⟩)
    · intro h
      exact h.trans (isConj_iff.mpr ⟨a, rfl⟩)
  exact if_congr hiff rfl rfl

lemma coeff_conjClassSum_of_isConj {u y : G} (h : IsConj u y) :
    (conjClassSum u).val.coeff y = 1 := by
  classical
  simp only [conjClassSum, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    MonoidAlgebra.coeff_single, Finsupp.single_apply, Finset.sum_ite_eq',
    Finset.mem_filter, Finset.mem_univ, true_and]
  exact if_pos h

lemma coeff_conjClassSum_of_not_isConj {u y : G} (h : ¬ IsConj u y) :
    (conjClassSum u).val.coeff y = 0 := by
  classical
  simp only [conjClassSum, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    MonoidAlgebra.coeff_single, Finsupp.single_apply, Finset.sum_ite_eq',
    Finset.mem_filter, Finset.mem_univ, true_and]
  exact if_neg h

lemma conj_product_pow {n : ℤ} (hn : Int.gcd n (Fintype.card G : ℤ) = 1) (g h : G) :
    ∃ a b : G, (g * h) ^ n = (a * g ^ n * a⁻¹) * (b * h ^ n * b⁻¹) := by
  let act := centerAction (G := G) n hn
  let e : G ≃ G := powEquiv n hn
  have hact_val : ∀ z : OMA.S_mo_415174.IntegralCenter G,
      (act z).val = MonoidAlgebra.mapDomain e z.val := fun _ => rfl
  have hact_conj : ∀ u : G, act (conjClassSum u) = conjClassSum (u ^ n) := by
    intro u
    apply Subtype.ext
    apply MonoidAlgebra.ext
    ext y
    rw [hact_val, coeff_mapDomain_equiv]
    have hiff : IsConj u (e.symm y) ↔ IsConj (u ^ n) y := by
      constructor
      · intro hu
        have h' := isConj_zpow hu n
        change IsConj (u ^ n) (e (e.symm y)) at h'
        rwa [Equiv.apply_symm_apply] at h'
      · intro hu
        have h' := isConj_zpow hu (Int.gcdA n (Fintype.card G : ℤ))
        change IsConj (e.symm (e u)) (e.symm y) at h'
        rwa [Equiv.symm_apply_apply] at h'
    by_cases hy : IsConj (u ^ n) y
    · rw [coeff_conjClassSum_of_isConj (hiff.mpr hy), coeff_conjClassSum_of_isConj hy]
    · rw [coeff_conjClassSum_of_not_isConj (mt hiff.mp hy), coeff_conjClassSum_of_not_isConj hy]
  have hmul : (conjClassSum (g ^ n) * conjClassSum (h ^ n)).val =
      MonoidAlgebra.mapDomain e (conjClassSum g * conjClassSum h).val := by
    rw [← hact_conj g, ← hact_conj h, ← map_mul, hact_val]
  have heval : ((conjClassSum (g ^ n)).val * (conjClassSum (h ^ n)).val).coeff ((g * h) ^ n) =
      ((conjClassSum g).val * (conjClassSum h).val).coeff (g * h) := by
    have := congrArg (fun f : MonoidAlgebra ℤ G => f.coeff (e (g * h))) hmul
    rw [coeff_mapDomain_equiv, Equiv.symm_apply_apply] at this
    exact this
  have hpos : (0 : ℤ) < ((conjClassSum g).val * (conjClassSum h).val).coeff (g * h) := by
    rw [coeff_mul_eq_sum]
    have hnonneg : ∀ x ∈ (Finset.univ : Finset G),
        (0 : ℤ) ≤ (conjClassSum g).val.coeff x * (conjClassSum h).val.coeff (x⁻¹ * (g * h)) := by
      intro x _
      by_cases h1 : IsConj g x
      · by_cases h2 : IsConj h (x⁻¹ * (g * h))
        · rw [coeff_conjClassSum_of_isConj h1, coeff_conjClassSum_of_isConj h2]
          norm_num
        · rw [coeff_conjClassSum_of_not_isConj h2, mul_zero]
      · rw [coeff_conjClassSum_of_not_isConj h1, zero_mul]
    have hterm : (conjClassSum g).val.coeff g * (conjClassSum h).val.coeff (g⁻¹ * (g * h)) = 1 := by
      rw [coeff_conjClassSum_of_isConj (IsConj.refl g), inv_mul_cancel_left,
        coeff_conjClassSum_of_isConj (IsConj.refl h), mul_one]
    have hle := Finset.single_le_sum hnonneg (Finset.mem_univ g)
    linarith
  rw [← heval, coeff_mul_eq_sum] at hpos
  have hex : ∃ x : G, (conjClassSum (g ^ n)).val.coeff x *
      (conjClassSum (h ^ n)).val.coeff (x⁻¹ * (g * h) ^ n) ≠ 0 := by
    by_contra hall
    push Not at hall
    have hzero : (∑ x : G, (conjClassSum (g ^ n)).val.coeff x *
        (conjClassSum (h ^ n)).val.coeff (x⁻¹ * (g * h) ^ n)) = 0 :=
      Finset.sum_eq_zero (fun x _ => hall x)
    linarith
  obtain ⟨x, hx⟩ := hex
  have hx1 : IsConj (g ^ n) x := by
    by_contra h1
    rw [coeff_conjClassSum_of_not_isConj h1, zero_mul] at hx
    exact hx rfl
  have hx2 : IsConj (h ^ n) (x⁻¹ * (g * h) ^ n) := by
    by_contra h2
    rw [coeff_conjClassSum_of_not_isConj h2, mul_zero] at hx
    exact hx rfl
  obtain ⟨a, ha⟩ := isConj_iff.mp hx1
  obtain ⟨b, hb⟩ := isConj_iff.mp hx2
  refine ⟨a, b, ?_⟩
  rw [ha, hb, mul_inv_cancel_left]

end MainConstruction

end Mo415174

theorem OMA.solution : type_of% @OMA.S_mo_415174.main := by
  intro G _ _ n hn
  exact ⟨⟨Mo415174.centerAction n hn, fun _ => rfl⟩, Mo415174.conj_product_pow hn⟩
