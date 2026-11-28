import OMAReductions.R_SerreMultiplicityConjectures_supportDim_add_supportDim_le_ringKrullDim_R1

/-!
# Proof of H3 for Serre's Dimension Inequality

Cohen presentation of a complete ramified mixed-characteristic regular local ring as a
hypersurface quotient of a complete unramified regular local ring of dimension one higher.
-/

namespace OMA.H3Proof

open IsLocalRing Ideal Module
open scoped Pointwise

section RegularLocalHelpers

lemma spanFinrank_quotient_span_singleton_add_one_le {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {x : R} (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2)
    [IsLocalRing (R ⧸ Ideal.span {x})] :
    (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 ≤ (maximalIdeal R).spanFinrank := by
  classical
  let q : R →+* R ⧸ Ideal.span {x} := Ideal.Quotient.mk (Ideal.span {x})
  have hmax_quot : maximalIdeal (R ⧸ Ideal.span {x}) = (maximalIdeal R).map q := by
    have hle : RingHom.ker q ≤ maximalIdeal R := by
      rw [Ideal.mk_ker, Ideal.span_singleton_le_iff_mem]
      exact hx
    have hmax : ((maximalIdeal R).map q).IsMaximal :=
      Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective hle
    exact (IsLocalRing.eq_maximalIdeal hmax).symm
  let m := maximalIdeal R
  let k := ResidueField R
  let V := CotangentSpace R
  let v : V := m.toCotangent ⟨x, hx⟩
  have hv_ne : v ≠ 0 := fun h => hx2 ((m.toCotangent_eq_zero ⟨x, hx⟩).mp h)
  let W : Submodule k V := Submodule.span k {v}
  have hfinV : Module.Finite k V := by
    have : Module.Finite R V := Module.Finite.of_surjective m.toCotangent m.toCotangent_surjective
    exact Module.Finite.of_restrictScalars_finite R k V
  have hfinW : Module.finrank k W = 1 := finrank_span_singleton hv_ne
  have hrank : Module.finrank k (V ⧸ W) + 1 = Module.finrank k V := by
    rw [← hfinW]
    exact Submodule.finrank_quotient_add_finrank W
  have hfin_eq : Module.finrank k V = m.spanFinrank :=
    (IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace R).symm
  let n : ℕ := Module.finrank k (V ⧸ W)
  let b := Module.finBasis k (V ⧸ W)
  have hlift : ∀ i : Fin n, ∃ y : m, W.mkQ (m.toCotangent y) = b i := fun i => by
    obtain ⟨u, hu⟩ := Submodule.mkQ_surjective W (b i)
    obtain ⟨y, hy⟩ := m.toCotangent_surjective u
    exact ⟨y, by rw [hy, hu]⟩
  let y : Fin n → m := fun i => (hlift i).choose
  have hy_spec : ∀ i : Fin n, W.mkQ (m.toCotangent (y i)) = b i := fun i => (hlift i).choose_spec
  let J : Ideal R := Ideal.span (insert x (Set.range (fun i : Fin n => (y i : R))))
  have hJm : J ≤ m := by
    rw [Ideal.span_le]
    rintro z (rfl | ⟨i, rfl⟩)
    · exact hx
    · exact (y i).2
  have hm_le : m ≤ J ⊔ m ^ 2 := by
    intro a ha
    let u : V := m.toCotangent ⟨a, ha⟩
    have hdecomp : W.mkQ u = ∑ i : Fin n, b.repr (W.mkQ u) i • b i :=
      (b.sum_repr (W.mkQ u)).symm
    have hrep_lift : ∀ i : Fin n, ∃ r : R, IsLocalRing.residue R r = b.repr (W.mkQ u) i :=
      fun i => IsLocalRing.residue_surjective _
    let r : Fin n → R := fun i => (hrep_lift i).choose
    have hr : ∀ i : Fin n, IsLocalRing.residue R (r i) = b.repr (W.mkQ u) i :=
      fun i => (hrep_lift i).choose_spec
    have hsubW : u - ∑ i : Fin n, r i • m.toCotangent (y i) ∈ W := by
      rw [← Submodule.ker_mkQ W, LinearMap.mem_ker, map_sub, map_sum, sub_eq_zero]
      rw [hdecomp]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hy_spec i, ← hr i]
      have hsmul : (IsLocalRing.residue R (r i)) • m.toCotangent (y i) = r i • m.toCotangent (y i) :=
        algebraMap_smul k (r i) (m.toCotangent (y i))
      rw [← hsmul, LinearMap.map_smul]
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hsubW
    obtain ⟨r0, hr0⟩ := IsLocalRing.residue_surjective c
    have hdiff : m.toCotangent (⟨a, ha⟩ - (r0 • ⟨x, hx⟩ + ∑ i : Fin n, r i • y i)) = 0 := by
      rw [map_sub, map_add, map_sum, map_smul]
      have hsmul0 : c • v = r0 • v := by
        rw [← hr0]
        exact algebraMap_smul k r0 v
      have hsum : ∑ i : Fin n, m.toCotangent (r i • y i) = ∑ i : Fin n, r i • m.toCotangent (y i) :=
        Finset.sum_congr rfl fun i _ => map_smul _ _ _
      rw [hsum, ← hsmul0, hc]
      abel
    have hmem2 : a - (r0 * x + ∑ i : Fin n, r i * (y i : R)) ∈ m ^ 2 := by
      have := (m.toCotangent_eq_zero _).mp hdiff
      simpa [Submodule.coe_sum, smul_eq_mul] using this
    have hmemJ : r0 * x + ∑ i : Fin n, r i * (y i : R) ∈ J := by
      refine J.add_mem (J.mul_mem_left r0 (Ideal.subset_span (Set.mem_insert _ _))) ?_
      exact J.sum_mem fun i _ => J.mul_mem_left (r i)
        (Ideal.subset_span (Set.mem_insert_of_mem x ⟨i, rfl⟩))
    have ha_eq : a = (r0 * x + ∑ i : Fin n, r i * (y i : R)) +
        (a - (r0 * x + ∑ i : Fin n, r i * (y i : R))) := by ring
    rw [ha_eq]
    exact Submodule.add_mem_sup hmemJ hmem2
  have hm_eq : m = J := by
    have hm_le_smul : m ≤ J ⊔ m • m := by
      simpa [pow_two, smul_eq_mul] using hm_le
    have hfg : m.FG := m.fg_of_isNoetherianRing
    have hjac : m ≤ Ideal.jacobson ⊥ := IsLocalRing.maximalIdeal_le_jacobson ⊥
    exact le_antisymm (Submodule.le_of_le_smul_of_le_jacobson_bot hfg hjac hm_le_smul) hJm
  have hmax_span : maximalIdeal (R ⧸ Ideal.span {x}) =
      Ideal.span (Set.range (fun i : Fin n => q (y i : R))) := by
    rw [hmax_quot]
    have hmap : (maximalIdeal R).map q = J.map q := congrArg (Ideal.map q) hm_eq
    rw [hmap, Ideal.map_span]
    refine le_antisymm ?_ ?_
    · rw [Ideal.span_le]
      rintro _ ⟨z, hz, rfl⟩
      rcases Set.mem_insert_iff.mp hz with hzx | ⟨i, rfl⟩
      · rw [hzx]
        have hqx : q x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
        rw [hqx]
        exact Ideal.zero_mem _
      · exact Ideal.subset_span ⟨i, rfl⟩
    · refine Ideal.span_mono ?_
      rintro _ ⟨i, rfl⟩
      exact ⟨(y i : R), Set.mem_insert_of_mem x ⟨i, rfl⟩, rfl⟩
  have hle_n : (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank ≤ n := by
    rw [hmax_span]
    let f_img : Fin n → R ⧸ Ideal.span {x} := fun i => q (y i : R)
    have hrange : Set.range f_img = f_img '' Set.univ := Set.image_univ.symm
    calc (Ideal.span (Set.range f_img)).spanFinrank
        ≤ (Set.range f_img).ncard :=
          Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)
      _ = (f_img '' Set.univ).ncard := by rw [hrange]
      _ ≤ (Set.univ : Set (Fin n)).ncard := Set.ncard_image_le Set.finite_univ
      _ = n := by simp [Set.ncard_univ]
  have hfin_m : m.spanFinrank = (maximalIdeal R).spanFinrank := rfl
  omega

lemma isRegularLocalRing_isDomain_aux :
    ∀ (d : ℕ) (R : Type*) [CommRing R] [IsRegularLocalRing R],
      (maximalIdeal R).spanFinrank = d → IsDomain R := by
  intro d
  induction d with
  | zero =>
    intro R _ _ hd
    have hfg : (maximalIdeal R).FG := (maximalIdeal R).fg_of_isNoetherianRing
    have hfin : ((maximalIdeal R).generators : Set R).Finite := Submodule.FG.finite_generators hfg
    have hcard : ((maximalIdeal R).generators : Set R).ncard = 0 := by
      rw [Submodule.FG.generators_ncard hfg, hd]
    have hempty : (maximalIdeal R).generators = ∅ := (Set.ncard_eq_zero hfin).mp hcard
    have hbot : maximalIdeal R = ⊥ := by
      rw [← (maximalIdeal R).span_generators, hempty, Submodule.span_empty]
    have hnz : NoZeroDivisors R := ⟨fun {a b} hab => by
      by_cases ha : a = 0
      · exact Or.inl ha
      · right
        have hu : IsUnit a := by
          by_contra hnu
          have hmem : a ∈ maximalIdeal R := hnu
          rw [hbot] at hmem
          exact ha hmem
        exact hu.mul_right_eq_zero.mp hab⟩
    exact NoZeroDivisors.to_isDomain R
  | succ n ih =>
    intro R _ _ hd
    classical
    have hdim : ringKrullDim R = ((n + 1 : ℕ) : WithBot ℕ∞) := by
      rw [← hd]
      exact ((isRegularLocalRing_iff R).mp ‹IsRegularLocalRing R›).symm
    have hm_ne_bot : maximalIdeal R ≠ ⊥ := by
      intro hbot
      have h0 : (maximalIdeal R).spanFinrank = 0 := by
        rw [hbot]
        exact Submodule.spanFinrank_bot
      omega
    have hm_not_le_sq : ¬ maximalIdeal R ≤ maximalIdeal R ^ 2 := by
      intro hle
      have hbot : maximalIdeal R = ⊥ :=
        Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) (maximalIdeal R)
          (maximalIdeal R).fg_of_isNoetherianRing
          (by simpa [pow_two, smul_eq_mul] using hle)
          (IsLocalRing.maximalIdeal_le_jacobson ⊥)
      exact hm_ne_bot hbot
    have hm_not_le_min : ∀ P ∈ minimalPrimes R, ¬ maximalIdeal R ≤ P := by
      intro P hP hle
      have hPprime : P.IsPrime := hP.1.1
      have hPeq : P = maximalIdeal R :=
        le_antisymm (IsLocalRing.le_maximalIdeal hPprime.ne_top) hle
      have hdim0 : ringKrullDim R = 0 := by
        refine le_antisymm ?_ (ringKrullDim_nonneg_of_nontrivial)
        rw [ringKrullDim, Order.krullDim]
        refine iSup_le fun s => ?_
        have hlen : s.length = 0 := by
          by_contra hne
          have hpos : 0 < s.length := Nat.pos_of_ne_zero hne
          have hlt : (s ⟨0, by omega⟩).asIdeal < (s ⟨1, by omega⟩).asIdeal :=
            s.strictMono (Fin.mk_lt_mk.mpr Nat.zero_lt_one)
          have hle1 : (s ⟨1, by omega⟩).asIdeal ≤ maximalIdeal R :=
            IsLocalRing.le_maximalIdeal (s ⟨1, by omega⟩).isPrime.ne_top
          have hle0 : (s ⟨0, by omega⟩).asIdeal ≤ P := hPeq ▸ (le_of_lt hlt).trans hle1
          have heq0 : (s ⟨0, by omega⟩).asIdeal = P :=
            le_antisymm hle0 (hP.2 ⟨(s ⟨0, by omega⟩).isPrime, bot_le⟩ hle0)
          rw [heq0, hPeq] at hlt
          exact not_lt_of_ge hle1 hlt
        simp [hlen]
      rw [hdim] at hdim0
      have : n + 1 = 0 := by exact_mod_cast hdim0
      omega
    have hfinMin : (minimalPrimes R).Finite := minimalPrimes.finite_of_isNoetherianRing R
    let S : Set (Ideal R) := insert (maximalIdeal R ^ 2) (minimalPrimes R)
    have hfinS : S.Finite := hfinMin.insert _
    have hnot_sub : ¬ (maximalIdeal R : Set R) ⊆ ⋃ I ∈ S, (I : Set R) := by
      intro hsub
      have hprime : ∀ I ∈ S, I ≠ maximalIdeal R ^ 2 → I ≠ maximalIdeal R ^ 2 → I.IsPrime := by
        intro I hI hne _
        rcases Set.mem_insert_iff.mp hI with rfl | hmin
        · exact absurd rfl hne
        · exact hmin.1.1
      obtain ⟨I, hIS, hle⟩ := (Ideal.subset_union_prime_finite hfinS (f := id)
        (maximalIdeal R ^ 2) (maximalIdeal R ^ 2) hprime).mp hsub
      rcases Set.mem_insert_iff.mp hIS with rfl | hmin
      · exact hm_not_le_sq hle
      · exact hm_not_le_min I hmin hle
    obtain ⟨x, hx, hx_not⟩ := Set.not_subset.mp hnot_sub
    have hx2 : x ∉ maximalIdeal R ^ 2 := fun h =>
      hx_not (Set.mem_biUnion (Set.mem_insert _ _) h)
    have hx_min : ∀ P ∈ minimalPrimes R, x ∉ P := fun P hP h =>
      hx_not (Set.mem_biUnion (Set.mem_insert_of_mem _ hP) h)
    have hx_ne_top : Ideal.span {x} ≠ ⊤ := by
      intro htop
      have h1 : (1 : R) ∈ maximalIdeal R :=
        (Ideal.span_singleton_le_iff_mem _).mpr hx (htop ▸ Submodule.mem_top)
      exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
    have : Nontrivial (R ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial_iff.mpr hx_ne_top
    have : IsLocalRing (R ⧸ Ideal.span {x}) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective
    have hspan_le : (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank ≤ n := by
      have h := spanFinrank_quotient_span_singleton_add_one_le hx hx2
      omega
    have hdim_quot : ringKrullDim (R ⧸ Ideal.span {x}) + 1 = ringKrullDim R := by
      have h_smul : (Ideal.span {x} : Ideal R) = x • (⊤ : Ideal R) := by
        ext r
        simp only [Ideal.mem_span_singleton, Submodule.mem_smul_pointwise_iff_exists,
          Submodule.mem_top, true_and, smul_eq_mul]
        exact ⟨fun ⟨b, hb⟩ => ⟨b, hb.symm⟩, fun ⟨b, hb⟩ => ⟨b, hb.symm⟩⟩
      have heq_quot : R ⧸ Ideal.span {x} ≃+* R ⧸ (x • (⊤ : Ideal R)) :=
        (Ideal.quotientEquivAlgOfEq R h_smul).toRingEquiv
      rw [ringKrullDim_eq_of_ringEquiv heq_quot]
      rw [← Module.supportDim_quotient_eq_ringKrullDim, ← Module.supportDim_self_eq_ringKrullDim]
      refine Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal ?_ hx
      intro P hP
      have hbot_ann : Module.annihilator R R = ⊥ := by
        ext r
        simp only [Module.mem_annihilator, smul_eq_mul, Ideal.mem_bot]
        exact ⟨fun h => by simpa using h 1, fun h m => by simp [h]⟩
      rw [hbot_ann] at hP
      exact hx_min P hP
    have hdim_q_eq : ringKrullDim (R ⧸ Ideal.span {x}) = (n : WithBot ℕ∞) := by
      obtain ⟨m, hm⟩ := OMA.R_SerreMultiplicityConjectures_supportDim_add_supportDim_le_ringKrullDim_R1.ringKrullDim_quotient_eq_natCast
        (Ideal.span {x}) hx_ne_top
      rw [hm, hdim] at hdim_quot
      have hmn : m + 1 = n + 1 := by exact_mod_cast hdim_quot
      rw [hm]
      exact_mod_cast (show m = n by omega)
    have hreg_q : IsRegularLocalRing (R ⧸ Ideal.span {x}) :=
      IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ (hdim_q_eq ▸ Nat.cast_le.mpr hspan_le)
    have hspan_q_eq : (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank = n := by
      have h := (isRegularLocalRing_iff (R ⧸ Ideal.span {x})).mp hreg_q
      rw [hdim_q_eq] at h
      exact_mod_cast h
    have hdom_q : IsDomain (R ⧸ Ideal.span {x}) := ih (R ⧸ Ideal.span {x}) hspan_q_eq
    have hx_prime : (Ideal.span {x}).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp hdom_q
    obtain ⟨P, hPmin, hPle⟩ := Ideal.exists_minimalPrimes_le (J := Ideal.span {x}) bot_le
    have hPprime : P.IsPrime := hPmin.1.1
    have hx_notP : x ∉ P := hx_min P hPmin
    have hP_le_smul : P ≤ Ideal.span {x} • P := by
      intro y hy
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp (hPle hy)
      have hrP : r ∈ P := by
        have hmul : x * r ∈ P := hr ▸ hy
        exact (hPprime.mem_or_mem hmul).resolve_left hx_notP
      rw [hr]
      exact Submodule.smul_mem_smul (Ideal.subset_span rfl) hrP
    have hP_bot : P = ⊥ :=
      Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {x}) P
        (IsNoetherian.noetherian P) hP_le_smul
        (((Ideal.span_singleton_le_iff_mem _).mpr hx).trans (IsLocalRing.maximalIdeal_le_jacobson ⊥))
    have hbot_prime : (⊥ : Ideal R).IsPrime := hP_bot ▸ hPprime
    have : NoZeroDivisors R := ⟨fun {a b} hab => hbot_prime.mem_or_mem hab⟩
    exact NoZeroDivisors.to_isDomain R

lemma isRegularLocalRing_isDomain (R : Type*) [CommRing R] [IsRegularLocalRing R] :
    IsDomain R :=
  isRegularLocalRing_isDomain_aux (maximalIdeal R).spanFinrank R rfl

lemma isRegularLocalRing_quotient_of_mem_not_mem_sq {S : Type*} [CommRing S]
    [IsRegularLocalRing S] {g : S} (hg : g ∈ maximalIdeal S) (hg2 : g ∉ maximalIdeal S ^ 2) :
    IsRegularLocalRing (S ⧸ Ideal.span {g}) ∧
      ringKrullDim (S ⧸ Ideal.span {g}) + 1 = ringKrullDim S := by
  have : IsDomain S := isRegularLocalRing_isDomain S
  have hg_ne : g ≠ 0 := fun h0 => hg2 (h0.symm ▸ (maximalIdeal S ^ 2).zero_mem)
  have hg_nzd : g ∈ nonZeroDivisors S := mem_nonZeroDivisors_of_ne_zero hg_ne
  have hdim_eq : ringKrullDim (S ⧸ Ideal.span {g}) + 1 = ringKrullDim S :=
    ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors hg_nzd hg
  have hg_ne_top : Ideal.span {g} ≠ ⊤ := by
    intro htop
    have h1 : (1 : S) ∈ maximalIdeal S :=
      (Ideal.span_singleton_le_iff_mem _).mpr hg (htop ▸ Submodule.mem_top)
    exact (IsLocalRing.maximalIdeal.isMaximal S).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
  have : Nontrivial (S ⧸ Ideal.span {g}) := Ideal.Quotient.nontrivial_iff.mpr hg_ne_top
  have : IsLocalRing (S ⧸ Ideal.span {g}) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {g})) Ideal.Quotient.mk_surjective
  obtain ⟨m, hm⟩ := OMA.R_SerreMultiplicityConjectures_supportDim_add_supportDim_le_ringKrullDim_R1.ringKrullDim_quotient_eq_natCast
    (Ideal.span {g}) hg_ne_top
  have hdimS : ringKrullDim S = ((maximalIdeal S).spanFinrank : WithBot ℕ∞) :=
    ((isRegularLocalRing_iff S).mp ‹IsRegularLocalRing S›).symm
  rw [hm, hdimS] at hdim_eq
  have hm_eq : m + 1 = (maximalIdeal S).spanFinrank := by exact_mod_cast hdim_eq
  have hspan_le : (maximalIdeal (S ⧸ Ideal.span {g})).spanFinrank ≤ m := by
    have h := spanFinrank_quotient_span_singleton_add_one_le hg hg2
    omega
  refine ⟨IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ (hm ▸ Nat.cast_le.mpr hspan_le), ?_⟩
  rw [hm, hdimS]
  exact_mod_cast hm_eq

end RegularLocalHelpers

section PBasis

variable (k : Type) [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p]

def Monom (s : Set k) (n : ℕ) : Type :=
  { e : s →₀ ℕ // ∀ b : s, e b < p ^ n }

def monomVal {s : Set k} {n : ℕ} (e : Monom k p s n) : k :=
  e.1.prod (fun b m => (b : k) ^ m)

def pIndep (s : Set k) : Prop :=
  ∀ f : Monom k p s 1 →₀ k,
    f.sum (fun e c => c ^ p * monomVal k p e) = 0 → f = 0

lemma exists_pBasis :
    ∃ B : Set k, pIndep k p B ∧
      ∀ x : k, ∃ f : Monom k p B 1 →₀ k,
        f.sum (fun e c => c ^ p * monomVal k p e) = x := by
  classical
  have hzorn : ∃ B : Set k, Maximal (pIndep k p) B := by
    refine zorn_subset { s : Set k | pIndep k p s } fun c hc hchain => ?_
    refine ⟨⋃₀ c, ?_, fun s hs => Set.subset_sUnion_of_mem hs⟩
    intro f hf
    rcases Set.eq_empty_or_nonempty c with rfl | ⟨s0, hs0⟩
    · ext e
      have he0 : e.1 = 0 := by
        ext u
        exact False.elim (by simpa using u.2)
      have huniq : ∀ e' : Monom k p (⋃₀ (∅ : Set (Set k))) 1, e' = e := fun e' => by
        apply Subtype.ext
        ext u
        exact False.elim (by simpa using u.2)
      have hsum : f.sum (fun e' c => c ^ p * monomVal k p e') = f e ^ p := by
        by_cases hfe : f e = 0
        · have hf0 : f = 0 := by
            ext e'
            rw [huniq e', hfe]
            rfl
          simp [hf0, hp.out.ne_zero]
        · have hsupp : f.support = {e} := by
            ext e'
            simp [huniq e', hfe]
          rw [Finsupp.sum, hsupp, Finset.sum_singleton]
          have hmv : monomVal k p e = 1 := by
            simp [monomVal, he0]
          rw [hmv, mul_one]
      rw [hsum] at hf
      exact eq_zero_of_pow_eq_zero hf
    · let U : Finset (↥(⋃₀ c)) := f.support.biUnion fun e => e.1.support
      have hU' : ∃ s ∈ c, ∀ u ∈ U, (u : k) ∈ s := by
        refine Finset.induction_on U ⟨s0, hs0, by simp⟩ ?_
        intro u U' _ ⟨s1, hs1, hU1⟩
        obtain ⟨s2, hs2, hus2⟩ := Set.mem_sUnion.mp u.2
        rcases hchain.total hs1 hs2 with h12 | h21
        · refine ⟨s2, hs2, fun v hv => ?_⟩
          rcases Finset.mem_insert.mp hv with rfl | hv'
          · exact hus2
          · exact h12 (hU1 v hv')
        · refine ⟨s1, hs1, fun v hv => ?_⟩
          rcases Finset.mem_insert.mp hv with rfl | hv'
          · exact h21 hus2
          · exact hU1 v hv'
      obtain ⟨s, hsc, hsU⟩ := hU'
      let emb : Monom k p s 1 → Monom k p (⋃₀ c) 1 := fun e =>
        ⟨e.1.mapDomain (Set.inclusion (Set.subset_sUnion_of_mem hsc)), fun u => by
          by_cases hu : ∃ v : s, (v : k) = (u : k)
          · obtain ⟨v, hv⟩ := hu
            have hu_eq : u = Set.inclusion (Set.subset_sUnion_of_mem hsc) v := Subtype.ext hv.symm
            rw [hu_eq, Finsupp.mapDomain_apply (Set.inclusion_injective _)]
            exact e.2 v
          · have hzero : (e.1.mapDomain (Set.inclusion (Set.subset_sUnion_of_mem hsc))) u = 0 := by
              rw [Finsupp.mapDomain_of_notMem_range]
              rintro ⟨v, hv⟩
              exact hu ⟨v, congrArg Subtype.val hv⟩
            rw [hzero]
            exact pow_pos hp.out.pos 1⟩
      have hemb_inj : Function.Injective emb := by
        intro e1 e2 heq
        apply Subtype.ext
        have hval := congrArg Subtype.val heq
        exact Finsupp.mapDomain_injective (Set.inclusion_injective _) hval
      have hemb_val : ∀ e : Monom k p s 1, monomVal k p (emb e) = monomVal k p e := fun e => by
        simp only [monomVal, emb]
        rw [Finsupp.prod_mapDomain_index_inj (Set.inclusion_injective _)]
      have hsupp_in : ∀ e ∈ f.support, ∃ e' : Monom k p s 1, emb e' = e := by
        intro e he
        let e' : s →₀ ℕ := e.1.comapDomain (Set.inclusion (Set.subset_sUnion_of_mem hsc))
          (Set.inclusion_injective _).injOn
        have he'_lt : ∀ v : s, e' v < p ^ 1 := fun v => by
          simp only [e', Finsupp.comapDomain_apply]
          exact e.2 _
        refine ⟨⟨e', he'_lt⟩, ?_⟩
        apply Subtype.ext
        ext u
        by_cases hu : u ∈ e.1.support
        · have hus : (u : k) ∈ s := hsU u (Finset.mem_biUnion.mpr ⟨e, he, hu⟩)
          have hu_eq : u = Set.inclusion (Set.subset_sUnion_of_mem hsc) ⟨u.1, hus⟩ := rfl
          conv_lhs => rw [hu_eq]
          rw [Finsupp.mapDomain_apply (Set.inclusion_injective _)]
          simp [e']
        · have hu0 : e.1 u = 0 := Finsupp.notMem_support_iff.mp hu
          rw [hu0]
          by_cases hus : (u : k) ∈ s
          · have hu_eq : u = Set.inclusion (Set.subset_sUnion_of_mem hsc) ⟨u.1, hus⟩ := rfl
            conv_lhs => rw [hu_eq]
            rw [Finsupp.mapDomain_apply (Set.inclusion_injective _)]
            simp [e', hu0]
          · rw [Finsupp.mapDomain_of_notMem_range]
            rintro ⟨v, hv⟩
            exact hus (congrArg Subtype.val hv ▸ v.2)
      let g : Monom k p s 1 →₀ k := f.comapDomain emb hemb_inj.injOn
      have hg_sum : g.sum (fun e c => c ^ p * monomVal k p e) =
          f.sum (fun e c => c ^ p * monomVal k p e) := by
        rw [Finsupp.sum, Finsupp.sum]
        refine Finset.sum_bij (fun e _ => emb e) ?_ ?_ ?_ ?_
        · intro e he
          rw [Finsupp.mem_support_iff] at he ⊢
          simpa [g] using he
        · intro e1 _ e2 _ h
          exact hemb_inj h
        · intro e he
          obtain ⟨e', rfl⟩ := hsupp_in e he
          refine ⟨e', ?_, rfl⟩
          rw [Finsupp.mem_support_iff] at he ⊢
          simpa [g] using he
        · intro e _
          simp [g, hemb_val]
      have hg0 : g = 0 := hc hsc g (hg_sum.trans hf)
      ext e
      by_cases he : e ∈ f.support
      · obtain ⟨e', rfl⟩ := hsupp_in e he
        have : g e' = 0 := by simp [hg0]
        simpa [g] using this
      · exact Finsupp.notMem_support_iff.mp he
  obtain ⟨B, hBmax⟩ := hzorn
  have hBindep : pIndep k p B := hBmax.prop
  let Lset : Set k := { x : k | ∃ f : Monom k p B 1 →₀ k,
    f.sum (fun e c => c ^ p * monomVal k p e) = x }
  have hL_zero : (0 : k) ∈ Lset := ⟨0, by simp⟩
  have hL_one : (1 : k) ∈ Lset := by
    let e0 : Monom k p B 1 := ⟨0, fun _ => pow_pos hp.out.pos 1⟩
    refine ⟨Finsupp.single e0 1, ?_⟩
    rw [Finsupp.sum_single_index (by simp [zero_pow hp.out.ne_zero])]
    simp [e0, monomVal]
  have hL_add : ∀ x y, x ∈ Lset → y ∈ Lset → x + y ∈ Lset := by
    rintro x y ⟨fx, rfl⟩ ⟨fy, rfl⟩
    refine ⟨fx + fy, ?_⟩
    rw [Finsupp.sum_add_index']
    · intro e; simp [zero_pow hp.out.ne_zero]
    · intro e a b
      rw [add_pow_char a b, add_mul]
  have hL_neg : ∀ x, x ∈ Lset → -x ∈ Lset := by
    rintro x ⟨fx, rfl⟩
    refine ⟨-fx, ?_⟩
    have hsum : (-fx).sum (fun e c => c ^ p * monomVal k p e) +
        fx.sum (fun e c => c ^ p * monomVal k p e) = 0 := by
      rw [← Finsupp.sum_add_index']
      · simp
      · intro e; simp [zero_pow hp.out.ne_zero]
      · intro e a b; rw [add_pow_char a b, add_mul]
    exact eq_neg_of_add_eq_zero_left hsum
  have hL_mul_term : ∀ (c1 c2 : k) (e1 e2 : Monom k p B 1),
      (c1 ^ p * monomVal k p e1) * (c2 ^ p * monomVal k p e2) ∈ Lset := by
    intro c1 c2 e1 e2
    let e : B →₀ ℕ := e1.1 + e2.1
    let q : B →₀ ℕ := e.mapRange (· / p) (Nat.zero_div p)
    let r : B →₀ ℕ := e.mapRange (· % p) (Nat.zero_mod p)
    have hr_lt : ∀ b : B, r b < p ^ 1 := fun b => by
      simp only [r, Finsupp.mapRange_apply, pow_one]
      exact Nat.mod_lt _ hp.out.pos
    have he_eq : e = p • q + r := by
      ext b
      simp only [q, r, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
      exact (Nat.div_add_mod (e b) p).symm
    let rM : Monom k p B 1 := ⟨r, hr_lt⟩
    let qVal : k := q.prod (fun b m => (b : k) ^ m)
    have hprod_eq : monomVal k p e1 * monomVal k p e2 = qVal ^ p * monomVal k p rM := by
      have h1 : monomVal k p e1 * monomVal k p e2 = e.prod (fun b m => (b : k) ^ m) := by
        simp only [monomVal, e]
        rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
      rw [h1, he_eq, Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
      congr 1
      simp only [qVal, Finsupp.prod]
      have hsupp : (p • q).support = q.support := by
        ext b
        simp [hp.out.ne_zero]
      rw [hsupp, ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun b _ => ?_
      simp only [Finsupp.smul_apply, smul_eq_mul]
      rw [mul_comm, pow_mul]
    refine ⟨Finsupp.single rM (c1 * c2 * qVal), ?_⟩
    rw [Finsupp.sum_single_index (by simp [zero_pow hp.out.ne_zero])]
    calc (c1 * c2 * qVal) ^ p * monomVal k p rM
        = c1 ^ p * c2 ^ p * (qVal ^ p * monomVal k p rM) := by ring
      _ = c1 ^ p * c2 ^ p * (monomVal k p e1 * monomVal k p e2) := by rw [hprod_eq]
      _ = (c1 ^ p * monomVal k p e1) * (c2 ^ p * monomVal k p e2) := by ring
  have hsum_mem : ∀ {ι : Type} (s : Finset ι) (g : ι → k),
      (∀ i ∈ s, g i ∈ Lset) → ∑ i ∈ s, g i ∈ Lset := by
    intro ι s g
    refine Finset.induction_on s (fun _ => hL_zero) ?_
    intro a s' ha ih hg
    rw [Finset.sum_insert ha]
    exact hL_add _ _ (hg a (Finset.mem_insert_self a s'))
      (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))
  have hL_mul : ∀ x y, x ∈ Lset → y ∈ Lset → x * y ∈ Lset := by
    rintro x y ⟨fx, rfl⟩ ⟨fy, rfl⟩
    rw [Finsupp.sum, Finsupp.sum, Finset.sum_mul]
    refine hsum_mem fx.support _ fun e1 _ => ?_
    rw [Finset.mul_sum]
    exact hsum_mem fy.support _ fun e2 _ => hL_mul_term _ _ e1 e2
  have hL_pow_mul : ∀ (c : k) {x : k}, x ∈ Lset → c ^ p * x ∈ Lset := by
    rintro c x ⟨fx, rfl⟩
    refine ⟨c • fx, ?_⟩
    rw [Finsupp.sum, Finsupp.sum, Finset.mul_sum]
    by_cases hc : c = 0
    · simp [hc, zero_pow hp.out.ne_zero]
    · have hsupp : (c • fx).support = fx.support := by
        ext e
        simp [hc]
      rw [hsupp]
      refine Finset.sum_congr rfl fun e _ => ?_
      simp [mul_pow, mul_assoc]
  have hL_pow : ∀ {x : k}, x ∈ Lset → ∀ m : ℕ, x ^ m ∈ Lset := by
    intro x hx m
    induction m with
    | zero => simpa using hL_one
    | succ m ih => rw [pow_succ]; exact hL_mul _ _ ih hx
  have hL_inv : ∀ x, x ∈ Lset → x⁻¹ ∈ Lset := by
    intro x hx
    by_cases hx0 : x = 0
    · simp [hx0, hL_zero]
    · have heq : (x⁻¹) ^ p * x ^ (p - 1) = x⁻¹ := by
        have hp1 : 1 ≤ p := hp.out.one_le
        calc (x⁻¹) ^ p * x ^ (p - 1)
            = x⁻¹ * (x⁻¹) ^ (p - 1) * x ^ (p - 1) := by
              rw [← pow_succ', Nat.sub_add_cancel hp1]
          _ = x⁻¹ * ((x⁻¹ * x) ^ (p - 1)) := by rw [mul_assoc, ← mul_pow]
          _ = x⁻¹ := by rw [inv_mul_cancel₀ hx0, one_pow, mul_one]
      rw [← heq]
      exact hL_pow_mul x⁻¹ (hL_pow hx (p - 1))
  let L : Subfield k :=
    { carrier := Lset
      zero_mem' := hL_zero
      one_mem' := hL_one
      add_mem' := fun hx hy => hL_add _ _ hx hy
      neg_mem' := fun hx => hL_neg _ hx
      mul_mem' := fun hx hy => hL_mul _ _ hx hy
      inv_mem' := fun {_} hx => hL_inv _ hx }
  refine ⟨B, hBindep, fun a => ?_⟩
  by_contra ha_not
  have ha_notL : a ∉ L := ha_not
  have ha_notB : a ∉ B := by
    intro haB
    apply ha_notL
    let e : Monom k p B 1 := ⟨Finsupp.single ⟨a, haB⟩ 1, fun b => by
      by_cases h : b = ⟨a, haB⟩
      · subst h; simp [hp.out.one_lt]
      · simp [Finsupp.single_eq_of_ne h, hp.out.pos]⟩
    refine ⟨Finsupp.single e 1, ?_⟩
    rw [Finsupp.sum_single_index (by simp [zero_pow hp.out.ne_zero])]
    simp [e, monomVal, Finsupp.prod_single_index]
  have ha_pow_mem : a ^ p ∈ L := by
    show a ^ p ∈ Lset
    have : a ^ p * (1 : k) ∈ Lset := hL_pow_mul a hL_one
    simpa using this
  have hlin_a : ∀ g : Fin p → L, (∑ i : Fin p, (g i : k) * a ^ (i : ℕ)) = 0 → ∀ i, g i = 0 := by
    intro g hg
    by_contra hne
    push Not at hne
    let P : Polynomial L := ∑ i : Fin p, Polynomial.C (g i) * Polynomial.X ^ (i : ℕ)
    have hP_coeff : ∀ i : Fin p, P.coeff (i : ℕ) = g i := fun i => by
      simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        have : (i : ℕ) ≠ (j : ℕ) := fun h => hji (Fin.ext h.symm)
        simp [this]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    have hP_ne : P ≠ 0 := by
      obtain ⟨i, hi⟩ := hne
      intro h0
      have := hP_coeff i
      rw [h0, Polynomial.coeff_zero] at this
      exact hi this.symm
    have hP_deg : P.natDegree < p := by
      refine lt_of_le_of_lt (Polynomial.natDegree_sum_le _ _) ?_
      change Finset.univ.sup (fun i : Fin p => (Polynomial.C (g i) * Polynomial.X ^ (i : ℕ)).natDegree) < p
      rw [Finset.sup_lt_iff hp.out.pos]
      intro i _
      exact lt_of_le_of_lt (Polynomial.natDegree_C_mul_X_pow_le _ _) i.2
    have hP_eval : Polynomial.aeval a P = 0 := by
      simp only [P, map_sum, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
      exact hg
    have ha_int : IsIntegral L a := by
      refine ⟨Polynomial.X ^ p - Polynomial.C ⟨a ^ p, ha_pow_mem⟩, ?_, ?_⟩
      · exact Polynomial.monic_X_pow_sub_C _ hp.out.ne_zero
      · rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
        exact sub_self (a ^ p)
    let μ : Polynomial L := minpoly L a
    have hμ_monic : μ.Monic := minpoly.monic ha_int
    have hμ_dvd_P : μ ∣ P := minpoly.dvd L a hP_eval
    have hμ_deg_lt : μ.natDegree < p :=
      lt_of_le_of_lt (Polynomial.natDegree_le_of_dvd hμ_dvd_P hP_ne) hP_deg
    have hμ_dvd_Xp : μ ∣ Polynomial.X ^ p - Polynomial.C ⟨a ^ p, ha_pow_mem⟩ :=
      minpoly.dvd L a (by
        rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
        exact sub_self (a ^ p))
    have hμ_map_dvd : μ.map (algebraMap L k) ∣ (Polynomial.X - Polynomial.C a) ^ p := by
      have h1 := Polynomial.map_dvd (algebraMap L k) hμ_dvd_Xp
      have h2 : (Polynomial.X ^ p - Polynomial.C ⟨a ^ p, ha_pow_mem⟩ : Polynomial L).map
          (algebraMap L k) = (Polynomial.X - Polynomial.C a) ^ p := by
        rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
        change Polynomial.X ^ p - Polynomial.C (a ^ p) = (Polynomial.X - Polynomial.C a) ^ p
        rw [sub_pow_char, map_pow]
      exact h2 ▸ h1
    have hμ_deg_pos : 0 < μ.natDegree := minpoly.natDegree_pos ha_int
    have hXsub_prime : Prime (Polynomial.X - Polynomial.C a : Polynomial k) :=
      (Polynomial.irreducible_X_sub_C a).prime
    obtain ⟨m, hm_le, hassoc⟩ := (dvd_prime_pow hXsub_prime p).mp hμ_map_dvd
    have hμ_map_monic : (μ.map (algebraMap L k)).Monic := hμ_monic.map _
    have hpow_monic : ((Polynomial.X - Polynomial.C a : Polynomial k) ^ m).Monic :=
      (Polynomial.monic_X_sub_C a).pow m
    have hμ_map_eq : μ.map (algebraMap L k) = (Polynomial.X - Polynomial.C a) ^ m :=
      Polynomial.eq_of_monic_of_associated hμ_map_monic hpow_monic hassoc
    have hm_eq : m = μ.natDegree := by
      have hdeg := congrArg Polynomial.natDegree hμ_map_eq
      rw [hμ_monic.natDegree_map, Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one] at hdeg
      exact hdeg.symm
    have hm_pos : 0 < m := hm_eq ▸ hμ_deg_pos
    have hm_lt : m < p := hm_eq ▸ hμ_deg_lt
    have hcoeff : ((Polynomial.X - Polynomial.C a : Polynomial k) ^ m).coeff (m - 1) =
        -(m : k) * a := by
      rw [sub_eq_add_neg, add_pow, Polynomial.finsetSum_coeff]
      rw [Finset.sum_eq_single (m - 1)]
      · have h1 : m - (m - 1) = 1 := by omega
        rw [h1, pow_one, ← Polynomial.C_neg, Polynomial.coeff_mul_natCast,
          Polynomial.coeff_mul_C, Polynomial.coeff_X_pow_self]
        have hchoose : m.choose (m - 1) = m := by
          rw [← Nat.choose_symm (by omega), h1, Nat.choose_one_right]
        rw [hchoose]
        ring
      · intro j hj hne_j
        rw [Finset.mem_range] at hj
        rw [← Polynomial.C_neg, ← map_pow, Polynomial.coeff_mul_natCast,
          Polynomial.coeff_mul_C, Polynomial.coeff_X_pow, if_neg (Ne.symm hne_j)]
        simp
      · intro hnot
        exact absurd (Finset.mem_range.mpr (by omega)) hnot
    have hcoeff_L : (μ.coeff (m - 1) : k) = -(m : k) * a := by
      rw [← hcoeff, ← hμ_map_eq, Polynomial.coeff_map]
      rfl
    have hm_ne0 : (m : k) ≠ 0 := by
      intro h0
      have hdvd : p ∣ m := (CharP.cast_eq_zero_iff k p m).mp h0
      have hle : p ≤ m := Nat.le_of_dvd hm_pos hdvd
      omega
    have ha_eq : a = -((m : k)⁻¹ * (μ.coeff (m - 1) : k)) := by
      rw [hcoeff_L]
      field_simp [hm_ne0]
    have haL : a ∈ L := by
      rw [ha_eq]
      exact L.neg_mem (L.mul_mem (L.inv_mem (natCast_mem L m)) (μ.coeff (m - 1)).2)
    exact ha_notL haL
  have hins : pIndep k p (insert a B) := by
    intro f hf
    let aIns : ↥(insert a B) := ⟨a, Set.mem_insert a B⟩
    let split : Monom k p (insert a B) 1 → Fin p × Monom k p B 1 := fun e =>
      (⟨e.1 aIns, by simpa using e.2 aIns⟩,
       ⟨e.1.comapDomain (Set.inclusion (Set.subset_insert a B)) (Set.inclusion_injective _).injOn,
        fun b => by
          simp only [Finsupp.comapDomain_apply]
          exact e.2 _⟩)
    have hsplit_inj : Function.Injective split := by
      intro e1 e2 h
      have h1 : e1.1 aIns = e2.1 aIns := congrArg (fun x => x.1.1) h
      have h2 : ∀ b : B, e1.1 ⟨b.1, Set.mem_insert_of_mem a b.2⟩ =
          e2.1 ⟨b.1, Set.mem_insert_of_mem a b.2⟩ := fun b => by
        have := congrArg (fun x => x.2.1 b) h
        simpa [split] using this
      apply Subtype.ext
      ext u
      rcases Set.mem_insert_iff.mp u.2 with hu | hu
      · have : u = aIns := Subtype.ext hu
        rw [this, h1]
      · exact h2 ⟨u.1, hu⟩
    have hsplit_val : ∀ e : Monom k p (insert a B) 1,
        monomVal k p e = monomVal k p (split e).2 * a ^ ((split e).1 : ℕ) := fun e => by
      simp only [monomVal, split]
      have hsupp : (e.1.comapDomain (Set.inclusion (Set.subset_insert a B))
          (Set.inclusion_injective _).injOn).prod (fun b m => (b : k) ^ m) * a ^ e.1 aIns =
          e.1.prod (fun u m => (u : k) ^ m) := by
        rw [Finsupp.prod, Finsupp.prod]
        by_cases ha0 : e.1 aIns = 0
        · rw [ha0, pow_zero, mul_one]
          refine Finset.prod_bij (fun b _ => Set.inclusion (Set.subset_insert a B) b) ?_ ?_ ?_ ?_
          · intro b hb
            rw [Finsupp.mem_support_iff] at hb ⊢
            simpa using hb
          · intro b1 _ b2 _ h
            exact Set.inclusion_injective _ h
          · intro u hu
            have hne : u ≠ aIns := fun h => by
              rw [Finsupp.mem_support_iff, h] at hu
              exact hu ha0
            have huB : u.1 ∈ B := (Set.mem_insert_iff.mp u.2).resolve_left fun h => hne (Subtype.ext h)
            refine ⟨⟨u.1, huB⟩, ?_, rfl⟩
            rw [Finsupp.mem_support_iff] at hu ⊢
            simpa using hu
          · intro b _; rfl
        · have hmem : aIns ∈ e.1.support := Finsupp.mem_support_iff.mpr ha0
          rw [← Finset.prod_erase_mul e.1.support _ hmem]
          congr 1
          refine Finset.prod_bij (fun b _ => Set.inclusion (Set.subset_insert a B) b) ?_ ?_ ?_ ?_
          · intro b hb
            rw [Finset.mem_erase, Finsupp.mem_support_iff]
            refine ⟨fun h => ha_notB (by
              have hv : b.1 = a := congrArg Subtype.val h
              exact hv ▸ b.2), ?_⟩
            rw [Finsupp.mem_support_iff] at hb
            simpa using hb
          · intro b1 _ b2 _ h
            exact Set.inclusion_injective _ h
          · intro u hu
            rw [Finset.mem_erase, Finsupp.mem_support_iff] at hu
            have huB : u.1 ∈ B := (Set.mem_insert_iff.mp u.2).resolve_left fun h => hu.1 (Subtype.ext h)
            refine ⟨⟨u.1, huB⟩, ?_, rfl⟩
            rw [Finsupp.mem_support_iff]
            simpa using hu.2
          · intro b _; rfl
      exact hsupp.symm
    let fiber : Fin p → Monom k p B 1 →₀ k := fun i =>
      f.sum fun e c => if (split e).1 = i then Finsupp.single (split e).2 c else 0
    have hfiber_val : ∀ i : Fin p,
        (fiber i).sum (fun e' c => c ^ p * monomVal k p e') =
        f.sum (fun e c => if (split e).1 = i then c ^ p * monomVal k p (split e).2 else 0) := by
      intro i
      dsimp only [fiber]
      rw [Finsupp.sum_sum_index]
      · refine Finsupp.sum_congr fun e _ => ?_
        split_ifs
        · rw [Finsupp.sum_single_index (by simp [zero_pow hp.out.ne_zero])]
        · simp
      · intro e'; simp [zero_pow hp.out.ne_zero]
      · intro e' c1 c2; rw [add_pow_char c1 c2, add_mul]
    have hsum_eq : ∑ i : Fin p, ((fiber i).sum (fun e' c => c ^ p * monomVal k p e')) * a ^ (i : ℕ) =
        f.sum (fun e c => c ^ p * monomVal k p e) := by
      simp_rw [hfiber_val, Finsupp.sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [Finset.sum_eq_single (split e).1]
      · simp [hsplit_val e, mul_assoc]
      · intro i _ hi
        simp [Ne.symm hi]
      · intro hi; exact absurd (Finset.mem_univ _) hi
    let gL : Fin p → L := fun i => ⟨(fiber i).sum (fun e' c => c ^ p * monomVal k p e'), ⟨fiber i, rfl⟩⟩
    have hgL_sum : ∑ i : Fin p, (gL i : k) * a ^ (i : ℕ) = 0 := hsum_eq.trans hf
    have hgL_zero : ∀ i : Fin p, gL i = 0 := hlin_a gL hgL_sum
    have hfiber_zero : ∀ i : Fin p, fiber i = 0 := fun i =>
      hBindep (fiber i) (congrArg Subtype.val (hgL_zero i))
    ext e
    have hfe : fiber (split e).1 (split e).2 = f e := by
      dsimp only [fiber]
      rw [Finsupp.sum_apply, Finsupp.sum]
      by_cases hmem : e ∈ f.support
      · rw [Finset.sum_eq_single e]
        · simp
        · intro e' _ hne
          split_ifs with h1
          · rw [Finsupp.single_apply, if_neg]
            intro h2
            exact hne (hsplit_inj (Prod.ext h1 h2))
          · rfl
        · intro h; exact absurd hmem h
      · have hf0 : f e = 0 := Finsupp.notMem_support_iff.mp hmem
        rw [hf0]
        refine Finset.sum_eq_zero fun e' he' => ?_
        have hne : e' ≠ e := fun h => hmem (h ▸ he')
        split_ifs with h1
        · rw [Finsupp.single_apply, if_neg]
          intro h2
          exact hne (hsplit_inj (Prod.ext h1 h2))
        · rfl
    rw [← hfe, hfiber_zero]
    rfl
  have hsub : insert a B ⊆ B := hBmax.le_of_ge hins (Set.subset_insert a B)
  exact ha_notB (hsub (Set.mem_insert a B))

lemma pBasis_pow_repr {B : Set k} (hBindep : pIndep k p B)
    (hBspan : ∀ x : k, ∃ f : Monom k p B 1 →₀ k,
      f.sum (fun e c => c ^ p * monomVal k p e) = x) :
    ∀ n : ℕ,
      (∀ f : Monom k p B n →₀ k,
        f.sum (fun e c => c ^ (p ^ n) * monomVal k p e) = 0 → f = 0) ∧
      (∀ x : k, ∃ f : Monom k p B n →₀ k,
        f.sum (fun e c => c ^ (p ^ n) * monomVal k p e) = x) := by
  classical
  intro n
  induction n with
  | zero =>
    constructor
    · intro f hf
      ext e
      have he0 : e.1 = 0 := by
        ext b
        have := e.2 b
        simp at this
        exact this
      have huniq : ∀ e' : Monom k p B 0, e' = e := fun e' => by
        apply Subtype.ext
        ext b
        have h1 := e'.2 b
        have h2 := e.2 b
        simp at h1 h2
        omega
      have hsum : f.sum (fun e' c => c ^ (p ^ 0) * monomVal k p e') = f e := by
        by_cases hfe : f e = 0
        · have hf0 : f = 0 := by ext e'; rw [huniq e', hfe]; rfl
          simp [hf0]
        · have hsupp : f.support = {e} := by ext e'; simp [huniq e', hfe]
          rw [Finsupp.sum, hsupp, Finset.sum_singleton]
          simp [monomVal, he0]
      exact hsum.symm.trans hf
    · intro x
      let e0 : Monom k p B 0 := ⟨0, fun _ => by simp⟩
      refine ⟨Finsupp.single e0 x, ?_⟩
      rw [Finsupp.sum_single_index (by simp)]
      simp [e0, monomVal]
  | succ n ih =>
    let decomp : Monom k p B (n + 1) → Monom k p B 1 × Monom k p B n := fun e =>
      (⟨e.1.mapRange (· % p) (Nat.zero_mod p), fun b => by
          simp only [Finsupp.mapRange_apply, pow_one]
          exact Nat.mod_lt _ hp.out.pos⟩,
       ⟨e.1.mapRange (· / p) (Nat.zero_div p), fun b => by
          simp only [Finsupp.mapRange_apply]
          exact Nat.div_lt_of_lt_mul (by simpa [pow_succ'] using e.2 b)⟩)
    let recomp : Monom k p B 1 × Monom k p B n → Monom k p B (n + 1) := fun ⟨r, q⟩ =>
      ⟨r.1 + p • q.1, fun b => by
        simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
        have hr : r.1 b < p := by simpa using r.2 b
        have hq : q.1 b < p ^ n := q.2 b
        calc r.1 b + p * q.1 b
            < p + p * q.1 b := Nat.add_lt_add_right hr _
          _ = p * (q.1 b + 1) := by ring
          _ ≤ p * p ^ n := Nat.mul_le_mul_left p hq
          _ = p ^ (n + 1) := (pow_succ' p n).symm⟩
    have hlr : ∀ e, recomp (decomp e) = e := fun e => by
      apply Subtype.ext
      ext b
      simp only [decomp, recomp, Finsupp.add_apply, Finsupp.smul_apply,
        Finsupp.mapRange_apply, smul_eq_mul]
      rw [add_comm]
      exact Nat.div_add_mod (e.1 b) p
    have hval_recomp : ∀ r q, monomVal k p (recomp (r, q)) =
        monomVal k p r * (monomVal k p q) ^ p := fun r q => by
      simp only [monomVal, recomp]
      rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
      congr 1
      simp only [Finsupp.prod]
      have hsupp : (p • q.1).support = q.1.support := by
        ext b; simp [hp.out.ne_zero]
      rw [hsupp, ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun b _ => ?_
      simp only [Finsupp.smul_apply, smul_eq_mul]
      rw [mul_comm, pow_mul]
    constructor
    · intro f hf
      let fiber : Monom k p B 1 → Monom k p B n →₀ k := fun r =>
        f.sum fun e c => if (decomp e).1 = r then Finsupp.single (decomp e).2 c else 0
      let outer : Monom k p B 1 →₀ k :=
        f.sum fun e c => Finsupp.single (decomp e).1 (c ^ (p ^ n) * monomVal k p (decomp e).2)
      have houter_eq : ∀ r : Monom k p B 1,
          outer r = (fiber r).sum (fun q c => c ^ (p ^ n) * monomVal k p q) := fun r => by
        dsimp only [outer, fiber]
        rw [Finsupp.sum_apply, Finsupp.sum_sum_index]
        · refine Finsupp.sum_congr fun e _ => ?_
          split_ifs with h
          · subst h
            rw [Finsupp.single_eq_same,
              Finsupp.sum_single_index (by simp [zero_pow (pow_ne_zero n hp.out.ne_zero)])]
          · rw [Finsupp.single_eq_of_ne (Ne.symm h), Finsupp.sum_zero_index]
        · intro q; simp [zero_pow (pow_ne_zero n hp.out.ne_zero)]
        · intro q c1 c2; rw [add_pow_char_pow c1 c2, add_mul]
      have houter_sum : outer.sum (fun r c => c ^ p * monomVal k p r) =
          f.sum (fun e c => c ^ (p ^ (n + 1)) * monomVal k p e) := by
        dsimp only [outer]
        rw [Finsupp.sum_sum_index]
        · refine Finsupp.sum_congr fun e _ => ?_
          rw [Finsupp.sum_single_index (by simp [zero_pow hp.out.ne_zero])]
          have hmv : monomVal k p e = monomVal k p (decomp e).1 * (monomVal k p (decomp e).2) ^ p := by
            conv_lhs => rw [← hlr e]
            exact hval_recomp _ _
          rw [hmv, mul_pow, ← pow_mul, ← pow_succ]
          ring
        · intro r; simp [zero_pow hp.out.ne_zero]
        · intro r c1 c2; rw [add_pow_char c1 c2, add_mul]
      have houter0 : outer = 0 := hBindep outer (houter_sum.trans hf)
      have hfiber0 : ∀ r, fiber r = 0 := fun r => by
        refine ih.1 (fiber r) ?_
        rw [← houter_eq r, houter0]
        rfl
      ext e
      have hfe : fiber (decomp e).1 (decomp e).2 = f e := by
        dsimp only [fiber]
        rw [Finsupp.sum_apply, Finsupp.sum]
        by_cases hmem : e ∈ f.support
        · rw [Finset.sum_eq_single e]
          · simp
          · intro e' _ hne
            split_ifs with h1
            · rw [Finsupp.single_apply, if_neg]
              intro h2
              exact hne (by rw [← hlr e', ← hlr e, Prod.ext h1 h2])
            · rfl
          · intro h; exact absurd hmem h
        · have hf0 : f e = 0 := Finsupp.notMem_support_iff.mp hmem
          rw [hf0]
          refine Finset.sum_eq_zero fun e' he' => ?_
          have hne : e' ≠ e := fun h => hmem (h ▸ he')
          split_ifs with h1
          · rw [Finsupp.single_apply, if_neg]
            intro h2
            exact hne (by rw [← hlr e', ← hlr e, Prod.ext h1 h2])
          · rfl
      rw [← hfe, hfiber0]
      rfl
    · intro x
      obtain ⟨g, hg⟩ := hBspan x
      let h : Monom k p B 1 → Monom k p B n →₀ k := fun r => (ih.2 (g r)).choose
      have hh : ∀ r, (h r).sum (fun q c => c ^ (p ^ n) * monomVal k p q) = g r :=
        fun r => (ih.2 (g r)).choose_spec
      let f : Monom k p B (n + 1) →₀ k :=
        g.sum fun r _ => (h r).sum fun q c => Finsupp.single (recomp (r, q)) c
      refine ⟨f, ?_⟩
      dsimp only [f]
      rw [Finsupp.sum_sum_index]
      · have hstep : ∀ r ∈ g.support,
            ((h r).sum fun q c => Finsupp.single (recomp (r, q)) c).sum
              (fun e c => c ^ (p ^ (n + 1)) * monomVal k p e) =
            (g r) ^ p * monomVal k p r := fun r _ => by
          rw [Finsupp.sum_sum_index]
          · calc (h r).sum (fun q c =>
                  (Finsupp.single (recomp (r, q)) c).sum
                    (fun e c' => c' ^ (p ^ (n + 1)) * monomVal k p e))
                = (h r).sum (fun q c =>
                    (c ^ (p ^ n) * monomVal k p q) ^ p * monomVal k p r) := by
                  refine Finsupp.sum_congr fun q _ => ?_
                  rw [Finsupp.sum_single_index (by simp [zero_pow (pow_ne_zero (n + 1) hp.out.ne_zero)])]
                  rw [hval_recomp r q, mul_pow, ← pow_mul, ← pow_succ]
                  ring
              _ = ((h r).sum (fun q c => c ^ (p ^ n) * monomVal k p q)) ^ p * monomVal k p r := by
                  rw [Finsupp.sum, Finsupp.sum, ← Finset.sum_mul]
                  congr 1
                  exact (map_sum (frobenius k p) _ _).symm
              _ = (g r) ^ p * monomVal k p r := by rw [hh r]
          · intro e; simp [zero_pow (pow_ne_zero (n + 1) hp.out.ne_zero)]
          · intro e c1 c2; rw [add_pow_char_pow c1 c2, add_mul]
        rw [Finsupp.sum, Finset.sum_congr rfl hstep]
        exact hg
      · intro e; simp [zero_pow (pow_ne_zero (n + 1) hp.out.ne_zero)]
      · intro e c1 c2; rw [add_pow_char_pow c1 c2, add_mul]

end PBasis

section CohenRingConstruction

variable (k : Type) [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p]
variable (B : Set k)

abbrev PerfK : Type := PerfectClosure k p

abbrev WittK : Type := WittVector p (PerfK k p)

def iotaK : k →+* PerfK k p := PerfectClosure.of k p

lemma iotaK_injective : Function.Injective (iotaK k p) :=
  RingHom.injective (iotaK k p)

noncomputable def frobRingHom : ℕ → WittK k p →+* WittK k p
  | 0 => RingHom.id _
  | n + 1 => WittVector.frobenius.comp (frobRingHom n)

lemma frobRingHom_coeff (n : ℕ) (w : WittK k p) (i : ℕ) :
    (frobRingHom k p n w).coeff i = (w.coeff i) ^ (p ^ n) := by
  induction n with
  | zero => simp [frobRingHom]
  | succ n ih =>
    simp only [frobRingHom, RingHom.comp_apply, WittVector.coeff_frobenius_charP, ih,
      ← pow_mul, ← pow_succ]

noncomputable def Fpow (n : ℕ) : WittVector p k →+* WittK k p :=
  (frobRingHom k p n).comp (WittVector.map (iotaK k p))

lemma Fpow_coeff (n : ℕ) (z : WittVector p k) (i : ℕ) :
    (Fpow k p n z).coeff i = iotaK k p ((z.coeff i) ^ (p ^ n)) := by
  simp only [Fpow, RingHom.comp_apply, frobRingHom_coeff, WittVector.map_coeff, map_pow]

lemma Fpow_succ_eq (n : ℕ) (z : WittVector p k) :
    Fpow k p (n + 1) z = Fpow k p n (WittVector.frobenius z) := by
  ext i
  rw [Fpow_coeff, Fpow_coeff, WittVector.coeff_frobenius_charP, ← pow_mul, ← pow_succ']

lemma Fpow_succ_verschiebung (n : ℕ) (z : WittVector p k) :
    Fpow k p (n + 1) (WittVector.verschiebung z) = (p : WittK k p) * Fpow k p n z := by
  have h1 : WittVector.frobenius (WittVector.map (iotaK k p) (WittVector.verschiebung z)) =
      (p : WittK k p) * WittVector.map (iotaK k p) z := by
    rw [WittVector.map_verschiebung, WittVector.frobenius_verschiebung, mul_comm]
  have hcomm : ∀ m (w : WittK k p),
      frobRingHom k p (m + 1) w = frobRingHom k p m (WittVector.frobenius w) := by
    intro m
    induction m with
    | zero => intro w; rfl
    | succ m ih =>
      intro w
      change WittVector.frobenius (frobRingHom k p (m + 1) w) =
        WittVector.frobenius (frobRingHom k p m (WittVector.frobenius w))
      rw [ih w]
  calc Fpow k p (n + 1) (WittVector.verschiebung z)
      = frobRingHom k p n (WittVector.frobenius (WittVector.map (iotaK k p) (WittVector.verschiebung z))) :=
        hcomm n _
    _ = frobRingHom k p n ((p : WittK k p) * WittVector.map (iotaK k p) z) := by rw [h1]
    _ = (p : WittK k p) * Fpow k p n z := by
        rw [map_mul, map_natCast]
        rfl

noncomputable def teichB (b : B) : WittK k p :=
  WittVector.teichmuller p (iotaK k p b.1)

noncomputable def tMonom (e : B →₀ ℕ) : WittK k p :=
  e.prod (fun b m => teichB k p B b ^ m)

lemma tMonom_zero : tMonom k p B 0 = 1 := by
  simp [tMonom]

lemma tMonom_add (e1 e2 : B →₀ ℕ) :
    tMonom k p B (e1 + e2) = tMonom k p B e1 * tMonom k p B e2 := by
  simp only [tMonom]
  exact Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

lemma tMonom_coeff_zero (e : B →₀ ℕ) :
    (tMonom k p B e).coeff 0 = iotaK k p (e.prod (fun b m => (b : k) ^ m)) := by
  change WittVector.constantCoeff (tMonom k p B e) = _
  simp only [tMonom, Finsupp.prod, map_prod, map_pow]
  refine Finset.prod_congr rfl fun b _ => ?_
  rfl

lemma tMonom_pow_mul (n : ℕ) (q : B →₀ ℕ) :
    tMonom k p B ((p ^ n) • q) = Fpow k p n (q.prod (fun b m => WittVector.teichmuller p (b : k) ^ m)) := by
  classical
  have h1 : tMonom k p B ((p ^ n) • q) = (tMonom k p B q) ^ (p ^ n) := by
    simp only [tMonom, Finsupp.prod]
    have hsupp : ((p ^ n) • q).support = q.support := by
      ext b
      simp only [Finsupp.mem_support_iff, Finsupp.smul_apply, smul_eq_mul, ne_eq, mul_eq_zero,
        pow_ne_zero n hp.out.ne_zero, false_or]
    rw [hsupp, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun b _ => ?_
    simp only [Finsupp.smul_apply, smul_eq_mul]
    rw [mul_comm, pow_mul]
  rw [h1]
  have hteich : ∀ a : k, Fpow k p n (WittVector.teichmuller p a) =
      WittVector.teichmuller p (iotaK k p a) ^ (p ^ n) := fun a => by
    ext i
    rw [Fpow_coeff, ← map_pow (WittVector.teichmuller p)]
    cases i with
    | zero =>
      rw [WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero, map_pow]
    | succ i =>
      rw [WittVector.teichmuller_coeff_pos p a (i + 1) (Nat.succ_pos i),
        zero_pow (pow_ne_zero n hp.out.ne_zero), map_zero,
        WittVector.teichmuller_coeff_pos p _ (i + 1) (Nat.succ_pos i)]
  simp only [tMonom, Finsupp.prod, map_prod, map_pow, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [hteich b.1, ← pow_mul, mul_comm, pow_mul]
  rfl

noncomputable def SSub (n : ℕ) : Subring (WittK k p) :=
  Subring.closure (Set.range (teichB k p B) ∪ Set.range (Fpow k p n))

lemma SSub_antitone : Antitone (SSub k p B) := by
  refine antitone_nat_of_succ_le fun n => ?_
  rw [SSub, Subring.closure_le]
  rintro x (⟨b, rfl⟩ | ⟨z, rfl⟩)
  · exact Subring.subset_closure (Or.inl ⟨b, rfl⟩)
  · rw [Fpow_succ_eq]
    exact Subring.subset_closure (Or.inr ⟨WittVector.frobenius z, rfl⟩)

lemma mem_SSub_iff_exists_sum (n : ℕ) (x : WittK k p) :
    x ∈ SSub k p B n ↔
      ∃ f : Monom k p B n →₀ WittVector p k,
        x = f.sum (fun e z => Fpow k p n z * tMonom k p B e.1) := by
  classical
  constructor
  · intro hx
    let T : Subring (WittK k p) :=
      { carrier := { y | ∃ f : Monom k p B n →₀ WittVector p k,
          y = f.sum (fun e z => Fpow k p n z * tMonom k p B e.1) }
        zero_mem' := ⟨0, by simp⟩
        one_mem' := by
          let e0 : Monom k p B n := ⟨0, fun _ => pow_pos hp.out.pos n⟩
          refine ⟨Finsupp.single e0 1, ?_⟩
          rw [Finsupp.sum_single_index (by simp)]
          simp [e0, tMonom_zero]
        add_mem' := by
          rintro _ _ ⟨f1, rfl⟩ ⟨f2, rfl⟩
          refine ⟨f1 + f2, ?_⟩
          rw [Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by rw [map_add, add_mul])]
        neg_mem' := by
          rintro _ ⟨f, rfl⟩
          refine ⟨-f, ?_⟩
          have hsum : (-f).sum (fun e z => Fpow k p n z * tMonom k p B e.1) +
              f.sum (fun e z => Fpow k p n z * tMonom k p B e.1) = 0 := by
            rw [← Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by rw [map_add, add_mul])]
            simp
          exact eq_neg_of_add_eq_zero_left hsum |>.symm
        mul_mem' := by
          have hterm : ∀ (z1 z2 : WittVector p k) (e1 e2 : Monom k p B n),
              ∃ f : Monom k p B n →₀ WittVector p k,
                (Fpow k p n z1 * tMonom k p B e1.1) * (Fpow k p n z2 * tMonom k p B e2.1) =
                f.sum (fun e z => Fpow k p n z * tMonom k p B e.1) := by
            intro z1 z2 e1 e2
            let e : B →₀ ℕ := e1.1 + e2.1
            let q : B →₀ ℕ := e.mapRange (· / p ^ n) (Nat.zero_div _)
            let r : B →₀ ℕ := e.mapRange (· % p ^ n) (Nat.zero_mod _)
            have hr_lt : ∀ b : B, r b < p ^ n := fun b => by
              simp only [r, Finsupp.mapRange_apply]
              exact Nat.mod_lt _ (pow_pos hp.out.pos n)
            have he_eq : e1.1 + e2.1 = (p ^ n) • q + r := by
              ext b
              simp only [e, q, r, Finsupp.add_apply, Finsupp.smul_apply,
                Finsupp.mapRange_apply, smul_eq_mul]
              exact (Nat.div_add_mod (e1.1 b + e2.1 b) (p ^ n)).symm
            let rM : Monom k p B n := ⟨r, hr_lt⟩
            let qW : WittVector p k := q.prod (fun b m => WittVector.teichmuller p (b : k) ^ m)
            refine ⟨Finsupp.single rM (z1 * z2 * qW), ?_⟩
            rw [Finsupp.sum_single_index (by simp)]
            have ht : tMonom k p B e1.1 * tMonom k p B e2.1 = Fpow k p n qW * tMonom k p B r := by
              rw [← tMonom_add, he_eq, tMonom_add, tMonom_pow_mul]
            calc (Fpow k p n z1 * tMonom k p B e1.1) * (Fpow k p n z2 * tMonom k p B e2.1)
                = Fpow k p n z1 * Fpow k p n z2 * (tMonom k p B e1.1 * tMonom k p B e2.1) := by ring
              _ = Fpow k p n z1 * Fpow k p n z2 * (Fpow k p n qW * tMonom k p B r) := by rw [ht]
              _ = Fpow k p n (z1 * z2 * qW) * tMonom k p B rM.1 := by
                  simp only [map_mul, rM]; ring
          have hadd_mem : ∀ {y1 y2 : WittK k p},
              (∃ f : Monom k p B n →₀ WittVector p k, y1 = f.sum (fun e z => Fpow k p n z * tMonom k p B e.1)) →
              (∃ f : Monom k p B n →₀ WittVector p k, y2 = f.sum (fun e z => Fpow k p n z * tMonom k p B e.1)) →
              ∃ f : Monom k p B n →₀ WittVector p k, y1 + y2 = f.sum (fun e z => Fpow k p n z * tMonom k p B e.1) := by
            rintro _ _ ⟨f1, rfl⟩ ⟨f2, rfl⟩
            exact ⟨f1 + f2, (Finsupp.sum_add_index' (fun _ => by simp)
              (fun _ _ _ => by rw [map_add, add_mul])).symm⟩
          have hfin_sum : ∀ {ι : Type} (s : Finset ι) (g : ι → WittK k p),
              (∀ i ∈ s, ∃ f : Monom k p B n →₀ WittVector p k,
                g i = f.sum (fun e z => Fpow k p n z * tMonom k p B e.1)) →
              ∃ f : Monom k p B n →₀ WittVector p k,
                ∑ i ∈ s, g i = f.sum (fun e z => Fpow k p n z * tMonom k p B e.1) := by
            intro ι s g
            refine Finset.induction_on s (fun _ => ⟨0, by simp⟩) ?_
            intro a s' ha ih hg
            rw [Finset.sum_insert ha]
            exact hadd_mem (hg a (Finset.mem_insert_self a s'))
              (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))
          rintro _ _ ⟨f1, rfl⟩ ⟨f2, rfl⟩
          rw [Finsupp.sum, Finsupp.sum, Finset.sum_mul]
          refine hfin_sum f1.support _ fun e1 _ => ?_
          rw [Finset.mul_sum]
          exact hfin_sum f2.support _ fun e2 _ => hterm _ _ e1 e2 }
    have hle : SSub k p B n ≤ T := by
      rw [SSub, Subring.closure_le]
      rintro y (⟨b, rfl⟩ | ⟨z, rfl⟩)
      · cases n with
        | zero =>
          let e0 : Monom k p B 0 := ⟨0, fun _ => by simp⟩
          refine ⟨Finsupp.single e0 (WittVector.teichmuller p b.1), ?_⟩
          rw [Finsupp.sum_single_index (by simp), tMonom_zero, mul_one]
          simp [Fpow, frobRingHom, teichB]
        | succ m =>
          let eb : Monom k p B (m + 1) := ⟨Finsupp.single b 1, fun b' => by
            by_cases h : b' = b
            · subst h
              rw [Finsupp.single_eq_same]
              exact one_lt_pow₀ hp.out.one_lt (Nat.succ_ne_zero m)
            · rw [Finsupp.single_eq_of_ne h]
              exact pow_pos hp.out.pos _⟩
          refine ⟨Finsupp.single eb 1, ?_⟩
          rw [Finsupp.sum_single_index (by simp), map_one, one_mul]
          simp [eb, tMonom, Finsupp.prod_single_index]
      · let e0 : Monom k p B n := ⟨0, fun _ => pow_pos hp.out.pos n⟩
        refine ⟨Finsupp.single e0 z, ?_⟩
        rw [Finsupp.sum_single_index (by simp), tMonom_zero, mul_one]
    exact hle hx
  · rintro ⟨f, rfl⟩
    rw [Finsupp.sum]
    refine Subring.sum_mem _ fun e _ => Subring.mul_mem _ ?_ ?_
    · exact Subring.subset_closure (Or.inr ⟨f e, rfl⟩)
    · simp only [tMonom, Finsupp.prod]
      exact (SSub k p B n).prod_mem fun b _ => (SSub k p B n).pow_mem
        (Subring.subset_closure (Or.inl ⟨b, rfl⟩)) _

lemma SSub_inter_p (hBindep : pIndep k p B)
    (hBspan : ∀ x : k, ∃ f : Monom k p B 1 →₀ k,
      f.sum (fun e c => c ^ p * monomVal k p e) = x)
    (n : ℕ) {x : WittK k p} (hx : x ∈ SSub k p B (n + 1))
    (hxp : x ∈ Ideal.span {(p : WittK k p)}) :
    ∃ y ∈ SSub k p B n, x = (p : WittK k p) * y := by
  classical
  obtain ⟨f, rfl⟩ := (mem_SSub_iff_exists_sum k p B (n + 1) x).mp hx
  have hx0 : (f.sum (fun e z => Fpow k p (n + 1) z * tMonom k p B e.1)).coeff 0 = 0 :=
    (WittVector.mem_span_p_iff_coeff_zero_eq_zero _).mp hxp
  let f0 : Monom k p B (n + 1) →₀ k := f.mapRange (fun z => z.coeff 0) (WittVector.zero_coeff p k 0)
  have hf0_sum : f0.sum (fun e c => c ^ (p ^ (n + 1)) * monomVal k p e) = 0 := by
    apply iotaK_injective k p
    rw [map_zero, ← hx0]
    change iotaK k p (f0.sum (fun e c => c ^ (p ^ (n + 1)) * monomVal k p e)) =
      WittVector.constantCoeff (f.sum (fun e z => Fpow k p (n + 1) z * tMonom k p B e.1))
    rw [Finsupp.sum_mapRange_index (fun _ => by simp [zero_pow (pow_ne_zero (n + 1) hp.out.ne_zero)])]
    rw [Finsupp.sum, Finsupp.sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [map_mul, map_mul]
    congr 1
    · exact (Fpow_coeff k p (n + 1) (f e) 0).symm
    · exact (tMonom_coeff_zero k p B e.1).symm
  have hf0_zero : f0 = 0 :=
    (pBasis_pow_repr k p hBindep hBspan (n + 1)).1 f0 hf0_sum
  have hcoeff0 : ∀ e : Monom k p B (n + 1), (f e).coeff 0 = 0 := fun e => by
    have := congrArg (fun g : Monom k p B (n + 1) →₀ k => g e) hf0_zero
    simpa [f0] using this
  have hshift : ∀ e : Monom k p B (n + 1), f e = WittVector.verschiebung ((f e).shift 1) := fun e => by
    have h1 := WittVector.eq_iterate_verschiebung (x := f e) (n := 1) (fun i hi => by
      have : i = 0 := by omega
      subst this
      exact hcoeff0 e)
    simpa using h1
  let y : WittK k p := f.sum (fun e z => Fpow k p n (z.shift 1) * tMonom k p B e.1)
  have hy_mem : y ∈ SSub k p B n := by
    dsimp only [y]
    rw [Finsupp.sum]
    refine Subring.sum_mem _ fun e _ => Subring.mul_mem _ ?_ ?_
    · exact Subring.subset_closure (Or.inr ⟨(f e).shift 1, rfl⟩)
    · simp only [tMonom, Finsupp.prod]
      exact (SSub k p B n).prod_mem fun b _ => (SSub k p B n).pow_mem
        (Subring.subset_closure (Or.inl ⟨b, rfl⟩)) _
  refine ⟨y, hy_mem, ?_⟩
  dsimp only [y]
  rw [Finsupp.sum, Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  conv_lhs => rw [hshift e, Fpow_succ_verschiebung]
  ring

lemma coeff_zero_mem_range_of_mem_SSub (n : ℕ) {x : WittK k p} (hx : x ∈ SSub k p B n) :
    ∃ a : k, x.coeff 0 = iotaK k p a := by
  obtain ⟨f, rfl⟩ := (mem_SSub_iff_exists_sum k p B n x).mp hx
  refine ⟨f.sum (fun e z => (z.coeff 0) ^ (p ^ n) * monomVal k p e), ?_⟩
  change WittVector.constantCoeff (f.sum (fun e z => Fpow k p n z * tMonom k p B e.1)) = _
  rw [Finsupp.sum, Finsupp.sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [map_mul, map_mul]
  congr 1
  · exact Fpow_coeff k p n (f e) 0
  · exact tMonom_coeff_zero k p B e.1

lemma exists_mem_SSub_coeff_zero_eq (hBindep : pIndep k p B)
    (hBspan : ∀ x : k, ∃ f : Monom k p B 1 →₀ k,
      f.sum (fun e c => c ^ p * monomVal k p e) = x)
    (n : ℕ) (a : k) :
    ∃ x ∈ SSub k p B n, x.coeff 0 = iotaK k p a := by
  classical
  obtain ⟨f, hf⟩ := (pBasis_pow_repr k p hBindep hBspan n).2 a
  let fW : Monom k p B n →₀ WittVector p k :=
    f.mapRange (fun c => WittVector.teichmuller p c) (WittVector.teichmuller_zero p)
  let x : WittK k p := fW.sum (fun e z => Fpow k p n z * tMonom k p B e.1)
  refine ⟨x, (mem_SSub_iff_exists_sum k p B n x).mpr ⟨fW, rfl⟩, ?_⟩
  change WittVector.constantCoeff x = iotaK k p a
  rw [← hf]
  dsimp only [x, fW]
  rw [Finsupp.sum_mapRange_index (fun _ => by simp)]
  rw [Finsupp.sum, Finsupp.sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [map_mul, map_mul]
  congr 1
  · exact Fpow_coeff k p n (WittVector.teichmuller p (f e)) 0
  · exact tMonom_coeff_zero k p B e.1

lemma SSub_le_SSub_add_pow (hBindep : pIndep k p B)
    (hBspan : ∀ x : k, ∃ f : Monom k p B 1 →₀ k,
      f.sum (fun e c => c ^ p * monomVal k p e) = x) :
    ∀ n m : ℕ, 1 ≤ n → n ≤ m → ∀ x ∈ SSub k p B n,
      ∃ y ∈ SSub k p B m, x - y ∈ Ideal.span {(p : WittK k p) ^ n} := by
  intro n
  induction n with
  | zero => intro m h0; omega
  | succ n ih =>
    intro m _ hnm x hx
    cases n with
    | zero =>
      obtain ⟨a, ha⟩ := coeff_zero_mem_range_of_mem_SSub k p B 1 hx
      obtain ⟨y, hy, hy0⟩ := exists_mem_SSub_coeff_zero_eq k p B hBindep hBspan m a
      refine ⟨y, hy, ?_⟩
      rw [pow_one, WittVector.mem_span_p_iff_coeff_zero_eq_zero]
      rw [← WittVector.constantCoeff_apply, map_sub]
      change x.coeff 0 - y.coeff 0 = 0
      rw [ha, hy0, sub_self]
    | succ n' =>
      obtain ⟨a, ha⟩ := coeff_zero_mem_range_of_mem_SSub k p B (n' + 2) hx
      obtain ⟨y0, hy0_mem, hy0_coeff⟩ := exists_mem_SSub_coeff_zero_eq k p B hBindep hBspan m a
      have hy0_le : y0 ∈ SSub k p B (n' + 2) := SSub_antitone k p B hnm hy0_mem
      have hdiff_p : x - y0 ∈ Ideal.span {(p : WittK k p)} := by
        rw [WittVector.mem_span_p_iff_coeff_zero_eq_zero, ← WittVector.constantCoeff_apply, map_sub]
        change x.coeff 0 - y0.coeff 0 = 0
        rw [ha, hy0_coeff, sub_self]
      obtain ⟨u, hu_mem, hxu⟩ := SSub_inter_p k p B hBindep hBspan (n' + 1)
        ((SSub k p B (n' + 2)).sub_mem hx hy0_le) hdiff_p
      obtain ⟨v, hv_mem, huv⟩ := ih m (Nat.succ_le_succ (Nat.zero_le _)) (by omega) u hu_mem
      refine ⟨y0 + (p : WittK k p) * v, (SSub k p B m).add_mem hy0_mem
        ((SSub k p B m).mul_mem (natCast_mem _ p) hv_mem), ?_⟩
      obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp huv
      rw [Ideal.mem_span_singleton]
      refine ⟨w, ?_⟩
      have h1 : x - (y0 + (p : WittK k p) * v) = (p : WittK k p) * (u - v) := by
        linear_combination hxu
      rw [h1, hw]
      ring

noncomputable def BSub (n : ℕ) : Subring (WittK k p) where
  carrier := { x : WittK k p | ∃ s ∈ SSub k p B n, x - s ∈ Ideal.span {(p : WittK k p) ^ n} }
  zero_mem' := ⟨0, (SSub k p B n).zero_mem, by simp⟩
  one_mem' := ⟨1, (SSub k p B n).one_mem, by simp⟩
  add_mem' := by
    rintro x y ⟨sx, hsx, hx⟩ ⟨sy, hsy, hy⟩
    refine ⟨sx + sy, (SSub k p B n).add_mem hsx hsy, ?_⟩
    have : x + y - (sx + sy) = (x - sx) + (y - sy) := by ring
    rw [this]
    exact Ideal.add_mem _ hx hy
  neg_mem' := by
    rintro x ⟨sx, hsx, hx⟩
    refine ⟨-sx, (SSub k p B n).neg_mem hsx, ?_⟩
    have : -x - -sx = -(x - sx) := by ring
    rw [this]
    exact Submodule.neg_mem _ hx
  mul_mem' := by
    rintro x y ⟨sx, hsx, hx⟩ ⟨sy, hsy, hy⟩
    refine ⟨sx * sy, (SSub k p B n).mul_mem hsx hsy, ?_⟩
    have : x * y - sx * sy = (x - sx) * y + sx * (y - sy) := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_right y _ hx) (Ideal.mul_mem_left _ sx hy)

lemma BSub_antitone : Antitone (BSub k p B) := by
  refine antitone_nat_of_succ_le fun n x ⟨s, hs, hxs⟩ => ?_
  refine ⟨s, SSub_antitone k p B (Nat.le_succ n) hs, ?_⟩
  have hle : Ideal.span {(p : WittK k p) ^ (n + 1)} ≤ Ideal.span {(p : WittK k p) ^ n} := by
    rw [Ideal.span_singleton_le_span_singleton]
    exact pow_dvd_pow _ (Nat.le_succ n)
  exact hle hxs

noncomputable def CohenSub : Subring (WittK k p) :=
  ⨅ n : ℕ, BSub k p B (n + 1)

abbrev CohenRing : Type := CohenSub k p B

lemma mem_CohenSub_iff (x : WittK k p) :
    x ∈ CohenSub k p B ↔ ∀ n : ℕ, 1 ≤ n → x ∈ BSub k p B n := by
  simp only [CohenSub, Subring.mem_iInf]
  constructor
  · intro h n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    exact h m
  · intro h n
    exact h (n + 1) (Nat.succ_le_succ (Nat.zero_le n))

lemma exists_cohen_sub_mem_pow (hBindep : pIndep k p B)
    (hBspan : ∀ x : k, ∃ f : Monom k p B 1 →₀ k,
      f.sum (fun e c => c ^ p * monomVal k p e) = x)
    (n : ℕ) (hn : 1 ≤ n) {s : WittK k p} (hs : s ∈ SSub k p B n) :
    ∃ c : CohenRing k p B, (c : WittK k p) - s ∈ Ideal.span {(p : WittK k p) ^ n} := by
  classical
  have hstep : ∀ k0 : ℕ, ∀ x ∈ SSub k p B (n + k0),
      ∃ y ∈ SSub k p B (n + k0 + 1), x - y ∈ Ideal.span {(p : WittK k p) ^ (n + k0)} :=
    fun k0 x hx => SSub_le_SSub_add_pow k p B hBindep hBspan (n + k0) (n + k0 + 1)
      (by omega) (Nat.le_succ _) x hx
  let seq : (j : ℕ) → { x : WittK k p // x ∈ SSub k p B (n + j) } :=
    Nat.rec ⟨s, hs⟩ fun j prev =>
      ⟨(hstep j prev.1 prev.2).choose, (hstep j prev.1 prev.2).choose_spec.1⟩
  have hseq_diff : ∀ j : ℕ, (seq j).1 - (seq (j + 1)).1 ∈ Ideal.span {(p : WittK k p) ^ (n + j)} :=
    fun j => (hstep j (seq j).1 (seq j).2).choose_spec.2
  have hseq_le : ∀ {i j : ℕ}, i ≤ j →
      (seq i).1 - (seq j).1 ∈ Ideal.span {(p : WittK k p) ^ (n + i)} := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => simp
    | succ j hij ih =>
      have h1 : (seq i).1 - (seq (j + 1)).1 = ((seq i).1 - (seq j).1) + ((seq j).1 - (seq (j + 1)).1) := by
        ring
      rw [h1]
      refine Ideal.add_mem _ ih ?_
      have hle : Ideal.span {(p : WittK k p) ^ (n + j)} ≤ Ideal.span {(p : WittK k p) ^ (n + i)} := by
        rw [Ideal.span_singleton_le_span_singleton]
        exact pow_dvd_pow _ (Nat.add_le_add_left hij n)
      exact hle (hseq_diff j)
  let cauchy : ℕ → WittK k p := fun m => (seq m).1
  have hcauchy : ∀ {a b : ℕ}, a ≤ b →
      cauchy a ≡ cauchy b [SMOD (Ideal.span {(p : WittK k p)} ^ a • (⊤ : Submodule (WittK k p) (WittK k p)))] := by
    intro a b hab
    rw [SModEq.sub_mem, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top]
    have hle : Ideal.span {(p : WittK k p) ^ (n + a)} ≤ Ideal.span {(p : WittK k p) ^ a} := by
      rw [Ideal.span_singleton_le_span_singleton]
      exact pow_dvd_pow _ (Nat.le_add_left a n)
    exact hle (hseq_le hab)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {(p : WittK k p)}) (M := WittK k p) cauchy hcauchy
  have hL_diff : ∀ j : ℕ, L - (seq j).1 ∈ Ideal.span {(p : WittK k p) ^ (n + j)} := by
    intro j
    have h1 := hL (n + j)
    rw [SModEq.sub_mem, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top] at h1
    have h1' : L - (seq (n + j)).1 ∈ Ideal.span {(p : WittK k p) ^ (n + j)} := by
      simpa [cauchy, neg_sub] using Submodule.neg_mem _ h1
    have h2 : (seq (n + j)).1 - (seq j).1 ∈ Ideal.span {(p : WittK k p) ^ (n + j)} := by
      have hneg := Submodule.neg_mem _ (hseq_le (Nat.le_add_left j n))
      simpa [neg_sub] using hneg
    have h3 : L - (seq j).1 = (L - (seq (n + j)).1) + ((seq (n + j)).1 - (seq j).1) := by ring
    rw [h3]
    exact Ideal.add_mem _ h1' h2
  have hL_mem : L ∈ CohenSub k p B := by
    rw [mem_CohenSub_iff]
    intro m hm
    by_cases hmn : m ≤ n
    · refine BSub_antitone k p B hmn ⟨s, hs, ?_⟩
      simpa [seq] using hL_diff 0
    · obtain ⟨j, rfl⟩ : ∃ j, m = n + j := ⟨m - n, by omega⟩
      exact ⟨(seq j).1, (seq j).2, hL_diff j⟩
  refine ⟨⟨L, hL_mem⟩, ?_⟩
  simpa [seq] using hL_diff 0

lemma CohenRing_inter_p (hBindep : pIndep k p B)
    (hBspan : ∀ x : k, ∃ f : Monom k p B 1 →₀ k,
      f.sum (fun e c => c ^ p * monomVal k p e) = x)
    (c : CohenRing k p B) (hcp : (c : WittK k p) ∈ Ideal.span {(p : WittK k p)}) :
    ∃ c' : CohenRing k p B, c = (p : CohenRing k p B) * c' := by
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hcp
  have hy_mem : y ∈ CohenSub k p B := by
    rw [mem_CohenSub_iff]
    intro n hn
    have hc_mem : (c : WittK k p) ∈ BSub k p B (n + 1) :=
      (mem_CohenSub_iff k p B _).mp c.2 (n + 1) (by omega)
    obtain ⟨s, hs, hcs⟩ := hc_mem
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp hcs
    have hsp : s ∈ Ideal.span {(p : WittK k p)} := by
      rw [Ideal.mem_span_singleton]
      refine ⟨y - (p : WittK k p) ^ n * w, ?_⟩
      calc s = (c : WittK k p) - ((c : WittK k p) - s) := by ring
        _ = (p : WittK k p) * y - (p : WittK k p) ^ (n + 1) * w := by rw [hw, hy]
        _ = (p : WittK k p) * (y - (p : WittK k p) ^ n * w) := by rw [pow_succ']; ring
    obtain ⟨t, ht, hst⟩ := SSub_inter_p k p B hBindep hBspan n hs hsp
    refine ⟨t, ht, ?_⟩
    rw [Ideal.mem_span_singleton]
    refine ⟨w, ?_⟩
    have hmul : (p : WittK k p) * (y - t) = (p : WittK k p) * ((p : WittK k p) ^ n * w) := by
      calc (p : WittK k p) * (y - t)
          = (c : WittK k p) - s := by rw [hy, hst]; ring
        _ = (p : WittK k p) ^ (n + 1) * w := hw
        _ = (p : WittK k p) * ((p : WittK k p) ^ n * w) := by rw [pow_succ']; ring
    have hmul0 : (y - t - (p : WittK k p) ^ n * w) * (p : WittK k p) = 0 := by
      linear_combination hmul
    exact sub_eq_zero.mp (WittVector.eq_zero_of_p_mul_eq_zero _ hmul0)
  refine ⟨⟨y, hy_mem⟩, Subtype.ext ?_⟩
  simpa using hy

lemma CohenRing_inter_p_pow (hBindep : pIndep k p B)
    (hBspan : ∀ x : k, ∃ f : Monom k p B 1 →₀ k,
      f.sum (fun e c => c ^ p * monomVal k p e) = x)
    (n : ℕ) (c : CohenRing k p B) :
    (c : WittK k p) ∈ Ideal.span {(p : WittK k p) ^ n} ↔
      c ∈ Ideal.span {(p : CohenRing k p B) ^ n} := by
  induction n generalizing c with
  | zero => simp
  | succ n ih =>
    constructor
    · intro hc
      have hcp : (c : WittK k p) ∈ Ideal.span {(p : WittK k p)} := by
        have hle : Ideal.span {(p : WittK k p) ^ (n + 1)} ≤ Ideal.span {(p : WittK k p)} := by
          rw [Ideal.span_singleton_le_span_singleton]
          exact dvd_pow_self _ (Nat.succ_ne_zero n)
        exact hle hc
      obtain ⟨c', rfl⟩ := CohenRing_inter_p k p B hBindep hBspan c hcp
      have hc' : (c' : WittK k p) ∈ Ideal.span {(p : WittK k p) ^ n} := by
        obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp hc
        rw [Ideal.mem_span_singleton]
        refine ⟨w, ?_⟩
        have hmul0 : ((c' : WittK k p) - (p : WittK k p) ^ n * w) * (p : WittK k p) = 0 := by
          have : (p : WittK k p) * (c' : WittK k p) = (p : WittK k p) ^ (n + 1) * w := by
            simpa using hw
          rw [pow_succ'] at this
          linear_combination this
        exact sub_eq_zero.mp (WittVector.eq_zero_of_p_mul_eq_zero _ hmul0)
      obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp ((ih c').mp hc')
      rw [Ideal.mem_span_singleton]
      refine ⟨d, ?_⟩
      rw [hd, pow_succ']
      ring
    · intro hc
      obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp hc
      rw [Ideal.mem_span_singleton]
      exact ⟨(d : WittK k p), by simpa using congrArg Subtype.val hd⟩

lemma CohenRing_isUnit_of_coeff_zero_ne_zero (hBindep : pIndep k p B)
    (hBspan : ∀ x : k, ∃ f : Monom k p B 1 →₀ k,
      f.sum (fun e c => c ^ p * monomVal k p e) = x)
    (c : CohenRing k p B) (hc : (c : WittK k p).coeff 0 ≠ 0) : IsUnit c := by
  have huW : IsUnit (c : WittK k p) := WittVector.isUnit_of_coeff_zero_ne_zero _ hc
  let uW : (WittK k p)ˣ := huW.unit
  let uWinv : WittK k p := (uW⁻¹ : (WittK k p)ˣ)
  have huWinv_mul : uWinv * (c : WittK k p) = 1 := uW.inv_mul
  have hmul_uWinv : (c : WittK k p) * uWinv = 1 := uW.mul_inv
  have hinv_mem : uWinv ∈ CohenSub k p B := by
    rw [mem_CohenSub_iff]
    intro n hn
    have hc1 : (c : WittK k p) ∈ BSub k p B 1 := (mem_CohenSub_iff k p B _).mp c.2 1 le_rfl
    obtain ⟨s1, hs1, hcs1⟩ := hc1
    obtain ⟨a0, ha0⟩ := coeff_zero_mem_range_of_mem_SSub k p B 1 hs1
    have hca0 : (c : WittK k p).coeff 0 = iotaK k p a0 := by
      have h0 := (WittVector.mem_span_p_iff_coeff_zero_eq_zero _).mp (by simpa using hcs1)
      rw [← WittVector.constantCoeff_apply, map_sub, sub_eq_zero] at h0
      exact h0.trans ha0
    have ha0_ne : a0 ≠ 0 := fun h0 => hc (by rw [hca0, h0, map_zero])
    obtain ⟨b0, hb0_mem, hb0_coeff⟩ := exists_mem_SSub_coeff_zero_eq k p B hBindep hBspan n a0⁻¹
    have h1_sub : 1 - (c : WittK k p) * b0 ∈ Ideal.span {(p : WittK k p)} := by
      rw [WittVector.mem_span_p_iff_coeff_zero_eq_zero, ← WittVector.constantCoeff_apply,
        map_sub, map_one, map_mul]
      change 1 - (c : WittK k p).coeff 0 * b0.coeff 0 = 0
      rw [hca0, hb0_coeff, ← map_mul, mul_inv_cancel₀ ha0_ne, map_one, sub_self]
    let d : WittK k p := 1 - (c : WittK k p) * b0
    have hd_mem : d ∈ BSub k p B n :=
      (BSub k p B n).sub_mem (BSub k p B n).one_mem
        ((BSub k p B n).mul_mem ((mem_CohenSub_iff k p B _).mp c.2 n hn) ⟨b0, hb0_mem, by simp⟩)
    let invApprox : WittK k p := b0 * ∑ i ∈ Finset.range n, d ^ i
    have hinvApprox_mem : invApprox ∈ BSub k p B n :=
      (BSub k p B n).mul_mem ⟨b0, hb0_mem, by simp⟩
        ((BSub k p B n).sum_mem fun i _ => (BSub k p B n).pow_mem hd_mem i)
    have hmul_eq : (c : WittK k p) * invApprox = 1 - d ^ n := by
      have hgeom : (1 - d) * ∑ i ∈ Finset.range n, d ^ i = 1 - d ^ n := by
        have := geom_sum_mul d n
        linear_combination -this
      have h1d : (c : WittK k p) * b0 = 1 - d := by dsimp only [d]; ring
      calc (c : WittK k p) * invApprox
          = ((c : WittK k p) * b0) * ∑ i ∈ Finset.range n, d ^ i := by dsimp only [invApprox]; ring
        _ = (1 - d) * ∑ i ∈ Finset.range n, d ^ i := by rw [h1d]
        _ = 1 - d ^ n := hgeom
    have hdn : d ^ n ∈ Ideal.span {(p : WittK k p) ^ n} := by
      rw [← Ideal.span_singleton_pow]
      exact Ideal.pow_mem_pow h1_sub n
    have hdiff : uWinv - invApprox ∈ Ideal.span {(p : WittK k p) ^ n} := by
      have hcalc : uWinv - invApprox = uWinv * d ^ n := by
        calc uWinv - invApprox
            = uWinv - uWinv * ((c : WittK k p) * invApprox) := by
              rw [← mul_assoc, huWinv_mul, one_mul]
          _ = uWinv * (1 - (c : WittK k p) * invApprox) := by ring
          _ = uWinv * d ^ n := by rw [hmul_eq]; ring
      rw [hcalc]
      exact Ideal.mul_mem_left _ _ hdn
    obtain ⟨s, hs, hinv_s⟩ := hinvApprox_mem
    refine ⟨s, hs, ?_⟩
    have : uWinv - s = (uWinv - invApprox) + (invApprox - s) := by ring
    rw [this]
    exact Ideal.add_mem _ hdiff hinv_s
  refine ⟨⟨c, ⟨uWinv, hinv_mem⟩, ?_, ?_⟩, rfl⟩
  · exact Subtype.ext hmul_uWinv
  · exact Subtype.ext huWinv_mul

lemma CohenRing_isDVR (hBindep : pIndep k p B)
    (hBspan : ∀ x : k, ∃ f : Monom k p B 1 →₀ k,
      f.sum (fun e c => c ^ p * monomVal k p e) = x) :
    IsDiscreteValuationRing (CohenRing k p B) := by
  have hp_not_unit : ¬ IsUnit (p : CohenRing k p B) := by
    intro hu
    have huW : IsUnit (p : WittK k p) := by
      have := hu.map (CohenSub k p B).subtype
      simpa using this
    exact (WittVector.irreducible p (k := PerfK k p)).not_isUnit huW
  have hp_irred : Irreducible (p : CohenRing k p B) := by
    refine ⟨hp_not_unit, fun a b hab => ?_⟩
    have habW : (p : WittK k p) = (a : WittK k p) * (b : WittK k p) := by
      simpa using congrArg Subtype.val hab
    rcases (WittVector.irreducible p (k := PerfK k p)).isUnit_or_isUnit habW with ha | hb
    · left
      have ha0 : (a : WittK k p).coeff 0 ≠ 0 := by
        intro h0
        have hp_mem : (a : WittK k p) ∈ Ideal.span {(p : WittK k p)} :=
          (WittVector.mem_span_p_iff_coeff_zero_eq_zero _).mpr h0
        obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp hp_mem
        exact (WittVector.irreducible p (k := PerfK k p)).not_isUnit (isUnit_of_mul_isUnit_left (hw ▸ ha))
      exact CohenRing_isUnit_of_coeff_zero_ne_zero k p B hBindep hBspan a ha0
    · right
      have hb0 : (b : WittK k p).coeff 0 ≠ 0 := by
        intro h0
        have hp_mem : (b : WittK k p) ∈ Ideal.span {(p : WittK k p)} :=
          (WittVector.mem_span_p_iff_coeff_zero_eq_zero _).mpr h0
        obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp hp_mem
        exact (WittVector.irreducible p (k := PerfK k p)).not_isUnit (isUnit_of_mul_isUnit_left (hw ▸ hb))
      exact CohenRing_isUnit_of_coeff_zero_ne_zero k p B hBindep hBspan b hb0
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨p, hp_irred, fun {x} hx => ?_⟩
  have hxW : (x : WittK k p) ≠ 0 := fun h0 => hx (Subtype.ext h0)
  obtain ⟨m, uW, hxu⟩ := WittVector.exists_eq_pow_p_mul' (x : WittK k p) hxW
  have hx_pow : x ∈ Ideal.span {(p : CohenRing k p B) ^ m} := by
    rw [← CohenRing_inter_p_pow k p B hBindep hBspan m x, Ideal.mem_span_singleton]
    exact ⟨(uW : WittK k p), hxu⟩
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.mp hx_pow
  have huW_eq : (u : WittK k p) = (uW : WittK k p) := by
    have hmul : (p : WittK k p) ^ m * (u : WittK k p) = (p : WittK k p) ^ m * (uW : WittK k p) := by
      have := congrArg Subtype.val hu
      simpa [hxu] using this.symm
    exact mul_left_cancel₀ (pow_ne_zero m (WittVector.p_nonzero p (PerfK k p))) hmul
  have hu0 : (u : WittK k p).coeff 0 ≠ 0 := by
    rw [huW_eq]
    intro h0
    have hp_mem : (uW : WittK k p) ∈ Ideal.span {(p : WittK k p)} :=
      (WittVector.mem_span_p_iff_coeff_zero_eq_zero _).mpr h0
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp hp_mem
    exact (WittVector.irreducible p (k := PerfK k p)).not_isUnit (isUnit_of_mul_isUnit_left (hw ▸ uW.isUnit))
  have hu_unit : IsUnit u := CohenRing_isUnit_of_coeff_zero_ne_zero k p B hBindep hBspan u hu0
  refine ⟨m, hu_unit.unit, ?_⟩
  rw [hu_unit.unit_spec]
  exact hu.symm

lemma CohenRing_maximalIdeal_eq_span_p (hBindep : pIndep k p B)
    (hBspan : ∀ x : k, ∃ f : Monom k p B 1 →₀ k,
      f.sum (fun e c => c ^ p * monomVal k p e) = x)
    [IsDiscreteValuationRing (CohenRing k p B)] :
    maximalIdeal (CohenRing k p B) = Ideal.span {(p : CohenRing k p B)} := by
  refine le_antisymm ?_ ?_
  · intro c hc
    have hc0 : (c : WittK k p).coeff 0 = 0 := by
      by_contra hne
      exact hc (CohenRing_isUnit_of_coeff_zero_ne_zero k p B hBindep hBspan c hne)
    have hcp : (c : WittK k p) ∈ Ideal.span {(p : WittK k p)} :=
      (WittVector.mem_span_p_iff_coeff_zero_eq_zero _).mpr hc0
    obtain ⟨c', rfl⟩ := CohenRing_inter_p k p B hBindep hBspan c hcp
    exact Ideal.mem_span_singleton.mpr ⟨c', rfl⟩
  · rw [Ideal.span_singleton_le_iff_mem]
    intro hu
    exact (WittVector.irreducible p (k := PerfK k p)).not_isUnit
      (by simpa using hu.map (CohenSub k p B).subtype)

lemma CohenRing_isAdicComplete (hBindep : pIndep k p B)
    (hBspan : ∀ x : k, ∃ f : Monom k p B 1 →₀ k,
      f.sum (fun e c => c ^ p * monomVal k p e) = x)
    [IsDiscreteValuationRing (CohenRing k p B)] :
    IsAdicComplete (maximalIdeal (CohenRing k p B)) (CohenRing k p B) := by
  rw [CohenRing_maximalIdeal_eq_span_p k p B hBindep hBspan]
  refine { haus' := ?_, prec' := ?_ }
  · intro c hc
    apply Subtype.ext
    refine IsHausdorff.haus' (I := Ideal.span {(p : WittK k p)}) (M := WittK k p) (c : WittK k p) fun n => ?_
    have hcn := hc n
    rw [SModEq.zero, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top] at hcn ⊢
    exact (CohenRing_inter_p_pow k p B hBindep hBspan n c).mpr hcn
  · intro f hf
    have hfW : ∀ {m n : ℕ}, m ≤ n →
        (f m : WittK k p) ≡ (f n : WittK k p)
          [SMOD (Ideal.span {(p : WittK k p)} ^ m • (⊤ : Submodule (WittK k p) (WittK k p)))] := by
      intro m n hmn
      have h := hf hmn
      rw [SModEq.sub_mem, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top] at h ⊢
      exact (CohenRing_inter_p_pow k p B hBindep hBspan m (f m - f n)).mpr h
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {(p : WittK k p)}) (M := WittK k p)
      (fun m => (f m : WittK k p)) hfW
    have hL_mem : L ∈ CohenSub k p B := by
      rw [mem_CohenSub_iff]
      intro n hn
      have hLn := hL n
      rw [SModEq.sub_mem, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top] at hLn
      have hLn' : L - (f n : WittK k p) ∈ Ideal.span {(p : WittK k p) ^ n} := by
        simpa [neg_sub] using Submodule.neg_mem _ hLn
      obtain ⟨s, hs, hfs⟩ := (mem_CohenSub_iff k p B _).mp (f n).2 n hn
      refine ⟨s, hs, ?_⟩
      have : L - s = (L - (f n : WittK k p)) + ((f n : WittK k p) - s) := by ring
      rw [this]
      exact Ideal.add_mem _ hLn' hfs
    refine ⟨⟨L, hL_mem⟩, fun n => ?_⟩
    rw [SModEq.sub_mem, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top]
    rw [← CohenRing_inter_p_pow k p B hBindep hBspan n]
    have hLn := hL n
    rw [SModEq.sub_mem, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top] at hLn
    simpa using hLn

lemma cohen_exists_coeff_zero (c : CohenRing k p B) :
    ∃ a : k, (c : WittK k p).coeff 0 = iotaK k p a := by
  obtain ⟨s, hs, hcs⟩ := (mem_CohenSub_iff k p B _).mp c.2 1 le_rfl
  obtain ⟨a, ha⟩ := coeff_zero_mem_range_of_mem_SSub k p B 1 hs
  refine ⟨a, ?_⟩
  have hdiff := (WittVector.mem_span_p_iff_coeff_zero_eq_zero _).mp (by simpa using hcs)
  rw [← WittVector.constantCoeff_apply, map_sub, sub_eq_zero] at hdiff
  simp only [WittVector.constantCoeff_apply] at hdiff
  exact hdiff.trans ha

noncomputable def cohenToK : CohenRing k p B →+* k :=
  { toFun := fun c => (cohen_exists_coeff_zero k p B c).choose
    map_one' := by
      apply iotaK_injective k p
      rw [← (cohen_exists_coeff_zero k p B 1).choose_spec, map_one]
      exact WittVector.one_coeff_zero (p := p) (R := PerfK k p)
    map_mul' := fun x y => by
      apply iotaK_injective k p
      rw [map_mul, ← (cohen_exists_coeff_zero k p B _).choose_spec,
        ← (cohen_exists_coeff_zero k p B x).choose_spec,
        ← (cohen_exists_coeff_zero k p B y).choose_spec]
      exact WittVector.mul_coeff_zero _ _
    map_zero' := by
      apply iotaK_injective k p
      rw [← (cohen_exists_coeff_zero k p B 0).choose_spec, map_zero]
      exact WittVector.zero_coeff p (PerfK k p) 0
    map_add' := fun x y => by
      apply iotaK_injective k p
      rw [map_add, ← (cohen_exists_coeff_zero k p B _).choose_spec,
        ← (cohen_exists_coeff_zero k p B x).choose_spec,
        ← (cohen_exists_coeff_zero k p B y).choose_spec]
      exact WittVector.add_coeff_zero _ _ }

lemma iotaK_cohenToK (c : CohenRing k p B) :
    iotaK k p (cohenToK k p B c) = (c : WittK k p).coeff 0 :=
  (cohen_exists_coeff_zero k p B c).choose_spec.symm

lemma cohenToK_surjective (hBindep : pIndep k p B)
    (hBspan : ∀ x : k, ∃ f : Monom k p B 1 →₀ k,
      f.sum (fun e c => c ^ p * monomVal k p e) = x) :
    Function.Surjective (cohenToK k p B) := by
  intro a
  obtain ⟨s, hs, hs0⟩ := exists_mem_SSub_coeff_zero_eq k p B hBindep hBspan 1 a
  obtain ⟨c, hc⟩ := exists_cohen_sub_mem_pow k p B hBindep hBspan 1 le_rfl hs
  refine ⟨c, iotaK_injective k p ?_⟩
  rw [iotaK_cohenToK, ← hs0]
  have hdiff := (WittVector.mem_span_p_iff_coeff_zero_eq_zero _).mp (by simpa using hc)
  rw [← WittVector.constantCoeff_apply, map_sub, sub_eq_zero] at hdiff
  exact hdiff

lemma ker_cohenToK (hBindep : pIndep k p B)
    (hBspan : ∀ x : k, ∃ f : Monom k p B 1 →₀ k,
      f.sum (fun e c => c ^ p * monomVal k p e) = x)
    [IsDiscreteValuationRing (CohenRing k p B)] :
    RingHom.ker (cohenToK k p B) = maximalIdeal (CohenRing k p B) := by
  rw [CohenRing_maximalIdeal_eq_span_p k p B hBindep hBspan]
  ext c
  rw [RingHom.mem_ker, ← (iotaK_injective k p).eq_iff, map_zero, iotaK_cohenToK,
    ← WittVector.mem_span_p_iff_coeff_zero_eq_zero]
  simpa using CohenRing_inter_p_pow k p B hBindep hBspan 1 c

lemma CohenRing_residueField_charP (hBindep : pIndep k p B)
    (hBspan : ∀ x : k, ∃ f : Monom k p B 1 →₀ k,
      f.sum (fun e c => c ^ p * monomVal k p e) = x)
    [IsDiscreteValuationRing (CohenRing k p B)] :
    CharP (ResidueField (CohenRing k p B)) p := by
  let e : ResidueField (CohenRing k p B) ≃+* k :=
    (Ideal.quotEquivOfEq (ker_cohenToK k p B hBindep hBspan).symm).trans
      (RingHom.quotientKerEquivOfSurjective (cohenToK_surjective k p B hBindep hBspan))
  exact ⟨fun n => by
    rw [← map_eq_zero_iff e.toRingHom e.injective, map_natCast]
    exact CharP.cast_eq_zero_iff k p n⟩

lemma CohenRing_p_not_mem_maximalIdeal_sq (hBindep : pIndep k p B)
    (hBspan : ∀ x : k, ∃ f : Monom k p B 1 →₀ k,
      f.sum (fun e c => c ^ p * monomVal k p e) = x)
    [IsDiscreteValuationRing (CohenRing k p B)] :
    (p : CohenRing k p B) ∉ maximalIdeal (CohenRing k p B) ^ 2 := by
  rw [CohenRing_maximalIdeal_eq_span_p k p B hBindep hBspan, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  rintro ⟨u, hu⟩
  have hp_ne : (p : CohenRing k p B) ≠ 0 := fun h0 =>
    WittVector.p_nonzero p (PerfK k p) (by simpa using congrArg Subtype.val h0)
  have h1 : (p : CohenRing k p B) * 1 = (p : CohenRing k p B) * ((p : CohenRing k p B) * u) := by
    calc (p : CohenRing k p B) * 1 = (p : CohenRing k p B) := mul_one _
      _ = (p : CohenRing k p B) ^ 2 * u := hu
      _ = (p : CohenRing k p B) * ((p : CohenRing k p B) * u) := by ring
  have hu1 : (p : CohenRing k p B) * u = 1 := (mul_left_cancel₀ hp_ne h1).symm
  have hp_unit : IsUnit (p : CohenRing k p B) := isUnit_iff_exists_inv.mpr ⟨u, hu1⟩
  exact (WittVector.irreducible p (k := PerfK k p)).not_isUnit
    (by simpa using hp_unit.map (CohenSub k p B).subtype)

end CohenRingConstruction

section CohenRingMap

variable (R : Type) [CommRing R] [IsLocalRing R]
variable (p : ℕ) [hp : Fact p.Prime] [CharP (ResidueField R) p]

lemma map_ghostComponent_eq {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (w : WittVector p A) (n : ℕ) :
    f (WittVector.ghostComponent n w) = WittVector.ghostComponent n (WittVector.map f w) := by
  rw [WittVector.ghostComponent_apply, WittVector.ghostComponent_apply,
    aeval_wittPolynomial, aeval_wittPolynomial, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, map_pow, map_natCast, WittVector.map_coeff]

omit [IsLocalRing R] [CharP (ResidueField R) p] in
lemma pow_p_pow_sub_mem {I : Ideal R} (hpI : (p : R) ∈ I) :
    ∀ (j : ℕ) {x y : R}, x - y ∈ I → x ^ (p ^ j) - y ^ (p ^ j) ∈ I ^ (j + 1) := by
  intro j
  induction j with
  | zero =>
    intro x y hxy
    simpa using hxy
  | succ j ih =>
    intro x y hxy
    let u : R := x ^ (p ^ j)
    let v : R := y ^ (p ^ j)
    have hδ : u - v ∈ I ^ (j + 1) := ih hxy
    let δ : R := u - v
    have hu : u = v + δ := by dsimp only [δ]; ring
    have hexp : x ^ (p ^ (j + 1)) - y ^ (p ^ (j + 1)) = (v + δ) ^ p - v ^ p := by
      rw [pow_succ, pow_mul, pow_mul]
      change u ^ p - v ^ p = (v + δ) ^ p - v ^ p
      rw [hu]
    rw [hexp, add_pow, Finset.sum_range_succ]
    have hlast : v ^ p * δ ^ (p - p) * (p.choose p : R) = v ^ p := by simp
    rw [hlast, add_sub_cancel_right]
    refine Ideal.sum_mem _ fun i hi => ?_
    rw [Finset.mem_range] at hi
    by_cases hi0 : i = 0
    · subst hi0
      simp only [pow_zero, one_mul, tsub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
      have hmem1 : δ ^ p ∈ (I ^ (j + 1)) ^ p := Ideal.pow_mem_pow hδ p
      rw [← pow_mul] at hmem1
      have hge : j + 2 ≤ (j + 1) * p := by
        have hp2 : 2 ≤ p := hp.out.two_le
        calc j + 2 ≤ (j + 1) * 2 := by omega
          _ ≤ (j + 1) * p := Nat.mul_le_mul_left (j + 1) hp2
      exact Ideal.pow_le_pow_right hge hmem1
    · have hdvd : p ∣ p.choose i := hp.out.dvd_choose_self hi0 hi
      obtain ⟨c, hc⟩ := hdvd
      have hchoose_mem : (p.choose i : R) ∈ I := by
        rw [hc, Nat.cast_mul]
        exact I.mul_mem_right (c : R) hpI
      have hδ_pow : δ ^ (p - i) ∈ I ^ (j + 1) := by
        have hpos : 1 ≤ p - i := by omega
        obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le' hpos
        have hm1 : δ ^ (p - i) = δ ^ m * δ := by rw [hm, pow_succ]
        rw [hm1]
        exact (I ^ (j + 1)).mul_mem_left (δ ^ m) hδ
      have hmul : (p.choose i : R) * δ ^ (p - i) ∈ I ^ (j + 2) := by
        have : I ^ (j + 2) = I * I ^ (j + 1) := by rw [pow_succ']
        rw [this]
        exact Ideal.mul_mem_mul hchoose_mem hδ_pow
      have heq : v ^ i * δ ^ (p - i) * (p.choose i : R) =
          v ^ i * ((p.choose i : R) * δ ^ (p - i)) := by ring
      rw [heq]
      exact (I ^ (j + 2)).mul_mem_left (v ^ i) hmul

noncomputable def secR : ResidueField R → R :=
  fun a => (IsLocalRing.residue_surjective a).choose

lemma residue_secR (a : ResidueField R) : IsLocalRing.residue R (secR R a) = a :=
  (IsLocalRing.residue_surjective a).choose_spec

noncomputable def quotToRes (n : ℕ) (hn : 1 ≤ n) :
    R ⧸ maximalIdeal R ^ n →+* ResidueField R :=
  Ideal.Quotient.lift (maximalIdeal R ^ n) (IsLocalRing.residue R) fun r hr => by
    rw [IsLocalRing.residue_eq_zero_iff]
    exact Ideal.pow_le_self (by omega) hr

lemma quotToRes_mk (n : ℕ) (hn : 1 ≤ n) (r : R) :
    quotToRes R n hn (Ideal.Quotient.mk (maximalIdeal R ^ n) r) = IsLocalRing.residue R r :=
  rfl

omit [CharP (ResidueField R) p] in
lemma ghostComponent_eq_of_quotToRes_eq (hp_mem : (p : R) ∈ maximalIdeal R)
    (n : ℕ) (hn : 1 ≤ n) (w1 w2 : WittVector p (R ⧸ maximalIdeal R ^ n))
    (h : ∀ i ≤ n, quotToRes R n hn (w1.coeff i) = quotToRes R n hn (w2.coeff i)) :
    WittVector.ghostComponent n w1 = WittVector.ghostComponent n w2 := by
  rw [WittVector.ghostComponent_apply, WittVector.ghostComponent_apply,
    aeval_wittPolynomial, aeval_wittPolynomial]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  by_cases hin : i = n
  · rw [hin]
    have hp0 : ((p : R ⧸ maximalIdeal R ^ n) ^ n) = 0 := by
      have : (p : R ⧸ maximalIdeal R ^ n) ^ n =
          Ideal.Quotient.mk (maximalIdeal R ^ n) ((p : R) ^ n) := by simp
      rw [this, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_mem_pow hp_mem n
    simp [hp0]
  · have hilt : i < n := by omega
    obtain ⟨a1, ha1⟩ := Ideal.Quotient.mk_surjective (w1.coeff i)
    obtain ⟨a2, ha2⟩ := Ideal.Quotient.mk_surjective (w2.coeff i)
    have hres : IsLocalRing.residue R a1 = IsLocalRing.residue R a2 := by
      have h1 := h i (by omega)
      rw [← ha1, ← ha2, quotToRes_mk, quotToRes_mk] at h1
      exact h1
    have hdiff : a1 - a2 ∈ maximalIdeal R := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hres, sub_self]
    have hpow := pow_p_pow_sub_mem R p hp_mem (n - i) hdiff
    have hterm : (p : R) ^ i * (a1 ^ (p ^ (n - i)) - a2 ^ (p ^ (n - i))) ∈ maximalIdeal R ^ n := by
      have hpi : (p : R) ^ i ∈ maximalIdeal R ^ i := Ideal.pow_mem_pow hp_mem i
      have hmul := Ideal.mul_mem_mul hpi hpow
      rw [← pow_add] at hmul
      have hge : n ≤ i + (n - i + 1) := by omega
      exact Ideal.pow_le_pow_right hge hmul
    rw [← ha1, ← ha2, ← sub_eq_zero]
    have hsub : (p : R ⧸ maximalIdeal R ^ n) ^ i *
        (Ideal.Quotient.mk (maximalIdeal R ^ n) a1) ^ (p ^ (n - i)) -
        (p : R ⧸ maximalIdeal R ^ n) ^ i *
        (Ideal.Quotient.mk (maximalIdeal R ^ n) a2) ^ (p ^ (n - i)) =
        Ideal.Quotient.mk (maximalIdeal R ^ n)
          ((p : R) ^ i * (a1 ^ (p ^ (n - i)) - a2 ^ (p ^ (n - i)))) := by
      simp [map_mul, map_sub, map_pow, mul_sub]
    rw [hsub, Ideal.Quotient.eq_zero_iff_mem]
    exact hterm

noncomputable def liftWitt (n : ℕ) (z : WittVector p (ResidueField R)) :
    WittVector p (R ⧸ maximalIdeal R ^ n) :=
  WittVector.mk p fun i => Ideal.Quotient.mk (maximalIdeal R ^ n) (secR R (z.coeff i))

omit [CharP (ResidueField R) p] in
lemma map_quotToRes_liftWitt (n : ℕ) (hn : 1 ≤ n) (z : WittVector p (ResidueField R)) :
    WittVector.map (quotToRes R n hn) (liftWitt R p n z) = z := by
  ext i
  simp [liftWitt, quotToRes_mk, residue_secR]

noncomputable def psiMod (hp_mem : (p : R) ∈ maximalIdeal R) (n : ℕ) :
    WittVector p (ResidueField R) →+* R ⧸ maximalIdeal R ^ n :=
  if hn : 1 ≤ n then
    { toFun := fun z => WittVector.ghostComponent n (liftWitt R p n z)
      map_one' := by
        have h1 : WittVector.ghostComponent n (liftWitt R p n 1) =
            WittVector.ghostComponent n (1 : WittVector p (R ⧸ maximalIdeal R ^ n)) := by
          refine ghostComponent_eq_of_quotToRes_eq R p hp_mem n hn _ _ fun i _ => ?_
          rw [← WittVector.map_coeff, ← WittVector.map_coeff, map_quotToRes_liftWitt, map_one]
        rw [h1, map_one]
      map_mul' := fun z1 z2 => by
        have hmul : WittVector.ghostComponent n (liftWitt R p n (z1 * z2)) =
            WittVector.ghostComponent n (liftWitt R p n z1 * liftWitt R p n z2) := by
          refine ghostComponent_eq_of_quotToRes_eq R p hp_mem n hn _ _ fun i _ => ?_
          rw [← WittVector.map_coeff, ← WittVector.map_coeff, map_quotToRes_liftWitt,
            map_mul, map_quotToRes_liftWitt, map_quotToRes_liftWitt]
        rw [hmul, map_mul]
      map_zero' := by
        have h0 : WittVector.ghostComponent n (liftWitt R p n 0) =
            WittVector.ghostComponent n (0 : WittVector p (R ⧸ maximalIdeal R ^ n)) := by
          refine ghostComponent_eq_of_quotToRes_eq R p hp_mem n hn _ _ fun i _ => ?_
          rw [← WittVector.map_coeff, ← WittVector.map_coeff, map_quotToRes_liftWitt, map_zero]
        rw [h0, map_zero]
      map_add' := fun z1 z2 => by
        have hadd : WittVector.ghostComponent n (liftWitt R p n (z1 + z2)) =
            WittVector.ghostComponent n (liftWitt R p n z1 + liftWitt R p n z2) := by
          refine ghostComponent_eq_of_quotToRes_eq R p hp_mem n hn _ _ fun i _ => ?_
          rw [← WittVector.map_coeff, ← WittVector.map_coeff, map_quotToRes_liftWitt,
            map_add, map_quotToRes_liftWitt, map_quotToRes_liftWitt]
        rw [hadd, map_add] }
  else
    have hn0 : n = 0 := by omega
    have : Subsingleton (R ⧸ maximalIdeal R ^ n) := by
      rw [hn0, pow_zero]
      exact Ideal.Quotient.subsingleton_iff.mpr Ideal.one_eq_top
    { toFun := fun _ => 0
      map_one' := Subsingleton.elim _ _
      map_mul' := fun _ _ => Subsingleton.elim _ _
      map_zero' := rfl
      map_add' := fun _ _ => Subsingleton.elim _ _ }

omit [CharP (ResidueField R) p] in
lemma psiMod_eq_ghostComponent_of_lift (hp_mem : (p : R) ∈ maximalIdeal R)
    (n : ℕ) (hn : 1 ≤ n) (z : WittVector p (ResidueField R))
    (w : WittVector p (R ⧸ maximalIdeal R ^ n))
    (hw : WittVector.map (quotToRes R n hn) w = z) :
    psiMod R p hp_mem n z = WittVector.ghostComponent n w := by
  simp only [psiMod, dif_pos hn, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
  refine ghostComponent_eq_of_quotToRes_eq R p hp_mem n hn _ _ fun i _ => ?_
  rw [← WittVector.map_coeff, ← WittVector.map_coeff, map_quotToRes_liftWitt, hw]

omit [CharP (ResidueField R) p] in
lemma psiMod_teichmuller (hp_mem : (p : R) ∈ maximalIdeal R) (n : ℕ)
    (a : ResidueField R) :
    psiMod R p hp_mem n (WittVector.teichmuller p a) =
      (Ideal.Quotient.mk (maximalIdeal R ^ n) (secR R a)) ^ (p ^ n) := by
  by_cases hn : 1 ≤ n
  · rw [psiMod_eq_ghostComponent_of_lift R p hp_mem n hn _
      (WittVector.teichmuller p (Ideal.Quotient.mk (maximalIdeal R ^ n) (secR R a)))]
    · exact WittVector.ghostComponent_teichmuller p _ n
    · rw [WittVector.map_teichmuller, quotToRes_mk, residue_secR]
  · have hn0 : n = 0 := by omega
    have : Subsingleton (R ⧸ maximalIdeal R ^ n) := by
      rw [hn0, pow_zero]
      exact Ideal.Quotient.subsingleton_iff.mpr Ideal.one_eq_top
    exact Subsingleton.elim _ _

omit [CharP (ResidueField R) p] in
lemma psiMod_factor (hp_mem : (p : R) ∈ maximalIdeal R) (n : ℕ)
    (z : WittVector p (ResidueField R)) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right n.le_succ) (psiMod R p hp_mem (n + 1) z) =
      psiMod R p hp_mem n (WittVector.frobenius z) := by
  by_cases hn : 1 ≤ n
  · let fac : R ⧸ maximalIdeal R ^ (n + 1) →+* R ⧸ maximalIdeal R ^ n :=
      Ideal.Quotient.factor (Ideal.pow_le_pow_right n.le_succ)
    have h1 : psiMod R p hp_mem (n + 1) z = WittVector.ghostComponent (n + 1) (liftWitt R p (n + 1) z) := by
      simp [psiMod]
    rw [h1, map_ghostComponent_eq, ← WittVector.ghostComponent_frobenius]
    symm
    refine psiMod_eq_ghostComponent_of_lift R p hp_mem n hn _ _ ?_
    have hcomm : (quotToRes R n hn).comp fac = quotToRes R (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) := by
      ext r; rfl
    have hmap_frob : WittVector.map (quotToRes R n hn)
        (WittVector.frobenius (WittVector.map fac (liftWitt R p (n + 1) z))) =
        WittVector.frobenius (WittVector.map (quotToRes R n hn) (WittVector.map fac (liftWitt R p (n + 1) z))) := by
      ext i
      simp only [WittVector.map_coeff, WittVector.coeff_frobenius]
      let u := WittVector.map fac (liftWitt R p (n + 1) z)
      have heval : ∀ P : MvPolynomial ℕ ℤ,
          quotToRes R n hn (MvPolynomial.aeval u.coeff P) =
          MvPolynomial.aeval (fun j => quotToRes R n hn (u.coeff j)) P := by
        intro P
        refine MvPolynomial.induction_on (motive := fun P =>
          quotToRes R n hn (MvPolynomial.aeval u.coeff P) =
          MvPolynomial.aeval (fun j => quotToRes R n hn (u.coeff j)) P) P ?_ ?_ ?_
        · intro c; simp
        · intro P1 P2 h1 h2; simp [h1, h2]
        · intro P1 m ih; simp [ih]
      exact heval (WittVector.frobeniusPoly p i)
    have hmap_comp : WittVector.map (quotToRes R n hn) (WittVector.map fac (liftWitt R p (n + 1) z)) =
        WittVector.map (quotToRes R (n + 1) (Nat.succ_le_succ (Nat.zero_le n))) (liftWitt R p (n + 1) z) := by
      ext i
      simp only [WittVector.map_coeff]
      simpa only [RingHom.comp_apply] using RingHom.congr_fun hcomm ((liftWitt R p (n + 1) z).coeff i)
    change WittVector.map (quotToRes R n hn)
        (WittVector.frobenius (WittVector.map fac (liftWitt R p (n + 1) z))) = WittVector.frobenius z
    rw [hmap_frob, hmap_comp, map_quotToRes_liftWitt]
  · have hn0 : n = 0 := by omega
    have : Subsingleton (R ⧸ maximalIdeal R ^ n) := by
      rw [hn0, pow_zero]
      exact Ideal.Quotient.subsingleton_iff.mpr Ideal.one_eq_top
    exact Subsingleton.elim _ _

omit [CharP (ResidueField R) p] in
lemma psiMod_verschiebung (hp_mem : (p : R) ∈ maximalIdeal R) (n : ℕ)
    (z : WittVector p (ResidueField R)) (y : R)
    (hy : Ideal.Quotient.mk (maximalIdeal R ^ n) y = psiMod R p hp_mem n z) :
    Ideal.Quotient.mk (maximalIdeal R ^ (n + 1)) ((p : R) * y) =
      psiMod R p hp_mem (n + 1) (WittVector.verschiebung z) := by
  by_cases hn : 1 ≤ n
  · let w : WittVector p (R ⧸ maximalIdeal R ^ (n + 1)) := liftWitt R p (n + 1) z
    have hV : psiMod R p hp_mem (n + 1) (WittVector.verschiebung z) =
        WittVector.ghostComponent (n + 1) (WittVector.verschiebung w) := by
      refine psiMod_eq_ghostComponent_of_lift R p hp_mem (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) _ _ ?_
      rw [WittVector.map_verschiebung, map_quotToRes_liftWitt]
    rw [hV, WittVector.ghostComponent_verschiebung]
    obtain ⟨y0, hy0⟩ := Ideal.Quotient.mk_surjective (WittVector.ghostComponent n w)
    have hy0_mod : Ideal.Quotient.mk (maximalIdeal R ^ n) y0 = psiMod R p hp_mem n z := by
      let fac : R ⧸ maximalIdeal R ^ (n + 1) →+* R ⧸ maximalIdeal R ^ n :=
        Ideal.Quotient.factor (Ideal.pow_le_pow_right n.le_succ)
      have hfac : fac (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1)) y0) =
          Ideal.Quotient.mk (maximalIdeal R ^ n) y0 := rfl
      rw [← hfac, hy0, map_ghostComponent_eq]
      symm
      refine psiMod_eq_ghostComponent_of_lift R p hp_mem n hn z (WittVector.map fac w) ?_
      have hcomm : (quotToRes R n hn).comp fac = quotToRes R (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) := by
        ext r; rfl
      have hmap_comp : WittVector.map (quotToRes R n hn) (WittVector.map fac w) =
          WittVector.map (quotToRes R (n + 1) (Nat.succ_le_succ (Nat.zero_le n))) w := by
        ext i
        simp only [WittVector.map_coeff]
        simpa only [RingHom.comp_apply] using RingHom.congr_fun hcomm (w.coeff i)
      rw [hmap_comp, map_quotToRes_liftWitt]
    have hdiff_mn : y - y0 ∈ maximalIdeal R ^ n := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hy, hy0_mod, sub_self]
    have hp_diff : (p : R) * (y - y0) ∈ maximalIdeal R ^ (n + 1) := by
      rw [pow_succ']
      exact Ideal.mul_mem_mul hp_mem hdiff_mn
    rw [← hy0, ← map_natCast (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1))) p, ← map_mul,
      ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    simpa [mul_sub] using hp_diff
  · have hn0 : n = 0 := by omega
    subst hn0
    have h1 : Ideal.Quotient.mk (maximalIdeal R ^ 1) ((p : R) * y) = 0 := by
      rw [pow_one, Ideal.Quotient.eq_zero_iff_mem]
      exact (maximalIdeal R).mul_mem_right y hp_mem
    have h2 : psiMod R p hp_mem 1 (WittVector.verschiebung z) = 0 := by
      have hV : psiMod R p hp_mem 1 (WittVector.verschiebung z) =
          WittVector.ghostComponent 1 (WittVector.verschiebung (liftWitt R p 1 z)) := by
        refine psiMod_eq_ghostComponent_of_lift R p hp_mem 1 le_rfl _ _ ?_
        rw [WittVector.map_verschiebung, map_quotToRes_liftWitt]
      rw [hV, WittVector.ghostComponent_verschiebung]
      have hp0 : (p : R ⧸ maximalIdeal R ^ 1) = 0 := by
        rw [← map_natCast (Ideal.Quotient.mk (maximalIdeal R ^ 1)) p, Ideal.Quotient.eq_zero_iff_mem, pow_one]
        exact hp_mem
      rw [hp0, zero_mul]
    rw [h1, h2]

noncomputable def rMonom (B : Set (ResidueField R)) (n : ℕ) (e : B →₀ ℕ) :
    R ⧸ maximalIdeal R ^ n :=
  e.prod fun b m => (Ideal.Quotient.mk (maximalIdeal R ^ n) (secR R b.1)) ^ m

lemma rMonom_zero (B : Set (ResidueField R)) (n : ℕ) : rMonom R B n 0 = 1 := by
  simp [rMonom]

lemma rMonom_add (B : Set (ResidueField R)) (n : ℕ) (e1 e2 : B →₀ ℕ) :
    rMonom R B n (e1 + e2) = rMonom R B n e1 * rMonom R B n e2 := by
  simp only [rMonom]
  exact Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

omit [CharP (ResidueField R) p] in
lemma rMonom_pow_mul (hp_mem : (p : R) ∈ maximalIdeal R) (B : Set (ResidueField R))
    (n : ℕ) (q : B →₀ ℕ) :
    rMonom R B n ((p ^ n) • q) =
      psiMod R p hp_mem n (q.prod fun b m => WittVector.teichmuller p (b : ResidueField R) ^ m) := by
  classical
  have h1 : rMonom R B n ((p ^ n) • q) = (rMonom R B n q) ^ (p ^ n) := by
    simp only [rMonom, Finsupp.prod]
    have hsupp : ((p ^ n) • q).support = q.support := by
      ext b
      simp only [Finsupp.mem_support_iff, Finsupp.smul_apply, smul_eq_mul, ne_eq, mul_eq_zero,
        pow_ne_zero n hp.out.ne_zero, false_or]
    rw [hsupp, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun b _ => ?_
    simp only [Finsupp.smul_apply, smul_eq_mul]
    rw [mul_comm, pow_mul]
  rw [h1]
  simp only [rMonom, Finsupp.prod, map_prod, map_pow, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [psiMod_teichmuller, ← pow_mul, mul_comm, pow_mul]

lemma evalSSub_eq_zero_of_mem_p_pow (hp_mem : (p : R) ∈ maximalIdeal R)
    (B : Set (ResidueField R)) (hBindep : pIndep (ResidueField R) p B)
    (hBspan : ∀ x : ResidueField R, ∃ f : Monom (ResidueField R) p B 1 →₀ ResidueField R,
      f.sum (fun e c => c ^ p * monomVal (ResidueField R) p e) = x) :
    ∀ (n : ℕ) (f : Monom (ResidueField R) p B n →₀ WittVector p (ResidueField R)),
      f.sum (fun e z => Fpow (ResidueField R) p n z * tMonom (ResidueField R) p B e.1) ∈
        Ideal.span {(p : WittK (ResidueField R) p) ^ n} →
      f.sum (fun e z => psiMod R p hp_mem n z * rMonom R B n e.1) = 0 := by
  classical
  intro n
  induction n with
  | zero =>
    intro f _
    have : Subsingleton (R ⧸ maximalIdeal R ^ 0) := by
      rw [pow_zero]
      exact Ideal.Quotient.subsingleton_iff.mpr Ideal.one_eq_top
    exact Subsingleton.elim _ _
  | succ n ih =>
    intro f hf
    let k := ResidueField R
    have hfp : f.sum (fun e z => Fpow k p (n + 1) z * tMonom k p B e.1) ∈
        Ideal.span {(p : WittK k p)} := by
      have hle : Ideal.span {(p : WittK k p) ^ (n + 1)} ≤ Ideal.span {(p : WittK k p)} := by
        rw [Ideal.span_singleton_le_span_singleton]
        exact dvd_pow_self _ (Nat.succ_ne_zero n)
      exact hle hf
    have hx0 : (f.sum (fun e z => Fpow k p (n + 1) z * tMonom k p B e.1)).coeff 0 = 0 :=
      (WittVector.mem_span_p_iff_coeff_zero_eq_zero _).mp hfp
    let f0 : Monom k p B (n + 1) →₀ k := f.mapRange (fun z => z.coeff 0) (WittVector.zero_coeff p k 0)
    have hf0_sum : f0.sum (fun e c => c ^ (p ^ (n + 1)) * monomVal k p e) = 0 := by
      apply iotaK_injective k p
      rw [map_zero, ← hx0]
      change iotaK k p (f0.sum (fun e c => c ^ (p ^ (n + 1)) * monomVal k p e)) =
        WittVector.constantCoeff (f.sum (fun e z => Fpow k p (n + 1) z * tMonom k p B e.1))
      rw [Finsupp.sum_mapRange_index (fun _ => by simp [zero_pow (pow_ne_zero (n + 1) hp.out.ne_zero)])]
      rw [Finsupp.sum, Finsupp.sum, map_sum, map_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [map_mul, map_mul]
      congr 1
      · exact (Fpow_coeff k p (n + 1) (f e) 0).symm
      · exact (tMonom_coeff_zero k p B e.1).symm
    have hf0_zero : f0 = 0 := (pBasis_pow_repr k p hBindep hBspan (n + 1)).1 f0 hf0_sum
    have hcoeff0 : ∀ e : Monom k p B (n + 1), (f e).coeff 0 = 0 := fun e => by
      have := congrArg (fun g : Monom k p B (n + 1) →₀ k => g e) hf0_zero
      simpa [f0] using this
    have hshift : ∀ e : Monom k p B (n + 1), f e = WittVector.verschiebung ((f e).shift 1) := fun e => by
      have h1 := WittVector.eq_iterate_verschiebung (x := f e) (n := 1) (fun i hi => by
        have : i = 0 := by omega
        subst this
        exact hcoeff0 e)
      simpa using h1
    let x' : WittK k p := f.sum (fun e z => Fpow k p n (z.shift 1) * tMonom k p B e.1)
    have hx_eq : f.sum (fun e z => Fpow k p (n + 1) z * tMonom k p B e.1) = (p : WittK k p) * x' := by
      dsimp only [x']
      rw [Finsupp.sum, Finsupp.sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      conv_lhs => rw [hshift e, Fpow_succ_verschiebung]
      ring
    have hx'_mem : x' ∈ Ideal.span {(p : WittK k p) ^ n} := by
      rw [hx_eq] at hf
      obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp hf
      rw [Ideal.mem_span_singleton]
      refine ⟨w, ?_⟩
      have hmul0 : (x' - (p : WittK k p) ^ n * w) * (p : WittK k p) = 0 := by
        rw [pow_succ'] at hw
        linear_combination hw
      exact sub_eq_zero.mp (WittVector.eq_zero_of_p_mul_eq_zero _ hmul0)
    let qOf : Monom k p B (n + 1) → (B →₀ ℕ) := fun e => e.1.mapRange (· / p ^ n) (Nat.zero_div _)
    let rOf : Monom k p B (n + 1) → Monom k p B n := fun e =>
      ⟨e.1.mapRange (· % p ^ n) (Nat.zero_mod _), fun b => by
        simp only [Finsupp.mapRange_apply]
        exact Nat.mod_lt _ (pow_pos hp.out.pos n)⟩
    have he_split : ∀ e : Monom k p B (n + 1), e.1 = (p ^ n) • qOf e + (rOf e).1 := fun e => by
      ext b
      simp only [qOf, rOf, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
      exact (Nat.div_add_mod (e.1 b) (p ^ n)).symm
    let qW : Monom k p B (n + 1) → WittVector p k := fun e =>
      (qOf e).prod fun b m => WittVector.teichmuller p (b : k) ^ m
    let g : Monom k p B n →₀ WittVector p k :=
      f.sum fun e z => Finsupp.single (rOf e) (z.shift 1 * qW e)
    have hg_W : g.sum (fun r z => Fpow k p n z * tMonom k p B r.1) = x' := by
      dsimp only [g, x']
      rw [Finsupp.sum_sum_index (fun _ => by simp) (fun _ _ _ => by rw [map_add, add_mul])]
      refine Finsupp.sum_congr fun e _ => ?_
      rw [Finsupp.sum_single_index (by simp), map_mul, mul_assoc]
      congr 1
      rw [he_split e, tMonom_add, tMonom_pow_mul]
    have hg_R : g.sum (fun r z => psiMod R p hp_mem n z * rMonom R B n r.1) =
        f.sum (fun e z => psiMod R p hp_mem n (z.shift 1) * rMonom R B n e.1) := by
      dsimp only [g]
      rw [Finsupp.sum_sum_index (fun _ => by simp) (fun _ _ _ => by rw [map_add, add_mul])]
      refine Finsupp.sum_congr fun e _ => ?_
      rw [Finsupp.sum_single_index (by simp), map_mul, mul_assoc]
      congr 1
      rw [he_split e, rMonom_add, rMonom_pow_mul]
    have hIH : f.sum (fun e z => psiMod R p hp_mem n (z.shift 1) * rMonom R B n e.1) = 0 := by
      rw [← hg_R]
      exact ih g (hg_W.symm ▸ hx'_mem)
    have hlift : ∀ e : Monom k p B (n + 1), ∃ y : R,
        Ideal.Quotient.mk (maximalIdeal R ^ n) y = psiMod R p hp_mem n ((f e).shift 1) :=
      fun e => Ideal.Quotient.mk_surjective _
    let y : Monom k p B (n + 1) → R := fun e => (hlift e).choose
    have hy : ∀ e, Ideal.Quotient.mk (maximalIdeal R ^ n) (y e) = psiMod R p hp_mem n ((f e).shift 1) :=
      fun e => (hlift e).choose_spec
    let rVal : (B →₀ ℕ) → R := fun e => e.prod fun b m => secR R b.1 ^ m
    have hrVal_mk : ∀ m (e : B →₀ ℕ),
        Ideal.Quotient.mk (maximalIdeal R ^ m) (rVal e) = rMonom R B m e := fun m e => by
      simp only [rVal, rMonom, Finsupp.prod, map_prod, map_pow]
    have hsum_mem : ∑ e ∈ f.support, y e * rVal e.1 ∈ maximalIdeal R ^ n := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum]
      have heq : ∑ e ∈ f.support, Ideal.Quotient.mk (maximalIdeal R ^ n) (y e * rVal e.1) =
          f.sum (fun e z => psiMod R p hp_mem n (z.shift 1) * rMonom R B n e.1) := by
        rw [Finsupp.sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [map_mul, hy e, hrVal_mk]
      rw [heq, hIH]
    have hp_sum_mem : (p : R) * ∑ e ∈ f.support, y e * rVal e.1 ∈ maximalIdeal R ^ (n + 1) := by
      rw [pow_succ']
      exact Ideal.mul_mem_mul hp_mem hsum_mem
    have hzero : Ideal.Quotient.mk (maximalIdeal R ^ (n + 1)) ((p : R) * ∑ e ∈ f.support, y e * rVal e.1) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hp_sum_mem
    rw [Finset.mul_sum, map_sum] at hzero
    rw [← hzero, Finsupp.sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← mul_assoc, map_mul, hrVal_mk, hshift e, psiMod_verschiebung R p hp_mem n ((f e).shift 1) (y e) (hy e)]

lemma evalSSub_well_defined (hp_mem : (p : R) ∈ maximalIdeal R)
    (B : Set (ResidueField R)) (hBindep : pIndep (ResidueField R) p B)
    (hBspan : ∀ x : ResidueField R, ∃ f : Monom (ResidueField R) p B 1 →₀ ResidueField R,
      f.sum (fun e c => c ^ p * monomVal (ResidueField R) p e) = x)
    (n : ℕ) (f1 f2 : Monom (ResidueField R) p B n →₀ WittVector p (ResidueField R))
    (hdiff : f1.sum (fun e z => Fpow (ResidueField R) p n z * tMonom (ResidueField R) p B e.1) -
      f2.sum (fun e z => Fpow (ResidueField R) p n z * tMonom (ResidueField R) p B e.1) ∈
      Ideal.span {(p : WittK (ResidueField R) p) ^ n}) :
    f1.sum (fun e z => psiMod R p hp_mem n z * rMonom R B n e.1) =
      f2.sum (fun e z => psiMod R p hp_mem n z * rMonom R B n e.1) := by
  classical
  have hsub1 : (f1 - f2).sum (fun e z => Fpow (ResidueField R) p n z * tMonom (ResidueField R) p B e.1) =
      f1.sum (fun e z => Fpow (ResidueField R) p n z * tMonom (ResidueField R) p B e.1) -
      f2.sum (fun e z => Fpow (ResidueField R) p n z * tMonom (ResidueField R) p B e.1) := by
    rw [sub_eq_add_neg, Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by rw [map_add, add_mul])]
    have hneg : (-f2).sum (fun e z => Fpow (ResidueField R) p n z * tMonom (ResidueField R) p B e.1) +
        f2.sum (fun e z => Fpow (ResidueField R) p n z * tMonom (ResidueField R) p B e.1) = 0 := by
      rw [← Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by rw [map_add, add_mul])]
      simp
    rw [eq_neg_of_add_eq_zero_left hneg, sub_eq_add_neg]
  have hsub2 : (f1 - f2).sum (fun e z => psiMod R p hp_mem n z * rMonom R B n e.1) =
      f1.sum (fun e z => psiMod R p hp_mem n z * rMonom R B n e.1) -
      f2.sum (fun e z => psiMod R p hp_mem n z * rMonom R B n e.1) := by
    rw [sub_eq_add_neg, Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by rw [map_add, add_mul])]
    have hneg : (-f2).sum (fun e z => psiMod R p hp_mem n z * rMonom R B n e.1) +
        f2.sum (fun e z => psiMod R p hp_mem n z * rMonom R B n e.1) = 0 := by
      rw [← Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by rw [map_add, add_mul])]
      simp
    rw [eq_neg_of_add_eq_zero_left hneg, sub_eq_add_neg]
  have hzero := evalSSub_eq_zero_of_mem_p_pow R p hp_mem B hBindep hBspan n (f1 - f2) (hsub1.symm ▸ hdiff)
  rw [hsub2, sub_eq_zero] at hzero
  exact hzero

lemma exists_rep_for_cohen (B : Set (ResidueField R)) (n : ℕ) (hn : 1 ≤ n)
    (c : CohenRing (ResidueField R) p B) :
    ∃ f : Monom (ResidueField R) p B n →₀ WittVector p (ResidueField R),
      (c : WittK (ResidueField R) p) -
        f.sum (fun e z => Fpow (ResidueField R) p n z * tMonom (ResidueField R) p B e.1) ∈
        Ideal.span {(p : WittK (ResidueField R) p) ^ n} := by
  obtain ⟨s, hs, hcs⟩ := (mem_CohenSub_iff (ResidueField R) p B _).mp c.2 n hn
  obtain ⟨f, rfl⟩ := (mem_SSub_iff_exists_sum (ResidueField R) p B n s).mp hs
  exact ⟨f, hcs⟩

noncomputable def phiMod (hp_mem : (p : R) ∈ maximalIdeal R)
    (B : Set (ResidueField R)) (hBindep : pIndep (ResidueField R) p B)
    (hBspan : ∀ x : ResidueField R, ∃ f : Monom (ResidueField R) p B 1 →₀ ResidueField R,
      f.sum (fun e c => c ^ p * monomVal (ResidueField R) p e) = x)
    (n : ℕ) : CohenRing (ResidueField R) p B →+* R ⧸ maximalIdeal R ^ n :=
  if hn : 1 ≤ n then
    let evalRep : (Monom (ResidueField R) p B n →₀ WittVector p (ResidueField R)) →
        R ⧸ maximalIdeal R ^ n :=
      fun f => f.sum (fun e z => psiMod R p hp_mem n z * rMonom R B n e.1)
    let evalW : (Monom (ResidueField R) p B n →₀ WittVector p (ResidueField R)) →
        WittK (ResidueField R) p :=
      fun f => f.sum (fun e z => Fpow (ResidueField R) p n z * tMonom (ResidueField R) p B e.1)
    let toF : CohenRing (ResidueField R) p B → R ⧸ maximalIdeal R ^ n :=
      fun c => evalRep (exists_rep_for_cohen R p B n hn c).choose
    have hchar : ∀ (c : CohenRing (ResidueField R) p B)
        (f : Monom (ResidueField R) p B n →₀ WittVector p (ResidueField R)),
        (c : WittK (ResidueField R) p) - evalW f ∈ Ideal.span {(p : WittK (ResidueField R) p) ^ n} →
        toF c = evalRep f := fun c f hf => by
      refine evalSSub_well_defined R p hp_mem B hBindep hBspan n _ f ?_
      have hch := (exists_rep_for_cohen R p B n hn c).choose_spec
      have : evalW (exists_rep_for_cohen R p B n hn c).choose - evalW f =
          ((c : WittK (ResidueField R) p) - evalW f) -
          ((c : WittK (ResidueField R) p) - evalW (exists_rep_for_cohen R p B n hn c).choose) := by ring
      rw [this]
      exact Ideal.sub_mem _ hf hch
    { toFun := toF
      map_one' := by
        let e0 : Monom (ResidueField R) p B n := ⟨0, fun _ => pow_pos hp.out.pos n⟩
        have h1 : toF 1 = evalRep (Finsupp.single e0 1) := by
          refine hchar 1 (Finsupp.single e0 1) ?_
          dsimp only [evalW]
          rw [Finsupp.sum_single_index (by simp), map_one, one_mul, tMonom_zero]
          simp
        rw [h1]
        dsimp only [evalRep]
        rw [Finsupp.sum_single_index (by simp), map_one, one_mul, rMonom_zero]
      map_zero' := by
        have h0 : toF 0 = evalRep 0 := by
          refine hchar 0 0 ?_
          simp [evalW]
        rw [h0]
        simp [evalRep]
      map_add' := fun c1 c2 => by
        classical
        let f1 := (exists_rep_for_cohen R p B n hn c1).choose
        let f2 := (exists_rep_for_cohen R p B n hn c2).choose
        have hf1 := (exists_rep_for_cohen R p B n hn c1).choose_spec
        have hf2 := (exists_rep_for_cohen R p B n hn c2).choose_spec
        have hadd : toF (c1 + c2) = evalRep (f1 + f2) := by
          refine hchar (c1 + c2) (f1 + f2) ?_
          have hW : evalW (f1 + f2) = evalW f1 + evalW f2 :=
            Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by rw [map_add, add_mul])
          rw [hW]
          have : ((c1 + c2 : CohenRing (ResidueField R) p B) : WittK (ResidueField R) p) -
              (evalW f1 + evalW f2) = ((c1 : WittK (ResidueField R) p) - evalW f1) +
              ((c2 : WittK (ResidueField R) p) - evalW f2) := by
            push_cast; ring
          rw [this]
          exact Ideal.add_mem _ hf1 hf2
        rw [hadd]
        exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by rw [map_add, add_mul])
      map_mul' := fun c1 c2 => by
        classical
        let f1 := (exists_rep_for_cohen R p B n hn c1).choose
        let f2 := (exists_rep_for_cohen R p B n hn c2).choose
        have hf1 := (exists_rep_for_cohen R p B n hn c1).choose_spec
        have hf2 := (exists_rep_for_cohen R p B n hn c2).choose_spec
        let qOf : Monom (ResidueField R) p B n → Monom (ResidueField R) p B n → (B →₀ ℕ) :=
          fun e1 e2 => (e1.1 + e2.1).mapRange (· / p ^ n) (Nat.zero_div _)
        let rOf : Monom (ResidueField R) p B n → Monom (ResidueField R) p B n → Monom (ResidueField R) p B n :=
          fun e1 e2 => ⟨(e1.1 + e2.1).mapRange (· % p ^ n) (Nat.zero_mod _), fun b => by
            simp only [Finsupp.mapRange_apply]
            exact Nat.mod_lt _ (pow_pos hp.out.pos n)⟩
        have hsplit : ∀ e1 e2, e1.1 + e2.1 = (p ^ n) • qOf e1 e2 + (rOf e1 e2).1 := fun e1 e2 => by
          ext b
          simp only [qOf, rOf, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
          exact (Nat.div_add_mod (e1.1 b + e2.1 b) (p ^ n)).symm
        let qW : Monom (ResidueField R) p B n → Monom (ResidueField R) p B n → WittVector p (ResidueField R) :=
          fun e1 e2 => (qOf e1 e2).prod fun b m => WittVector.teichmuller p (b : ResidueField R) ^ m
        let fProd : Monom (ResidueField R) p B n →₀ WittVector p (ResidueField R) :=
          f1.sum fun e1 z1 => f2.sum fun e2 z2 => Finsupp.single (rOf e1 e2) (z1 * z2 * qW e1 e2)
        have hW_prod : evalW fProd = evalW f1 * evalW f2 := by
          dsimp only [evalW, fProd]
          rw [Finsupp.sum_sum_index (fun _ => by simp) (fun _ _ _ => by rw [map_add, add_mul])]
          rw [Finsupp.sum, Finsupp.sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun e1 _ => ?_
          rw [Finsupp.sum_sum_index (fun _ => by simp) (fun _ _ _ => by rw [map_add, add_mul])]
          rw [Finsupp.sum]
          conv_rhs => rw [Finsupp.sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun e2 _ => ?_
          rw [Finsupp.sum_single_index (by simp)]
          have ht : tMonom (ResidueField R) p B e1.1 * tMonom (ResidueField R) p B e2.1 =
              Fpow (ResidueField R) p n (qW e1 e2) * tMonom (ResidueField R) p B (rOf e1 e2).1 := by
            rw [← tMonom_add, hsplit e1 e2, tMonom_add, tMonom_pow_mul]
          calc Fpow (ResidueField R) p n (f1 e1 * f2 e2 * qW e1 e2) * tMonom (ResidueField R) p B (rOf e1 e2).1
              = Fpow (ResidueField R) p n (f1 e1) * Fpow (ResidueField R) p n (f2 e2) *
                (Fpow (ResidueField R) p n (qW e1 e2) * tMonom (ResidueField R) p B (rOf e1 e2).1) := by
                  simp only [map_mul]; ring
            _ = Fpow (ResidueField R) p n (f1 e1) * Fpow (ResidueField R) p n (f2 e2) *
                (tMonom (ResidueField R) p B e1.1 * tMonom (ResidueField R) p B e2.1) := by rw [ht]
            _ = (Fpow (ResidueField R) p n (f1 e1) * tMonom (ResidueField R) p B e1.1) *
                (Fpow (ResidueField R) p n (f2 e2) * tMonom (ResidueField R) p B e2.1) := by ring
        have hR_prod : evalRep fProd = evalRep f1 * evalRep f2 := by
          dsimp only [evalRep, fProd]
          rw [Finsupp.sum_sum_index (fun _ => by simp) (fun _ _ _ => by rw [map_add, add_mul])]
          rw [Finsupp.sum, Finsupp.sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun e1 _ => ?_
          rw [Finsupp.sum_sum_index (fun _ => by simp) (fun _ _ _ => by rw [map_add, add_mul])]
          rw [Finsupp.sum]
          conv_rhs => rw [Finsupp.sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun e2 _ => ?_
          rw [Finsupp.sum_single_index (by simp)]
          have hr : rMonom R B n e1.1 * rMonom R B n e2.1 =
              psiMod R p hp_mem n (qW e1 e2) * rMonom R B n (rOf e1 e2).1 := by
            rw [← rMonom_add, hsplit e1 e2, rMonom_add, rMonom_pow_mul]
          calc psiMod R p hp_mem n (f1 e1 * f2 e2 * qW e1 e2) * rMonom R B n (rOf e1 e2).1
              = psiMod R p hp_mem n (f1 e1) * psiMod R p hp_mem n (f2 e2) *
                (psiMod R p hp_mem n (qW e1 e2) * rMonom R B n (rOf e1 e2).1) := by
                  simp only [map_mul]; ring
            _ = psiMod R p hp_mem n (f1 e1) * psiMod R p hp_mem n (f2 e2) *
                (rMonom R B n e1.1 * rMonom R B n e2.1) := by rw [hr]
            _ = (psiMod R p hp_mem n (f1 e1) * rMonom R B n e1.1) *
                (psiMod R p hp_mem n (f2 e2) * rMonom R B n e2.1) := by ring
        have hmul : toF (c1 * c2) = evalRep fProd := by
          refine hchar (c1 * c2) fProd ?_
          rw [hW_prod]
          have : ((c1 * c2 : CohenRing (ResidueField R) p B) : WittK (ResidueField R) p) -
              evalW f1 * evalW f2 =
              ((c1 : WittK (ResidueField R) p) - evalW f1) * (c2 : WittK (ResidueField R) p) +
              evalW f1 * ((c2 : WittK (ResidueField R) p) - evalW f2) := by
            push_cast; ring
          rw [this]
          exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hf1) (Ideal.mul_mem_left _ _ hf2)
        rw [hmul, hR_prod] }
  else
    have hn0 : n = 0 := by omega
    have : Subsingleton (R ⧸ maximalIdeal R ^ n) := by
      rw [hn0, pow_zero]
      exact Ideal.Quotient.subsingleton_iff.mpr Ideal.one_eq_top
    { toFun := fun _ => 0
      map_one' := Subsingleton.elim _ _
      map_mul' := fun _ _ => Subsingleton.elim _ _
      map_zero' := rfl
      map_add' := fun _ _ => Subsingleton.elim _ _ }

lemma phiMod_eq_eval (hp_mem : (p : R) ∈ maximalIdeal R)
    (B : Set (ResidueField R)) (hBindep : pIndep (ResidueField R) p B)
    (hBspan : ∀ x : ResidueField R, ∃ f : Monom (ResidueField R) p B 1 →₀ ResidueField R,
      f.sum (fun e c => c ^ p * monomVal (ResidueField R) p e) = x)
    (n : ℕ) (hn : 1 ≤ n) (c : CohenRing (ResidueField R) p B)
    (f : Monom (ResidueField R) p B n →₀ WittVector p (ResidueField R))
    (hf : (c : WittK (ResidueField R) p) -
      f.sum (fun e z => Fpow (ResidueField R) p n z * tMonom (ResidueField R) p B e.1) ∈
      Ideal.span {(p : WittK (ResidueField R) p) ^ n}) :
    phiMod R p hp_mem B hBindep hBspan n c =
      f.sum (fun e z => psiMod R p hp_mem n z * rMonom R B n e.1) := by
  simp only [phiMod, dif_pos hn, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
  refine evalSSub_well_defined R p hp_mem B hBindep hBspan n _ f ?_
  have hch := (exists_rep_for_cohen R p B n hn c).choose_spec
  have hsub : (exists_rep_for_cohen R p B n hn c).choose.sum
        (fun e z => Fpow (ResidueField R) p n z * tMonom (ResidueField R) p B e.1) -
      f.sum (fun e z => Fpow (ResidueField R) p n z * tMonom (ResidueField R) p B e.1) =
      ((c : WittK (ResidueField R) p) -
        f.sum (fun e z => Fpow (ResidueField R) p n z * tMonom (ResidueField R) p B e.1)) -
      ((c : WittK (ResidueField R) p) -
        (exists_rep_for_cohen R p B n hn c).choose.sum
          (fun e z => Fpow (ResidueField R) p n z * tMonom (ResidueField R) p B e.1)) := by ring
  rw [hsub]
  exact Ideal.sub_mem _ hf hch

lemma phiMod_compat (hp_mem : (p : R) ∈ maximalIdeal R)
    (B : Set (ResidueField R)) (hBindep : pIndep (ResidueField R) p B)
    (hBspan : ∀ x : ResidueField R, ∃ f : Monom (ResidueField R) p B 1 →₀ ResidueField R,
      f.sum (fun e c => c ^ p * monomVal (ResidueField R) p e) = x)
    (n : ℕ) (c : CohenRing (ResidueField R) p B) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right n.le_succ)
        (phiMod R p hp_mem B hBindep hBspan (n + 1) c) =
      phiMod R p hp_mem B hBindep hBspan n c := by
  classical
  by_cases hn : 1 ≤ n
  · obtain ⟨f, hf⟩ := exists_rep_for_cohen R p B (n + 1) (by omega) c
    have h1 := phiMod_eq_eval R p hp_mem B hBindep hBspan (n + 1) (by omega) c f hf
    let qOf : Monom (ResidueField R) p B (n + 1) → (B →₀ ℕ) :=
      fun e => e.1.mapRange (· / p ^ n) (Nat.zero_div _)
    let rOf : Monom (ResidueField R) p B (n + 1) → Monom (ResidueField R) p B n := fun e =>
      ⟨e.1.mapRange (· % p ^ n) (Nat.zero_mod _), fun b => by
        simp only [Finsupp.mapRange_apply]
        exact Nat.mod_lt _ (pow_pos hp.out.pos n)⟩
    have hsplit : ∀ e : Monom (ResidueField R) p B (n + 1), e.1 = (p ^ n) • qOf e + (rOf e).1 := fun e => by
      ext b
      simp only [qOf, rOf, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
      exact (Nat.div_add_mod (e.1 b) (p ^ n)).symm
    let qW : Monom (ResidueField R) p B (n + 1) → WittVector p (ResidueField R) := fun e =>
      (qOf e).prod fun b m => WittVector.teichmuller p (b : ResidueField R) ^ m
    let g : Monom (ResidueField R) p B n →₀ WittVector p (ResidueField R) :=
      f.sum fun e z => Finsupp.single (rOf e) (WittVector.frobenius z * qW e)
    have hg_W : g.sum (fun r z => Fpow (ResidueField R) p n z * tMonom (ResidueField R) p B r.1) =
        f.sum (fun e z => Fpow (ResidueField R) p (n + 1) z * tMonom (ResidueField R) p B e.1) := by
      dsimp only [g]
      rw [Finsupp.sum_sum_index (fun _ => by simp) (fun _ _ _ => by rw [map_add, add_mul])]
      refine Finsupp.sum_congr fun e _ => ?_
      rw [Finsupp.sum_single_index (by simp), map_mul, mul_assoc, ← Fpow_succ_eq]
      congr 1
      rw [hsplit e, tMonom_add, tMonom_pow_mul]
    have hle : Ideal.span {(p : WittK (ResidueField R) p) ^ (n + 1)} ≤
        Ideal.span {(p : WittK (ResidueField R) p) ^ n} := by
      rw [Ideal.span_singleton_le_span_singleton]
      exact pow_dvd_pow _ n.le_succ
    have h2 := phiMod_eq_eval R p hp_mem B hBindep hBspan n hn c g (hg_W.symm ▸ hle hf)
    rw [h1, h2]
    dsimp only [g]
    rw [Finsupp.sum_sum_index (fun _ => by simp) (fun _ _ _ => by rw [map_add, add_mul])]
    rw [Finsupp.sum, Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finsupp.sum_single_index (by simp), map_mul, psiMod_factor, map_mul, mul_assoc]
    congr 1
    have hfac_r : Ideal.Quotient.factor (Ideal.pow_le_pow_right n.le_succ) (rMonom R B (n + 1) e.1) =
        rMonom R B n e.1 := by
      simp only [rMonom, Finsupp.prod, map_prod, map_pow]
      rfl
    rw [hfac_r, hsplit e, rMonom_add, rMonom_pow_mul]
  · have hn0 : n = 0 := by omega
    have : Subsingleton (R ⧸ maximalIdeal R ^ n) := by
      rw [hn0, pow_zero]
      exact Ideal.Quotient.subsingleton_iff.mpr Ideal.one_eq_top
    exact Subsingleton.elim _ _

lemma phiMod_one_eq_cohenToK (hp_mem : (p : R) ∈ maximalIdeal R)
    (B : Set (ResidueField R)) (hBindep : pIndep (ResidueField R) p B)
    (hBspan : ∀ x : ResidueField R, ∃ f : Monom (ResidueField R) p B 1 →₀ ResidueField R,
      f.sum (fun e c => c ^ p * monomVal (ResidueField R) p e) = x)
    (c : CohenRing (ResidueField R) p B) :
    quotToRes R 1 le_rfl (phiMod R p hp_mem B hBindep hBspan 1 c) =
      cohenToK (ResidueField R) p B c := by
  obtain ⟨f, hf⟩ := exists_rep_for_cohen R p B 1 le_rfl c
  rw [phiMod_eq_eval R p hp_mem B hBindep hBspan 1 le_rfl c f hf]
  apply iotaK_injective (ResidueField R) p
  rw [iotaK_cohenToK]
  have hdiff := (WittVector.mem_span_p_iff_coeff_zero_eq_zero _).mp (by simpa using hf)
  rw [← WittVector.constantCoeff_apply, map_sub, sub_eq_zero] at hdiff
  simp only [WittVector.constantCoeff_apply] at hdiff
  rw [hdiff]
  change iotaK (ResidueField R) p (quotToRes R 1 le_rfl _) =
    WittVector.constantCoeff (f.sum (fun e z => Fpow (ResidueField R) p 1 z * tMonom (ResidueField R) p B e.1))
  rw [Finsupp.sum, Finsupp.sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [map_mul, map_mul, map_mul]
  congr 1
  · have hpsi1 : quotToRes R 1 le_rfl (psiMod R p hp_mem 1 (f e)) = ((f e).coeff 0) ^ p := by
      have h1 : psiMod R p hp_mem 1 (f e) = WittVector.ghostComponent 1 (liftWitt R p 1 (f e)) := by
        simp [psiMod]
      rw [h1, WittVector.ghostComponent_apply, aeval_wittPolynomial]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, one_mul,
        tsub_zero, pow_one, tsub_self]
      rw [map_add, map_mul, map_pow, map_natCast]
      have hp0 : (p : ResidueField R) = 0 := CharP.cast_eq_zero (ResidueField R) p
      rw [hp0, zero_mul, add_zero]
      simp [liftWitt, quotToRes_mk, residue_secR]
    rw [hpsi1, WittVector.constantCoeff_apply, Fpow_coeff, pow_one]
  · have hr1 : quotToRes R 1 le_rfl (rMonom R B 1 e.1) = monomVal (ResidueField R) p e := by
      simp only [rMonom, monomVal, Finsupp.prod, map_prod, map_pow]
      refine Finset.prod_congr rfl fun b _ => ?_
      rw [quotToRes_mk, residue_secR]
    rw [hr1, WittVector.constantCoeff_apply, tMonom_coeff_zero]
    rfl

lemma exists_cohenMapToR [IsAdicComplete (maximalIdeal R) R]
    (hp_mem : (p : R) ∈ maximalIdeal R)
    (B : Set (ResidueField R)) (hBindep : pIndep (ResidueField R) p B)
    (hBspan : ∀ x : ResidueField R, ∃ f : Monom (ResidueField R) p B 1 →₀ ResidueField R,
      f.sum (fun e c => c ^ p * monomVal (ResidueField R) p e) = x) :
    ∃ phi : CohenRing (ResidueField R) p B →+* R,
      ∀ c, IsLocalRing.residue R (phi c) = cohenToK (ResidueField R) p B c := by
  let liftVal : CohenRing (ResidueField R) p B → ℕ → R :=
    fun c n => (Ideal.Quotient.mk_surjective (phiMod R p hp_mem B hBindep hBspan n c)).choose
  have hliftVal : ∀ c n,
      Ideal.Quotient.mk (maximalIdeal R ^ n) (liftVal c n) = phiMod R p hp_mem B hBindep hBspan n c :=
    fun c n => (Ideal.Quotient.mk_surjective (phiMod R p hp_mem B hBindep hBspan n c)).choose_spec
  have hcauchy : ∀ c {m n : ℕ}, m ≤ n →
      liftVal c m ≡ liftVal c n [SMOD (maximalIdeal R ^ m • (⊤ : Submodule R R))] := by
    intro c m n hmn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq_zero_iff_mem, map_sub,
      sub_eq_zero, hliftVal c m]
    have hfac : ∀ {a b : ℕ} (hab : a ≤ b),
        Ideal.Quotient.factor (Ideal.pow_le_pow_right hab)
          (phiMod R p hp_mem B hBindep hBspan b c) =
        phiMod R p hp_mem B hBindep hBspan a c := by
      intro a b hab
      induction b, hab using Nat.le_induction with
      | base => simp
      | succ b hab ih =>
        rw [← Ideal.Quotient.factor_comp_apply (Ideal.pow_le_pow_right b.le_succ)
          (Ideal.pow_le_pow_right hab), phiMod_compat, ih]
    rw [← hfac hmn, ← hliftVal c n]
    rfl
  let toF : CohenRing (ResidueField R) p B → R :=
    fun c => (IsPrecomplete.prec' (I := maximalIdeal R) (M := R) (liftVal c) (hcauchy c)).choose
  have htoF_mod : ∀ c n,
      Ideal.Quotient.mk (maximalIdeal R ^ n) (toF c) = phiMod R p hp_mem B hBindep hBspan n c := by
    intro c n
    have hL := (IsPrecomplete.prec' (I := maximalIdeal R) (M := R) (liftVal c) (hcauchy c)).choose_spec n
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hL
    have hsub : Ideal.Quotient.mk (maximalIdeal R ^ n) (liftVal c n - toF c) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hL
    rw [map_sub, sub_eq_zero, hliftVal c n] at hsub
    exact hsub.symm
  let phi : CohenRing (ResidueField R) p B →+* R :=
    { toFun := toF
      map_one' := by
        refine sub_eq_zero.mp (IsHausdorff.haus' (I := maximalIdeal R) (M := R) (toF 1 - 1) fun n => ?_)
        rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq_zero_iff_mem, map_sub,
          htoF_mod, map_one, map_one, sub_self]
      map_zero' := by
        refine IsHausdorff.haus' (I := maximalIdeal R) (M := R) (toF 0) fun n => ?_
        rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq_zero_iff_mem,
          htoF_mod, map_zero]
      map_add' := fun x y => by
        refine sub_eq_zero.mp (IsHausdorff.haus' (I := maximalIdeal R) (M := R) (toF (x + y) - (toF x + toF y)) fun n => ?_)
        rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_add,
          htoF_mod, htoF_mod, htoF_mod, map_add, sub_self]
      map_mul' := fun x y => by
        refine sub_eq_zero.mp (IsHausdorff.haus' (I := maximalIdeal R) (M := R) (toF (x * y) - toF x * toF y) fun n => ?_)
        rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul,
          htoF_mod, htoF_mod, htoF_mod, map_mul, sub_self] }
  refine ⟨phi, fun c => ?_⟩
  rw [← quotToRes_mk R 1 le_rfl]
  change quotToRes R 1 le_rfl (Ideal.Quotient.mk (maximalIdeal R ^ 1) (toF c)) = _
  rw [htoF_mod c 1]
  exact phiMod_one_eq_cohenToK R p hp_mem B hBindep hBspan c

end CohenRingMap

section IteratedPowerSeries

lemma powerSeries_mem_maximalIdeal_iff {A : Type*} [CommRing A] [IsLocalRing A]
    (f : PowerSeries A) :
    f ∈ maximalIdeal (PowerSeries A) ↔ PowerSeries.constantCoeff f ∈ maximalIdeal A := by
  simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]

lemma powerSeries_X_mem_maximalIdeal {A : Type*} [CommRing A] [IsLocalRing A] :
    (PowerSeries.X : PowerSeries A) ∈ maximalIdeal (PowerSeries A) := by
  rw [powerSeries_mem_maximalIdeal_iff, PowerSeries.constantCoeff_X]
  exact (maximalIdeal A).zero_mem

lemma powerSeries_map_constantCoeff_maximalIdeal {A : Type*} [CommRing A] [IsLocalRing A] :
    (maximalIdeal (PowerSeries A)).map PowerSeries.constantCoeff = maximalIdeal A := by
  refine le_antisymm ?_ ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro f hf
    exact (powerSeries_mem_maximalIdeal_iff f).mp hf
  · intro a ha
    have hCa : PowerSeries.C a ∈ maximalIdeal (PowerSeries A) := by
      rw [powerSeries_mem_maximalIdeal_iff, PowerSeries.constantCoeff_C]
      exact ha
    have := Ideal.mem_map_of_mem PowerSeries.constantCoeff hCa
    simpa using this

lemma powerSeries_mem_span_X_pow_of_coeff_zero {A : Type*} [CommRing A] :
    ∀ (k : ℕ) (f : PowerSeries A),
      (∀ i < k, PowerSeries.coeff i f = 0) → f ∈ Ideal.span {(PowerSeries.X : PowerSeries A) ^ k} := by
  intro k
  induction k with
  | zero =>
    intro f _
    simp
  | succ k ih =>
    intro f hf
    have hf0 : PowerSeries.constantCoeff f = 0 := by
      have := hf 0 (Nat.succ_pos k)
      simpa using this
    let g : PowerSeries A := PowerSeries.mk fun i => PowerSeries.coeff (i + 1) f
    have hfg : f = PowerSeries.X * g := by
      ext i
      cases i with
      | zero => simpa using hf0
      | succ i =>
        rw [PowerSeries.coeff_succ_X_mul]
        simp [g]
    have hg : ∀ i < k, PowerSeries.coeff i g = 0 := fun i hi => by
      simp only [g, PowerSeries.coeff_mk]
      exact hf (i + 1) (Nat.succ_lt_succ hi)
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp (ih g hg)
    rw [Ideal.mem_span_singleton]
    refine ⟨q, ?_⟩
    rw [hfg, hq, pow_succ']
    ring

lemma ideal_pow_mono_left {A : Type*} [CommRing A] {I J : Ideal A} (h : I ≤ J) (k : ℕ) :
    I ^ k ≤ J ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact Ideal.mul_mono ih h

lemma powerSeries_mem_maximalIdeal_pow_iff {A : Type*} [CommRing A] [IsLocalRing A] :
    ∀ (k : ℕ) (f : PowerSeries A),
      f ∈ maximalIdeal (PowerSeries A) ^ k ↔
        ∀ i < k, PowerSeries.coeff i f ∈ maximalIdeal A ^ (k - i) := by
  intro k
  induction k with
  | zero =>
    intro f
    simp
  | succ k ih =>
    intro f
    constructor
    · intro hf
      rw [pow_succ] at hf
      refine Submodule.mul_induction_on hf ?_ ?_
      · intro a ha b hb i hi
        rw [PowerSeries.coeff_mul]
        refine Ideal.sum_mem _ fun p hp => ?_
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
        by_cases hp2 : p.2 = 0
        · have hp1 : p.1 = i := by omega
          rw [hp1, hp2]
          have hb0 : PowerSeries.coeff 0 b ∈ maximalIdeal A := by
            have := (powerSeries_mem_maximalIdeal_iff b).mp hb
            simpa using this
          by_cases hik : i < k
          · have ha1 : PowerSeries.coeff i a ∈ maximalIdeal A ^ (k - i) := (ih a).mp ha i hik
            have hmul := Ideal.mul_mem_mul ha1 hb0
            have hsub : k + 1 - i = (k - i) + 1 := by omega
            rw [hsub, pow_succ]
            exact hmul
          · have hik_eq : i = k := by omega
            rw [hik_eq]
            have hsub : k + 1 - k = 1 := by omega
            rw [hsub, pow_one]
            exact (maximalIdeal A).mul_mem_left _ hb0
        · have hp1_lt : p.1 < k := by omega
          have ha1 : PowerSeries.coeff p.1 a ∈ maximalIdeal A ^ (k - p.1) := (ih a).mp ha p.1 hp1_lt
          have hle : k + 1 - i ≤ k - p.1 := by omega
          exact (maximalIdeal A ^ (k + 1 - i)).mul_mem_right _ (Ideal.pow_le_pow_right hle ha1)
      · intro a b ha hb i hi
        rw [map_add]
        exact Ideal.add_mem _ (ha i hi) (hb i hi)
    · intro hf
      let poly : PowerSeries A :=
        ∑ i ∈ Finset.range (k + 1), PowerSeries.C (PowerSeries.coeff i f) * PowerSeries.X ^ i
      have hpoly_mem : poly ∈ maximalIdeal (PowerSeries A) ^ (k + 1) := by
        refine Ideal.sum_mem _ fun i hi => ?_
        rw [Finset.mem_range] at hi
        have hci : PowerSeries.coeff i f ∈ maximalIdeal A ^ (k + 1 - i) := hf i hi
        have hC_mem : PowerSeries.C (PowerSeries.coeff i f) ∈
            maximalIdeal (PowerSeries A) ^ (k + 1 - i) := by
          have hle : (maximalIdeal A).map PowerSeries.C ≤ maximalIdeal (PowerSeries A) := by
            rw [Ideal.map_le_iff_le_comap]
            intro a ha
            rw [Ideal.mem_comap, powerSeries_mem_maximalIdeal_iff, PowerSeries.constantCoeff_C]
            exact ha
          have hpow_le : ((maximalIdeal A).map PowerSeries.C) ^ (k + 1 - i) ≤
              maximalIdeal (PowerSeries A) ^ (k + 1 - i) := ideal_pow_mono_left hle _
          rw [← Ideal.map_pow] at hpow_le
          exact hpow_le (Ideal.mem_map_of_mem PowerSeries.C hci)
        have hX_mem : (PowerSeries.X : PowerSeries A) ^ i ∈ maximalIdeal (PowerSeries A) ^ i :=
          Ideal.pow_mem_pow powerSeries_X_mem_maximalIdeal i
        have hmul := Ideal.mul_mem_mul hC_mem hX_mem
        rw [← pow_add, Nat.sub_add_cancel (by omega)] at hmul
        exact hmul
      have hrem_zero : ∀ i < k + 1, PowerSeries.coeff i (f - poly) = 0 := fun i hi => by
        rw [map_sub, map_sum]
        have hsum : ∑ j ∈ Finset.range (k + 1),
            PowerSeries.coeff i (PowerSeries.C (PowerSeries.coeff j f) * PowerSeries.X ^ j) =
            PowerSeries.coeff i f := by
          rw [Finset.sum_eq_single i]
          · rw [PowerSeries.coeff_C_mul_X_pow, if_pos rfl]
          · intro j _ hji
            rw [PowerSeries.coeff_C_mul_X_pow, if_neg (Ne.symm hji)]
          · intro hni
            exact absurd (Finset.mem_range.mpr hi) hni
        rw [hsum, sub_self]
      have hrem_mem : f - poly ∈ maximalIdeal (PowerSeries A) ^ (k + 1) := by
        have hspan := powerSeries_mem_span_X_pow_of_coeff_zero (k + 1) (f - poly) hrem_zero
        have hle : Ideal.span {(PowerSeries.X : PowerSeries A) ^ (k + 1)} ≤
            maximalIdeal (PowerSeries A) ^ (k + 1) := by
          rw [Ideal.span_singleton_le_iff_mem]
          exact Ideal.pow_mem_pow powerSeries_X_mem_maximalIdeal (k + 1)
        exact hle hspan
      have hf_eq : f = poly + (f - poly) := by ring
      rw [hf_eq]
      exact Ideal.add_mem _ hpoly_mem hrem_mem

lemma powerSeries_isAdicComplete_maximalIdeal {A : Type*} [CommRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] :
    IsAdicComplete (maximalIdeal (PowerSeries A)) (PowerSeries A) := by
  refine { haus' := ?_, prec' := ?_ }
  · intro f hf
    ext i
    refine IsHausdorff.haus' (I := maximalIdeal A) (M := A) (PowerSeries.coeff i f) fun r => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    have hfi := hf (i + r + 1)
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top] at hfi
    have hcoeff := (powerSeries_mem_maximalIdeal_pow_iff (i + r + 1) f).mp hfi i (by omega)
    have hle : r ≤ i + r + 1 - i := by omega
    exact Ideal.pow_le_pow_right hle hcoeff
  · intro seq hseq
    have hcauchy_coeff : ∀ (i : ℕ) {a b : ℕ}, a ≤ b →
        PowerSeries.coeff i (seq (a + i + 1)) ≡ PowerSeries.coeff i (seq (b + i + 1))
          [SMOD (maximalIdeal A ^ a • (⊤ : Submodule A A))] := by
      intro i a b hab
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← map_sub]
      have h1 := hseq (show a + i + 1 ≤ b + i + 1 by omega)
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
      have h2 := (powerSeries_mem_maximalIdeal_pow_iff (a + i + 1) _).mp h1 i (by omega)
      have hle : a ≤ a + i + 1 - i := by omega
      exact Ideal.pow_le_pow_right hle h2
    let limCoeff : ℕ → A := fun i =>
      (IsPrecomplete.prec' (I := maximalIdeal A) (M := A)
        (fun a => PowerSeries.coeff i (seq (a + i + 1))) (hcauchy_coeff i)).choose
    have hlimCoeff : ∀ i a, PowerSeries.coeff i (seq (a + i + 1)) - limCoeff i ∈ maximalIdeal A ^ a := fun i a => by
      have h := (IsPrecomplete.prec' (I := maximalIdeal A) (M := A)
        (fun a => PowerSeries.coeff i (seq (a + i + 1))) (hcauchy_coeff i)).choose_spec a
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h
      exact h
    let L : PowerSeries A := PowerSeries.mk limCoeff
    refine ⟨L, fun k => ?_⟩
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, powerSeries_mem_maximalIdeal_pow_iff]
    intro i hi
    rw [map_sub]
    have h1 : PowerSeries.coeff i (seq k) - PowerSeries.coeff i (seq (k + i + 1)) ∈ maximalIdeal A ^ (k - i) := by
      rw [← map_sub]
      have hk := hseq (show k ≤ k + i + 1 by omega)
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hk
      exact (powerSeries_mem_maximalIdeal_pow_iff k _).mp hk i hi
    have h2 : PowerSeries.coeff i (seq (k + i + 1)) - PowerSeries.coeff i L ∈ maximalIdeal A ^ (k - i) := by
      simp only [L, PowerSeries.coeff_mk]
      exact Ideal.pow_le_pow_right (Nat.sub_le k i) (hlimCoeff i k)
    have hsplit : PowerSeries.coeff i (seq k) - PowerSeries.coeff i L =
        (PowerSeries.coeff i (seq k) - PowerSeries.coeff i (seq (k + i + 1))) +
        (PowerSeries.coeff i (seq (k + i + 1)) - PowerSeries.coeff i L) := by ring
    rw [hsplit]
    exact Ideal.add_mem _ h1 h2

lemma powerSeries_isRegularLocalRing_and_dim {A : Type*} [CommRing A] [IsRegularLocalRing A] :
    IsRegularLocalRing (PowerSeries A) ∧
      ringKrullDim (PowerSeries A) = ringKrullDim A + 1 := by
  have hdimA : ringKrullDim A = ((maximalIdeal A).spanFinrank : WithBot ℕ∞) :=
    ((isRegularLocalRing_iff A).mp ‹IsRegularLocalRing A›).symm
  have hspan_le : (maximalIdeal (PowerSeries A)).spanFinrank ≤ (maximalIdeal A).spanFinrank + 1 := by
    have h1 := PowerSeries.spanFinrank_le_spanFinrank_map_constantCoeff_add_one_of_X_mem
      (I := maximalIdeal (PowerSeries A)) powerSeries_X_mem_maximalIdeal
    rwa [powerSeries_map_constantCoeff_maximalIdeal] at h1
  have hdim_ge : ((maximalIdeal A).spanFinrank + 1 : ℕ) ≤ ringKrullDim (PowerSeries A) := by
    have h1 := ringKrullDim_succ_le_ringKrullDim_powerseries (R := A)
    rw [hdimA] at h1
    simpa [Nat.cast_add, Nat.cast_one] using h1
  have hspan_le_dim : ((maximalIdeal (PowerSeries A)).spanFinrank : WithBot ℕ∞) ≤
      ringKrullDim (PowerSeries A) :=
    (Nat.cast_le.mpr hspan_le).trans hdim_ge
  have hreg : IsRegularLocalRing (PowerSeries A) :=
    IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ hspan_le_dim
  refine ⟨hreg, ?_⟩
  have hdim_le : ringKrullDim (PowerSeries A) ≤ ((maximalIdeal A).spanFinrank + 1 : ℕ) :=
    (ringKrullDim_le_spanFinrank_maximalIdeal (PowerSeries A)).trans (Nat.cast_le.mpr hspan_le)
  have hdim_eq : ringKrullDim (PowerSeries A) = ((maximalIdeal A).spanFinrank + 1 : ℕ) :=
    le_antisymm hdim_le hdim_ge
  rw [hdim_eq, hdimA]
  push_cast
  rfl

lemma powerSeries_residueField_charP {A : Type*} [CommRing A] [IsLocalRing A]
    (p : ℕ) [CharP (ResidueField A) p] :
    CharP (ResidueField (PowerSeries A)) p := by
  let g : PowerSeries A →+* ResidueField A := (IsLocalRing.residue A).comp PowerSeries.constantCoeff
  have hg_surj : Function.Surjective g :=
    IsLocalRing.residue_surjective.comp PowerSeries.constantCoeff_surj
  have hg_ker : RingHom.ker g = maximalIdeal (PowerSeries A) := by
    ext f
    rw [RingHom.mem_ker, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff,
      powerSeries_mem_maximalIdeal_iff]
  let e : ResidueField (PowerSeries A) ≃+* ResidueField A :=
    (Ideal.quotEquivOfEq hg_ker.symm).trans (RingHom.quotientKerEquivOfSurjective hg_surj)
  exact ⟨fun n => by
    rw [← map_eq_zero_iff e.toRingHom e.injective, map_natCast]
    exact CharP.cast_eq_zero_iff (ResidueField A) p n⟩

lemma powerSeries_natCast_not_mem_maximalIdeal_sq {A : Type*} [CommRing A] [IsLocalRing A]
    (p : ℕ) (hp : (p : A) ∉ maximalIdeal A ^ 2) :
    (p : PowerSeries A) ∉ maximalIdeal (PowerSeries A) ^ 2 := by
  intro hmem
  have h0 := (powerSeries_mem_maximalIdeal_pow_iff 2 (p : PowerSeries A)).mp hmem 0 (by omega)
  have hc0 : PowerSeries.coeff 0 (p : PowerSeries A) = (p : A) := by
    rw [← map_natCast (PowerSeries.C (R := A)) p]
    simp
  rw [hc0] at h0
  exact hp h0

lemma powerSeries_extendHom {A R : Type*} [CommRing A] [IsLocalRing A]
    [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
    (f : A →+* R) (hf_loc : ∀ a ∈ maximalIdeal A, f a ∈ maximalIdeal R)
    {x : R} (hx : x ∈ maximalIdeal R) :
    ∃ f' : PowerSeries A →+* R,
      (∀ a : A, f' (PowerSeries.C a) = f a) ∧
      f' PowerSeries.X = x ∧
      (∀ u ∈ maximalIdeal (PowerSeries A), f' u ∈ maximalIdeal R) := by
  let mk : (n : ℕ) → R →+* R ⧸ maximalIdeal R ^ n := fun n => Ideal.Quotient.mk _
  let gFun : (n : ℕ) → PowerSeries A → R ⧸ maximalIdeal R ^ n := fun n F =>
    ∑ i ∈ Finset.range n, mk n (f (PowerSeries.coeff i F) * x ^ i)
  have hxn : ∀ n i, n ≤ i → mk n (x ^ i) = 0 := fun n i hni => by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_le_pow_right hni (Ideal.pow_mem_pow hx i)
  let g : (n : ℕ) → PowerSeries A →+* R ⧸ maximalIdeal R ^ n := fun n =>
    { toFun := gFun n
      map_zero' := by simp [gFun]
      map_add' := fun F G => by
        simp only [gFun, map_add, add_mul, Finset.sum_add_distrib]
      map_one' := by
        cases n with
        | zero =>
          have : Subsingleton (R ⧸ maximalIdeal R ^ 0) := by
            rw [pow_zero]
            exact Ideal.Quotient.subsingleton_iff.mpr Ideal.one_eq_top
          exact Subsingleton.elim _ _
        | succ n =>
          dsimp only [gFun]
          rw [Finset.sum_eq_single 0]
          · simp
          · intro i _ hi0
            simp [PowerSeries.coeff_one, hi0]
          · intro h0
            exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h0
      map_mul' := fun F G => by
        dsimp only [gFun]
        have hLHS : ∑ i ∈ Finset.range n, mk n (f (PowerSeries.coeff i (F * G)) * x ^ i) =
            ∑ i ∈ Finset.range n, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal i,
              mk n (f (PowerSeries.coeff p.1 F) * x ^ p.1) *
              mk n (f (PowerSeries.coeff p.2 G) * x ^ p.2) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [PowerSeries.coeff_mul, map_sum, Finset.sum_mul, map_sum]
          refine Finset.sum_congr rfl fun p hp => ?_
          rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
          rw [← map_mul, ← hp, pow_add]
          congr 1
          rw [map_mul]
          ring
        rw [hLHS, Finset.sum_mul]
        simp_rw [Finset.mul_sum]
        have hRHS_eq : ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n,
              mk n (f (PowerSeries.coeff a F) * x ^ a) *
              mk n (f (PowerSeries.coeff b G) * x ^ b) =
            ∑ p ∈ (Finset.range n ×ˢ Finset.range n).filter (fun p => p.1 + p.2 < n),
              mk n (f (PowerSeries.coeff p.1 F) * x ^ p.1) *
              mk n (f (PowerSeries.coeff p.2 G) * x ^ p.2) := by
          rw [← Finset.sum_product']
          symm
          refine Finset.sum_subset (Finset.filter_subset _ _) fun p hp hpnot => ?_
          have hge : n ≤ p.1 + p.2 := by
            by_contra hlt
            push Not at hlt
            exact hpnot (Finset.mem_filter.mpr ⟨hp, hlt⟩)
          rw [← map_mul]
          have hmul_eq : (f (PowerSeries.coeff p.1 F) * x ^ p.1) *
              (f (PowerSeries.coeff p.2 G) * x ^ p.2) =
              (f (PowerSeries.coeff p.1 F) * f (PowerSeries.coeff p.2 G)) * x ^ (p.1 + p.2) := by
            rw [pow_add]; ring
          rw [hmul_eq, map_mul, hxn n (p.1 + p.2) hge, mul_zero]
        rw [hRHS_eq]
        rw [Finset.sum_sigma']
        refine Finset.sum_bij (fun q _ => q.2) ?_ ?_ ?_ ?_
        · intro q hq
          rw [Finset.mem_sigma, Finset.mem_range, Finset.HasAntidiagonal.mem_antidiagonal] at hq
          rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
          exact ⟨⟨by omega, by omega⟩, by omega⟩
        · intro q1 hq1 q2 hq2 heq
          rw [Finset.mem_sigma, Finset.HasAntidiagonal.mem_antidiagonal] at hq1 hq2
          refine Sigma.ext ?_ (heq_of_eq heq)
          rw [← hq1.2, ← hq2.2, heq]
        · intro p hp
          rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
          refine ⟨⟨p.1 + p.2, p⟩, ?_, rfl⟩
          rw [Finset.mem_sigma, Finset.mem_range, Finset.HasAntidiagonal.mem_antidiagonal]
          exact ⟨hp.2, rfl⟩
        · intro _ _; rfl }
  have hg_compat : ∀ n F, Ideal.Quotient.factor (Ideal.pow_le_pow_right n.le_succ) (g (n + 1) F) = g n F := by
    intro n F
    change Ideal.Quotient.factor (Ideal.pow_le_pow_right n.le_succ) (gFun (n + 1) F) = gFun n F
    dsimp only [gFun]
    rw [Finset.sum_range_succ, map_add, map_sum]
    have hlast : Ideal.Quotient.factor (Ideal.pow_le_pow_right n.le_succ)
        (mk (n + 1) (f (PowerSeries.coeff n F) * x ^ n)) = 0 := by
      change mk n (f (PowerSeries.coeff n F) * x ^ n) = 0
      rw [map_mul, hxn n n le_rfl, mul_zero]
    rw [hlast, add_zero]
    rfl
  let liftVal : PowerSeries A → ℕ → R := fun F n =>
    ∑ i ∈ Finset.range n, f (PowerSeries.coeff i F) * x ^ i
  have hliftVal : ∀ F n, mk n (liftVal F n) = g n F := fun F n => by
    simp [liftVal, g, gFun, mk]
  have hcauchy : ∀ F {a b : ℕ}, a ≤ b →
      liftVal F a ≡ liftVal F b [SMOD (maximalIdeal R ^ a • (⊤ : Submodule R R))] := by
    intro F a b hab
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq_zero_iff_mem, map_sub,
      sub_eq_zero]
    change mk a (liftVal F a) = mk a (liftVal F b)
    rw [hliftVal F a]
    have hfac : ∀ {u v : ℕ} (huv : u ≤ v),
        Ideal.Quotient.factor (Ideal.pow_le_pow_right huv) (g v F) = g u F := by
      intro u v huv
      induction v, huv using Nat.le_induction with
      | base => simp
      | succ v huv ih =>
        rw [← Ideal.Quotient.factor_comp_apply (Ideal.pow_le_pow_right v.le_succ)
          (Ideal.pow_le_pow_right huv), hg_compat, ih]
    rw [← hfac hab, ← hliftVal F b]
    rfl
  let toF : PowerSeries A → R := fun F =>
    (IsPrecomplete.prec' (I := maximalIdeal R) (M := R) (liftVal F) (hcauchy F)).choose
  have htoF_mod : ∀ F n, mk n (toF F) = g n F := fun F n => by
    have hL := (IsPrecomplete.prec' (I := maximalIdeal R) (M := R) (liftVal F) (hcauchy F)).choose_spec n
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hL
    have hsub : mk n (liftVal F n - toF F) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hL
    rw [map_sub, sub_eq_zero, hliftVal F n] at hsub
    exact hsub.symm
  let f' : PowerSeries A →+* R :=
    { toFun := toF
      map_one' := by
        refine sub_eq_zero.mp (IsHausdorff.haus' (I := maximalIdeal R) (M := R) (toF 1 - 1) fun n => ?_)
        rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq_zero_iff_mem, map_sub]
        change mk n (toF 1) - mk n 1 = 0
        rw [htoF_mod, map_one, map_one, sub_self]
      map_zero' := by
        refine IsHausdorff.haus' (I := maximalIdeal R) (M := R) (toF 0) fun n => ?_
        rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq_zero_iff_mem]
        change mk n (toF 0) = 0
        rw [htoF_mod, map_zero]
      map_add' := fun F G => by
        refine sub_eq_zero.mp (IsHausdorff.haus' (I := maximalIdeal R) (M := R)
          (toF (F + G) - (toF F + toF G)) fun n => ?_)
        rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_add]
        change mk n (toF (F + G)) - (mk n (toF F) + mk n (toF G)) = 0
        rw [htoF_mod, htoF_mod, htoF_mod, map_add, sub_self]
      map_mul' := fun F G => by
        refine sub_eq_zero.mp (IsHausdorff.haus' (I := maximalIdeal R) (M := R)
          (toF (F * G) - toF F * toF G) fun n => ?_)
        rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul]
        change mk n (toF (F * G)) - mk n (toF F) * mk n (toF G) = 0
        rw [htoF_mod, htoF_mod, htoF_mod, map_mul, sub_self] }
  refine ⟨f', ?_, ?_, ?_⟩
  · intro a
    refine sub_eq_zero.mp (IsHausdorff.haus' (I := maximalIdeal R) (M := R) (f' (PowerSeries.C a) - f a) fun n => ?_)
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq_zero_iff_mem, map_sub]
    change mk n (toF (PowerSeries.C a)) - mk n (f a) = 0
    rw [htoF_mod]
    cases n with
    | zero =>
      have : Subsingleton (R ⧸ maximalIdeal R ^ 0) := by
        rw [pow_zero]
        exact Ideal.Quotient.subsingleton_iff.mpr Ideal.one_eq_top
      exact Subsingleton.elim _ _
    | succ n =>
      change gFun (n + 1) (PowerSeries.C a) - mk (n + 1) (f a) = 0
      dsimp only [gFun]
      rw [Finset.sum_eq_single 0]
      · simp
      · intro i _ hi0
        simp [PowerSeries.coeff_C, hi0]
      · intro h0
        exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h0
  · refine sub_eq_zero.mp (IsHausdorff.haus' (I := maximalIdeal R) (M := R) (f' PowerSeries.X - x) fun n => ?_)
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq_zero_iff_mem, map_sub]
    change mk n (toF PowerSeries.X) - mk n x = 0
    rw [htoF_mod]
    cases n with
    | zero =>
      have : Subsingleton (R ⧸ maximalIdeal R ^ 0) := by
        rw [pow_zero]
        exact Ideal.Quotient.subsingleton_iff.mpr Ideal.one_eq_top
      exact Subsingleton.elim _ _
    | succ n =>
      cases n with
      | zero =>
        change gFun 1 PowerSeries.X - mk 1 x = 0
        have hmx : mk 1 x = 0 := by
          rw [Ideal.Quotient.eq_zero_iff_mem, pow_one]
          exact hx
        simp [gFun, hmx]
      | succ n =>
        change gFun (n + 2) PowerSeries.X - mk (n + 2) x = 0
        dsimp only [gFun]
        rw [Finset.sum_eq_single 1]
        · simp
        · intro i _ hi1
          simp [PowerSeries.coeff_X, hi1]
        · intro h1
          exact absurd (Finset.mem_range.mpr (by omega)) h1
  · intro u hu
    have hmod1 : mk 1 (toF u) = g 1 u := htoF_mod u 1
    have hg1 : g 1 u = 0 := by
      change gFun 1 u = 0
      simp only [gFun, Finset.sum_range_one, pow_zero, mul_one, PowerSeries.coeff_zero_eq_constantCoeff]
      rw [Ideal.Quotient.eq_zero_iff_mem, pow_one]
      exact hf_loc _ ((powerSeries_mem_maximalIdeal_iff u).mp hu)
    have h0 : mk 1 (f' u) = 0 := hmod1.trans hg1
    rw [Ideal.Quotient.eq_zero_iff_mem, pow_one] at h0
    exact h0

def IterPowerSeries (C : Type) : ℕ → Type
  | 0 => C
  | n + 1 => PowerSeries (IterPowerSeries C n)

lemma exists_iterPowerSeries_extension {C R : Type} [CommRing C] [IsRegularLocalRing C]
    [IsAdicComplete (maximalIdeal C) C] (p : ℕ) [CharP (ResidueField C) p]
    (hpC : (p : C) ∉ maximalIdeal C ^ 2)
    [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
    (phi : C →+* R) (hphi_loc : ∀ c ∈ maximalIdeal C, phi c ∈ maximalIdeal R)
    (hphi_res : Function.Surjective ((IsLocalRing.residue R).comp phi)) :
    ∀ (n : ℕ) (xs : Fin n → R), (∀ i, xs i ∈ maximalIdeal R) →
      ∃ (S : Type) (_ : CommRing S) (_ : IsRegularLocalRing S)
        (_ : IsAdicComplete (maximalIdeal S) S) (f : S →+* R),
        CharP (ResidueField S) p ∧
        (p : S) ∉ maximalIdeal S ^ 2 ∧
        ringKrullDim S = ringKrullDim C + (n : WithBot ℕ∞) ∧
        (∀ u ∈ maximalIdeal S, f u ∈ maximalIdeal R) ∧
        Function.Surjective ((IsLocalRing.residue R).comp f) ∧
        (∀ i : Fin n, ∃ s ∈ maximalIdeal S, f s = xs i) := by
  intro n
  induction n with
  | zero =>
    intro xs _
    refine ⟨C, inferInstance, inferInstance, inferInstance, phi, inferInstance, hpC, ?_,
      hphi_loc, hphi_res, fun i => Fin.elim0 i⟩
    simp
  | succ n ih =>
    intro xs hxs
    obtain ⟨S0, hComm0, hReg0, hComp0, f0, hChar0, hpS0, hdim0, hf0_loc, hf0_res, hf0_xs⟩ :=
      ih (fun i : Fin n => xs i.castSucc) (fun i => hxs i.castSucc)
    let _ : CommRing S0 := hComm0
    have : IsRegularLocalRing S0 := hReg0
    have : IsAdicComplete (maximalIdeal S0) S0 := hComp0
    have : CharP (ResidueField S0) p := hChar0
    let S1 : Type := PowerSeries S0
    have hreg1 := powerSeries_isRegularLocalRing_and_dim (A := S0)
    have : IsRegularLocalRing S1 := hreg1.1
    have : IsAdicComplete (maximalIdeal S1) S1 := powerSeries_isAdicComplete_maximalIdeal
    have hChar1 : CharP (ResidueField S1) p := powerSeries_residueField_charP p
    have hpS1 : (p : S1) ∉ maximalIdeal S1 ^ 2 := powerSeries_natCast_not_mem_maximalIdeal_sq p hpS0
    obtain ⟨f1, hf1_C, hf1_X, hf1_loc⟩ :=
      powerSeries_extendHom f0 hf0_loc (hxs (Fin.last n))
    refine ⟨S1, inferInstance, inferInstance, inferInstance, f1, hChar1, hpS1, ?_, hf1_loc, ?_, ?_⟩
    · rw [hreg1.2, hdim0]
      push_cast
      rw [add_assoc]
    · intro a
      obtain ⟨s0, hs0⟩ := hf0_res a
      refine ⟨PowerSeries.C s0, ?_⟩
      change IsLocalRing.residue R (f1 (PowerSeries.C s0)) = a
      rw [hf1_C]
      exact hs0
    · intro i
      refine Fin.lastCases ?_ ?_ i
      · exact ⟨PowerSeries.X, powerSeries_X_mem_maximalIdeal, hf1_X⟩
      · intro j
        obtain ⟨s0, hs0_mem, hs0_eq⟩ := hf0_xs j
        refine ⟨PowerSeries.C s0, ?_, ?_⟩
        · rw [powerSeries_mem_maximalIdeal_iff, PowerSeries.constantCoeff_C]
          exact hs0_mem
        · rw [hf1_C, hs0_eq]

lemma surjective_of_complete_local {S R : Type*} [CommRing S] [IsLocalRing S]
    [IsAdicComplete (maximalIdeal S) S]
    [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
    (f : S →+* R) (hf_loc : ∀ u ∈ maximalIdeal S, f u ∈ maximalIdeal R)
    (hf_res : Function.Surjective ((IsLocalRing.residue R).comp f))
    {d : ℕ} (xs : Fin d → R) (hxs_span : maximalIdeal R = Ideal.span (Set.range xs))
    (hxs_im : ∀ i : Fin d, ∃ s ∈ maximalIdeal S, f s = xs i) :
    Function.Surjective f := by
  have hf_pow : ∀ k (u : S), u ∈ maximalIdeal S ^ k → f u ∈ maximalIdeal R ^ k := by
    intro k u hu
    have hle : (maximalIdeal S).map f ≤ maximalIdeal R := by
      rw [Ideal.map_le_iff_le_comap]
      exact hf_loc
    have hpow := ideal_pow_mono_left hle k
    rw [← Ideal.map_pow] at hpow
    exact hpow (Ideal.mem_map_of_mem f hu)
  have happrox : ∀ k : ℕ, ∀ y ∈ maximalIdeal R ^ k,
      ∃ s ∈ maximalIdeal S ^ k, y - f s ∈ maximalIdeal R ^ (k + 1) := by
    intro k
    induction k with
    | zero =>
      intro y _
      obtain ⟨s, hs⟩ := hf_res (IsLocalRing.residue R y)
      refine ⟨s, by simp, ?_⟩
      rw [pow_one, ← IsLocalRing.residue_eq_zero_iff, map_sub]
      change IsLocalRing.residue R y - ((IsLocalRing.residue R).comp f) s = 0
      rw [hs, sub_self]
    | succ k ih =>
      intro y hy
      rw [pow_succ] at hy
      refine Submodule.mul_induction_on hy ?_ ?_
      · intro a ha b hb
        rw [hxs_span, Submodule.mem_span_range_iff_exists_fun] at hb
        obtain ⟨r, hr⟩ := hb
        have hstep : ∀ i : Fin d, ∃ s ∈ maximalIdeal S ^ k,
            a * r i - f s ∈ maximalIdeal R ^ (k + 1) := fun i =>
          ih (a * r i) ((maximalIdeal R ^ k).mul_mem_right (r i) ha)
        let s : Fin d → S := fun i => (hstep i).choose
        have hs_mem : ∀ i, s i ∈ maximalIdeal S ^ k := fun i => (hstep i).choose_spec.1
        have hs_diff : ∀ i, a * r i - f (s i) ∈ maximalIdeal R ^ (k + 1) := fun i => (hstep i).choose_spec.2
        let t : Fin d → S := fun i => (hxs_im i).choose
        have ht_mem : ∀ i, t i ∈ maximalIdeal S := fun i => (hxs_im i).choose_spec.1
        have ht_eq : ∀ i, f (t i) = xs i := fun i => (hxs_im i).choose_spec.2
        refine ⟨∑ i : Fin d, s i * t i, ?_, ?_⟩
        · refine Ideal.sum_mem _ fun i _ => ?_
          rw [pow_succ]
          exact Ideal.mul_mem_mul (hs_mem i) (ht_mem i)
        · have hab : a * b = ∑ i : Fin d, (a * r i) * xs i := by
            rw [← hr, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            simp [smul_eq_mul, mul_assoc]
          rw [hab, map_sum, ← Finset.sum_sub_distrib]
          refine Ideal.sum_mem _ fun i _ => ?_
          rw [map_mul, ht_eq i, ← sub_mul, pow_succ]
          have hxi_mem : xs i ∈ maximalIdeal R := hxs_span ▸ Ideal.subset_span ⟨i, rfl⟩
          exact Ideal.mul_mem_mul (hs_diff i) hxi_mem
      · intro a b ⟨sa, hsa_mem, hsa_diff⟩ ⟨sb, hsb_mem, hsb_diff⟩
        refine ⟨sa + sb, Ideal.add_mem _ hsa_mem hsb_mem, ?_⟩
        rw [map_add]
        have : a + b - (f sa + f sb) = (a - f sa) + (b - f sb) := by ring
        rw [this]
        exact Ideal.add_mem _ hsa_diff hsb_diff
  intro y
  let step : (k : ℕ) → { p : S // y - f p ∈ maximalIdeal R ^ k } →
      { p : S // y - f p ∈ maximalIdeal R ^ (k + 1) } := fun k prev =>
    let s := (happrox k (y - f prev.1) prev.2).choose
    ⟨prev.1 + s, by
      have hdiff := (happrox k (y - f prev.1) prev.2).choose_spec.2
      rw [map_add]
      have : y - (f prev.1 + f s) = (y - f prev.1) - f s := by ring
      rw [this]
      exact hdiff⟩
  let seq : (k : ℕ) → { p : S // y - f p ∈ maximalIdeal R ^ k } :=
    Nat.rec ⟨0, by simp⟩ step
  have hseq_step : ∀ k : ℕ, (seq (k + 1)).1 - (seq k).1 ∈ maximalIdeal S ^ k := fun k => by
    change ((seq k).1 + (happrox k (y - f (seq k).1) (seq k).2).choose) - (seq k).1 ∈ maximalIdeal S ^ k
    rw [add_sub_cancel_left]
    exact (happrox k (y - f (seq k).1) (seq k).2).choose_spec.1
  have hcauchy : ∀ {a b : ℕ}, a ≤ b →
      (seq a).1 ≡ (seq b).1 [SMOD (maximalIdeal S ^ a • (⊤ : Submodule S S))] := by
    intro a b hab
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    induction b, hab using Nat.le_induction with
    | base => simp
    | succ b hab ih =>
      have h1 : (seq a).1 - (seq (b + 1)).1 = ((seq a).1 - (seq b).1) - ((seq (b + 1)).1 - (seq b).1) := by
        ring
      rw [h1]
      exact Ideal.sub_mem _ ih (Ideal.pow_le_pow_right hab (hseq_step b))
  obtain ⟨T, hT⟩ := IsPrecomplete.prec' (I := maximalIdeal S) (M := S) (fun k => (seq k).1) hcauchy
  refine ⟨T, ?_⟩
  refine sub_eq_zero.mp (IsHausdorff.haus' (I := maximalIdeal R) (M := R) (f T - y) fun k => ?_)
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  have hTk := hT k
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hTk
  have h1 : f ((seq k).1 - T) ∈ maximalIdeal R ^ k := hf_pow k _ hTk
  have h2 : y - f (seq k).1 ∈ maximalIdeal R ^ k := (seq k).2
  have h3 : f T - y = -(f ((seq k).1 - T) + (y - f (seq k).1)) := by
    rw [map_sub]; ring
  rw [h3]
  exact Submodule.neg_mem _ (Ideal.add_mem _ h1 h2)

end IteratedPowerSeries

end OMA.H3Proof

theorem OMA.solution : OMA.R_SerreMultiplicityConjectures_supportDim_add_supportDim_le_ringKrullDim_R1.H3 := by
  intro R _ _ _ hp_ne hp_mem2
  open IsLocalRing Ideal Module OMA.H3Proof in
  let k := ResidueField R
  let p : ℕ := ringChar k
  have hp_ne_zero : p ≠ 0 := by
    intro h0
    apply hp_ne
    change (p : R) = 0
    rw [h0, Nat.cast_zero]
  have hp_prime : p.Prime :=
    (CharP.char_is_prime_or_zero k p).resolve_right hp_ne_zero
  have : Fact p.Prime := ⟨hp_prime⟩
  have : CharP k p := ringChar.charP k
  have hp_mem : (p : R) ∈ maximalIdeal R :=
    Ideal.pow_le_self (by norm_num) hp_mem2
  obtain ⟨B, hBindep, hBspan⟩ := exists_pBasis k p
  let C : Type := CohenRing k p B
  have : IsDiscreteValuationRing C := CohenRing_isDVR k p B hBindep hBspan
  have : IsRegularLocalRing C := inferInstance
  have : IsAdicComplete (maximalIdeal C) C := CohenRing_isAdicComplete k p B hBindep hBspan
  have : CharP (ResidueField C) p := CohenRing_residueField_charP k p B hBindep hBspan
  have hpC : (p : C) ∉ maximalIdeal C ^ 2 := CohenRing_p_not_mem_maximalIdeal_sq k p B hBindep hBspan
  have hdimC : ringKrullDim C = 1 := IsDiscreteValuationRing.ringKrullDim_eq_one C
  obtain ⟨phi, hphi_res_eq⟩ := exists_cohenMapToR R p hp_mem B hBindep hBspan
  have hphi_loc : ∀ c ∈ maximalIdeal C, phi c ∈ maximalIdeal R := by
    intro c hc
    rw [← IsLocalRing.residue_eq_zero_iff, hphi_res_eq c, ← RingHom.mem_ker,
      ker_cohenToK k p B hBindep hBspan]
    exact hc
  have hphi_res : Function.Surjective ((IsLocalRing.residue R).comp phi) := by
    intro a
    obtain ⟨c, hc⟩ := cohenToK_surjective k p B hBindep hBspan a
    exact ⟨c, (hphi_res_eq c).trans hc⟩
  let d : ℕ := (maximalIdeal R).spanFinrank
  have hdimR : ringKrullDim R = (d : WithBot ℕ∞) :=
    ((isRegularLocalRing_iff R).mp ‹IsRegularLocalRing R›).symm
  have hmFG : (maximalIdeal R).FG := (maximalIdeal R).fg_of_isNoetherianRing
  have hmFin : ((maximalIdeal R).generators : Set R).Finite := Submodule.FG.finite_generators hmFG
  have : Finite (maximalIdeal R).generators := hmFin.to_subtype
  have hmCard : ((maximalIdeal R).generators : Set R).ncard = d := Submodule.FG.generators_ncard hmFG
  have hcard_eq : Nat.card (maximalIdeal R).generators = d := by
    rw [Nat.card_coe_set_eq]
    exact hmCard
  let eGen : Fin d ≃ (maximalIdeal R).generators :=
    (Finite.equivFinOfCardEq hcard_eq).symm
  let xs : Fin d → R := fun i => (eGen i : R)
  have hxs_mem : ∀ i : Fin d, xs i ∈ maximalIdeal R := fun i =>
    ((maximalIdeal R).span_generators).le (Ideal.subset_span (eGen i).2)
  have hxs_span : maximalIdeal R = Ideal.span (Set.range xs) := by
    rw [← (maximalIdeal R).span_generators]
    congr 1
    ext r
    constructor
    · intro hr
      exact ⟨eGen.symm ⟨r, hr⟩, by simp [xs]⟩
    · rintro ⟨i, rfl⟩
      exact (eGen i).2
  obtain ⟨S, hCommS, hRegS, hCompS, f, hCharS, hpS_unram, hdimS_eq, hf_loc, hf_res, hf_xs⟩ :=
    exists_iterPowerSeries_extension p hpC phi hphi_loc hphi_res d xs hxs_mem
  let _ : CommRing S := hCommS
  have : IsRegularLocalRing S := hRegS
  have : IsAdicComplete (maximalIdeal S) S := hCompS
  have : CharP (ResidueField S) p := hCharS
  have hcharS_eq : ringChar (ResidueField S) = p := ringChar.eq (ResidueField S) p
  have hf_surj : Function.Surjective f :=
    surjective_of_complete_local f hf_loc hf_res xs hxs_span hf_xs
  have hf_max_eq : (maximalIdeal S).map f = maximalIdeal R := by
    refine le_antisymm ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      exact hf_loc
    · rw [hxs_span, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      obtain ⟨s, hs_mem, hs_eq⟩ := hf_xs i
      rw [← hs_eq]
      exact Ideal.mem_map_of_mem f hs_mem
  have hp_mem_f2 : (p : R) ∈ (maximalIdeal S ^ 2).map f := by
    rw [Ideal.map_pow, hf_max_eq]
    exact hp_mem2
  rw [Ideal.mem_map_iff_of_surjective f hf_surj] at hp_mem_f2
  obtain ⟨h, hh_mem2, hfh⟩ := hp_mem_f2
  let g : S := (p : S) - h
  have hpS_mem : (p : S) ∈ maximalIdeal S := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
    exact CharP.cast_eq_zero (ResidueField S) p
  have hg_mem : g ∈ maximalIdeal S :=
    (maximalIdeal S).sub_mem hpS_mem (Ideal.pow_le_self (by norm_num) hh_mem2)
  have hg_not2 : g ∉ maximalIdeal S ^ 2 := by
    intro hg2
    have : (p : S) = g + h := by dsimp only [g]; ring
    rw [this] at hpS_unram
    exact hpS_unram ((maximalIdeal S ^ 2).add_mem hg2 hh_mem2)
  have hg_ne : g ≠ 0 := fun h0 => hg_not2 (h0.symm ▸ (maximalIdeal S ^ 2).zero_mem)
  have hfg : f g = 0 := by
    dsimp only [g]
    rw [map_sub, map_natCast, hfh, sub_self]
  have hdimS : ringKrullDim S = ringKrullDim R + 1 := by
    rw [hdimS_eq, hdimC, hdimR, add_comm]
  have hquot_reg := isRegularLocalRing_quotient_of_mem_not_mem_sq hg_mem hg_not2
  have : IsRegularLocalRing (S ⧸ Ideal.span {g}) := hquot_reg.1
  have : IsDomain (S ⧸ Ideal.span {g}) := isRegularLocalRing_isDomain (S ⧸ Ideal.span {g})
  have hdim_quot : ringKrullDim (S ⧸ Ideal.span {g}) = ringKrullDim R := by
    have h1 := hquot_reg.2
    rw [hdimS, hdimR] at h1
    have hg_ne_top : Ideal.span {g} ≠ ⊤ := by
      intro htop
      have h1' : (1 : S) ∈ maximalIdeal S :=
        (Ideal.span_singleton_le_iff_mem _).mpr hg_mem (htop ▸ Submodule.mem_top)
      exact (IsLocalRing.maximalIdeal.isMaximal S).ne_top (Ideal.eq_top_of_isUnit_mem _ h1' isUnit_one)
    obtain ⟨m, hm⟩ := OMA.R_SerreMultiplicityConjectures_supportDim_add_supportDim_le_ringKrullDim_R1.ringKrullDim_quotient_eq_natCast
      (Ideal.span {g}) hg_ne_top
    rw [hm] at h1 ⊢
    have hmd : m + 1 = d + 1 := by exact_mod_cast h1
    rw [hdimR]
    exact_mod_cast (show m = d by omega)
  have hker_f : RingHom.ker f = Ideal.span {g} := by
    have hle : Ideal.span {g} ≤ RingHom.ker f := by
      rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
      exact hfg
    refine le_antisymm ?_ hle
    intro s hs
    by_contra hs_not
    let fbar : S ⧸ Ideal.span {g} →+* R := Ideal.Quotient.lift (Ideal.span {g}) f fun a ha => by
      exact hle ha
    have hfbar_surj : Function.Surjective fbar :=
      Ideal.Quotient.lift_surjective_of_surjective _ _ hf_surj
    let sbar : S ⧸ Ideal.span {g} := Ideal.Quotient.mk (Ideal.span {g}) s
    have hsbar_ne : sbar ≠ 0 := by
      intro h0
      exact hs_not (Ideal.Quotient.eq_zero_iff_mem.mp h0)
    have hsbar_nzd : sbar ∈ nonZeroDivisors (S ⧸ Ideal.span {g}) :=
      mem_nonZeroDivisors_of_ne_zero hsbar_ne
    have hfbar_sbar : fbar sbar = 0 := hs
    have hdim_le := ringKrullDim_succ_le_of_surjective fbar hfbar_surj hsbar_nzd hfbar_sbar
    rw [hdim_quot, hdimR] at hdim_le
    have : d + 1 ≤ d := by exact_mod_cast hdim_le
    omega
  refine ⟨S, hCommS, hRegS, hCompS, g, f, ?_, hg_mem, hg_ne, hf_surj, hker_f, hdimS⟩
  rw [hcharS_eq]
  exact hpS_unram
