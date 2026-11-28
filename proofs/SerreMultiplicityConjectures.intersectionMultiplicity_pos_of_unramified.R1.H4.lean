import OMAReductions.R_SerreMultiplicityConjectures_intersectionMultiplicity_pos_of_unramified_R1
import Mathlib

/-!
Serre non-negativity and positivity for prime quotients of multivariate power series
over a complete discrete valuation ring.
-/

open IsLocalRing Module Ideal TensorProduct CategoryTheory Limits MonoidalCategory Pointwise Function

namespace SerreHypersurfaceVanishing
section RegularLocal
lemma isRegularLocalRing_quotient_span_singleton
    {R : Type*} [CommRing R] [IsRegularLocalRing R]
    {n : ℕ} (hdim : (maximalIdeal R).spanFinrank = n + 1)
    {x : R} (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2) :
    let I := Ideal.span ({x} : Set R)
    let _ : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
      (fun h => (maximalIdeal.isMaximal R).ne_top
        (top_unique (h ▸ Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx))))
    let _ : IsLocalRing (R ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    IsRegularLocalRing (R ⧸ I) ∧ (maximalIdeal (R ⧸ I)).spanFinrank = n := by
  classical
  intro I _ _
  have hI_le : I ≤ maximalIdeal R := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx)
  have hm_map : (maximalIdeal R).map (Ideal.Quotient.mk I) = maximalIdeal (R ⧸ I) :=
    IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hkrull_R : ringKrullDim R = (n + 1 : ℕ) := by
    rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := R), hdim]
  have hspan_le_n : (maximalIdeal (R ⧸ I)).spanFinrank ≤ n := by
    let k := ResidueField R
    have hfinrank : Module.finrank k (CotangentSpace R) = n + 1 := by
      have h1 := (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance
      rw [hkrull_R] at h1
      exact_mod_cast h1
    let v : CotangentSpace R := (maximalIdeal R).toCotangent ⟨x, hx⟩
    have hv : v ≠ 0 := by
      intro h0
      rw [Ideal.toCotangent_eq_zero] at h0
      exact hx2 (by simpa [pow_two] using h0)
    let L : Submodule k (CotangentSpace R) := Submodule.span k {v}
    have hL_rank : Module.finrank k L = 1 := finrank_span_singleton hv
    let Q := CotangentSpace R ⧸ L
    have hQ_rank : Module.finrank k Q = n := by
      have hadd := Submodule.finrank_quotient_add_finrank L
      dsimp only [Q]
      omega
    let b := Module.finBasisOfFinrankEq k Q hQ_rank
    have hlift (i : Fin n) : ∃ y : maximalIdeal R,
        L.mkQ ((maximalIdeal R).toCotangent y) = b i := by
      obtain ⟨w, hw⟩ := Submodule.mkQ_surjective L (b i)
      obtain ⟨y, hy⟩ := Ideal.toCotangent_surjective (maximalIdeal R) w
      exact ⟨y, by rw [hy, hw]⟩
    choose y hy using hlift
    let yf : Fin n → R := fun i => (y i : R)
    let s : Set (maximalIdeal R) := insert ⟨x, hx⟩ (Set.range y)
    have hspan_cot : Submodule.span k ((maximalIdeal R).toCotangent '' s) = ⊤ := by
      rw [eq_top_iff]
      intro w _
      have hbw : L.mkQ w ∈ Submodule.span k (Set.range b) := by
        rw [b.span_eq]; exact Submodule.mem_top
      rw [Submodule.mem_span_range_iff_exists_fun] at hbw
      obtain ⟨c, hc⟩ := hbw
      have hdiff : w - ∑ i : Fin n, c i • (maximalIdeal R).toCotangent (y i) ∈ L := by
        rw [← Submodule.ker_mkQ L, LinearMap.mem_ker, map_sub, map_sum]
        simp_rw [map_smul, hy]
        rw [hc, sub_self]
      rw [Submodule.mem_span_singleton] at hdiff
      obtain ⟨a, ha⟩ := hdiff
      have hw_eq : w = a • v + ∑ i : Fin n, c i • (maximalIdeal R).toCotangent (y i) := by
        rw [ha]; abel
      rw [hw_eq]
      refine Submodule.add_mem _ ?_ ?_
      · exact Submodule.smul_mem _ a (Submodule.subset_span ⟨⟨x, hx⟩, Set.mem_insert _ _, rfl⟩)
      · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ (c i)
          (Submodule.subset_span ⟨y i, Set.mem_insert_of_mem _ ⟨i, rfl⟩, rfl⟩)
    have hspan_top : Submodule.span R s = ⊤ :=
      (CotangentSpace.span_image_eq_top_iff).mp hspan_cot
    have hm_eq : maximalIdeal R = Ideal.span (insert x (Set.range yf)) := by
      have hmap := congrArg (Submodule.map (maximalIdeal R).subtype) hspan_top
      rw [Submodule.map_top, Submodule.range_subtype, Submodule.map_span] at hmap
      convert hmap.symm using 2
      ext z
      simp [s, yf, eq_comm]
    have hmq_eq : maximalIdeal (R ⧸ I) =
        Ideal.span (Set.range (fun i : Fin n => Ideal.Quotient.mk I (yf i))) := by
      rw [← hm_map, hm_eq, Ideal.map_span]
      apply le_antisymm
      · rw [Ideal.span_le]
        rintro _ ⟨z, hz, rfl⟩
        rcases hz with rfl | ⟨i, rfl⟩
        · have hx0 : Ideal.Quotient.mk I z = 0 :=
            Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
          rw [hx0]
          exact Submodule.zero_mem _
        · exact Ideal.subset_span ⟨i, rfl⟩
      · rw [Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        exact Ideal.subset_span ⟨yf i, Or.inr ⟨i, rfl⟩, rfl⟩
    rw [hmq_eq]
    calc (Ideal.span (Set.range (fun i : Fin n => Ideal.Quotient.mk I (yf i)))).spanFinrank
        ≤ (Set.range (fun i : Fin n => Ideal.Quotient.mk I (yf i))).ncard :=
          Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)
      _ ≤ n := by
          have h1 : (Set.range (fun i : Fin n => Ideal.Quotient.mk I (yf i))) =
              ((Finset.univ.image (fun i : Fin n => Ideal.Quotient.mk I (yf i))) : Set (R ⧸ I)) := by
            ext z; simp
          rw [h1, Set.ncard_coe_finset]
          exact Finset.card_image_le.trans (by simp)
  have hI_sf : I.spanFinrank ≤ 1 := by
    simpa [I] using Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_singleton x)
  have hI_jac : I ≤ Ring.jacobson R := by
    rw [Ring.jacobson_eq_sInf_isMaximal]
    exact le_sInf fun m hm => (IsLocalRing.eq_maximalIdeal hm).symm ▸ hI_le
  have hkd := ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank I hI_jac
  have hkd_ge : (n : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ I) := by
    rw [hkrull_R] at hkd
    have h1 : (I.spanFinrank : WithBot ℕ∞) ≤ 1 := by exact_mod_cast hI_sf
    have h2 : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ I) + 1 :=
      hkd.trans (add_le_add le_rfl h1)
    cases hd : ringKrullDim (R ⧸ I) with
    | bot =>
      rw [hd] at h2
      simp at h2
    | coe a =>
      rw [hd] at h2
      have h2' : ((n + 1 : ℕ) : ℕ∞) ≤ a + 1 := WithBot.coe_le_coe.mp h2
      have ha : (n : ℕ∞) ≤ a := by
        cases a with
        | top => exact le_top
        | coe m =>
          norm_cast at h2' ⊢
          omega
      exact WithBot.coe_le_coe.mpr ha
  have hreg : IsRegularLocalRing (R ⧸ I) :=
    IsRegularLocalRing.of_spanFinrank_maximalIdeal_le (R ⧸ I)
      ((Nat.cast_le.mpr hspan_le_n).trans hkd_ge)
  have hkd_le : ringKrullDim (R ⧸ I) ≤ (n : WithBot ℕ∞) := by
    rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := R ⧸ I)]
    exact_mod_cast hspan_le_n
  have heq : ((maximalIdeal (R ⧸ I)).spanFinrank : WithBot ℕ∞) = (n : WithBot ℕ∞) := by
    rw [IsRegularLocalRing.spanFinrank_maximalIdeal (R := R ⧸ I)]
    exact le_antisymm hkd_le hkd_ge
  exact ⟨hreg, by exact_mod_cast heq⟩
lemma maximalIdeal_not_le_sq {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {n : ℕ} (hdim : (maximalIdeal R).spanFinrank = n + 1) :
    ¬ (maximalIdeal R ≤ maximalIdeal R ^ 2) := by
  intro hle
  have hm_bot : maximalIdeal R = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) (maximalIdeal R)
      (IsNoetherian.noetherian _)
      (by simpa [smul_eq_mul, pow_two] using hle)
      (IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal R) bot_ne_top).ge
  have h0 : (maximalIdeal R).spanFinrank = 0 := by simp [hm_bot]
  omega
theorem isDomain_of_isRegularLocalRing_aux (d : ℕ) :
    ∀ (R : Type*) [CommRing R] [IsRegularLocalRing R],
      (maximalIdeal R).spanFinrank = d → IsDomain R := by
  induction d with
  | zero =>
    intro R _ _ h0
    have hm_bot : maximalIdeal R = ⊥ := by
      have h1 : Module.finrank (ResidueField R) (CotangentSpace R) = 0 := by
        have h2 := (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance
        rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := R), h0] at h2
        exact_mod_cast h2
      have hsub : Subsingleton (CotangentSpace R) :=
        Module.finrank_zero_iff.mp h1
      have hfield : IsField R := subsingleton_cotangentSpace_iff.mp hsub
      exact (IsLocalRing.isField_iff_maximalIdeal_eq).mp hfield
    let _ : Field R := (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hm_bot).toField
    infer_instance
  | succ n ih =>
    intro R _ _ hdim
    have hm_ne_sq := maximalIdeal_not_le_sq hdim
    have hm_not_min (p : Ideal R) (hp : p ∈ minimalPrimes R) : ¬ (maximalIdeal R ≤ p) := by
      intro hle
      have hp_prime : p.IsPrime := hp.1.1
      have hp_eq : p = maximalIdeal R :=
        le_antisymm (IsLocalRing.le_maximalIdeal hp_prime.ne_top) hle
      have hkd0 : Ring.KrullDimLE 0 R := by
        rw [Ring.krullDimLE_zero_iff]
        intro q hq
        have hqp : q ≤ p := hp_eq ▸ IsLocalRing.le_maximalIdeal hq.ne_top
        have heq : q = p := le_antisymm hqp (hp.2 ⟨hq, bot_le⟩ hqp)
        rw [heq, hp_eq]
        exact maximalIdeal.isMaximal R
      have hle0 : ringKrullDim R ≤ 0 := Ring.krullDimLE_iff.mp hkd0
      rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := R), hdim] at hle0
      have : (n + 1 : ℕ) ≤ 0 := by exact_mod_cast hle0
      omega
    have hfin : (minimalPrimes R).Finite := minimalPrimes.finite_of_isNoetherianRing R
    have hex : ∃ x ∈ maximalIdeal R, x ∉ maximalIdeal R ^ 2 ∧ ∀ p ∈ minimalPrimes R, x ∉ p := by
      by_contra! hall
      have hsub' : (maximalIdeal R : Set R) ⊆
          ⋃ I ∈ insert (maximalIdeal R ^ 2) (minimalPrimes R), (I : Set R) := by
        intro x hx
        by_cases hx2 : x ∈ maximalIdeal R ^ 2
        · exact Set.mem_biUnion (Set.mem_insert _ _) hx2
        · obtain ⟨p, hp, hxp⟩ := hall x hx hx2
          exact Set.mem_biUnion (Set.mem_insert_of_mem _ hp) hxp
      have havoid := Ideal.subset_union_prime_finite (I := maximalIdeal R)
        (hfin.insert (maximalIdeal R ^ 2))
        (maximalIdeal R ^ 2) (maximalIdeal R ^ 2)
        (fun I hI hne1 _ => by
          rcases Set.mem_insert_iff.mp hI with rfl | hmin
          · exact (hne1 rfl).elim
          · exact hmin.1.1)
      obtain ⟨I, hI, hle⟩ := havoid.mp hsub'
      rcases Set.mem_insert_iff.mp hI with rfl | hmin
      · exact hm_ne_sq hle
      · exact hm_not_min I hmin hle
    obtain ⟨x, hx, hx2, hx_min⟩ := hex
    let I := Ideal.span ({x} : Set R)
    have hI_le : I ≤ maximalIdeal R := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx)
    have hI_ne : I ≠ ⊤ := fun h => (maximalIdeal.isMaximal R).ne_top (top_unique (h ▸ hI_le))
    let _ : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI_ne
    let _ : IsLocalRing (R ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    obtain ⟨hreg_q, hdim_q⟩ := isRegularLocalRing_quotient_span_singleton hdim hx hx2
    have hdom_q : IsDomain (R ⧸ I) := ih (R ⧸ I) hdim_q
    have hI_prime : I.IsPrime := (Ideal.Quotient.isDomain_iff_prime I).mp hdom_q
    obtain ⟨p, hp_min, hp_le⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := I) bot_le
    have hp_prime : p.IsPrime := hp_min.1.1
    have hp_le_mul : p ≤ maximalIdeal R • p := by
      intro y hy
      have hyI : y ∈ I := hp_le hy
      rw [Ideal.mem_span_singleton] at hyI
      obtain ⟨r, rfl⟩ := hyI
      have hr : r ∈ p := (hp_prime.mem_or_mem hy).resolve_left (hx_min p hp_min)
      simpa [smul_eq_mul] using Submodule.smul_mem_smul hx hr
    have hp_bot : p = ⊥ :=
      Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) p
        (IsNoetherian.noetherian p)
        hp_le_mul
        (IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal R) bot_ne_top).ge
    have hbot_prime : (⊥ : Ideal R).IsPrime := hp_bot ▸ hp_prime
    let _ : NoZeroDivisors R := ⟨fun {a b} hab => by
      have hmem : a * b ∈ (⊥ : Ideal R) := by simpa using hab
      rcases hbot_prime.mem_or_mem hmem with ha | hb
      · exact Or.inl (by simpa using ha)
      · exact Or.inr (by simpa using hb)⟩
    exact NoZeroDivisors.to_isDomain R
theorem isDomain_of_isRegularLocalRing (R : Type*) [CommRing R] [IsRegularLocalRing R] :
    IsDomain R :=
  isDomain_of_isRegularLocalRing_aux (maximalIdeal R).spanFinrank R rfl
lemma exists_param_of_isRegularLocalRing {R : Type*} [CommRing R] [IsRegularLocalRing R]
    {n : ℕ} (hdim : (maximalIdeal R).spanFinrank = n + 1) :
    ∃ x : R, x ∈ maximalIdeal R ∧ x ∉ maximalIdeal R ^ 2 ∧ x ≠ 0 := by
  obtain ⟨x, hx, hx2⟩ := SetLike.not_le_iff_exists.mp (maximalIdeal_not_le_sq hdim)
  exact ⟨x, hx, hx2, fun h0 => hx2 (h0 ▸ zero_mem _)⟩
end RegularLocal
section FiniteProjRes
def HasFiniteProjRes (R : Type) [CommRing R] :
    ℕ → ∀ (N : Type) [AddCommGroup N] [Module R N], Prop
  | 0, N, _, _ => Module.Finite R N ∧ Module.Projective R N
  | n + 1, N, _, _ =>
      ∃ (P : Type) (_ : AddCommGroup P) (_ : Module R P),
        Module.Finite R P ∧ Module.Projective R P ∧
        ∃ (f : P →ₗ[R] N), Function.Surjective f ∧ HasFiniteProjRes R n (LinearMap.ker f)
lemma hasFiniteProjRes_of_equiv {R : Type} [CommRing R] {n : ℕ}
    {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (hM : HasFiniteProjRes R n M) : HasFiniteProjRes R n N := by
  cases n with
  | zero =>
    obtain ⟨hfin, hproj⟩ := hM
    exact ⟨Module.Finite.equiv e, Module.Projective.of_equiv e⟩
  | succ m =>
    obtain ⟨P, _, _, hfin, hproj, f, hf, hK⟩ := hM
    have hf' : Function.Surjective (e.toLinearMap.comp f) := e.surjective.comp hf
    have hker : LinearMap.ker (e.toLinearMap.comp f) = LinearMap.ker f := by
      ext x; simp [LinearMap.mem_ker]
    refine ⟨P, inferInstance, inferInstance, hfin, hproj, e.toLinearMap.comp f, hf', ?_⟩
    exact hasFiniteProjRes_of_equiv (LinearEquiv.ofEq _ _ hker.symm) hK
lemma hasFiniteProjRes_prod_right {R : Type} [CommRing R] {n : ℕ}
    {M P : Type} [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P]
    (hM : HasFiniteProjRes R n M) : HasFiniteProjRes R n (M × P) := by
  cases n with
  | zero =>
    obtain ⟨hfin, hproj⟩ := hM
    exact ⟨inferInstance, inferInstance⟩
  | succ m =>
    obtain ⟨Q, _, _, hfinQ, hprojQ, f, hf, hK⟩ := hM
    let g : Q × P →ₗ[R] M × P := f.prodMap LinearMap.id
    have hg : Function.Surjective g := fun ⟨a, b⟩ => by
      obtain ⟨q, hq⟩ := hf a
      exact ⟨(q, b), by simp [g, hq]⟩
    let ek : LinearMap.ker f ≃ₗ[R] LinearMap.ker g :=
      { toFun := fun ⟨q, hq⟩ => ⟨(q, 0), by simp [g, LinearMap.mem_ker.mp hq]⟩
        invFun := fun ⟨⟨q, p⟩, hqp⟩ => ⟨q, by
          have h1 := LinearMap.mem_ker.mp hqp
          simp [g, Prod.ext_iff] at h1
          exact h1.1⟩
        map_add' := fun _ _ => by ext <;> simp
        map_smul' := fun _ _ => by ext <;> simp
        left_inv := fun ⟨_, _⟩ => rfl
        right_inv := fun ⟨⟨q, p⟩, hqp⟩ => by
          have h1 := LinearMap.mem_ker.mp hqp
          simp [g, Prod.ext_iff] at h1
          ext
          · rfl
          · exact h1.2.symm }
    exact ⟨Q × P, inferInstance, inferInstance, inferInstance, inferInstance, g, hg,
      hasFiniteProjRes_of_equiv ek hK⟩
lemma schanuel_nonempty {R : Type} [CommRing R]
    {N P₁ P₂ : Type} [AddCommGroup N] [Module R N]
    [AddCommGroup P₁] [Module R P₁] [Module.Projective R P₁]
    [AddCommGroup P₂] [Module R P₂] [Module.Projective R P₂]
    (f₁ : P₁ →ₗ[R] N) (hf₁ : Function.Surjective f₁)
    (f₂ : P₂ →ₗ[R] N) (hf₂ : Function.Surjective f₂) :
    Nonempty ((LinearMap.ker f₁ × P₂) ≃ₗ[R] (LinearMap.ker f₂ × P₁)) := by
  let Q : Submodule R (P₁ × P₂) :=
    LinearMap.ker (f₁.comp (LinearMap.fst R P₁ P₂) - f₂.comp (LinearMap.snd R P₁ P₂))
  have hmemQ (p : P₁ × P₂) : p ∈ Q ↔ f₁ p.1 = f₂ p.2 := by
    simp [Q, LinearMap.mem_ker, sub_eq_zero]
  obtain ⟨s₂, hs₂⟩ := Module.projective_lifting_property f₁ f₂ hf₁
  obtain ⟨s₁, hs₁⟩ := Module.projective_lifting_property f₂ f₁ hf₂
  let e₂ : (LinearMap.ker f₁ × P₂) ≃ₗ[R] Q :=
    { toFun := fun ⟨⟨k, hk⟩, p₂⟩ => ⟨(k + s₂ p₂, p₂), by
        rw [hmemQ]
        simp [LinearMap.mem_ker.mp hk]
        exact LinearMap.congr_fun hs₂ p₂⟩
      invFun := fun ⟨⟨p₁, p₂⟩, hq⟩ => ⟨⟨p₁ - s₂ p₂, by
        rw [LinearMap.mem_ker, map_sub, (hmemQ _).mp hq]
        have h2 : f₁ (s₂ p₂) = f₂ p₂ := LinearMap.congr_fun hs₂ p₂
        rw [h2, sub_self]⟩, p₂⟩
      map_add' := fun _ _ => by ext <;> simp [add_assoc, add_left_comm]
      map_smul' := fun _ _ => by ext <;> simp [smul_add]
      left_inv := fun ⟨⟨k, hk⟩, p₂⟩ => by ext <;> simp
      right_inv := fun ⟨⟨p₁, p₂⟩, hq⟩ => by ext <;> simp }
  let e₁ : (LinearMap.ker f₂ × P₁) ≃ₗ[R] Q :=
    { toFun := fun ⟨⟨k, hk⟩, p₁⟩ => ⟨(p₁, k + s₁ p₁), by
        rw [hmemQ]
        simp [LinearMap.mem_ker.mp hk]
        exact (LinearMap.congr_fun hs₁ p₁).symm⟩
      invFun := fun ⟨⟨p₁, p₂⟩, hq⟩ => ⟨⟨p₂ - s₁ p₁, by
        rw [LinearMap.mem_ker, map_sub, ← (hmemQ _).mp hq]
        have h1 : f₂ (s₁ p₁) = f₁ p₁ := LinearMap.congr_fun hs₁ p₁
        rw [h1, sub_self]⟩, p₁⟩
      map_add' := fun _ _ => by ext <;> simp [add_assoc, add_left_comm]
      map_smul' := fun _ _ => by ext <;> simp [smul_add]
      left_inv := fun ⟨⟨k, hk⟩, p₁⟩ => by ext <;> simp
      right_inv := fun ⟨⟨p₁, p₂⟩, hq⟩ => by ext <;> simp }
  exact ⟨e₂.trans e₁.symm⟩
lemma exists_finite_free_surj {R : Type} [CommRing R]
    (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ (r : ℕ) (f : (Fin r → R) →ₗ[R] M), Function.Surjective f := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := M)
  let e := s.equivFin
  let g : (Fin s.card → R) →ₗ[R] M :=
    Fintype.linearCombination R (fun i : Fin s.card => (e.symm i : M))
  refine ⟨s.card, g, fun m => ?_⟩
  have hm : m ∈ Submodule.span R (Set.range fun i : Fin s.card => (e.symm i : M)) := by
    have hr : Set.range (fun i : Fin s.card => (e.symm i : M)) = (s : Set M) := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩; exact (e.symm i).property
      · intro hx; exact ⟨e ⟨x, hx⟩, by simp⟩
    rw [hr, hs]
    exact Submodule.mem_top
  rw [Submodule.mem_span_range_iff_exists_fun] at hm
  obtain ⟨c, hc⟩ := hm
  exact ⟨c, by simpa [g, Fintype.linearCombination_apply] using hc⟩
lemma hasFiniteProjRes_ker_of_succ {R : Type} [CommRing R] [IsNoetherianRing R] :
    ∀ (n : ℕ) (N : Type) [AddCommGroup N] [Module R N]
      (P : Type) [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P]
      (f : P →ₗ[R] N) (_hf : Function.Surjective f),
      HasFiniteProjRes R (n + 1) N → HasFiniteProjRes R n (LinearMap.ker f) := by
  intro n
  induction n with
  | zero =>
    intro N _ _ P _ _ _ _ f hf hres
    obtain ⟨P', _, _, hfinP', hprojP', f', hf', hfinK', hprojK'⟩ := hres
    obtain ⟨e⟩ := schanuel_nonempty f hf f' hf'
    let i : LinearMap.ker f →ₗ[R] LinearMap.ker f' × P :=
      e.toLinearMap.comp (LinearMap.inl R (LinearMap.ker f) P')
    let p : LinearMap.ker f' × P →ₗ[R] LinearMap.ker f :=
      (LinearMap.fst R (LinearMap.ker f) P').comp e.symm.toLinearMap
    have hpi : p.comp i = LinearMap.id := by
      ext x; simp [p, i]
    have hprojK : Module.Projective R (LinearMap.ker f) :=
      Module.Projective.of_split i p hpi
    have hfinK : Module.Finite R (LinearMap.ker f) :=
      Module.Finite.of_surjective p (Function.RightInverse.surjective (LinearMap.congr_fun hpi))
    exact ⟨hfinK, hprojK⟩
  | succ m ih =>
    intro N _ _ P _ _ _ _ f hf hres
    obtain ⟨P', _, _, hfinP', hprojP', f', hf', hK'⟩ := hres
    obtain ⟨e⟩ := schanuel_nonempty f hf f' hf'
    let _ : IsNoetherian R P := isNoetherian_of_isNoetherianRing_of_finite R P
    let _ : Module.Finite R (LinearMap.ker f) := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
    obtain ⟨r, g, hg⟩ := exists_finite_free_surj (R := R) (LinearMap.ker f)
    let Q := Fin r → R
    let h : Q × P' →ₗ[R] LinearMap.ker f' × P :=
      e.toLinearMap.comp (g.prodMap LinearMap.id)
    have hh : Function.Surjective h :=
      e.surjective.comp (fun ⟨a, b⟩ => by
        obtain ⟨q, hq⟩ := hg a
        exact ⟨(q, b), by simp [hq]⟩)
    have hres_prod : HasFiniteProjRes R (m + 1) (LinearMap.ker f' × P) :=
      hasFiniteProjRes_prod_right hK'
    have hker_h : HasFiniteProjRes R m (LinearMap.ker h) :=
      ih (LinearMap.ker f' × P) (Q × P') h hh hres_prod
    let ek : LinearMap.ker h ≃ₗ[R] LinearMap.ker g :=
      { toFun := fun ⟨⟨q, p'⟩, hqp⟩ => ⟨q, by
          have h1 := LinearMap.mem_ker.mp hqp
          simp [h] at h1
          exact h1.1⟩
        invFun := fun ⟨q, hq⟩ => ⟨(q, 0), by
          simp [h, LinearMap.mem_ker.mp hq]⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        left_inv := fun ⟨⟨q, p'⟩, hqp⟩ => by
          have h1 := LinearMap.mem_ker.mp hqp
          simp [h] at h1
          ext
          · rfl
          · exact h1.2.symm
        right_inv := fun ⟨_, _⟩ => rfl }
    exact ⟨Q, inferInstance, inferInstance, inferInstance, inferInstance, g, hg,
      hasFiniteProjRes_of_equiv ek hker_h⟩
noncomputable def baseChangeFinEquiv (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (r : ℕ) :
    (S ⊗[R] (Fin r → R)) ≃ₗ[S] (Fin r → S) := by
  let toF : S ⊗[R] (Fin r → R) →ₗ[S] (Fin r → S) :=
    TensorProduct.AlgebraTensorModule.lift
      { toFun := fun s =>
          { toFun := fun v i => s * algebraMap R S (v i)
            map_add' := fun v₁ v₂ => by ext i; simp [mul_add]
            map_smul' := fun a v => by
              ext i
              simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply, Algebra.smul_def]
              ring }
        map_add' := fun s₁ s₂ => by apply LinearMap.ext; intro v; ext i; simp [add_mul]
        map_smul' := fun s₁ s₂ => by apply LinearMap.ext; intro v; ext i; simp [mul_assoc] }
  let invF : (Fin r → S) →ₗ[S] S ⊗[R] (Fin r → R) :=
    { toFun := fun u => ∑ i : Fin r, u i ⊗ₜ[R] Pi.single i (1 : R)
      map_add' := fun u₁ u₂ => by
        simp only [Pi.add_apply, TensorProduct.add_tmul, Finset.sum_add_distrib]
      map_smul' := fun s u => by
        simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, RingHom.id_apply]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [TensorProduct.smul_tmul', smul_eq_mul] }
  refine LinearEquiv.ofLinearMap toF invF ?_ ?_
  · apply LinearMap.ext; intro u; ext j
    simp only [LinearMap.comp_apply, LinearMap.id_apply, toF, invF, LinearMap.coe_mk, AddHom.coe_mk,
      map_sum, TensorProduct.AlgebraTensorModule.lift_apply, TensorProduct.lift.tmul,
      Finset.sum_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij; simp [Pi.single_eq_of_ne hij.symm]
    · intro hj; exact (hj (Finset.mem_univ j)).elim
  · apply LinearMap.restrictScalars_injective R
    apply TensorProduct.ext'
    intro s v
    change invF (toF (s ⊗ₜ[R] v)) = s ⊗ₜ[R] v
    simp only [toF, invF, LinearMap.coe_mk, AddHom.coe_mk,
      TensorProduct.AlgebraTensorModule.lift_apply, TensorProduct.lift.tmul]
    have hv : v = ∑ i : Fin r, v i • Pi.single i (1 : R) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hv, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    change (s * algebraMap R S (v i)) ⊗ₜ[R] Pi.single i (1 : R) = s ⊗ₜ[R] (v i • Pi.single i 1)
    rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_comm]
lemma mem_ideal_smul_top_of_one_tmul_eq_zero {R : Type} [CommRing R] (I : Ideal R)
    {M : Type} [AddCommGroup M] [Module R M] {m : M}
    (h0 : (1 : R ⧸ I) ⊗ₜ[R] m = 0) : m ∈ I • (⊤ : Submodule R M) := by
  let f₀ : R →ₗ[R] M →ₗ[R] (M ⧸ (I • (⊤ : Submodule R M))) :=
    { toFun := fun a =>
        { toFun := fun z => Submodule.Quotient.mk (a • z)
          map_add' := fun z₁ z₂ => by simp [smul_add]
          map_smul' := fun s z => by simp only [RingHom.id_apply, smul_comm a s z]; rfl }
      map_add' := fun a₁ a₂ => by ext z; simp [add_smul]
      map_smul' := fun s a => by
        ext z
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, smul_eq_mul,
          mul_smul, RingHom.id_apply]
        rfl }
  let f : (R ⧸ I) →ₗ[R] M →ₗ[R] (M ⧸ (I • (⊤ : Submodule R M))) :=
    Submodule.liftQ I f₀ (fun a ha => by
      rw [LinearMap.mem_ker]
      ext z
      simp only [f₀, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply]
      exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.smul_mem_smul ha Submodule.mem_top))
  have hf0 := congrArg (TensorProduct.lift f) h0
  simp only [TensorProduct.lift.tmul, map_zero] at hf0
  have h1 : f (1 : R ⧸ I) m = Submodule.Quotient.mk m := by
    change f (Submodule.Quotient.mk (1 : R)) m = _
    rw [Submodule.liftQ_apply]
    simp [f₀]
  rw [h1] at hf0
  exact (Submodule.Quotient.mk_eq_zero _).mp hf0
lemma exists_one_tmul_eq {R : Type} [CommRing R] (I : Ideal R)
    {M : Type} [AddCommGroup M] [Module R M] (w : (R ⧸ I) ⊗[R] M) :
    ∃ z : M, (1 : R ⧸ I) ⊗ₜ[R] z = w := by
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul c z =>
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    refine ⟨a • z, ?_⟩
    rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    rfl
  | add w₁ w₂ ih₁ ih₂ =>
    obtain ⟨z₁, hz₁⟩ := ih₁
    obtain ⟨z₂, hz₂⟩ := ih₂
    exact ⟨z₁ + z₂, by rw [TensorProduct.tmul_add, hz₁, hz₂]⟩
lemma module_finite_baseChange_of_finite {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Module.Finite S (S ⊗[R] M) := by
  obtain ⟨m, g, hg⟩ := exists_finite_free_surj (R := R) M
  exact Module.Finite.of_surjective
    ((LinearMap.baseChange S g).comp (baseChangeFinEquiv R S m).symm.toLinearMap)
    ((LinearMap.lTensor_surjective S hg).comp (baseChangeFinEquiv R S m).symm.surjective)
lemma eq_bot_of_tensor_residueField_subsingleton
    {R : Type} [CommRing R] [IsLocalRing R]
    {L : Type} [AddCommGroup L] [Module R L] [Module.Finite R L]
    (hsub : Subsingleton (ResidueField R ⊗[R] L)) : Subsingleton L := by
  have htop : (⊤ : Submodule R L) ≤ maximalIdeal R • (⊤ : Submodule R L) := by
    intro x _
    have h0 : (1 : ResidueField R) ⊗ₜ[R] x = 0 := Subsingleton.elim _ _
    exact mem_ideal_smul_top_of_one_tmul_eq_zero (maximalIdeal R) h0
  have hbot : (⊤ : Submodule R L) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) (⊤ : Submodule R L)
      (Module.Finite.fg_top) htop
      (IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal R) bot_ne_top).ge
  exact ⟨fun x y => by
    have hx : x ∈ (⊥ : Submodule R L) := hbot ▸ Submodule.mem_top
    have hy : y ∈ (⊥ : Submodule R L) := hbot ▸ Submodule.mem_top
    simp only [Submodule.mem_bot] at hx hy
    rw [hx, hy]⟩
lemma exists_fin_equiv_of_projective_local {R : Type} [CommRing R] [IsLocalRing R]
    {Z : Type} [AddCommGroup Z] [Module R Z] [Module.Finite R Z] [Module.Projective R Z] :
    ∃ r : ℕ, Nonempty ((Fin r → R) ≃ₗ[R] Z) := by
  let k := ResidueField R
  let _ : Module.Finite k (k ⊗[R] Z) := module_finite_baseChange_of_finite (R := R) (S := k) Z
  let r := Module.finrank k (k ⊗[R] Z)
  let b := Module.finBasisOfFinrankEq k (k ⊗[R] Z) rfl
  choose z hz using fun i : Fin r => exists_one_tmul_eq (maximalIdeal R) (b i)
  let φ : (Fin r → R) →ₗ[R] Z := Fintype.linearCombination R z
  have hφ_surj : Function.Surjective φ := by
    let C := Z ⧸ LinearMap.range φ
    have hC_sub : Subsingleton (k ⊗[R] C) := by
      refine ⟨fun u v => ?_⟩
      have hzero (w : k ⊗[R] C) : w = 0 := by
        induction w using TensorProduct.induction_on with
        | zero => rfl
        | tmul c q =>
          obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ q
          have hby : c ⊗ₜ[R] y ∈ Submodule.span k (Set.range b) := by
            rw [b.span_eq]; exact Submodule.mem_top
          rw [Submodule.mem_span_range_iff_exists_fun] at hby
          obtain ⟨coeff, hcoeff⟩ := hby
          let π : k ⊗[R] Z →ₗ[k] k ⊗[R] C :=
            LinearMap.baseChange k (LinearMap.range φ).mkQ
          have hπ : π (c ⊗ₜ[R] y) = c ⊗ₜ[R] (LinearMap.range φ).mkQ y := rfl
          rw [← hπ, ← hcoeff, map_sum]
          refine Finset.sum_eq_zero fun i _ => ?_
          rw [map_smul, ← hz i]
          change coeff i • ((1 : k) ⊗ₜ[R] (LinearMap.range φ).mkQ (z i)) = 0
          have hmem : z i ∈ LinearMap.range φ :=
            ⟨Pi.single i 1, by simp [φ, Fintype.linearCombination_apply]⟩
          have hq0 : (LinearMap.range φ).mkQ (z i) = 0 :=
            (Submodule.Quotient.mk_eq_zero _).mpr hmem
          rw [hq0, TensorProduct.tmul_zero, smul_zero]
        | add w₁ w₂ ih₁ ih₂ => rw [ih₁, ih₂, add_zero]
      rw [hzero u, hzero v]
    have hC_sub' : Subsingleton C := eq_bot_of_tensor_residueField_subsingleton hC_sub
    intro y
    have h0 : (LinearMap.range φ).mkQ y = 0 := Subsingleton.elim _ _
    exact (Submodule.Quotient.mk_eq_zero _).mp h0
  obtain ⟨s, hs⟩ := Module.projective_lifting_property φ LinearMap.id hφ_surj
  have hφs (y : Z) : φ (s y) = y := LinearMap.congr_fun hs y
  let e_split : (Fin r → R) ≃ₗ[R] (Z × LinearMap.ker φ) :=
    { toFun := fun v => (φ v, ⟨v - s (φ v), by
        rw [LinearMap.mem_ker, map_sub, hφs (φ v), sub_self]⟩)
      invFun := fun ⟨y, ⟨w, _⟩⟩ => s y + w
      map_add' := fun _ _ => by ext <;> simp; ring
      map_smul' := fun _ _ => by ext <;> simp [smul_sub]
      left_inv := fun v => by simp
      right_inv := fun ⟨y, ⟨w, hw⟩⟩ => by
        have hfw : φ w = 0 := LinearMap.mem_ker.mp hw
        ext
        · simp [hfw, hφs]
        · simp [hfw, hφs] }
  let _ : Module.Finite R (LinearMap.ker φ) :=
    Module.Finite.of_surjective ((LinearMap.snd R Z (LinearMap.ker φ)).comp e_split.toLinearMap)
      (Prod.snd_surjective.comp e_split.surjective)
  have hker_sub : Subsingleton (k ⊗[R] LinearMap.ker φ) := by
    let e_base : (k ⊗[R] (Fin r → R)) ≃ₗ[k] (k ⊗[R] Z) × (k ⊗[R] LinearMap.ker φ) :=
      (LinearEquiv.baseChange R k _ _ e_split).trans
        (TensorProduct.prodRight R k k Z (LinearMap.ker φ))
    have hfr1 : Module.finrank k (k ⊗[R] (Fin r → R)) = r := by
      rw [(baseChangeFinEquiv R k r).finrank_eq, Module.finrank_pi]
      simp
    have hfr2 : Module.finrank k ((k ⊗[R] Z) × (k ⊗[R] LinearMap.ker φ)) =
        r + Module.finrank k (k ⊗[R] LinearMap.ker φ) := by
      rw [Module.finrank_prod]
    have hfr_eq : Module.finrank k (k ⊗[R] LinearMap.ker φ) = 0 := by
      have h3 := e_base.finrank_eq
      rw [hfr1, hfr2] at h3
      omega
    exact Module.finrank_zero_iff.mp hfr_eq
  have hker_sub' : Subsingleton (LinearMap.ker φ) :=
    eq_bot_of_tensor_residueField_subsingleton hker_sub
  have hφ_inj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    have h0 : (⟨v, hv⟩ : LinearMap.ker φ) = 0 := Subsingleton.elim _ _
    exact congrArg Subtype.val h0
  exact ⟨r, ⟨LinearEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩⟩⟩
theorem hasFiniteProjRes_of_isRegularLocalRing_aux (d : ℕ) :
    ∀ (R : Type) [CommRing R] [IsRegularLocalRing R],
      (maximalIdeal R).spanFinrank = d →
      ∀ (N : Type) [AddCommGroup N] [Module R N] [Module.Finite R N],
        HasFiniteProjRes R d N := by
  induction d with
  | zero =>
    intro R _ _ h0 N _ _ _
    have hm_bot : maximalIdeal R = ⊥ := by
      have h1 : Module.finrank (ResidueField R) (CotangentSpace R) = 0 := by
        have h2 := (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance
        rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := R), h0] at h2
        exact_mod_cast h2
      exact (IsLocalRing.isField_iff_maximalIdeal_eq).mp
        (subsingleton_cotangentSpace_iff.mp (Module.finrank_zero_iff.mp h1))
    let _ : Field R := (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hm_bot).toField
    exact ⟨inferInstance, inferInstance⟩
  | succ n ih =>
    intro R _ _ hdim N _ _ _
    let _ : IsDomain R := isDomain_of_isRegularLocalRing R
    obtain ⟨x, hx, hx2, hx_ne⟩ := exists_param_of_isRegularLocalRing hdim
    let I := Ideal.span ({x} : Set R)
    have hI_le : I ≤ maximalIdeal R := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx)
    have hI_ne : I ≠ ⊤ := fun h => (maximalIdeal.isMaximal R).ne_top (top_unique (h ▸ hI_le))
    let _ : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI_ne
    let _ : IsLocalRing (R ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    obtain ⟨hreg_q, hdim_q⟩ := isRegularLocalRing_quotient_span_singleton hdim hx hx2
    obtain ⟨r₀, f₀, hf₀⟩ := exists_finite_free_surj (R := R) N
    let F₀ := Fin r₀ → R
    let K := LinearMap.ker f₀
    let _ : IsNoetherian R F₀ := isNoetherian_of_isNoetherianRing_of_finite R F₀
    let _ : Module.Finite R K := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
    have hK_reg : ∀ y : K, x • y = 0 → y = 0 := fun y hy => by
      ext i
      have hi : x * y.val i = 0 := congrFun (congrArg Subtype.val hy) i
      exact (mul_eq_zero.mp hi).resolve_left hx_ne
    have hdescent : ∀ (m : ℕ) (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M],
        (∀ y : M, x • y = 0 → y = 0) →
        HasFiniteProjRes (R ⧸ I) m ((R ⧸ I) ⊗[R] M) →
        HasFiniteProjRes R m M := by
      intro m
      induction m with
      | zero =>
        intro M _ _ _ hregM hresM
        obtain ⟨hfin_q, hproj_q⟩ := hresM
        obtain ⟨r, ⟨e_q⟩⟩ := exists_fin_equiv_of_projective_local (R := R ⧸ I) (Z := (R ⧸ I) ⊗[R] M)
        choose z hz using fun i : Fin r => exists_one_tmul_eq I (e_q (Pi.single i 1))
        let φ : (Fin r → R) →ₗ[R] M := Fintype.linearCombination R z
        have hbase_eq : LinearMap.baseChange (R ⧸ I) φ =
            e_q.toLinearMap.comp (baseChangeFinEquiv R (R ⧸ I) r).toLinearMap := by
          apply LinearMap.restrictScalars_injective R
          apply TensorProduct.ext'
          intro c v
          change LinearMap.baseChange (R ⧸ I) φ (c ⊗ₜ[R] v) =
            e_q (baseChangeFinEquiv R (R ⧸ I) r (c ⊗ₜ[R] v))
          rw [LinearMap.baseChange_tmul]
          have hv : v = ∑ i : Fin r, v i • Pi.single i (1 : R) := by
            ext j; simp [Finset.sum_apply, Pi.single_apply]
          conv_lhs => rw [hv, map_sum]
          rw [TensorProduct.tmul_sum]
          have h1 : ∀ i : Fin r, c ⊗ₜ[R] φ (v i • Pi.single i 1) =
              (c * Ideal.Quotient.mk I (v i)) • e_q (Pi.single i 1) := by
            intro i
            rw [map_smul, TensorProduct.tmul_smul]
            have hφi : φ (Pi.single i 1) = z i := by
              simp [φ, Fintype.linearCombination_apply]
            rw [hφi]
            have hc : c ⊗ₜ[R] z i = c • ((1 : R ⧸ I) ⊗ₜ[R] z i) := by
              rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
            rw [hc, hz i, ← smul_assoc]
            congr 1
            rw [Algebra.smul_def, mul_comm]
            rfl
          simp_rw [h1, ← map_smul]
          rw [← map_sum]
          congr 1
          ext j
          simp [baseChangeFinEquiv, Finset.sum_apply, Pi.single_apply]
        have hbase_bij : Function.Bijective (LinearMap.baseChange (R ⧸ I) φ) := by
          rw [hbase_eq]
          exact e_q.bijective.comp (baseChangeFinEquiv R (R ⧸ I) r).bijective
        have hφ_surj : Function.Surjective φ := by
          let C := M ⧸ LinearMap.range φ
          have htop : (⊤ : Submodule R C) ≤ maximalIdeal R • (⊤ : Submodule R C) := by
            intro u _
            obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ u
            obtain ⟨t, ht⟩ := hbase_bij.2 ((1 : R ⧸ I) ⊗ₜ[R] y)
            obtain ⟨v, rfl⟩ := exists_one_tmul_eq I t
            have h0 : (1 : R ⧸ I) ⊗ₜ[R] (y - φ v) = 0 := by
              rw [TensorProduct.tmul_sub, ← ht]; simp
            have hmemI : y - φ v ∈ I • (⊤ : Submodule R M) :=
              mem_ideal_smul_top_of_one_tmul_eq_zero I h0
            have hmem_m : y - φ v ∈ maximalIdeal R • (⊤ : Submodule R M) :=
              Submodule.smul_mono_left hI_le hmemI
            have hmk0 : (LinearMap.range φ).mkQ (φ v) = 0 :=
              (Submodule.Quotient.mk_eq_zero _).mpr ⟨v, rfl⟩
            have hmk : (LinearMap.range φ).mkQ y = (LinearMap.range φ).mkQ (y - φ v) := by
              rw [map_sub, hmk0, sub_zero]
            rw [hmk]
            refine Submodule.smul_induction_on hmem_m ?_ ?_
            · intro a ha m _
              rw [map_smul]
              exact Submodule.smul_mem_smul ha Submodule.mem_top
            · intro m₁ m₂ hm₁ hm₂
              rw [map_add]
              exact Submodule.add_mem _ hm₁ hm₂
          have hbot : (⊤ : Submodule R C) = ⊥ :=
            Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) (⊤ : Submodule R C)
              (Module.Finite.fg_top) htop
              (IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal R) bot_ne_top).ge
          intro y
          have h0 : (LinearMap.range φ).mkQ y = 0 := by
            have hmem : (LinearMap.range φ).mkQ y ∈ (⊥ : Submodule R C) := hbot ▸ Submodule.mem_top
            simpa using hmem
          exact (Submodule.Quotient.mk_eq_zero _).mp h0
        have hker_le : LinearMap.ker φ ≤ maximalIdeal R • LinearMap.ker φ := by
          intro v hv
          have h0 : LinearMap.baseChange (R ⧸ I) φ ((1 : R ⧸ I) ⊗ₜ[R] v) = 0 := by
            rw [LinearMap.baseChange_tmul, LinearMap.mem_ker.mp hv, TensorProduct.tmul_zero]
          have h1 : (1 : R ⧸ I) ⊗ₜ[R] v = 0 := hbase_bij.1 (h0.trans (map_zero _).symm)
          have hcoord (i : Fin r) : v i ∈ I := by
            have hev := congrFun (congrArg (baseChangeFinEquiv R (R ⧸ I) r) h1) i
            simp only [baseChangeFinEquiv, map_zero, Pi.zero_apply] at hev
            change (1 : R ⧸ I) * Ideal.Quotient.mk I (v i) = 0 at hev
            rw [one_mul] at hev
            exact Ideal.Quotient.eq_zero_iff_mem.mp hev
          choose w hw using fun i : Fin r => Ideal.mem_span_singleton.mp (hcoord i)
          have hv_eq : v = x • w := by ext i; exact hw i
          have hw_ker : w ∈ LinearMap.ker φ := by
            rw [LinearMap.mem_ker]
            apply hregM (φ w)
            rw [← map_smul, ← hv_eq]
            exact LinearMap.mem_ker.mp hv
          rw [hv_eq]
          exact Submodule.smul_mem_smul hx hw_ker
        have hker_bot : LinearMap.ker φ = ⊥ :=
          Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) (LinearMap.ker φ)
            (IsNoetherian.noetherian _) hker_le
            (IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal R) bot_ne_top).ge
        have hφ_inj : Function.Injective φ := LinearMap.ker_eq_bot.mp hker_bot
        exact hasFiniteProjRes_of_equiv (LinearEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩)
          ⟨inferInstance, inferInstance⟩
      | succ k ihk =>
        intro M _ _ _ hregM hresM
        obtain ⟨r, g, hg⟩ := exists_finite_free_surj (R := R) M
        let G := Fin r → R
        let L := LinearMap.ker g
        let _ : IsNoetherian R G := isNoetherian_of_isNoetherianRing_of_finite R G
        let _ : Module.Finite R L := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
        have hL_reg : ∀ y : L, x • y = 0 → y = 0 := fun y hy => by
          ext i
          have hi : x * y.val i = 0 := congrFun (congrArg Subtype.val hy) i
          exact (mul_eq_zero.mp hi).resolve_left hx_ne
        let gq : ((R ⧸ I) ⊗[R] G) →ₗ[R ⧸ I] ((R ⧸ I) ⊗[R] M) := LinearMap.baseChange (R ⧸ I) g
        have hgq_surj : Function.Surjective gq := LinearMap.lTensor_surjective (R ⧸ I) hg
        let _ : Module.Finite (R ⧸ I) ((R ⧸ I) ⊗[R] G) :=
          Module.Finite.equiv (baseChangeFinEquiv R (R ⧸ I) r).symm
        let _ : Module.Projective (R ⧸ I) ((R ⧸ I) ⊗[R] G) :=
          Module.Projective.of_equiv (baseChangeFinEquiv R (R ⧸ I) r).symm
        have hker_gq : HasFiniteProjRes (R ⧸ I) k (LinearMap.ker gq) :=
          hasFiniteProjRes_ker_of_succ k ((R ⧸ I) ⊗[R] M) ((R ⧸ I) ⊗[R] G) gq hgq_surj hresM
        let ιq : ((R ⧸ I) ⊗[R] L) →ₗ[R ⧸ I] LinearMap.ker gq :=
          LinearMap.codRestrict (LinearMap.ker gq) (LinearMap.baseChange (R ⧸ I) L.subtype) (fun t => by
            rw [LinearMap.mem_ker]
            induction t using TensorProduct.induction_on with
            | zero => simp
            | tmul c y =>
              simp only [LinearMap.baseChange_tmul, Submodule.coe_subtype, gq]
              rw [LinearMap.mem_ker.mp y.property, TensorProduct.tmul_zero]
            | add t₁ t₂ ih₁ ih₂ => simp [ih₁, ih₂])
        have hιq_bij : Function.Bijective ιq := by
          constructor
          · rw [injective_iff_map_eq_zero]
            intro t ht
            obtain ⟨y, rfl⟩ := exists_one_tmul_eq I t
            have h0 : (1 : R ⧸ I) ⊗ₜ[R] y.val = 0 := congrArg Subtype.val ht
            have hcoord (i : Fin r) : y.val i ∈ I := by
              have hev := congrFun (congrArg (baseChangeFinEquiv R (R ⧸ I) r) h0) i
              simp only [baseChangeFinEquiv, map_zero, Pi.zero_apply] at hev
              change (1 : R ⧸ I) * Ideal.Quotient.mk I (y.val i) = 0 at hev
              rw [one_mul] at hev
              exact Ideal.Quotient.eq_zero_iff_mem.mp hev
            choose w hw using fun i : Fin r => Ideal.mem_span_singleton.mp (hcoord i)
            have hy_eq : y.val = x • w := by ext i; exact hw i
            have hw_L : w ∈ L := by
              rw [LinearMap.mem_ker]
              apply hregM (g w)
              rw [← map_smul, ← hy_eq]
              exact LinearMap.mem_ker.mp y.property
            have hy' : y = x • ⟨w, hw_L⟩ := Subtype.ext hy_eq
            rw [hy', ← TensorProduct.smul_tmul]
            have hx0 : x • (1 : R ⧸ I) = 0 := by
              rw [Algebra.smul_def, mul_one]
              exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
            rw [hx0, TensorProduct.zero_tmul]
          · rintro ⟨u, hu⟩
            obtain ⟨v, rfl⟩ := exists_one_tmul_eq I u
            have h0 : (1 : R ⧸ I) ⊗ₜ[R] g v = 0 := LinearMap.mem_ker.mp hu
            have hmemI : g v ∈ I • (⊤ : Submodule R M) :=
              mem_ideal_smul_top_of_one_tmul_eq_zero I h0
            have hex_m : ∃ m : M, x • m = g v := by
              refine Submodule.smul_induction_on hmemI ?_ ?_
              · intro a ha m _
                obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
                exact ⟨c • m, by rw [smul_smul]⟩
              · rintro _ _ ⟨m₁, rfl⟩ ⟨m₂, rfl⟩
                exact ⟨m₁ + m₂, by rw [smul_add]⟩
            obtain ⟨m, hm⟩ := hex_m
            obtain ⟨w, rfl⟩ := hg m
            have hv_mem : v - x • w ∈ L := by
              rw [LinearMap.mem_ker, map_sub, map_smul, hm, sub_self]
            refine ⟨(1 : R ⧸ I) ⊗ₜ[R] ⟨v - x • w, hv_mem⟩, Subtype.ext ?_⟩
            change (1 : R ⧸ I) ⊗ₜ[R] (v - x • w) = (1 : R ⧸ I) ⊗ₜ[R] v
            rw [TensorProduct.tmul_sub, ← TensorProduct.smul_tmul]
            have hx0 : x • (1 : R ⧸ I) = 0 := by
              rw [Algebra.smul_def, mul_one]
              exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
            rw [hx0, TensorProduct.zero_tmul, sub_zero]
        have hresL : HasFiniteProjRes (R ⧸ I) k ((R ⧸ I) ⊗[R] L) :=
          hasFiniteProjRes_of_equiv (LinearEquiv.ofBijective ιq hιq_bij).symm hker_gq
        exact ⟨G, inferInstance, inferInstance, inferInstance, inferInstance, g, hg,
          ihk L hL_reg hresL⟩
    let _ : Module.Finite (R ⧸ I) ((R ⧸ I) ⊗[R] K) :=
      module_finite_baseChange_of_finite (R := R) (S := R ⧸ I) K
    have hK_q : HasFiniteProjRes (R ⧸ I) n ((R ⧸ I) ⊗[R] K) :=
      ih (R ⧸ I) hdim_q ((R ⧸ I) ⊗[R] K)
    have hK_res : HasFiniteProjRes R n K := hdescent n K hK_reg hK_q
    exact ⟨F₀, inferInstance, inferInstance, inferInstance, inferInstance, f₀, hf₀, hK_res⟩
theorem hasFiniteProjRes_of_isRegularLocalRing
    (R : Type) [CommRing R] [IsRegularLocalRing R]
    (N : Type) [AddCommGroup N] [Module R N] [Module.Finite R N] :
    HasFiniteProjRes R (maximalIdeal R).spanFinrank N :=
  hasFiniteProjRes_of_isRegularLocalRing_aux (maximalIdeal R).spanFinrank R rfl N
end FiniteProjRes
section TorLES
noncomputable abbrev torMod (R : Type) [CommRing R]
    (M N : Type) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (i : ℕ) : ModuleCat.{0} R :=
  ((Tor (ModuleCat.{0} R) i).obj (ModuleCat.of R M)).obj (ModuleCat.of R N)
noncomputable def torMap {R : Type} [CommRing R]
    (M : Type) [AddCommGroup M] [Module R M]
    {A B : Type} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (f : A →ₗ[R] B) (i : ℕ) :
    torMod R M A i →ₗ[R] torMod R M B i :=
  (((Tor (ModuleCat.{0} R) i).obj (ModuleCat.of R M)).map (ModuleCat.ofHom f)).hom
noncomputable def torZeroEquiv (R : Type) [CommRing R]
    (M N : Type) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] :
    torMod R M N 0 ≃ₗ[R] (M ⊗[R] N) :=
  (((tensoringLeft (ModuleCat.{0} R)).obj (ModuleCat.of R M)).leftDerivedZeroIsoSelf.app
    (ModuleCat.of R N)).toLinearEquiv
lemma torZeroEquiv_naturality {R : Type} [CommRing R]
    (M : Type) [AddCommGroup M] [Module R M]
    {A B : Type} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (f : A →ₗ[R] B) (x : torMod R M A 0) :
    torZeroEquiv R M B (torMap M f 0 x) = LinearMap.lTensor M f (torZeroEquiv R M A x) := by
  have hnat := (((tensoringLeft (ModuleCat.{0} R)).obj
    (ModuleCat.of R M)).leftDerivedZeroIsoSelf.hom.naturality (ModuleCat.ofHom f))
  exact congrArg (fun φ : torMod R M A 0 ⟶ ModuleCat.of R (M ⊗[R] B) => φ.hom x) hnat
lemma tor_succ_subsingleton_of_projective {R : Type} [CommRing R]
    (M N : Type) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Projective R N] (i : ℕ) :
    Subsingleton (torMod R M N (i + 1)) :=
  ModuleCat.isZero_iff_subsingleton.mp
    (isZero_Tor_succ_of_projective (ModuleCat.{0} R) (ModuleCat.of R M) (ModuleCat.of R N) i)
noncomputable def projectiveResolutionOfExact {R : Type} [CommRing R]
    (B : Type) [AddCommGroup B] [Module R B]
    (K : ChainComplex (ModuleCat.{0} R) ℕ)
    (hproj : ∀ n, Module.Projective R (K.X n))
    (ε : (K.X 0) →ₗ[R] B)
    (hε_surj : Function.Surjective ε)
    (hε_comp : ∀ x : K.X 1, ε ((K.d 1 0).hom x) = 0)
    (hε_exact : ∀ x : K.X 0, ε x = 0 → ∃ y : K.X 1, (K.d 1 0).hom y = x)
    (hexact : ∀ n : ℕ, ∀ x : K.X (n + 1), (K.d (n + 1) n).hom x = 0 →
      ∃ y : K.X (n + 2), (K.d (n + 2) (n + 1)).hom y = x) :
    ProjectiveResolution (ModuleCat.of R B) := by
  let π : K ⟶ (ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B) :=
    (ChainComplex.toSingle₀Equiv K (ModuleCat.of R B)).symm
      ⟨ModuleCat.ofHom ε, by ext x; exact hε_comp x⟩
  have hπ0 : (π.f 0).hom = ε := by
    change ((ChainComplex.toSingle₀Equiv K (ModuleCat.of R B)).symm
      ⟨ModuleCat.ofHom ε, _⟩ |>.f 0).hom = ε
    rw [ChainComplex.toSingle₀Equiv_symm_apply_f_zero]
    rfl
  have hq : QuasiIso π := by
    rw [quasiIso_iff]
    intro n
    cases n with
    | zero =>
      rw [quasiIsoAt_iff_isIso_homologyMap]
      have hK_g0 : (K.sc 0).g = 0 := K.shape 0 _ (by simp)
      have hS_g0 : (((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).sc 0).g = 0 :=
        ((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).shape 0 _ (by simp)
      have _ : IsIso (K.homologyι 0) := ShortComplex.isIso_homologyι (K.sc 0) hK_g0
      have _ : IsIso (((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).homologyι 0) :=
        ShortComplex.isIso_homologyι _ hS_g0
      have hcomm : (HomologicalComplex.homologyMap π 0 ≫
          ((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).homologyι 0) =
          (K.homologyι 0 ≫ HomologicalComplex.opcyclesMap π 0) :=
        HomologicalComplex.homologyι_naturality π 0
      have hop_bij : Function.Bijective (HomologicalComplex.opcyclesMap π 0).hom := by
        constructor
        · intro u v huv
          have hp_surj : Function.Surjective (K.pOpcycles 0) :=
            (ModuleCat.epi_iff_surjective (K.pOpcycles 0)).mp inferInstance
          obtain ⟨x, rfl⟩ := hp_surj u
          obtain ⟨y, rfl⟩ := hp_surj v
          have hsub : HomologicalComplex.opcyclesMap π 0 (K.pOpcycles 0 (x - y)) = 0 := by
            change (HomologicalComplex.opcyclesMap π 0).hom ((K.pOpcycles 0).hom (x - y)) = 0
            rw [map_sub, map_sub, huv, sub_self]
          have hnat : (HomologicalComplex.opcyclesMap π 0).hom ((K.pOpcycles 0).hom (x - y)) =
              (((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).pOpcycles 0).hom
                ((π.f 0).hom (x - y)) :=
            congrArg (fun φ : K.X 0 ⟶
              ((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).opcycles 0 =>
                φ.hom (x - y))
              (ShortComplex.p_opcyclesMap ((HomologicalComplex.shortComplexFunctor _ _ 0).map π))
          rw [hnat] at hsub
          have hmem := (ShortComplex.moduleCat_pOpcycles_eq_zero_iff _ _).mp hsub
          have hSf0 : (((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).sc 0).f = 0 := by
            simp [HomologicalComplex.sc]; rfl
          obtain ⟨w, hw⟩ := hmem
          have hε0 : ε (x - y) = 0 := by
            rw [← hπ0]
            have hw0 : ((((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).sc 0).f).hom w = 0 := by
              rw [hSf0]; rfl
            exact hw.symm.trans hw0
          obtain ⟨z, hz⟩ := hε_exact (x - y) hε0
          have h0 : (K.pOpcycles 0).hom (x - y) = 0 := by
            rw [← hz]
            exact congrArg (fun φ : K.X 1 ⟶ K.opcycles 0 => φ.hom z) (K.d_pOpcycles 1 0)
          rw [map_sub] at h0
          exact sub_eq_zero.mp h0
        · intro w
          have hpS_surj : Function.Surjective
              (((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).pOpcycles 0) :=
            (ModuleCat.epi_iff_surjective _).mp inferInstance
          obtain ⟨b, rfl⟩ := hpS_surj w
          obtain ⟨x, hx⟩ := hε_surj b
          refine ⟨K.pOpcycles 0 x, ?_⟩
          have hnat : (HomologicalComplex.opcyclesMap π 0).hom ((K.pOpcycles 0).hom x) =
              (((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).pOpcycles 0).hom
                ((π.f 0).hom x) :=
            congrArg (fun φ : K.X 0 ⟶
              ((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).opcycles 0 =>
                φ.hom x)
              (ShortComplex.p_opcyclesMap ((HomologicalComplex.shortComplexFunctor _ _ 0).map π))
          change (HomologicalComplex.opcyclesMap π 0).hom ((K.pOpcycles 0).hom x) = _
          rw [hnat]
          have hxb : (π.f 0).hom x = b := by
            have h1 : (π.f 0).hom x = ε x := LinearMap.congr_fun hπ0 x
            exact h1.trans hx
          exact congrArg
            (((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).pOpcycles 0).hom hxb
      have hop_iso : IsIso (HomologicalComplex.opcyclesMap π 0) :=
        ⟨ModuleCat.ofHom (LinearEquiv.ofBijective _ hop_bij).symm.toLinearMap,
          by ext u; exact (LinearEquiv.ofBijective _ hop_bij).left_inv u,
          by ext v; exact (LinearEquiv.ofBijective _ hop_bij).right_inv v⟩
      have hmul : HomologicalComplex.homologyMap π 0 =
          K.homologyι 0 ≫ HomologicalComplex.opcyclesMap π 0 ≫
            inv (((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).homologyι 0) := by
        rw [← Category.assoc, ← hcomm, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      rw [hmul]
      infer_instance
    | succ m =>
      rw [quasiIsoAt_iff_exactAt' π (m + 1) (ChainComplex.exactAt_succ_single_obj _ _)]
      rw [HomologicalComplex.exactAt_iff' K (m + 2) (m + 1) m (by simp) (by simp)]
      rw [ShortComplex.moduleCat_exact_iff]
      exact hexact m
  exact
    { complex := K
      projective := fun n => by
        let _ := hproj n
        infer_instance
      π := π
      quasiIso := hq }
lemma horseshoe_tor_les {R : Type} [CommRing R]
    (M : Type) [AddCommGroup M] [Module R M]
    {A B C : Type} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    (i : A →ₗ[R] B) (p : B →ₗ[R] C)
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hip : LinearMap.range i = LinearMap.ker p) :
    ∃ δ : ∀ n : ℕ, torMod R M C (n + 1) →ₗ[R] torMod R M A n,
      (∀ n, Function.Exact (δ n) (torMap M i n)) ∧
      (∀ n, Function.Exact (torMap M i n) (torMap M p n)) ∧
      (∀ n, Function.Exact (torMap M p (n + 1)) (δ n)) := by
  let PA : ProjectiveResolution (ModuleCat.of R A) := projectiveResolution (ModuleCat.of R A)
  let PC : ProjectiveResolution (ModuleCat.of R C) := projectiveResolution (ModuleCat.of R C)
  have hPA_proj (n : ℕ) : Module.Projective R (PA.complex.X n) :=
    ModuleCat.projective_of_module_projective (P := PA.complex.X n)
  have hPC_proj (n : ℕ) : Module.Projective R (PC.complex.X n) :=
    ModuleCat.projective_of_module_projective (P := PC.complex.X n)
  let εA : PA.complex.X 0 →ₗ[R] A := (PA.π.f 0).hom
  let εC : PC.complex.X 0 →ₗ[R] C := (PC.π.f 0).hom
  have hεA_surj : Function.Surjective εA :=
    (ModuleCat.epi_iff_surjective (PA.π.f 0)).mp inferInstance
  have hεC_surj : Function.Surjective εC :=
    (ModuleCat.epi_iff_surjective (PC.π.f 0)).mp inferInstance
  have hεA_comp (x : PA.complex.X 1) : εA ((PA.complex.d 1 0).hom x) = 0 :=
    congrArg (fun φ : PA.complex.X 1 ⟶ ModuleCat.of R A => φ.hom x) PA.complex_d_comp_π_f_zero
  have hεC_comp (x : PC.complex.X 1) : εC ((PC.complex.d 1 0).hom x) = 0 :=
    congrArg (fun φ : PC.complex.X 1 ⟶ ModuleCat.of R C => φ.hom x) PC.complex_d_comp_π_f_zero
  have hε_exact_of_res {X : Type} [AddCommGroup X] [Module R X]
      (PX : ProjectiveResolution (ModuleCat.of R X)) (x : PX.complex.X 0)
      (hx : (PX.π.f 0).hom x = 0) :
      ∃ y : PX.complex.X 1, (PX.complex.d 1 0).hom y = x := by
    let Q := PX.complex.X 0 ⧸ LinearMap.range (PX.complex.d 1 0).hom
    let q : PX.complex.X 0 ⟶ ModuleCat.of R Q := ModuleCat.ofHom (LinearMap.range (PX.complex.d 1 0).hom).mkQ
    have hqw : (PX.complex.d 1 0 ≫ q) = 0 := by
      ext z; exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨z, rfl⟩
    let desc : ModuleCat.of R X ⟶ ModuleCat.of R Q :=
      PX.isColimitCokernelCofork.desc (CokernelCofork.ofπ q hqw)
    have hfac : (PX.π.f 0 ≫ desc) = q :=
      PX.isColimitCokernelCofork.fac (CokernelCofork.ofπ q hqw) WalkingParallelPair.one
    have hqx : q.hom x = 0 := by
      have h1 : desc.hom ((PX.π.f 0).hom x) = q.hom x :=
        congrArg (fun φ : PX.complex.X 0 ⟶ ModuleCat.of R Q => φ.hom x) hfac
      have hx0 : (PX.π.f 0).hom x = (0 : X) := hx
      rw [← h1, hx0]
      exact map_zero desc.hom
    exact (Submodule.Quotient.mk_eq_zero _).mp hqx
  have hεA_exact := hε_exact_of_res PA
  have hεC_exact := hε_exact_of_res PC
  have hPA_exact (n : ℕ) (x : PA.complex.X (n + 1)) (hx : (PA.complex.d (n + 1) n).hom x = 0) :
      ∃ y : PA.complex.X (n + 2), (PA.complex.d (n + 2) (n + 1)).hom y = x :=
    (ShortComplex.moduleCat_exact_iff _).mp (PA.exact_succ n) x hx
  have hPC_exact (n : ℕ) (x : PC.complex.X (n + 1)) (hx : (PC.complex.d (n + 1) n).hom x = 0) :
      ∃ y : PC.complex.X (n + 2), (PC.complex.d (n + 2) (n + 1)).hom y = x :=
    (ShortComplex.moduleCat_exact_iff _).mp (PC.exact_succ n) x hx
  have hPA_dd (n : ℕ) (x : PA.complex.X (n + 2)) :
      (PA.complex.d (n + 1) n).hom ((PA.complex.d (n + 2) (n + 1)).hom x) = 0 :=
    congrArg (fun φ : PA.complex.X (n + 2) ⟶ PA.complex.X n => φ.hom x)
      (PA.complex.d_comp_d (n + 2) (n + 1) n)
  have hPC_dd (n : ℕ) (x : PC.complex.X (n + 2)) :
      (PC.complex.d (n + 1) n).hom ((PC.complex.d (n + 2) (n + 1)).hom x) = 0 :=
    congrArg (fun φ : PC.complex.X (n + 2) ⟶ PC.complex.X n => φ.hom x)
      (PC.complex.d_comp_d (n + 2) (n + 1) n)
  let _ := hPC_proj 0
  obtain ⟨s0, hs0⟩ := Module.projective_lifting_property p εC hp
  let εB : (PA.complex.X 0 × PC.complex.X 0) →ₗ[R] B := (i.comp εA).coprod s0
  have h_step0 : ∃ h0 : PC.complex.X 1 →ₗ[R] PA.complex.X 0,
      ∀ c : PC.complex.X 1, i (εA (h0 c)) + s0 ((PC.complex.d 1 0).hom c) = 0 := by
    let _ := hPC_proj 1
    let neg_s0_dC : PC.complex.X 1 →ₗ[R] LinearMap.ker p :=
      LinearMap.codRestrict (LinearMap.ker p) (-(s0.comp (PC.complex.d 1 0).hom)) (fun c => by
        rw [LinearMap.mem_ker, LinearMap.neg_apply, map_neg, LinearMap.comp_apply]
        have h1 : p (s0 ((PC.complex.d 1 0).hom c)) = εC ((PC.complex.d 1 0).hom c) :=
          LinearMap.congr_fun hs0 _
        rw [h1, hεC_comp, neg_zero])
    let mapA : PA.complex.X 0 →ₗ[R] LinearMap.ker p :=
      LinearMap.codRestrict (LinearMap.ker p) (i.comp εA) (fun a => by
        rw [LinearMap.mem_ker, LinearMap.comp_apply, ← LinearMap.mem_ker, ← hip]
        exact ⟨εA a, rfl⟩)
    have hmapA_surj : Function.Surjective mapA := by
      rintro ⟨b, hb⟩
      rw [← hip] at hb
      obtain ⟨a, rfl⟩ := hb
      obtain ⟨x, rfl⟩ := hεA_surj a
      exact ⟨x, rfl⟩
    obtain ⟨h0, hh0⟩ := Module.projective_lifting_property mapA neg_s0_dC hmapA_surj
    refine ⟨h0, fun c => ?_⟩
    have hc := congrArg Subtype.val (LinearMap.congr_fun hh0 c)
    change i (εA (h0 c)) = -(s0 ((PC.complex.d 1 0).hom c)) at hc
    rw [hc, neg_add_cancel]
  have h_next : ∀ (n : ℕ) (hcur : PC.complex.X (n + 1) →ₗ[R] PA.complex.X n),
      (∀ c : PC.complex.X (n + 2), ∃ a : PA.complex.X (n + 1),
        (PA.complex.d (n + 1) n).hom a = -(hcur ((PC.complex.d (n + 2) (n + 1)).hom c))) →
      ∃ hnxt : PC.complex.X (n + 2) →ₗ[R] PA.complex.X (n + 1),
        ∀ c : PC.complex.X (n + 2),
          (PA.complex.d (n + 1) n).hom (hnxt c) + hcur ((PC.complex.d (n + 2) (n + 1)).hom c) = 0 := by
    intro n hcur hpre
    let _ := hPC_proj (n + 2)
    let targ : PC.complex.X (n + 2) →ₗ[R] LinearMap.range (PA.complex.d (n + 1) n).hom :=
      LinearMap.codRestrict _ (-(hcur.comp (PC.complex.d (n + 2) (n + 1)).hom)) (fun c => hpre c)
    obtain ⟨hnxt, hhnxt⟩ := Module.projective_lifting_property
      (LinearMap.rangeRestrict (PA.complex.d (n + 1) n).hom) targ
      (LinearMap.surjective_rangeRestrict _)
    refine ⟨hnxt, fun c => ?_⟩
    have hc := congrArg Subtype.val (LinearMap.congr_fun hhnxt c)
    change (PA.complex.d (n + 1) n).hom (hnxt c) = -(hcur ((PC.complex.d (n + 2) (n + 1)).hom c)) at hc
    rw [hc, neg_add_cancel]
  let buildAux : ∀ n : ℕ,
      Σ' (h : PC.complex.X (n + 1) →ₗ[R] PA.complex.X n),
        ∀ c : PC.complex.X (n + 2), ∃ a : PA.complex.X (n + 1),
          (PA.complex.d (n + 1) n).hom a = -(h ((PC.complex.d (n + 2) (n + 1)).hom c)) :=
    Nat.rec
      ⟨Classical.choose h_step0, fun c => by
        have h0 := Classical.choose_spec h_step0 ((PC.complex.d 2 1).hom c)
        rw [hPC_dd 0 c, map_zero, add_zero] at h0
        have he : εA (-(Classical.choose h_step0 ((PC.complex.d 2 1).hom c))) = 0 := by
          rw [map_neg, hi (h0.trans (map_zero i).symm), neg_zero]
        exact hεA_exact _ he⟩
      (fun n prev =>
        let hex := h_next n prev.1 prev.2
        ⟨Classical.choose hex, fun c => by
          have h1 := Classical.choose_spec hex ((PC.complex.d (n + 3) (n + 2)).hom c)
          rw [hPC_dd (n + 1) c, map_zero, add_zero] at h1
          have hneg : (PA.complex.d (n + 1) n).hom
              (-(Classical.choose hex ((PC.complex.d (n + 3) (n + 2)).hom c))) = 0 := by
            rw [map_neg, h1, neg_zero]
          exact hPA_exact n _ hneg⟩)
  let h (n : ℕ) : PC.complex.X (n + 1) →ₗ[R] PA.complex.X n := (buildAux n).1
  have hh0 (c : PC.complex.X 1) :
      i (εA (h 0 c)) + s0 ((PC.complex.d 1 0).hom c) = 0 :=
    Classical.choose_spec h_step0 c
  have hh_succ (n : ℕ) (c : PC.complex.X (n + 2)) :
      (PA.complex.d (n + 1) n).hom (h (n + 1) c) +
        h n ((PC.complex.d (n + 2) (n + 1)).hom c) = 0 :=
    Classical.choose_spec (h_next n (buildAux n).1 (buildAux n).2) c
  let dB (n : ℕ) : ModuleCat.of R (PA.complex.X (n + 1) × PC.complex.X (n + 1)) ⟶
      ModuleCat.of R (PA.complex.X n × PC.complex.X n) :=
    ModuleCat.ofHom
      { toFun := fun x => ((PA.complex.d (n + 1) n).hom x.1 + h n x.2, (PC.complex.d (n + 1) n).hom x.2)
        map_add' := fun x y => by
          ext
          · change (PA.complex.d (n + 1) n).hom (x.1 + y.1) + h n (x.2 + y.2) =
              ((PA.complex.d (n + 1) n).hom x.1 + h n x.2) + ((PA.complex.d (n + 1) n).hom y.1 + h n y.2)
            rw [map_add, map_add]; abel
          · exact map_add (PC.complex.d (n + 1) n).hom x.2 y.2
        map_smul' := fun r x => by
          ext
          · change (PA.complex.d (n + 1) n).hom (r • x.1) + h n (r • x.2) =
              r • ((PA.complex.d (n + 1) n).hom x.1 + h n x.2)
            rw [map_smul, map_smul, smul_add]
          · exact map_smul (PC.complex.d (n + 1) n).hom r x.2 }
  have hdB_sq (n : ℕ) : (dB (n + 1) ≫ dB n) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨a, c⟩
    ext
    · change (PA.complex.d (n + 1) n).hom ((PA.complex.d (n + 2) (n + 1)).hom a + h (n + 1) c) +
        h n ((PC.complex.d (n + 2) (n + 1)).hom c) = 0
      rw [map_add, hPA_dd n a, zero_add, hh_succ n c]
    · change (PC.complex.d (n + 1) n).hom ((PC.complex.d (n + 2) (n + 1)).hom c) = 0
      exact hPC_dd n c
  let KB : ChainComplex (ModuleCat.{0} R) ℕ :=
    ChainComplex.of (fun n => ModuleCat.of R (PA.complex.X n × PC.complex.X n)) dB hdB_sq
  let ιK : PA.complex ⟶ KB :=
    { f := fun n => ModuleCat.ofHom (LinearMap.inl R (PA.complex.X n) (PC.complex.X n))
      comm' := fun n m hnm => by
        cases hnm
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro a
        ext
        · change ((KB.d (m + 1) m).hom (a, 0)).1 = (PA.complex.d (m + 1) m).hom a
          simp [KB, ChainComplex.of_d, dB]
        · change ((KB.d (m + 1) m).hom (a, 0)).2 = 0
          simp [KB, ChainComplex.of_d, dB] }
  let πK : KB ⟶ PC.complex :=
    { f := fun n => ModuleCat.ofHom (LinearMap.snd R (PA.complex.X n) (PC.complex.X n))
      comm' := fun n m hnm => by
        cases hnm
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        rintro ⟨a, c⟩
        change (PC.complex.d (m + 1) m).hom c = ((KB.d (m + 1) m).hom (a, c)).2
        simp [KB, ChainComplex.of_d, dB] }
  have hS_zero : (ιK ≫ πK) = 0 := by
    ext n a
    rfl
  let SK : ShortComplex (ChainComplex (ModuleCat.{0} R) ℕ) := ShortComplex.mk ιK πK hS_zero
  have hKB_proj (n : ℕ) : Module.Projective R (KB.X n) := by
    let _ := hPA_proj n
    let _ := hPC_proj n
    change Module.Projective R (PA.complex.X n × PC.complex.X n)
    infer_instance
  have hps0 (c : PC.complex.X 0) : p (s0 c) = εC c := LinearMap.congr_fun hs0 c
  have hεB_surj : Function.Surjective εB := fun b => by
    obtain ⟨c, hc⟩ := hεC_surj (p b)
    have hker : b - s0 c ∈ LinearMap.ker p := by
      rw [LinearMap.mem_ker, map_sub, hps0 c, hc, sub_self]
    rw [← hip] at hker
    obtain ⟨a0, ha0⟩ := hker
    obtain ⟨a, rfl⟩ := hεA_surj a0
    refine ⟨(a, c), ?_⟩
    change i (εA a) + s0 c = b
    rw [ha0, sub_add_cancel]
  have hεB_comp (x : KB.X 1) : εB ((KB.d 1 0).hom x) = 0 := by
    rcases x with ⟨a, c⟩
    change i (εA ((PA.complex.d 1 0).hom a + h 0 c)) + s0 ((PC.complex.d 1 0).hom c) = 0
    rw [map_add, map_add, hεA_comp a, map_zero, zero_add, hh0 c]
  have hεB_exact (x : KB.X 0) (hx : εB x = 0) : ∃ y : KB.X 1, (KB.d 1 0).hom y = x := by
    rcases x with ⟨a, c⟩
    change i (εA a) + s0 c = 0 at hx
    have hpc : εC c = 0 := by
      have hp0 := congrArg p hx
      rw [map_add, map_zero, hps0 c] at hp0
      have hi0 : p (i (εA a)) = 0 := by
        rw [← LinearMap.mem_ker, ← hip]; exact ⟨εA a, rfl⟩
      rw [hi0, zero_add] at hp0
      exact hp0
    obtain ⟨c1, hc1⟩ := hεC_exact c hpc
    have ha_ker : εA (a - h 0 c1) = 0 := by
      apply hi
      rw [map_zero, map_sub, map_sub]
      have h1 := hh0 c1
      rw [hc1] at h1
      have hia : i (εA a) = - s0 c := eq_neg_of_add_eq_zero_left hx
      have hih : i (εA (h 0 c1)) = - s0 c := eq_neg_of_add_eq_zero_left h1
      rw [hia, hih, sub_self]
    obtain ⟨a1, ha1⟩ := hεA_exact _ ha_ker
    refine ⟨(a1, c1), ?_⟩
    change ((PA.complex.d 1 0).hom a1 + h 0 c1, (PC.complex.d 1 0).hom c1) = (a, c)
    ext
    · rw [ha1, sub_add_cancel]
    · exact hc1
  have hKB_exact (n : ℕ) (x : KB.X (n + 1)) (hx : (KB.d (n + 1) n).hom x = 0) :
      ∃ y : KB.X (n + 2), (KB.d (n + 2) (n + 1)).hom y = x := by
    rcases x with ⟨a, c⟩
    have hx' : ((PA.complex.d (n + 1) n).hom a + h n c, (PC.complex.d (n + 1) n).hom c) = (0, 0) := by
      simpa [KB, ChainComplex.of_d, dB] using hx
    have hx1 : (PA.complex.d (n + 1) n).hom a + h n c = 0 := congrArg Prod.fst hx'
    have hx2 : (PC.complex.d (n + 1) n).hom c = 0 := congrArg Prod.snd hx'
    obtain ⟨c1, hc1⟩ := hPC_exact n c hx2
    have ha_ker : (PA.complex.d (n + 1) n).hom (a - h (n + 1) c1) = 0 := by
      rw [map_sub]
      have h1 := hh_succ n c1
      rw [hc1] at h1
      have h2 : (PA.complex.d (n + 1) n).hom a = - h n c := eq_neg_of_add_eq_zero_left hx1
      have h3 : (PA.complex.d (n + 1) n).hom (h (n + 1) c1) = - h n c := eq_neg_of_add_eq_zero_left h1
      rw [h2, h3, sub_self]
    obtain ⟨a1, ha1⟩ := hPA_exact n _ ha_ker
    refine ⟨(a1, c1), ?_⟩
    have hd_eq : (KB.d (n + 2) (n + 1)).hom (a1, c1) =
        ((PA.complex.d (n + 2) (n + 1)).hom a1 + h (n + 1) c1,
          (PC.complex.d (n + 2) (n + 1)).hom c1) :=
      congrArg (fun φ : KB.X (n + 2) ⟶ KB.X (n + 1) => φ.hom (a1, c1))
        (ChainComplex.of_d _ dB (n + 1))
    rw [hd_eq]
    ext
    · rw [ha1, sub_add_cancel]
    · exact hc1
  let PB : ProjectiveResolution (ModuleCat.of R B) :=
    projectiveResolutionOfExact B KB hKB_proj εB hεB_surj hεB_comp hεB_exact hKB_exact
  have hcomm_i : (ιK.f 0 ≫ PB.π.f 0) = (PA.π.f 0 ≫ ModuleCat.ofHom i) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change εB (a, 0) = i (εA a)
    simp [εB]
  have hcomm_p : (πK.f 0 ≫ PC.π.f 0) = (PB.π.f 0 ≫ ModuleCat.ofHom p) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨a, c⟩
    change εC c = p (εB (a, c))
    simp only [εB, LinearMap.coprod_apply, map_add, LinearMap.comp_apply]
    have hi0 : p (i (εA a)) = 0 := by
      rw [← LinearMap.mem_ker, ← hip]; exact ⟨εA a, rfl⟩
    rw [hi0, zero_add, hps0 c]
  let F := (tensoringLeft (ModuleCat.{0} R)).obj (ModuleCat.of R M)
  let SM : ShortComplex (ChainComplex (ModuleCat.{0} R) ℕ) :=
    SK.map (F.mapHomologicalComplex (ComplexShape.down ℕ))
  have hSM_exact : SM.ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro n
    let split_n : (SK.map (HomologicalComplex.eval _ _ n)).Splitting :=
      { r := ModuleCat.ofHom (LinearMap.fst R (PA.complex.X n) (PC.complex.X n))
        s := ModuleCat.ofHom (LinearMap.inr R (PA.complex.X n) (PC.complex.X n))
        f_r := by apply ModuleCat.hom_ext; apply LinearMap.ext; intro a; rfl
        s_g := by apply ModuleCat.hom_ext; apply LinearMap.ext; intro c; rfl
        id := by
          apply ModuleCat.hom_ext; apply LinearMap.ext; rintro ⟨a, c⟩
          change (a, 0) + (0, c) = (a, c)
          ext <;> simp }
    let split_Mn : (SM.map (HomologicalComplex.eval _ _ n)).Splitting :=
      split_n.map F
    exact split_Mn.shortExact
  let eA (n : ℕ) : torMod R M A n ≅ SM.X₁.homology n := PA.isoLeftDerivedObj F n
  let eB (n : ℕ) : torMod R M B n ≅ SM.X₂.homology n := PB.isoLeftDerivedObj F n
  let eC (n : ℕ) : torMod R M C n ≅ SM.X₃.homology n := PC.isoLeftDerivedObj F n
  let δ (n : ℕ) : torMod R M C (n + 1) →ₗ[R] torMod R M A n :=
    ((eC (n + 1)).hom ≫ hSM_exact.δ (n + 1) n rfl ≫ (eA n).inv).hom
  have htor_i_hom (n : ℕ) (x : torMod R M A n) :
      (eB n).hom.hom (torMap M i n x) = (HomologicalComplex.homologyMap SM.f n).hom ((eA n).hom.hom x) :=
    congrArg (fun φ : torMod R M A n ⟶ SM.X₂.homology n => φ.hom x)
      (ProjectiveResolution.isoLeftDerivedObj_hom_naturality (ModuleCat.ofHom i) PA PB ιK hcomm_i F n)
  have htor_p_hom (n : ℕ) (x : torMod R M B n) :
      (eC n).hom.hom (torMap M p n x) = (HomologicalComplex.homologyMap SM.g n).hom ((eB n).hom.hom x) :=
    congrArg (fun φ : torMod R M B n ⟶ SM.X₃.homology n => φ.hom x)
      (ProjectiveResolution.isoLeftDerivedObj_hom_naturality (ModuleCat.ofHom p) PB PC πK hcomm_p F n)
  have iso_hom_inv {X Y : ModuleCat.{0} R} (e : X ≅ Y) (y : Y) :
      e.hom.hom (e.inv.hom y) = y :=
    congrArg (fun φ : Y ⟶ Y => φ.hom y) e.inv_hom_id
  have iso_inv_hom {X Y : ModuleCat.{0} R} (e : X ≅ Y) (x : X) :
      e.inv.hom (e.hom.hom x) = x :=
    congrArg (fun φ : X ⟶ X => φ.hom x) e.hom_inv_id
  refine ⟨δ, ?_, ?_, ?_⟩
  · intro n x
    have hex := (ShortComplex.moduleCat_exact_iff _).mp (hSM_exact.homology_exact₁ (n + 1) n rfl)
    have h1 : torMap M i n x = 0 ↔
        (HomologicalComplex.homologyMap SM.f n).hom ((eA n).hom.hom x) = 0 := by
      rw [← htor_i_hom n x]
      exact (eB n).toLinearEquiv.map_eq_zero_iff.symm
    rw [h1]
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := hex ((eA n).hom.hom x) hx
      refine ⟨(eC (n + 1)).inv.hom y, ?_⟩
      change (eA n).inv.hom ((hSM_exact.δ (n + 1) n rfl).hom ((eC (n + 1)).hom.hom ((eC (n + 1)).inv.hom y))) = x
      rw [iso_hom_inv (eC (n + 1)) y, hy]
      exact iso_inv_hom (eA n) x
    · rintro ⟨z, rfl⟩
      have hcomp := congrArg (fun φ : SM.X₃.homology (n + 1) ⟶ SM.X₂.homology n =>
        φ.hom ((eC (n + 1)).hom.hom z)) (hSM_exact.δ_comp (n + 1) n rfl)
      change (HomologicalComplex.homologyMap SM.f n).hom
        ((eA n).hom.hom ((eA n).inv.hom ((hSM_exact.δ (n + 1) n rfl).hom ((eC (n + 1)).hom.hom z)))) = 0
      rw [iso_hom_inv (eA n)]
      exact hcomp
  · intro n x
    have hex := (ShortComplex.moduleCat_exact_iff _).mp (hSM_exact.homology_exact₂ n)
    have h1 : torMap M p n x = 0 ↔
        (HomologicalComplex.homologyMap SM.g n).hom ((eB n).hom.hom x) = 0 := by
      rw [← htor_p_hom n x]
      exact (eC n).toLinearEquiv.map_eq_zero_iff.symm
    rw [h1]
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := hex ((eB n).hom.hom x) hx
      refine ⟨(eA n).inv.hom y, ?_⟩
      apply (eB n).toLinearEquiv.injective
      change (eB n).hom.hom (torMap M i n ((eA n).inv.hom y)) = (eB n).hom.hom x
      rw [htor_i_hom n, iso_hom_inv (eA n) y, hy]
    · rintro ⟨z, rfl⟩
      rw [htor_i_hom n]
      have hzero : (HomologicalComplex.homologyMap SM.f n ≫ HomologicalComplex.homologyMap SM.g n) = 0 := by
        rw [← HomologicalComplex.homologyMap_comp, SM.zero, HomologicalComplex.homologyMap_zero]
      exact congrArg (fun φ : SM.X₁.homology n ⟶ SM.X₃.homology n => φ.hom ((eA n).hom.hom z)) hzero
  · intro n x
    have hex := (ShortComplex.moduleCat_exact_iff _).mp (hSM_exact.homology_exact₃ (n + 1) n rfl)
    have h1 : δ n x = 0 ↔
        (hSM_exact.δ (n + 1) n rfl).hom ((eC (n + 1)).hom.hom x) = 0 := by
      change (eA n).inv.hom ((hSM_exact.δ (n + 1) n rfl).hom ((eC (n + 1)).hom.hom x)) = 0 ↔ _
      exact (eA n).toLinearEquiv.symm.map_eq_zero_iff
    rw [h1]
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := hex ((eC (n + 1)).hom.hom x) hx
      refine ⟨(eB (n + 1)).inv.hom y, ?_⟩
      apply (eC (n + 1)).toLinearEquiv.injective
      change (eC (n + 1)).hom.hom (torMap M p (n + 1) ((eB (n + 1)).inv.hom y)) = (eC (n + 1)).hom.hom x
      rw [htor_p_hom (n + 1), iso_hom_inv (eB (n + 1)) y, hy]
    · rintro ⟨z, rfl⟩
      rw [htor_p_hom (n + 1)]
      exact congrArg (fun φ : SM.X₂.homology (n + 1) ⟶ SM.X₁.homology n =>
        φ.hom ((eB (n + 1)).hom.hom z)) (hSM_exact.comp_δ (n + 1) n rfl)
lemma tor_subsingleton_of_hasFiniteProjRes {R : Type} [CommRing R]
    (M : Type) [AddCommGroup M] [Module R M] :
    ∀ (d : ℕ) (N : Type) [AddCommGroup N] [Module R N],
      HasFiniteProjRes R d N → ∀ i : ℕ, d < i → Subsingleton (torMod R M N i) := by
  intro d
  induction d with
  | zero =>
    intro N _ _ hres i hi
    obtain ⟨_, hproj⟩ := hres
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    exact tor_succ_subsingleton_of_projective M N k
  | succ m ih =>
    intro N _ _ hres i hi
    obtain ⟨P, _, _, _, hprojP, f, hf, hK⟩ := hres
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    obtain ⟨δ, hδ_ex, _, hp_ex⟩ := horseshoe_tor_les M (LinearMap.ker f).subtype f
      (LinearMap.ker f).injective_subtype hf (by simp)
    have hK_sub : Subsingleton (torMod R M (LinearMap.ker f) k) := ih _ hK k (by omega)
    have hP_sub : Subsingleton (torMod R M P (k + 1)) := tor_succ_subsingleton_of_projective M P k
    refine ⟨fun x y => ?_⟩
    have h0 : δ k (x - y) = 0 := Subsingleton.elim _ _
    obtain ⟨z, hz⟩ := (hp_ex k (x - y)).mp h0
    have hz0 : z = 0 := Subsingleton.elim _ _
    rw [hz0, map_zero] at hz
    exact sub_eq_zero.mp hz.symm
lemma module_finite_tensor_of_finite {R : Type} [CommRing R]
    (M N : Type) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] :
    Module.Finite R (M ⊗[R] N) := by
  obtain ⟨r, g, hg⟩ := exists_finite_free_surj (R := R) N
  have hsurj : Function.Surjective (LinearMap.lTensor M g) :=
    LinearMap.lTensor_surjective M hg
  let φ : (Fin r → M) →ₗ[R] (M ⊗[R] (Fin r → R)) :=
    { toFun := fun u => ∑ j : Fin r, u j ⊗ₜ[R] Pi.single j (1 : R)
      map_add' := fun u v => by simp [TensorProduct.add_tmul, Finset.sum_add_distrib]
      map_smul' := fun c u => by
        simp only [Pi.smul_apply, Finset.smul_sum, RingHom.id_apply]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [TensorProduct.smul_tmul'] }
  have hφ_surj : Function.Surjective φ := fun t => by
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp [φ]⟩
    | tmul m v =>
      refine ⟨fun j => v j • m, ?_⟩
      simp only [φ, LinearMap.coe_mk, AddHom.coe_mk]
      have hv : v = ∑ j : Fin r, v j • Pi.single j (1 : R) := by
        ext k; simp [Finset.sum_apply, Pi.single_apply]
      conv_rhs => rw [hv, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [TensorProduct.smul_tmul]
    | add t₁ t₂ ih₁ ih₂ =>
      obtain ⟨u₁, hu₁⟩ := ih₁
      obtain ⟨u₂, hu₂⟩ := ih₂
      exact ⟨u₁ + u₂, by rw [map_add, hu₁, hu₂]⟩
  exact Module.Finite.of_surjective ((LinearMap.lTensor M g).comp φ) (hsurj.comp hφ_surj)
lemma tor_finite_of_hasFiniteProjRes {R : Type} [CommRing R] [IsNoetherianRing R]
    (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∀ (d : ℕ) (N : Type) [AddCommGroup N] [Module R N],
      HasFiniteProjRes R d N → ∀ i : ℕ, Module.Finite R (torMod R M N i) := by
  intro d
  induction d with
  | zero =>
    intro N _ _ hres i
    obtain ⟨hfin, hproj⟩ := hres
    cases i with
    | zero =>
      let _ : Module.Finite R (M ⊗[R] N) := module_finite_tensor_of_finite M N
      exact Module.Finite.equiv (torZeroEquiv R M N).symm
    | succ k =>
      have _ : Subsingleton (torMod R M N (k + 1)) := tor_succ_subsingleton_of_projective M N k
      exact ⟨⟨∅, Submodule.eq_top_iff'.mpr fun (x : torMod R M N (k + 1)) => by
        rw [Subsingleton.elim x 0]; exact zero_mem _⟩⟩
  | succ m ih =>
    intro N _ _ hres i
    obtain ⟨P, _, _, hfinP, hprojP, f, hf, hK⟩ := hres
    cases i with
    | zero =>
      let _ : Module.Finite R N := Module.Finite.of_surjective f hf
      let _ : Module.Finite R (M ⊗[R] N) := module_finite_tensor_of_finite M N
      exact Module.Finite.equiv (torZeroEquiv R M N).symm
    | succ k =>
      obtain ⟨δ, _, _, hp_ex⟩ := horseshoe_tor_les M (LinearMap.ker f).subtype f
        (LinearMap.ker f).injective_subtype hf (by simp)
      have _ : Subsingleton (torMod R M P (k + 1)) := tor_succ_subsingleton_of_projective M P k
      have hδ_inj : Function.Injective (δ k) := by
        rw [injective_iff_map_eq_zero]
        intro x hx
        obtain ⟨z, hz⟩ := (hp_ex k x).mp hx
        rw [Subsingleton.elim z 0, map_zero] at hz
        exact hz.symm
      have _ : Module.Finite R (torMod R M (LinearMap.ker f) k) := ih _ hK k
      let _ : IsNoetherian R (torMod R M (LinearMap.ker f) k) :=
        isNoetherian_of_isNoetherianRing_of_finite R _
      let e : torMod R M N (k + 1) ≃ₗ[R] LinearMap.range (δ k) :=
        LinearEquiv.ofInjective (δ k) hδ_inj
      let _ : Module.Finite R (LinearMap.range (δ k)) :=
        Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
      exact Module.Finite.equiv e.symm
lemma tor_smul_eq_zero_left {R : Type} [CommRing R]
    (M N : Type) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {a : R} (ha : ∀ m : M, a • m = 0) (i : ℕ) (x : torMod R M N i) : a • x = 0 := by
  let PN := projectiveResolution (ModuleCat.of R N)
  let F := (tensoringLeft (ModuleCat.{0} R)).obj (ModuleCat.of R M)
  let e : torMod R M N i ≅ ((F.mapHomologicalComplex _).obj PN.complex).homology i :=
    PN.isoLeftDerivedObj F i
  have hx' : e.hom.hom (a • x) = 0 := by
    rw [map_smul]
    let K := (F.mapHomologicalComplex _).obj PN.complex
    have hsurj : Function.Surjective (K.homologyπ i) :=
      (ModuleCat.epi_iff_surjective (K.homologyπ i)).mp inferInstance
    obtain ⟨c, hc⟩ := hsurj (e.hom.hom x)
    rw [← hc, ← map_smul]
    have hc0 : a • c = 0 := by
      apply (ModuleCat.mono_iff_injective (K.iCycles i)).mp inferInstance
      rw [map_smul, map_zero]
      have ht0 : ∀ t : M ⊗[R] PN.complex.X i, a • t = 0 := fun t => by
        induction t using TensorProduct.induction_on with
        | zero => simp
        | tmul m p => rw [TensorProduct.smul_tmul', ha m, TensorProduct.zero_tmul]
        | add t₁ t₂ ih₁ ih₂ => rw [smul_add, ih₁, ih₂, add_zero]
      exact ht0 ((K.iCycles i).hom c)
    rw [hc0, map_zero]
  exact e.toLinearEquiv.injective (hx'.trans (map_zero _).symm)
lemma tor_smul_eq_zero_right {R : Type} [CommRing R]
    (M N : Type) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {b : R} (hb : ∀ n : N, b • n = 0) (i : ℕ) (x : torMod R M N i) : b • x = 0 := by
  let PN := projectiveResolution (ModuleCat.of R N)
  let F := (tensoringLeft (ModuleCat.{0} R)).obj (ModuleCat.of R M)
  let e : torMod R M N i ≅ ((F.mapHomologicalComplex _).obj PN.complex).homology i :=
    PN.isoLeftDerivedObj F i
  let multN : ModuleCat.of R N ⟶ ModuleCat.of R N :=
    ModuleCat.ofHom (b • LinearMap.id)
  have hmultN_zero : multN = 0 := by
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro n; exact hb n
  let multP : PN.complex ⟶ PN.complex :=
    { f := fun k => ModuleCat.ofHom (b • LinearMap.id)
      comm' := fun k l _ => by
        apply ModuleCat.hom_ext; apply LinearMap.ext; intro y
        change (PN.complex.d k l).hom (b • y) = b • (PN.complex.d k l).hom y
        exact map_smul _ b y }
  have hcomm : (multP.f 0 ≫ PN.π.f 0) = (PN.π.f 0 ≫ multN) := by
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro y
    change (PN.π.f 0).hom (b • y) = b • (PN.π.f 0).hom y
    exact map_smul _ b y
  have hnat := ProjectiveResolution.isoLeftDerivedObj_hom_naturality multN PN PN multP hcomm F i
  have hmap0 : (F.leftDerived i).map multN = 0 := by
    rw [hmultN_zero]
    rw [Functor.leftDerived_map_eq F i (0 : ModuleCat.of R N ⟶ ModuleCat.of R N) (P := PN) (Q := PN) 0
      (by simp)]
    simp only [Functor.map_zero, Limits.comp_zero, Limits.zero_comp]
  rw [hmap0, Limits.zero_comp] at hnat
  have hFmult : ((F.mapHomologicalComplex _).map multP) =
      { f := fun k => ModuleCat.ofHom (b • LinearMap.id)
        comm' := fun k l _ => by
          apply ModuleCat.hom_ext; apply LinearMap.ext; intro t
          change (((F.mapHomologicalComplex _).obj PN.complex).d k l).hom (b • t) =
            b • (((F.mapHomologicalComplex _).obj PN.complex).d k l).hom t
          exact map_smul _ b t } := by
    apply HomologicalComplex.hom_ext
    intro k
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro m p
    change m ⊗ₜ[R] (b • p) = b • (m ⊗ₜ[R] p)
    exact TensorProduct.tmul_smul b m p
  have hHmult (y : ((F.mapHomologicalComplex _).obj PN.complex).homology i) :
      (HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map multP) i).hom y = b • y := by
    let K := (F.mapHomologicalComplex _).obj PN.complex
    have hsurj : Function.Surjective (K.homologyπ i) :=
      (ModuleCat.epi_iff_surjective (K.homologyπ i)).mp inferInstance
    obtain ⟨c, rfl⟩ := hsurj y
    have h1 : (HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map multP) i).hom
        ((K.homologyπ i).hom c) =
        (K.homologyπ i).hom ((ShortComplex.cyclesMap
          ((HomologicalComplex.shortComplexFunctor _ _ i).map
            ((F.mapHomologicalComplex _).map multP))).hom c) :=
      congrArg (fun φ : K.cycles i ⟶ K.homology i => φ.hom c)
        (ShortComplex.homologyπ_naturality ((HomologicalComplex.shortComplexFunctor _ _ i).map
          ((F.mapHomologicalComplex _).map multP)))
    rw [h1, ← map_smul]
    congr 1
    apply (ModuleCat.mono_iff_injective (K.iCycles i)).mp inferInstance
    have h2 : (K.iCycles i).hom ((ShortComplex.cyclesMap
        ((HomologicalComplex.shortComplexFunctor _ _ i).map
          ((F.mapHomologicalComplex _).map multP))).hom c) =
        (((F.mapHomologicalComplex _).map multP).f i).hom ((K.iCycles i).hom c) :=
      congrArg (fun φ : K.cycles i ⟶ K.X i => φ.hom c)
        (ShortComplex.cyclesMap_i ((HomologicalComplex.shortComplexFunctor _ _ i).map
          ((F.mapHomologicalComplex _).map multP)))
    rw [h2, map_smul, hFmult]
    rfl
  have hx' : e.hom.hom (b • x) = 0 := by
    rw [map_smul, ← hHmult (e.hom.hom x)]
    have h0 := congrArg (fun φ : torMod R M N i ⟶ _ => φ.hom x) hnat
    exact h0.symm
  exact e.toLinearEquiv.injective (hx'.trans (map_zero _).symm)
lemma length_ne_top_of_annihilated_radical_eq_maximalIdeal
    {S : Type} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    {I : Ideal S} (hI : I.radical = maximalIdeal S)
    {X : Type} [AddCommGroup X] [Module S X] [Module.Finite S X]
    (hann : ∀ a ∈ I, ∀ x : X, a • x = 0) :
    Module.length S X ≠ ⊤ := by
  have hI_le : I ≤ maximalIdeal S := hI ▸ Ideal.le_radical
  have hI_ne : I ≠ ⊤ := fun h => (maximalIdeal.isMaximal S).ne_top (top_unique (h ▸ hI_le))
  let _ : Nontrivial (S ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI_ne
  have hkd0 : Ring.KrullDimLE 0 (S ⧸ I) := by
    rw [Ring.krullDimLE_zero_iff]
    intro p hp
    let q := p.comap (Ideal.Quotient.mk I)
    have hq_prime : q.IsPrime := Ideal.IsPrime.comap (Ideal.Quotient.mk I)
    have hIq : I ≤ q := by
      intro a ha
      change Ideal.Quotient.mk I a ∈ p
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
      exact zero_mem p
    have hm_le_q : maximalIdeal S ≤ q := by
      rw [← hI]
      exact hq_prime.radical_le_iff.mpr hIq
    have hq_eq : q = maximalIdeal S :=
      le_antisymm (IsLocalRing.le_maximalIdeal hq_prime.ne_top) hm_le_q
    have hq_max : q.IsMaximal := hq_eq ▸ maximalIdeal.isMaximal S
    rw [Ideal.isMaximal_iff]
    refine ⟨fun h1 => hp.ne_top (Ideal.eq_top_of_isUnit_mem p h1 isUnit_one), fun J x hJp hxp hxJ => ?_⟩
    have hqJ : q ≤ J.comap (Ideal.Quotient.mk I) := fun a ha => hJp ha
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hyq : y ∉ q := hxp
    have hyJ : y ∈ J.comap (Ideal.Quotient.mk I) := hxJ
    have hJ_top : J.comap (Ideal.Quotient.mk I) = ⊤ := by
      by_contra hne
      exact hyq (hq_max.eq_of_le hne hqJ ▸ hyJ)
    have h1 : (1 : S) ∈ J.comap (Ideal.Quotient.mk I) := hJ_top ▸ Submodule.mem_top
    exact h1
  let _ : IsArtinianRing (S ⧸ I) := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  let _ : Module (S ⧸ I) X :=
    Module.compHom X (Ideal.Quotient.lift I (Module.toAddMonoidEnd S X)
      (fun a ha => AddMonoidHom.ext fun x => hann a ha x))
  have hst : IsScalarTower S (S ⧸ I) X :=
    ⟨fun s c x => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
      change (s * a) • x = s • (a • x)
      exact mul_smul s a x⟩
  let _ : Module.Finite (S ⧸ I) X := Module.Finite.of_restrictScalars_finite S (S ⧸ I) X
  let _ : IsNoetherian (S ⧸ I) X := isNoetherian_of_isNoetherianRing_of_finite (S ⧸ I) X
  let _ : IsArtinian (S ⧸ I) X := by
    obtain ⟨r, g, hg⟩ := exists_finite_free_surj (R := S ⧸ I) X
    exact isArtinian_of_surjective (Fin r → S ⧸ I) g hg
  rw [Module.length_eq_of_surjective (S := S) (R := S ⧸ I) (M := X) Ideal.Quotient.mk_surjective]
  exact Module.length_ne_top
end TorLES
section ChangeOfRings
lemma length_nat_add_of_exact {R : Type} [CommRing R]
    {A B C : Type} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hex : Function.Exact f g)
    (hA : Module.length R A ≠ ⊤) (hC : Module.length R C ≠ ⊤) :
    Module.length R B ≠ ⊤ ∧
      (Module.length R B).toNat = (Module.length R A).toNat + (Module.length R C).toNat := by
  have heq := Module.length_eq_add_of_exact f g hf hg hex
  rw [← ENat.natCast_toNat hA, ← ENat.natCast_toNat hC, ← Nat.cast_add] at heq
  rw [heq]
  exact ⟨ENat.natCast_ne_top _, ENat.toNat_natCast _⟩
lemma length_nat_of_exact_middle {R : Type} [CommRing R]
    {A B C : Type} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hex : Function.Exact f g)
    (hA : Module.length R A ≠ ⊤) (hC : Module.length R C ≠ ⊤) :
    Module.length R B ≠ ⊤ ∧
      Module.length R (LinearMap.range f) ≠ ⊤ ∧
      Module.length R (LinearMap.range g) ≠ ⊤ ∧
      (Module.length R B).toNat =
        (Module.length R (LinearMap.range f)).toNat +
          (Module.length R (LinearMap.range g)).toNat := by
  have hrf_le : Module.length R (LinearMap.range f) ≤ Module.length R A :=
    Module.length_le_of_surjective f.rangeRestrict f.surjective_rangeRestrict
  have hrf_fin : Module.length R (LinearMap.range f) ≠ ⊤ :=
    ne_top_of_le_ne_top hA hrf_le
  have hrg_le : Module.length R (LinearMap.range g) ≤ Module.length R C :=
    Module.length_le_of_injective (LinearMap.range g).subtype (Submodule.subtype_injective _)
  have hrg_fin : Module.length R (LinearMap.range g) ≠ ⊤ :=
    ne_top_of_le_ne_top hC hrg_le
  have hker_eq : LinearMap.ker g = LinearMap.range f := LinearMap.exact_iff.mp hex
  have hkeq : Module.length R (LinearMap.ker g) = Module.length R (LinearMap.range f) :=
    (LinearEquiv.ofEq _ _ hker_eq).length_eq
  have hker_fin : Module.length R (LinearMap.ker g) ≠ ⊤ := hkeq ▸ hrf_fin
  have hB := length_nat_add_of_exact (LinearMap.ker g).subtype g.rangeRestrict
    (Submodule.subtype_injective _) g.surjective_rangeRestrict
    (fun b => by
      constructor
      · intro hb
        have hb0 : g b = 0 := congrArg Subtype.val hb
        exact ⟨⟨b, hb0⟩, rfl⟩
      · rintro ⟨⟨b, hb⟩, rfl⟩
        exact Subtype.ext hb)
    hker_fin hrg_fin
  refine ⟨hB.1, hrf_fin, hrg_fin, ?_⟩
  rw [hB.2, hkeq]
lemma length_ker_coker_comp {R : Type} [CommRing R]
    {A B C : Type} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    (α : A →ₗ[R] B) (β : B →ₗ[R] C)
    (hka : Module.length R (LinearMap.ker α) ≠ ⊤)
    (hkb : Module.length R (LinearMap.ker β) ≠ ⊤)
    (hca : Module.length R (B ⧸ LinearMap.range α) ≠ ⊤) :
    let J : Submodule R (LinearMap.range β) :=
      (LinearMap.range (β.comp α)).comap (LinearMap.range β).subtype
    Module.length R (LinearMap.ker (β.comp α)) ≠ ⊤ ∧
    Module.length R (LinearMap.range β ⧸ J) ≠ ⊤ ∧
    (Module.length R (LinearMap.ker (β.comp α))).toNat +
        (Module.length R (B ⧸ LinearMap.range α)).toNat =
      (Module.length R (LinearMap.ker α)).toNat +
        (Module.length R (LinearMap.ker β)).toNat +
        (Module.length R (LinearMap.range β ⧸ J)).toNat := by
  intro J
  let K : Submodule R B := LinearMap.ker β
  let I : Submodule R B := LinearMap.range α
  let IK : Submodule R K := I.comap K.subtype
  have hIK_fin : Module.length R IK ≠ ⊤ :=
    ne_top_of_le_ne_top hkb (Module.length_le_of_injective IK.subtype (Submodule.subtype_injective _))
  have hK_quot_fin : Module.length R (K ⧸ IK) ≠ ⊤ :=
    ne_top_of_le_ne_top hkb (Module.length_le_of_surjective IK.mkQ (Submodule.mkQ_surjective _))
  have hK_split := length_nat_add_of_exact IK.subtype IK.mkQ
    (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)
    (LinearMap.exact_subtype_mkQ IK) hIK_fin hK_quot_fin
  let incl : LinearMap.ker α →ₗ[R] LinearMap.ker (β.comp α) :=
    LinearMap.codRestrict (LinearMap.ker (β.comp α)) (LinearMap.ker α).subtype (fun x => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.coe_subtype,
        LinearMap.mem_ker.mp x.2, map_zero])
  let proj : LinearMap.ker (β.comp α) →ₗ[R] IK :=
    LinearMap.codRestrict IK
      (LinearMap.codRestrict K (α.comp (LinearMap.ker (β.comp α)).subtype) (fun x => x.2))
      (fun x => ⟨x.1, rfl⟩)
  have hincl_inj : Function.Injective incl := fun x y h =>
    Subtype.ext (congrArg (fun u : LinearMap.ker (β.comp α) => u.1) h)
  have hproj_surj : Function.Surjective proj := by
    rintro ⟨⟨b, hbK⟩, ⟨a, ha⟩⟩
    have ha_ker : a ∈ LinearMap.ker (β.comp α) := by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, ha]
      exact hbK
    refine ⟨⟨a, ha_ker⟩, ?_⟩
    apply Subtype.ext; apply Subtype.ext; exact ha
  have hexA : Function.Exact incl proj := fun x => by
    constructor
    · intro hx
      have h0 : α x.1 = 0 := congrArg (fun u => u.1.1) hx
      exact ⟨⟨x.1, h0⟩, rfl⟩
    · rintro ⟨⟨a, ha⟩, rfl⟩
      apply Subtype.ext; apply Subtype.ext; exact ha
  have hA_split := length_nat_add_of_exact incl proj hincl_inj hproj_surj hexA hka hIK_fin
  let φ : (B ⧸ I) →ₗ[R] (LinearMap.range β ⧸ J) :=
    I.liftQ (J.mkQ.comp β.rangeRestrict) (by
      rintro b ⟨a, rfl⟩
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      exact ⟨a, rfl⟩)
  have hφ_surj : Function.Surjective φ := by
    intro y
    obtain ⟨⟨c, ⟨b, rfl⟩⟩, rfl⟩ := Submodule.Quotient.mk_surjective J y
    exact ⟨Submodule.Quotient.mk b, rfl⟩
  have hqJ_fin : Module.length R (LinearMap.range β ⧸ J) ≠ ⊤ :=
    ne_top_of_le_ne_top hca (Module.length_le_of_surjective φ hφ_surj)
  let ψ : (K ⧸ IK) →ₗ[R] (B ⧸ I) :=
    IK.liftQ (I.mkQ.comp K.subtype) (fun k hk => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.coe_subtype, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      exact hk)
  have hψ_inj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro u hu
    obtain ⟨k, rfl⟩ := Submodule.Quotient.mk_surjective IK u
    rw [Submodule.Quotient.mk_eq_zero]
    exact (Submodule.Quotient.mk_eq_zero I).mp hu
  have hexB : Function.Exact ψ φ := by
    intro u
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective I u
    constructor
    · intro hu
      have hmem : β.rangeRestrict b ∈ J := (Submodule.Quotient.mk_eq_zero J).mp hu
      obtain ⟨a, ha⟩ := hmem
      have hk : b - α a ∈ K := by
        rw [LinearMap.mem_ker, map_sub]
        exact sub_eq_zero.mpr ha.symm
      refine ⟨Submodule.Quotient.mk ⟨b - α a, hk⟩, ?_⟩
      change Submodule.Quotient.mk (b - α a) = Submodule.Quotient.mk b
      rw [Submodule.Quotient.eq]
      have : (b - α a) - b = -(α a) := by abel
      rw [this]
      exact neg_mem ⟨a, rfl⟩
    · rintro ⟨v, hv⟩
      obtain ⟨k, rfl⟩ := Submodule.Quotient.mk_surjective IK v
      rw [← hv]
      change Submodule.Quotient.mk (β.rangeRestrict k.1) = 0
      have hk0 : β.rangeRestrict k.1 = 0 := Subtype.ext k.2
      rw [hk0]
      rfl
  have hB_split := length_nat_add_of_exact ψ φ hψ_inj hφ_surj hexB hK_quot_fin hqJ_fin
  refine ⟨hA_split.1, hqJ_fin, ?_⟩
  dsimp only [K, I] at hK_split hA_split hB_split
  omega
noncomputable def liftBaseChange {S R X A : Type} [CommRing S] [CommRing R] [Algebra S R]
    [AddCommGroup X] [Module S X] [AddCommMonoid A] [Module S A] [Module R A] [IsScalarTower S R A]
    (f : X →ₗ[S] A) : (R ⊗[S] X) →ₗ[R] A :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun r =>
        { toFun := fun x => r • f x
          map_add' := fun x y => by rw [map_add, smul_add]
          map_smul' := fun s x => by
            change r • f (s • x) = s • (r • f x)
            rw [map_smul, smul_comm] }
      map_add' := fun r₁ r₂ => by ext x; exact add_smul r₁ r₂ (f x)
      map_smul' := fun c r => by ext x; exact mul_smul c r (f x) }
lemma projective_baseChange {S R X : Type} [CommRing S] [CommRing R] [Algebra S R]
    [AddCommGroup X] [Module S X] [Module.Projective S X] :
    Module.Projective R (R ⊗[S] X) := by
  refine Module.Projective.of_lifting_property' fun {A B} _ _ _ _ f g hf => ?_
  let _ : Module S A := Module.compHom A (algebraMap S R)
  let _ : Module S B := Module.compHom B (algebraMap S R)
  have _ : IsScalarTower S R A := ⟨fun s r a => by
    rw [Algebra.smul_def, mul_smul]; rfl⟩
  have _ : IsScalarTower S R B := ⟨fun s r b => by
    rw [Algebra.smul_def, mul_smul]; rfl⟩
  let gS : X →ₗ[S] B :=
    { toFun := fun x => g (1 ⊗ₜ[S] x)
      map_add' := fun x y => by rw [TensorProduct.tmul_add, map_add]
      map_smul' := fun s x => by
        change g (1 ⊗ₜ[S] (s • x)) = algebraMap S R s • g (1 ⊗ₜ[S] x)
        rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one,
          ← mul_one (algebraMap S R s), ← smul_eq_mul, ← TensorProduct.smul_tmul', map_smul,
          smul_eq_mul, mul_one] }
  obtain ⟨hS, hhS⟩ := Module.projective_lifting_property (f.restrictScalars S) gS hf
  let h : (R ⊗[S] X) →ₗ[R] A := liftBaseChange hS
  refine ⟨h, ?_⟩
  apply TensorProduct.AlgebraTensorModule.ext
  intro r x
  change f (r • hS x) = g (r ⊗ₜ[S] x)
  rw [map_smul]
  have h1 : f (hS x) = g (1 ⊗ₜ[S] x) := LinearMap.congr_fun hhS x
  rw [h1, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
lemma smul_injective_of_projective_domain {S X : Type} [CommRing S] [IsDomain S]
    [AddCommGroup X] [Module S X] [Module.Projective S X]
    {g : S} (hg : g ≠ 0) :
    Function.Injective (fun x : X => g • x) := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property
    (Finsupp.linearCombination S (id : X → X)) LinearMap.id
    (Finsupp.linearCombination_id_surjective S X)
  intro x y hxy
  change g • x = g • y at hxy
  have h0 : g • (x - y) = 0 := by rw [smul_sub, hxy, sub_self]
  have hs0 : g • s (x - y) = 0 := by rw [← map_smul, h0, map_zero]
  have hsz : s (x - y) = 0 := by
    ext z
    have hz : g * (s (x - y)) z = 0 := congrArg (fun f : X →₀ S => f z) hs0
    exact (mul_eq_zero.mp hz).resolve_left hg
  have hxy0 : x - y = 0 := by
    have h1 : Finsupp.linearCombination S (id : X → X) (s (x - y)) = x - y :=
      LinearMap.congr_fun hs (x - y)
    rw [hsz, map_zero] at h1
    exact h1.symm
  exact sub_eq_zero.mp hxy0
lemma homology_zero_equiv_quot_range {R : Type} [CommRing R]
    (K : ChainComplex (ModuleCat.{0} R) ℕ) :
    Nonempty (K.homology 0 ≃ₗ[R] (K.X 0 ⧸ LinearMap.range (K.d 1 0).hom)) := by
  have hg0 : (K.sc' 1 0 0).g = 0 := K.shape 0 0 (by simp)
  have _ : IsIso (K.sc' 1 0 0).homologyι := ShortComplex.isIso_homologyι (K.sc' 1 0 0) hg0
  let e1 : K.homology 0 ≅ (K.sc' 1 0 0).homology :=
    K.homologyIsoSc' 1 0 0 (ChainComplex.prev ℕ 0) ChainComplex.next_nat_zero
  let e2 : (K.sc' 1 0 0).homology ≅ (K.sc' 1 0 0).opcycles := asIso (K.sc' 1 0 0).homologyι
  let e3 : (K.sc' 1 0 0).opcycles ≅ ModuleCat.of R (K.X 0 ⧸ LinearMap.range (K.d 1 0).hom) :=
    (K.sc' 1 0 0).moduleCatOpcyclesIso
  exact ⟨(e1 ≪≫ e2 ≪≫ e3).toLinearEquiv⟩
lemma homology_succ_equiv_of_iso {R : Type} [CommRing R]
    (K : ChainComplex (ModuleCat.{0} R) ℕ) (k : ℕ)
    {A₀ A₁ A₂ : Type} [AddCommGroup A₀] [Module R A₀]
    [AddCommGroup A₁] [Module R A₁] [AddCommGroup A₂] [Module R A₂]
    (e₀ : A₀ ≃ₗ[R] K.X k) (e₁ : A₁ ≃ₗ[R] K.X (k + 1)) (e₂ : A₂ ≃ₗ[R] K.X (k + 2))
    (f : A₂ →ₗ[R] A₁) (g : A₁ →ₗ[R] A₀)
    (hf : ∀ x, e₁ (f x) = (K.d (k + 2) (k + 1)).hom (e₂ x))
    (hg : ∀ x, e₀ (g x) = (K.d (k + 1) k).hom (e₁ x)) :
    Nonempty (K.homology (k + 1) ≃ₗ[R]
      (LinearMap.ker g ⧸ (LinearMap.range f).comap (LinearMap.ker g).subtype)) := by
  let eH : K.homology (k + 1) ≅ (K.sc' (k + 2) (k + 1) k).moduleCatLeftHomologyData.H :=
    K.homologyIsoSc' (k + 2) (k + 1) k (ChainComplex.prev ℕ (k + 1)) (ChainComplex.next_nat_succ k) ≪≫
      (K.sc' (k + 2) (k + 1) k).moduleCatHomologyIso
  let eKer : LinearMap.ker g ≃ₗ[R] LinearMap.ker (K.d (k + 1) k).hom :=
    { toFun := fun x => ⟨e₁ x.1, by
        rw [LinearMap.mem_ker, ← hg x.1, x.2, map_zero]⟩
      invFun := fun y => ⟨e₁.symm y.1, by
        rw [LinearMap.mem_ker]
        apply e₀.injective
        rw [map_zero, hg, e₁.apply_symm_apply]
        exact y.2⟩
      map_add' := fun x y => Subtype.ext (map_add e₁ x.1 y.1)
      map_smul' := fun r x => Subtype.ext (map_smul e₁ r x.1)
      left_inv := fun x => Subtype.ext (e₁.symm_apply_apply x.1)
      right_inv := fun y => Subtype.ext (e₁.apply_symm_apply y.1) }
  have hsub : Submodule.map eKer.toLinearMap ((LinearMap.range f).comap (LinearMap.ker g).subtype) =
      LinearMap.range (K.sc' (k + 2) (k + 1) k).moduleCatToCycles := by
    ext ⟨y, hy⟩
    constructor
    · rintro ⟨⟨x, hx⟩, ⟨a, ha⟩, heq⟩
      refine ⟨e₂ a, Subtype.ext ?_⟩
      change (K.d (k + 2) (k + 1)).hom (e₂ a) = y
      rw [← hf a, ha]
      exact congrArg Subtype.val heq
    · rintro ⟨z, hz⟩
      have hz' : (K.d (k + 2) (k + 1)).hom z = y := congrArg Subtype.val hz
      let z' : K.X (k + 2) := z
      have hker_f : f (e₂.symm z') ∈ LinearMap.ker g := by
        rw [LinearMap.mem_ker]
        apply e₀.injective
        rw [map_zero, hg, hf, e₂.apply_symm_apply z']
        change (K.d (k + 1) k).hom ((K.d (k + 2) (k + 1)).hom z) = 0
        rw [hz']
        exact hy
      refine ⟨⟨f (e₂.symm z'), hker_f⟩, ⟨e₂.symm z', rfl⟩, Subtype.ext ?_⟩
      change e₁ (f (e₂.symm z')) = y
      rw [hf, e₂.apply_symm_apply z']
      exact hz'
  let eQ := Submodule.quotEquivOfEq _ _ hsub
  let eQuot : (LinearMap.ker g ⧸ (LinearMap.range f).comap (LinearMap.ker g).subtype) ≃ₗ[R]
      (K.sc' (k + 2) (k + 1) k).moduleCatLeftHomologyData.H :=
    (Submodule.Quotient.equiv _ _ eKer rfl).trans eQ
  exact ⟨eH.toLinearEquiv.trans eQuot.symm⟩
noncomputable def baseChangeTensorEquiv
    {S R M X : Type} [CommRing S] [CommRing R] [Algebra S R]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower S R M]
    [AddCommGroup X] [Module S X]
    (hsurj : Function.Surjective (algebraMap S R)) :
    (M ⊗[R] (R ⊗[S] X)) ≃ₗ[S] (M ⊗[S] X) := by
  let _ : SMulCommClass R S M := ⟨fun r s m => by
    obtain ⟨a, rfl⟩ := hsurj r
    rw [algebraMap_smul, algebraMap_smul, smul_comm]⟩
  let _ : SMulCommClass S R M := SMulCommClass.symm R S M
  let _ : Module R (M ⊗[S] X) := TensorProduct.leftModule
  let _ : IsScalarTower S R (M ⊗[S] X) := ⟨fun s r t => by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul m x =>
      change ((s • r) • m) ⊗ₜ[S] x = s • ((r • m) ⊗ₜ[S] x)
      rw [smul_assoc, TensorProduct.smul_tmul']
    | add t₁ t₂ ih₁ ih₂ => rw [smul_add, smul_add, smul_add, ih₁, ih₂]⟩
  let inner (m : M) : (R ⊗[S] X) →ₗ[R] (M ⊗[S] X) :=
    liftBaseChange
      { toFun := fun x => m ⊗ₜ[S] x
        map_add' := fun x₁ x₂ => TensorProduct.tmul_add m x₁ x₂
        map_smul' := fun s x => TensorProduct.tmul_smul s m x }
  let fwdR : (M ⊗[R] (R ⊗[S] X)) →ₗ[R] (M ⊗[S] X) :=
    TensorProduct.lift
      { toFun := inner
        map_add' := fun m₁ m₂ => by
          apply TensorProduct.AlgebraTensorModule.ext; intro r x
          change (r • (m₁ + m₂)) ⊗ₜ[S] x = (r • m₁) ⊗ₜ[S] x + (r • m₂) ⊗ₜ[S] x
          rw [smul_add, TensorProduct.add_tmul]
        map_smul' := fun c m => by
          apply TensorProduct.AlgebraTensorModule.ext; intro r x
          change (r • (c • m)) ⊗ₜ[S] x = (c • (r • m)) ⊗ₜ[S] x
          rw [smul_comm] }
  let bwdS : (M ⊗[S] X) →ₗ[S] (M ⊗[R] (R ⊗[S] X)) :=
    TensorProduct.lift
      (LinearMap.mk₂ S (fun m x => m ⊗ₜ[R] ((1 : R) ⊗ₜ[S] x))
        (fun m₁ m₂ x => TensorProduct.add_tmul m₁ m₂ _)
        (fun s m x => (TensorProduct.smul_tmul' s m ((1 : R) ⊗ₜ[S] x)).symm)
        (fun m x₁ x₂ => by rw [TensorProduct.tmul_add, TensorProduct.tmul_add])
        (fun s m x => by
          change m ⊗ₜ[R] ((1 : R) ⊗ₜ[S] (s • x)) = s • (m ⊗ₜ[R] ((1 : R) ⊗ₜ[S] x))
          rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one,
            ← mul_one (algebraMap S R s), ← smul_eq_mul, ← TensorProduct.smul_tmul',
            TensorProduct.tmul_smul]
          exact algebraMap_smul R s (m ⊗ₜ[R] ((1 : R) ⊗ₜ[S] x))))
  refine LinearEquiv.ofLinearMap (fwdR.restrictScalars S) bwdS ?_ ?_
  · apply TensorProduct.ext'
    intro m x
    change ((1 : R) • m) ⊗ₜ[S] x = m ⊗ₜ[S] x
    rw [one_smul]
  · apply LinearMap.ext
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul m u =>
      induction u using TensorProduct.induction_on with
      | zero => simp
      | tmul r x =>
        change (r • m) ⊗ₜ[R] ((1 : R) ⊗ₜ[S] x) = m ⊗ₜ[R] (r ⊗ₜ[S] x)
        rw [TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      | add u₁ u₂ ih₁ ih₂ =>
        simp only [LinearMap.comp_apply, LinearMap.id_apply, TensorProduct.tmul_add, map_add] at ih₁ ih₂ ⊢
        rw [ih₁, ih₂]
    | add t₁ t₂ ih₁ ih₂ =>
      simp only [LinearMap.comp_apply, LinearMap.id_apply, map_add] at ih₁ ih₂ ⊢
      rw [ih₁, ih₂]
lemma baseChangeTensorEquiv_comm
    {S R M X Y : Type} [CommRing S] [CommRing R] [Algebra S R]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower S R M]
    [AddCommGroup X] [Module S X] [AddCommGroup Y] [Module S Y]
    (hsurj : Function.Surjective (algebraMap S R))
    (f : X →ₗ[S] Y) (t : M ⊗[R] (R ⊗[S] X)) :
    baseChangeTensorEquiv hsurj (LinearMap.lTensor M (LinearMap.baseChange R f) t) =
      LinearMap.lTensor M f (baseChangeTensorEquiv hsurj t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul m u =>
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul r x => rfl
    | add u₁ u₂ ih₁ ih₂ =>
      simp only [TensorProduct.tmul_add, map_add] at ih₁ ih₂ ⊢
      rw [ih₁, ih₂]
  | add t₁ t₂ ih₁ ih₂ => rw [map_add, map_add, map_add, map_add, ih₁, ih₂]
lemma length_ker_lTensor_eq_range_delta {R : Type} [CommRing R]
    (M : Type) [AddCommGroup M] [Module R M]
    {A B C : Type} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    (i : A →ₗ[R] B) (δ : torMod R M C 1 →ₗ[R] torMod R M A 0)
    (hδ : Function.Exact δ (torMap M i 0)) :
    Module.length R (LinearMap.ker (LinearMap.lTensor M i)) =
      Module.length R (LinearMap.range δ) := by
  have hker_eq : LinearMap.ker (LinearMap.lTensor M i) =
      Submodule.map (torZeroEquiv R M A).toLinearMap (LinearMap.range δ) := by
    ext y
    obtain ⟨x, rfl⟩ := (torZeroEquiv R M A).surjective y
    constructor
    · intro hy
      have h0 : torMap M i 0 x = 0 := by
        apply (torZeroEquiv R M B).injective
        rw [map_zero, torZeroEquiv_naturality]
        exact hy
      obtain ⟨z, rfl⟩ := (hδ x).mp h0
      exact ⟨δ z, ⟨z, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨z, rfl⟩, hz⟩
      have hx : x = δ z := (torZeroEquiv R M A).injective hz.symm
      rw [hx, LinearMap.mem_ker, ← torZeroEquiv_naturality, (hδ (δ z)).mpr ⟨z, rfl⟩, map_zero]
  rw [hker_eq]
  exact (Submodule.equivMapOfInjective (torZeroEquiv R M A).toLinearMap
    (torZeroEquiv R M A).injective (LinearMap.range δ)).symm.length_eq
lemma length_quot_ker_comp_of_surj {R : Type} [CommRing R]
    {W X Y Z : Type} [AddCommGroup W] [Module R W] [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z]
    (d : W →ₗ[R] X) (p : X →ₗ[R] Y) (f : Y →ₗ[R] Z) (h : X →ₗ[R] Z)
    (hp : Function.Surjective p) (hh : h = f.comp p)
    (hker : LinearMap.ker p = LinearMap.range d) :
    Module.length R (LinearMap.ker h ⧸ (LinearMap.range d).comap (LinearMap.ker h).subtype) =
      Module.length R (LinearMap.ker f) := by
  let φ : LinearMap.ker h →ₗ[R] LinearMap.ker f :=
    LinearMap.codRestrict (LinearMap.ker f) (p.comp (LinearMap.ker h).subtype) (fun u => by
      change f (p u.1) = 0
      have hu : h u.1 = 0 := u.2
      exact (LinearMap.congr_fun hh u.1).symm.trans hu)
  have hφ_surj : Function.Surjective φ := by
    rintro ⟨b, hb⟩
    obtain ⟨u, rfl⟩ := hp b
    have hu : h u = 0 := (LinearMap.congr_fun hh u).trans hb
    exact ⟨⟨u, hu⟩, rfl⟩
  have hφ_ker : LinearMap.ker φ = (LinearMap.range d).comap (LinearMap.ker h).subtype := by
    ext ⟨u, hu⟩
    rw [LinearMap.mem_ker, Subtype.ext_iff]
    change p u = 0 ↔ u ∈ LinearMap.range d
    rw [← LinearMap.mem_ker, hker]
  exact ((Submodule.quotEquivOfEq _ _ hφ_ker.symm).trans (φ.quotKerEquivOfSurjective hφ_surj)).length_eq
lemma length_quot_ker_split {R : Type} [CommRing R]
    {W V U X Y Z : Type} [AddCommGroup W] [Module R W] [AddCommGroup V] [Module R V]
    [AddCommGroup U] [Module R U] [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z]
    (d : W →ₗ[R] X) (α : V →ₗ[R] U) (β : U →ₗ[R] X) (p : X →ₗ[R] Y) (γ : Y →ₗ[R] Z) (h : X →ₗ[R] Z)
    (hp : Function.Surjective p) (hh : h = γ.comp p)
    (hker_p : LinearMap.ker p = LinearMap.range β)
    (hrange_d : LinearMap.range d = LinearMap.range (β.comp α)) :
    Module.length R (LinearMap.ker h ⧸ (LinearMap.range d).comap (LinearMap.ker h).subtype) =
      Module.length R (LinearMap.range β ⧸
        (LinearMap.range (β.comp α)).comap (LinearMap.range β).subtype) +
        Module.length R (LinearMap.ker γ) := by
  let K0 := LinearMap.ker h
  let R1 : Submodule R K0 := (LinearMap.range d).comap K0.subtype
  let J : Submodule R (LinearMap.range β) :=
    (LinearMap.range (β.comp α)).comap (LinearMap.range β).subtype
  have hβ_le_K0 : LinearMap.range β ≤ K0 := by
    rw [← hker_p]
    intro u hu
    change h u = 0
    rw [LinearMap.congr_fun hh u, LinearMap.comp_apply, LinearMap.mem_ker.mp hu, map_zero]
  let f1 : (LinearMap.range β ⧸ J) →ₗ[R] (K0 ⧸ R1) :=
    J.liftQ (R1.mkQ.comp (LinearMap.codRestrict K0 (LinearMap.range β).subtype
      (fun x => hβ_le_K0 x.2))) (by
        rintro ⟨u, hu⟩ hJ
        rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
          Submodule.Quotient.mk_eq_zero]
        change u ∈ LinearMap.range d
        rw [hrange_d]
        exact hJ)
  let g1 : (K0 ⧸ R1) →ₗ[R] LinearMap.ker γ :=
    R1.liftQ (LinearMap.codRestrict (LinearMap.ker γ) (p.comp K0.subtype) (fun u => by
      change γ (p u.1) = 0
      exact (LinearMap.congr_fun hh u.1).symm.trans u.2)) (by
        rintro ⟨u, hu⟩ huR1
        rw [LinearMap.mem_ker]
        apply Subtype.ext
        change p u = 0
        have hmem : u ∈ LinearMap.range (β.comp α) := hrange_d ▸ huR1
        obtain ⟨a, rfl⟩ := hmem
        have : β (α a) ∈ LinearMap.range β := ⟨α a, rfl⟩
        rw [← hker_p] at this
        exact this)
  have hf1_inj : Function.Injective f1 := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective J y
    rw [Submodule.Quotient.mk_eq_zero]
    have hmem : x.1 ∈ LinearMap.range d := (Submodule.Quotient.mk_eq_zero R1).mp hy
    rw [hrange_d] at hmem
    exact hmem
  have hg1_surj : Function.Surjective g1 := by
    rintro ⟨b, hb⟩
    obtain ⟨u, rfl⟩ := hp b
    have hu : u ∈ K0 := by change h u = 0; exact (LinearMap.congr_fun hh u).trans hb
    exact ⟨Submodule.Quotient.mk ⟨u, hu⟩, rfl⟩
  have hex1 : Function.Exact f1 g1 := by
    intro y
    obtain ⟨⟨u, hu⟩, rfl⟩ := Submodule.Quotient.mk_surjective R1 y
    constructor
    · intro hy
      have h0 : p u = 0 := congrArg Subtype.val hy
      have huβ : u ∈ LinearMap.range β := by rw [← hker_p]; exact h0
      exact ⟨Submodule.Quotient.mk ⟨u, huβ⟩, rfl⟩
    · rintro ⟨z, hz⟩
      obtain ⟨⟨v, hv⟩, rfl⟩ := Submodule.Quotient.mk_surjective J z
      rw [← hz]
      apply Subtype.ext
      change p v = 0
      rw [← LinearMap.mem_ker, hker_p]
      exact hv
  exact Module.length_eq_add_of_exact f1 g1 hf1_inj hg1_surj hex1
set_option maxHeartbeats 800000 in
lemma serre_h4_aux
    (S : Type) [CommRing S] [IsRegularLocalRing S] [IsDomain S]
    (g : S) (hg_ne : g ≠ 0)
    (R : Type) [CommRing R] [Algebra S R] [IsRegularLocalRing R]
    (hsurj : Function.Surjective (algebraMap S R))
    (hsurj_tmul : ∀ {X : Type} [AddCommGroup X] [Module S X] (u : R ⊗[S] X),
      ∃ x : X, (1 : R) ⊗ₜ[S] x = u)
    (hone_tmul_zero_iff : ∀ {X : Type} [AddCommGroup X] [Module S X] (x : X),
      (1 : R) ⊗ₜ[S] x = 0 ↔ ∃ y : X, g • y = x)
    (P Q : Ideal S) (hPQ : (P ⊔ Q).radical = maximalIdeal S)
    (M : Type) [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower S R M]
    [Module.Finite S M] [Module.Finite R M]
    (N : Type) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower S R N]
    [Module.Finite S N] [Module.Finite R N]
    (hM_annP : ∀ a ∈ P, ∀ m : M, a • m = 0)
    (hN_annQ : ∀ a ∈ Q, ∀ n : N, a • n = 0)
    (hgN : ∀ n : N, g • n = 0) :
    Module.intersectionMultiplicity S M N = 0 := by
  let PN : ProjectiveResolution (ModuleCat.of S N) := projectiveResolution (ModuleCat.of S N)
  have hPN_proj (n : ℕ) : Module.Projective S (PN.complex.X n) :=
    ModuleCat.projective_of_module_projective (P := PN.complex.X n)
  have hPN_reg (n : ℕ) : Function.Injective (fun x : PN.complex.X n => g • x) := by
    let _ := hPN_proj n
    exact smul_injective_of_projective_domain hg_ne
  let εP : PN.complex.X 0 →ₗ[S] N := (PN.π.f 0).hom
  have hεP_surj : Function.Surjective εP :=
    (ModuleCat.epi_iff_surjective (PN.π.f 0)).mp inferInstance
  have hεP_comp (x : PN.complex.X 1) : εP ((PN.complex.d 1 0).hom x) = 0 :=
    congrArg (fun φ : PN.complex.X 1 ⟶ ModuleCat.of S N => φ.hom x) PN.complex_d_comp_π_f_zero
  have hεP_exact (x : PN.complex.X 0) (hx : εP x = 0) :
      ∃ y : PN.complex.X 1, (PN.complex.d 1 0).hom y = x := by
    let Quot := PN.complex.X 0 ⧸ LinearMap.range (PN.complex.d 1 0).hom
    let q : PN.complex.X 0 ⟶ ModuleCat.of S Quot :=
      ModuleCat.ofHom (LinearMap.range (PN.complex.d 1 0).hom).mkQ
    have hqw : (PN.complex.d 1 0 ≫ q) = 0 := by
      ext z; exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨z, rfl⟩
    let desc : ModuleCat.of S N ⟶ ModuleCat.of S Quot :=
      PN.isColimitCokernelCofork.desc (CokernelCofork.ofπ q hqw)
    have hfac : (PN.π.f 0 ≫ desc) = q :=
      PN.isColimitCokernelCofork.fac (CokernelCofork.ofπ q hqw) WalkingParallelPair.one
    have hqx : q.hom x = 0 := by
      have h1 : desc.hom ((PN.π.f 0).hom x) = q.hom x :=
        congrArg (fun φ : PN.complex.X 0 ⟶ ModuleCat.of S Quot => φ.hom x) hfac
      have hx0 : (PN.π.f 0).hom x = (0 : N) := hx
      rw [← h1, hx0]
      exact map_zero desc.hom
    exact (Submodule.Quotient.mk_eq_zero _).mp hqx
  have hPN_exact (n : ℕ) (x : PN.complex.X (n + 1)) (hx : (PN.complex.d (n + 1) n).hom x = 0) :
      ∃ y : PN.complex.X (n + 2), (PN.complex.d (n + 2) (n + 1)).hom y = x :=
    (ShortComplex.moduleCat_exact_iff _).mp (PN.exact_succ n) x hx
  have hPN_dd (n : ℕ) (x : PN.complex.X (n + 2)) :
      (PN.complex.d (n + 1) n).hom ((PN.complex.d (n + 2) (n + 1)).hom x) = 0 :=
    congrArg (fun φ : PN.complex.X (n + 2) ⟶ PN.complex.X n => φ.hom x)
      (PN.complex.d_comp_d (n + 2) (n + 1) n)
  have hQ_proj (n : ℕ) : Module.Projective R ((R ⊗[S] PN.complex.X n)) := by
    let _ := hPN_proj n
    exact projective_baseChange
  let dQ (n : ℕ) : (R ⊗[S] PN.complex.X (n + 1)) →ₗ[R] (R ⊗[S] PN.complex.X n) :=
    LinearMap.baseChange R (PN.complex.d (n + 1) n).hom
  have hdQ_tmul (n : ℕ) (r : R) (x : PN.complex.X (n + 1)) :
      dQ n (r ⊗ₜ[S] x) = r ⊗ₜ[S] ((PN.complex.d (n + 1) n).hom x) := rfl
  have hdQ_sq (n : ℕ) (u : (R ⊗[S] PN.complex.X (n + 2))) : dQ n (dQ (n + 1) u) = 0 := by
    obtain ⟨x, rfl⟩ := hsurj_tmul u
    rw [hdQ_tmul, hdQ_tmul, hPN_dd n x, TensorProduct.tmul_zero]
  let εQ : (R ⊗[S] PN.complex.X 0) →ₗ[R] N := liftBaseChange εP
  have hεQ_tmul (r : R) (x : PN.complex.X 0) : εQ (r ⊗ₜ[S] x) = r • εP x := rfl
  have hεQ_surj : Function.Surjective εQ := fun n => by
    obtain ⟨x, rfl⟩ := hεP_surj n
    exact ⟨1 ⊗ₜ[S] x, by rw [hεQ_tmul, one_smul]⟩
  have hεQ_comp (u : (R ⊗[S] PN.complex.X 1)) : εQ (dQ 0 u) = 0 := by
    obtain ⟨x, rfl⟩ := hsurj_tmul u
    rw [hdQ_tmul, hεQ_tmul, hεP_comp x, smul_zero]
  have hεQ_exact (u : (R ⊗[S] PN.complex.X 0)) (hu : εQ u = 0) : ∃ v : (R ⊗[S] PN.complex.X 1), dQ 0 v = u := by
    obtain ⟨x, rfl⟩ := hsurj_tmul u
    rw [hεQ_tmul, one_smul] at hu
    obtain ⟨y, hy⟩ := hεP_exact x hu
    exact ⟨1 ⊗ₜ[S] y, by rw [hdQ_tmul, hy]⟩
  have hQ_exact_ge2 (n : ℕ) (u : (R ⊗[S] PN.complex.X (n + 2))) (hu : dQ (n + 1) u = 0) :
      ∃ v : (R ⊗[S] PN.complex.X (n + 3)), dQ (n + 2) v = u := by
    obtain ⟨x, rfl⟩ := hsurj_tmul u
    rw [hdQ_tmul] at hu
    obtain ⟨y, hy⟩ := (hone_tmul_zero_iff _).mp hu
    have hdy : (PN.complex.d (n + 1) n).hom y = 0 := by
      apply hPN_reg n
      dsimp only
      rw [smul_zero, ← map_smul, hy, hPN_dd n x]
    obtain ⟨z, hz⟩ := hPN_exact n y hdy
    have hdxz : (PN.complex.d (n + 2) (n + 1)).hom (x - g • z) = 0 := by
      rw [map_sub, map_smul, hz, hy, sub_self]
    obtain ⟨w, hw⟩ := hPN_exact (n + 1) (x - g • z) hdxz
    refine ⟨1 ⊗ₜ[S] w, ?_⟩
    rw [hdQ_tmul, hw, TensorProduct.tmul_sub]
    have hgz0 : (1 : R) ⊗ₜ[S] (g • z) = 0 := (hone_tmul_zero_iff _).mpr ⟨z, rfl⟩
    rw [hgz0, sub_zero]
  let B0 : Submodule R (R ⊗[S] PN.complex.X 0) := LinearMap.range (dQ 0)
  let _ : AddCommGroup B0 := Submodule.addCommGroup B0
  let Z1 : Submodule R (R ⊗[S] PN.complex.X 1) := LinearMap.ker (dQ 0)
  let _ : AddCommGroup Z1 := Submodule.addCommGroup Z1
  let dQ1_to_Z1 : (R ⊗[S] PN.complex.X 2) →ₗ[R] Z1 := LinearMap.codRestrict Z1 (dQ 1) (fun u => hdQ_sq 0 u)
  let B1 : Submodule R Z1 := LinearMap.range dQ1_to_Z1
  let _ : AddCommGroup B1 := Submodule.addCommGroup B1
  have hZ1_exists_y (u : Z1) :
      ∃ y : PN.complex.X 0, ∃ x : PN.complex.X 1,
        (1 : R) ⊗ₜ[S] x = u.1 ∧ g • y = (PN.complex.d 1 0).hom x := by
    obtain ⟨x, hx⟩ := hsurj_tmul u.1
    have h0 : (1 : R) ⊗ₜ[S] (PN.complex.d 1 0).hom x = 0 := by
      rw [← hdQ_tmul 0 1 x, hx]
      exact u.2
    obtain ⟨y, hy⟩ := (hone_tmul_zero_iff _).mp h0
    exact ⟨y, x, hx, hy⟩
  have hψ_well_def (u : Z1) (x₁ x₂ : PN.complex.X 1) (y₁ y₂ : PN.complex.X 0)
      (hx₁ : (1 : R) ⊗ₜ[S] x₁ = u.1) (hx₂ : (1 : R) ⊗ₜ[S] x₂ = u.1)
      (hy₁ : g • y₁ = (PN.complex.d 1 0).hom x₁)
      (hy₂ : g • y₂ = (PN.complex.d 1 0).hom x₂) :
      εP y₁ = εP y₂ := by
    have hdiff0 : (1 : R) ⊗ₜ[S] (x₁ - x₂) = 0 := by
      rw [TensorProduct.tmul_sub, hx₁, hx₂, sub_self]
    obtain ⟨z, hz⟩ := (hone_tmul_zero_iff _).mp hdiff0
    have hy_diff : y₁ - y₂ = (PN.complex.d 1 0).hom z := by
      apply hPN_reg 0
      dsimp only
      rw [smul_sub, hy₁, hy₂, ← map_sub, ← hz, map_smul]
    have hε0 : εP (y₁ - y₂) = 0 := by rw [hy_diff, hεP_comp z]
    rw [map_sub] at hε0
    exact sub_eq_zero.mp hε0
  let ψFun (u : Z1) : N := εP (Classical.choose (hZ1_exists_y u))
  have hψ_eq (u : Z1) (x : PN.complex.X 1) (y : PN.complex.X 0)
      (hx : (1 : R) ⊗ₜ[S] x = u.1) (hy : g • y = (PN.complex.d 1 0).hom x) :
      ψFun u = εP y := by
    have hspec := Classical.choose_spec (hZ1_exists_y u)
    obtain ⟨x0, hx0, hy0⟩ := hspec
    exact hψ_well_def u x0 x _ y hx0 hx hy0 hy
  let ψ : Z1 →ₗ[R] N :=
    { toFun := ψFun
      map_add' := fun u₁ u₂ => by
        obtain ⟨y₁, x₁, hx₁, hy₁⟩ := hZ1_exists_y u₁
        obtain ⟨y₂, x₂, hx₂, hy₂⟩ := hZ1_exists_y u₂
        rw [hψ_eq u₁ x₁ y₁ hx₁ hy₁, hψ_eq u₂ x₂ y₂ hx₂ hy₂, ← map_add]
        exact hψ_eq (u₁ + u₂) (x₁ + x₂) (y₁ + y₂)
          (by rw [TensorProduct.tmul_add, hx₁, hx₂]; rfl)
          (by rw [smul_add, map_add, hy₁, hy₂])
      map_smul' := fun r u => by
        obtain ⟨s, rfl⟩ := hsurj r
        obtain ⟨y, x, hx, hy⟩ := hZ1_exists_y u
        rw [hψ_eq u x y hx hy]
        change ψFun ((algebraMap S R s) • u) = (algebraMap S R s) • εP y
        rw [algebraMap_smul R s (εP y), ← map_smul]
        exact hψ_eq ((algebraMap S R s) • u) (s • x) (s • y)
          (by
            change (1 : R) ⊗ₜ[S] (s • x) = (algebraMap S R s) • u.1
            rw [← hx, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one,
              ← mul_one (algebraMap S R s), ← smul_eq_mul, ← TensorProduct.smul_tmul',
              smul_eq_mul, mul_one])
          (by rw [smul_comm, hy, map_smul]) }
  have hψ_surj : Function.Surjective ψ := fun n => by
    obtain ⟨y, rfl⟩ := hεP_surj n
    have hgy : εP (g • y) = 0 := by rw [map_smul]; exact hgN (εP y)
    obtain ⟨x, hx⟩ := hεP_exact (g • y) hgy
    have hu_mem : (1 : R) ⊗ₜ[S] x ∈ Z1 := by
      rw [LinearMap.mem_ker, hdQ_tmul, hx]
      exact (hone_tmul_zero_iff _).mpr ⟨y, rfl⟩
    refine ⟨⟨(1 : R) ⊗ₜ[S] x, hu_mem⟩, ?_⟩
    exact hψ_eq ⟨(1 : R) ⊗ₜ[S] x, hu_mem⟩ x y rfl hx.symm
  have hB1_eq_ker_ψ : B1 = LinearMap.ker ψ := by
    ext u
    constructor
    · rintro ⟨w, rfl⟩
      obtain ⟨z, rfl⟩ := hsurj_tmul w
      rw [LinearMap.mem_ker]
      have h1 : ψ (dQ1_to_Z1 (1 ⊗ₜ[S] z)) = εP 0 :=
        hψ_eq (dQ1_to_Z1 (1 ⊗ₜ[S] z)) ((PN.complex.d 2 1).hom z) 0 rfl
          (by rw [smul_zero, hPN_dd 0 z])
      rw [h1, map_zero]
    · intro hu
      rw [LinearMap.mem_ker] at hu
      obtain ⟨y, x, hx, hy⟩ := hZ1_exists_y u
      have hεy : εP y = 0 := (hψ_eq u x y hx hy).symm.trans hu
      obtain ⟨z, hz⟩ := hεP_exact y hεy
      have hdxz : (PN.complex.d 1 0).hom (x - g • z) = 0 := by
        rw [map_sub, map_smul, hz, hy, sub_self]
      obtain ⟨w, hw⟩ := hPN_exact 0 (x - g • z) hdxz
      refine ⟨1 ⊗ₜ[S] w, Subtype.ext ?_⟩
      change dQ 1 (1 ⊗ₜ[S] w) = u.1
      rw [hdQ_tmul, hw, TensorProduct.tmul_sub, (hone_tmul_zero_iff _).mpr ⟨z, rfl⟩, sub_zero, hx]
  have hSES1 : LinearMap.range B0.subtype = LinearMap.ker εQ := by
    rw [Submodule.range_subtype]
    ext u
    exact ⟨by rintro ⟨v, rfl⟩; exact hεQ_comp v, fun hu => hεQ_exact u hu⟩
  have hSES2 : LinearMap.range Z1.subtype = LinearMap.ker (dQ 0).rangeRestrict := by
    rw [Submodule.range_subtype]
    ext u
    simp [Z1, LinearMap.mem_ker]
  have hSES3 : LinearMap.range B1.subtype = LinearMap.ker ψ := by
    rw [Submodule.range_subtype]
    exact hB1_eq_ker_ψ
  let dQ_shift (n : ℕ) : ModuleCat.of R ((R ⊗[S] PN.complex.X (n + 3))) ⟶ ModuleCat.of R ((R ⊗[S] PN.complex.X (n + 2))) :=
    ModuleCat.ofHom (dQ (n + 2))
  have hdQ_shift_sq (n : ℕ) : (dQ_shift (n + 1) ≫ dQ_shift n) = 0 := by
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro u; exact hdQ_sq (n + 2) u
  let Qshift : ChainComplex (ModuleCat.{0} R) ℕ :=
    ChainComplex.of (fun n => ModuleCat.of R ((R ⊗[S] PN.complex.X (n + 2)))) dQ_shift hdQ_shift_sq
  have hQshift_d (n : ℕ) : (Qshift.d (n + 1) n).hom = dQ (n + 2) := by
    change (ChainComplex.of.d (fun k => ModuleCat.of R ((R ⊗[S] PN.complex.X (k + 2)))) dQ_shift (n + 1) n).hom =
      dQ (n + 2)
    rw [ChainComplex.of_d]
    rfl
  let p2 : (R ⊗[S] PN.complex.X 2) →ₗ[R] B1 := dQ1_to_Z1.rangeRestrict
  have hp2_surj : Function.Surjective p2 := dQ1_to_Z1.surjective_rangeRestrict
  have hp2_comp (u : Qshift.X 1) : p2 ((Qshift.d 1 0).hom u) = 0 := by
    rw [hQshift_d 0]
    apply Subtype.ext; apply Subtype.ext
    exact hdQ_sq 1 u
  have hp2_exact (u : Qshift.X 0) (hu : p2 u = 0) :
      ∃ v : Qshift.X 1, (Qshift.d 1 0).hom v = u := by
    rw [hQshift_d 0]
    have h0 : dQ 1 u = 0 := congrArg (fun z : B1 => z.1.1) hu
    exact hQ_exact_ge2 0 u h0
  have hQshift_exact (n : ℕ) (u : Qshift.X (n + 1)) (hu : (Qshift.d (n + 1) n).hom u = 0) :
      ∃ v : Qshift.X (n + 2), (Qshift.d (n + 2) (n + 1)).hom v = u := by
    rw [hQshift_d n] at hu
    rw [hQshift_d (n + 1)]
    exact hQ_exact_ge2 (n + 1) u hu
  let PB1 : ProjectiveResolution (ModuleCat.of R B1) :=
    projectiveResolutionOfExact B1 Qshift (fun n => hQ_proj (n + 2)) p2
      hp2_surj hp2_comp hp2_exact hQshift_exact
  let eMQ (n : ℕ) : (M ⊗[R] (R ⊗[S] PN.complex.X n)) ≃ₗ[S] (M ⊗[S] PN.complex.X n) :=
    baseChangeTensorEquiv (S := S) (R := R) (M := M) (X := PN.complex.X n) hsurj
  have heMQ_comm (n : ℕ) (t : M ⊗[R] (R ⊗[S] PN.complex.X (n + 1))) :
      eMQ n (LinearMap.lTensor M (dQ n) t) =
        LinearMap.lTensor M (PN.complex.d (n + 1) n).hom (eMQ (n + 1) t) :=
    baseChangeTensorEquiv_comm (S := S) (R := R) (M := M) hsurj
      (PN.complex.d (n + 1) n).hom t
  let FS := (tensoringLeft (ModuleCat.{0} S)).obj (ModuleCat.of S M)
  let KSN : ChainComplex (ModuleCat.{0} S) ℕ := (FS.mapHomologicalComplex _).obj PN.complex
  have hTorS_iso (i : ℕ) : Nonempty (torMod S M N i ≃ₗ[S] KSN.homology i) :=
    ⟨(PN.isoLeftDerivedObj FS i).toLinearEquiv⟩
  have hTorS_zero : Nonempty (torMod S M N 0 ≃ₗ[S] ((M ⊗[R] (R ⊗[S] PN.complex.X 0)) ⧸ LinearMap.range (LinearMap.lTensor M (dQ 0)))) := by
    obtain ⟨e1⟩ := hTorS_iso 0
    obtain ⟨e2⟩ := homology_zero_equiv_quot_range KSN
    let q : KSN.X 0 →ₗ[S] ((M ⊗[R] (R ⊗[S] PN.complex.X 0)) ⧸ LinearMap.range (LinearMap.lTensor M (dQ 0))) :=
      ((Submodule.mkQ (LinearMap.range (LinearMap.lTensor M (dQ 0)))).restrictScalars S).comp
        (eMQ 0).symm.toLinearMap
    have hq_surj : Function.Surjective q :=
      (Submodule.mkQ_surjective _).comp (eMQ 0).symm.surjective
    have hq_ker : LinearMap.ker q = LinearMap.range (KSN.d 1 0).hom := by
      ext y
      change Submodule.Quotient.mk ((eMQ 0).symm y) = 0 ↔ y ∈ LinearMap.range (KSN.d 1 0).hom
      rw [Submodule.Quotient.mk_eq_zero]
      constructor
      · rintro ⟨t, ht⟩
        let y' : M ⊗[S] PN.complex.X 0 := y
        refine ⟨eMQ 1 t, ?_⟩
        change LinearMap.lTensor M (PN.complex.d 1 0).hom (eMQ 1 t) = y'
        rw [← heMQ_comm 0 t, ht, (eMQ 0).apply_symm_apply y']
      · rintro ⟨z, rfl⟩
        let z' : M ⊗[S] PN.complex.X 1 := z
        refine ⟨(eMQ 1).symm z', ?_⟩
        apply (eMQ 0).injective
        rw [heMQ_comm 0, (eMQ 1).apply_symm_apply z']
        exact ((eMQ 0).apply_symm_apply (LinearMap.lTensor M (PN.complex.d 1 0).hom z')).symm
    let eQ0 : (KSN.X 0 ⧸ LinearMap.range (KSN.d 1 0).hom) ≃ₗ[S]
        ((M ⊗[R] (R ⊗[S] PN.complex.X 0)) ⧸ LinearMap.range (LinearMap.lTensor M (dQ 0))) :=
      (Submodule.quotEquivOfEq _ _ hq_ker.symm).trans (q.quotKerEquivOfSurjective hq_surj)
    exact ⟨e1.trans (e2.trans eQ0)⟩
  have hTorS_succ_len (k : ℕ) :
      Module.length S (torMod S M N (k + 1)) =
        Module.length R (LinearMap.ker (LinearMap.lTensor M (dQ k)) ⧸
          (LinearMap.range (LinearMap.lTensor M (dQ (k + 1)))).comap
            (LinearMap.ker (LinearMap.lTensor M (dQ k))).subtype) := by
    obtain ⟨e1⟩ := hTorS_iso (k + 1)
    let fS := (LinearMap.lTensor M (dQ (k + 1))).restrictScalars S
    let gS := (LinearMap.lTensor M (dQ k)).restrictScalars S
    obtain ⟨e2⟩ := homology_succ_equiv_of_iso KSN k (eMQ k) (eMQ (k + 1)) (eMQ (k + 2))
      fS gS (fun t => heMQ_comm (k + 1) t) (fun t => heMQ_comm k t)
    let KR := LinearMap.ker (LinearMap.lTensor M (dQ k))
    let RR : Submodule R KR := (LinearMap.range (LinearMap.lTensor M (dQ (k + 1)))).comap KR.subtype
    let q : LinearMap.ker gS →ₗ[S] (KR ⧸ RR) :=
      { toFun := fun u => Submodule.Quotient.mk ⟨u.1, u.2⟩
        map_add' := fun u v => rfl
        map_smul' := fun s u => by
          change Submodule.Quotient.mk (s • (⟨u.1, u.2⟩ : KR)) =
            s • Submodule.Quotient.mk (⟨u.1, u.2⟩ : KR)
          rfl }
    have hq_surj : Function.Surjective q := by
      intro w
      obtain ⟨⟨u, hu⟩, rfl⟩ := Submodule.Quotient.mk_surjective RR w
      exact ⟨⟨u, hu⟩, rfl⟩
    have hq_ker : LinearMap.ker q = (LinearMap.range fS).comap (LinearMap.ker gS).subtype := by
      ext ⟨u, hu⟩
      change Submodule.Quotient.mk (⟨u, hu⟩ : KR) = 0 ↔ u ∈ LinearMap.range fS
      rw [Submodule.Quotient.mk_eq_zero]
      rfl
    let e3 : (LinearMap.ker gS ⧸ (LinearMap.range fS).comap (LinearMap.ker gS).subtype) ≃ₗ[S]
        (KR ⧸ RR) :=
      (Submodule.quotEquivOfEq _ _ hq_ker.symm).trans (q.quotKerEquivOfSurjective hq_surj)
    rw [e1.length_eq, e2.length_eq, e3.length_eq,
      Module.length_eq_of_surjective (S := S) (R := R) hsurj]
  let FR := (tensoringLeft (ModuleCat.{0} R)).obj (ModuleCat.of R M)
  let KRB1 : ChainComplex (ModuleCat.{0} R) ℕ := (FR.mapHomologicalComplex _).obj PB1.complex
  have hTorS_ge3 (k : ℕ) :
      Module.length S (torMod S M N (k + 3)) = Module.length R (torMod R M B1 (k + 1)) := by
    have eR1 : torMod R M B1 (k + 1) ≃ₗ[R] KRB1.homology (k + 1) :=
      (PB1.isoLeftDerivedObj FR (k + 1)).toLinearEquiv
    obtain ⟨eR2⟩ := homology_succ_equiv_of_iso KRB1 k
      (LinearEquiv.refl R (M ⊗[R] (R ⊗[S] PN.complex.X (k + 2))))
      (LinearEquiv.refl R (M ⊗[R] (R ⊗[S] PN.complex.X (k + 3))))
      (LinearEquiv.refl R (M ⊗[R] (R ⊗[S] PN.complex.X (k + 4))))
      (LinearMap.lTensor M (dQ (k + 3)))
      (LinearMap.lTensor M (dQ (k + 2)))
      (fun t => by
        change LinearMap.lTensor M (dQ (k + 3)) t = LinearMap.lTensor M (Qshift.d (k + 2) (k + 1)).hom t
        rw [hQshift_d (k + 1)])
      (fun t => by
        change LinearMap.lTensor M (dQ (k + 2)) t = LinearMap.lTensor M (Qshift.d (k + 1) k).hom t
        rw [hQshift_d k])
    rw [hTorS_succ_len (k + 2), eR1.length_eq, eR2.length_eq]
  let d : ℕ := (maximalIdeal R).spanFinrank
  have hN_res : HasFiniteProjRes R d N := hasFiniteProjRes_of_isRegularLocalRing R N
  have hTorR_sub (i : ℕ) (hi : d < i) : Subsingleton (torMod R M N i) :=
    tor_subsingleton_of_hasFiniteProjRes M d N hN_res i hi
  have hTorR_fin (i : ℕ) : Module.Finite R (torMod R M N i) :=
    tor_finite_of_hasFiniteProjRes M d N hN_res i
  have hTorR_len_fin (i : ℕ) : Module.length R (torMod R M N i) ≠ ⊤ := by
    let _ : Module.Finite R (torMod R M N i) := hTorR_fin i
    let _ : Module S (torMod R M N i) := Module.compHom _ (algebraMap S R)
    let _ : IsScalarTower S R (torMod R M N i) :=
      ⟨fun s r x => by
        obtain ⟨a, rfl⟩ := hsurj r
        rw [Algebra.smul_def, mul_smul]; rfl⟩
    let _ : Module.Finite S (torMod R M N i) := by
      obtain ⟨r, g', hg'⟩ := exists_finite_free_surj (R := R) (torMod R M N i)
      let liftS : (Fin r → S) →ₗ[S] (Fin r → R) :=
        { toFun := fun v j => algebraMap S R (v j)
          map_add' := fun u v => by ext j; exact map_add _ _ _
          map_smul' := fun s v => by
            ext j
            simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Algebra.smul_def, map_mul] }
      have hliftS : Function.Surjective liftS := fun w => by
        refine ⟨fun j => Classical.choose (hsurj (w j)), ?_⟩
        ext j; exact Classical.choose_spec (hsurj (w j))
      exact Module.Finite.of_surjective ((g'.restrictScalars S).comp liftS) (hg'.comp hliftS)
    rw [← Module.length_eq_of_surjective (S := S) (R := R) hsurj]
    refine length_ne_top_of_annihilated_radical_eq_maximalIdeal hPQ fun a ha x => ?_
    rw [Submodule.mem_sup] at ha
    obtain ⟨p, hp, q, hq, rfl⟩ := ha
    change (algebraMap S R (p + q)) • x = 0
    rw [map_add, add_smul]
    have hp0 : (algebraMap S R p) • x = 0 :=
      tor_smul_eq_zero_left (R := R) M N (a := algebraMap S R p)
        (fun m => by rw [algebraMap_smul]; exact hM_annP p hp m) i x
    have hq0 : (algebraMap S R q) • x = 0 :=
      tor_smul_eq_zero_right (R := R) M N (b := algebraMap S R q)
        (fun n => by rw [algebraMap_smul]; exact hN_annQ q hq n) i x
    rw [hp0, hq0, add_zero]
  obtain ⟨δ1, hδ1_1, hδ1_2, hδ1_3⟩ := horseshoe_tor_les (R := R) M (A := B0) B0.subtype εQ
    (Submodule.subtype_injective B0) hεQ_surj hSES1
  obtain ⟨δ2, hδ2_1, hδ2_2, hδ2_3⟩ := horseshoe_tor_les (R := R) M (A := Z1) (C := B0)
    Z1.subtype (dQ 0).rangeRestrict
    (Submodule.subtype_injective Z1) (dQ 0).surjective_rangeRestrict hSES2
  obtain ⟨δ3, hδ3_1, hδ3_2, hδ3_3⟩ := horseshoe_tor_les (R := R) M (A := B1) (B := Z1) (C := N)
    B1.subtype ψ (Submodule.subtype_injective B1) hψ_surj hSES3
  have hTorB0_equiv (k : ℕ) :
      Nonempty (torMod R M N (k + 2) ≃ₗ[R] torMod R M B0 (k + 1)) := by
    let _ := hQ_proj 0
    have hsub1 : Subsingleton (torMod R M ((R ⊗[S] PN.complex.X 0)) (k + 1)) :=
      tor_succ_subsingleton_of_projective M ((R ⊗[S] PN.complex.X 0)) k
    have hsub2 : Subsingleton (torMod R M ((R ⊗[S] PN.complex.X 0)) (k + 2)) :=
      tor_succ_subsingleton_of_projective M ((R ⊗[S] PN.complex.X 0)) (k + 1)
    have hbij : Function.Bijective (δ1 (k + 1)) := by
      constructor
      · rw [injective_iff_map_eq_zero]
        intro x hx
        obtain ⟨z, hz⟩ := (hδ1_3 (k + 1) x).mp hx
        rw [Subsingleton.elim z 0, map_zero] at hz
        exact hz.symm
      · intro y
        exact (hδ1_1 (k + 1) y).mp (Subsingleton.elim _ _)
    exact ⟨LinearEquiv.ofBijective (δ1 (k + 1)) hbij⟩
  have hTorZ1_equiv (k : ℕ) :
      Nonempty (torMod R M N (k + 3) ≃ₗ[R] torMod R M Z1 (k + 1)) := by
    let _ := hQ_proj 1
    have hsub1 : Subsingleton (torMod R M ((R ⊗[S] PN.complex.X 1)) (k + 1)) :=
      tor_succ_subsingleton_of_projective M ((R ⊗[S] PN.complex.X 1)) k
    have hsub2 : Subsingleton (torMod R M ((R ⊗[S] PN.complex.X 1)) (k + 2)) :=
      tor_succ_subsingleton_of_projective M ((R ⊗[S] PN.complex.X 1)) (k + 1)
    have hbij : Function.Bijective (δ2 (k + 1)) := by
      constructor
      · rw [injective_iff_map_eq_zero]
        intro x hx
        obtain ⟨z, hz⟩ := (hδ2_3 (k + 1) x).mp hx
        rw [Subsingleton.elim z 0, map_zero] at hz
        exact hz.symm
      · intro y
        exact (hδ2_1 (k + 1) y).mp (Subsingleton.elim _ _)
    obtain ⟨e1⟩ := hTorB0_equiv (k + 1)
    exact ⟨e1.trans (LinearEquiv.ofBijective (δ2 (k + 1)) hbij)⟩
  let α : (M ⊗[R] B1) →ₗ[R] (M ⊗[R] Z1) := LinearMap.lTensor M B1.subtype
  let β : (M ⊗[R] Z1) →ₗ[R] (M ⊗[R] (R ⊗[S] PN.complex.X 1)) := LinearMap.lTensor M Z1.subtype
  let γ : (M ⊗[R] B0) →ₗ[R] (M ⊗[R] (R ⊗[S] PN.complex.X 0)) := LinearMap.lTensor M B0.subtype
  let Lp1 : (M ⊗[R] (R ⊗[S] PN.complex.X 1)) →ₗ[R] (M ⊗[R] B0) := LinearMap.lTensor M (dQ 0).rangeRestrict
  let Lp2 : (M ⊗[R] (R ⊗[S] PN.complex.X 2)) →ₗ[R] (M ⊗[R] B1) := LinearMap.lTensor M p2
  have hLp1_surj : Function.Surjective Lp1 :=
    LinearMap.lTensor_surjective M (dQ 0).surjective_rangeRestrict
  have hLp2_surj : Function.Surjective Lp2 :=
    LinearMap.lTensor_surjective M hp2_surj
  have hd0_fac : LinearMap.lTensor M (dQ 0) = γ.comp Lp1 := by
    rw [← LinearMap.lTensor_comp]; rfl
  have hd1_fac : LinearMap.lTensor M (dQ 1) = (β.comp α).comp Lp2 := by
    rw [LinearMap.comp_assoc, ← LinearMap.lTensor_comp, ← LinearMap.lTensor_comp]; rfl
  have hker_Lp1 : LinearMap.ker Lp1 = LinearMap.range β :=
    LinearMap.exact_iff.mp (lTensor_exact M (LinearMap.exact_iff.mpr hSES2.symm)
      (dQ 0).surjective_rangeRestrict)
  have hker_Lp2 : LinearMap.ker Lp2 = LinearMap.range (LinearMap.lTensor M (dQ 2)) := by
    have hex_d2 : Function.Exact (dQ 2) p2 := fun u => by
      constructor
      · intro hu
        have h0 : dQ 1 u = 0 := congrArg (fun z : B1 => z.1.1) hu
        exact hQ_exact_ge2 0 u h0
      · rintro ⟨v, rfl⟩
        apply Subtype.ext; apply Subtype.ext; exact hdQ_sq 1 v
    exact LinearMap.exact_iff.mp (lTensor_exact M hex_d2 hp2_surj)
  have hker_γ_len : Module.length R (LinearMap.ker γ) = Module.length R (torMod R M N 1) := by
    let _ := hQ_proj 0
    have hsub : Subsingleton (torMod R M ((R ⊗[S] PN.complex.X 0)) 1) :=
      tor_succ_subsingleton_of_projective M ((R ⊗[S] PN.complex.X 0)) 0
    have hδ1_inj : Function.Injective (δ1 0) := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨z, hz⟩ := (hδ1_3 0 x).mp hx
      rw [Subsingleton.elim z 0, map_zero] at hz
      exact hz.symm
    rw [length_ker_lTensor_eq_range_delta M B0.subtype (δ1 0) (hδ1_1 0),
      (LinearEquiv.ofInjective (δ1 0) hδ1_inj).length_eq.symm]
  have hker_β_len : Module.length R (LinearMap.ker β) = Module.length R (torMod R M N 2) := by
    let _ := hQ_proj 1
    have hsub : Subsingleton (torMod R M ((R ⊗[S] PN.complex.X 1)) 1) :=
      tor_succ_subsingleton_of_projective M ((R ⊗[S] PN.complex.X 1)) 0
    have hδ2_inj : Function.Injective (δ2 0) := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨z, hz⟩ := (hδ2_3 0 x).mp hx
      rw [Subsingleton.elim z 0, map_zero] at hz
      exact hz.symm
    obtain ⟨eB0⟩ := hTorB0_equiv 0
    rw [length_ker_lTensor_eq_range_delta M Z1.subtype (δ2 0) (hδ2_1 0),
      (LinearEquiv.ofInjective (δ2 0) hδ2_inj).length_eq.symm, eB0.length_eq]
  have hker_α_len : Module.length R (LinearMap.ker α) = Module.length R (LinearMap.range (δ3 0)) :=
    length_ker_lTensor_eq_range_delta M B1.subtype (δ3 0) (hδ3_1 0)
  have hcoker_α_len :
      Module.length R ((M ⊗[R] Z1) ⧸ LinearMap.range α) = Module.length R (torMod R M N 0) := by
    have hsurj : Function.Surjective (LinearMap.lTensor M ψ) :=
      LinearMap.lTensor_surjective M hψ_surj
    have hker : LinearMap.ker (LinearMap.lTensor M ψ) = LinearMap.range α :=
      LinearMap.exact_iff.mp (lTensor_exact M (LinearMap.exact_iff.mpr hSES3.symm) hψ_surj)
    let e1 := (Submodule.quotEquivOfEq _ _ hker.symm).trans
      ((LinearMap.lTensor M ψ).quotKerEquivOfSurjective hsurj)
    rw [e1.length_eq, (torZeroEquiv R M N).length_eq]
  have hs0_len : Module.length S (torMod S M N 0) = Module.length R (torMod R M N 0) := by
    obtain ⟨eS0⟩ := hTorS_zero
    rw [eS0.length_eq,
      Module.length_eq_of_surjective (S := S) (R := R) hsurj]
    have hrange_d0 : LinearMap.range (LinearMap.lTensor M (dQ 0)) = LinearMap.range γ := by
      rw [hd0_fac, LinearMap.range_comp, LinearMap.range_eq_top.mpr hLp1_surj, Submodule.map_top]
    have hsurj : Function.Surjective (LinearMap.lTensor M εQ) :=
      LinearMap.lTensor_surjective M hεQ_surj
    have hker : LinearMap.ker (LinearMap.lTensor M εQ) = LinearMap.range γ :=
      LinearMap.exact_iff.mp (lTensor_exact M (LinearMap.exact_iff.mpr hSES1.symm) hεQ_surj)
    let e := (Submodule.quotEquivOfEq _ _ (hrange_d0.trans hker.symm)).trans
      ((LinearMap.lTensor M εQ).quotKerEquivOfSurjective hsurj)
    rw [e.length_eq, (torZeroEquiv R M N).length_eq]
  have hs2_len : Module.length S (torMod S M N 2) = Module.length R (LinearMap.ker (β.comp α)) := by
    rw [hTorS_succ_len 1]
    exact length_quot_ker_comp_of_surj (LinearMap.lTensor M (dQ 2)) Lp2 (β.comp α)
      (LinearMap.lTensor M (dQ 1)) hLp2_surj hd1_fac hker_Lp2
  let J : Submodule R (LinearMap.range β) :=
    (LinearMap.range (β.comp α)).comap (LinearMap.range β).subtype
  have hs1_split : Module.length S (torMod S M N 1) =
      Module.length R (LinearMap.range β ⧸ J) + Module.length R (torMod R M N 1) := by
    rw [hTorS_succ_len 0, ← hker_γ_len]
    have hrange_d1 : LinearMap.range (LinearMap.lTensor M (dQ 1)) = LinearMap.range (β.comp α) := by
      ext y
      constructor
      · rintro ⟨u, rfl⟩
        exact ⟨Lp2 u, (LinearMap.congr_fun hd1_fac u).symm⟩
      · rintro ⟨b, rfl⟩
        obtain ⟨u, rfl⟩ := hLp2_surj b
        exact ⟨u, LinearMap.congr_fun hd1_fac u⟩
    exact length_quot_ker_split (LinearMap.lTensor M (dQ 1)) α β Lp1 γ
      (LinearMap.lTensor M (dQ 0)) hLp1_surj hd0_fac hker_Lp1 hrange_d1
  have hka_fin : Module.length R (LinearMap.ker α) ≠ ⊤ := by
    rw [hker_α_len]
    exact ne_top_of_le_ne_top (hTorR_len_fin 1)
      (Module.length_le_of_surjective (δ3 0).rangeRestrict (δ3 0).surjective_rangeRestrict)
  have hkb_fin : Module.length R (LinearMap.ker β) ≠ ⊤ := hker_β_len ▸ hTorR_len_fin 2
  have hca_fin : Module.length R ((M ⊗[R] Z1) ⧸ LinearMap.range α) ≠ ⊤ :=
    hcoker_α_len ▸ hTorR_len_fin 0
  have hKC := length_ker_coker_comp α β hka_fin hkb_fin hca_fin
  let s (i : ℕ) : ℤ := ((Module.length S (torMod S M N i)).toNat : ℤ)
  let t (i : ℕ) : ℤ := ((Module.length R (torMod R M N i)).toNat : ℤ)
  let r (k : ℕ) : ℤ := ((Module.length R (LinearMap.range (δ3 k))).toNat : ℤ)
  have hbase : s 0 - s 1 + s 2 = r 0 - t 1 + t 2 := by
    have hs0 : (Module.length S (torMod S M N 0)).toNat = (Module.length R (torMod R M N 0)).toNat :=
      congrArg ENat.toNat hs0_len
    have hs1 : (Module.length S (torMod S M N 1)).toNat =
        (Module.length R (LinearMap.range β ⧸ J)).toNat + (Module.length R (torMod R M N 1)).toNat := by
      have heq := hs1_split
      rw [← ENat.natCast_toNat hKC.2.1, ← ENat.natCast_toNat (hTorR_len_fin 1), ← Nat.cast_add] at heq
      rw [heq, ENat.toNat_natCast]
    have hs2 : (Module.length S (torMod S M N 2)).toNat =
        (Module.length R (LinearMap.ker (β.comp α))).toNat :=
      congrArg ENat.toNat hs2_len
    have hka : (Module.length R (LinearMap.ker α)).toNat =
        (Module.length R (LinearMap.range (δ3 0))).toNat :=
      congrArg ENat.toNat hker_α_len
    have hkb : (Module.length R (LinearMap.ker β)).toNat =
        (Module.length R (torMod R M N 2)).toNat :=
      congrArg ENat.toNat hker_β_len
    have hca : (Module.length R ((M ⊗[R] Z1) ⧸ LinearMap.range α)).toNat =
        (Module.length R (torMod R M N 0)).toNat :=
      congrArg ENat.toNat hcoker_α_len
    have hnat := hKC.2.2
    rw [← hs2, hca, hka, hkb] at hnat
    dsimp only [s, t, r, J] at *
    omega
  have hstep (m : ℕ) : s (m + 3) = r (m + 1) + r m + t (m + 3) - t (m + 1) := by
    obtain ⟨eZ⟩ := hTorZ1_equiv m
    have hZ_fin : Module.length R (torMod R M Z1 (m + 1)) ≠ ⊤ := by
      rw [← eZ.length_eq]; exact hTorR_len_fin (m + 3)
    have hZ_len : (Module.length R (torMod R M Z1 (m + 1))).toNat =
        (Module.length R (torMod R M N (m + 3))).toNat :=
      congrArg ENat.toNat eZ.length_eq.symm
    have hB1_mid := length_nat_of_exact_middle (δ3 (m + 1)) (torMap M B1.subtype (m + 1))
      (hδ3_1 (m + 1)) (hTorR_len_fin (m + 2)) hZ_fin
    have hZ1_mid := length_nat_of_exact_middle (torMap M B1.subtype (m + 1)) (torMap M ψ (m + 1))
      (hδ3_2 (m + 1)) hB1_mid.1 (hTorR_len_fin (m + 1))
    have hN_mid : (Module.length R (torMod R M N (m + 1))).toNat =
        (Module.length R (LinearMap.range (torMap M ψ (m + 1)))).toNat +
          (Module.length R (LinearMap.range (δ3 m))).toNat := by
      have hker_eq : LinearMap.ker (δ3 m) = LinearMap.range (torMap M ψ (m + 1)) :=
        LinearMap.exact_iff.mp (hδ3_3 m)
      have hrf_fin : Module.length R (LinearMap.ker (δ3 m)) ≠ ⊤ :=
        ne_top_of_le_ne_top (hTorR_len_fin (m + 1))
          (Module.length_le_of_injective (LinearMap.ker (δ3 m)).subtype (Submodule.subtype_injective _))
      have hrg_fin : Module.length R (LinearMap.range (δ3 m)) ≠ ⊤ :=
        ne_top_of_le_ne_top (hTorR_len_fin (m + 1))
          (Module.length_le_of_surjective (δ3 m).rangeRestrict (δ3 m).surjective_rangeRestrict)
      have hsplit := length_nat_add_of_exact (LinearMap.ker (δ3 m)).subtype (δ3 m).rangeRestrict
        (Submodule.subtype_injective _) (δ3 m).surjective_rangeRestrict
        (fun b => by
          constructor
          · intro hb; exact ⟨⟨b, congrArg Subtype.val hb⟩, rfl⟩
          · rintro ⟨⟨b, hb⟩, rfl⟩; exact Subtype.ext hb)
        hrf_fin hrg_fin
      rw [hsplit.2, (LinearEquiv.ofEq _ _ hker_eq).length_eq]
    have hs_eq : (Module.length S (torMod S M N (m + 3))).toNat =
        (Module.length R (torMod R M B1 (m + 1))).toNat :=
      congrArg ENat.toNat (hTorS_ge3 m)
    dsimp only [s, t, r]
    omega
  have ht_zero (i : ℕ) (hi : d < i) : t i = 0 := by
    have _ : Subsingleton (torMod R M N i) := hTorR_sub i hi
    simp [t]
  have hr_zero (k : ℕ) (hk : d ≤ k) : r k = 0 := by
    have _ : Subsingleton (torMod R M N (k + 1)) := hTorR_sub (k + 1) (by omega)
    have _ : Subsingleton (LinearMap.range (δ3 k)) :=
      ⟨fun ⟨_, ⟨a, ha⟩⟩ ⟨_, ⟨b, hb⟩⟩ =>
        Subtype.ext (ha.symm.trans ((congrArg (δ3 k) (Subsingleton.elim a b)).trans hb))⟩
    simp [r]
  have hs_zero (i : ℕ) (hi : d + 2 < i) : s i = 0 := by
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 3 := ⟨i - 3, by omega⟩
    rw [hstep m, hr_zero (m + 1) (by omega), hr_zero m (by omega),
      ht_zero (m + 3) (by omega), ht_zero (m + 1) (by omega)]
    ring
  have hsum_tail (n : ℕ) :
      ∑ m ∈ Finset.range n, (-1 : ℤ) ^ (m + 3) * s (m + 3) =
        (-1 : ℤ) ^ (n + 2) * r n - r 0 +
          (-1 : ℤ) ^ (n + 2) * t (n + 2) + (-1 : ℤ) ^ (n + 1) * t (n + 1) + t 1 - t 2 := by
    induction n with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, zero_add]
      ring
    | succ k ih =>
      rw [Finset.sum_range_succ, ih, hstep k]
      have hp1 : (-1 : ℤ) ^ (k + 3) = -((-1 : ℤ) ^ (k + 2)) := by rw [pow_succ]; ring
      have hp2 : (-1 : ℤ) ^ (k + 2) = -((-1 : ℤ) ^ (k + 1)) := by rw [pow_succ]; ring
      rw [hp1, hp2]
      ring
  have hsum_zero : ∑ i ∈ Finset.range (d + 3), (-1 : ℤ) ^ i * s i = 0 := by
    have hsplit : ∑ i ∈ Finset.range (d + 3), (-1 : ℤ) ^ i * s i =
        (s 0 - s 1 + s 2) + ∑ m ∈ Finset.range d, (-1 : ℤ) ^ (m + 3) * s (m + 3) := by
      have h1 : d + 3 = 3 + d := by omega
      rw [h1, Finset.sum_range_add]
      have h3 : ∑ i ∈ Finset.range 3, (-1 : ℤ) ^ i * s i = s 0 - s 1 + s 2 := by
        simp [Finset.sum_range_succ]; ring
      rw [h3]
      congr 1
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [add_comm 3 m]
    rw [hsplit, hbase, hsum_tail d, hr_zero d le_rfl,
      ht_zero (d + 2) (by omega), ht_zero (d + 1) (by omega)]
    ring
  unfold Module.intersectionMultiplicity
  rw [finsum_eq_sum_of_support_subset (s := Finset.range (d + 3))]
  · exact hsum_zero
  · intro i hi
    simp only [Function.mem_support, ne_eq, Finset.mem_coe, Finset.mem_range] at hi ⊢
    by_contra hle
    have h0 : s i = 0 := hs_zero i (by omega)
    exact hi (by dsimp [s] at h0; rw [h0, mul_zero])
theorem serre_h4_main
    (S : Type) [CommRing S] [IsRegularLocalRing S]
    (g : S) (_hg_mem : g ∈ maximalIdeal S) (hg_ne : g ≠ 0)
    (hR_reg : IsRegularLocalRing (S ⧸ Ideal.span {g}))
    (P Q : Ideal S) [P.IsPrime] [Q.IsPrime]
    (hgP : g ∈ P) (hgQ : g ∈ Q)
    (hPQ : (P ⊔ Q).radical = maximalIdeal S) :
    Module.intersectionMultiplicity S (S ⧸ P) (S ⧸ Q) = 0 := by
  let _ : IsDomain S := isDomain_of_isRegularLocalRing S
  let I : Ideal S := Ideal.span {g}
  have hI_le_P : I ≤ P := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hgP)
  have hI_le_Q : I ≤ Q := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hgQ)
  have hM_annP : ∀ a ∈ P, ∀ m : S ⧸ P, a • m = 0 := fun a ha m => by
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective m
    change Ideal.Quotient.mk P (a * s) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (P.mul_mem_right s ha)
  have hN_annQ : ∀ a ∈ Q, ∀ n : S ⧸ Q, a • n = 0 := fun a ha n => by
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective n
    change Ideal.Quotient.mk Q (a * s) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Q.mul_mem_right s ha)
  let _ : IsRegularLocalRing (S ⧸ I) := hR_reg
  let _ : Module (S ⧸ I) (S ⧸ P) :=
    Module.compHom (S ⧸ P) (Ideal.Quotient.lift I (Module.toAddMonoidEnd S (S ⧸ P))
      (fun a ha => AddMonoidHom.ext fun m => hM_annP a (hI_le_P ha) m))
  let _ : Module (S ⧸ I) (S ⧸ Q) :=
    Module.compHom (S ⧸ Q) (Ideal.Quotient.lift I (Module.toAddMonoidEnd S (S ⧸ Q))
      (fun a ha => AddMonoidHom.ext fun n => hN_annQ a (hI_le_Q ha) n))
  let _ : IsScalarTower S (S ⧸ I) (S ⧸ P) :=
    ⟨fun s r m => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
      change (s * a) • m = s • (a • m)
      exact mul_smul s a m⟩
  let _ : IsScalarTower S (S ⧸ I) (S ⧸ Q) :=
    ⟨fun s r n => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
      change (s * a) • n = s • (a • n)
      exact mul_smul s a n⟩
  let _ : Module.Finite S (S ⧸ P) :=
    Module.Finite.of_surjective (Submodule.mkQ P) (Submodule.mkQ_surjective P)
  let _ : Module.Finite S (S ⧸ Q) :=
    Module.Finite.of_surjective (Submodule.mkQ Q) (Submodule.mkQ_surjective Q)
  let _ : Module.Finite (S ⧸ I) (S ⧸ P) := Module.Finite.of_restrictScalars_finite S (S ⧸ I) (S ⧸ P)
  let _ : Module.Finite (S ⧸ I) (S ⧸ Q) := Module.Finite.of_restrictScalars_finite S (S ⧸ I) (S ⧸ Q)
  refine serre_h4_aux S g hg_ne (S ⧸ I) Ideal.Quotient.mk_surjective
    (fun {X} _ _ u => exists_one_tmul_eq I u)
    (fun {X} _ _ x => ?_) P Q hPQ (S ⧸ P) (S ⧸ Q) hM_annP hN_annQ (hN_annQ g hgQ)
  constructor
  · intro h0
    have hmem : x ∈ I • (⊤ : Submodule S X) :=
      mem_ideal_smul_top_of_one_tmul_eq_zero I h0
    have hle : I • (⊤ : Submodule S X) ≤ LinearMap.range (g • (LinearMap.id : X →ₗ[S] X)) := by
      rw [Submodule.smul_le]
      rintro a ha y -
      obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton.mp ha
      exact ⟨s • y, by change g • (s • y) = (g * s) • y; rw [mul_smul]⟩
    obtain ⟨y, hy⟩ := hle hmem
    exact ⟨y, hy⟩
  · rintro ⟨y, rfl⟩
    rw [← TensorProduct.smul_tmul]
    have hg0 : g • (1 : S ⧸ I) = 0 := by
      change Ideal.Quotient.mk I (g * 1) = 0
      rw [mul_one]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    rw [hg0, TensorProduct.zero_tmul]
end ChangeOfRings
end SerreHypersurfaceVanishing
namespace SerrePositivity
lemma support_subset_closedPoint_of_isFiniteLength {R : Type*} [CommRing R] [IsLocalRing R]
    {X : Type*} [AddCommGroup X] [Module R X] (h : IsFiniteLength R X) :
    Module.support R X ⊆ {IsLocalRing.closedPoint R} := by
  induction h with
  | of_subsingleton =>
    simp [Module.support_eq_empty]
  | @of_simple_quotient M _ _ N _ _ ih =>
    have hsupp := Module.support_of_exact (f := N.subtype) (g := N.mkQ)
      (LinearMap.exact_iff.mpr (by rw [Submodule.ker_mkQ, Submodule.range_subtype]))
      N.injective_subtype N.mkQ_surjective
    rw [hsupp]
    refine Set.union_subset ih ?_
    obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp ‹IsSimpleModule R (M ⧸ N)›
    rw [IsLocalRing.eq_maximalIdeal hm] at e
    rw [e.support_eq]
    intro p hp
    have hle := Module.annihilator_le_of_mem_support hp
    rw [Ideal.annihilator_quotient] at hle
    simp only [Set.mem_singleton_iff]
    exact PrimeSpectrum.ext (le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) hle)
lemma mem_support_tensorProduct_of_mem {R : Type*} [CommRing R]
    {M N : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N]
    {p : PrimeSpectrum R} (hM : p ∈ Module.support R M) (hN : p ∈ Module.support R N) :
    p ∈ Module.support R (M ⊗[R] N) := by
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct] at hM hN ⊢
  let K := p.asIdeal.ResidueField
  have : Nontrivial (K ⊗[R] M) := hM
  have : Nontrivial (K ⊗[R] N) := hN
  have e : K ⊗[R] (M ⊗[R] N) ≃ₗ[K] (K ⊗[R] M) ⊗[K] (K ⊗[R] N) :=
    TensorProduct.AlgebraTensorModule.distribBaseChange R K M N
  refine e.toEquiv.nontrivial_congr.mpr ?_
  obtain ⟨u, hu⟩ := exists_ne (0 : K ⊗[R] M)
  obtain ⟨v, hv⟩ := exists_ne (0 : K ⊗[R] N)
  let bM := Module.Basis.ofVectorSpace K (K ⊗[R] M)
  let bN := Module.Basis.ofVectorSpace K (K ⊗[R] N)
  have hcoordM : ∃ i, bM.repr u i ≠ 0 := by
    by_contra h
    push Not at h
    exact hu (bM.repr.injective (by ext i; simp [h i]))
  obtain ⟨i, hφ⟩ := hcoordM
  have hcoordN : ∃ j, bN.repr v j ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (bN.repr.injective (by ext j; simp [h j]))
  obtain ⟨j, hψ⟩ := hcoordN
  let φ : (K ⊗[R] M) →ₗ[K] K := bM.coord i
  let ψ : (K ⊗[R] N) →ₗ[K] K := bN.coord j
  let B : (K ⊗[R] M) ⊗[K] (K ⊗[R] N) →ₗ[K] K :=
    TensorProduct.lift (LinearMap.mk₂ K (fun x y => φ x * ψ y)
      (fun x₁ x₂ y => by simp [add_mul])
      (fun c x y => by simp [mul_assoc])
      (fun x y₁ y₂ => by simp [mul_add])
      (fun c x y => by simp [mul_left_comm]))
  refine ⟨⟨u ⊗ₜ[K] v, 0, fun h => ?_⟩⟩
  have hB : B (u ⊗ₜ[K] v) = B 0 := congrArg B h
  simp only [B, TensorProduct.lift.tmul, LinearMap.mk₂_apply, map_zero, mul_eq_zero] at hB
  rcases hB with h1 | h2
  · exact hφ h1
  · exact hψ h2
lemma exists_ltSeries_of_krullDim_eq_natCast {α : Type*} [Preorder α] {n : ℕ}
    (h : Order.krullDim α = (n : WithBot ℕ∞)) :
    ∃ c : LTSeries α, c.length = n := by
  have hne : Nonempty α := by
    rw [← Order.krullDim_ne_bot_iff, h]
    exact WithBot.coe_ne_bot
  cases n with
  | zero =>
    obtain ⟨a⟩ := hne
    exact ⟨RelSeries.singleton _ a, rfl⟩
  | succ k =>
    by_contra hno
    push Not at hno
    have hle : Order.krullDim α ≤ (k : WithBot ℕ∞) := by
      rw [Order.krullDim_eq_iSup_length]
      apply WithBot.coe_le_coe.mpr
      refine iSup_le fun c => ?_
      have hc_le : (c.length : WithBot ℕ∞) ≤ ((k + 1 : ℕ) : WithBot ℕ∞) := by
        rw [← h, Order.krullDim_eq_iSup_length]
        exact WithBot.coe_le_coe.mpr (le_iSup (fun s : LTSeries α => (s.length : ℕ∞)) c)
      have hc_nat : c.length ≤ k + 1 := by exact_mod_cast hc_le
      have hc_lt : c.length < k + 1 := lt_of_le_of_ne hc_nat (hno c)
      exact Nat.cast_le.mpr (Nat.lt_succ_iff.mp hc_lt)
    rw [h] at hle
    have : k + 1 ≤ k := by exact_mod_cast hle
    omega
lemma ringKrullDim_quotient_eq_natCast {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (I : Ideal R) (hI : I ≠ ⊤) :
    ∃ n : ℕ, ringKrullDim (R ⧸ I) = (n : WithBot ℕ∞) := by
  have hle : ringKrullDim (R ⧸ I) ≤ ((maximalIdeal R).spanFinrank : WithBot ℕ∞) :=
    (ringKrullDim_quotient_le I).trans (ringKrullDim_le_spanFinrank_maximalIdeal R)
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have hne_bot : ringKrullDim (R ⧸ I) ≠ ⊥ := by
    intro hbot
    have hnn := ringKrullDim_nonneg_of_nontrivial (R := R ⧸ I)
    rw [hbot] at hnn
    exact absurd hnn (by decide)
  cases h : ringKrullDim (R ⧸ I) with
  | bot => exact absurd h hne_bot
  | coe e =>
    cases e with
    | top =>
      rw [h] at hle
      have htop : (⊤ : ℕ∞) ≤ ((maximalIdeal R).spanFinrank : ℕ∞) := WithBot.coe_le_coe.mp hle
      exact absurd (top_le_iff.mp htop) (ENat.natCast_ne_top _)
    | coe n =>
      exact ⟨n, rfl⟩
lemma exists_prime_ge_with_ringKrullDim_eq {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (I : Ideal R) (hI : I ≠ ⊤) :
    ∃ (P : Ideal R) (_ : P.IsPrime), I ≤ P ∧ ringKrullDim (R ⧸ P) = ringKrullDim (R ⧸ I) := by
  obtain ⟨n, hn⟩ := ringKrullDim_quotient_eq_natCast I hI
  have hkd : Order.krullDim (PrimeSpectrum.zeroLocus (I : Set R)) = (n : WithBot ℕ∞) := by
    rw [← ringKrullDim_quotient, hn]
  obtain ⟨c, hc⟩ := exists_ltSeries_of_krullDim_eq_natCast hkd
  let P : Ideal R := c.head.1.asIdeal
  have hIP : I ≤ P := fun x hx => c.head.2 hx
  refine ⟨P, c.head.1.isPrime, hIP, le_antisymm ?_ ?_⟩
  · exact ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hIP)
  · rw [hn, ringKrullDim_quotient, Order.krullDim]
    let c' : LTSeries (PrimeSpectrum.zeroLocus (P : Set R)) :=
      { length := c.length
        toFun := fun i => ⟨(c i).1, by
          simp only [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
          exact c.monotone (Fin.zero_le i)⟩
        step := fun i => c.step i }
    have hge : (c'.length : WithBot ℕ∞) ≤
        ⨆ s : LTSeries (PrimeSpectrum.zeroLocus (P : Set R)), (s.length : WithBot ℕ∞) :=
      le_iSup (fun s : LTSeries (PrimeSpectrum.zeroLocus (P : Set R)) =>
        (s.length : WithBot ℕ∞)) c'
    simpa [c', hc] using hge
section BasicIterPowerSeries
abbrev z0 (C:Type) : ℕ → Type
 | 0=>C
 | n+1=>PowerSeries (z0 C n)
noncomputable instance instCommRingIterPowerSeries (C:Type) [CommRing C] :
  ∀ n : ℕ,CommRing (z0 C n)
 | 0=>inferInstanceAs (CommRing C)
 | n+1 =>
  let _:=instCommRingIterPowerSeries C n
  inferInstanceAs (CommRing (PowerSeries (z0 C n)))
noncomputable instance instIsLocalRingIterPowerSeries (C:Type) [CommRing C] [IsLocalRing C] :
  ∀ n : ℕ,IsLocalRing (z0 C n)
 | 0=>inferInstanceAs (IsLocalRing C)
 | n+1 =>
  let _:=instCommRingIterPowerSeries C n;let _:=instIsLocalRingIterPowerSeries C n
  inferInstanceAs (IsLocalRing (PowerSeries (z0 C n)))
instance instIsNoetherianRingIterPowerSeries (C:Type) [CommRing C] [IsNoetherianRing C] :
  ∀ n : ℕ,IsNoetherianRing (z0 C n)
 | 0=>inferInstanceAs (IsNoetherianRing C)
 | n+1 =>
  let _:=instCommRingIterPowerSeries C n;let _:=instIsNoetherianRingIterPowerSeries C n
  inferInstanceAs (IsNoetherianRing (PowerSeries (z0 C n)))
instance instIsDomainIterPowerSeries (C:Type) [CommRing C] [IsDomain C] :
  ∀ n : ℕ,IsDomain (z0 C n)
 | 0=>inferInstanceAs (IsDomain C)
 | n+1 =>
  let _:=instCommRingIterPowerSeries C n;let _:=instIsDomainIterPowerSeries C n
  inferInstanceAs (IsDomain (PowerSeries (z0 C n)))
lemma z3 {A:Type*} [CommRing A] [IsLocalRing A]
  (f:PowerSeries A) :
  f∈maximalIdeal (PowerSeries A)↔PowerSeries.constantCoeff f∈maximalIdeal A:=by
 simp only [mem_maximalIdeal,mem_nonunits_iff,PowerSeries.isUnit_iff_constantCoeff]
lemma z4 {A:Type*} [CommRing A] [IsLocalRing A] :
  (PowerSeries.X:PowerSeries A)∈maximalIdeal (PowerSeries A):=by
 rw [z3,PowerSeries.constantCoeff_X];exact (maximalIdeal A).zero_mem
lemma z5 {A:Type*} [CommRing A] [IsLocalRing A] :
  (maximalIdeal (PowerSeries A)).map PowerSeries.constantCoeff=maximalIdeal A:=by
 refine le_antisymm ?_ ?_
 ·
  rw [map_le_iff_le_comap];intro f hf;exact (z3 f).mp hf
 ·
  intro a ha
  have hCa:PowerSeries.C a∈maximalIdeal (PowerSeries A):=by
   rw [z3,PowerSeries.constantCoeff_C];exact ha
  have:=mem_map_of_mem PowerSeries.constantCoeff hCa;simpa using this
lemma z6 {A:Type*} [CommRing A] :
  ∀ (k : ℕ) (f:PowerSeries A),(∀ i < k,PowerSeries.coeff i f=0)→f∈span {(PowerSeries.X:PowerSeries A) ^ k}:=by
 intro k
 induction k with
 | zero =>
  intro f _;simp
 | succ k ih =>
  intro f hf
  have hf0:PowerSeries.constantCoeff f=0:=by
   have:=hf 0 (Nat.succ_pos k);simpa using this
  let g:PowerSeries A:=PowerSeries.mk fun i=>PowerSeries.coeff (i+1) f
  have hfg:f=PowerSeries.X*g:=by
   ext i
   cases i with
   | zero=>simpa using hf0
   | succ i =>
    rw [PowerSeries.coeff_succ_X_mul];simp [g]
  have hg:∀ i < k,PowerSeries.coeff i g=0:=fun i hi=>by
   simp only [g,PowerSeries.coeff_mk];exact hf (i+1) (Nat.succ_lt_succ hi)
  obtain ⟨q,hq⟩:=mem_span_singleton.mp (ih g hg);rw [mem_span_singleton]
  refine ⟨q,?_⟩
  rw [hfg,hq,pow_succ'];ring
lemma z7 {A:Type*} [CommRing A] {I J:Ideal A} (h:I ≤ J) (k : ℕ) :
  I ^ k ≤ J ^ k:=by
 induction k with
 | zero=>simp
 | succ k ih =>
  rw [pow_succ,pow_succ];exact Ideal.mul_mono ih h
lemma z8 {A:Type*} [CommRing A] [IsLocalRing A] :
  ∀ (k : ℕ) (f:PowerSeries A),
   f∈maximalIdeal (PowerSeries A) ^ k↔∀ i < k,PowerSeries.coeff i f∈maximalIdeal A ^ (k - i):=by
 intro k
 induction k with
 | zero =>
  intro f;simp
 | succ k ih =>
  intro f;constructor
  ·
   intro hf;rw [pow_succ] at hf
   refine Submodule.mul_induction_on hf ?_ ?_
   ·
    intro a ha b hb i hi;rw [PowerSeries.coeff_mul]
    refine Ideal.sum_mem _ fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    by_cases hp2:p.2=0
    ·
     have hp1:p.1=i:=by omega
     rw [hp1,hp2]
     have hb0:PowerSeries.coeff 0 b∈maximalIdeal A:=by
      have:=(z3 b).mp hb;simpa using this
     by_cases hik:i < k
     ·
      have ha1:PowerSeries.coeff i a∈maximalIdeal A ^ (k - i):=(ih a).mp ha i hik;have q12:=mul_mem_mul ha1 hb0
      have q11:k+1 - i=(k - i)+1:=by omega
      rw [q11,pow_succ];exact q12
     ·
      have q7:i=k:=by omega
      rw [q7]
      have q11:k+1 - k=1:=by omega
      rw [q11,pow_one];exact (maximalIdeal A).mul_mem_left _ hb0
    ·
     have q5:p.1 < k:=by omega
     have ha1:PowerSeries.coeff p.1 a∈maximalIdeal A ^ (k - p.1):=(ih a).mp ha p.1 q5
     have hle:k+1 - i ≤ k - p.1:=by omega
     exact (maximalIdeal A ^ (k+1 - i)).mul_mem_right _ (pow_le_pow_right hle ha1)
   ·
    intro a b ha hb i hi;rw [map_add];exact Ideal.add_mem _ (ha i hi) (hb i hi)
  ·
   intro hf;let q10:PowerSeries A := ∑ i∈Finset.range (k+1),PowerSeries.C (PowerSeries.coeff i f)*PowerSeries.X ^ i
   have q0:q10∈maximalIdeal (PowerSeries A) ^ (k+1):=by
    refine Ideal.sum_mem _ fun i hi => ?_
    rw [Finset.mem_range] at hi;have hci:PowerSeries.coeff i f∈maximalIdeal A ^ (k+1 - i):=hf i hi
    have q4:PowerSeries.C (PowerSeries.coeff i f) ∈
      maximalIdeal (PowerSeries A) ^ (k+1 - i):=by
     have hle:(maximalIdeal A).map PowerSeries.C ≤ maximalIdeal (PowerSeries A):=by
      rw [map_le_iff_le_comap];intro a ha;rw [mem_comap,z3,PowerSeries.constantCoeff_C];exact ha
     have q3:((maximalIdeal A).map PowerSeries.C) ^ (k+1 - i) ≤ maximalIdeal (PowerSeries A) ^ (k+1 - i):=z7 hle _;rw [← Ideal.map_pow] at q3;exact q3 (mem_map_of_mem PowerSeries.C hci)
    have q6:(PowerSeries.X:PowerSeries A) ^ i∈maximalIdeal (PowerSeries A) ^ i:=Ideal.pow_mem_pow z4 i;have q12:=mul_mem_mul q4 q6;rw [← pow_add,Nat.sub_add_cancel (by omega)] at q12;exact q12
   have q1:∀ i < k+1,PowerSeries.coeff i (f - q10)=0:=fun i hi=>by
    rw [map_sub,map_sum]
    have q13 : ∑ j∈Finset.range (k+1),PowerSeries.coeff i (PowerSeries.C (PowerSeries.coeff j f)*PowerSeries.X ^ j)=PowerSeries.coeff i f:=by
     rw [Finset.sum_eq_single i]
     · rw [PowerSeries.coeff_C_mul_X_pow,if_pos rfl]
     ·
      intro j _ hji;rw [PowerSeries.coeff_C_mul_X_pow,if_neg (Ne.symm hji)]
     ·
      intro hni;exact absurd (Finset.mem_range.mpr hi) hni
    rw [q13,sub_self]
   have q2:f - q10∈maximalIdeal (PowerSeries A) ^ (k+1):=by
    have q8:=z6 (k+1) (f - q10) q1
    have hle:span {(PowerSeries.X:PowerSeries A) ^ (k+1)} ≤ maximalIdeal (PowerSeries A) ^ (k+1):=by
     rw [span_singleton_le_iff_mem];exact Ideal.pow_mem_pow z4 (k+1)
    exact hle q8
   have q9:f=q10+(f - q10):=by ring
   rw [q9];exact Ideal.add_mem _ q0 q2
lemma z9 {A:Type*} [CommRing A] [IsLocalRing A]
  [IsAdicComplete (maximalIdeal A) A] :
  IsAdicComplete (maximalIdeal (PowerSeries A)) (PowerSeries A):=by
 refine { haus' := ?_,prec' := ?_ }
 ·
  intro f hf;ext i
  refine IsHausdorff.haus' (I:=maximalIdeal A) (M:=A) (PowerSeries.coeff i f) fun r => ?_
  rw [SModEq.zero,smul_eq_mul,mul_top];have hfi:=hf (i+r+1);rw [SModEq.zero,smul_eq_mul,mul_top] at hfi;have q4:=(z8 (i+r+1) f).mp hfi i (by omega)
  have hle:r ≤ i+r+1 - i:=by omega
  exact pow_le_pow_right hle q4
 ·
  intro seq hseq
  have q0:∀ (i : ℕ) {a b : ℕ},a ≤ b →
    PowerSeries.coeff i (seq (a+i+1)) ≡ PowerSeries.coeff i (seq (b+i+1))
     [SMOD (maximalIdeal A ^ a•(⊤ : Submodule A A))]:=by
   intro i a b hab;rw [SModEq.sub_mem,smul_eq_mul,mul_top,← map_sub];have h1:=hseq (show a+i+1 ≤ b+i+1 by omega);rw [SModEq.sub_mem,smul_eq_mul,mul_top] at h1;have h2:=(z8 (a+i+1) _).mp h1 i (by omega)
   have hle:a ≤ a+i+1 - i:=by omega
   exact pow_le_pow_right hle h2
  let q2 : ℕ → A:=fun i =>
   (IsPrecomplete.prec' (I:=maximalIdeal A) (M:=A)
    (fun a=>PowerSeries.coeff i (seq (a+i+1))) (q0 i)).choose
  have q1:∀ i a,PowerSeries.coeff i (seq (a+i+1)) - q2 i∈maximalIdeal A ^ a:=fun i a=>by
   have h:=(IsPrecomplete.prec' (I:=maximalIdeal A) (M:=A)
    (fun a=>PowerSeries.coeff i (seq (a+i+1))) (q0 i)).choose_spec a
   rw [SModEq.sub_mem,smul_eq_mul,mul_top] at h;exact h
  let L:PowerSeries A:=PowerSeries.mk q2
  refine ⟨L,fun k => ?_⟩
  rw [SModEq.sub_mem,smul_eq_mul,mul_top,z8];intro i hi;rw [map_sub]
  have h1:PowerSeries.coeff i (seq k) - PowerSeries.coeff i (seq (k+i+1)) ∈
    maximalIdeal A ^ (k - i):=by
   rw [← map_sub];have hk:=hseq (show k ≤ k+i+1 by omega);rw [SModEq.sub_mem,smul_eq_mul,mul_top] at hk;exact (z8 k _).mp hk i hi
  have h2:PowerSeries.coeff i (seq (k+i+1)) - PowerSeries.coeff i L ∈
    maximalIdeal A ^ (k - i):=by
   simp only [L,PowerSeries.coeff_mk];exact pow_le_pow_right (Nat.sub_le k i) (q1 i k)
  have q3:PowerSeries.coeff i (seq k) - PowerSeries.coeff i L=(PowerSeries.coeff i (seq k) - PowerSeries.coeff i (seq (k+i+1)))+(PowerSeries.coeff i (seq (k+i+1)) - PowerSeries.coeff i L):=by ring
  rw [q3];exact Ideal.add_mem _ h1 h2
lemma z10 {A:Type*} [CommRing A] [IsRegularLocalRing A] :
  IsRegularLocalRing (PowerSeries A) ∧
   ringKrullDim (PowerSeries A)=ringKrullDim A+1:=by
 have q5:ringKrullDim A=((maximalIdeal A).spanFinrank:WithBot ℕ∞):=((isRegularLocalRing_iff A).mp ‹IsRegularLocalRing A›).symm
 have q1:(maximalIdeal (PowerSeries A)).spanFinrank ≤ (maximalIdeal A).spanFinrank+1:=by
  have h1:=PowerSeries.spanFinrank_le_spanFinrank_map_constantCoeff_add_one_of_X_mem
   (I:=maximalIdeal (PowerSeries A)) z4
  rwa [z5] at h1
 have q4:((maximalIdeal A).spanFinrank+1 : ℕ) ≤ ringKrullDim (PowerSeries A):=by
  have h1:=ringKrullDim_succ_le_ringKrullDim_powerseries (R:=A);rw [q5] at h1;simpa [Nat.cast_add,Nat.cast_one] using h1
 have q0:((maximalIdeal (PowerSeries A)).spanFinrank:WithBot ℕ∞) ≤
   ringKrullDim (PowerSeries A) :=
  (Nat.cast_le.mpr q1).trans q4
 have q6:IsRegularLocalRing (PowerSeries A):=IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ q0
 refine ⟨q6,?_⟩
 have q2:ringKrullDim (PowerSeries A) ≤ ((maximalIdeal A).spanFinrank+1 : ℕ):=(ringKrullDim_le_spanFinrank_maximalIdeal (PowerSeries A)).trans (Nat.cast_le.mpr q1);have q3:ringKrullDim (PowerSeries A)=((maximalIdeal A).spanFinrank+1 : ℕ):=le_antisymm q2 q4;rw [q3,q5];push_cast;rfl
instance instIsAdicCompleteIterPowerSeries (C:Type) [CommRing C] [IsLocalRing C]
  [IsAdicComplete (maximalIdeal C) C] :
  ∀ n : ℕ,IsAdicComplete (maximalIdeal (z0 C n)) (z0 C n)
 | 0=>inferInstanceAs (IsAdicComplete (maximalIdeal C) C)
 | n+1 =>
  let _:=instIsAdicCompleteIterPowerSeries C n
  z9
instance instIsRegularLocalRingIterPowerSeries (C:Type) [CommRing C] [IsRegularLocalRing C] :
  ∀ n : ℕ,IsRegularLocalRing (z0 C n)
 | 0=>inferInstanceAs (IsRegularLocalRing C)
 | n+1 =>
  let _:=instIsRegularLocalRingIterPowerSeries C n
  (z10 (A:=z0 C n)).1
lemma z11 (C:Type) [CommRing C] [IsRegularLocalRing C] :
  ∀ n : ℕ,ringKrullDim (z0 C n)=ringKrullDim C+(n:WithBot ℕ∞)
 | 0=>by
  change ringKrullDim C=ringKrullDim C+(0:WithBot ℕ∞);simp
 | n+1=>by
  have h1:=(z10 (A:=z0 C n)).2;have h2:=z11 C n;change ringKrullDim (PowerSeries (z0 C n))=_;rw [h1,h2];push_cast;rw [add_assoc]
lemma z12 {A R:Type*} [CommRing A] [IsLocalRing A]
  [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
  (f:A →+* R) (q9:∀ a∈maximalIdeal A,f a∈maximalIdeal R)
  {x:R} (hx:x∈maximalIdeal R) :
  ∃ f':PowerSeries A →+* R,(∀ a:A,f' (PowerSeries.C a)=f a)∧f' PowerSeries.X=x∧(∀ u∈maximalIdeal (PowerSeries A),f' u∈maximalIdeal R):=by
 let mk:(n : ℕ)→R →+* R⧸maximalIdeal R ^ n:=fun n=>Ideal.Quotient.mk _
 let q12:(n : ℕ)→PowerSeries A→R⧸maximalIdeal R ^ n:=fun n F =>
  ∑ i∈Finset.range n,mk n (f (PowerSeries.coeff i F)*x ^ i)
 have hxn:∀ n i,n ≤ i→mk n (x ^ i)=0:=fun n i hni=>by
  rw [Ideal.Quotient.eq_zero_iff_mem];exact pow_le_pow_right hni (Ideal.pow_mem_pow hx i)
 let g:(n : ℕ)→PowerSeries A →+* R⧸maximalIdeal R ^ n:=fun n =>
  {
   toFun:=q12 n
   map_zero':=by simp [q12]
   map_add':=fun F G=>by
    simp only [q12,map_add,add_mul,Finset.sum_add_distrib]
   map_one':=by
    cases n with
    | zero =>
     have : Subsingleton (R⧸maximalIdeal R ^ 0):=by
      rw [pow_zero];exact Ideal.Quotient.subsingleton_iff.mpr Ideal.one_eq_top
     exact Subsingleton.elim _ _
    | succ n =>
     dsimp only [q12];rw [Finset.sum_eq_single 0]
     · simp
     ·
      intro i _ hi0;simp [PowerSeries.coeff_one,hi0]
     ·
      intro h0;exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h0
   map_mul':=fun F G=>by
    dsimp only [q12]
    have q15 : ∑ i∈Finset.range n,mk n (f (PowerSeries.coeff i (F*G))*x ^ i) =
      ∑ i∈Finset.range n,∑ p∈Finset.HasAntidiagonal.antidiagonal i,mk n (f (PowerSeries.coeff p.1 F)*x ^ p.1)*mk n (f (PowerSeries.coeff p.2 G)*x ^ p.2):=by
     refine Finset.sum_congr rfl fun i _ => ?_
     rw [PowerSeries.coeff_mul,map_sum,Finset.sum_mul,map_sum]
     refine Finset.sum_congr rfl fun p hp => ?_
     rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp;rw [← map_mul,← hp,pow_add];congr 1;rw [map_mul];ring
    rw [q15,Finset.sum_mul];simp_rw [Finset.mul_sum]
    have q6 : ∑ a∈Finset.range n,∑ b∈Finset.range n,mk n (f (PowerSeries.coeff a F)*x ^ a)*mk n (f (PowerSeries.coeff b G)*x ^ b) =
      ∑ p∈(Finset.range n ×ˢ Finset.range n).filter (fun p=>p.1+p.2 < n),mk n (f (PowerSeries.coeff p.1 F)*x ^ p.1)*mk n (f (PowerSeries.coeff p.2 G)*x ^ p.2):=by
     rw [← Finset.sum_product']
     symm
     refine Finset.sum_subset (Finset.filter_subset _ _) fun p hp hpnot => ?_
     have hge:n ≤ p.1+p.2:=by
      by_contra hlt
      push Not at hlt
      exact hpnot (Finset.mem_filter.mpr ⟨hp,hlt⟩)
     rw [← map_mul]
     have q5:(f (PowerSeries.coeff p.1 F)*x ^ p.1)*(f (PowerSeries.coeff p.2 G)*x ^ p.2)=(f (PowerSeries.coeff p.1 F)*f (PowerSeries.coeff p.2 G))*x ^ (p.1+p.2):=by
      rw [pow_add];ring
     rw [q5,map_mul,hxn n (p.1+p.2) hge,mul_zero]
    rw [q6];rw [Finset.sum_sigma']
    refine Finset.sum_bij (fun q _=>q.2) ?_ ?_ ?_ ?_
    ·
     intro q hq;rw [Finset.mem_sigma,Finset.mem_range,Finset.HasAntidiagonal.mem_antidiagonal] at hq;rw [Finset.mem_filter,Finset.mem_product,Finset.mem_range,Finset.mem_range];exact ⟨⟨by omega,by omega⟩,by omega⟩
    ·
     intro q1 hq1 q2 hq2 heq;rw [Finset.mem_sigma,Finset.HasAntidiagonal.mem_antidiagonal] at hq1 hq2
     refine Sigma.ext ?_ (heq_of_eq heq)
     rw [← hq1.2,← hq2.2,heq]
    ·
     intro p hp;rw [Finset.mem_filter,Finset.mem_product,Finset.mem_range,Finset.mem_range] at hp
     refine ⟨⟨p.1+p.2,p⟩,?_,rfl⟩
     rw [Finset.mem_sigma,Finset.mem_range,Finset.HasAntidiagonal.mem_antidiagonal];exact ⟨hp.2,rfl⟩
    · intro _ _;rfl }
 have q0:∀ n F,Ideal.Quotient.factor (pow_le_pow_right n.le_succ) (g (n+1) F)=g n F:=by
  intro n F;change Ideal.Quotient.factor (pow_le_pow_right n.le_succ) (q12 (n+1) F)=q12 n F;dsimp only [q12];rw [Finset.sum_range_succ,map_add,map_sum]
  have q11:Ideal.Quotient.factor (pow_le_pow_right n.le_succ)
    (mk (n+1) (f (PowerSeries.coeff n F)*x ^ n))=0:=by
   change mk n (f (PowerSeries.coeff n F)*x ^ n)=0;rw [map_mul,hxn n n le_rfl,mul_zero]
  rw [q11,add_zero];rfl
 let q8:PowerSeries A → ℕ → R:=fun F n =>
  ∑ i∈Finset.range n,f (PowerSeries.coeff i F)*x ^ i
 have q4:∀ F n,mk n (q8 F n)=g n F:=fun F n=>by
  simp [q8,g,q12,mk]
 have q7:∀ F {a b : ℕ},a ≤ b→q8 F a ≡ q8 F b [SMOD (maximalIdeal R ^ a•(⊤ : Submodule R R))]:=by
  intro F a b hab;rw [SModEq.sub_mem,smul_eq_mul,mul_top,← Ideal.Quotient.eq_zero_iff_mem,map_sub,sub_eq_zero];change mk a (q8 F a)=mk a (q8 F b);rw [q4 F a]
  have q14:∀ {u v : ℕ} (huv:u ≤ v),Ideal.Quotient.factor (pow_le_pow_right huv) (g v F)=g u F:=by
   intro u v huv
   induction v,huv using Nat.le_induction with
   | base=>simp
   | succ v huv ih =>
    rw [← Ideal.Quotient.factor_comp_apply (pow_le_pow_right v.le_succ)
     (pow_le_pow_right huv),q0,ih]
  rw [← q14 hab,← q4 F b];rfl
 let toF:PowerSeries A→R:=fun F =>
  (IsPrecomplete.prec' (I:=maximalIdeal R) (M:=R) (q8 F) (q7 F)).choose
 have q3:∀ F n,mk n (toF F)=g n F:=fun F n=>by
  have hL:=(IsPrecomplete.prec' (I:=maximalIdeal R) (M:=R) (q8 F) (q7 F)).choose_spec n;rw [SModEq.sub_mem,smul_eq_mul,mul_top] at hL;have q13:mk n (q8 F n - toF F)=0:=Ideal.Quotient.eq_zero_iff_mem.mpr hL;rw [map_sub,sub_eq_zero,q4 F n] at q13;exact q13.symm
 let f':PowerSeries A →+* R :=
  {
   toFun:=toF
   map_one':=by
    refine sub_eq_zero.mp (IsHausdorff.haus' (I:=maximalIdeal R) (M:=R) (toF 1 - 1) fun n => ?_)
    rw [SModEq.zero,smul_eq_mul,mul_top,← Ideal.Quotient.eq_zero_iff_mem,map_sub];change mk n (toF 1) - mk n 1=0;rw [q3,map_one,map_one,sub_self]
   map_zero':=by
    refine IsHausdorff.haus' (I:=maximalIdeal R) (M:=R) (toF 0) fun n => ?_
    rw [SModEq.zero,smul_eq_mul,mul_top,← Ideal.Quotient.eq_zero_iff_mem];change mk n (toF 0)=0;rw [q3,map_zero]
   map_add':=fun F G=>by
    refine sub_eq_zero.mp (IsHausdorff.haus' (I:=maximalIdeal R) (M:=R)
     (toF (F+G) - (toF F+toF G)) fun n => ?_)
    rw [SModEq.zero,smul_eq_mul,mul_top,← Ideal.Quotient.eq_zero_iff_mem,map_sub,map_add];change mk n (toF (F+G)) - (mk n (toF F)+mk n (toF G))=0;rw [q3,q3,q3,map_add,sub_self]
   map_mul':=fun F G=>by
    refine sub_eq_zero.mp (IsHausdorff.haus' (I:=maximalIdeal R) (M:=R)
     (toF (F*G) - toF F*toF G) fun n => ?_)
    rw [SModEq.zero,smul_eq_mul,mul_top,← Ideal.Quotient.eq_zero_iff_mem,map_sub,map_mul];change mk n (toF (F*G)) - mk n (toF F)*mk n (toF G)=0
    rw [q3,q3,q3,map_mul,sub_self] }
 refine ⟨f',?_,?_,?_⟩
 ·
  intro a
  refine sub_eq_zero.mp (IsHausdorff.haus' (I:=maximalIdeal R) (M:=R) (f' (PowerSeries.C a) - f a) fun n => ?_)
  rw [SModEq.zero,smul_eq_mul,mul_top,← Ideal.Quotient.eq_zero_iff_mem,map_sub];change mk n (toF (PowerSeries.C a)) - mk n (f a)=0;rw [q3]
  cases n with
  | zero =>
   have : Subsingleton (R⧸maximalIdeal R ^ 0):=by
    rw [pow_zero];exact Ideal.Quotient.subsingleton_iff.mpr Ideal.one_eq_top
   exact Subsingleton.elim _ _
  | succ n =>
   change q12 (n+1) (PowerSeries.C a) - mk (n+1) (f a)=0;dsimp only [q12];rw [Finset.sum_eq_single 0]
   · simp
   ·
    intro i _ hi0;simp [PowerSeries.coeff_C,hi0]
   ·
    intro h0;exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h0
 ·
  refine sub_eq_zero.mp (IsHausdorff.haus' (I:=maximalIdeal R) (M:=R) (f' PowerSeries.X - x) fun n => ?_)
  rw [SModEq.zero,smul_eq_mul,mul_top,← Ideal.Quotient.eq_zero_iff_mem,map_sub];change mk n (toF PowerSeries.X) - mk n x=0;rw [q3]
  cases n with
  | zero =>
   have : Subsingleton (R⧸maximalIdeal R ^ 0):=by
    rw [pow_zero];exact Ideal.Quotient.subsingleton_iff.mpr Ideal.one_eq_top
   exact Subsingleton.elim _ _
  | succ n =>
   cases n with
   | zero =>
    change q12 1 PowerSeries.X - mk 1 x=0
    have hmx:mk 1 x=0:=by
     rw [Ideal.Quotient.eq_zero_iff_mem,pow_one];exact hx
    simp [q12,hmx]
   | succ n =>
    change q12 (n+2) PowerSeries.X - mk (n+2) x=0;dsimp only [q12];rw [Finset.sum_eq_single 1]
    · simp
    ·
     intro i _ hi1;simp [PowerSeries.coeff_X,hi1]
    ·
     intro h1;exact absurd (Finset.mem_range.mpr (by omega)) h1
 ·
  intro u hu;have q10:mk 1 (toF u)=g 1 u:=q3 u 1
  have hg1:g 1 u=0:=by
   change q12 1 u=0;simp only [q12,Finset.sum_range_one,pow_zero,mul_one,PowerSeries.coeff_zero_eq_constantCoeff];rw [Ideal.Quotient.eq_zero_iff_mem,pow_one];exact q9 _ ((z3 u).mp hu)
  have h0:mk 1 (f' u)=0:=q10.trans hg1;rw [Ideal.Quotient.eq_zero_iff_mem,pow_one] at h0;exact h0
noncomputable def z13 (C:Type) [CommRing C] :
  ∀ n : ℕ,C →+* z0 C n
 | 0=>RingHom.id C
 | n+1=>(PowerSeries.C (R:=z0 C n)).comp (z13 C n)
noncomputable def z14 (C:Type) [CommRing C] :
  ∀ {n : ℕ},Fin n→z0 C n
 | 0,i=>Fin.elim0 i
 | n+1,i =>
  Fin.lastCases (PowerSeries.X:PowerSeries (z0 C n))
   (fun j=>PowerSeries.C (z14 C j)) i
noncomputable def z15 {C D:Type} [CommRing C] [CommRing D] (f:C →+* D) :
  ∀ n : ℕ,z0 C n →+* z0 D n
 | 0=>f
 | n+1=>PowerSeries.map (z15 f n)
lemma z16 (C:Type) [CommRing C] :
  ∀ n : ℕ,Injective (z13 C n)
 | 0=>Function.injective_id
 | n+1=>(PowerSeries.C_injective (R:=z0 C n)).comp (z16 C n)
lemma z17 {C:Type} [CommRing C] [IsLocalRing C] :
  ∀ (n : ℕ) {c:C},c∈maximalIdeal C→z13 C n c∈maximalIdeal (z0 C n)
 | 0,_,hc=>hc
 | n+1,_,hc=>by
  change PowerSeries.C (z13 C n _)∈maximalIdeal (PowerSeries (z0 C n));rw [z3,PowerSeries.constantCoeff_C];exact z17 n hc
lemma z18 {C:Type} [CommRing C] [IsLocalRing C] :
  ∀ {n : ℕ} (i:Fin n),z14 C i∈maximalIdeal (z0 C n)
 | 0,i=>Fin.elim0 i
 | n+1,i=>by
  refine Fin.lastCases ?_ ?_ i
  ·
   simp only [z14,Fin.lastCases_last];exact z4
  ·
   intro j;simp only [z14,Fin.lastCases_castSucc];rw [z3,PowerSeries.constantCoeff_C];exact z18 j
lemma z19 {C D:Type} [CommRing C] [CommRing D] (f:C →+* D) :
  ∀ (n : ℕ) (c:C),z15 f n (z13 C n c)=z13 D n (f c)
 | 0,_=>rfl
 | n+1,c=>by
  change PowerSeries.map (z15 f n) (PowerSeries.C (z13 C n c))=PowerSeries.C (z13 D n (f c));rw [PowerSeries.map_C,z19 f n c]
lemma z20 {C D:Type} [CommRing C] [CommRing D] (f:C →+* D) :
  ∀ {n : ℕ} (i:Fin n),z15 f n (z14 C i)=z14 D i
 | 0,i=>Fin.elim0 i
 | n+1,i=>by
  refine Fin.lastCases ?_ ?_ i
  ·
   simp only [z14,Fin.lastCases_last,z15];exact PowerSeries.map_X (z15 f n)
  ·
   intro j;simp only [z14,Fin.lastCases_castSucc,z15];rw [PowerSeries.map_C,z20 f j]
lemma z21 {C D:Type} [CommRing C] [CommRing D] {f:C →+* D}
  (hf:Injective f) :
  ∀ n : ℕ,Injective (z15 f n)
 | 0=>hf
 | n+1=>by
  intro a b hab;ext k;have hk:=congrArg (PowerSeries.coeff k) hab;change z15 f n (PowerSeries.coeff k a)=z15 f n (PowerSeries.coeff k b) at hk;exact z21 hf n hk
lemma z22 {C D:Type} [CommRing C] [CommRing D] {f:C →+* D}
  (hf:Surjective f) :
  ∀ n : ℕ,Surjective (z15 f n)
 | 0=>hf
 | n+1=>by
  intro b;have ih:=z22 hf n
  refine ⟨PowerSeries.mk fun k=>(ih (PowerSeries.coeff k b)).choose,?_⟩
  ext k;simp only [z15,PowerSeries.coeff_map,PowerSeries.coeff_mk];exact (ih (PowerSeries.coeff k b)).choose_spec
lemma z23 {C D:Type} [CommRing C] [IsLocalRing C] [CommRing D] [IsLocalRing D]
  {f:C →+* D} (hf:∀ c∈maximalIdeal C,f c∈maximalIdeal D) :
  ∀ (n : ℕ) {x:z0 C n},x∈maximalIdeal (z0 C n)→z15 f n x∈maximalIdeal (z0 D n)
 | 0,_,hx=>hf _ hx
 | n+1,x,hx=>by
  change PowerSeries.map (z15 f n) x∈maximalIdeal (PowerSeries (z0 D n));rw [z3];have hx0:PowerSeries.constantCoeff x∈maximalIdeal (z0 C n):=(z3 x).mp hx
  have q0:PowerSeries.constantCoeff (PowerSeries.map (z15 f n) x)=z15 f n (PowerSeries.constantCoeff x):=by
   rw [← PowerSeries.coeff_zero_eq_constantCoeff,PowerSeries.coeff_map,PowerSeries.coeff_zero_eq_constantCoeff]
  rw [q0];exact z23 hf n hx0
lemma z24 {C R:Type} [CommRing C] [IsLocalRing C]
  [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
  (phi:C →+* R) (q0:∀ c∈maximalIdeal C,phi c∈maximalIdeal R) :
  ∀ (n : ℕ) (xs:Fin n→R),(∀ i,xs i∈maximalIdeal R) →
   ∃ f:z0 C n →+* R,(∀ c:C,f (z13 C n c)=phi c)∧(∀ i:Fin n,f (z14 C i)=xs i)∧(∀ u∈maximalIdeal (z0 C n),f u∈maximalIdeal R):=by
 intro n
 induction n with
 | zero =>
  intro xs _
  exact ⟨phi,fun _=>rfl,fun i=>Fin.elim0 i,q0⟩
 | succ n ih =>
  intro xs hxs
  obtain ⟨f0,hf0_C,hf0_var,hf0_loc⟩:=ih (fun j:Fin n=>xs j.castSucc) (fun j=>hxs j.castSucc)
  obtain ⟨f1,hf1_C,hf1_X,hf1_loc⟩:=z12 f0 hf0_loc (hxs (Fin.last n))
  refine ⟨f1,?_,?_,hf1_loc⟩
  ·
   intro c;change f1 (PowerSeries.C (z13 C n c))=phi c;rw [hf1_C,hf0_C]
  ·
   intro i
   refine Fin.lastCases ?_ ?_ i
   ·
    simp only [z14,Fin.lastCases_last];exact hf1_X
   ·
    intro j;simp only [z14,Fin.lastCases_castSucc];rw [hf1_C,hf0_var]
lemma z25 {S:Type*} [CommRing S] [IsNoetherianRing S] (I:Ideal S) :
  RingHom.ker (PowerSeries.map (Ideal.Quotient.mk I))=I.map (PowerSeries.C (R:=S)):=by
 refine le_antisymm ?_ ?_
 ·
  intro f hf;rw [RingHom.mem_ker] at hf
  have q0:∀ k : ℕ,PowerSeries.coeff k f∈I:=fun k=>by
   have hk:=congrArg (PowerSeries.coeff k) hf;rw [PowerSeries.coeff_map,map_zero,Ideal.Quotient.eq_zero_iff_mem] at hk;exact hk
  obtain ⟨T,hT⟩:=IsNoetherian.noetherian I
  have q2:∀ k : ℕ,∃ c:T→S,∑ t:T,c t*(t:S)=PowerSeries.coeff k f:=fun k=>by
   have h1:PowerSeries.coeff k f∈Submodule.span S (T:Set S):=hT▸q0 k;rw [Submodule.mem_span_finset] at h1;obtain ⟨g,_,hg⟩:=h1
   refine ⟨fun t=>g t.1,?_⟩
   simpa [smul_eq_mul] using (Finset.sum_coe_sort T (fun x=>g x*x)).trans hg
  let ps:T→PowerSeries S:=fun t=>PowerSeries.mk fun k=>(q2 k).choose t
  have q1:f = ∑ t:T,ps t*PowerSeries.C (t:S):=by
   ext k;rw [map_sum]
   have q3 : ∑ t:T,PowerSeries.coeff k (ps t*PowerSeries.C (t:S)) = ∑ t:T,(q2 k).choose t*(t:S):=by
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [PowerSeries.coeff_mul_C];simp [ps]
   rw [q3,(q2 k).choose_spec]
  rw [q1]
  refine Ideal.sum_mem _ fun t _ => ?_
  refine Ideal.mul_mem_left _ _ ?_
  exact mem_map_of_mem PowerSeries.C (hT▸subset_span t.2)
 ·
  rw [map_le_iff_le_comap];intro a ha;rw [mem_comap,RingHom.mem_ker,PowerSeries.map_C];have ha0:Ideal.Quotient.mk I a=0:=Ideal.Quotient.eq_zero_iff_mem.mpr ha;rw [ha0,map_zero]
lemma z26 {S:Type} [CommRing S] [IsNoetherianRing S] (I:Ideal S) :
  ∀ n : ℕ,RingHom.ker (z15 (Ideal.Quotient.mk I) n)=I.map (z13 S n)
 | 0=>by
  change RingHom.ker (Ideal.Quotient.mk I)=I.map (RingHom.id S);rw [mk_ker,Ideal.map_id]
 | n+1=>by
  let _:=instIsNoetherianRingIterPowerSeries S n;let g:=z15 (Ideal.Quotient.mk I) n;have q0:Surjective g:=z22 Ideal.Quotient.mk_surjective n;have q3:RingHom.ker g=I.map (z13 S n):=z26 I n;let J:Ideal (z0 S n):=I.map (z13 S n);let eQ:(z0 S n⧸J) ≃+* z0 (S⧸I) n:=(Ideal.quotEquivOfEq q3.symm).trans (RingHom.quotientKerEquivOfSurjective q0)
  have q4:g=eQ.toRingHom.comp (Ideal.Quotient.mk J):=by
   ext x;rfl
  change RingHom.ker (PowerSeries.map g)=I.map ((PowerSeries.C).comp (z13 S n));rw [← Ideal.map_map,q4]
  have q1:PowerSeries.map (eQ.toRingHom.comp (Ideal.Quotient.mk J))=(PowerSeries.map eQ.toRingHom).comp (PowerSeries.map (Ideal.Quotient.mk J)):=by
   ext f k;simp [PowerSeries.coeff_map]
  rw [q1];ext f;rw [RingHom.mem_ker,RingHom.comp_apply]
  have q2:Injective (PowerSeries.map eQ.toRingHom):=by
   intro a b hab;ext k;have hk:=congrArg (PowerSeries.coeff k) hab;rw [PowerSeries.coeff_map,PowerSeries.coeff_map] at hk;exact eQ.injective hk
  rw [map_eq_zero_iff _ q2,← RingHom.mem_ker,z25 J]
noncomputable def z27 {S:Type} [CommRing S] [IsNoetherianRing S] (I:Ideal S) (n : ℕ) :
  (z0 S n⧸I.map (z13 S n)) ≃+* z0 (S⧸I) n :=
 (Ideal.quotEquivOfEq (z26 I n).symm).trans
  (RingHom.quotientKerEquivOfSurjective (z22 Ideal.Quotient.mk_surjective n))
noncomputable def z28 {A B:Type*} [CommRing A] [CommRing B]
  (f:A →+* B) (c:B) (k : ℕ) (hc:c ^ k=0) :
  PowerSeries A →+* B where
 toFun F := ∑ i∈Finset.range k,f (PowerSeries.coeff i F)*c ^ i
 map_zero':=by simp
 map_add' F G:=by simp [map_add,add_mul,Finset.sum_add_distrib]
 map_one':=by
  cases k with
  | zero =>
   rw [pow_zero] at hc;have : Subsingleton B:=subsingleton_of_zero_eq_one hc.symm;exact Subsingleton.elim _ _
  | succ k =>
   rw [Finset.sum_eq_single 0]
   · simp
   · intro i _ hi0;simp [PowerSeries.coeff_one,hi0]
   · intro h0;exact absurd (Finset.mem_range.mpr (Nat.succ_pos k)) h0
 map_mul' F G:=by
  have hcn:∀ m,k ≤ m→c ^ m=0:=fun m hm=>by
   rw [← Nat.add_sub_of_le hm,pow_add,hc,zero_mul]
  have q4 : ∑ i∈Finset.range k,f (PowerSeries.coeff i (F*G))*c ^ i =
    ∑ i∈Finset.range k,∑ p∈Finset.HasAntidiagonal.antidiagonal i,(f (PowerSeries.coeff p.1 F)*c ^ p.1)*(f (PowerSeries.coeff p.2 G)*c ^ p.2):=by
   refine Finset.sum_congr rfl fun i _ => ?_
   rw [PowerSeries.coeff_mul,map_sum,Finset.sum_mul]
   refine Finset.sum_congr rfl fun p hp => ?_
   rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp;rw [← hp,pow_add,map_mul];ring
  rw [q4,Finset.sum_mul];simp_rw [Finset.mul_sum]
  have q0 : ∑ a∈Finset.range k,∑ b∈Finset.range k,(f (PowerSeries.coeff a F)*c ^ a)*(f (PowerSeries.coeff b G)*c ^ b) =
    ∑ p∈(Finset.range k ×ˢ Finset.range k).filter (fun p=>p.1+p.2 < k),(f (PowerSeries.coeff p.1 F)*c ^ p.1)*(f (PowerSeries.coeff p.2 G)*c ^ p.2):=by
   rw [← Finset.sum_product']
   symm
   refine Finset.sum_subset (Finset.filter_subset _ _) fun p hp hpnot => ?_
   have hge:k ≤ p.1+p.2:=by
    by_contra hlt;push Not at hlt
    exact hpnot (Finset.mem_filter.mpr ⟨hp,hlt⟩)
   have q3:(f (PowerSeries.coeff p.1 F)*c ^ p.1)*(f (PowerSeries.coeff p.2 G)*c ^ p.2)=(f (PowerSeries.coeff p.1 F)*f (PowerSeries.coeff p.2 G))*c ^ (p.1+p.2):=by
    rw [pow_add];ring
   rw [q3,hcn _ hge,mul_zero]
  rw [q0,Finset.sum_sigma']
  refine Finset.sum_bij (fun q _=>q.2) ?_ ?_ ?_ ?_
  ·
   intro q hq;rw [Finset.mem_sigma,Finset.mem_range,Finset.HasAntidiagonal.mem_antidiagonal] at hq;rw [Finset.mem_filter,Finset.mem_product,Finset.mem_range,Finset.mem_range];exact ⟨⟨by omega,by omega⟩,by omega⟩
  ·
   intro q1 hq1 q2 hq2 heq;rw [Finset.mem_sigma,Finset.HasAntidiagonal.mem_antidiagonal] at hq1 hq2
   refine Sigma.ext ?_ (heq_of_eq heq)
   rw [← hq1.2,← hq2.2,heq]
  ·
   intro p hp;rw [Finset.mem_filter,Finset.mem_product,Finset.mem_range,Finset.mem_range] at hp
   refine ⟨⟨p.1+p.2,p⟩,?_,rfl⟩
   rw [Finset.mem_sigma,Finset.mem_range,Finset.HasAntidiagonal.mem_antidiagonal];exact ⟨hp.2,rfl⟩
  · intro _ _;rfl
lemma z29 {A B:Type*} [CommRing A] [CommRing B]
  (f:A →+* B) (c:B) (k : ℕ) (hc:c ^ k=0) (a:A) :
  z28 f c k hc (PowerSeries.C a)=f a:=by
 cases k with
 | zero =>
  rw [pow_zero] at hc;have : Subsingleton B:=subsingleton_of_zero_eq_one hc.symm;exact Subsingleton.elim _ _
 | succ k =>
  change ∑ i∈Finset.range (k+1),f (PowerSeries.coeff i (PowerSeries.C a))*c ^ i=f a;rw [Finset.sum_eq_single 0]
  · simp
  · intro i _ hi0;simp [PowerSeries.coeff_C,hi0]
  · intro h0;exact absurd (Finset.mem_range.mpr (Nat.succ_pos k)) h0
lemma z30 {A B:Type*} [CommRing A] [CommRing B]
  (f:A →+* B) (c:B) (k : ℕ) (hc:c ^ k=0) :
  z28 f c k hc PowerSeries.X=c:=by
 cases k with
 | zero =>
  rw [pow_zero] at hc;have : Subsingleton B:=subsingleton_of_zero_eq_one hc.symm;exact Subsingleton.elim _ _
 | succ k =>
  cases k with
  | zero =>
   rw [pow_one] at hc;change ∑ i∈Finset.range 1,f (PowerSeries.coeff i PowerSeries.X)*c ^ i=c;simp [hc]
  | succ k =>
   change ∑ i∈Finset.range (k+2),f (PowerSeries.coeff i PowerSeries.X)*c ^ i=c;rw [Finset.sum_eq_single 1]
   · simp
   · intro i _ hi1;simp [PowerSeries.coeff_X,hi1]
   · intro h1;exact absurd (Finset.mem_range.mpr (by omega)) h1
lemma z31 {A B:Type*} [CommRing A] [CommRing B]
    (g₁ g₂ : PowerSeries A →+* B)
    (hC:∀ a:A,g₁ (PowerSeries.C a)=g₂ (PowerSeries.C a))
    (hX:g₁ PowerSeries.X=g₂ PowerSeries.X)
    {k : ℕ} (q1:g₁ PowerSeries.X ^ k=0) :
    g₁ = g₂ := by
  ext F;let q2:PowerSeries A := ∑ i∈Finset.range k,PowerSeries.C (PowerSeries.coeff i F)*PowerSeries.X ^ i
  have q0:∀ i < k,PowerSeries.coeff i (F - q2)=0:=fun i hi=>by
    rw [map_sub,map_sum]
    have q3 : ∑ j∈Finset.range k,PowerSeries.coeff i (PowerSeries.C (PowerSeries.coeff j F)*PowerSeries.X ^ j)=PowerSeries.coeff i F:=by
      rw [Finset.sum_eq_single i]
      · rw [PowerSeries.coeff_C_mul_X_pow,if_pos rfl]
      · intro j _ hji;rw [PowerSeries.coeff_C_mul_X_pow,if_neg (Ne.symm hji)]
      · intro hni;exact absurd (Finset.mem_range.mpr hi) hni
    rw [q3,sub_self]
  obtain ⟨q,hq⟩:=mem_span_singleton.mp
    (z6 k (F - q2) q0)
  have hF:F=q2+PowerSeries.X ^ k*q:=by
    calc F=q2+(F - q2):=by ring
      _=q2+PowerSeries.X ^ k*q:=by rw [hq]
  rw [hF,map_add,map_add,map_mul,map_mul,map_pow,map_pow,q1,← hX,q1,zero_mul,zero_mul,add_zero,add_zero];simp only [q2,map_sum,map_mul,map_pow,hC,hX]
lemma z32 {C B:Type} [CommRing C] [CommRing B] :
  ∀ {n : ℕ} (g₁ g₂ : z0 C n →+* B),(∀ c:C,g₁ (z13 C n c)=g₂ (z13 C n c))→(∀ i:Fin n,g₁ (z14 C i)=g₂ (z14 C i))→(∀ i:Fin n,∃ k : ℕ,g₁ (z14 C i) ^ k=0) → g₁ = g₂
 | 0,g₁,g₂,hC,_,_=>RingHom.ext hC
 | n+1,g₁,g₂,hC,hvar,hnilp=>by
  let g₁':z0 C n →+* B:=g₁.comp PowerSeries.C;let g₂':z0 C n →+* B:=g₂.comp PowerSeries.C
  have q2:g₁'=g₂':=z32 g₁' g₂'
   (fun c=>hC c)
   (fun j=>by simpa [g₁',g₂',z14] using hvar j.castSucc)
   (fun j=>by simpa [g₁',z14] using hnilp j.castSucc)
  obtain ⟨k,hk⟩:=hnilp (Fin.last n)
  have q1:g₁ (PowerSeries.X:PowerSeries (z0 C n))=g₂ (PowerSeries.X:PowerSeries (z0 C n)):=by
   simpa [z14] using hvar (Fin.last n)
  have q0:g₁ (PowerSeries.X:PowerSeries (z0 C n)) ^ k=0:=by
   simpa [z14] using hk
  exact z31 g₁ g₂ (fun a=>RingHom.congr_fun q2 a) q1 q0
lemma z33 {C B:Type} [CommRing C] [CommRing B]
  (f:C →+* B) :
  ∀ (n : ℕ) (cs:Fin n→B),(∀ i,∃ k : ℕ,cs i ^ k=0) →
   ∃ g:z0 C n →+* B,(∀ c:C,g (z13 C n c)=f c)∧(∀ i:Fin n,g (z14 C i)=cs i):=by
 intro n
 induction n with
 | zero =>
  intro cs _
  exact ⟨f,fun _=>rfl,fun i=>Fin.elim0 i⟩
 | succ n ih =>
  intro cs hcs
  obtain ⟨g0,hg0_C,hg0_var⟩:=ih (fun j=>cs j.castSucc) (fun j=>hcs j.castSucc)
  obtain ⟨k,hk⟩:=hcs (Fin.last n)
  refine ⟨z28 g0 (cs (Fin.last n)) k hk,?_,?_⟩
  ·
   intro c;change z28 g0 (cs (Fin.last n)) k hk (PowerSeries.C (z13 C n c))=f c;rw [z29,hg0_C]
  ·
   intro i
   refine Fin.lastCases ?_ ?_ i
   ·
    simp only [z14,Fin.lastCases_last];exact z30 g0 (cs (Fin.last n)) k hk
   ·
    intro j;simp only [z14,Fin.lastCases_castSucc];rw [z29,hg0_var]
lemma z34 {C:Type} [CommRing C] [IsLocalRing C] :
  ∀ n : ℕ,maximalIdeal (z0 C n)=(maximalIdeal C).map (z13 C n)⊔span (Set.range (z14 C (n:=n)))
 | 0=>by
  change maximalIdeal C=(maximalIdeal C).map (RingHom.id C)⊔span (Set.range _);rw [Ideal.map_id,Set.range_eq_empty,Ideal.span_empty,sup_bot_eq]
 | n+1=>by
  refine le_antisymm ?_ ?_
  ·
   intro f hf;have hf0:PowerSeries.constantCoeff f∈maximalIdeal (z0 C n):=(z3 f).mp hf
   have q1:f - PowerSeries.C (PowerSeries.constantCoeff f) ∈
     span {(PowerSeries.X:PowerSeries (z0 C n))}:=by
    have h1:=z6 1
     (f - PowerSeries.C (PowerSeries.constantCoeff f)) (fun i hi=>by
      have hi0:i=0:=by omega
      subst hi0
      simp)
    simpa using h1
   have q2:PowerSeries.C (PowerSeries.constantCoeff f) ∈
     (maximalIdeal C).map (z13 C (n+1))⊔span (Set.range (z14 C (n:=n+1))):=by
    rw [z34 n] at hf0
    have q3:PowerSeries.C (PowerSeries.constantCoeff f) ∈
      ((maximalIdeal C).map (z13 C n)⊔span (Set.range (z14 C (n:=n)))).map PowerSeries.C :=
     mem_map_of_mem PowerSeries.C hf0
    rw [Ideal.map_sup,Ideal.map_map] at q3
    have q6:(maximalIdeal C).map (PowerSeries.C.comp (z13 C n))⊔(span (Set.range (z14 C (n:=n)))).map PowerSeries.C ≤ (maximalIdeal C).map (z13 C (n+1))⊔span (Set.range (z14 C (n:=n+1))):=by
     refine sup_le_sup le_rfl ?_
     rw [map_span,span_le];rintro _ ⟨_,⟨j,rfl⟩,rfl⟩;exact subset_span ⟨j.castSucc,by simp [z14]⟩
    exact q6 q3
   have q4:(PowerSeries.X:PowerSeries (z0 C n)) ∈
     (maximalIdeal C).map (z13 C (n+1))⊔span (Set.range (z14 C (n:=n+1))) :=
    mem_sup_right (subset_span ⟨Fin.last n,by simp [z14]⟩)
   have q0:f - PowerSeries.C (PowerSeries.constantCoeff f) ∈
     (maximalIdeal C).map (z13 C (n+1))⊔span (Set.range (z14 C (n:=n+1))) :=
    (span_singleton_le_iff_mem _).mpr q4 q1
   have q5:=Ideal.add_mem _ q2 q0;simpa using q5
  ·
   refine sup_le ?_ ?_
   ·
    rw [map_le_iff_le_comap];intro c hc;exact z17 (n+1) hc
   ·
    rw [span_le];rintro _ ⟨i,rfl⟩;exact z18 i
lemma z35 {C:Type} [CommRing C] [IsLocalRing C] :
  ∀ n : ℕ,Surjective ((residue (z0 C n)).comp (z13 C n))
 | 0=>residue_surjective
 | n+1=>by
  intro y;obtain ⟨f,rfl⟩:=residue_surjective y
  have q2:f - PowerSeries.C (PowerSeries.constantCoeff f) ∈
    maximalIdeal (PowerSeries (z0 C n)):=by
   rw [z3,map_sub,PowerSeries.constantCoeff_C,sub_self];exact (maximalIdeal _).zero_mem
  obtain ⟨c,hc⟩:=z35 n (residue _ (PowerSeries.constantCoeff f))
  have q0:PowerSeries.constantCoeff f - z13 C n c∈maximalIdeal (z0 C n):=by
   rw [← residue_eq_zero_iff,map_sub]
   change residue _ (PowerSeries.constantCoeff f) -
    ((residue _).comp (z13 C n)) c=0
   rw [hc,sub_self]
  refine ⟨c,?_⟩
  change residue _ (PowerSeries.C (z13 C n c))=residue _ f
  symm
  rw [← sub_eq_zero,← map_sub,residue_eq_zero_iff]
  have q1:f - PowerSeries.C (z13 C n c)=(f - PowerSeries.C (PowerSeries.constantCoeff f))+PowerSeries.C (PowerSeries.constantCoeff f - z13 C n c):=by
   rw [map_sub];ring
  rw [q1]
  refine (maximalIdeal _).add_mem q2 ?_
  rw [z3,PowerSeries.constantCoeff_C];exact q0
end BasicIterPowerSeries
section DimensionInequality
lemma z36 {S:Type*} [CommRing S] [IsLocalRing S]
  (I:Ideal S) [Nontrivial (S⧸I)] : IsLocalRing (S⧸I) :=
 IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
lemma z37 {A B:Type*} [CommRing A] [CommRing B]
  [Algebra A B] [Algebra.IsIntegral A B] (q0:Injective (algebraMap A B)) :
  ringKrullDim B=ringKrullDim A:=by
 have q1:ringKrullDim B ≤ ringKrullDim A:=by
  rw [ringKrullDim,ringKrullDim,Order.krullDim,Order.krullDim]
  refine iSup_le fun c => ?_
  let c':LTSeries (PrimeSpectrum A) :=
   {
    length:=c.length
    toFun:=fun i=>PrimeSpectrum.comap (algebraMap A B) (c i)
    step:=fun i=>IsIntegral.comap_lt_comap (c.step i) }
  exact le_iSup (fun s:LTSeries (PrimeSpectrum A)=>(s.length:WithBot ℕ∞)) c'
 have q2:ringKrullDim A ≤ ringKrullDim B:=by
  rw [ringKrullDim,ringKrullDim,Order.krullDim,Order.krullDim]
  refine iSup_le fun c => ?_
  obtain ⟨Q₀,_,hQ₀_prime,hQ₀_over⟩ :=
   Ideal.exists_ideal_over_prime_of_isIntegral (c 0).asIdeal (⊥ : Ideal B)
    (by
     rw [← RingHom.ker_eq_comap_bot,(RingHom.injective_iff_ker_eq_bot _).mp q0]
     exact bot_le)
  have : Q₀.IsPrime:=hQ₀_prime;have : Q₀.LiesOver (RelSeries.head c).asIdeal:=⟨hQ₀_over.symm⟩;obtain ⟨cB,hcB_len,_,_⟩:=Ideal.exists_ltSeries_of_hasGoingUp (R:=A) (S:=B) c Q₀;rw [← hcB_len]
  exact le_iSup (fun s:LTSeries (PrimeSpectrum B)=>(s.length:WithBot ℕ∞)) cB
 exact le_antisymm q1 q2
lemma z38 {A:Type*} [CommRing A] [IsDomain A]
  [IsLocalRing A] [IsNoetherianRing A] {I:Ideal A} (q4:I ≠ ⊥) (q3:I ≠ ⊤) :
  ringKrullDim (A⧸I) < ringKrullDim A:=by
 obtain ⟨r,hr⟩ :=
  ringKrullDim_quotient_eq_natCast
   I q3
 obtain ⟨n,hn⟩ :=
  ringKrullDim_quotient_eq_natCast
   (⊥ : Ideal A) bot_ne_top
 have q5:ringKrullDim A=(n:WithBot ℕ∞):=by
  rw [← ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot A),hn]
 have hkd:Order.krullDim (PrimeSpectrum.zeroLocus (I:Set A))=(r:WithBot ℕ∞):=by
  rw [← ringKrullDim_quotient,hr]
 obtain ⟨c,hc⟩ :=
  exists_ltSeries_of_krullDim_eq_natCast
   hkd
 have q0:(⟨⊥,Ideal.isPrime_bot⟩ : PrimeSpectrum A) < (c 0).1:=by
  refine lt_of_le_of_ne bot_le fun heq=>q4 ?_
  have hle:I ≤ (c 0).1.asIdeal:=(c 0).2;rw [← heq] at hle;exact le_bot_iff.mp hle
 let c':LTSeries (PrimeSpectrum A) :=
  {
   length:=c.length+1
   toFun:=Fin.cons ⟨⊥,Ideal.isPrime_bot⟩ (fun i=>(c i).1)
   step:=fun i=>by
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using q0
    · simpa using c.step j }
 have q2:(c'.length:WithBot ℕ∞) ≤ ringKrullDim A:=by
  rw [ringKrullDim,Order.krullDim]
  exact le_iSup (fun s:LTSeries (PrimeSpectrum A)=>(s.length:WithBot ℕ∞)) c'
 rw [hr,q5]
 have q6:c'.length=r+1:=by simp [c',hc]
 rw [q6,q5] at q2
 have hnat:r+1 ≤ n:=by exact_mod_cast q2
 have q1:r < n:=by omega
 exact_mod_cast q1
lemma z39 :
  ∀ (r : ℕ) (D:Type) [CommRing D] [IsLocalRing D] [IsNoetherianRing D],
   ringKrullDim D=(r:WithBot ℕ∞) →
   ∃ us:Fin r→D,(∀ i,us i∈maximalIdeal D)∧(span (Set.range us)).radical=maximalIdeal D:=by
 intro r
 induction r with
 | zero =>
  intro D _ _ _ hdim
  refine ⟨Fin.elim0,fun i=>Fin.elim0 i,?_⟩
  rw [Set.range_eq_empty,Ideal.span_empty]
  refine le_antisymm ?_ ?_
  ·
   rw [← (maximalIdeal.isMaximal D).isPrime.radical];exact Ideal.radical_mono bot_le
  ·
   rw [Ideal.radical_eq_sInf,le_sInf_iff];intro P ⟨_,hP⟩;have hzero:Ring.KrullDimLE 0 D:=(Ring.krullDimLE_iff (n:=0) (R:=D)).mpr (by rw [hdim]);have q23:P.IsMaximal:=Ideal.isMaximal_iff_isPrime.mpr hP;rw [eq_maximalIdeal q23]
 | succ r ih =>
  intro D _ _ _ hdim;have q22:(minimalPrimes D).Finite:=Ideal.finite_minimalPrimes_of_isNoetherianRing D ⊥
  have q6 : ¬ ((maximalIdeal D:Set D) ⊆ ⋃ p∈minimalPrimes D,(p:Set D)):=by
   intro q19
   obtain ⟨p,hp_mem,hle⟩:=(Ideal.subset_union_prime_finite q22 ⊥ ⊥ fun q hq _ _=>hq.1.1).mp q19
   have q14:p=maximalIdeal D:=le_antisymm (le_maximalIdeal hp_mem.1.1.ne_top) hle
   have q15:ringKrullDim D ≤ 0:=by
    rw [ringKrullDim,Order.krullDim]
    refine iSup_le fun c => ?_
    by_cases hlen:c.length=0
    · simp [hlen]
    ·
     exfalso;have q13:(c 0).asIdeal < (c ⟨1,by omega⟩).asIdeal:=c.strictMono (by simp [Fin.lt_def]);obtain ⟨q,hq_min,hq_le⟩:=Ideal.exists_minimalPrimes_le (I := ⊥) (J:=(c 0).asIdeal) bot_le;have q3:q ≤ maximalIdeal D:=le_maximalIdeal hq_min.1.1.ne_top
     have q17:q=maximalIdeal D:=by
      have q18:q ≤ p:=q14.symm▸q3;have q7:p ≤ q:=hp_mem.2 ⟨hq_min.1.1,bot_le⟩ q18;exact q14▸le_antisymm q18 q7
     have q16:(c 0).asIdeal=maximalIdeal D:=le_antisymm (le_maximalIdeal (c 0).isPrime.ne_top) (q17▸hq_le);have q12:(c ⟨1,by omega⟩).asIdeal ≤ maximalIdeal D:=le_maximalIdeal (c ⟨1,by omega⟩).isPrime.ne_top;rw [q16] at q13;exact not_lt_of_ge q12 q13
   rw [hdim] at q15
   have : r+1 ≤ 0:=by exact_mod_cast q15
   omega
  obtain ⟨u0,hu0_mem,hu0_not⟩:=Set.not_subset.mp q6
  have q1:∀ p∈(annihilator D D).minimalPrimes,u0∉p:=by
   intro p hp hmem
   have q21:annihilator D D = ⊥ := by
    ext x;simp only [Module.mem_annihilator,Submodule.mem_bot]
    exact ⟨fun h=>by simpa using h 1,fun h y=>by simp [h]⟩
   rw [q21] at hp;exact hu0_not (Set.mem_biUnion hp hmem)
  have q10:span {u0} ≠ ⊤ :=
   ne_top_of_le_ne_top (maximalIdeal.isMaximal D).ne_top
    ((span_singleton_le_iff_mem _).mpr hu0_mem)
  have q4:ringKrullDim (D⧸span {u0})=(r:WithBot ℕ∞):=by
   have h1:=Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal
    (R:=D) (M:=D) q1 hu0_mem
   have hsp:span {u0} = (u0•(⊤ : Ideal D)):=by
    ext x;simp only [mem_span_singleton,Submodule.mem_smul_pointwise_iff_exists,Submodule.mem_top,true_and,smul_eq_mul,dvd_def]
    exact ⟨fun ⟨a,ha⟩=>⟨a,ha.symm⟩,fun ⟨a,ha⟩=>⟨a,ha.symm⟩⟩
   rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquivAlgOfEq D hsp).toRingEquiv];rw [Module.supportDim_self_eq_ringKrullDim,hdim] at h1;have q11:(u0•(⊤ : Ideal D)) ≠ ⊤ := hsp▸q10
   obtain ⟨m,hm⟩ :=
    ringKrullDim_quotient_eq_natCast
     (u0•(⊤ : Ideal D)) q11
   have hsd:supportDim D (QuotSMulTop u0 D)=ringKrullDim (D⧸(u0•(⊤ : Ideal D))):=Module.supportDim_quotient_eq_ringKrullDim (R:=D) (I:=u0•(⊤ : Ideal D));rw [hsd,hm] at h1;rw [hm]
   have hnat:m+1=r+1:=by exact_mod_cast h1
   have : m=r:=by omega
   exact_mod_cast this
  let D':=D⧸span {u0};have : Nontrivial D':=Ideal.Quotient.nontrivial_iff.mpr q10;have : IsLocalRing D':=z36 (span {u0});obtain ⟨us',hus'_mem,hus'_rad⟩:=ih D' q4
  let q8:Fin r→D:=fun j=>(Ideal.Quotient.mk_surjective (us' j)).choose
  have q0:∀ j,Ideal.Quotient.mk (span {u0}) (q8 j)=us' j:=fun j=>(Ideal.Quotient.mk_surjective (us' j)).choose_spec
  have q2:(maximalIdeal D').comap (Ideal.Quotient.mk (span {u0}))=maximalIdeal D :=
   eq_maximalIdeal
    (comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
  let us:Fin (r+1)→D:=Fin.cons u0 q8
  refine ⟨us,?_,?_⟩
  ·
   intro i
   refine Fin.cases hu0_mem (fun j => ?_) i
   change q8 j∈maximalIdeal D;rw [← q2,mem_comap,q0 j];exact hus'_mem j
  ·
   refine le_antisymm ?_ ?_
   ·
    rw [← (maximalIdeal.isMaximal D).isPrime.radical]
    refine Ideal.radical_mono (span_le.mpr ?_)
    rintro _ ⟨i,rfl⟩
    refine Fin.cases hu0_mem (fun j => ?_) i
    change q8 j∈maximalIdeal D;rw [← q2,mem_comap,q0 j];exact hus'_mem j
   ·
    intro x hx
    have hx':Ideal.Quotient.mk (span {u0}) x∈maximalIdeal D':=by
     rw [← q2] at hx;exact hx
    rw [← hus'_rad] at hx';obtain ⟨k,hk⟩:=hx';rw [← map_pow] at hk
    have q5:span (Set.range us')=(span (Set.range us)).map (Ideal.Quotient.mk (span {u0})):=by
     rw [map_span]
     refine le_antisymm (span_le.mpr ?_) (span_le.mpr ?_)
     ·
      rintro _ ⟨j,rfl⟩;exact subset_span ⟨us j.succ,⟨j.succ,rfl⟩,q0 j⟩
     ·
      rintro _ ⟨_,⟨i,rfl⟩,rfl⟩
      refine Fin.cases ?_ (fun j => ?_) i
      ·
       change Ideal.Quotient.mk (span {u0}) u0∈span (Set.range us');have h0:Ideal.Quotient.mk (span {u0}) u0=0:=Ideal.Quotient.eq_zero_iff_mem.mpr (subset_span rfl);rw [h0];exact Ideal.zero_mem _
      ·
       change Ideal.Quotient.mk (span {u0}) (q8 j)∈span (Set.range us');rw [q0 j];exact subset_span ⟨j,rfl⟩
    rw [q5,mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hk;obtain ⟨y,hy_span,hy_eq⟩:=hk
    have q19:x ^ k - y∈span {u0}:=by
     rw [← Ideal.Quotient.eq_zero_iff_mem,map_sub,hy_eq,sub_self]
    have q9:span {u0} ≤ span (Set.range us):=(span_singleton_le_iff_mem _).mpr (subset_span ⟨0,rfl⟩)
    refine ⟨k,?_⟩
    have q20:=Ideal.add_mem _ hy_span (q9 q19);simpa using q20
lemma z40 {B D:Type*} [CommRing B] [IsLocalRing B]
  [IsNoetherianRing B] [IsAdicComplete (maximalIdeal B) B]
  [CommRing D] [IsLocalRing D] [IsNoetherianRing D]
  [Algebra B D] (q22:∀ b∈maximalIdeal B,algebraMap B D b∈maximalIdeal D)
  (q17:Surjective ((residue D).comp (algebraMap B D)))
  (q20:((maximalIdeal B).map (algebraMap B D)).radical=maximalIdeal D) :
  Module.Finite B D:=by
 let I:Ideal D:=(maximalIdeal B).map (algebraMap B D)
 have q13:∃ N : ℕ,maximalIdeal D ^ N ≤ I:=by
  have hfg:(maximalIdeal D).FG:=IsNoetherian.noetherian _;have hle:maximalIdeal D ≤ I.radical:=q20.symm.le;exact Ideal.exists_pow_le_of_le_radical_of_fg hle hfg
 obtain ⟨N,hN⟩:=q13
 have q3:∀ k : ℕ,∃ S:Finset D,
   ((maximalIdeal D ^ k:Ideal D).restrictScalars B) ≤ Submodule.span B (S:Set D)⊔((maximalIdeal D ^ (k+1) : Ideal D).restrictScalars B):=by
  intro k;obtain ⟨T,hT⟩:=IsNoetherian.noetherian (maximalIdeal D ^ k)
  refine ⟨T,?_⟩
  intro x hx;have hx':x∈Submodule.span D (T:Set D):=hT▸hx;rw [Submodule.mem_span_finset] at hx';obtain ⟨g,_,rfl⟩:=hx'
  refine Submodule.sum_mem _ fun t ht => ?_
  obtain ⟨b,hb⟩:=q17 (residue D (g t))
  have q15:g t - algebraMap B D b∈maximalIdeal D:=by
   rw [← residue_eq_zero_iff,map_sub];change residue D (g t) - ((residue D).comp (algebraMap B D)) b=0;rw [hb,sub_self]
  have q8:g t•t=b•t+(g t - algebraMap B D b)*t:=by
   simp only [smul_eq_mul,Algebra.smul_def];ring
  rw [q8]
  refine Submodule.add_mem _ ?_ ?_
  · exact Submodule.mem_sup_left (Submodule.smul_mem _ b (Submodule.subset_span ht))
  ·
   refine Submodule.mem_sup_right ?_
   change (g t - algebraMap B D b)*t∈maximalIdeal D ^ (k+1);rw [pow_succ'];exact mul_mem_mul q15 (hT▸subset_span ht)
 have q2:∀ k : ℕ,∃ S:Finset D,
   (⊤ : Submodule B D) ≤ Submodule.span B (S:Set D)⊔((maximalIdeal D ^ k:Ideal D).restrictScalars B):=by
  intro k
  induction k with
  | zero =>
   refine ⟨∅,fun x _=>Submodule.mem_sup_right ?_⟩
   change x∈maximalIdeal D ^ 0;rw [pow_zero,Ideal.one_eq_top];exact Submodule.mem_top
  | succ k ih =>
   obtain ⟨S1,hS1⟩:=ih;obtain ⟨S2,hS2⟩:=q3 k
   classical
   refine ⟨S1 ∪ S2,fun x _ => ?_⟩
   obtain ⟨a,ha,y,hy,hxy⟩:=Submodule.mem_sup.mp (hS1 (Submodule.mem_top:x∈(⊤ : Submodule B D)));obtain ⟨b,hb,z,hz,hyz⟩:=Submodule.mem_sup.mp (hS2 hy)
   have q11:x=(a+b)+z:=by rw [← hxy,← hyz,add_assoc]
   rw [q11]
   refine Submodule.add_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right hz)
   exact Submodule.add_mem _
    (Submodule.span_mono (Finset.coe_subset.mpr Finset.subset_union_left) ha)
    (Submodule.span_mono (Finset.coe_subset.mpr Finset.subset_union_right) hb)
 obtain ⟨S,hS⟩:=q2 N
 have q9:∀ x:D,x∈Submodule.span B (S:Set D)⊔(I.restrictScalars B):=fun x=>by
  obtain ⟨a,ha,y,hy,hxy⟩:=Submodule.mem_sup.mp (hS (Submodule.mem_top:x∈(⊤ : Submodule B D)));rw [← hxy];exact Submodule.add_mem _ (Submodule.mem_sup_left ha) (Submodule.mem_sup_right (hN hy))
 obtain ⟨G,hG⟩:=IsNoetherian.noetherian (maximalIdeal B)
 have q7:∀ k : ℕ,∀ x∈I ^ k,
   ∃ c:S→B,(∀ s,c s∈maximalIdeal B ^ k)∧x - ∑ s:S,c s•(s:D)∈I ^ (k+1):=by
  intro k
  induction k with
  | zero =>
   intro x _;obtain ⟨a,ha,y,hy,hxy⟩:=Submodule.mem_sup.mp (q9 x);rw [Submodule.mem_span_finset] at ha;obtain ⟨f,_,rfl⟩:=ha
   refine ⟨fun s=>f s.1,fun _=>by simp,?_⟩
   have q19 : ∑ s:S,f s.1•(s:D) = ∑ s∈S,f s•s:=Finset.sum_coe_sort S (fun s=>f s•s)
   rw [q19,← hxy,add_sub_cancel_left,pow_one];exact hy
  | succ k ih =>
   intro x hx;rw [pow_succ] at hx
   refine Submodule.mul_induction_on hx ?_ ?_
   ·
    intro a ha b hb
    have hb':b∈Submodule.span D (Set.range (fun g:G=>algebraMap B D (g:B))):=by
     have q16:I=span (Set.range (fun g:G=>algebraMap B D (g:B))):=by
      dsimp only [I];rw [← hG,map_span];congr 1;ext y;simp
     rw [q16] at hb;exact hb
    rw [Submodule.mem_span_range_iff_exists_fun] at hb';obtain ⟨u,hu⟩:=hb'
    have q12:∀ g:G,∃ c:S→B,(∀ s,c s∈maximalIdeal B ^ k)∧a*u g - ∑ s:S,c s•(s:D)∈I ^ (k+1):=fun g =>
     ih (a*u g) ((I ^ k).mul_mem_right (u g) ha)
    let c:S→B:=fun s => ∑ g:G,(q12 g).choose s*(g:B)
    refine ⟨c,?_,?_⟩
    ·
     intro s
     refine Ideal.sum_mem _ fun g _ => ?_
     rw [pow_succ];exact mul_mem_mul ((q12 g).choose_spec.1 s) (hG▸subset_span g.2)
    ·
     have hab:a*b = ∑ g:G,(a*u g)*algebraMap B D (g:B):=by
      rw [← hu,Finset.mul_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      simp [smul_eq_mul,mul_assoc]
     have q10 : ∑ s:S,c s•(s:D) = ∑ g:G,(∑ s:S,(q12 g).choose s•(s:D))*algebraMap B D (g:B):=by
      simp only [c,Finset.sum_smul];rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [Algebra.smul_def,map_mul];ring
     rw [hab,q10,← Finset.sum_sub_distrib]
     refine Ideal.sum_mem _ fun g _ => ?_
     rw [← sub_mul,pow_succ]
     exact mul_mem_mul ((q12 g).choose_spec.2)
      (mem_map_of_mem (algebraMap B D) (hG▸subset_span g.2))
   ·
    intro a b ⟨ca,hca_mem,hca_diff⟩ ⟨cb,hcb_mem,hcb_diff⟩
    refine ⟨fun s=>ca s+cb s,fun s=>Ideal.add_mem _ (hca_mem s) (hcb_mem s),?_⟩
    simp only [add_smul,Finset.sum_add_distrib]
    have q8:a+b - (∑ s:S,ca s•(s:D) + ∑ s:S,cb s•(s:D))=(a - ∑ s:S,ca s•(s:D))+(b - ∑ s:S,cb s•(s:D)):=by ring
    rw [q8];exact Ideal.add_mem _ hca_diff hcb_diff
 have q1:I ≤ maximalIdeal D:=map_le_iff_le_comap.mpr q22
 refine ⟨⟨S,?_⟩⟩
 rw [eq_top_iff];intro x _
 let step:(k : ℕ)→{ p:S→B // x - ∑ s:S,p s•(s:D)∈I ^ k } →
   { p:S→B // x - ∑ s:S,p s•(s:D)∈I ^ (k+1) }:=fun k prev =>
  let c:=(q7 k (x - ∑ s:S,prev.1 s•(s:D)) prev.2).choose
  ⟨fun s=>prev.1 s+c s,by
   have q15:=(q7 k (x - ∑ s:S,prev.1 s•(s:D)) prev.2).choose_spec.2;simp only [add_smul,Finset.sum_add_distrib]
   have q8:x - (∑ s:S,prev.1 s•(s:D) + ∑ s:S,c s•(s:D))=(x - ∑ s:S,prev.1 s•(s:D)) - ∑ s:S,c s•(s:D):=by ring
   rw [q8]
   exact q15⟩
 let seq:(k : ℕ)→{ p:S→B // x - ∑ s:S,p s•(s:D)∈I ^ k }:=Nat.rec ⟨fun _=>0,by simp⟩ step
 have q0:∀ (k : ℕ) (s:S),(seq (k+1)).1 s - (seq k).1 s∈maximalIdeal B ^ k :=
  fun k s=>by
   change ((seq k).1 s+(q7 k _ (seq k).2).choose s) - (seq k).1 s∈maximalIdeal B ^ k;rw [add_sub_cancel_left];exact (q7 k _ (seq k).2).choose_spec.1 s
 have q6:∀ (s:S) {a b : ℕ},a ≤ b→(seq a).1 s ≡ (seq b).1 s [SMOD (maximalIdeal B ^ a•(⊤ : Submodule B B))]:=by
  intro s a b hab;rw [SModEq.sub_mem,smul_eq_mul,mul_top]
  induction b,hab using Nat.le_induction with
  | base=>simp
  | succ b hab ih =>
   have h1:(seq a).1 s - (seq (b+1)).1 s=((seq a).1 s - (seq b).1 s) - ((seq (b+1)).1 s - (seq b).1 s):=by ring
   rw [h1];exact Ideal.sub_mem _ ih (pow_le_pow_right hab (q0 b s))
 let q21:S→B:=fun s =>
  (IsPrecomplete.prec' (I:=maximalIdeal B) (M:=B) (fun k=>(seq k).1 s) (q6 s)).choose
 have q14:∀ (s:S) (k : ℕ),(seq k).1 s - q21 s∈maximalIdeal B ^ k:=fun s k=>by
  have h:=(IsPrecomplete.prec' (I:=maximalIdeal B) (M:=B)
   (fun k=>(seq k).1 s) (q6 s)).choose_spec k
  rw [SModEq.sub_mem,smul_eq_mul,mul_top] at h;exact h
 have q11:x = ∑ s:S,q21 s•(s:D):=by
  refine sub_eq_zero.mp ?_
  have q5:x - ∑ s:S,q21 s•(s:D) ∈
    ⨅ k : ℕ,(maximalIdeal D ^ k•(⊤ : Submodule D D)):=by
   rw [Submodule.mem_iInf];intro k;rw [smul_eq_mul,mul_top]
   refine z7 q1 k ?_
   have q8:x - ∑ s:S,q21 s•(s:D)=(x - ∑ s:S,(seq k).1 s•(s:D)) + ∑ s:S,((seq k).1 s - q21 s)•(s:D):=by
    simp only [sub_smul,Finset.sum_sub_distrib];ring
   rw [q8]
   refine Ideal.add_mem _ (seq k).2 (Ideal.sum_mem _ fun s _ => ?_)
   rw [Algebra.smul_def]
   refine (I ^ k).mul_mem_right (s:D) ?_
   have q4:(algebraMap B D) ((seq k).1 s - q21 s) ∈
     (maximalIdeal B ^ k).map (algebraMap B D) :=
    mem_map_of_mem (algebraMap B D) (q14 s k)
   rwa [Ideal.map_pow] at q4
  have q18:=Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (R:=D) (M:=D)
   (maximalIdeal D) (maximalIdeal.isMaximal D).ne_top
  rw [q18] at q5;exact q5
 rw [q11]
 exact Submodule.sum_mem _ fun s _=>Submodule.smul_mem _ (q21 s) (Submodule.subset_span s.2)
lemma z41 (K:Type*) [Field K]
  (V W:Type*) [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [Nontrivial V] [Nontrivial W] :
  Nontrivial (V ⊗[K] W):=by
 obtain ⟨u,hu⟩:=exists_ne (0:V);obtain ⟨v,hv⟩:=exists_ne (0:W);let bV:=Module.Basis.ofVectorSpace K V;let bW:=Module.Basis.ofVectorSpace K W
 have q0:∃ i,bV.repr u i≠0:=by
  by_contra h;push Not at h
  exact hu (bV.repr.injective (by ext i;simp [h i]))
 obtain ⟨i,hi⟩:=q0
 have q1:∃ j,bW.repr v j≠0:=by
  by_contra h;push Not at h
  exact hv (bW.repr.injective (by ext j;simp [h j]))
 obtain ⟨j,hj⟩:=q1
 let B:V ⊗[K] W →ₗ[K] K :=
  TensorProduct.lift (LinearMap.mk₂ K (fun x y=>bV.coord i x*bW.coord j y)
   (fun _ _ _=>by simp [add_mul])
   (fun _ _ _=>by simp [mul_assoc])
   (fun _ _ _=>by simp [mul_add])
   (fun _ _ _=>by simp [mul_left_comm]))
 refine ⟨⟨u ⊗ₜ[K] v,0,fun h => ?_⟩⟩
 have hB:B (u ⊗ₜ[K] v)=B 0:=congrArg B h;simp only [B,TensorProduct.lift.tmul,LinearMap.mk₂_apply,map_zero,mul_eq_zero] at hB
 rcases hB with h1 | h2
 · exact hi h1
 · exact hj h2
lemma z42 {B₁ D₁ K:Type*}
  [CommRing B₁] [IsDomain B₁] [CommRing D₁] [Field K]
  [Algebra B₁ D₁] [Algebra B₁ K]
  (hD:Injective (algebraMap B₁ D₁))
  (hK:Injective (algebraMap B₁ K)) :
  Nontrivial (K ⊗[B₁] D₁):=by
 let K₁ := FractionRing B₁
 let q1:K₁ →+* K:=IsLocalization.lift (M:=nonZeroDivisors B₁) (g:=algebraMap B₁ K)
  (fun y=>by
   have hy0:(y:B₁)≠0:=nonZeroDivisors.ne_zero y.2
   exact isUnit_iff_ne_zero.mpr fun h0=>hy0 (hK (by simpa using h0)))
 let _:Algebra K₁ K:=q1.toAlgebra
 have : IsScalarTower B₁ K₁ K:=IsScalarTower.of_algebraMap_eq fun b=>by
  change algebraMap B₁ K b=q1 (algebraMap B₁ K₁ b);exact (IsLocalization.lift_eq _ b).symm
 have q0:Injective ((Algebra.linearMap B₁ D₁).lTensor K₁):=Module.Flat.lTensor_preserves_injective_linearMap (Algebra.linearMap B₁ D₁) hD
 have hK₁D_nt:Nontrivial (K₁ ⊗[B₁] D₁):=by
  refine ⟨⟨1 ⊗ₜ[B₁] 1,0,fun h => ?_⟩⟩
  have h0:((Algebra.linearMap B₁ D₁).lTensor K₁) (1 ⊗ₜ[B₁] 1)=((Algebra.linearMap B₁ D₁).lTensor K₁) 0:=by
   simpa [LinearMap.lTensor_tmul] using h
  have h10:(1:K₁) ⊗ₜ[B₁] (1:B₁)=0:=q0 h0;let e:=TensorProduct.rid B₁ K₁;have h1:e (1 ⊗ₜ[B₁] 1)=e 0:=congrArg e h10;simp only [e,TensorProduct.rid_tmul,one_smul,map_zero] at h1;exact one_ne_zero h1
 let e:K ⊗[B₁] D₁ ≃ₗ[K₁] K ⊗[K₁] (K₁ ⊗[B₁] D₁):=(TensorProduct.AlgebraTensorModule.cancelBaseChange B₁ K₁ K₁ K D₁).symm;exact e.toEquiv.nontrivial_congr.mpr (z41 K₁ K (K₁ ⊗[B₁] D₁))
lemma z43 {S:Type*} [CommRing S] [IsLocalRing S]
  [IsNoetherianRing S] [IsAdicComplete (maximalIdeal S) S] (I:Ideal S)
  [IsLocalRing (S⧸I)] :
  IsAdicComplete (maximalIdeal (S⧸I)) (S⧸I):=by
 have q1:maximalIdeal (S⧸I)=(maximalIdeal S).map (Ideal.Quotient.mk I):=by
  have q4:(maximalIdeal (S⧸I)).comap (Ideal.Quotient.mk I)=maximalIdeal S:=eq_maximalIdeal (comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective);rw [← q4,Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
 refine { haus' := ?_,prec' := ?_ }
 ·
  intro x hx
  have q6:x ∈ ⨅ k : ℕ,(maximalIdeal (S⧸I) ^ k•(⊤ : Submodule (S⧸I) (S⧸I))):=by
   rw [Submodule.mem_iInf];intro k;simpa [SModEq.zero] using hx k
  have q7:=Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (R:=S⧸I) (M:=S⧸I)
   (maximalIdeal (S⧸I)) (maximalIdeal.isMaximal (S⧸I)).ne_top
  rw [q7] at q6;exact q6
 ·
  intro seq hseq
  have q5:∀ k : ℕ,∃ d:S,d∈maximalIdeal S ^ k∧Ideal.Quotient.mk I d=seq (k+1) - seq k:=fun k=>by
   have hk:=hseq (Nat.le_succ k);rw [SModEq.sub_mem,smul_eq_mul,mul_top,q1,← Ideal.map_pow,mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hk;obtain ⟨d,hd,hdeq⟩:=hk
   refine ⟨-d,(maximalIdeal S ^ k).neg_mem hd,?_⟩
   rw [map_neg,hdeq,neg_sub]
  let a0:S:=(Ideal.Quotient.mk_surjective (seq 0)).choose;have ha0:Ideal.Quotient.mk I a0=seq 0:=(Ideal.Quotient.mk_surjective (seq 0)).choose_spec
  let q3 : ℕ → S:=fun k=>a0 + ∑ j∈Finset.range k,(q5 j).choose
  have q0:∀ k : ℕ,Ideal.Quotient.mk I (q3 k)=seq k:=fun k=>by
   induction k with
   | zero=>simp [q3,ha0]
   | succ k ih =>
    dsimp only [q3] at ih ⊢;rw [Finset.sum_range_succ,← add_assoc,map_add,ih,(q5 k).choose_spec.2];ring
  have q2:∀ {a b : ℕ},a ≤ b→q3 a ≡ q3 b [SMOD (maximalIdeal S ^ a•(⊤ : Submodule S S))]:=by
   intro a b hab;rw [SModEq.sub_mem,smul_eq_mul,mul_top]
   induction b,hab using Nat.le_induction with
   | base=>simp
   | succ b hab ih =>
    have h1:q3 a - q3 (b+1)=(q3 a - q3 b) - (q5 b).choose:=by
     dsimp only [q3];rw [Finset.sum_range_succ];ring
    rw [h1];exact Ideal.sub_mem _ ih (pow_le_pow_right hab (q5 b).choose_spec.1)
  obtain ⟨L,hL⟩:=IsPrecomplete.prec' (I:=maximalIdeal S) (M:=S) q3 q2
  refine ⟨Ideal.Quotient.mk I L,fun k => ?_⟩
  rw [SModEq.sub_mem,smul_eq_mul,mul_top,q1,← Ideal.map_pow,← q0 k,← map_sub];have hLk:=hL k;rw [SModEq.sub_mem,smul_eq_mul,mul_top] at hLk;exact mem_map_of_mem (Ideal.Quotient.mk I) hLk
set_option maxHeartbeats 800000 in
lemma z44 {Λ : Type} [CommRing Λ] [IsRegularLocalRing Λ] [IsDomain Λ]
  [IsAdicComplete (maximalIdeal Λ) Λ]
  (n : ℕ) (P Q:Ideal (z0 Λ n)) [P.IsPrime] [Q.IsPrime]
  (r' s' : ℕ)
  (u:Fin r'→z0 Λ n) (q25:∀ i,u i∈maximalIdeal (z0 Λ n))
  (v:Fin s'→z0 Λ n) (q18:∀ j,v j∈maximalIdeal (z0 Λ n))
  (q21:((maximalIdeal Λ).map (z13 Λ n)⊔span (Set.range u)⊔P).radical=maximalIdeal (z0 Λ n))
  (q24:((maximalIdeal Λ).map (z13 Λ n)⊔span (Set.range v)⊔Q).radical=maximalIdeal (z0 Λ n))
  (q12:∀ f:z0 Λ r' →+* (z0 Λ n⧸P),(∀ c,f (z13 Λ r' c)=Ideal.Quotient.mk P (z13 Λ n c))→(∀ i,f (z14 Λ i)=Ideal.Quotient.mk P (u i))→Injective f)
  (q14:∀ f:z0 Λ s' →+* (z0 Λ n⧸Q),(∀ c,f (z13 Λ s' c)=Ideal.Quotient.mk Q (z13 Λ n c))→(∀ j,f (z14 Λ j)=Ideal.Quotient.mk Q (v j))→Injective f) :
  let R:=z0 Λ n;let T:=z0 R n;let i₁ : R →+* T:=z15 (z13 Λ n) n;let i₂ : R →+* T:=z13 R n
  ringKrullDim Λ + (s':WithBot ℕ∞)+(r':WithBot ℕ∞) ≤
   ringKrullDim (T⧸(P.map i₁ ⊔ Q.map i₂)):=by
 intro R T i₁ i₂;let I:Ideal T:=P.map i₁ ⊔ Q.map i₂
 have q4:I ≤ maximalIdeal T:=by
  refine sup_le ?_ ?_
  ·
   rw [map_le_iff_le_comap];intro x hx
   exact z23 (fun c hc=>z17 n hc) n
    (le_maximalIdeal ‹P.IsPrime›.ne_top hx)
  ·
   rw [map_le_iff_le_comap];intro x hx;exact z17 n (le_maximalIdeal ‹Q.IsPrime›.ne_top hx)
 have q3:I ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal T).ne_top q4;let A:=T⧸I;have : Nontrivial A:=Ideal.Quotient.nontrivial_iff.mpr q3;have : IsLocalRing A:=z36 I;have : IsLocalRing (R⧸P):=z36 P;have : IsLocalRing (R⧸Q):=z36 Q;have : IsAdicComplete (maximalIdeal A) A:=z43 I;have : IsAdicComplete (maximalIdeal (R⧸P)) (R⧸P):=z43 P
 have : IsAdicComplete (maximalIdeal (R⧸Q)) (R⧸Q):=z43 Q;have q1:(maximalIdeal (R⧸P)).comap (Ideal.Quotient.mk P)=maximalIdeal R:=eq_maximalIdeal (comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective);have q2:(maximalIdeal (R⧸Q)).comap (Ideal.Quotient.mk Q)=maximalIdeal R:=eq_maximalIdeal (comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
 have q0:(maximalIdeal A).comap (Ideal.Quotient.mk I)=maximalIdeal T:=eq_maximalIdeal (comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective);let B₁ := z0 Λ r';let B₂ := z0 Λ s';let B:=z0 B₂ r'
 obtain ⟨f₁,hf₁_C,hf₁_var,hf₁_loc⟩ :=
  z24 (C := Λ) (R:=R⧸P)
   ((Ideal.Quotient.mk P).comp (z13 Λ n))
   (fun c hc=>by
    rw [RingHom.comp_apply,← mem_comap,q1]
    exact z17 n hc)
   r' (fun i=>Ideal.Quotient.mk P (u i))
   (fun i=>by rw [← mem_comap,q1];exact q25 i)
 obtain ⟨f₂,hf₂_C,hf₂_var,hf₂_loc⟩ :=
  z24 (C := Λ) (R:=R⧸Q)
   ((Ideal.Quotient.mk Q).comp (z13 Λ n))
   (fun c hc=>by
    rw [RingHom.comp_apply,← mem_comap,q2]
    exact z17 n hc)
   s' (fun j=>Ideal.Quotient.mk Q (v j))
   (fun j=>by rw [← mem_comap,q2];exact q18 j)
 have hf₁_inj:Injective f₁ := q12 f₁ hf₁_C hf₁_var;have hf₂_inj:Injective f₂ := q14 f₂ hf₂_C hf₂_var;let j₁ : B₁ →+* B:=z15 (z13 Λ s') r';let j₂ : B₂ →+* B:=z13 B₂ r';have hj₁_inj:Injective j₁ := z21 (z16 Λ s') r';have hj₂_inj:Injective j₂ := z16 B₂ r'
 obtain ⟨β₂,hβ₂_C,hβ₂_var,hβ₂_loc⟩ :=
  z24 (C := Λ) (R:=A)
   (((Ideal.Quotient.mk I).comp i₂).comp (z13 Λ n))
   (fun c hc=>by
    rw [RingHom.comp_apply,RingHom.comp_apply,← mem_comap,q0]
    exact z17 n (z17 n hc))
   s' (fun j=>Ideal.Quotient.mk I (i₂ (v j)))
   (fun j=>by
    rw [← mem_comap,q0]
    exact z17 n (q18 j))
 obtain ⟨β,hβ_C,hβ_var,hβ_loc⟩ :=
  z24 (C:=B₂) (R:=A) β₂ hβ₂_loc
   r' (fun i=>Ideal.Quotient.mk I (i₁ (u i)))
   (fun i=>by
    rw [← mem_comap,q0]
    exact z23 (fun c hc=>z17 n hc) n (q25 i))
 have hrad₁ : ((maximalIdeal B₁).map f₁).radical=maximalIdeal (R⧸P):=by
  refine le_antisymm ?_ ?_
  ·
   rw [← (maximalIdeal.isMaximal (R⧸P)).isPrime.radical];exact Ideal.radical_mono (map_le_iff_le_comap.mpr hf₁_loc)
  ·
   intro x hx;obtain ⟨y,rfl⟩:=Ideal.Quotient.mk_surjective x;have hy:y∈maximalIdeal R:=q1▸hx;rw [← q21] at hy;obtain ⟨k,hk⟩:=hy
   refine ⟨k,?_⟩
   rw [← map_pow]
   have q13:((maximalIdeal Λ).map (z13 Λ n)⊔span (Set.range u)⊔P).map
     (Ideal.Quotient.mk P) ≤ (maximalIdeal B₁).map f₁ := by
    rw [Ideal.map_sup,Ideal.map_sup]
    refine sup_le (sup_le ?_ ?_) ?_
    ·
     rw [map_le_iff_le_comap,map_le_iff_le_comap];intro c hc;rw [mem_comap,mem_comap];have q35:Ideal.Quotient.mk P (z13 Λ n c)=f₁ (z13 Λ r' c):=(hf₁_C c).symm;rw [q35];exact mem_map_of_mem f₁ (z17 r' hc)
    ·
     rw [map_span,span_le];rintro _ ⟨_,⟨i,rfl⟩,rfl⟩;rw [← hf₁_var i];exact mem_map_of_mem f₁ (z18 i)
    ·
     rw [map_le_iff_le_comap];intro p hp;rw [mem_comap,Ideal.Quotient.eq_zero_iff_mem.mpr hp];exact Ideal.zero_mem _
   exact q13 (mem_map_of_mem (Ideal.Quotient.mk P) hk)
 have hrad₂ : ((maximalIdeal B₂).map f₂).radical=maximalIdeal (R⧸Q):=by
  refine le_antisymm ?_ ?_
  ·
   rw [← (maximalIdeal.isMaximal (R⧸Q)).isPrime.radical];exact Ideal.radical_mono (map_le_iff_le_comap.mpr hf₂_loc)
  ·
   intro x hx;obtain ⟨y,rfl⟩:=Ideal.Quotient.mk_surjective x;have hy:y∈maximalIdeal R:=q2▸hx;rw [← q24] at hy;obtain ⟨k,hk⟩:=hy
   refine ⟨k,?_⟩
   rw [← map_pow]
   have q13:((maximalIdeal Λ).map (z13 Λ n)⊔span (Set.range v)⊔Q).map
     (Ideal.Quotient.mk Q) ≤ (maximalIdeal B₂).map f₂ := by
    rw [Ideal.map_sup,Ideal.map_sup]
    refine sup_le (sup_le ?_ ?_) ?_
    ·
     rw [map_le_iff_le_comap,map_le_iff_le_comap];intro c hc;rw [mem_comap,mem_comap];have q35:Ideal.Quotient.mk Q (z13 Λ n c)=f₂ (z13 Λ s' c):=(hf₂_C c).symm;rw [q35];exact mem_map_of_mem f₂ (z17 s' hc)
    ·
     rw [map_span,span_le];rintro _ ⟨_,⟨j,rfl⟩,rfl⟩;rw [← hf₂_var j];exact mem_map_of_mem f₂ (z18 j)
    ·
     rw [map_le_iff_le_comap];intro q hq;rw [mem_comap,Ideal.Quotient.eq_zero_iff_mem.mpr hq];exact Ideal.zero_mem _
   exact q13 (mem_map_of_mem (Ideal.Quotient.mk Q) hk)
 have q33:((maximalIdeal B).map β).radical=maximalIdeal A:=by
  refine le_antisymm ?_ ?_
  ·
   rw [← (maximalIdeal.isMaximal A).isPrime.radical];exact Ideal.radical_mono (map_le_iff_le_comap.mpr hβ_loc)
  ·
   have q9:maximalIdeal A=(maximalIdeal T).map (Ideal.Quotient.mk I):=by
    rw [← q0,Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
   rw [q9,z34 n,Ideal.map_sup]
   refine sup_le ?_ ?_
   ·
    rw [Ideal.map_map,map_le_iff_le_comap];intro y hy;rw [← q24] at hy;obtain ⟨k,hk⟩:=hy
    refine ⟨k,?_⟩
    rw [RingHom.comp_apply,← map_pow,← map_pow]
    have q13:((maximalIdeal Λ).map (z13 Λ n)⊔span (Set.range v)⊔Q).map
      ((Ideal.Quotient.mk I).comp i₂) ≤ (maximalIdeal B).map β := by
     rw [Ideal.map_sup,Ideal.map_sup]
     refine sup_le (sup_le ?_ ?_) ?_
     ·
      rw [map_le_iff_le_comap,map_le_iff_le_comap];intro c hc;rw [mem_comap,mem_comap];change Ideal.Quotient.mk I (i₂ (z13 Λ n c))∈(maximalIdeal B).map β
      have q31:Ideal.Quotient.mk I (i₂ (z13 Λ n c)) = β (j₂ (z13 Λ s' c)):=by
       rw [hβ_C,hβ₂_C];rfl
      rw [q31];exact mem_map_of_mem β (z17 r' (z17 s' hc))
     ·
      rw [map_span,span_le];rintro _ ⟨_,⟨j,rfl⟩,rfl⟩;change Ideal.Quotient.mk I (i₂ (v j))∈(maximalIdeal B).map β;rw [← hβ₂_var j,← hβ_C];exact mem_map_of_mem β (z17 r' (z18 j))
     ·
      rw [map_le_iff_le_comap];intro q hq;rw [mem_comap,RingHom.comp_apply];have hqI:i₂ q∈I:=mem_sup_right (mem_map_of_mem i₂ hq);rw [Ideal.Quotient.eq_zero_iff_mem.mpr hqI];exact Ideal.zero_mem _
    exact q13 (mem_map_of_mem ((Ideal.Quotient.mk I).comp i₂) hk)
   ·
    rw [map_span,span_le];rintro _ ⟨_,⟨k,rfl⟩,rfl⟩;have q16:z14 R k=i₁ (z14 Λ k):=(z20 (z13 Λ n) k).symm;rw [q16];have hy:z14 Λ k∈maximalIdeal R:=z18 k;rw [← q21] at hy;obtain ⟨m,hm⟩:=hy
    refine ⟨m,?_⟩
    rw [← map_pow,← map_pow]
    have q13:((maximalIdeal Λ).map (z13 Λ n)⊔span (Set.range u)⊔P).map
      ((Ideal.Quotient.mk I).comp i₁) ≤ (maximalIdeal B).map β := by
     rw [Ideal.map_sup,Ideal.map_sup]
     refine sup_le (sup_le ?_ ?_) ?_
     ·
      rw [map_le_iff_le_comap,map_le_iff_le_comap];intro c hc;rw [mem_comap,mem_comap,RingHom.comp_apply];have h12:i₁ (z13 Λ n c)=i₂ (z13 Λ n c):=z19 (z13 Λ n) n c;rw [h12]
      have q31:Ideal.Quotient.mk I (i₂ (z13 Λ n c)) = β (j₂ (z13 Λ s' c)):=by
       rw [hβ_C,hβ₂_C];rfl
      rw [q31];exact mem_map_of_mem β (z17 r' (z17 s' hc))
     ·
      rw [map_span,span_le];rintro _ ⟨_,⟨i,rfl⟩,rfl⟩;change Ideal.Quotient.mk I (i₁ (u i))∈(maximalIdeal B).map β;rw [← hβ_var i];exact mem_map_of_mem β (z18 i)
     ·
      rw [map_le_iff_le_comap];intro p hp;rw [mem_comap,RingHom.comp_apply];have hpI:i₁ p∈I:=mem_sup_left (mem_map_of_mem i₁ hp);rw [Ideal.Quotient.eq_zero_iff_mem.mpr hpI];exact Ideal.zero_mem _
    exact q13 (mem_map_of_mem ((Ideal.Quotient.mk I).comp i₁) hm)
 letI : Algebra B₁ (R⧸P):=f₁.toAlgebra
 letI : Algebra B₂ (R⧸Q):=f₂.toAlgebra
 letI : Algebra B₁ B:=j₁.toAlgebra
 letI : Algebra B₂ B:=j₂.toAlgebra
 letI : Algebra B A := β.toAlgebra
 have q29:Surjective ((residue (R⧸P)).comp f₁):=by
  intro y;obtain ⟨r,rfl⟩:=residue_surjective y;obtain ⟨x,rfl⟩:=Ideal.Quotient.mk_surjective r;obtain ⟨c,hc⟩:=z35 n (residue R x)
  refine ⟨z13 Λ r' c,?_⟩
  rw [RingHom.comp_apply,hf₁_C]
  symm
  rw [← sub_eq_zero,← map_sub,residue_eq_zero_iff,RingHom.comp_apply,← map_sub,← mem_comap,q1,← residue_eq_zero_iff,map_sub];change residue R x - ((residue R).comp (z13 Λ n)) c=0;rw [hc,sub_self]
 have q32:Surjective ((residue (R⧸Q)).comp f₂):=by
  intro y;obtain ⟨r,rfl⟩:=residue_surjective y;obtain ⟨x,rfl⟩:=Ideal.Quotient.mk_surjective r;obtain ⟨c,hc⟩:=z35 n (residue R x)
  refine ⟨z13 Λ s' c,?_⟩
  rw [RingHom.comp_apply,hf₂_C]
  symm
  rw [← sub_eq_zero,← map_sub,residue_eq_zero_iff,RingHom.comp_apply,← map_sub,← mem_comap,q2,← residue_eq_zero_iff,map_sub];change residue R x - ((residue R).comp (z13 Λ n)) c=0;rw [hc,sub_self]
 have q30:Surjective ((residue A).comp β):=by
  intro y;obtain ⟨a,rfl⟩:=residue_surjective y;obtain ⟨t,rfl⟩:=Ideal.Quotient.mk_surjective a;obtain ⟨x,hx⟩:=z35 n (residue T t);obtain ⟨c,hc⟩:=z35 n (residue R x)
  refine ⟨j₂ (z13 Λ s' c),?_⟩
  rw [RingHom.comp_apply,hβ_C,hβ₂_C]
  symm
  rw [← sub_eq_zero,← map_sub,residue_eq_zero_iff];change Ideal.Quotient.mk I t - Ideal.Quotient.mk I (i₂ (z13 Λ n c))∈maximalIdeal A;rw [← map_sub,← mem_comap,q0]
  have ht1:t - i₂ x∈maximalIdeal T:=by
   rw [← residue_eq_zero_iff,map_sub];change residue T t - ((residue T).comp (z13 R n)) x=0;rw [hx,sub_self]
  have ht2:x - z13 Λ n c∈maximalIdeal R:=by
   rw [← residue_eq_zero_iff,map_sub];change residue R x - ((residue R).comp (z13 Λ n)) c=0;rw [hc,sub_self]
  have q19:t - i₂ (z13 Λ n c)=(t - i₂ x)+i₂ (x - z13 Λ n c):=by
   rw [map_sub];ring
  rw [q19];exact (maximalIdeal T).add_mem ht1 (z17 n ht2)
 have : Module.Finite B₁ (R⧸P):=z40 hf₁_loc q29 hrad₁;have : Module.Finite B₂ (R⧸Q):=z40 hf₂_loc q32 hrad₂;have : Module.Finite B A:=z40 hβ_loc q30 q33;let A₁ := B ⊗[B₁] (R⧸P);let A₂ := B ⊗[B₂] (R⧸Q)
 letI : Algebra B A₁ := Algebra.TensorProduct.leftAlgebra
 letI : Algebra B A₂ := Algebra.TensorProduct.leftAlgebra
 let M:=A₁ ⊗[B] A₂
 letI : CommRing M:=inferInstanceAs (CommRing (A₁ ⊗[B] A₂))
 letI : Algebra B M:=inferInstanceAs (Algebra B (A₁ ⊗[B] A₂))
 have : Module.Finite B A₁ := inferInstance;have : Module.Finite B A₂ := inferInstance;have : Module.Finite B M:=inferInstance
 have hβ_inj:Injective β := by
  rw [injective_iff_map_eq_zero];intro b hb
  have q7:(algebraMap B M) b ∈ ⨅ t : ℕ,(maximalIdeal B ^ t•(⊤ : Submodule B M)):=by
   rw [Submodule.mem_iInf];intro t;let Jt:Ideal M:=(maximalIdeal B ^ t).map (algebraMap B M);let Mt:=M⧸Jt;let q41:M →+* Mt:=Ideal.Quotient.mk Jt;let toA₁ : (R⧸P) →+* A₁ := Algebra.TensorProduct.includeRight.toRingHom;let toA₂ : (R⧸Q) →+* A₂ := Algebra.TensorProduct.includeRight.toRingHom;let q39:A₁ →+* M:=Algebra.TensorProduct.includeLeftRingHom
   let q34:A₂ →+* M:=Algebra.TensorProduct.includeRight.toRingHom;let φ₁ : R →+* Mt:=q41.comp (q39.comp (toA₁.comp (Ideal.Quotient.mk P)));let φ₂ : R →+* Mt:=q41.comp (q34.comp (toA₂.comp (Ideal.Quotient.mk Q)))
   have q10:∀ z∈maximalIdeal B,(q41 (algebraMap B M z)) ^ t=0:=fun z hz=>by
    rw [← map_pow,← map_pow,Ideal.Quotient.eq_zero_iff_mem];exact mem_map_of_mem (algebraMap B M) (Ideal.pow_mem_pow hz t)
   have q8:∀ z:B₁,toA₁ (f₁ z)=algebraMap B A₁ (j₁ z):=fun z=>by
    change (1:B) ⊗ₜ[B₁] (f₁ z)=(j₁ z) ⊗ₜ[B₁] (1:R⧸P)
    have hz1:f₁ z=z•(1:R⧸P):=by rw [Algebra.smul_def,mul_one];rfl
    have hz2:j₁ z=z•(1:B):=by rw [Algebra.smul_def,mul_one];rfl
    rw [hz1,hz2,TensorProduct.tmul_smul,smul_tmul']
   have q11:∀ z:B₂,toA₂ (f₂ z)=algebraMap B A₂ (j₂ z):=fun z=>by
    change (1:B) ⊗ₜ[B₂] (f₂ z)=(j₂ z) ⊗ₜ[B₂] (1:R⧸Q)
    have hz1:f₂ z=z•(1:R⧸Q):=by rw [Algebra.smul_def,mul_one];rfl
    have hz2:j₂ z=z•(1:B):=by rw [Algebra.smul_def,mul_one];rfl
    rw [hz1,hz2,TensorProduct.tmul_smul,smul_tmul']
   have q6:∀ z:B,q39 (algebraMap B A₁ z)=q34 (algebraMap B A₂ z):=fun z=>by
    change (algebraMap B A₁ z) ⊗ₜ[B] (1:A₂)=(1:A₁) ⊗ₜ[B] (algebraMap B A₂ z);have hz1:algebraMap B A₁ z=z•(1:A₁):=Algebra.algebraMap_eq_smul_one z;have hz2:algebraMap B A₂ z=z•(1:A₂):=Algebra.algebraMap_eq_smul_one z;rw [hz1,hz2,TensorProduct.tmul_smul,smul_tmul']
   have hφ₁_nilp:∀ x∈maximalIdeal R,∃ k : ℕ,φ₁ x ^ k=0:=fun x hx=>by
    have hx':Ideal.Quotient.mk P x∈((maximalIdeal B₁).map f₁).radical:=by
     rw [hrad₁,← mem_comap,q1];exact hx
    obtain ⟨k,hk⟩:=hx'
    refine ⟨k*t,?_⟩
    rw [pow_mul,← map_pow];have q5:(Ideal.Quotient.mk P x) ^ k∈(maximalIdeal B₁).map f₁ := hk
    have hJt:toA₁ ((Ideal.Quotient.mk P x) ^ k)∈(maximalIdeal B).map (algebraMap B A₁):=by
     have hle:((maximalIdeal B₁).map f₁).map toA₁ ≤ (maximalIdeal B).map (algebraMap B A₁):=by
      rw [Ideal.map_map,map_le_iff_le_comap];intro z hz;rw [mem_comap,RingHom.comp_apply,q8 z]
      exact mem_map_of_mem (algebraMap B A₁)
       (z23 (fun c hc=>z17 s' hc) r' hz)
     exact hle (mem_map_of_mem toA₁ q5)
    have q17:q39 (toA₁ ((Ideal.Quotient.mk P x) ^ k)) ∈
      (maximalIdeal B).map (algebraMap B M):=by
     have hle:((maximalIdeal B).map (algebraMap B A₁)).map q39 ≤ (maximalIdeal B).map (algebraMap B M):=by
      rw [Ideal.map_map];exact le_of_eq rfl
     exact hle (mem_map_of_mem q39 hJt)
    have q37:(q39 (toA₁ ((Ideal.Quotient.mk P x) ^ k))) ^ t∈Jt:=by
     have h1:(q39 (toA₁ ((Ideal.Quotient.mk P x) ^ k))) ^ t ∈
       ((maximalIdeal B).map (algebraMap B M)) ^ t:=Ideal.pow_mem_pow q17 t
     rwa [← Ideal.map_pow] at h1
    change (q41 (q39 (toA₁ (Ideal.Quotient.mk P (x ^ k))))) ^ t=0;rw [map_pow (Ideal.Quotient.mk P),← map_pow q41];exact Ideal.Quotient.eq_zero_iff_mem.mpr q37
   obtain ⟨Ψ,hΨ_C,hΨ_var⟩:=z33 φ₂ n
    (fun k => φ₁ (z14 Λ k))
    (fun k=>hφ₁_nilp (z14 Λ k) (z18 k))
   have hφ12_C:∀ c : Λ,φ₁ (z13 Λ n c) = φ₂ (z13 Λ n c):=fun c=>by
    have h1:toA₁ (Ideal.Quotient.mk P (z13 Λ n c))=algebraMap B A₁ (j₁ (z13 Λ r' c)):=by
     have hc:Ideal.Quotient.mk P (z13 Λ n c)=f₁ (z13 Λ r' c):=(hf₁_C c).symm;rw [hc,q8]
    have h2:toA₂ (Ideal.Quotient.mk Q (z13 Λ n c))=algebraMap B A₂ (j₂ (z13 Λ s' c)):=by
     have hc:Ideal.Quotient.mk Q (z13 Λ n c)=f₂ (z13 Λ s' c):=(hf₂_C c).symm;rw [hc,q11]
    have q42:j₁ (z13 Λ r' c)=j₂ (z13 Λ s' c):=z19 (z13 Λ s') r' c;dsimp only [φ₁,φ₂];simp only [RingHom.comp_apply,h1,h2,q42];rw [q6]
   have hΨ_i₁ : Ψ.comp i₁ = φ₁ := by
    refine z32 (Ψ.comp i₁) φ₁ ?_ ?_ ?_
    ·
     intro c;rw [RingHom.comp_apply,z19 (z13 Λ n) n c];change Ψ (z13 R n (z13 Λ n c)) = φ₁ (z13 Λ n c);rw [hΨ_C,hφ12_C]
    ·
     intro k;rw [RingHom.comp_apply,z20 (z13 Λ n) k];exact hΨ_var k
    ·
     intro k;rw [RingHom.comp_apply,z20 (z13 Λ n) k,hΨ_var k];exact hφ₁_nilp (z14 Λ k) (z18 k)
   have q28:I ≤ RingHom.ker Ψ := by
    refine sup_le ?_ ?_
    ·
     rw [map_le_iff_le_comap];intro p hp;rw [mem_comap,RingHom.mem_ker];change (Ψ.comp i₁) p=0;rw [hΨ_i₁];dsimp only [φ₁];simp [Ideal.Quotient.eq_zero_iff_mem.mpr hp]
    ·
     rw [map_le_iff_le_comap];intro q hq;rw [mem_comap,RingHom.mem_ker];change Ψ (z13 R n q)=0;rw [hΨ_C];dsimp only [φ₂];simp [Ideal.Quotient.eq_zero_iff_mem.mpr hq]
   let barΨ : A →+* Mt:=Ideal.Quotient.lift I Ψ q28
   have hbarΨ_mk:∀ x:T,barΨ (Ideal.Quotient.mk I x) = Ψ x:=fun x =>
    Ideal.Quotient.lift_mk I Ψ q28
   have hbarΨ_β : barΨ.comp β = q41.comp (algebraMap B M):=by
    have q20:(barΨ.comp β).comp j₂ = (q41.comp (algebraMap B M)).comp j₂ := by
     refine z32 _ _ ?_ ?_ ?_
     ·
      intro c;dsimp only [j₂];simp only [RingHom.comp_apply,hβ_C,hβ₂_C];change barΨ (Ideal.Quotient.mk I (i₂ (z13 Λ n c)))=q41 (algebraMap B M (j₂ (z13 Λ s' c)));rw [hbarΨ_mk];change Ψ (z13 R n (z13 Λ n c))=_;rw [hΨ_C];dsimp only [φ₂];simp only [RingHom.comp_apply]
      have h2:toA₂ (Ideal.Quotient.mk Q (z13 Λ n c))=algebraMap B A₂ (j₂ (z13 Λ s' c)):=by
       have hc:Ideal.Quotient.mk Q (z13 Λ n c)=f₂ (z13 Λ s' c):=(hf₂_C c).symm;rw [hc,q11]
      rw [h2,← q6];rfl
     ·
      intro j;dsimp only [j₂];simp only [RingHom.comp_apply,hβ_C,hβ₂_var];change barΨ (Ideal.Quotient.mk I (i₂ (v j)))=q41 (algebraMap B M (j₂ (z14 Λ j)));rw [hbarΨ_mk];change Ψ (z13 R n (v j))=q41 (algebraMap B M (j₂ (z14 Λ j)));rw [hΨ_C];dsimp only [φ₂];simp only [RingHom.comp_apply]
      have h2:toA₂ (Ideal.Quotient.mk Q (v j))=algebraMap B A₂ (j₂ (z14 Λ j)):=by
       rw [← hf₂_var j,q11]
      rw [h2,← q6];rfl
     ·
      intro j
      refine ⟨t,?_⟩
      have q40:((barΨ.comp β).comp j₂) (z14 Λ j)=q41 (algebraMap B M (j₂ (z14 Λ j))):=by
       dsimp only [j₂];simp only [RingHom.comp_apply,hβ_C,hβ₂_var];change barΨ (Ideal.Quotient.mk I (i₂ (v j)))=q41 (algebraMap B M (j₂ (z14 Λ j)));rw [hbarΨ_mk];change Ψ (z13 R n (v j))=q41 (algebraMap B M (j₂ (z14 Λ j)));rw [hΨ_C];dsimp only [φ₂];simp only [RingHom.comp_apply]
       have h2:toA₂ (Ideal.Quotient.mk Q (v j))=algebraMap B A₂ (j₂ (z14 Λ j)):=by
        rw [← hf₂_var j,q11]
       rw [h2,← q6];rfl
      rw [q40];exact q10 _ (z17 r' (z18 j))
    refine z32 (barΨ.comp β) (q41.comp (algebraMap B M))
     (fun c=>RingHom.congr_fun q20 c) ?_ ?_
    ·
     intro i;simp only [RingHom.comp_apply,hβ_var];change barΨ (Ideal.Quotient.mk I (i₁ (u i)))=q41 (algebraMap B M (z14 B₂ i));rw [hbarΨ_mk];change (Ψ.comp i₁) (u i)=q41 (algebraMap B M (z14 B₂ i));rw [hΨ_i₁];dsimp only [φ₁];simp only [RingHom.comp_apply]
     have h1:toA₁ (Ideal.Quotient.mk P (u i))=algebraMap B A₁ (z14 B₂ i):=by
      rw [← hf₁_var i,← z20 (z13 Λ s') i];exact q8 (z14 Λ i)
     rw [h1];rfl
    ·
     intro i
     refine ⟨t,?_⟩
     have q40:(barΨ.comp β) (z14 B₂ i)=q41 (algebraMap B M (z14 B₂ i)):=by
      simp only [RingHom.comp_apply,hβ_var];change barΨ (Ideal.Quotient.mk I (i₁ (u i)))=q41 (algebraMap B M (z14 B₂ i));rw [hbarΨ_mk];change (Ψ.comp i₁) (u i)=q41 (algebraMap B M (z14 B₂ i));rw [hΨ_i₁];dsimp only [φ₁];simp only [RingHom.comp_apply]
      have h1:toA₁ (Ideal.Quotient.mk P (u i))=algebraMap B A₁ (z14 B₂ i):=by
       rw [← hf₁_var i,← z20 (z13 Λ s') i];exact q8 (z14 Λ i)
      rw [h1];rfl
     rw [q40];exact q10 _ (z18 i)
   have h0:q41 (algebraMap B M b)=0:=by
    have:=RingHom.congr_fun hbarΨ_β b;simp only [RingHom.comp_apply,hb,map_zero] at this;exact this.symm
   rw [Ideal.Quotient.eq_zero_iff_mem] at h0
   have q22:(Jt:Set M)⊆(((maximalIdeal B ^ t•(⊤ : Submodule B M)) : Submodule B M) : Set M):=by
    intro m hm
    have hle:(Jt.restrictScalars B) ≤ maximalIdeal B ^ t•(⊤ : Submodule B M):=by
     intro x hx;have hx':x∈span (algebraMap B M '' ((maximalIdeal B ^ t:Ideal B) : Set B)):=hx
     refine Submodule.span_induction ?_ (Submodule.zero_mem _) (fun _ _ _ _=>Submodule.add_mem _)
      (fun r y _ hy => ?_) hx'
     ·
      rintro _ ⟨a,ha,rfl⟩
      have : algebraMap B M a=a•(1:M):=by rw [Algebra.smul_def,mul_one]
      rw [this];exact Submodule.smul_mem_smul ha Submodule.mem_top
     ·
      refine Submodule.smul_induction_on hy ?_ ?_
      ·
       intro a ha z _
       have : r•(a•z)=a•(r*z):=by
        simp only [smul_eq_mul,Algebra.smul_def];ring
       rw [this];exact Submodule.smul_mem_smul ha Submodule.mem_top
      ·
       intro u v hu hv;rw [smul_add];exact Submodule.add_mem _ hu hv
    exact hle hm
   exact q22 h0
  have q38:=Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (R:=B) (M:=M)
   (maximalIdeal B) (maximalIdeal.isMaximal B).ne_top
  rw [q38] at q7;have hbM:algebraMap B M b=0:=q7;let K:=FractionRing B;have q27:Injective (algebraMap B K):=IsFractionRing.injective B K
  have hKA₁_nt:Nontrivial (K ⊗[B] A₁):=by
   let e1:K ⊗[B] A₁ ≃ₗ[K] K ⊗[B₁] (R⧸P):=TensorProduct.AlgebraTensorModule.cancelBaseChange B₁ B K K (R⧸P)
   refine e1.toEquiv.nontrivial_congr.mpr ?_
   exact z42 hf₁_inj (q27.comp hj₁_inj)
  have hKA₂_nt:Nontrivial (K ⊗[B] A₂):=by
   let e2:K ⊗[B] A₂ ≃ₗ[K] K ⊗[B₂] (R⧸Q):=TensorProduct.AlgebraTensorModule.cancelBaseChange B₂ B K K (R⧸Q)
   refine e2.toEquiv.nontrivial_congr.mpr ?_
   exact z42 hf₂_inj (q27.comp hj₂_inj)
  have q26:Nontrivial (K ⊗[B] M):=by
   let eM:K ⊗[B] M ≃ₗ[K] (K ⊗[B] A₁) ⊗[K] (K ⊗[B] A₂):=TensorProduct.AlgebraTensorModule.distribBaseChange B K A₁ A₂
   exact eM.toEquiv.nontrivial_congr.mpr
    (z41 K (K ⊗[B] A₁) (K ⊗[B] A₂))
  by_contra hb0
  have q23:algebraMap B K b≠0:=fun h=>hb0 (q27 (by simpa using h))
  have h10:(1:K ⊗[B] M)=0:=by
   have q43:(algebraMap B K b)•(1:K ⊗[B] M)=0:=by
    change (algebraMap B K b)•((1:K) ⊗ₜ[B] (1:M))=0;rw [smul_tmul',smul_eq_mul,mul_one]
    have hbK:algebraMap B K b=b•(1:K):=by rw [Algebra.smul_def,mul_one]
    have hbM':b•(1:M)=0:=by rw [Algebra.smul_def,mul_one,hbM]
    rw [hbK,smul_tmul,hbM',tmul_zero]
   have q36:=congrArg (fun x=>(algebraMap B K b)⁻¹ • x) q43
   simp only [smul_smul,smul_zero,inv_mul_cancel₀ q23,one_smul] at q36;exact q36
  have : Subsingleton (K ⊗[B] M):=subsingleton_of_zero_eq_one h10.symm;exact not_subsingleton (K ⊗[B] M) this
 have : Algebra.IsIntegral B A:=Algebra.IsIntegral.of_finite B A;have q15:ringKrullDim A=ringKrullDim B:=z37 hβ_inj;rw [q15,z11 B₂ r',z11 Λ s']
lemma z45 {C R:Type} [CommRing C] [IsLocalRing C]
  [CommRing R] [IsLocalRing R] [IsHausdorff (maximalIdeal R) R] :
  ∀ {n : ℕ} (g₁ g₂ : z0 C n →+* R),(∀ c:C,g₁ (z13 C n c)=g₂ (z13 C n c))→(∀ i:Fin n,g₁ (z14 C i)=g₂ (z14 C i))→(∀ i:Fin n,g₁ (z14 C i)∈maximalIdeal R) → g₁ = g₂ := by
 intro n g₁ g₂ hC hvar hmem;ext x
 refine sub_eq_zero.mp (IsHausdorff.haus' (I:=maximalIdeal R) (M:=R) (g₁ x - g₂ x) fun t => ?_)
 rw [SModEq.zero,smul_eq_mul,mul_top,← Ideal.Quotient.eq_zero_iff_mem,map_sub,sub_eq_zero];let mk:R →+* R⧸maximalIdeal R ^ t:=Ideal.Quotient.mk _
 have heq:mk.comp g₁ = mk.comp g₂ := by
  refine z32 (mk.comp g₁) (mk.comp g₂)
   (fun c=>by simp [hC c])
   (fun i=>by simp [hvar i])
   (fun i=>⟨t,?_⟩)
  rw [RingHom.comp_apply,← map_pow,Ideal.Quotient.eq_zero_iff_mem];exact Ideal.pow_mem_pow (hmem i) t
 exact RingHom.congr_fun heq x
lemma z46 (D:Type) [CommRing D] [IsLocalRing D]
  [IsAdicComplete (maximalIdeal D) D] (c:D) (hc:c∈maximalIdeal D) :
  ∃ e:PowerSeries D ≃+* PowerSeries D,(∀ d:D,e (PowerSeries.C d)=PowerSeries.C d)∧e PowerSeries.X=PowerSeries.X+PowerSeries.C c∧(∀ d:D,e.symm (PowerSeries.C d)=PowerSeries.C d)∧e.symm PowerSeries.X=PowerSeries.X - PowerSeries.C c:=by
 have q0:∀ d∈maximalIdeal D,(PowerSeries.C d:PowerSeries D)∈maximalIdeal (PowerSeries D):=by
  intro d hd;rw [z3,PowerSeries.constantCoeff_C];exact hd
 have hXc:(PowerSeries.X:PowerSeries D)+PowerSeries.C c∈maximalIdeal (PowerSeries D):=(maximalIdeal (PowerSeries D)).add_mem z4 (q0 c hc);have q1:(PowerSeries.X:PowerSeries D) - PowerSeries.C c∈maximalIdeal (PowerSeries D):=(maximalIdeal (PowerSeries D)).sub_mem z4 (q0 c hc);have : IsAdicComplete (maximalIdeal (PowerSeries D)) (PowerSeries D):=z9
 obtain ⟨φ,hφ_C,hφ_X,_⟩:=z12 PowerSeries.C q0 hXc;obtain ⟨ψ,hψ_C,hψ_X,_⟩:=z12 PowerSeries.C q0 q1
 have hψφ : ψ.comp φ = RingHom.id (PowerSeries D):=by
  refine z45 (C:=D) (n:=1) (ψ.comp φ) (RingHom.id _)
   (fun d=>by
    change ψ (φ (PowerSeries.C d))=PowerSeries.C d
    rw [hφ_C,hψ_C])
   (fun i=>by
    have hi:i=Fin.last 0:=Subsingleton.elim _ _;subst hi;change ψ (φ PowerSeries.X)=PowerSeries.X;rw [hφ_X,map_add,hψ_X,hψ_C]
    ring)
   (fun i=>by
    have hi:i=Fin.last 0:=Subsingleton.elim _ _;subst hi;change ψ (φ PowerSeries.X)∈maximalIdeal (PowerSeries D);rw [hφ_X,map_add,hψ_X,hψ_C]
    have : PowerSeries.X - PowerSeries.C c+PowerSeries.C c=(PowerSeries.X:PowerSeries D):=by
     ring
    rw [this]
    exact z4)
 have hφψ : φ.comp ψ = RingHom.id (PowerSeries D):=by
  refine z45 (C:=D) (n:=1) (φ.comp ψ) (RingHom.id _)
   (fun d=>by
    change φ (ψ (PowerSeries.C d))=PowerSeries.C d
    rw [hψ_C,hφ_C])
   (fun i=>by
    have hi:i=Fin.last 0:=Subsingleton.elim _ _;subst hi;change φ (ψ PowerSeries.X)=PowerSeries.X;rw [hψ_X,map_sub,hφ_X,hφ_C]
    ring)
   (fun i=>by
    have hi:i=Fin.last 0:=Subsingleton.elim _ _;subst hi;change φ (ψ PowerSeries.X)∈maximalIdeal (PowerSeries D);rw [hψ_X,map_sub,hφ_X,hφ_C]
    have : PowerSeries.X+PowerSeries.C c - PowerSeries.C c=(PowerSeries.X:PowerSeries D):=by
     ring
    rw [this]
    exact z4)
 let e:PowerSeries D ≃+* PowerSeries D :=
  {
   toFun := φ
   invFun := ψ
   left_inv:=RingHom.congr_fun hψφ
   right_inv:=RingHom.congr_fun hφψ
   map_mul' := φ.map_mul
   map_add' := φ.map_add }
 exact ⟨e,hφ_C,hφ_X,hψ_C,hψ_X⟩
lemma z47 (D:Type) [CommRing D] [IsLocalRing D]
  [IsAdicComplete (maximalIdeal D) D] :
  ∀ (n : ℕ) (cs:Fin n→D),(∀ i,cs i∈maximalIdeal D) →
   ∃ e:z0 D n ≃+* z0 D n,(∀ d:D,e (z13 D n d)=z13 D n d)∧(∀ i:Fin n,e (z14 D i)=z14 D i+z13 D n (cs i))∧(∀ d:D,e.symm (z13 D n d)=z13 D n d)∧(∀ i:Fin n,e.symm (z14 D i)=z14 D i - z13 D n (cs i)):=by
 intro n
 induction n with
 | zero =>
  intro cs _
  exact ⟨RingEquiv.refl D,fun _=>rfl,fun i=>Fin.elim0 i,fun _=>rfl,fun i=>Fin.elim0 i⟩
 | succ n ih =>
  intro cs hcs
  obtain ⟨e0,he0_C,he0_var,he0_symm_C,he0_symm_var⟩:=ih (fun j=>cs j.castSucc) (fun j=>hcs j.castSucc)
  let q2:PowerSeries (z0 D n) ≃+* PowerSeries (z0 D n) :=
   {
    toFun:=PowerSeries.map e0.toRingHom
    invFun:=PowerSeries.map e0.symm.toRingHom
    left_inv:=fun f=>by ext k;simp [PowerSeries.coeff_map]
    right_inv:=fun f=>by ext k;simp [PowerSeries.coeff_map]
    map_mul':=(PowerSeries.map e0.toRingHom).map_mul
    map_add':=(PowerSeries.map e0.toRingHom).map_add }
  have q1:∀ f,q2 f=PowerSeries.map e0.toRingHom f:=fun _=>rfl
  have q0:∀ f,q2.symm f=PowerSeries.map e0.symm.toRingHom f:=fun _=>rfl
  obtain ⟨eShift,heS_C,heS_X,heS_symm_C,heS_symm_X⟩ :=
   z46 (z0 D n) (z13 D n (cs (Fin.last n)))
    (z17 n (hcs (Fin.last n)))
  let e:z0 D (n+1) ≃+* z0 D (n+1):=q2.trans eShift
  refine ⟨e,?_,?_,?_,?_⟩
  ·
   intro d;simp only [e,z13,RingEquiv.trans_apply,RingHom.comp_apply,q1,PowerSeries.map_C];change eShift (PowerSeries.C (e0 (z13 D n d)))=PowerSeries.C (z13 D n d);rw [he0_C,heS_C]
  ·
   intro i
   refine Fin.lastCases ?_ ?_ i
   · simp only [e,z14,z13,Fin.lastCases_last,RingEquiv.trans_apply,RingHom.comp_apply,q1,PowerSeries.map_X,heS_X]
   ·
    intro j;simp only [e,z14,z13,Fin.lastCases_castSucc,RingEquiv.trans_apply,RingHom.comp_apply,q1,PowerSeries.map_C];change eShift (PowerSeries.C (e0 (z14 D j)))=PowerSeries.C (z14 D j)+PowerSeries.C (z13 D n (cs j.castSucc));rw [he0_var,heS_C,map_add]
  ·
   intro d;simp only [e,z13,RingEquiv.symm_trans_apply,RingHom.comp_apply,heS_symm_C,q0,PowerSeries.map_C];change PowerSeries.C (e0.symm (z13 D n d))=PowerSeries.C (z13 D n d);rw [he0_symm_C]
  ·
   intro i
   refine Fin.lastCases ?_ ?_ i
   ·
    simp only [e,z14,z13,Fin.lastCases_last,RingEquiv.symm_trans_apply,RingHom.comp_apply,heS_symm_X,map_sub,q0,PowerSeries.map_X,PowerSeries.map_C];change PowerSeries.X - PowerSeries.C (e0.symm (z13 D n (cs (Fin.last n))))=PowerSeries.X - PowerSeries.C (z13 D n (cs (Fin.last n)));rw [he0_symm_C]
   ·
    intro j;simp only [e,z14,z13,Fin.lastCases_castSucc,RingEquiv.symm_trans_apply,RingHom.comp_apply,heS_symm_C,q0,PowerSeries.map_C];change PowerSeries.C (e0.symm (z14 D j))=PowerSeries.C (z14 D j) - PowerSeries.C (z13 D n (cs j.castSucc));rw [he0_symm_var,map_sub]
noncomputable def z48 (D:Type) [CommRing D] :
  ∀ n : ℕ,z0 D n →+* D
 | 0=>RingHom.id D
 | n+1=>(z48 D n).comp PowerSeries.constantCoeff
lemma z49 (D:Type) [CommRing D] :
  ∀ (n : ℕ) (d:D),z48 D n (z13 D n d)=d
 | 0,_=>rfl
 | n+1,d=>by
  change z48 D n (PowerSeries.constantCoeff (PowerSeries.C (z13 D n d)))=d;rw [PowerSeries.constantCoeff_C,z49 D n d]
lemma z50 (D:Type) [CommRing D] :
  ∀ {n : ℕ} (i:Fin n),z48 D n (z14 D i)=0
 | 0,i=>Fin.elim0 i
 | n+1,i=>by
  refine Fin.lastCases ?_ ?_ i
  · simp only [z48,z14,Fin.lastCases_last,RingHom.comp_apply,PowerSeries.constantCoeff_X,map_zero]
  ·
   intro j;simp only [z48,z14,Fin.lastCases_castSucc,RingHom.comp_apply,PowerSeries.constantCoeff_C,z50 D j]
lemma z51 (D:Type) [CommRing D] :
  ∀ n : ℕ,RingHom.ker (z48 D n)=span (Set.range (z14 D (n:=n)))
 | 0=>by
  ext x;simp [z48,RingHom.mem_ker,Set.range_eq_empty]
 | n+1=>by
  refine le_antisymm ?_ ?_
  ·
   intro f hf;rw [RingHom.mem_ker] at hf;have hf0:PowerSeries.constantCoeff f∈RingHom.ker (z48 D n):=hf;rw [z51 D n] at hf0
   have q0:PowerSeries.C (PowerSeries.constantCoeff f) ∈
     span (Set.range (z14 D (n:=n+1))):=by
    have h1:=mem_map_of_mem PowerSeries.C hf0
    have hle:(span (Set.range (z14 D (n:=n)))).map PowerSeries.C ≤ span (Set.range (z14 D (n:=n+1))):=by
     rw [map_span,span_le];rintro _ ⟨_,⟨j,rfl⟩,rfl⟩;exact subset_span ⟨j.castSucc,by simp [z14]⟩
    exact hle h1
   have q2:f - PowerSeries.C (PowerSeries.constantCoeff f) ∈
     span {(PowerSeries.X:PowerSeries (z0 D n))}:=by
    have h1:=z6 1
     (f - PowerSeries.C (PowerSeries.constantCoeff f)) (fun i hi=>by
      have hi0:i=0:=by omega
      subst hi0;simp)
    simpa using h1
   have q1:span {(PowerSeries.X:PowerSeries (z0 D n))} ≤ span (Set.range (z14 D (n:=n+1))):=(span_singleton_le_iff_mem _).mpr (subset_span ⟨Fin.last n,by simp [z14]⟩);have q3:=Ideal.add_mem _ q0 (q1 q2);simpa using q3
  ·
   rw [span_le];rintro _ ⟨i,rfl⟩;rw [SetLike.mem_coe,RingHom.mem_ker];exact z50 D i
lemma z52 {Λ : Type} [CommRing Λ] [IsLocalRing Λ]
  [IsAdicComplete (maximalIdeal Λ) Λ] (n : ℕ) :
  let R:=z0 Λ n;let T:=z0 R n;let i₁ : R →+* T:=z15 (z13 Λ n) n;let i₂ : R →+* T:=z13 R n
  let Δ : Ideal T:=span (Set.range (fun k:Fin n=>z14 R k - i₂ (z14 Λ k)))
  ∃ μ : T →+* R,μ.comp i₁ = RingHom.id R ∧ μ.comp i₂ = RingHom.id R∧Surjective μ ∧ RingHom.ker μ = Δ := by
 intro R T i₁ i₂ Δ
 obtain ⟨eShift,heS_C,heS_var,heS_symm_C,heS_symm_var⟩:=z47 R n (z14 Λ) (fun k=>z18 k)
 let μ : T →+* R:=(z48 R n).comp eShift.toRingHom
 have hμ_i₂ : μ.comp i₂ = RingHom.id R:=by
  ext r;simp only [μ,i₂,RingHom.comp_apply,RingHom.id_apply,RingEquiv.toRingHom_eq_coe,RingEquiv.coe_toRingHom,heS_C,z49]
 have hμ_var:∀ k:Fin n,μ (z14 R k)=z14 Λ k:=fun k=>by
  simp only [μ,RingHom.comp_apply,RingEquiv.toRingHom_eq_coe,RingEquiv.coe_toRingHom,heS_var,map_add,z50,z49,zero_add]
 have hμ_i₁ : μ.comp i₁ = RingHom.id R:=by
  refine z45 (C := Λ) (R:=R) (μ.comp i₁) (RingHom.id R) ?_ ?_ ?_
  ·
   intro c;rw [RingHom.comp_apply,RingHom.id_apply,z19 (z13 Λ n) n c];exact RingHom.congr_fun hμ_i₂ (z13 Λ n c)
  ·
   intro k;rw [RingHom.comp_apply,RingHom.id_apply,z20 (z13 Λ n) k];exact hμ_var k
  ·
   intro k;rw [RingHom.comp_apply,z20 (z13 Λ n) k,hμ_var k];exact z18 k
 have hμ_surj:Surjective μ := fun r=>⟨i₂ r,RingHom.congr_fun hμ_i₂ r⟩
 have hμ_ker:RingHom.ker μ = Δ := by
  refine le_antisymm ?_ ?_
  ·
   intro t ht;rw [RingHom.mem_ker] at ht;have h1:eShift t∈RingHom.ker (z48 R n):=ht;rw [z51 R n] at h1
   have h2:eShift.symm (eShift t) ∈
     (span (Set.range (z14 R (n:=n)))).map eShift.symm.toRingHom :=
    mem_map_of_mem eShift.symm.toRingHom h1
   rw [eShift.symm_apply_apply,map_span] at h2
   refine (span_le.mpr ?_) h2
   rintro _ ⟨_,⟨k,rfl⟩,rfl⟩;simp only [RingEquiv.toRingHom_eq_coe,RingEquiv.coe_toRingHom,heS_symm_var];exact subset_span ⟨k,rfl⟩
  ·
   rw [span_le];rintro _ ⟨k,rfl⟩;rw [SetLike.mem_coe,RingHom.mem_ker,map_sub,hμ_var k];have h2 : μ (i₂ (z14 Λ k))=z14 Λ k:=RingHom.congr_fun hμ_i₂ (z14 Λ k);rw [h2,sub_self]
 exact ⟨μ,hμ_i₁,hμ_i₂,hμ_surj,hμ_ker⟩
lemma z53 {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ]
    [IsAdicComplete (maximalIdeal Λ) Λ]
    (n : ℕ) (P Q:Ideal (z0 Λ n)) [P.IsPrime] [Q.IsPrime]
    (hPQ:(P⊔Q).radical=maximalIdeal (z0 Λ n)) :
    let R:=z0 Λ n;let T:=z0 R n;let i₁ : R →+* T:=z15 (z13 Λ n) n;let i₂ : R →+* T:=z13 R n
    ringKrullDim (T⧸(P.map i₁ ⊔ Q.map i₂)) ≤ (n:WithBot ℕ∞):=by
  intro R T i₁ i₂;let I:Ideal T:=P.map i₁ ⊔ Q.map i₂
  have q3:I ≤ maximalIdeal T:=by
    refine sup_le ?_ ?_
    · rw [map_le_iff_le_comap]
      intro x hx
      exact z23 (fun c hc=>z17 n hc) n
        (le_maximalIdeal ‹P.IsPrime›.ne_top hx)
    · rw [map_le_iff_le_comap]
      intro x hx;exact z17 n (le_maximalIdeal ‹Q.IsPrime›.ne_top hx)
  have q2:I ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal T).ne_top q3;let A:=T⧸I;have : Nontrivial A:=Ideal.Quotient.nontrivial_iff.mpr q2;have : IsLocalRing A:=z36 I;obtain ⟨μ,hμ_i₁,hμ_i₂,hμ_surj,hμ_ker⟩:=z52 (Λ := Λ) n
  let Δ : Ideal T:=span (Set.range (fun k:Fin n=>z14 R k - i₂ (z14 Λ k)))
  let g:T →+* R⧸(P⊔Q):=(Ideal.Quotient.mk (P⊔Q)).comp μ;have q9:Surjective g:=Ideal.Quotient.mk_surjective.comp hμ_surj
  have q14:RingHom.ker g=I ⊔ Δ := by
    refine le_antisymm ?_ ?_
    · intro t ht
      rw [RingHom.mem_ker,RingHom.comp_apply,Ideal.Quotient.eq_zero_iff_mem] at ht;obtain ⟨p,hp,q,hq,hpq⟩:=Submodule.mem_sup.mp ht
      have q19:t - (i₁ p+i₂ q)∈RingHom.ker μ := by
        rw [RingHom.mem_ker,map_sub,map_add];have hp' : μ (i₁ p)=p:=RingHom.congr_fun hμ_i₁ p;have hq' : μ (i₂ q)=q:=RingHom.congr_fun hμ_i₂ q;rw [hp',hq',hpq,sub_self]
      rw [hμ_ker] at q19
      have q12:i₁ p+i₂ q∈I :=
        Ideal.add_mem _ (mem_sup_left (mem_map_of_mem i₁ hp))
          (mem_sup_right (mem_map_of_mem i₂ hq))
      have q22:=Ideal.add_mem _ (mem_sup_left q12) (mem_sup_right q19);simpa using q22
    · refine sup_le (sup_le ?_ ?_) ?_
      · rw [map_le_iff_le_comap]
        intro p hp;rw [mem_comap,RingHom.mem_ker,RingHom.comp_apply];have hp' : μ (i₁ p)=p:=RingHom.congr_fun hμ_i₁ p;rw [hp',Ideal.Quotient.eq_zero_iff_mem];exact mem_sup_left hp
      · rw [map_le_iff_le_comap]
        intro q hq;rw [mem_comap,RingHom.mem_ker,RingHom.comp_apply];have hq' : μ (i₂ q)=q:=RingHom.congr_fun hμ_i₂ q;rw [hq',Ideal.Quotient.eq_zero_iff_mem];exact mem_sup_right hq
      · have hΔ_eq : Δ = RingHom.ker μ := hμ_ker.symm
        rw [hΔ_eq];intro t ht;rw [RingHom.mem_ker,RingHom.comp_apply,RingHom.mem_ker.mp ht,map_zero]
  classical
  let S:Finset A:=Finset.univ.image (fun k:Fin n =>
    Ideal.Quotient.mk I (z14 R k - i₂ (z14 Λ k)))
  have q13:(S:Set A)⊆Ring.jacobson A:=by
    rw [IsLocalRing.ringJacobson_eq_maximalIdeal];intro a ha;rw [Finset.mem_coe,Finset.mem_image] at ha;obtain ⟨k,_,rfl⟩:=ha;have q0:(maximalIdeal A).comap (Ideal.Quotient.mk I)=maximalIdeal T:=eq_maximalIdeal (comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective);rw [SetLike.mem_coe,← mem_comap,q0]
    exact (maximalIdeal T).sub_mem (z18 k)
      (z17 n (z18 k))
  have q10:span (S:Set A) = Δ.map (Ideal.Quotient.mk I):=by
    rw [map_span];congr 1;ext a;simp [S]
  have q20:S.card ≤ n:=by
    calc S.card ≤ (Finset.univ:Finset (Fin n)).card:=Finset.card_image_le
      _=n:=Fintype.card_fin n
  have q1:(A⧸span (S:Set A)) ≃+* (R⧸(P⊔Q)):=by
    have q15:∀ a∈I,g a=0:=fun a ha =>
      RingHom.mem_ker.mp ((q14▸le_sup_left:I ≤ RingHom.ker g) ha)
    let gA:A →+* R⧸(P⊔Q):=Ideal.Quotient.lift I g q15
    have q6:Surjective gA:=fun y=>by
      obtain ⟨t,rfl⟩:=q9 y;exact ⟨Ideal.Quotient.mk I t,rfl⟩
    have q8:RingHom.ker gA=span (S:Set A):=by
      rw [q10];ext a;obtain ⟨t,rfl⟩:=Ideal.Quotient.mk_surjective a;rw [RingHom.mem_ker];dsimp only [gA];rw [Ideal.Quotient.lift_mk,← RingHom.mem_ker,q14,mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective];constructor
      · intro ht
        obtain ⟨u,hu,v,hv,huv⟩:=Submodule.mem_sup.mp ht
        refine ⟨v,hv,?_⟩
        symm
        rw [← sub_eq_zero,← map_sub,Ideal.Quotient.eq_zero_iff_mem]
        have : t - v=u:=by rw [← huv];ring
        rw [this];exact hu
      · rintro ⟨v,hv,hvt⟩
        have q21:t - v∈I:=by
          rw [← Ideal.Quotient.eq_zero_iff_mem,map_sub,hvt,sub_self]
        have q22:=Ideal.add_mem _ (mem_sup_left q21) (mem_sup_right hv);simpa using q22
    exact (Ideal.quotEquivOfEq q8.symm).trans (RingHom.quotientKerEquivOfSurjective q6)
  have q7:ringKrullDim (R⧸(P⊔Q))=0:=by
    have q11:P⊔Q ≠ ⊤ := by
      intro q23
      have h1:(P⊔Q).radical = ⊤ := by rw [q23,Ideal.radical_top]
      rw [hPQ] at h1;exact (maximalIdeal.isMaximal R).ne_top h1
    have : Nontrivial (R⧸(P⊔Q)):=Ideal.Quotient.nontrivial_iff.mpr q11
    have q24:ringKrullDim (R⧸(P⊔Q)) ≤ 0:=by
      rw [ringKrullDim_quotient,Order.krullDim]
      refine iSup_le fun c => ?_
      by_cases hlen:c.length=0
      · simp [hlen]
      · exfalso
        have q17:(c 0).1.asIdeal < (c ⟨1,by omega⟩).1.asIdeal:=c.strictMono (by simp [Fin.lt_def]);have q4:(c 0).1.asIdeal ≤ maximalIdeal R:=le_maximalIdeal (c 0).1.isPrime.ne_top
        have q5:maximalIdeal R ≤ (c 0).1.asIdeal:=by
          rw [← hPQ,← (c 0).1.isPrime.radical];exact Ideal.radical_mono (c 0).2
        have q18:(c 0).1.asIdeal=maximalIdeal R:=le_antisymm q4 q5;have q16:(c ⟨1,by omega⟩).1.asIdeal ≤ maximalIdeal R:=le_maximalIdeal (c ⟨1,by omega⟩).1.isPrime.ne_top;rw [q18] at q17;exact not_lt_of_ge q16 q17
    exact le_antisymm q24 (ringKrullDim_nonneg_of_nontrivial (R:=R⧸(P⊔Q)))
  have hle:=ringKrullDim_le_ringKrullDim_quotient_add_card S q13;rw [ringKrullDim_eq_of_ringEquiv q1,q7,zero_add] at hle;exact hle.trans (Nat.cast_le.mpr q20)
lemma z54 {k:Type} [Field k] (n : ℕ)
  (P Q:Ideal (z0 k n)) [P.IsPrime] [Q.IsPrime]
  (hPQ:(P⊔Q).radical=maximalIdeal (z0 k n)) :
  let R:=z0 k n;let T:=z0 R n;let i₁ : R →+* T:=z15 (z13 k n) n;let i₂ : R →+* T:=z13 R n
  ringKrullDim (R⧸P)+ringKrullDim (R⧸Q) ≤ ringKrullDim (T⧸(P.map i₁ ⊔ Q.map i₂)) ∧
  ringKrullDim (R⧸P)+ringKrullDim (R⧸Q) ≤ ringKrullDim R:=by
 intro R T i₁ i₂;have : IsLocalRing (R⧸P):=z36 P;have : IsLocalRing (R⧸Q):=z36 Q
 obtain ⟨r,hr⟩ :=
  ringKrullDim_quotient_eq_natCast
   P ‹P.IsPrime›.ne_top
 obtain ⟨s,hs⟩ :=
  ringKrullDim_quotient_eq_natCast
   Q ‹Q.IsPrime›.ne_top
 obtain ⟨u',hu'_mem,hu'_rad⟩:=z39 r (R⧸P) hr;obtain ⟨v',hv'_mem,hv'_rad⟩:=z39 s (R⧸Q) hs
 let u:Fin r→R:=fun i=>(Ideal.Quotient.mk_surjective (u' i)).choose
 have q18:∀ i,Ideal.Quotient.mk P (u i)=u' i:=fun i=>(Ideal.Quotient.mk_surjective (u' i)).choose_spec
 let v:Fin s→R:=fun j=>(Ideal.Quotient.mk_surjective (v' j)).choose
 have q17:∀ j,Ideal.Quotient.mk Q (v j)=v' j:=fun j=>(Ideal.Quotient.mk_surjective (v' j)).choose_spec
 have q0:(maximalIdeal (R⧸P)).comap (Ideal.Quotient.mk P)=maximalIdeal R:=eq_maximalIdeal (comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective);have q1:(maximalIdeal (R⧸Q)).comap (Ideal.Quotient.mk Q)=maximalIdeal R:=eq_maximalIdeal (comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
 have q13:∀ i,u i∈maximalIdeal R:=fun i=>by
  rw [← q0,mem_comap,q18 i];exact hu'_mem i
 have q8:∀ j,v j∈maximalIdeal R:=fun j=>by
  rw [← q1,mem_comap,q17 j];exact hv'_mem j
 have q2:∀ {J:Ideal R} [J.IsPrime] {m : ℕ} (w:Fin m→R) (w':Fin m→R⧸J)
   (_:IsLocalRing (R⧸J)),
   (∀ i,Ideal.Quotient.mk J (w i)=w' i) →
   (∀ i,w i∈maximalIdeal R) →
   (span (Set.range w')).radical=maximalIdeal (R⧸J) →
   ((maximalIdeal k).map (z13 k n)⊔span (Set.range w)⊔J).radical=maximalIdeal R:=by
  intro J _ m w w' _ hw_eq hw_mem hw'_rad;have q15:(maximalIdeal (R⧸J)).comap (Ideal.Quotient.mk J)=maximalIdeal R:=eq_maximalIdeal (comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
  refine le_antisymm ?_ ?_
  ·
   rw [← (maximalIdeal.isMaximal R).isPrime.radical]
   refine Ideal.radical_mono (sup_le (sup_le ?_ ?_) (le_maximalIdeal ‹J.IsPrime›.ne_top))
   · rw [map_le_iff_le_comap];intro c hc;exact z17 n hc
   · rw [span_le];rintro _ ⟨i,rfl⟩;exact hw_mem i
  ·
   intro x hx
   have hx':Ideal.Quotient.mk J x∈(span (Set.range w')).radical:=by
    rw [hw'_rad,← mem_comap,q15];exact hx
   obtain ⟨t,ht⟩:=hx';rw [← map_pow] at ht
   have q23:span (Set.range w')=(span (Set.range w)).map (Ideal.Quotient.mk J):=by
    rw [map_span];congr 1;ext y;simp [hw_eq]
   rw [q23,mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at ht;obtain ⟨y,hy_span,hy_eq⟩:=ht
   have q20:x ^ t - y∈J:=by
    rw [← Ideal.Quotient.eq_zero_iff_mem,map_sub,hy_eq,sub_self]
   refine ⟨t,?_⟩
   have q21:y+(x ^ t - y)∈(maximalIdeal k).map (z13 k n)⊔span (Set.range w)⊔J :=
    Ideal.add_mem _ (mem_sup_left (mem_sup_right hy_span))
     (mem_sup_right q20)
   simpa using q21
 have q9:=q2 u u' inferInstance q18 q13 hu'_rad;have q11:=q2 v v' inferInstance q17 q8 hv'_rad
 have q4:∀ {J:Ideal R} [J.IsPrime] {m : ℕ} (w:Fin m→R)
   (_:IsLocalRing (R⧸J)),
   ringKrullDim (R⧸J)=(m:WithBot ℕ∞) →
   ((maximalIdeal k).map (z13 k n)⊔span (Set.range w)⊔J).radical=maximalIdeal R →
   ∀ f:z0 k m →+* R⧸J,(∀ c,f (z13 k m c)=Ideal.Quotient.mk J (z13 k n c))→(∀ i,f (z14 k i)=Ideal.Quotient.mk J (w i))→Injective f:=by
  intro J _ m w _ hdimJ hw_rad f hfC hfvar;have q15:(maximalIdeal (R⧸J)).comap (Ideal.Quotient.mk J)=maximalIdeal R:=eq_maximalIdeal (comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
  have q14:∀ x∈maximalIdeal (z0 k m),f x∈maximalIdeal (R⧸J):=by
   intro x hx;have q6:(maximalIdeal (R⧸J)).comap f ≠ ⊤ := (Ideal.comap_isPrime f (maximalIdeal (R⧸J))).ne_top;have hle:(maximalIdeal (R⧸J)).comap f ≤ maximalIdeal (z0 k m):=le_maximalIdeal q6;rw [z34 m] at hx
   have q16:(maximalIdeal k).map (z13 k m)⊔span (Set.range (z14 k (n:=m))) ≤ (maximalIdeal (R⧸J)).comap f:=by
    refine sup_le ?_ ?_
    ·
     rw [map_le_iff_le_comap];intro c hc;rw [mem_comap,mem_comap,hfC,← mem_comap,q15];exact z17 n hc
    ·
     rw [span_le];rintro _ ⟨i,rfl⟩;rw [SetLike.mem_coe,mem_comap,hfvar]
     have hwi:w i∈maximalIdeal R:=by
      rw [← hw_rad];exact Ideal.le_radical (mem_sup_left (mem_sup_right (subset_span ⟨i,rfl⟩)))
     rw [← mem_comap,q15];exact hwi
   exact q16 hx
  have q12:Surjective ((residue (R⧸J)).comp f):=by
   intro y;obtain ⟨r,rfl⟩:=residue_surjective y;obtain ⟨x,rfl⟩:=Ideal.Quotient.mk_surjective r;obtain ⟨c,hc⟩:=z35 n (residue R x)
   refine ⟨z13 k m c,?_⟩
   rw [RingHom.comp_apply,hfC]
   symm
   rw [← sub_eq_zero,← map_sub,residue_eq_zero_iff,← map_sub,← mem_comap,q15,← residue_eq_zero_iff,map_sub];change residue R x - ((residue R).comp (z13 k n)) c=0;rw [hc,sub_self]
  have q10:((maximalIdeal (z0 k m)).map f).radical=maximalIdeal (R⧸J):=by
   refine le_antisymm ?_ ?_
   ·
    rw [← (maximalIdeal.isMaximal (R⧸J)).isPrime.radical];exact Ideal.radical_mono (map_le_iff_le_comap.mpr q14)
   ·
    intro x hx;obtain ⟨y,rfl⟩:=Ideal.Quotient.mk_surjective x;have hy:y∈maximalIdeal R:=q15▸hx;rw [← hw_rad] at hy;obtain ⟨t,ht⟩:=hy
    refine ⟨t,?_⟩
    rw [← map_pow]
    have hle:((maximalIdeal k).map (z13 k n)⊔span (Set.range w)⊔J).map
      (Ideal.Quotient.mk J) ≤ (maximalIdeal (z0 k m)).map f:=by
     rw [Ideal.map_sup,Ideal.map_sup]
     refine sup_le (sup_le ?_ ?_) ?_
     ·
      rw [map_le_iff_le_comap,map_le_iff_le_comap];intro c hc;rw [mem_comap,mem_comap,← hfC c];exact mem_map_of_mem f (z17 m hc)
     ·
      rw [map_span,span_le];rintro _ ⟨_,⟨i,rfl⟩,rfl⟩;rw [← hfvar i];exact mem_map_of_mem f (z18 i)
     ·
      rw [map_le_iff_le_comap];intro a ha;rw [mem_comap,Ideal.Quotient.eq_zero_iff_mem.mpr ha];exact Ideal.zero_mem _
    exact hle (mem_map_of_mem (Ideal.Quotient.mk J) ht)
  let _:Algebra (z0 k m) (R⧸J):=f.toAlgebra;have : Module.Finite (z0 k m) (R⧸J):=z40 q14 q12 q10;rw [RingHom.injective_iff_ker_eq_bot]
  by_contra hker_ne
  have q5:RingHom.ker f ≠ ⊤ := by
   intro q22;have h1:(1:z0 k m)∈RingHom.ker f:=q22▸Submodule.mem_top;rw [RingHom.mem_ker,map_one] at h1;exact one_ne_zero h1
  let q24:(z0 k m⧸RingHom.ker f) →+* R⧸J:=Ideal.Quotient.lift (RingHom.ker f) f (fun _ h=>h)
  have q3:Injective q24:=RingHom.kerLift_injective f;let _:Algebra (z0 k m⧸RingHom.ker f) (R⧸J):=q24.toAlgebra
  have : Module.Finite (z0 k m⧸RingHom.ker f) (R⧸J):=by
   obtain ⟨S,hS⟩:=Module.Finite.fg_top (R:=z0 k m) (M:=R⧸J)
   refine ⟨⟨S,eq_top_iff.mpr fun x _ => ?_⟩⟩
   have hx:x∈Submodule.span (z0 k m) (S:Set (R⧸J)):=hS▸Submodule.mem_top;rw [Submodule.mem_span_finset] at hx ⊢;obtain ⟨c,hc,rfl⟩:=hx
   refine ⟨fun s=>Ideal.Quotient.mk (RingHom.ker f) (c s),fun s hs => ?_,?_⟩
   · exact hc (fun h0=>hs (by simp [h0]))
   ·
    refine Finset.sum_congr rfl fun s _ => ?_
    rfl
  have : Algebra.IsIntegral (z0 k m⧸RingHom.ker f) (R⧸J):=Algebra.IsIntegral.of_finite _ _;have q7:=z37 q3;have hlt:=z38 hker_ne q5;rw [← q7,hdimJ,z11 k m,ringKrullDim_eq_zero_of_field k,zero_add] at hlt;exact lt_irrefl _ hlt
 have hge:=z44 (Λ := k) n P Q r s u q13 v q8 q9 q11
  (q4 u inferInstance hr q9) (q4 v inferInstance hs q11)
 have hle:=z53 (Λ := k) n P Q hPQ;rw [ringKrullDim_eq_zero_of_field k,zero_add] at hge
 have hge':ringKrullDim (R⧸P)+ringKrullDim (R⧸Q) ≤
   ringKrullDim (T⧸(P.map i₁ ⊔ Q.map i₂)):=by
  rw [hr,hs,add_comm];exact hge
 have q19:ringKrullDim R=(n:WithBot ℕ∞):=by
  rw [z11 k n,ringKrullDim_eq_zero_of_field k,zero_add]
 exact ⟨hge',hge'.trans (hle.trans_eq q19.symm)⟩
lemma z55 {V:Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [IsAdicComplete (maximalIdeal V) V] (p:V) (hp:maximalIdeal V=span {p})
  (n : ℕ) (P Q:Ideal (z0 V n)) [P.IsPrime] [Q.IsPrime]
  (hPQ:(P⊔Q).radical=maximalIdeal (z0 V n)) :
  let R:=z0 V n;let T:=z0 R n;let i₁ : R →+* T:=z15 (z13 V n) n;let i₂ : R →+* T:=z13 R n
  ringKrullDim (R⧸P)+ringKrullDim (R⧸Q) ≤ ringKrullDim R ∧
  (ringKrullDim (R⧸P)+ringKrullDim (R⧸Q)=ringKrullDim R→(z13 V n p∉P∨z13 V n p∉Q) ∧
   ringKrullDim (T⧸(P.map i₁ ⊔ Q.map i₂))=(n:WithBot ℕ∞)):=by
 intro R T i₁ i₂;have : IsLocalRing (R⧸P):=z36 P;have : IsLocalRing (R⧸Q):=z36 Q;have q51:ringKrullDim V=1:=IsDiscreteValuationRing.ringKrullDim_eq_one V
 have q52:ringKrullDim R=(n+1 : ℕ):=by
  rw [z11 V n,q51,add_comm];push_cast;rfl
 let k:=V⧸maximalIdeal V
 letI : Field k:=Ideal.Quotient.field (maximalIdeal V)
 let qR:R →+* z0 k n:=z15 (Ideal.Quotient.mk (maximalIdeal V)) n;have q9:Surjective qR:=z22 Ideal.Quotient.mk_surjective n
 have q20:RingHom.ker qR=span {z13 V n p}:=by
  rw [z26,hp,map_span,Set.image_singleton]
 have q48:=z53 (Λ := V) n P Q hPQ
 have q2:∀ (P' Q':Ideal R) [P'.IsPrime] [Q'.IsPrime],z13 V n p∈P'→z13 V n p∈Q'→(P'⊔Q').radical=maximalIdeal R →
   ringKrullDim (R⧸P')+ringKrullDim (R⧸Q') ≤
    ringKrullDim (T⧸(P'.map i₁ ⊔ Q'.map i₂)) ∧
   ringKrullDim (R⧸P')+ringKrullDim (R⧸Q') ≤ (n:WithBot ℕ∞):=by
  intro P' Q' _ _ hpP' hpQ' hP'Q'
  have hkerP':RingHom.ker qR ≤ P':=by
   rw [q20,span_singleton_le_iff_mem];exact hpP'
  have hkerQ':RingHom.ker qR ≤ Q':=by
   rw [q20,span_singleton_le_iff_mem];exact hpQ'
  let Pbar:Ideal (z0 k n):=P'.map qR;let Qbar:Ideal (z0 k n):=Q'.map qR;have : Pbar.IsPrime:=Ideal.map_isPrime_of_surjective q9 hkerP';have : Qbar.IsPrime:=Ideal.map_isPrime_of_surjective q9 hkerQ'
  have q11:(Pbar⊔Qbar).radical=maximalIdeal (z0 k n):=by
   refine le_antisymm ?_ ?_
   ·
    rw [← (maximalIdeal.isMaximal (z0 k n)).isPrime.radical]
    exact Ideal.radical_mono (sup_le (le_maximalIdeal ‹Pbar.IsPrime›.ne_top)
     (le_maximalIdeal ‹Qbar.IsPrime›.ne_top))
   ·
    intro y hy;obtain ⟨x,rfl⟩:=q9 y;have q3:(maximalIdeal (z0 k n)).comap qR=maximalIdeal R:=eq_maximalIdeal (comap_isMaximal_of_surjective qR q9);have hx:x∈maximalIdeal R:=q3▸hy;rw [← hP'Q'] at hx;obtain ⟨m,hm⟩:=hx
    refine ⟨m,?_⟩
    rw [← map_pow,← Ideal.map_sup];exact mem_map_of_mem qR hm
  have hdimP':ringKrullDim (z0 k n⧸Pbar)=ringKrullDim (R⧸P'):=by
   let g:R →+* z0 k n⧸Pbar:=(Ideal.Quotient.mk Pbar).comp qR;have q22:Surjective g:=Ideal.Quotient.mk_surjective.comp q9
   have q41:RingHom.ker g=P':=by
    ext x;rw [RingHom.mem_ker,RingHom.comp_apply,Ideal.Quotient.eq_zero_iff_mem,mem_map_iff_of_surjective qR q9];constructor
    ·
     rintro ⟨y,hy,hyx⟩
     have q54:x - y∈RingHom.ker qR:=by rw [RingHom.mem_ker,map_sub,hyx,sub_self]
     have:=Ideal.add_mem _ hy (hkerP' q54);simpa using this
    · intro hx;exact ⟨x,hx,rfl⟩
   exact (ringKrullDim_eq_of_ringEquiv
    ((Ideal.quotEquivOfEq q41.symm).trans (RingHom.quotientKerEquivOfSurjective q22))).symm
  have hdimQ':ringKrullDim (z0 k n⧸Qbar)=ringKrullDim (R⧸Q'):=by
   let g:R →+* z0 k n⧸Qbar:=(Ideal.Quotient.mk Qbar).comp qR;have q22:Surjective g:=Ideal.Quotient.mk_surjective.comp q9
   have q41:RingHom.ker g=Q':=by
    ext x;rw [RingHom.mem_ker,RingHom.comp_apply,Ideal.Quotient.eq_zero_iff_mem,mem_map_iff_of_surjective qR q9];constructor
    ·
     rintro ⟨y,hy,hyx⟩
     have q54:x - y∈RingHom.ker qR:=by rw [RingHom.mem_ker,map_sub,hyx,sub_self]
     have:=Ideal.add_mem _ hy (hkerQ' q54);simpa using this
    · intro hx;exact ⟨x,hx,rfl⟩
   exact (ringKrullDim_eq_of_ringEquiv
    ((Ideal.quotEquivOfEq q41.symm).trans (RingHom.quotientKerEquivOfSurjective q22))).symm
  have hf:=z54 n Pbar Qbar q11;dsimp only at hf;rw [hdimP',hdimQ',z11 k n,ringKrullDim_eq_zero_of_field k,zero_add] at hf;let Tbar:=z0 (z0 k n) n;let qT:T →+* Tbar:=z15 qR n;have q16:Surjective qT:=z22 q9 n;let Ibar:Ideal Tbar:=Pbar.map (z15 (z13 k n) n)⊔Qbar.map (z13 (z0 k n) n);let fT:T →+* Tbar⧸Ibar:=(Ideal.Quotient.mk Ibar).comp qT
  have q13:Surjective fT:=Ideal.Quotient.mk_surjective.comp q16
  have q18:P'.map i₁ ⊔ Q'.map i₂ ≤ RingHom.ker fT:=by
   refine sup_le ?_ ?_
   ·
    rw [map_le_iff_le_comap];intro x hx;rw [mem_comap,RingHom.mem_ker,RingHom.comp_apply,Ideal.Quotient.eq_zero_iff_mem]
    have q53:qT (i₁ x)=z15 (z13 k n) n (qR x):=by
     have heq:qT.comp i₁ = (z15 (z13 k n) n).comp qR:=by
      have : ∀ m : ℕ,(z15 qR m).comp (z15 (z13 V n) m)=(z15 (z13 k n) m).comp (z15 (Ideal.Quotient.mk (maximalIdeal V)) m):=by
       intro m
       induction m with
       | zero =>
        ext c;change qR (z13 V n c)=z13 k n (Ideal.Quotient.mk (maximalIdeal V) c);exact z19 (Ideal.Quotient.mk (maximalIdeal V)) n c
       | succ m ihm =>
        ext F j;simp only [RingHom.comp_apply,z15,PowerSeries.coeff_map];exact RingHom.congr_fun ihm (PowerSeries.coeff j F)
      exact this n
     exact RingHom.congr_fun heq x
    rw [q53];exact mem_sup_left (mem_map_of_mem _ (mem_map_of_mem qR hx))
   ·
    rw [map_le_iff_le_comap];intro x hx;rw [mem_comap,RingHom.mem_ker,RingHom.comp_apply,Ideal.Quotient.eq_zero_iff_mem];have q53:qT (i₂ x)=z13 (z0 k n) n (qR x):=z19 qR n x;rw [q53];exact mem_sup_right (mem_map_of_mem _ (mem_map_of_mem qR hx))
  let q44:(T⧸(P'.map i₁ ⊔ Q'.map i₂)) →+* (Tbar⧸Ibar):=Ideal.Quotient.lift (P'.map i₁ ⊔ Q'.map i₂) fT q18
  have q0:Surjective q44:=fun y=>by
   obtain ⟨t,rfl⟩:=q13 y;exact ⟨Ideal.Quotient.mk _ t,rfl⟩
  have q6:=ringKrullDim_le_of_surjective q44 q0;exact ⟨hf.1.trans q6,hf.2⟩
 have q4:∀ (J:Ideal R) [J.IsPrime],z13 V n p∉J →
   ringKrullDim (R⧸(J⊔span {z13 V n p}))+1=ringKrullDim (R⧸J):=by
  intro J _ hpJ;have : IsLocalRing (R⧸J):=z36 J;let q56:R⧸J:=Ideal.Quotient.mk J (z13 V n p)
  have q15:q56≠0:=fun h=>hpJ (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have q8:q56∈nonZeroDivisors (R⧸J):=mem_nonZeroDivisors_of_ne_zero q15
  have q5:q56∈maximalIdeal (R⧸J):=by
   have q43:(maximalIdeal (R⧸J)).comap (Ideal.Quotient.mk J)=maximalIdeal R:=eq_maximalIdeal (comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective);rw [← mem_comap,q43];exact z17 n (hp▸subset_span rfl)
  have h1:=ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
   q8 q5
  have q14:((R⧸J)⧸span {q56}) ≃+* (R⧸(J⊔span {z13 V n p})):=by
   let g:R →+* (R⧸J)⧸span {q56}:=(Ideal.Quotient.mk (span {q56})).comp (Ideal.Quotient.mk J);have q22:Surjective g:=Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
   have q41:RingHom.ker g=J⊔span {z13 V n p}:=by
    ext x;rw [RingHom.mem_ker,RingHom.comp_apply,Ideal.Quotient.eq_zero_iff_mem,mem_span_singleton];constructor
    ·
     rintro ⟨q,hq⟩;obtain ⟨r,rfl⟩:=Ideal.Quotient.mk_surjective q
     have q54:x - z13 V n p*r∈J:=by
      rw [← Ideal.Quotient.eq_zero_iff_mem,map_sub,map_mul];exact sub_eq_zero.mpr hq
     have q55:(x - z13 V n p*r)+z13 V n p*r∈J⊔span {z13 V n p} :=
      Ideal.add_mem _ (mem_sup_left q54)
       (mem_sup_right (mem_span_singleton.mpr ⟨r,rfl⟩))
     simpa using q55
    ·
     intro hx;obtain ⟨a,ha,b,hb,rfl⟩:=Submodule.mem_sup.mp hx;obtain ⟨r,rfl⟩:=mem_span_singleton.mp hb
     refine ⟨Ideal.Quotient.mk J r,?_⟩
     rw [map_add,Ideal.Quotient.eq_zero_iff_mem.mpr ha,zero_add,map_mul]
   exact ((Ideal.quotEquivOfEq q41.symm).trans
    (RingHom.quotientKerEquivOfSurjective q22)).symm
  rw [ringKrullDim_eq_of_ringEquiv q14] at h1;exact h1
 by_cases hpP:z13 V n p∈P
 ·
  by_cases hpQ:z13 V n p∈Q
  ·
   have hB1:=(q2 P Q hpP hpQ hPQ).2
   refine ⟨hB1.trans ?_,fun heq => ?_⟩
   ·
    rw [q52];exact_mod_cast Nat.le_succ n
   ·
    rw [heq,q52] at hB1
    have : n+1 ≤ n:=by exact_mod_cast hB1
    omega
  ·
   have q42:Q⊔span {z13 V n p} ≠ ⊤ := by
    refine ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top (sup_le
     (le_maximalIdeal ‹Q.IsPrime›.ne_top)
     ((span_singleton_le_iff_mem _).mpr (z17 n (hp▸subset_span rfl))))
   obtain ⟨Q',hQ'_prime,hQ'_ge,hQ'_dim⟩ :=
    exists_prime_ge_with_ringKrullDim_eq
     (Q⊔span {z13 V n p}) q42
   have : Q'.IsPrime:=hQ'_prime;have hpQ':z13 V n p∈Q':=hQ'_ge (mem_sup_right (subset_span rfl));have hQQ':Q ≤ Q':=le_sup_left.trans hQ'_ge
   have q10:(P⊔Q').radical=maximalIdeal R:=by
    refine le_antisymm ?_ ?_
    ·
     rw [← (maximalIdeal.isMaximal R).isPrime.radical]
     exact Ideal.radical_mono (sup_le (le_maximalIdeal ‹P.IsPrime›.ne_top)
      (le_maximalIdeal hQ'_prime.ne_top))
    ·
     rw [← hPQ];exact Ideal.radical_mono (sup_le_sup le_rfl hQQ')
   have q60:=q2 P Q' hpP hpQ' q10
   have q27:ringKrullDim (T⧸(P.map i₁ ⊔ Q'.map i₂)) ≤
     ringKrullDim (T⧸(P.map i₁ ⊔ Q.map i₂)) :=
    ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective
     (sup_le_sup le_rfl (Ideal.map_mono hQQ')))
   have q19:ringKrullDim (R⧸Q')+1=ringKrullDim (R⧸Q):=by
    rw [hQ'_dim];exact q4 Q hpQ
   obtain ⟨r,hr⟩ :=
    ringKrullDim_quotient_eq_natCast
     P ‹P.IsPrime›.ne_top
   obtain ⟨s',hs'⟩ :=
    ringKrullDim_quotient_eq_natCast
     Q' hQ'_prime.ne_top
   have hs:ringKrullDim (R⧸Q)=((s'+1 : ℕ) : WithBot ℕ∞):=by
    rw [← q19,hs'];push_cast;rfl
   have q24:r+s' ≤ n:=by
    have:=q60.2;rw [hr,hs'] at this;exact_mod_cast this
   refine ⟨?_,fun heq=>⟨Or.inr hpQ,?_⟩⟩
   ·
    rw [hr,hs,q52];exact_mod_cast (show r+(s'+1) ≤ n+1 by omega)
   ·
    rw [hr,hs,q52] at heq
    have q26:r+(s'+1)=n+1:=by exact_mod_cast heq
    have q50:(n:WithBot ℕ∞) ≤ ringKrullDim (T⧸(P.map i₁ ⊔ Q.map i₂)):=by
     have h1:=q60.1.trans q27;rw [hr,hs'] at h1
     have q21:((n : ℕ) : WithBot ℕ∞)=(r:WithBot ℕ∞)+(s':WithBot ℕ∞):=by
      have : n=r+s':=by omega
      rw [this];push_cast;rfl
     exact q21.le.trans h1
    exact le_antisymm q48 q50
 ·
  by_cases hpQ:z13 V n p∈Q
  ·
   have q37:P⊔span {z13 V n p} ≠ ⊤ := by
    refine ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top (sup_le
     (le_maximalIdeal ‹P.IsPrime›.ne_top)
     ((span_singleton_le_iff_mem _).mpr (z17 n (hp▸subset_span rfl))))
   obtain ⟨P',hP'_prime,hP'_ge,hP'_dim⟩ :=
    exists_prime_ge_with_ringKrullDim_eq
     (P⊔span {z13 V n p}) q37
   have : P'.IsPrime:=hP'_prime;have hpP':z13 V n p∈P':=hP'_ge (mem_sup_right (subset_span rfl));have hPP':P ≤ P':=le_sup_left.trans hP'_ge
   have q12:(P'⊔Q).radical=maximalIdeal R:=by
    refine le_antisymm ?_ ?_
    ·
     rw [← (maximalIdeal.isMaximal R).isPrime.radical]
     exact Ideal.radical_mono (sup_le (le_maximalIdeal hP'_prime.ne_top)
      (le_maximalIdeal ‹Q.IsPrime›.ne_top))
    ·
     rw [← hPQ];exact Ideal.radical_mono (sup_le_sup hPP' le_rfl)
   have q60:=q2 P' Q hpP' hpQ q12
   have q27:ringKrullDim (T⧸(P'.map i₁ ⊔ Q.map i₂)) ≤
     ringKrullDim (T⧸(P.map i₁ ⊔ Q.map i₂)) :=
    ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective
     (sup_le_sup (Ideal.map_mono hPP') le_rfl))
   have q25:ringKrullDim (R⧸P')+1=ringKrullDim (R⧸P):=by
    rw [hP'_dim];exact q4 P hpP
   obtain ⟨r',hr'⟩ :=
    ringKrullDim_quotient_eq_natCast
     P' hP'_prime.ne_top
   obtain ⟨s,hs⟩ :=
    ringKrullDim_quotient_eq_natCast
     Q ‹Q.IsPrime›.ne_top
   have hr:ringKrullDim (R⧸P)=((r'+1 : ℕ) : WithBot ℕ∞):=by
    rw [← q25,hr'];push_cast;rfl
   have q24:r'+s ≤ n:=by
    have:=q60.2;rw [hr',hs] at this;exact_mod_cast this
   refine ⟨?_,fun heq=>⟨Or.inl hpP,?_⟩⟩
   ·
    rw [hr,hs,q52];exact_mod_cast (show (r'+1)+s ≤ n+1 by omega)
   ·
    rw [hr,hs,q52] at heq
    have q26:(r'+1)+s=n+1:=by exact_mod_cast heq
    have q50:(n:WithBot ℕ∞) ≤ ringKrullDim (T⧸(P.map i₁ ⊔ Q.map i₂)):=by
     have h1:=q60.1.trans q27;rw [hr',hs] at h1
     have q21:((n : ℕ) : WithBot ℕ∞)=(r':WithBot ℕ∞)+(s:WithBot ℕ∞):=by
      have : n=r'+s:=by omega
      rw [this];push_cast;rfl
     exact q21.le.trans h1
    exact le_antisymm q48 q50
  ·
   have q37:P⊔span {z13 V n p} ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top (sup_le
     (le_maximalIdeal ‹P.IsPrime›.ne_top)
     ((span_singleton_le_iff_mem _).mpr (z17 n (hp▸subset_span rfl))))
   have q42:Q⊔span {z13 V n p} ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top (sup_le
     (le_maximalIdeal ‹Q.IsPrime›.ne_top)
     ((span_singleton_le_iff_mem _).mpr (z17 n (hp▸subset_span rfl))))
   obtain ⟨r',hr'⟩ :=
    ringKrullDim_quotient_eq_natCast
     (P⊔span {z13 V n p}) q37
   obtain ⟨s',hs'⟩ :=
    ringKrullDim_quotient_eq_natCast
     (Q⊔span {z13 V n p}) q42
   have hr:ringKrullDim (R⧸P)=((r'+1 : ℕ) : WithBot ℕ∞):=by
    rw [← q4 P hpP,hr'];push_cast;rfl
   have hs:ringKrullDim (R⧸Q)=((s'+1 : ℕ) : WithBot ℕ∞):=by
    rw [← q4 Q hpQ,hs'];push_cast;rfl
   have : Nontrivial (R⧸(P⊔span {z13 V n p})):=Ideal.Quotient.nontrivial_iff.mpr q37;have : Nontrivial (R⧸(Q⊔span {z13 V n p})):=Ideal.Quotient.nontrivial_iff.mpr q42;have : IsLocalRing (R⧸(P⊔span {z13 V n p})):=z36 _;have : IsLocalRing (R⧸(Q⊔span {z13 V n p})):=z36 _;obtain ⟨u',hu'_mem,hu'_rad⟩:=z39 r' (R⧸(P⊔span {z13 V n p})) hr'
   obtain ⟨v',hv'_mem,hv'_rad⟩:=z39 s' (R⧸(Q⊔span {z13 V n p})) hs'
   let u:Fin r'→R:=fun i=>(Ideal.Quotient.mk_surjective (u' i)).choose
   have q49:∀ i,Ideal.Quotient.mk (P⊔span {z13 V n p}) (u i)=u' i:=fun i=>(Ideal.Quotient.mk_surjective (u' i)).choose_spec
   let v:Fin s'→R:=fun j=>(Ideal.Quotient.mk_surjective (v' j)).choose
   have q46:∀ j,Ideal.Quotient.mk (Q⊔span {z13 V n p}) (v j)=v' j:=fun j=>(Ideal.Quotient.mk_surjective (v' j)).choose_spec
   have q40:(maximalIdeal (R⧸(P⊔span {z13 V n p}))).comap
     (Ideal.Quotient.mk _)=maximalIdeal R :=
    eq_maximalIdeal (comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
   have q31:(maximalIdeal (R⧸(Q⊔span {z13 V n p}))).comap
     (Ideal.Quotient.mk _)=maximalIdeal R :=
    eq_maximalIdeal (comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
   have q36:∀ i,u i∈maximalIdeal R:=fun i=>by
    rw [← q40,mem_comap,q49 i];exact hu'_mem i
   have q29:∀ j,v j∈maximalIdeal R:=fun j=>by
    rw [← q31,mem_comap,q46 j];exact hv'_mem j
   have q1:∀ {J:Ideal R} [J.IsPrime] {m : ℕ} (w:Fin m→R)
     (w':Fin m→R⧸(J⊔span {z13 V n p}))
     (_:IsLocalRing (R⧸(J⊔span {z13 V n p}))),
     (∀ i,Ideal.Quotient.mk (J⊔span {z13 V n p}) (w i)=w' i) →
     (∀ i,w i∈maximalIdeal R) →
     (span (Set.range w')).radical=maximalIdeal (R⧸(J⊔span {z13 V n p})) →
     ((maximalIdeal V).map (z13 V n)⊔span (Set.range w)⊔J).radical=maximalIdeal R:=by
    intro J _ m w w' _ hw_eq hw_mem hw'_rad
    have q30:(maximalIdeal (R⧸(J⊔span {z13 V n p}))).comap
      (Ideal.Quotient.mk _)=maximalIdeal R :=
     eq_maximalIdeal (comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
    refine le_antisymm ?_ ?_
    ·
     rw [← (maximalIdeal.isMaximal R).isPrime.radical]
     refine Ideal.radical_mono (sup_le (sup_le ?_ ?_) (le_maximalIdeal ‹J.IsPrime›.ne_top))
     · rw [map_le_iff_le_comap];intro c hc;exact z17 n hc
     · rw [span_le];rintro _ ⟨i,rfl⟩;exact hw_mem i
    ·
     intro x hx
     have hx':Ideal.Quotient.mk (J⊔span {z13 V n p}) x ∈
       (span (Set.range w')).radical:=by
      rw [hw'_rad,← mem_comap,q30];exact hx
     obtain ⟨t,ht⟩:=hx';rw [← map_pow] at ht
     have q57:span (Set.range w')=(span (Set.range w)).map (Ideal.Quotient.mk (J⊔span {z13 V n p})):=by
      rw [map_span];congr 1;ext y;simp [hw_eq]
     rw [q57,mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at ht;obtain ⟨y,hy_span,hy_eq⟩:=ht
     have q54:x ^ t - y∈J⊔span {z13 V n p}:=by
      rw [← Ideal.Quotient.eq_zero_iff_mem,map_sub,hy_eq,sub_self]
     obtain ⟨a,haJ,b,hbp,hab⟩:=Submodule.mem_sup.mp q54
     have hbp':b∈(maximalIdeal V).map (z13 V n):=by
      rw [hp,map_span,Set.image_singleton];exact hbp
     refine ⟨t,?_⟩
     have q55:=Ideal.add_mem _ (mem_sup_left (mem_sup_right hy_span))
      (Ideal.add_mem _ (mem_sup_right haJ) (mem_sup_left (mem_sup_left hbp')))
     have heq:y+(a+b)=x ^ t:=by rw [hab];ring
     rwa [heq] at q55
   have q32:=q1 u u' inferInstance q49 q36 hu'_rad;have q34:=q1 v v' inferInstance q46 q29 hv'_rad
   have q28:∀ {J:Ideal R} [J.IsPrime] {m : ℕ} (w:Fin m→R)
     (_:IsLocalRing (R⧸J)),
     ringKrullDim (R⧸J)=((m+1 : ℕ) : WithBot ℕ∞) →
     ((maximalIdeal V).map (z13 V n)⊔span (Set.range w)⊔J).radical=maximalIdeal R →
     ∀ f:z0 V m →+* R⧸J,(∀ c,f (z13 V m c)=Ideal.Quotient.mk J (z13 V n c))→(∀ i,f (z14 V i)=Ideal.Quotient.mk J (w i))→Injective f:=by
    intro J _ m w _ hdimJ hw_rad f hfC hfvar;have q43:(maximalIdeal (R⧸J)).comap (Ideal.Quotient.mk J)=maximalIdeal R:=eq_maximalIdeal (comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
    have q38:∀ x∈maximalIdeal (z0 V m),f x∈maximalIdeal (R⧸J):=by
     intro x hx;rw [z34 m] at hx
     have q45:(maximalIdeal V).map (z13 V m)⊔span (Set.range (z14 V (n:=m))) ≤ (maximalIdeal (R⧸J)).comap f:=by
      refine sup_le ?_ ?_
      ·
       rw [map_le_iff_le_comap];intro c hc;rw [mem_comap,mem_comap,hfC,← mem_comap,q43];exact z17 n hc
      ·
       rw [span_le];rintro _ ⟨i,rfl⟩;rw [SetLike.mem_coe,mem_comap,hfvar]
       have hwi:w i∈maximalIdeal R:=by
        rw [← hw_rad];exact Ideal.le_radical (mem_sup_left (mem_sup_right (subset_span ⟨i,rfl⟩)))
       rw [← mem_comap,q43];exact hwi
     exact q45 hx
    have q35:Surjective ((residue (R⧸J)).comp f):=by
     intro y;obtain ⟨r,rfl⟩:=residue_surjective y;obtain ⟨x,rfl⟩:=Ideal.Quotient.mk_surjective r;obtain ⟨c,hc⟩:=z35 n (residue R x)
     refine ⟨z13 V m c,?_⟩
     rw [RingHom.comp_apply,hfC]
     symm
     rw [← sub_eq_zero,← map_sub,residue_eq_zero_iff,← map_sub,← mem_comap,q43,← residue_eq_zero_iff,map_sub];change residue R x - ((residue R).comp (z13 V n)) c=0;rw [hc,sub_self]
    have q33:((maximalIdeal (z0 V m)).map f).radical=maximalIdeal (R⧸J):=by
     refine le_antisymm ?_ ?_
     ·
      rw [← (maximalIdeal.isMaximal (R⧸J)).isPrime.radical];exact Ideal.radical_mono (map_le_iff_le_comap.mpr q38)
     ·
      intro x hx;obtain ⟨y,rfl⟩:=Ideal.Quotient.mk_surjective x;have hy:y∈maximalIdeal R:=q43▸hx;rw [← hw_rad] at hy;obtain ⟨t,ht⟩:=hy
      refine ⟨t,?_⟩
      rw [← map_pow]
      have hle:((maximalIdeal V).map (z13 V n)⊔span (Set.range w)⊔J).map
        (Ideal.Quotient.mk J) ≤ (maximalIdeal (z0 V m)).map f:=by
       rw [Ideal.map_sup,Ideal.map_sup]
       refine sup_le (sup_le ?_ ?_) ?_
       ·
        rw [map_le_iff_le_comap,map_le_iff_le_comap];intro c hc;rw [mem_comap,mem_comap,← hfC c];exact mem_map_of_mem f (z17 m hc)
       ·
        rw [map_span,span_le];rintro _ ⟨_,⟨i,rfl⟩,rfl⟩;rw [← hfvar i];exact mem_map_of_mem f (z18 i)
       ·
        rw [map_le_iff_le_comap];intro a ha;rw [mem_comap,Ideal.Quotient.eq_zero_iff_mem.mpr ha];exact Ideal.zero_mem _
      exact hle (mem_map_of_mem (Ideal.Quotient.mk J) ht)
    let _:Algebra (z0 V m) (R⧸J):=f.toAlgebra;have : Module.Finite (z0 V m) (R⧸J):=z40 q38 q35 q33;rw [RingHom.injective_iff_ker_eq_bot]
    by_contra hker_ne
    have q17:RingHom.ker f ≠ ⊤ := by
     intro q58;have h1:(1:z0 V m)∈RingHom.ker f:=q58▸Submodule.mem_top;rw [RingHom.mem_ker,map_one] at h1;exact one_ne_zero h1
    let q59:(z0 V m⧸RingHom.ker f) →+* R⧸J:=Ideal.Quotient.lift (RingHom.ker f) f (fun _ h=>h)
    have q7:Injective q59:=RingHom.kerLift_injective f;let _:Algebra (z0 V m⧸RingHom.ker f) (R⧸J):=q59.toAlgebra
    have : Module.Finite (z0 V m⧸RingHom.ker f) (R⧸J):=by
     obtain ⟨S,hS⟩:=Module.Finite.fg_top (R:=z0 V m) (M:=R⧸J)
     refine ⟨⟨S,eq_top_iff.mpr fun x _ => ?_⟩⟩
     have hx:x∈Submodule.span (z0 V m) (S:Set (R⧸J)):=hS▸Submodule.mem_top;rw [Submodule.mem_span_finset] at hx ⊢;obtain ⟨c,hc,rfl⟩:=hx
     refine ⟨fun s=>Ideal.Quotient.mk (RingHom.ker f) (c s),fun s hs => ?_,?_⟩
     · exact hc (fun h0=>hs (by simp [h0]))
     ·
      refine Finset.sum_congr rfl fun s _ => ?_
      rfl
    have : Algebra.IsIntegral (z0 V m⧸RingHom.ker f) (R⧸J):=Algebra.IsIntegral.of_finite _ _;have q23:=z37 q7;have hlt:=z38 hker_ne q17;rw [← q23,hdimJ,z11 V m,q51] at hlt
    have q47:((m+1 : ℕ) : WithBot ℕ∞)=1+(m:WithBot ℕ∞):=by
     push_cast;rw [add_comm]
    rw [q47] at hlt;exact lt_irrefl _ hlt
   have hge:=z44 (Λ := V) n P Q r' s' u q36 v q29 q32 q34
    (q28 u inferInstance hr q32) (q28 v inferInstance hs q34)
   rw [q51] at hge;have q39:(1:WithBot ℕ∞)+(s':WithBot ℕ∞)+(r':WithBot ℕ∞) ≤ (n:WithBot ℕ∞):=hge.trans q48
   have hnat:1+s'+r' ≤ n:=by exact_mod_cast q39
   refine ⟨?_,fun heq=>⟨Or.inl hpP,?_⟩⟩
   ·
    rw [hr,hs,q52];exact_mod_cast (show (r'+1)+(s'+1) ≤ n+1 by omega)
   ·
    rw [hr,hs,q52] at heq
    have q26:(r'+1)+(s'+1)=n+1:=by exact_mod_cast heq
    have q50:(n:WithBot ℕ∞) ≤ ringKrullDim (T⧸(P.map i₁ ⊔ Q.map i₂)):=by
     have q21:((n : ℕ) : WithBot ℕ∞)=(1:WithBot ℕ∞)+(s':WithBot ℕ∞)+(r':WithBot ℕ∞):=by
      have : n=1+s'+r':=by omega
      rw [this];push_cast;rfl
     exact q21.le.trans hge
    exact le_antisymm q48 q50
end DimensionInequality
section TorAndFlatness
noncomputable abbrev z56 (R:Type) [CommRing R]
  (M N:Type) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (i : ℕ) : ModuleCat.{0} R :=
 ((Tor (ModuleCat.{0} R) i).obj (ModuleCat.of R M)).obj (ModuleCat.of R N)
noncomputable def z57 {R:Type} [CommRing R]
  (M:Type) [AddCommGroup M] [Module R M]
  {A B:Type} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  (f:A →ₗ[R] B) (i : ℕ) :
  z56 R M A i →ₗ[R] z56 R M B i :=
 (((Tor (ModuleCat.{0} R) i).obj (ModuleCat.of R M)).map (ModuleCat.ofHom f)).hom
noncomputable def z58 {R:Type} [CommRing R]
  {A B:Type} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  (f:A →ₗ[R] B) (N:Type) [AddCommGroup N] [Module R N] (i : ℕ) :
  z56 R A N i →ₗ[R] z56 R B N i :=
 (((Tor (ModuleCat.{0} R) i).map (ModuleCat.ofHom f)).app (ModuleCat.of R N)).hom
noncomputable def z59 (R:Type) [CommRing R]
  (M N:Type) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] :
  z56 R M N 0 ≃ₗ[R] (M ⊗[R] N) :=
 (((tensoringLeft (ModuleCat.{0} R)).obj (ModuleCat.of R M)).leftDerivedZeroIsoSelf.app
  (ModuleCat.of R N)).toLinearEquiv
lemma z60 {R:Type} [CommRing R]
  (M:Type) [AddCommGroup M] [Module R M]
  {A B:Type} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  (f:A →ₗ[R] B) (x:z56 R M A 0) :
  z59 R M B (z57 M f 0 x)=LinearMap.lTensor M f (z59 R M A x):=by
 have q0:=(((tensoringLeft (ModuleCat.{0} R)).obj
  (ModuleCat.of R M)).leftDerivedZeroIsoSelf.hom.naturality (ModuleCat.ofHom f))
 exact congrArg (fun φ : z56 R M A 0 ⟶ ModuleCat.of R (M ⊗[R] B) => φ.hom x) q0
lemma z61 {R:Type} [CommRing R]
  (M N:Type) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [Module.Projective R N] (i : ℕ) :
  Subsingleton (z56 R M N (i+1)) :=
 ModuleCat.isZero_iff_subsingleton.mp
  (isZero_Tor_succ_of_projective (ModuleCat.{0} R) (ModuleCat.of R M) (ModuleCat.of R N) i)
noncomputable def z62 {R:Type} [CommRing R]
  (B:Type) [AddCommGroup B] [Module R B]
  (K:ChainComplex (ModuleCat.{0} R) ℕ)
  (q5:∀ n,Module.Projective R (K.X n))
  (ε : (K.X 0) →ₗ[R] B)
  (hε_surj:Surjective ε)
  (hε_comp:∀ x:K.X 1,ε ((K.d 1 0).hom x)=0)
  (hε_exact:∀ x:K.X 0,ε x=0→∃ y:K.X 1,(K.d 1 0).hom y=x)
  (q4:∀ n : ℕ,∀ x:K.X (n+1),(K.d (n+1) n).hom x=0→∃ y:K.X (n+2),(K.d (n+2) (n+1)).hom y=x) :
  ProjectiveResolution (ModuleCat.of R B):=by
 let π : K ⟶ (ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B) :=
  (ChainComplex.toSingle₀Equiv K (ModuleCat.of R B)).symm
   ⟨ModuleCat.ofHom ε,by ext x;exact hε_comp x⟩
 have hπ0:(π.f 0).hom = ε := by
  change ((ChainComplex.toSingle₀Equiv K (ModuleCat.of R B)).symm
   ⟨ModuleCat.ofHom ε,_⟩ |>.f 0).hom = ε
  rw [ChainComplex.toSingle₀Equiv_symm_apply_f_zero];rfl
 have hq:QuasiIso π := by
  rw [quasiIso_iff];intro n
  cases n with
  | zero =>
   rw [quasiIsoAt_iff_isIso_homologyMap];have q8:(K.sc 0).g=0:=K.shape 0 _ (by simp);have q6:(((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).sc 0).g=0:=((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).shape 0 _ (by simp);have _:IsIso (K.homologyι 0):=ShortComplex.isIso_homologyι (K.sc 0) q8
   have _:IsIso (((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).homologyι 0):=ShortComplex.isIso_homologyι _ q6
   have q7:(HomologicalComplex.homologyMap π 0 ≫
     ((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).homologyι 0) =
     (K.homologyι 0 ≫ HomologicalComplex.opcyclesMap π 0) :=
    HomologicalComplex.homologyι_naturality π 0
   have q2:Bijective (HomologicalComplex.opcyclesMap π 0).hom:=by
    constructor
    ·
     intro u v huv;have q3:Surjective (K.pOpcycles 0):=(ModuleCat.epi_iff_surjective (K.pOpcycles 0)).mp inferInstance;obtain ⟨x,rfl⟩:=q3 u;obtain ⟨y,rfl⟩:=q3 v
     have q10:HomologicalComplex.opcyclesMap π 0 (K.pOpcycles 0 (x - y))=0:=by
      change (HomologicalComplex.opcyclesMap π 0).hom ((K.pOpcycles 0).hom (x - y))=0;rw [map_sub,map_sub,huv,sub_self]
     have q11:(HomologicalComplex.opcyclesMap π 0).hom ((K.pOpcycles 0).hom (x - y)) =
       (((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).pOpcycles 0).hom
        ((π.f 0).hom (x - y)) :=
      congrArg (fun φ : K.X 0 ⟶
       ((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).opcycles 0 =>
        φ.hom (x - y))
       (ShortComplex.p_opcyclesMap ((HomologicalComplex.shortComplexFunctor _ _ 0).map π))
     rw [q11] at q10;have q13:=(ShortComplex.moduleCat_pOpcycles_eq_zero_iff _ _).mp q10
     have q9:(((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).sc 0).f=0:=by
      simp [HomologicalComplex.sc];rfl
     obtain ⟨w,hw⟩:=q13
     have hε0 : ε (x - y)=0:=by
      rw [← hπ0]
      have hw0:((((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).sc 0).f).hom w=0:=by
       rw [q9];rfl
      exact hw.symm.trans hw0
     obtain ⟨z,hz⟩:=hε_exact (x - y) hε0
     have h0:(K.pOpcycles 0).hom (x - y)=0:=by
      rw [← hz]
      exact congrArg (fun φ : K.X 1 ⟶ K.opcycles 0 => φ.hom z) (K.d_pOpcycles 1 0)
     rw [map_sub] at h0;exact sub_eq_zero.mp h0
    ·
     intro w
     have q0:Surjective
       (((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).pOpcycles 0) :=
      (ModuleCat.epi_iff_surjective _).mp inferInstance
     obtain ⟨b,rfl⟩:=q0 w;obtain ⟨x,hx⟩:=hε_surj b
     refine ⟨K.pOpcycles 0 x,?_⟩
     have q11:(HomologicalComplex.opcyclesMap π 0).hom ((K.pOpcycles 0).hom x) =
       (((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).pOpcycles 0).hom
        ((π.f 0).hom x) :=
      congrArg (fun φ : K.X 0 ⟶
       ((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).opcycles 0 =>
        φ.hom x)
       (ShortComplex.p_opcyclesMap ((HomologicalComplex.shortComplexFunctor _ _ 0).map π))
     change (HomologicalComplex.opcyclesMap π 0).hom ((K.pOpcycles 0).hom x)=_;rw [q11]
     have hxb:(π.f 0).hom x=b:=by
      have h1:(π.f 0).hom x = ε x:=LinearMap.congr_fun hπ0 x;exact h1.trans hx
     exact congrArg
      (((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).pOpcycles 0).hom hxb
   have q1:IsIso (HomologicalComplex.opcyclesMap π 0) :=
    ⟨ModuleCat.ofHom (LinearEquiv.ofBijective _ q2).symm.toLinearMap,by ext u;exact (LinearEquiv.ofBijective _ q2).left_inv u,by ext v;exact (LinearEquiv.ofBijective _ q2).right_inv v⟩
   have q12:HomologicalComplex.homologyMap π 0 =
     K.homologyι 0 ≫ HomologicalComplex.opcyclesMap π 0 ≫
      inv (((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).homologyι 0):=by
    rw [← Category.assoc,← q7,Category.assoc,IsIso.hom_inv_id,Category.comp_id]
   rw [q12]
   infer_instance
  | succ m =>
   rw [quasiIsoAt_iff_exactAt' π (m+1) (ChainComplex.exactAt_succ_single_obj _ _)];rw [HomologicalComplex.exactAt_iff' K (m+2) (m+1) m (by simp) (by simp)];rw [ShortComplex.moduleCat_exact_iff];exact q4 m
 exact
  {
   complex:=K
   projective:=fun n=>by
    let _:=q5 n
    infer_instance
   π := π
   quasiIso:=hq }
lemma z63 {R:Type} [CommRing R]
  (M:Type) [AddCommGroup M] [Module R M]
  {A B C:Type} [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
  (i:A →ₗ[R] B) (p:B →ₗ[R] C)
  (hi:Injective i) (hp:Surjective p)
  (hip:LinearMap.range i=LinearMap.ker p) :
  ∃ δ : ∀ n : ℕ,z56 R M C (n+1) →ₗ[R] z56 R M A n,(∀ n,Function.Exact (δ n) (z57 M i n))∧(∀ n,Function.Exact (z57 M i n) (z57 M p n))∧(∀ n,Function.Exact (z57 M p (n+1)) (δ n)):=by
 let PA:ProjectiveResolution (ModuleCat.of R A):=projectiveResolution (ModuleCat.of R A);let PC:ProjectiveResolution (ModuleCat.of R C):=projectiveResolution (ModuleCat.of R C);have hPA_proj (n : ℕ) : Module.Projective R (PA.complex.X n):=ModuleCat.projective_of_module_projective (P:=PA.complex.X n)
 have hPC_proj (n : ℕ) : Module.Projective R (PC.complex.X n):=ModuleCat.projective_of_module_projective (P:=PC.complex.X n);let εA:PA.complex.X 0 →ₗ[R] A:=(PA.π.f 0).hom;let εC:PC.complex.X 0 →ₗ[R] C:=(PC.π.f 0).hom;have hεA_surj:Surjective εA:=(ModuleCat.epi_iff_surjective (PA.π.f 0)).mp inferInstance
 have hεC_surj:Surjective εC:=(ModuleCat.epi_iff_surjective (PC.π.f 0)).mp inferInstance
 have hεA_comp (x:PA.complex.X 1) : εA ((PA.complex.d 1 0).hom x)=0 :=
  congrArg (fun φ : PA.complex.X 1 ⟶ ModuleCat.of R A => φ.hom x) PA.complex_d_comp_π_f_zero
 have hεC_comp (x:PC.complex.X 1) : εC ((PC.complex.d 1 0).hom x)=0 :=
  congrArg (fun φ : PC.complex.X 1 ⟶ ModuleCat.of R C => φ.hom x) PC.complex_d_comp_π_f_zero
 have hε_exact_of_res {X:Type} [AddCommGroup X] [Module R X]
   (PX:ProjectiveResolution (ModuleCat.of R X)) (x:PX.complex.X 0)
   (hx:(PX.π.f 0).hom x=0) :
   ∃ y:PX.complex.X 1,(PX.complex.d 1 0).hom y=x:=by
  let Q:=PX.complex.X 0⧸LinearMap.range (PX.complex.d 1 0).hom;let q:PX.complex.X 0 ⟶ ModuleCat.of R Q:=ModuleCat.ofHom (LinearMap.range (PX.complex.d 1 0).hom).mkQ
  have hqw:(PX.complex.d 1 0 ≫ q)=0:=by
   ext z;exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨z,rfl⟩
  let desc:ModuleCat.of R X ⟶ ModuleCat.of R Q:=PX.isColimitCokernelCofork.desc (CokernelCofork.ofπ q hqw);have q17:(PX.π.f 0 ≫ desc)=q:=PX.isColimitCokernelCofork.fac (CokernelCofork.ofπ q hqw) WalkingParallelPair.one
  have hqx:q.hom x=0:=by
   have h1:desc.hom ((PX.π.f 0).hom x)=q.hom x :=
    congrArg (fun φ : PX.complex.X 0 ⟶ ModuleCat.of R Q => φ.hom x) q17
   have hx0:(PX.π.f 0).hom x=(0:X):=hx;rw [← h1,hx0];exact map_zero desc.hom
  exact (Submodule.Quotient.mk_eq_zero _).mp hqx
 have hεA_exact:=hε_exact_of_res PA;have hεC_exact:=hε_exact_of_res PC
 have hPA_exact (n : ℕ) (x:PA.complex.X (n+1)) (hx:(PA.complex.d (n+1) n).hom x=0) :
   ∃ y:PA.complex.X (n+2),(PA.complex.d (n+2) (n+1)).hom y=x :=
  (ShortComplex.moduleCat_exact_iff _).mp (PA.exact_succ n) x hx
 have hPC_exact (n : ℕ) (x:PC.complex.X (n+1)) (hx:(PC.complex.d (n+1) n).hom x=0) :
   ∃ y:PC.complex.X (n+2),(PC.complex.d (n+2) (n+1)).hom y=x :=
  (ShortComplex.moduleCat_exact_iff _).mp (PC.exact_succ n) x hx
 have hPA_dd (n : ℕ) (x:PA.complex.X (n+2)) :
   (PA.complex.d (n+1) n).hom ((PA.complex.d (n+2) (n+1)).hom x)=0 :=
  congrArg (fun φ : PA.complex.X (n+2) ⟶ PA.complex.X n => φ.hom x)
   (PA.complex.d_comp_d (n+2) (n+1) n)
 have hPC_dd (n : ℕ) (x:PC.complex.X (n+2)) :
   (PC.complex.d (n+1) n).hom ((PC.complex.d (n+2) (n+1)).hom x)=0 :=
  congrArg (fun φ : PC.complex.X (n+2) ⟶ PC.complex.X n => φ.hom x)
   (PC.complex.d_comp_d (n+2) (n+1) n)
 let _:=hPC_proj 0;obtain ⟨s0,hs0⟩:=Module.projective_lifting_property p εC hp;let εB:(PA.complex.X 0×PC.complex.X 0) →ₗ[R] B:=(i.comp εA).coprod s0
 have q8:∃ h0:PC.complex.X 1 →ₗ[R] PA.complex.X 0,∀ c:PC.complex.X 1,i (εA (h0 c))+s0 ((PC.complex.d 1 0).hom c)=0:=by
  let _:=hPC_proj 1
  let q1:PC.complex.X 1 →ₗ[R] LinearMap.ker p :=
   LinearMap.codRestrict (LinearMap.ker p) (-(s0.comp (PC.complex.d 1 0).hom)) (fun c=>by
    rw [LinearMap.mem_ker,LinearMap.neg_apply,map_neg,LinearMap.comp_apply];have h1:p (s0 ((PC.complex.d 1 0).hom c)) = εC ((PC.complex.d 1 0).hom c):=LinearMap.congr_fun hs0 _
    rw [h1,hεC_comp,neg_zero])
  let q19:PA.complex.X 0 →ₗ[R] LinearMap.ker p :=
   LinearMap.codRestrict (LinearMap.ker p) (i.comp εA) (fun a=>by
    rw [LinearMap.mem_ker,LinearMap.comp_apply,← LinearMap.mem_ker,← hip]
    exact ⟨εA a,rfl⟩)
  have q0:Surjective q19:=by
   rintro ⟨b,hb⟩;rw [← hip] at hb;obtain ⟨a,rfl⟩:=hb;obtain ⟨x,rfl⟩:=hεA_surj a;exact ⟨x,rfl⟩
  obtain ⟨h0,hh0⟩:=Module.projective_lifting_property q19 q1 q0
  refine ⟨h0,fun c => ?_⟩
  have hc:=congrArg Subtype.val (LinearMap.congr_fun hh0 c);change i (εA (h0 c)) = -(s0 ((PC.complex.d 1 0).hom c)) at hc;rw [hc,neg_add_cancel]
 have q9:∀ (n : ℕ) (q15:PC.complex.X (n+1) →ₗ[R] PA.complex.X n),
   (∀ c:PC.complex.X (n+2),∃ a:PA.complex.X (n+1),(PA.complex.d (n+1) n).hom a = -(q15 ((PC.complex.d (n+2) (n+1)).hom c))) →
   ∃ hnxt:PC.complex.X (n+2) →ₗ[R] PA.complex.X (n+1),
    ∀ c:PC.complex.X (n+2),(PA.complex.d (n+1) n).hom (hnxt c)+q15 ((PC.complex.d (n+2) (n+1)).hom c)=0:=by
  intro n q15 hpre;let _:=hPC_proj (n+2)
  let q18:PC.complex.X (n+2) →ₗ[R] LinearMap.range (PA.complex.d (n+1) n).hom:=LinearMap.codRestrict _ (-(q15.comp (PC.complex.d (n+2) (n+1)).hom)) (fun c=>hpre c)
  obtain ⟨hnxt,hhnxt⟩:=Module.projective_lifting_property
   (LinearMap.rangeRestrict (PA.complex.d (n+1) n).hom) q18
   (LinearMap.surjective_rangeRestrict _)
  refine ⟨hnxt,fun c => ?_⟩
  have hc:=congrArg Subtype.val (LinearMap.congr_fun hhnxt c);change (PA.complex.d (n+1) n).hom (hnxt c) = -(q15 ((PC.complex.d (n+2) (n+1)).hom c)) at hc;rw [hc,neg_add_cancel]
 let q3:∀ n : ℕ,
   Σ' (h:PC.complex.X (n+1) →ₗ[R] PA.complex.X n),
    ∀ c:PC.complex.X (n+2),∃ a:PA.complex.X (n+1),(PA.complex.d (n+1) n).hom a = -(h ((PC.complex.d (n+2) (n+1)).hom c)) :=
  Nat.rec
   ⟨Classical.choose q8,fun c=>by
    have h0:=Classical.choose_spec q8 ((PC.complex.d 2 1).hom c);rw [hPC_dd 0 c,map_zero,add_zero] at h0
    have he : εA (-(Classical.choose q8 ((PC.complex.d 2 1).hom c)))=0:=by
     rw [map_neg,hi (h0.trans (map_zero i).symm),neg_zero]
    exact hεA_exact _ he⟩
   (fun n prev =>
    let hex:=q9 n prev.1 prev.2
    ⟨Classical.choose hex,fun c=>by
     have h1:=Classical.choose_spec hex ((PC.complex.d (n+3) (n+2)).hom c);rw [hPC_dd (n+1) c,map_zero,add_zero] at h1
     have q14:(PA.complex.d (n+1) n).hom
       (-(Classical.choose hex ((PC.complex.d (n+3) (n+2)).hom c)))=0:=by
      rw [map_neg,h1,neg_zero]
     exact hPA_exact n _ q14⟩)
 let h (n : ℕ) : PC.complex.X (n+1) →ₗ[R] PA.complex.X n:=(q3 n).1
 have hh0 (c:PC.complex.X 1) :
   i (εA (h 0 c))+s0 ((PC.complex.d 1 0).hom c)=0 :=
  Classical.choose_spec q8 c
 have hh_succ (n : ℕ) (c:PC.complex.X (n+2)) :
   (PA.complex.d (n+1) n).hom (h (n+1) c)+h n ((PC.complex.d (n+2) (n+1)).hom c)=0 :=
  Classical.choose_spec (q9 n (q3 n).1 (q3 n).2) c
 let dB (n : ℕ) : ModuleCat.of R (PA.complex.X (n+1)×PC.complex.X (n+1)) ⟶
   ModuleCat.of R (PA.complex.X n×PC.complex.X n) :=
  ModuleCat.ofHom
   {
    toFun:=fun x=>((PA.complex.d (n+1) n).hom x.1+h n x.2,(PC.complex.d (n+1) n).hom x.2)
    map_add':=fun x y=>by
     ext
     ·
      change (PA.complex.d (n+1) n).hom (x.1+y.1)+h n (x.2+y.2)=((PA.complex.d (n+1) n).hom x.1+h n x.2)+((PA.complex.d (n+1) n).hom y.1+h n y.2);rw [map_add,map_add];abel
     · exact map_add (PC.complex.d (n+1) n).hom x.2 y.2
    map_smul':=fun r x=>by
     ext
     ·
      change (PA.complex.d (n+1) n).hom (r•x.1)+h n (r•x.2)=r•((PA.complex.d (n+1) n).hom x.1+h n x.2);rw [map_smul,map_smul,smul_add]
     · exact map_smul (PC.complex.d (n+1) n).hom r x.2 }
 have hdB_sq (n : ℕ) : (dB (n+1) ≫ dB n)=0:=by
  apply ModuleCat.hom_ext;apply LinearMap.ext;rintro ⟨a,c⟩;ext
  ·
   change (PA.complex.d (n+1) n).hom ((PA.complex.d (n+2) (n+1)).hom a+h (n+1) c)+h n ((PC.complex.d (n+2) (n+1)).hom c)=0;rw [map_add,hPA_dd n a,zero_add,hh_succ n c]
  ·
   change (PC.complex.d (n+1) n).hom ((PC.complex.d (n+2) (n+1)).hom c)=0;exact hPC_dd n c
 let KB:ChainComplex (ModuleCat.{0} R) ℕ := ChainComplex.of (fun n=>ModuleCat.of R (PA.complex.X n×PC.complex.X n)) dB hdB_sq
 let ιK:PA.complex ⟶ KB :=
  {
   f:=fun n=>ModuleCat.ofHom (LinearMap.inl R (PA.complex.X n) (PC.complex.X n))
   comm':=fun n m hnm=>by
    cases hnm
    apply ModuleCat.hom_ext;apply LinearMap.ext;intro a;ext
    ·
     change ((KB.d (m+1) m).hom (a,0)).1=(PA.complex.d (m+1) m).hom a;simp [KB,ChainComplex.of_d,dB]
    ·
     change ((KB.d (m+1) m).hom (a,0)).2=0
     simp [KB,ChainComplex.of_d,dB] }
 let πK:KB ⟶ PC.complex :=
  {
   f:=fun n=>ModuleCat.ofHom (LinearMap.snd R (PA.complex.X n) (PC.complex.X n))
   comm':=fun n m hnm=>by
    cases hnm
    apply ModuleCat.hom_ext;apply LinearMap.ext;rintro ⟨a,c⟩;change (PC.complex.d (m+1) m).hom c=((KB.d (m+1) m).hom (a,c)).2
    simp [KB,ChainComplex.of_d,dB] }
 have q6:(ιK ≫ πK)=0:=by ext n a;rfl
 let SK:ShortComplex (ChainComplex (ModuleCat.{0} R) ℕ):=ShortComplex.mk ιK πK q6
 have hKB_proj (n : ℕ) : Module.Projective R (KB.X n):=by
  let _:=hPA_proj n;let _:=hPC_proj n;change Module.Projective R (PA.complex.X n×PC.complex.X n)
  infer_instance
 have hps0 (c:PC.complex.X 0) : p (s0 c) = εC c:=LinearMap.congr_fun hs0 c
 have hεB_surj:Surjective εB:=fun b=>by
  obtain ⟨c,hc⟩:=hεC_surj (p b)
  have q16:b - s0 c∈LinearMap.ker p:=by
   rw [LinearMap.mem_ker,map_sub,hps0 c,hc,sub_self]
  rw [← hip] at q16;obtain ⟨a0,ha0⟩:=q16;obtain ⟨a,rfl⟩:=hεA_surj a0
  refine ⟨(a,c),?_⟩
  change i (εA a)+s0 c=b;rw [ha0,sub_add_cancel]
 have hεB_comp (x:KB.X 1) : εB ((KB.d 1 0).hom x)=0:=by
  rcases x with ⟨a,c⟩
  change i (εA ((PA.complex.d 1 0).hom a+h 0 c))+s0 ((PC.complex.d 1 0).hom c)=0;rw [map_add,map_add,hεA_comp a,map_zero,zero_add,hh0 c]
 have hεB_exact (x:KB.X 0) (hx : εB x=0) : ∃ y:KB.X 1,(KB.d 1 0).hom y=x:=by
  rcases x with ⟨a,c⟩
  change i (εA a)+s0 c=0 at hx
  have hpc : εC c=0:=by
   have hp0:=congrArg p hx;rw [map_add,map_zero,hps0 c] at hp0
   have hi0:p (i (εA a))=0:=by rw [← LinearMap.mem_ker,← hip];exact ⟨εA a,rfl⟩
   rw [hi0,zero_add] at hp0;exact hp0
  obtain ⟨c1,hc1⟩:=hεC_exact c hpc
  have q10 : εA (a - h 0 c1)=0:=by
   apply hi;rw [map_zero,map_sub,map_sub];have h1:=hh0 c1;rw [hc1] at h1;have hia:i (εA a) = - s0 c:=eq_neg_of_add_eq_zero_left hx;have hih:i (εA (h 0 c1)) = - s0 c:=eq_neg_of_add_eq_zero_left h1;rw [hia,hih,sub_self]
  obtain ⟨a1,ha1⟩:=hεA_exact _ q10
  refine ⟨(a1,c1),?_⟩
  change ((PA.complex.d 1 0).hom a1+h 0 c1,(PC.complex.d 1 0).hom c1)=(a,c);ext
  · rw [ha1,sub_add_cancel]
  · exact hc1
 have hKB_exact (n : ℕ) (x:KB.X (n+1)) (hx:(KB.d (n+1) n).hom x=0) :
   ∃ y:KB.X (n+2),(KB.d (n+2) (n+1)).hom y=x:=by
  rcases x with ⟨a,c⟩
  have hx':((PA.complex.d (n+1) n).hom a+h n c,(PC.complex.d (n+1) n).hom c)=(0,0):=by
   simpa [KB,ChainComplex.of_d,dB] using hx
  have hx1:(PA.complex.d (n+1) n).hom a+h n c=0:=congrArg Prod.fst hx';have hx2:(PC.complex.d (n+1) n).hom c=0:=congrArg Prod.snd hx';obtain ⟨c1,hc1⟩:=hPC_exact n c hx2
  have q10:(PA.complex.d (n+1) n).hom (a - h (n+1) c1)=0:=by
   rw [map_sub];have h1:=hh_succ n c1;rw [hc1] at h1;have h2:(PA.complex.d (n+1) n).hom a = - h n c:=eq_neg_of_add_eq_zero_left hx1;have h3:(PA.complex.d (n+1) n).hom (h (n+1) c1) = - h n c:=eq_neg_of_add_eq_zero_left h1;rw [h2,h3,sub_self]
  obtain ⟨a1,ha1⟩:=hPA_exact n _ q10
  refine ⟨(a1,c1),?_⟩
  have q11:(KB.d (n+2) (n+1)).hom (a1,c1) =
    ((PA.complex.d (n+2) (n+1)).hom a1+h (n+1) c1,(PC.complex.d (n+2) (n+1)).hom c1) :=
   congrArg (fun φ : KB.X (n+2) ⟶ KB.X (n+1) => φ.hom (a1,c1))
    (ChainComplex.of_d _ dB (n+1))
  rw [q11];ext
  · rw [ha1,sub_add_cancel]
  · exact hc1
 let PB:ProjectiveResolution (ModuleCat.of R B):=z62 B KB hKB_proj εB hεB_surj hεB_comp hεB_exact hKB_exact
 have q4:(ιK.f 0 ≫ PB.π.f 0)=(PA.π.f 0 ≫ ModuleCat.ofHom i):=by
  apply ModuleCat.hom_ext;apply LinearMap.ext;intro a;change εB (a,0)=i (εA a);simp [εB]
 have q5:(πK.f 0 ≫ PC.π.f 0)=(PB.π.f 0 ≫ ModuleCat.ofHom p):=by
  apply ModuleCat.hom_ext;apply LinearMap.ext;rintro ⟨a,c⟩;change εC c=p (εB (a,c));simp only [εB,LinearMap.coprod_apply,map_add,LinearMap.comp_apply]
  have hi0:p (i (εA a))=0:=by rw [← LinearMap.mem_ker,← hip];exact ⟨εA a,rfl⟩
  rw [hi0,zero_add,hps0 c]
 let F:=(tensoringLeft (ModuleCat.{0} R)).obj (ModuleCat.of R M);let SM:ShortComplex (ChainComplex (ModuleCat.{0} R) ℕ):=SK.map (F.mapHomologicalComplex (ComplexShape.down ℕ))
 have q2:SM.ShortExact:=by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact;intro n
  let q7:(SK.map (HomologicalComplex.eval _ _ n)).Splitting :=
   {
    r:=ModuleCat.ofHom (LinearMap.fst R (PA.complex.X n) (PC.complex.X n))
    s:=ModuleCat.ofHom (LinearMap.inr R (PA.complex.X n) (PC.complex.X n))
    f_r:=by apply ModuleCat.hom_ext;apply LinearMap.ext;intro a;rfl
    s_g:=by apply ModuleCat.hom_ext;apply LinearMap.ext;intro c;rfl
    id:=by
     apply ModuleCat.hom_ext;apply LinearMap.ext;rintro ⟨a,c⟩
     change (a,0)+(0,c)=(a,c);ext <;> simp }
  exact (q7.map F).shortExact
 let eA (n : ℕ) : z56 R M A n ≅ SM.X₁.homology n:=PA.isoLeftDerivedObj F n;let eB (n : ℕ) : z56 R M B n ≅ SM.X₂.homology n:=PB.isoLeftDerivedObj F n;let eC (n : ℕ) : z56 R M C n ≅ SM.X₃.homology n:=PC.isoLeftDerivedObj F n;let δ (n : ℕ) : z56 R M C (n+1) →ₗ[R] z56 R M A n:=((eC (n+1)).hom ≫ q2.δ (n+1) n rfl ≫ (eA n).inv).hom
 have htor_i_hom (n : ℕ) (x:z56 R M A n) :
   (eB n).hom.hom (z57 M i n x)=(HomologicalComplex.homologyMap SM.f n).hom ((eA n).hom.hom x) :=
  congrArg (fun φ : z56 R M A n ⟶ SM.X₂.homology n => φ.hom x)
   (ProjectiveResolution.isoLeftDerivedObj_hom_naturality (ModuleCat.ofHom i) PA PB ιK q4 F n)
 have htor_p_hom (n : ℕ) (x:z56 R M B n) :
   (eC n).hom.hom (z57 M p n x)=(HomologicalComplex.homologyMap SM.g n).hom ((eB n).hom.hom x) :=
  congrArg (fun φ : z56 R M B n ⟶ SM.X₃.homology n => φ.hom x)
   (ProjectiveResolution.isoLeftDerivedObj_hom_naturality (ModuleCat.ofHom p) PB PC πK q5 F n)
 have iso_hom_inv {X Y:ModuleCat.{0} R} (e:X ≅ Y) (y:Y) : e.hom.hom (e.inv.hom y)=y :=
  congrArg (fun φ : Y ⟶ Y => φ.hom y) e.inv_hom_id
 have iso_inv_hom {X Y:ModuleCat.{0} R} (e:X ≅ Y) (x:X) : e.inv.hom (e.hom.hom x)=x :=
  congrArg (fun φ : X ⟶ X => φ.hom x) e.hom_inv_id
 refine ⟨δ,?_,?_,?_⟩
 ·
  intro n x;have hex:=(ShortComplex.moduleCat_exact_iff _).mp (q2.homology_exact₁ (n+1) n rfl)
  have h1:z57 M i n x=0↔(HomologicalComplex.homologyMap SM.f n).hom ((eA n).hom.hom x)=0:=by
   rw [← htor_i_hom n x];exact (eB n).toLinearEquiv.map_eq_zero_iff.symm
  rw [h1];constructor
  ·
   intro hx;obtain ⟨y,hy⟩:=hex ((eA n).hom.hom x) hx
   refine ⟨(eC (n+1)).inv.hom y,?_⟩
   change (eA n).inv.hom ((q2.δ (n+1) n rfl).hom ((eC (n+1)).hom.hom ((eC (n+1)).inv.hom y)))=x;rw [iso_hom_inv (eC (n+1)) y,hy];exact iso_inv_hom (eA n) x
  ·
   rintro ⟨z,rfl⟩
   have q13:=congrArg (fun φ : SM.X₃.homology (n+1) ⟶ SM.X₂.homology n =>
    φ.hom ((eC (n+1)).hom.hom z)) (q2.δ_comp (n+1) n rfl)
   change (HomologicalComplex.homologyMap SM.f n).hom
    ((eA n).hom.hom ((eA n).inv.hom ((q2.δ (n+1) n rfl).hom ((eC (n+1)).hom.hom z))))=0
   rw [iso_hom_inv (eA n)];exact q13
 ·
  intro n x;have hex:=(ShortComplex.moduleCat_exact_iff _).mp (q2.homology_exact₂ n)
  have h1:z57 M p n x=0↔(HomologicalComplex.homologyMap SM.g n).hom ((eB n).hom.hom x)=0:=by
   rw [← htor_p_hom n x];exact (eC n).toLinearEquiv.map_eq_zero_iff.symm
  rw [h1];constructor
  ·
   intro hx;obtain ⟨y,hy⟩:=hex ((eB n).hom.hom x) hx
   refine ⟨(eA n).inv.hom y,?_⟩
   apply (eB n).toLinearEquiv.injective;change (eB n).hom.hom (z57 M i n ((eA n).inv.hom y))=(eB n).hom.hom x;rw [htor_i_hom n,iso_hom_inv (eA n) y,hy]
  ·
   rintro ⟨z,rfl⟩;rw [htor_i_hom n]
   have q12:(HomologicalComplex.homologyMap SM.f n ≫ HomologicalComplex.homologyMap SM.g n)=0:=by
    rw [← HomologicalComplex.homologyMap_comp,SM.zero,HomologicalComplex.homologyMap_zero]
   exact congrArg (fun φ : SM.X₁.homology n ⟶ SM.X₃.homology n => φ.hom ((eA n).hom.hom z)) q12
 ·
  intro n x;have hex:=(ShortComplex.moduleCat_exact_iff _).mp (q2.homology_exact₃ (n+1) n rfl)
  have h1 : δ n x=0↔(q2.δ (n+1) n rfl).hom ((eC (n+1)).hom.hom x)=0:=by
   change (eA n).inv.hom ((q2.δ (n+1) n rfl).hom ((eC (n+1)).hom.hom x))=0↔_;exact (eA n).toLinearEquiv.symm.map_eq_zero_iff
  rw [h1];constructor
  ·
   intro hx;obtain ⟨y,hy⟩:=hex ((eC (n+1)).hom.hom x) hx
   refine ⟨(eB (n+1)).inv.hom y,?_⟩
   apply (eC (n+1)).toLinearEquiv.injective;change (eC (n+1)).hom.hom (z57 M p (n+1) ((eB (n+1)).inv.hom y))=(eC (n+1)).hom.hom x;rw [htor_p_hom (n+1),iso_hom_inv (eB (n+1)) y,hy]
  ·
   rintro ⟨z,rfl⟩;rw [htor_p_hom (n+1)]
   exact congrArg (fun φ : SM.X₂.homology (n+1) ⟶ SM.X₁.homology n =>
    φ.hom ((eB (n+1)).hom.hom z)) (q2.comp_δ (n+1) n rfl)
lemma z64 {R:Type} [CommRing R]
  (M N:Type) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (b:R) (i : ℕ) (x:z56 R M N i) :
  z57 M (b•LinearMap.id (R:=R) (M:=N)) i x=b•x:=by
 let PN:=projectiveResolution (ModuleCat.of R N);let F:=(tensoringLeft (ModuleCat.{0} R)).obj (ModuleCat.of R M);let e:z56 R M N i ≅ ((F.mapHomologicalComplex _).obj PN.complex).homology i:=PN.isoLeftDerivedObj F i;let q4:ModuleCat.of R N ⟶ ModuleCat.of R N:=ModuleCat.ofHom (b•LinearMap.id)
 let q2:PN.complex ⟶ PN.complex :=
  {
   f:=fun k=>ModuleCat.ofHom (b•LinearMap.id)
   comm':=fun k l _=>by
    apply ModuleCat.hom_ext;apply LinearMap.ext;intro y
    exact map_smul (PN.complex.d k l).hom b y }
 have q5:(q2.f 0 ≫ PN.π.f 0)=(PN.π.f 0 ≫ q4):=by
  apply ModuleCat.hom_ext;apply LinearMap.ext;intro y;exact map_smul (PN.π.f 0).hom b y
 have q6:=ProjectiveResolution.isoLeftDerivedObj_hom_naturality q4 PN PN q2 q5 F i
 have q1:((F.mapHomologicalComplex _).map q2) =
   {
    f:=fun k=>ModuleCat.ofHom (b•LinearMap.id)
    comm':=fun k l _=>by
     apply ModuleCat.hom_ext;apply LinearMap.ext;intro t
     exact map_smul (((F.mapHomologicalComplex _).obj PN.complex).d k l).hom b t }:=by
  apply HomologicalComplex.hom_ext;intro k;apply ModuleCat.hom_ext;apply TensorProduct.ext';intro m p;change m ⊗ₜ[R] (b•p)=b•(m ⊗ₜ[R] p);rw [TensorProduct.tmul_smul]
 have q0:∀ y:((F.mapHomologicalComplex _).obj PN.complex).homology i,(HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map q2) i).hom y=b•y:=by
  intro y;let K:=(F.mapHomologicalComplex _).obj PN.complex;have q3:Surjective (K.homologyπ i):=(ModuleCat.epi_iff_surjective (K.homologyπ i)).mp inferInstance;obtain ⟨c,rfl⟩:=q3 y
  have h1:(HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map q2) i).hom
    ((K.homologyπ i).hom c) =
    (K.homologyπ i).hom ((HomologicalComplex.cyclesMap ((F.mapHomologicalComplex _).map q2) i).hom c) :=
   congrArg (fun φ : K.cycles i ⟶ K.homology i => φ.hom c)
    (HomologicalComplex.homologyπ_naturality ((F.mapHomologicalComplex _).map q2) i)
  rw [h1,← map_smul];congr 1;apply (ModuleCat.mono_iff_injective (K.iCycles i)).mp inferInstance
  have h2:(K.iCycles i).hom
    ((HomologicalComplex.cyclesMap ((F.mapHomologicalComplex _).map q2) i).hom c) =
    (((F.mapHomologicalComplex _).map q2).f i).hom ((K.iCycles i).hom c) :=
   congrArg (fun φ : K.cycles i ⟶ K.X i => φ.hom c)
    (HomologicalComplex.cyclesMap_i ((F.mapHomologicalComplex _).map q2) i)
  rw [h2,map_smul,q1];rfl
 apply e.toLinearEquiv.injective
 have h1:e.hom.hom (z57 M (b•LinearMap.id) i x)=(HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map q2) i).hom (e.hom.hom x) :=
  congrArg (fun φ : z56 R M N i ⟶ _ => φ.hom x) q6
 change e.hom.hom (z57 M (b•LinearMap.id) i x)=e.hom.hom (b•x);rw [h1,q0,map_smul]
lemma z65 {R:Type} [CommRing R]
  {A B C:Type} [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
  (i:A →ₗ[R] B) (p:B →ₗ[R] C)
  (hi:Injective i) (hp:Surjective p)
  (hip:LinearMap.range i=LinearMap.ker p)
  (N:Type) [AddCommGroup N] [Module R N] :
  ∃ δ : ∀ n : ℕ,z56 R C N (n+1) →ₗ[R] z56 R A N n,(∀ n,Function.Exact (δ n) (z58 i N n))∧(∀ n,Function.Exact (z58 i N n) (z58 p N n))∧(∀ n,Function.Exact (z58 p N (n+1)) (δ n)):=by
 let PN:=projectiveResolution (ModuleCat.of R N);let FA:=(tensoringLeft (ModuleCat.{0} R)).obj (ModuleCat.of R A);let FB:=(tensoringLeft (ModuleCat.{0} R)).obj (ModuleCat.of R B);let FC:=(tensoringLeft (ModuleCat.{0} R)).obj (ModuleCat.of R C);let KA:=(FA.mapHomologicalComplex (ComplexShape.down ℕ)).obj PN.complex;let KB:=(FB.mapHomologicalComplex (ComplexShape.down ℕ)).obj PN.complex
 let KC:=(FC.mapHomologicalComplex (ComplexShape.down ℕ)).obj PN.complex;let ηi:FA ⟶ FB:=(tensoringLeft (ModuleCat.{0} R)).map (ModuleCat.ofHom i);let ηp:FB ⟶ FC:=(tensoringLeft (ModuleCat.{0} R)).map (ModuleCat.ofHom p);let fi:KA ⟶ KB:=(NatTrans.mapHomologicalComplex ηi (ComplexShape.down ℕ)).app PN.complex
 let fp:KB ⟶ KC:=(NatTrans.mapHomologicalComplex ηp (ComplexShape.down ℕ)).app PN.complex
 have q5:(fi ≫ fp)=0:=by
  apply HomologicalComplex.hom_ext;intro n
  have hpi:p.comp i=0:=by
   ext a;rw [LinearMap.comp_apply,LinearMap.zero_apply,← LinearMap.mem_ker,← hip];exact ⟨a,rfl⟩
  apply ModuleCat.hom_ext;apply TensorProduct.ext';intro a y;change p (i a) ⊗ₜ[R] y=0;have : p (i a)=0:=LinearMap.congr_fun hpi a;rw [this,zero_tmul]
 let S:ShortComplex (ChainComplex (ModuleCat.{0} R) ℕ):=ShortComplex.mk fi fp q5
 have q3:S.ShortExact:=by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact;intro n;have q1:Module.Projective R (PN.complex.X n):=ModuleCat.projective_of_module_projective (P:=PN.complex.X n);have q2:Module.Flat R (PN.complex.X n):=inferInstance
  have q4:Mono (S.map (HomologicalComplex.eval _ _ n)).f:=by
   rw [ModuleCat.mono_iff_injective];exact Module.Flat.rTensor_preserves_injective_linearMap i hi
  have q7:Epi (S.map (HomologicalComplex.eval _ _ n)).g:=by
   rw [ModuleCat.epi_iff_surjective];exact LinearMap.rTensor_surjective (PN.complex.X n) hp
  have hex:(S.map (HomologicalComplex.eval _ _ n)).Exact:=by
   rw [ShortComplex.moduleCat_exact_iff];intro x hx;exact (rTensor_exact (PN.complex.X n) (LinearMap.exact_iff.mpr hip.symm) hp x).mp hx
  exact { exact:=hex,mono_f:=q4,epi_g:=q7 }
 let eA (n : ℕ) : z56 R A N n ≅ KA.homology n:=PN.isoLeftDerivedObj FA n;let eB (n : ℕ) : z56 R B N n ≅ KB.homology n:=PN.isoLeftDerivedObj FB n;let eC (n : ℕ) : z56 R C N n ≅ KC.homology n:=PN.isoLeftDerivedObj FC n;let δ (n : ℕ) : z56 R C N (n+1) →ₗ[R] z56 R A N n:=((eC (n+1)).hom ≫ q3.δ (n+1) n rfl ≫ (eA n).inv).hom
 have q0:∀ {X Y:Type} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
   (f:X →ₗ[R] Y) (n : ℕ) (x:z56 R X N n),
   let FX:=(tensoringLeft (ModuleCat.{0} R)).obj (ModuleCat.of R X);let FY:=(tensoringLeft (ModuleCat.{0} R)).obj (ModuleCat.of R Y);let η : FX ⟶ FY:=(tensoringLeft (ModuleCat.{0} R)).map (ModuleCat.ofHom f);let φ := (NatTrans.mapHomologicalComplex η (ComplexShape.down ℕ)).app PN.complex
   (PN.isoLeftDerivedObj FY n).hom.hom (z58 f N n x)=(HomologicalComplex.homologyMap φ n).hom ((PN.isoLeftDerivedObj FX n).hom.hom x):=by
  intro X Y _ _ _ _ f n x FX FY η φ;have h0:=ProjectiveResolution.leftDerived_app_eq η PN n
  have h1:CategoryStruct.comp ((NatTrans.leftDerived η n).app (ModuleCat.of R N))
    (PN.isoLeftDerivedObj FY n).hom =
    CategoryStruct.comp (PN.isoLeftDerivedObj FX n).hom
     ((HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ) n).map φ):=by
   rw [h0,Category.assoc,Category.assoc,Iso.inv_hom_id,Category.comp_id]
  exact congrArg (fun ψ : z56 R X N n ⟶ ((FY.mapHomologicalComplex _).obj PN.complex).homology n =>
   ψ.hom x) h1
 have htor_i (n : ℕ) (x:z56 R A N n) :
   (eB n).hom.hom (z58 i N n x)=(HomologicalComplex.homologyMap S.f n).hom ((eA n).hom.hom x) :=
  q0 i n x
 have htor_p (n : ℕ) (x:z56 R B N n) :
   (eC n).hom.hom (z58 p N n x)=(HomologicalComplex.homologyMap S.g n).hom ((eB n).hom.hom x) :=
  q0 p n x
 have iso_hom_inv {X Y:ModuleCat.{0} R} (e:X ≅ Y) (y:Y) : e.hom.hom (e.inv.hom y)=y :=
  congrArg (fun φ : Y ⟶ Y => φ.hom y) e.inv_hom_id
 have iso_inv_hom {X Y:ModuleCat.{0} R} (e:X ≅ Y) (x:X) : e.inv.hom (e.hom.hom x)=x :=
  congrArg (fun φ : X ⟶ X => φ.hom x) e.hom_inv_id
 refine ⟨δ,?_,?_,?_⟩
 ·
  intro n x;have hex:=(ShortComplex.moduleCat_exact_iff _).mp (q3.homology_exact₁ (n+1) n rfl)
  have h1:z58 i N n x=0↔(HomologicalComplex.homologyMap S.f n).hom ((eA n).hom.hom x)=0:=by
   rw [← htor_i n x];exact (eB n).toLinearEquiv.map_eq_zero_iff.symm
  rw [h1];constructor
  ·
   intro hx;obtain ⟨y,hy⟩:=hex ((eA n).hom.hom x) hx
   refine ⟨(eC (n+1)).inv.hom y,?_⟩
   change (eA n).inv.hom ((q3.δ (n+1) n rfl).hom ((eC (n+1)).hom.hom ((eC (n+1)).inv.hom y)))=x;rw [iso_hom_inv (eC (n+1)) y,hy];exact iso_inv_hom (eA n) x
  ·
   rintro ⟨z,rfl⟩
   have q6:=congrArg (fun φ : S.X₃.homology (n+1) ⟶ S.X₂.homology n =>
    φ.hom ((eC (n+1)).hom.hom z)) (q3.δ_comp (n+1) n rfl)
   change (HomologicalComplex.homologyMap S.f n).hom
    ((eA n).hom.hom ((eA n).inv.hom ((q3.δ (n+1) n rfl).hom ((eC (n+1)).hom.hom z))))=0
   rw [iso_hom_inv (eA n)];exact q6
 ·
  intro n x;have hex:=(ShortComplex.moduleCat_exact_iff _).mp (q3.homology_exact₂ n)
  have h1:z58 p N n x=0↔(HomologicalComplex.homologyMap S.g n).hom ((eB n).hom.hom x)=0:=by
   rw [← htor_p n x];exact (eC n).toLinearEquiv.map_eq_zero_iff.symm
  rw [h1];constructor
  ·
   intro hx;obtain ⟨y,hy⟩:=hex ((eB n).hom.hom x) hx
   refine ⟨(eA n).inv.hom y,?_⟩
   apply (eB n).toLinearEquiv.injective;change (eB n).hom.hom (z58 i N n ((eA n).inv.hom y))=(eB n).hom.hom x;rw [htor_i n,iso_hom_inv (eA n) y,hy]
  ·
   rintro ⟨z,rfl⟩;rw [htor_i n]
   have hzero':(HomologicalComplex.homologyMap S.f n ≫ HomologicalComplex.homologyMap S.g n)=0:=by
    rw [← HomologicalComplex.homologyMap_comp,S.zero,HomologicalComplex.homologyMap_zero]
   exact congrArg (fun φ : S.X₁.homology n ⟶ S.X₃.homology n => φ.hom ((eA n).hom.hom z)) hzero'
 ·
  intro n x;have hex:=(ShortComplex.moduleCat_exact_iff _).mp (q3.homology_exact₃ (n+1) n rfl)
  have h1 : δ n x=0↔(q3.δ (n+1) n rfl).hom ((eC (n+1)).hom.hom x)=0:=by
   change (eA n).inv.hom ((q3.δ (n+1) n rfl).hom ((eC (n+1)).hom.hom x))=0↔_;exact (eA n).toLinearEquiv.symm.map_eq_zero_iff
  rw [h1];constructor
  ·
   intro hx;obtain ⟨y,hy⟩:=hex ((eC (n+1)).hom.hom x) hx
   refine ⟨(eB (n+1)).inv.hom y,?_⟩
   apply (eC (n+1)).toLinearEquiv.injective;change (eC (n+1)).hom.hom (z58 p N (n+1) ((eB (n+1)).inv.hom y))=(eC (n+1)).hom.hom x;rw [htor_p (n+1),iso_hom_inv (eB (n+1)) y,hy]
  ·
   rintro ⟨z,rfl⟩;rw [htor_p (n+1)]
   exact congrArg (fun φ : S.X₂.homology (n+1) ⟶ S.X₁.homology n =>
    φ.hom ((eB (n+1)).hom.hom z)) (q3.comp_δ (n+1) n rfl)
lemma z66 {R:Type} [CommRing R]
  {A B:Type} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  (f:A →ₗ[R] B) (N:Type) [AddCommGroup N] [Module R N] (x:z56 R A N 0) :
  z59 R B N (z58 f N 0 x)=LinearMap.rTensor N f (z59 R A N x):=by
 let PN:=projectiveResolution (ModuleCat.of R N);let FA:=(tensoringLeft (ModuleCat.{0} R)).obj (ModuleCat.of R A);let FB:=(tensoringLeft (ModuleCat.{0} R)).obj (ModuleCat.of R B);let η : FA ⟶ FB:=(tensoringLeft (ModuleCat.{0} R)).map (ModuleCat.ofHom f)
 have hop:CategoryStruct.comp
   (HomologicalComplex.opcyclesMap ((NatTrans.mapHomologicalComplex η _).app PN.complex) 0)
   (PN.fromLeftDerivedZero' FB) =
   CategoryStruct.comp (PN.fromLeftDerivedZero' FA) (η.app (ModuleCat.of R N)):=by
  simp only [← cancel_epi (HomologicalComplex.pOpcycles _ _),HomologicalComplex.p_opcyclesMap_assoc,ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero',ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero'_assoc];exact (η.naturality (PN.π.f 0)).symm
 have h1:CategoryStruct.comp ((NatTrans.leftDerived η 0).app (ModuleCat.of R N))
   (FB.fromLeftDerivedZero.app (ModuleCat.of R N)) =
   CategoryStruct.comp (FA.fromLeftDerivedZero.app (ModuleCat.of R N))
    (η.app (ModuleCat.of R N)):=by
  rw [ProjectiveResolution.fromLeftDerivedZero_eq PN FA,ProjectiveResolution.fromLeftDerivedZero_eq PN FB,ProjectiveResolution.leftDerived_app_eq η PN 0];simp only [Category.assoc,Iso.inv_hom_id_assoc];congr 1;let φ := (NatTrans.mapHomologicalComplex η (ComplexShape.down ℕ)).app PN.complex
  have hι : CategoryStruct.comp (HomologicalComplex.homologyMap φ 0)
    (HomologicalComplex.homologyι ((FB.mapHomologicalComplex _).obj PN.complex) 0) =
    CategoryStruct.comp
     (HomologicalComplex.homologyι ((FA.mapHomologicalComplex _).obj PN.complex) 0)
     (HomologicalComplex.opcyclesMap φ 0) :=
   HomologicalComplex.homologyι_naturality φ 0
  change CategoryStruct.comp (HomologicalComplex.homologyMap φ 0)
   (CategoryStruct.comp (HomologicalComplex.homologyι ((FB.mapHomologicalComplex _).obj PN.complex) 0)
    (PN.fromLeftDerivedZero' FB)) =
   CategoryStruct.comp
    (HomologicalComplex.homologyι ((FA.mapHomologicalComplex _).obj PN.complex) 0)
    (CategoryStruct.comp (PN.fromLeftDerivedZero' FA) (η.app (ModuleCat.of R N)))
  rw [← Category.assoc,hι,Category.assoc,hop]
 exact congrArg (fun φ : z56 R A N 0 ⟶ ModuleCat.of R (B ⊗[R] N) => φ.hom x) h1
lemma z67 {R:Type} [CommRing R]
  (M N:Type) [AddCommGroup M] [Module R M] [Module.Flat R M]
  [AddCommGroup N] [Module R N] (i : ℕ) :
  Subsingleton (z56 R M N (i+1)):=by
 let PN:=projectiveResolution (ModuleCat.of R N);let F:=(tensoringLeft (ModuleCat.{0} R)).obj (ModuleCat.of R M);let e:z56 R M N (i+1) ≅ ((F.mapHomologicalComplex _).obj PN.complex).homology (i+1):=PN.isoLeftDerivedObj F (i+1)
 have hex:((F.mapHomologicalComplex _).obj PN.complex).ExactAt (i+1):=by
  rw [HomologicalComplex.exactAt_iff' _ (i+2) (i+1) i (by simp) (by simp)];rw [ShortComplex.moduleCat_exact_iff]
  have q1:Function.Exact (PN.complex.d (i+2) (i+1)).hom (PN.complex.d (i+1) i).hom:=by
   intro x;constructor
   · exact (ShortComplex.moduleCat_exact_iff _).mp (PN.exact_succ i) x
   ·
    rintro ⟨y,rfl⟩
    exact congrArg (fun φ : PN.complex.X (i+2) ⟶ PN.complex.X i => φ.hom y)
     (PN.complex.d_comp_d (i+2) (i+1) i)
  intro t ht;exact (Module.Flat.lTensor_exact M q1 t).mp ht
 have q0:IsZero (((F.mapHomologicalComplex _).obj PN.complex).homology (i+1)):=hex.isZero_homology;exact ModuleCat.isZero_iff_subsingleton.mp (IsZero.of_iso q0 e)
private lemma z68 {R:Type} [CommRing R]
  {A B C:ModuleCat.{0} R}
  (f:A →ₗ[R] B) (g:B →ₗ[R] C) (hf:Injective f) (hfg:Function.Exact f g) :
  Nonempty (A ≃ₗ[R] LinearMap.ker g):=by
 refine ⟨LinearEquiv.ofBijective
  {
   toFun:=fun a=>⟨f a,LinearMap.mem_ker.mpr ((hfg (f a)).mpr ⟨a,rfl⟩)⟩
   map_add':=fun x y=>Subtype.ext (map_add f x y)
   map_smul':=fun r x=>Subtype.ext (map_smul f r x) }
  ⟨fun x y h=>hf (congrArg Subtype.val h),fun ⟨b,hb⟩=>let ⟨a,ha⟩:=(hfg b).mp (LinearMap.mem_ker.mp hb);⟨a,Subtype.ext ha⟩⟩⟩
private lemma z69 {R:Type} [CommRing R]
    {A B A' B':ModuleCat.{0} R}
    (f:A →ₗ[R] B) (f':A' →ₗ[R] B')
    (eA:A ≃ₗ[R] A') (eB:B ≃ₗ[R] B')
    (hsq:∀ a,eB (f a)=f' (eA a)) :
    Nonempty (LinearMap.ker f ≃ₗ[R] LinearMap.ker f') :=
  ⟨{ toFun:=fun x=>⟨eA x.1,by rw [LinearMap.mem_ker,← hsq x.1,LinearMap.mem_ker.mp x.2,map_zero]⟩
     invFun:=fun y=>⟨eA.symm y.1,by
       rw [LinearMap.mem_ker];apply eB.injective;rw [map_zero,hsq,eA.apply_symm_apply]
       exact LinearMap.mem_ker.mp y.2⟩
     map_add':=fun _ _=>Subtype.ext (map_add eA _ _)
     map_smul':=fun _ _=>Subtype.ext (map_smul eA _ _)
     left_inv:=fun _=>Subtype.ext (eA.symm_apply_apply _)
     right_inv:=fun _=>Subtype.ext (eA.apply_symm_apply _) }⟩
private lemma z70 {R M N F K:Type} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup F] [Module R F] [Module.Projective R F] [Module.Flat R F]
  [AddCommGroup K] [Module R K]
  (incl:K →ₗ[R] F) (p:F →ₗ[R] M)
  (q1:Injective incl) (hp:Surjective p)
  (hex:LinearMap.range incl=LinearMap.ker p) :
  Nonempty (z56 R M N 1 ≃ₗ[R] z56 R N M 1) ∧
  (∀ k : ℕ,Nonempty (z56 R K N (k+1) ≃ₗ[R] z56 R N K (k+1))→Nonempty (z56 R M N (k+2) ≃ₗ[R] z56 R N M (k+2))):=by
 obtain ⟨δL,hL1,_,hL3⟩:=z65 incl p q1 hp hex N;obtain ⟨δR,hR1,_,hR3⟩:=z63 N incl p q1 hp hex;constructor
 ·
  have : Subsingleton (z56 R F N 1):=z67 F N 0;have : Subsingleton (z56 R N F 1):=z61 N F 0
  have hδL_inj:Injective (δL 0):=by
   rw [injective_iff_map_eq_zero];intro x hx;obtain ⟨y,rfl⟩:=(hL3 0 x).mp hx;rw [Subsingleton.elim y 0,map_zero]
  have hδR_inj:Injective (δR 0):=by
   rw [injective_iff_map_eq_zero];intro x hx;obtain ⟨y,rfl⟩:=(hR3 0 x).mp hx;rw [Subsingleton.elim y 0,map_zero]
  obtain ⟨eL1⟩:=z68 (δL 0) (z58 incl N 0) hδL_inj (hL1 0);obtain ⟨eR1⟩:=z68 (δR 0) (z57 N incl 0) hδR_inj (hR1 0);let q2:z56 R K N 0 ≃ₗ[R] z56 R N K 0:=(z59 R K N).trans ((TensorProduct.comm R K N).trans (z59 R N K).symm);let q0:z56 R F N 0 ≃ₗ[R] z56 R N F 0:=(z59 R F N).trans ((TensorProduct.comm R F N).trans (z59 R N F).symm)
  have hsq:∀ x:z56 R K N 0,q0 (z58 incl N 0 x)=z57 N incl 0 (q2 x):=fun x=>by
   apply (z59 R N F).injective;rw [z60];simp only [q0,q2,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply,z66]
   generalize z59 R K N x=t
   induction t using TensorProduct.induction_on with
   | zero=>simp
   | tmul k n=>simp
   | add t₁ t₂ ih₁ ih₂=>simp [ih₁,ih₂]
  obtain ⟨eKer⟩:=z69 (z58 incl N 0) (z57 N incl 0) q2 q0 hsq;exact ⟨eL1.trans (eKer.trans eR1.symm)⟩
 ·
  intro k ⟨eIH⟩;have : Subsingleton (z56 R F N (k+2)):=z67 F N (k+1);have : Subsingleton (z56 R N F (k+2)):=z61 N F (k+1);have : Subsingleton (z56 R F N (k+1)):=z67 F N k;have : Subsingleton (z56 R N F (k+1)):=z61 N F k
  have hδL_bij:Bijective (δL (k+1)):=by
   constructor
   ·
    rw [injective_iff_map_eq_zero];intro x hx;obtain ⟨y,rfl⟩:=(hL3 (k+1) x).mp hx;rw [Subsingleton.elim y 0,map_zero]
   · intro y;exact (hL1 (k+1) y).mp (Subsingleton.elim _ 0)
  have hδR_bij:Bijective (δR (k+1)):=by
   constructor
   ·
    rw [injective_iff_map_eq_zero];intro x hx;obtain ⟨y,rfl⟩:=(hR3 (k+1) x).mp hx;rw [Subsingleton.elim y 0,map_zero]
   · intro y;exact (hR1 (k+1) y).mp (Subsingleton.elim _ 0)
  exact ⟨(LinearEquiv.ofBijective (δL (k+1)) hδL_bij).trans
   (eIH.trans (LinearEquiv.ofBijective (δR (k+1)) hδR_bij).symm)⟩
lemma z71 {R:Type} [CommRing R] :
  ∀ (i : ℕ) (M N:Type) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N],Nonempty (z56 R M N i ≃ₗ[R] z56 R N M i):=by
 intro i
 induction i with
 | zero =>
  intro M N _ _ _ _;exact ⟨(z59 R M N).trans ((TensorProduct.comm R M N).trans (z59 R N M).symm)⟩
 | succ i ih =>
  intro M N _ _ _ _;let F:=M →₀ R;let p:F →ₗ[R] M:=Finsupp.linearCombination R id
  have hp:Surjective p:=fun m =>
   ⟨Finsupp.single m 1,by
    dsimp only [p]
    rw [Finsupp.linearCombination_single,one_smul,id_eq]⟩
  let K:=LinearMap.ker p
  have q0:=z70 (R:=R) (M:=M) (N:=N) (F:=F) (K := ↥K)
   K.subtype p Subtype.val_injective hp (Submodule.range_subtype K)
  cases i with
  | zero=>exact q0.1
  | succ k=>exact q0.2 k (ih (↥K) N)
lemma z72 {R:Type} [CommRing R]
  (M N:Type) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] :
  intersectionMultiplicity R M N=intersectionMultiplicity R N M:=by
 unfold intersectionMultiplicity
 refine finsum_congr fun i => ?_
 obtain ⟨e⟩:=z71 (R:=R) i M N;rw [e.length_eq]
set_option maxHeartbeats 800000 in
lemma z73 {R₁ S₁ : Type} [CommRing R₁] [IsNoetherianRing R₁]
  [CommRing S₁] [IsLocalRing S₁] [IsNoetherianRing S₁] [Algebra R₁ S₁]
  (x:R₁) (q24:algebraMap R₁ S₁ x∈maximalIdeal S₁)
  (q37:IsSMulRegular R₁ x) (q36:IsSMulRegular S₁ (algebraMap R₁ S₁ x))
  (q4 :
   let R₀ := R₁ ⧸ span {x};let S₀ := S₁ ⧸ span {algebraMap R₁ S₁ x}
   let f₀ : R₀ →+* S₀ := Ideal.Quotient.lift (span {x})
    ((Ideal.Quotient.mk (span {algebraMap R₁ S₁ x})).comp (algebraMap R₁ S₁))
    (fun a ha=>by
     obtain ⟨r,rfl⟩:=mem_span_singleton.mp ha;rw [RingHom.comp_apply,map_mul,Ideal.Quotient.eq_zero_iff_mem]
     exact Ideal.mul_mem_right _ _ (subset_span rfl))
   letI : Algebra R₀ S₀ := f₀.toAlgebra
   Module.Flat R₀ S₀) :
  Module.Flat R₁ S₁ := by
 let R₀ := R₁ ⧸ span {x};let S₀ := S₁ ⧸ span {algebraMap R₁ S₁ x}
 let f₀ : R₀ →+* S₀ := Ideal.Quotient.lift (span {x})
  ((Ideal.Quotient.mk (span {algebraMap R₁ S₁ x})).comp (algebraMap R₁ S₁))
  (fun a ha=>by
   obtain ⟨r,rfl⟩:=mem_span_singleton.mp ha;rw [RingHom.comp_apply,map_mul,Ideal.Quotient.eq_zero_iff_mem]
   exact Ideal.mul_mem_right _ _ (subset_span rfl))
 let : Algebra R₀ S₀ := f₀.toAlgebra;have : Module.Flat R₀ S₀ := q4
 have q10:Subsingleton (z56 R₁ S₁ R₀ 1):=by
  let q25:R₁ →ₗ[R₁] R₁ := x•LinearMap.id;have q5:Injective q25:=q37;have q11:Surjective (span {x}).mkQ:=Submodule.mkQ_surjective _
  have q34:LinearMap.range q25=LinearMap.ker (span {x}).mkQ:=by
   rw [Submodule.ker_mkQ];ext r;simp only [LinearMap.mem_range,q25,LinearMap.smul_apply,LinearMap.id_apply,smul_eq_mul,mem_span_singleton,dvd_def]
   exact ⟨fun ⟨a,ha⟩=>⟨a,ha.symm⟩,fun ⟨a,ha⟩=>⟨a,ha.symm⟩⟩
  obtain ⟨δ,h1,_,h3⟩:=z63 S₁ q25 (span {x}).mkQ q5 q11 q34;have : Subsingleton (z56 R₁ S₁ R₁ 1):=z61 S₁ R₁ 0
  refine subsingleton_iff_forall_eq 0 |>.mpr fun z => ?_
  have hδ0 : δ 0 z=0:=by
   apply (z59 R₁ S₁ R₁).injective;rw [map_zero];apply (TensorProduct.rid R₁ S₁).injective;rw [map_zero];apply q36;dsimp only;rw [smul_eq_mul,smul_eq_mul,mul_zero];have q30:z57 S₁ q25 0 (δ 0 z)=0:=(h1 0 (δ 0 z)).mpr ⟨z,rfl⟩;have h2:=congrArg (TensorProduct.rid R₁ S₁ ∘ z59 R₁ S₁ R₁) q30;simp only [Function.comp_apply,map_zero,z60] at h2
   have h3':∀ t:S₁ ⊗[R₁] R₁,
     TensorProduct.rid R₁ S₁ (LinearMap.lTensor S₁ q25 t)=algebraMap R₁ S₁ x*TensorProduct.rid R₁ S₁ t:=fun t=>by
    induction t using TensorProduct.induction_on with
    | zero=>simp
    | tmul s r =>
     rw [LinearMap.lTensor_tmul,TensorProduct.rid_tmul,TensorProduct.rid_tmul];change (x*r)•s=algebraMap R₁ S₁ x*(r•s);rw [Algebra.smul_def,Algebra.smul_def,map_mul];ring
    | add t₁ t₂ ih₁ ih₂=>simp [map_add,ih₁,ih₂,mul_add]
   rw [← h3'];exact h2
  obtain ⟨w,hw⟩:=(h3 0 z).mp hδ0;rw [← hw,Subsingleton.elim w 0,map_zero]
 have q2:∀ m : ℕ,Subsingleton (z56 R₁ S₁ (Fin m→R₀) 1):=by
  intro m
  induction m with
  | zero =>
   have : Module.Projective R₁ (Fin 0→R₀) :=
    Module.Projective.of_split (0:(Fin 0→R₀) →ₗ[R₁] (Fin 0→R₁)) 0
     (by ext f i;exact Fin.elim0 i)
   exact z61 S₁ (Fin 0→R₀) 0
  | succ m ih =>
   let i0:R₀ →ₗ[R₁] (Fin (m+1)→R₀) :=
    {
     toFun:=fun a=>Fin.cons a 0
     map_add':=fun a b=>by ext i;refine Fin.cases rfl (fun _=>by simp) i
     map_smul':=fun r a=>by ext i;refine Fin.cases rfl (fun _=>by simp) i }
   let p0:(Fin (m+1)→R₀) →ₗ[R₁] (Fin m→R₀) :=
    {
     toFun:=fun f j=>f j.succ
     map_add':=fun _ _=>rfl
     map_smul':=fun _ _=>rfl }
   have hi0:Injective i0:=fun a b h=>congrFun h 0
   have hp0:Surjective p0:=fun f=>⟨Fin.cons 0 f,by ext j;rfl⟩
   have q34:LinearMap.range i0=LinearMap.ker p0:=by
    ext f;simp only [LinearMap.mem_range,LinearMap.mem_ker,i0,p0,LinearMap.coe_mk,AddHom.coe_mk];constructor
    · rintro ⟨a,rfl⟩;ext j;rfl
    ·
     intro hf;refine ⟨f 0,?_⟩;ext i
     refine Fin.cases rfl (fun j => ?_) i
     exact (congrFun hf j).symm
   obtain ⟨_,_,h2,_⟩:=z63 S₁ i0 p0 hi0 hp0 q34
   refine subsingleton_iff_forall_eq 0 |>.mpr fun z => ?_
   have hpz:z57 S₁ p0 1 z=0:=Subsingleton.elim _ 0;obtain ⟨w,rfl⟩:=(h2 1 z).mp hpz;rw [Subsingleton.elim w 0,map_zero]
 have q3:∀ (M:Type) [AddCommGroup M] [Module R₁ M] [Module.Finite R₁ M],(∀ m:M,x•m=0)→Subsingleton (z56 R₁ S₁ M 1):=by
  intro M _ _ _ hMx
  let : Module R₀ M :=
   {
    smul:=fun r m=>Quotient.liftOn' r (fun a=>a•m) (fun a b hab=>by
     have q33:b - a∈span {x}:=by
      simpa [sub_eq_neg_add] using QuotientAddGroup.leftRel_apply.mp hab
     obtain ⟨c,hc⟩:=mem_span_singleton.mp q33
     have hba:b=a+x*c:=by rw [← hc];ring
     rw [hba,add_smul,mul_comm,mul_smul,hMx,smul_zero,add_zero])
    one_smul:=fun m=>one_smul R₁ m
    mul_smul:=fun r s m=>Quotient.inductionOn₂' r s fun a b=>mul_smul a b m
    smul_zero:=fun r=>Quotient.inductionOn' r fun a=>smul_zero a
    smul_add:=fun r m₁ m₂=>Quotient.inductionOn' r fun a=>smul_add a m₁ m₂
    add_smul:=fun r s m=>Quotient.inductionOn₂' r s fun a b=>add_smul a b m
    zero_smul:=fun m=>zero_smul R₁ m }
  have : IsScalarTower R₁ R₀ M:=⟨fun a r m=>Quotient.inductionOn' r fun b=>mul_smul a b m⟩
  obtain ⟨T,hT⟩:=Module.Finite.fg_top (R:=R₁) (M:=M);let m:=T.card;let eT:Fin m ≃ T:=(Fintype.equivFinOfCardEq (Fintype.card_coe T)).symm
  let pM:(Fin m→R₀) →ₗ[R₀] M :=
   {
    toFun:=fun g => ∑ i:Fin m,g i•(eT i:M)
    map_add':=fun g₁ g₂=>by simp [add_smul,Finset.sum_add_distrib]
    map_smul':=fun r g=>by simp [Finset.smul_sum,mul_smul] }
  have q13:Surjective pM:=fun y=>by
   have hy:y∈Submodule.span R₁ (T:Set M):=hT▸Submodule.mem_top;rw [Submodule.mem_span_finset] at hy;obtain ⟨c,_,rfl⟩:=hy
   refine ⟨fun i=>Ideal.Quotient.mk (span {x}) (c (eT i).1),?_⟩
   change ∑ i:Fin m,c (eT i).1•(eT i:M) = ∑ t∈T,c t•t
   rw [← Finset.sum_coe_sort T (fun t=>c t•t)]
   exact Fintype.sum_equiv eT _ _ fun _=>rfl
  let K:=LinearMap.ker pM;let iK:K →ₗ[R₀] (Fin m→R₀):=K.subtype;have q18:Injective iK:=Subtype.val_injective;let iK₁ : K →ₗ[R₁] (Fin m→R₀):=iK.restrictScalars R₁;let pM₁ : (Fin m→R₀) →ₗ[R₁] M:=pM.restrictScalars R₁
  have q34:LinearMap.range iK₁ = LinearMap.ker pM₁ := by
   ext g
   exact ⟨fun ⟨⟨y,hy⟩,h⟩=>h▸hy,fun hg=>⟨⟨g,hg⟩,rfl⟩⟩
  obtain ⟨δ,h1,_,h3⟩:=z63 S₁ iK₁ pM₁ q18 q13 q34;have : Subsingleton (z56 R₁ S₁ (Fin m→R₀) 1):=q2 m
  have q1:Injective (LinearMap.lTensor S₁ iK₁):=by
   have q8:∀ (N:Type) [AddCommGroup N] [Module R₁ N] [Module R₀ N] [IsScalarTower R₁ R₀ N],
     ∃ e:(S₁ ⊗[R₁] N) ≃ₗ[R₁] (S₀ ⊗[R₀] N),∀ (s:S₁) (n:N),e (s ⊗ₜ[R₁] n)=Ideal.Quotient.mk (span {algebraMap R₁ S₁ x}) s ⊗ₜ[R₀] n:=by
    intro N _ _ _ _
    let fwd:(S₁ ⊗[R₁] N) →ₗ[R₁] (S₀ ⊗[R₀] N) :=
     TensorProduct.lift
      {
       toFun:=fun s =>
        {
         toFun:=fun n=>Ideal.Quotient.mk (span {algebraMap R₁ S₁ x}) s ⊗ₜ[R₀] n
         map_add':=fun n₁ n₂=>tmul_add _ _ _
         map_smul':=fun r n=>by
          change Ideal.Quotient.mk _ s ⊗ₜ[R₀] (r•n)=r•(Ideal.Quotient.mk _ s ⊗ₜ[R₀] n);rw [← algebraMap_smul R₀ r n,TensorProduct.tmul_smul];have hL:(algebraMap R₁ R₀ r)•(Ideal.Quotient.mk (span {algebraMap R₁ S₁ x}) s ⊗ₜ[R₀] n)=((algebraMap R₁ R₀ r)•Ideal.Quotient.mk (span {algebraMap R₁ S₁ x}) s) ⊗ₜ[R₀] n:=(smul_tmul' _ _ _).symm
          have hR:r•(Ideal.Quotient.mk (span {algebraMap R₁ S₁ x}) s ⊗ₜ[R₀] n)=(r•Ideal.Quotient.mk (span {algebraMap R₁ S₁ x}) s) ⊗ₜ[R₀] n:=(smul_tmul' _ _ _).symm;rw [hL,hR];congr 1;rw [Algebra.smul_def,Algebra.smul_def]
          rfl }
       map_add':=fun s₁ s₂=>by ext n;simp [add_tmul]
       map_smul':=fun r s=>by
        ext n;let mkS:S₁ →+* S₀ := Ideal.Quotient.mk (span {algebraMap R₁ S₁ x});change mkS (r•s) ⊗ₜ[R₀] n=r•(mkS s ⊗ₜ[R₀] n)
        have h1:mkS (r•s)=r•mkS s:=by
         rw [Algebra.smul_def,map_mul,Algebra.smul_def];rfl
        rw [h1,smul_tmul'] }
    have hxt:∀ t':S₁ ⊗[R₁] N,x•t'=0:=fun t'=>by
     induction t' using TensorProduct.induction_on with
     | zero=>simp
     | tmul s n =>
      rw [← TensorProduct.tmul_smul,← algebraMap_smul R₀ x n];have hx0:algebraMap R₁ R₀ x=0:=Ideal.Quotient.eq_zero_iff_mem.mpr (subset_span rfl);rw [hx0,zero_smul,tmul_zero]
     | add t₁ t₂ ih₁ ih₂=>rw [smul_add,ih₁,ih₂,add_zero]
    let : Module R₀ (S₁ ⊗[R₁] N) :=
     {
      smul:=fun r t=>Quotient.liftOn' r (fun a=>a•t) (fun a b hab=>by
       have q33:b - a∈span {x}:=by
        simpa [sub_eq_neg_add] using QuotientAddGroup.leftRel_apply.mp hab
       obtain ⟨c,hc⟩:=mem_span_singleton.mp q33
       have hba:b=a+x*c:=by rw [← hc];ring
       rw [hba,add_smul,mul_comm,mul_smul,hxt,smul_zero,add_zero])
      one_smul:=fun t=>one_smul R₁ t
      mul_smul:=fun r s t=>Quotient.inductionOn₂' r s fun a b=>mul_smul a b t
      smul_zero:=fun r=>Quotient.inductionOn' r fun a=>smul_zero a
      smul_add:=fun r t₁ t₂=>Quotient.inductionOn' r fun a=>smul_add a t₁ t₂
      add_smul:=fun r s t=>Quotient.inductionOn₂' r s fun a b=>add_smul a b t
      zero_smul:=fun t=>zero_smul R₁ t }
    have : IsScalarTower R₁ R₀ (S₁ ⊗[R₁] N):=⟨fun a r t=>Quotient.inductionOn' r fun b=>mul_smul a b t⟩
    let q31:S₁ →ₗ[R₁] (N →ₗ[R₀] (S₁ ⊗[R₁] N)) :=
     {
      toFun:=fun s =>
       {
        toFun:=fun n=>s ⊗ₜ[R₁] n
        map_add':=fun n₁ n₂=>tmul_add s n₁ n₂
        map_smul':=fun r n=>Quotient.inductionOn' r fun a=>by
         change s ⊗ₜ[R₁] (algebraMap R₁ R₀ a•n)=a•(s ⊗ₜ[R₁] n)
         rw [algebraMap_smul,TensorProduct.tmul_smul] }
      map_add':=fun s₁ s₂=>by ext n;exact add_tmul s₁ s₂ n
      map_smul':=fun a s=>by
       ext n;change (a•s) ⊗ₜ[R₁] n=a•(s ⊗ₜ[R₁] n)
       rw [smul_tmul'] }
    let q20:S₀ →ₗ[R₀] (N →ₗ[R₀] (S₁ ⊗[R₁] N)) :=
     {
      toFun:=fun s0=>Quotient.liftOn' s0 (fun s=>q31 s) (fun s₁ s₂ hs=>by
       have q33:s₂ - s₁ ∈ span {algebraMap R₁ S₁ x}:=by
        simpa [sub_eq_neg_add] using QuotientAddGroup.leftRel_apply.mp hs
       obtain ⟨c,hc⟩:=mem_span_singleton.mp q33
       have hs2:s₂ = s₁ + algebraMap R₁ S₁ x*c:=by rw [← hc];ring
       ext n;change s₁ ⊗ₜ[R₁] n=s₂ ⊗ₜ[R₁] n;rw [hs2,add_tmul,← Algebra.smul_def,smul_tmul,← algebraMap_smul R₀ x n];have hx0:algebraMap R₁ R₀ x=0:=Ideal.Quotient.eq_zero_iff_mem.mpr (subset_span rfl)
       rw [hx0,zero_smul,tmul_zero,add_zero])
      map_add':=fun s₁ s₂=>Quotient.inductionOn₂' s₁ s₂ fun a b=>by
       ext n;exact add_tmul a b n
      map_smul':=fun r s0=>Quotient.inductionOn₂' r s0 fun a s=>by
       ext n;change (algebraMap R₁ S₁ a*s) ⊗ₜ[R₁] n=a•(s ⊗ₜ[R₁] n)
       rw [← Algebra.smul_def,smul_tmul'] }
    let bwd:(S₀ ⊗[R₀] N) →ₗ[R₀] (S₁ ⊗[R₁] N):=TensorProduct.lift q20
    let bwd₁ : (S₀ ⊗[R₀] N) →ₗ[R₁] (S₁ ⊗[R₁] N) :=
     {
      toFun:=bwd
      map_add':=bwd.map_add
      map_smul':=fun a t=>by
       induction t using TensorProduct.induction_on with
       | zero=>simp
       | tmul s0 n =>
        refine Quotient.inductionOn' s0 fun s => ?_
        change bwd ((Ideal.Quotient.mk _ (a•s)) ⊗ₜ[R₀] n)=a•(s ⊗ₜ[R₁] n);exact smul_tmul' a s n
       | add t₁ t₂ ih₁ ih₂=>simp [map_add,smul_add,ih₁,ih₂] }
    refine ⟨LinearEquiv.ofLinearMap fwd bwd₁ ?_ ?_,fun s n=>rfl⟩
    ·
     ext t
     induction t using TensorProduct.induction_on with
     | zero=>simp
     | tmul s0 n=>refine Quotient.inductionOn' s0 fun s=>rfl
     | add t₁ t₂ ih₁ ih₂=>simp [map_add,ih₁,ih₂]
    ·
     apply TensorProduct.ext';intro s n;rfl
   obtain ⟨eK,heK⟩:=q8 K;obtain ⟨eF,heF⟩:=q8 (Fin m→R₀)
   have q32:∀ t:S₁ ⊗[R₁] K,eF (LinearMap.lTensor S₁ iK₁ t)=LinearMap.lTensor S₀ iK (eK t):=fun t=>by
    induction t using TensorProduct.induction_on with
    | zero=>simp
    | tmul s k=>simp [heK,heF,iK₁]
    | add t₁ t₂ ih₁ ih₂=>simp [map_add,ih₁,ih₂]
   intro t₁ t₂ ht;apply eK.injective;apply Module.Flat.lTensor_preserves_injective_linearMap iK q18;rw [← q32,← q32,ht]
  refine subsingleton_iff_forall_eq 0 |>.mpr fun z => ?_
  have hδ0 : δ 0 z=0:=by
   apply (z59 R₁ S₁ K).injective;rw [map_zero];apply q1;rw [map_zero,← z60];have q30:z57 S₁ iK₁ 0 (δ 0 z)=0:=(h1 0 (δ 0 z)).mpr ⟨z,rfl⟩;rw [q30,map_zero]
  obtain ⟨w,hw⟩:=(h3 0 z).mp hδ0;rw [← hw,Subsingleton.elim w 0,map_zero]
 have q0:∀ (k : ℕ) (M:Type) [AddCommGroup M] [Module R₁ M] [Module.Finite R₁ M],(∀ m:M,(x ^ k)•m=0)→Subsingleton (z56 R₁ S₁ M 1):=by
  intro k
  induction k with
  | zero =>
   intro M _ _ _ hM0
   have : Subsingleton M:=subsingleton_iff_forall_eq 0 |>.mpr fun m=>by
    simpa using hM0 m
   have : Module.Projective R₁ M:=Module.Projective.of_split (0:M →ₗ[R₁] (Fin 0→R₁)) 0 (by ext m;exact Subsingleton.elim _ _);exact z61 S₁ M 0
  | succ k ih =>
   intro M _ _ _ hMk;let N:Submodule R₁ M:=LinearMap.range (x•LinearMap.id (R:=R₁) (M:=M));have : Module.Finite R₁ N:=Module.Finite.iff_fg.mpr (IsNoetherian.noetherian N)
   have hNk:∀ y:N,(x ^ k)•y=0:=fun ⟨y,hy⟩=>by
    apply Subtype.ext;obtain ⟨m,rfl⟩:=hy;change (x ^ k)•(x•m)=0;rw [← mul_smul,← pow_succ];exact hMk m
   have hQx:∀ q:M⧸N,x•q=0:=fun q=>by
    obtain ⟨m,rfl⟩:=Submodule.Quotient.mk_surjective N q
    change Submodule.Quotient.mk (p:=N) (x•m)=0
    rw [Submodule.Quotient.mk_eq_zero];exact ⟨m,rfl⟩
   have : Subsingleton (z56 R₁ S₁ N 1):=ih N hNk;have : Subsingleton (z56 R₁ S₁ (M⧸N) 1):=q3 (M⧸N) hQx
   obtain ⟨_,_,h2,_⟩:=z63 S₁ N.subtype N.mkQ
    Subtype.val_injective (Submodule.mkQ_surjective N)
    (by rw [Submodule.range_subtype,Submodule.ker_mkQ])
   refine subsingleton_iff_forall_eq 0 |>.mpr fun z => ?_
   obtain ⟨w,rfl⟩:=(h2 1 z).mp (Subsingleton.elim _ 0);rw [Subsingleton.elim w 0,map_zero]
 have q12:∀ (M:Type) [AddCommGroup M] [Module R₁ M] [Module.Finite R₁ M],Subsingleton (z56 R₁ S₁ M 1):=by
  intro M _ _ _
  let M0:Submodule R₁ M :=
   {
    carrier:={ m:M | ∃ k : ℕ,(x ^ k)•m=0 }
    add_mem':=fun {a b} ⟨ka,hka⟩ ⟨kb,hkb⟩=>⟨ka+kb,by
     rw [smul_add,pow_add,mul_smul,mul_smul,hkb,smul_zero,add_zero,smul_comm,hka,smul_zero]⟩
    zero_mem':=⟨0,by simp⟩
    smul_mem':=fun r {a} ⟨k,hk⟩=>⟨k,by rw [smul_comm,hk,smul_zero]⟩ }
  have : Module.Finite R₁ M0:=Module.Finite.iff_fg.mpr (IsNoetherian.noetherian M0);obtain ⟨U,hU⟩:=Module.Finite.fg_top (R:=R₁) (M:=M0)
  let Nmax : ℕ := U.sup fun u=>u.2.choose
  have q9:∀ u:M0,(x ^ Nmax)•u=0:=fun u=>by
   have hu:u∈Submodule.span R₁ (U:Set M0):=hU▸Submodule.mem_top;rw [Submodule.mem_span_finset] at hu;obtain ⟨c,_,rfl⟩:=hu;rw [Finset.smul_sum]
   refine Finset.sum_eq_zero fun v hv => ?_
   rw [smul_comm]
   have hle:v.2.choose ≤ Nmax:=Finset.le_sup (f:=fun w:M0=>w.2.choose) hv
   have h0:(x ^ Nmax)•v=0:=by
    apply Subtype.ext;change (x ^ Nmax)•(v:M)=0;rw [← Nat.sub_add_cancel hle,pow_add,mul_smul,v.2.choose_spec,smul_zero]
   rw [h0,smul_zero]
  have : Subsingleton (z56 R₁ S₁ M0 1):=q0 Nmax M0 q9;let Mbar:=M⧸M0
  have q15:Injective (x•LinearMap.id (R:=R₁) (M:=Mbar)):=by
   rw [injective_iff_map_eq_zero];intro q hq;obtain ⟨m,rfl⟩:=Submodule.Quotient.mk_surjective M0 q
   change Submodule.Quotient.mk (p:=M0) (x•m)=0 at hq
   rw [Submodule.Quotient.mk_eq_zero] at hq;obtain ⟨k,hk⟩:=hq;rw [Submodule.Quotient.mk_eq_zero]
   refine ⟨k+1,?_⟩
   rw [pow_succ,mul_smul];exact hk
  have q6:Subsingleton (z56 R₁ S₁ Mbar 1):=by
   let q29:Submodule R₁ Mbar:=LinearMap.range (x•LinearMap.id (R:=R₁) (M:=Mbar));let Qbar:=Mbar⧸q29
   have q16:∀ q:Qbar,x•q=0:=fun q=>by
    obtain ⟨m,rfl⟩:=Submodule.Quotient.mk_surjective q29 q
    change Submodule.Quotient.mk (p:=q29) (x•m)=0
    rw [Submodule.Quotient.mk_eq_zero];exact ⟨m,rfl⟩
   have : Subsingleton (z56 R₁ S₁ Qbar 1):=q3 Qbar q16;have q21:LinearMap.range (x•LinearMap.id (R:=R₁) (M:=Mbar))=LinearMap.ker q29.mkQ:=(Submodule.ker_mkQ q29).symm
   obtain ⟨_,_,h2_x,_⟩:=z63 S₁ (x•LinearMap.id (R:=R₁) (M:=Mbar))
    q29.mkQ q15 (Submodule.mkQ_surjective q29) q21
   have q17:Surjective (fun z:z56 R₁ S₁ Mbar 1=>x•z):=fun z=>by
    obtain ⟨w,hw⟩:=(h2_x 1 z).mp (Subsingleton.elim _ 0);exact ⟨w,(z64 S₁ Mbar x 1 w).symm.trans hw⟩
   obtain ⟨Tm,hTm⟩:=Module.Finite.fg_top (R:=R₁) (M:=Mbar);let r:=Tm.card;let eTm:Fin r ≃ Tm:=(Fintype.equivFinOfCardEq (Fintype.card_coe Tm)).symm
   let pF:(Fin r→R₁) →ₗ[R₁] Mbar :=
    {
     toFun:=fun g => ∑ i:Fin r,g i•(eTm i:Mbar)
     map_add':=fun g₁ g₂=>by simp [add_smul,Finset.sum_add_distrib]
     map_smul':=fun a g=>by simp [Finset.smul_sum,mul_smul] }
   have q7:Surjective pF:=fun y=>by
    have hy:y∈Submodule.span R₁ (Tm:Set Mbar):=hTm▸Submodule.mem_top;rw [Submodule.mem_span_finset] at hy;obtain ⟨c,_,rfl⟩:=hy
    refine ⟨fun i=>c (eTm i).1,?_⟩
    change ∑ i:Fin r,c (eTm i).1•(eTm i:Mbar) = ∑ t∈Tm,c t•t
    rw [← Finset.sum_coe_sort Tm (fun t=>c t•t)]
    exact Fintype.sum_equiv eTm _ _ fun _=>rfl
   let L:=LinearMap.ker pF;have : Module.Finite R₁ L:=Module.Finite.iff_fg.mpr (IsNoetherian.noetherian L)
   obtain ⟨δF,hF1,_,hF3⟩:=z63 S₁ L.subtype pF
    Subtype.val_injective q7 (Submodule.range_subtype L)
   have : Subsingleton (z56 R₁ S₁ (Fin r→R₁) 1):=z61 S₁ (Fin r→R₁) 0
   have hδF_inj:Injective (δF 0):=by
    rw [injective_iff_map_eq_zero];intro z hz;obtain ⟨w,rfl⟩:=(hF3 0 z).mp hz;rw [Subsingleton.elim w 0,map_zero]
   let q26:(S₁ ⊗[R₁] L) →ₗ[S₁] (S₁ ⊗[R₁] (Fin r→R₁)):=LinearMap.baseChange S₁ L.subtype;let K':Submodule S₁ (S₁ ⊗[R₁] L):=LinearMap.ker q26;have : Module.Finite S₁ (S₁ ⊗[R₁] L):=inferInstance;have q22:K'.FG:=IsNoetherian.noetherian K'
   have q23:K' ≤ maximalIdeal S₁ • K':=by
    intro t ht
    have q28:z57 S₁ L.subtype 0 ((z59 R₁ S₁ L).symm t)=0:=by
     apply (z59 R₁ S₁ (Fin r→R₁)).injective;rw [z60,LinearEquiv.apply_symm_apply,map_zero];exact ht
    obtain ⟨z,hz⟩:=(hF1 0 _).mp q28;obtain ⟨z',hz'⟩:=q17 z;dsimp only at hz';let t':S₁ ⊗[R₁] L:=z59 R₁ S₁ L (δF 0 z')
    have q14:t'∈K':=by
     change LinearMap.lTensor S₁ L.subtype (z59 R₁ S₁ L (δF 0 z'))=0;rw [← z60];have : z57 S₁ L.subtype 0 (δF 0 z')=0:=(hF1 0 (δF 0 z')).mpr ⟨z',rfl⟩;rw [this,map_zero]
    have q27:t=(algebraMap R₁ S₁ x)•t':=by
     rw [algebraMap_smul];change t=x•z59 R₁ S₁ L (δF 0 z');rw [← map_smul,← map_smul,hz',hz,LinearEquiv.apply_symm_apply]
    rw [q27];exact Submodule.smul_mem_smul q24 q14
   have q19:K' = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (I:=maximalIdeal S₁) (N:=K') q22 q23
     (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top])
   refine subsingleton_iff_forall_eq 0 |>.mpr fun z => ?_
   apply hδF_inj;rw [map_zero];apply (z59 R₁ S₁ L).injective;rw [map_zero]
   have q35:z59 R₁ S₁ L (δF 0 z)∈K':=by
    change LinearMap.lTensor S₁ L.subtype (z59 R₁ S₁ L (δF 0 z))=0;rw [← z60];have : z57 S₁ L.subtype 0 (δF 0 z)=0:=(hF1 0 (δF 0 z)).mpr ⟨z,rfl⟩;rw [this,map_zero]
   rw [q19] at q35;exact q35
  obtain ⟨_,_,h2_M,_⟩:=z63 S₁ M0.subtype M0.mkQ
   Subtype.val_injective (Submodule.mkQ_surjective M0)
   (by rw [Submodule.range_subtype,Submodule.ker_mkQ])
  refine subsingleton_iff_forall_eq 0 |>.mpr fun z => ?_
  obtain ⟨w,rfl⟩:=(h2_M 1 z).mp (Subsingleton.elim _ 0);rw [Subsingleton.elim w 0,map_zero]
 rw [Module.Flat.iff_lTensor_injective'];intro I;have : Subsingleton (z56 R₁ S₁ (R₁ ⧸ I) 1):=q12 (R₁ ⧸ I)
 obtain ⟨δ,h1,_,_⟩:=z63 S₁ I.subtype I.mkQ
  Subtype.val_injective (Submodule.mkQ_surjective I)
  (by rw [Submodule.range_subtype,Submodule.ker_mkQ])
 rw [injective_iff_map_eq_zero];intro t ht
 have h0:z57 S₁ I.subtype 0 ((z59 R₁ S₁ I).symm t)=0:=by
  apply (z59 R₁ S₁ R₁).injective;rw [z60,LinearEquiv.apply_symm_apply,map_zero];exact ht
 obtain ⟨w,hw⟩:=(h1 0 _).mp h0;rw [Subsingleton.elim w 0,map_zero] at hw;exact (z59 R₁ S₁ I).symm.injective (hw.symm.trans (map_zero _).symm)
private lemma z74 {R₀ S₀ A B:Type} [CommRing R₀] [CommRing S₀]
  [CommRing A] [CommRing B] [Algebra R₀ S₀] [Algebra A B] [Module.Flat A B]
  (eA:R₀ ≃+* A) (eB:S₀ ≃+* B)
  (q1:∀ r:R₀,eB (algebraMap R₀ S₀ r)=algebraMap A B (eA r)) :
  Module.Flat R₀ S₀ := by
 rw [Module.Flat.iff_lTensor_injective'];intro I;let IA:Ideal A:=I.map eA.toRingHom;have q0:Injective (LinearMap.lTensor B IA.subtype):=Module.Flat.lTensor_preserves_injective_linearMap IA.subtype Subtype.val_injective;let : Module R₀ IA:=Module.compHom IA eA.toRingHom;let : Module R₀ (B ⊗[A] IA):=Module.compHom (B ⊗[A] IA) eA.toRingHom
 let : Module A (S₀ ⊗[R₀] I):=Module.compHom (S₀ ⊗[R₀] I) eA.symm.toRingHom;let : Module R₀ (B ⊗[A] A):=Module.compHom (B ⊗[A] A) eA.toRingHom
 let eI:I ≃ₗ[R₀] IA :=
  {
   toFun:=fun x=>⟨eA x.1,mem_map_of_mem eA.toRingHom x.2⟩
   invFun:=fun y=>⟨eA.symm y.1,by
    obtain ⟨a,ha,hay⟩:=(mem_map_iff_of_surjective eA.toRingHom eA.surjective).mp y.2;have : eA.symm y.1=a:=eA.injective (by simpa using hay.symm)
    exact this▸ha⟩
   map_add':=fun _ _=>Subtype.ext (map_add eA _ _)
   map_smul':=fun r x=>Subtype.ext (map_mul eA r x.1)
   left_inv:=fun _=>Subtype.ext (eA.symm_apply_apply _)
   right_inv:=fun _=>Subtype.ext (eA.apply_symm_apply _) }
 let Φ₁ : (S₀ ⊗[R₀] I) →ₗ[R₀] (B ⊗[A] IA) :=
  TensorProduct.lift
   {
    toFun:=fun s0 =>
     {
      toFun:=fun x=>eB s0 ⊗ₜ[A] eI x
      map_add':=fun x₁ x₂=>by rw [map_add,tmul_add]
      map_smul':=fun r0 x=>by
       rw [RingHom.id_apply,map_smul eI]
       exact TensorProduct.tmul_smul (eA r0) (eB s0) (eI x) }
    map_add':=fun s₁ s₂=>by
     apply LinearMap.ext;intro x;exact (congrArg (· ⊗ₜ[A] eI x) (map_add eB s₁ s₂)).trans (add_tmul _ _ _)
    map_smul':=fun r0 s0=>by
     apply LinearMap.ext;intro x;change eB (r0•s0) ⊗ₜ[A] eI x=eA r0•(eB s0 ⊗ₜ[A] eI x);rw [Algebra.smul_def,map_mul,q1,← Algebra.smul_def]
     exact smul_tmul' (eA r0) (eB s0) (eI x) }
 let Ψ₁ : (B ⊗[A] IA) →ₗ[A] (S₀ ⊗[R₀] I) :=
  TensorProduct.lift
   {
    toFun:=fun b =>
     {
      toFun:=fun y=>eB.symm b ⊗ₜ[R₀] eI.symm y
      map_add':=fun y₁ y₂=>by rw [map_add,tmul_add]
      map_smul':=fun a y=>by
       have hsm:eI.symm (a•y)=eA.symm a•eI.symm y:=by
        apply Subtype.ext;exact map_mul eA.symm a y.1
       change eB.symm b ⊗ₜ[R₀] eI.symm (a•y)=eA.symm a•(eB.symm b ⊗ₜ[R₀] eI.symm y);rw [hsm]
       exact TensorProduct.tmul_smul (eA.symm a) (eB.symm b) (eI.symm y) }
    map_add':=fun b₁ b₂=>by
     apply LinearMap.ext;intro y;exact (congrArg (· ⊗ₜ[R₀] eI.symm y) (map_add eB.symm b₁ b₂)).trans (add_tmul _ _ _)
    map_smul':=fun a b=>by
     apply LinearMap.ext;intro y;change eB.symm (a•b) ⊗ₜ[R₀] eI.symm y=eA.symm a•(eB.symm b ⊗ₜ[R₀] eI.symm y)
     have hfa:eB.symm (algebraMap A B a)=algebraMap R₀ S₀ (eA.symm a):=by
      apply eB.injective;rw [eB.apply_symm_apply,q1,eA.apply_symm_apply]
     rw [Algebra.smul_def,map_mul,hfa,← Algebra.smul_def]
     exact smul_tmul' (eA.symm a) (eB.symm b) (eI.symm y) }
 have hΨΦ : ∀ t:S₀ ⊗[R₀] I,Ψ₁ (Φ₁ t)=t:=fun t=>by
  induction t using TensorProduct.induction_on with
  | zero=>simp
  | tmul s0 x =>
   change eB.symm (eB s0) ⊗ₜ[R₀] eI.symm (eI x)=s0 ⊗ₜ[R₀] x;rw [eB.symm_apply_apply,eI.symm_apply_apply]
  | add t₁ t₂ ih₁ ih₂=>rw [map_add,map_add,ih₁,ih₂]
 let Φ₂ : (S₀ ⊗[R₀] R₀) →ₗ[R₀] (B ⊗[A] A) :=
  TensorProduct.lift
   {
    toFun:=fun s0 =>
     {
      toFun:=fun r0=>eB s0 ⊗ₜ[A] eA r0
      map_add':=fun x₁ x₂=>by rw [map_add,tmul_add]
      map_smul':=fun r x=>by
       change eB s0 ⊗ₜ[A] eA (r*x)=eA r•(eB s0 ⊗ₜ[A] eA x);rw [map_mul,← smul_eq_mul]
       exact TensorProduct.tmul_smul (eA r) (eB s0) (eA x) }
    map_add':=fun s₁ s₂=>by
     apply LinearMap.ext;intro x;exact (congrArg (· ⊗ₜ[A] eA x) (map_add eB s₁ s₂)).trans (add_tmul _ _ _)
    map_smul':=fun r s0=>by
     apply LinearMap.ext;intro x;change eB (r•s0) ⊗ₜ[A] eA x=eA r•(eB s0 ⊗ₜ[A] eA x);rw [Algebra.smul_def,map_mul,q1,← Algebra.smul_def]
     exact smul_tmul' (eA r) (eB s0) (eA x) }
 have hsq:∀ t:S₀ ⊗[R₀] I,Φ₂ (LinearMap.lTensor S₀ I.subtype t)=LinearMap.lTensor B IA.subtype (Φ₁ t):=fun t=>by
  induction t using TensorProduct.induction_on with
  | zero=>simp
  | tmul s0 x=>rfl
  | add t₁ t₂ ih₁ ih₂=>rw [map_add,map_add,map_add,map_add,ih₁,ih₂]
 intro t₁ t₂ ht
 have h1:LinearMap.lTensor B IA.subtype (Φ₁ t₁)=LinearMap.lTensor B IA.subtype (Φ₁ t₂):=by
  rw [← hsq,← hsq,ht]
 have h2 : Φ₁ t₁ = Φ₁ t₂ := q0 h1;rw [← hΨΦ t₁,← hΨΦ t₂,h2]
private lemma z75 {V D:Type} [CommRing V] [IsDomain V]
  [IsDiscreteValuationRing V] [CommRing D] [IsDomain D] [Algebra V D]
  (q0:Injective (algebraMap V D)) : Module.Flat V D:=by
 rw [IsDedekindDomain.flat_iff_torsion_eq_bot,← Submodule.isTorsionFree_iff_torsion_eq_bot]
 exact Module.IsTorsionFree.of_smul_eq_zero fun {v d} hvd=>by
  rw [Algebra.smul_def,mul_eq_zero] at hvd
  exact hvd.imp (fun hv=>q0 (hv.trans (map_zero _).symm)) id
lemma z76 {A B:Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
  (f:A →+* B) (q4:∀ a∈maximalIdeal A,f a∈maximalIdeal B)
  (q5:letI : Algebra A B:=f.toAlgebra;Module.Flat A B) :
  letI : Algebra (PowerSeries A) (PowerSeries B):=(PowerSeries.map f).toAlgebra
  Module.Flat (PowerSeries A) (PowerSeries B):=by
 let : Algebra A B:=f.toAlgebra;let : Algebra (PowerSeries A) (PowerSeries B):=(PowerSeries.map f).toAlgebra;have : Module.Flat A B:=q5
 have q3:algebraMap (PowerSeries A) (PowerSeries B) PowerSeries.X ∈
   maximalIdeal (PowerSeries B):=by
  change PowerSeries.map f PowerSeries.X∈maximalIdeal (PowerSeries B);rw [PowerSeries.map_X];exact z4
 have q1:∀ (C:Type) [CommRing C],IsSMulRegular (PowerSeries C) (PowerSeries.X:PowerSeries C):=by
  intro C _ a b hab;ext k;have hk:=congrArg (PowerSeries.coeff (k+1)) hab;simpa [smul_eq_mul,PowerSeries.coeff_succ_X_mul] using hk
 have q7:IsSMulRegular (PowerSeries B) (algebraMap (PowerSeries A) (PowerSeries B) PowerSeries.X):=by
  change IsSMulRegular (PowerSeries B) (PowerSeries.map f PowerSeries.X);rw [PowerSeries.map_X];exact q1 B
 refine z73 PowerSeries.X q3 (q1 A) q7 ?_
 have q0:∀ (C:Type) [CommRing C],RingHom.ker (PowerSeries.constantCoeff (R:=C))=span {(PowerSeries.X:PowerSeries C)}:=by
  intro C _
  refine le_antisymm ?_ ?_
  ·
   intro F hF;rw [RingHom.mem_ker] at hF
   have h1:=z6 1 F (fun i hi=>by
    have hi0:i=0:=by omega
    subst hi0;simpa using hF)
   simpa using h1
  · rw [span_singleton_le_iff_mem,RingHom.mem_ker,PowerSeries.constantCoeff_X]
 let eA:(PowerSeries A⧸span {(PowerSeries.X:PowerSeries A)}) ≃+* A :=
  (Ideal.quotEquivOfEq (q0 A).symm).trans
   (RingHom.quotientKerEquivOfSurjective PowerSeries.constantCoeff_surj)
 have q2:span {algebraMap (PowerSeries A) (PowerSeries B) PowerSeries.X} = span {(PowerSeries.X:PowerSeries B)}:=by
  change span {PowerSeries.map f PowerSeries.X} = _;rw [PowerSeries.map_X]
 let eB:(PowerSeries B⧸span {algebraMap (PowerSeries A) (PowerSeries B) PowerSeries.X}) ≃+* B :=
  (Ideal.quotEquivOfEq q2).trans
   ((Ideal.quotEquivOfEq (q0 B).symm).trans
    (RingHom.quotientKerEquivOfSurjective PowerSeries.constantCoeff_surj))
 let R₀ := PowerSeries A⧸span {(PowerSeries.X:PowerSeries A)};let S₀ := PowerSeries B⧸span {algebraMap (PowerSeries A) (PowerSeries B) PowerSeries.X}
 let f₀ : R₀ →+* S₀ := Ideal.Quotient.lift (span {PowerSeries.X})
  ((Ideal.Quotient.mk _).comp (algebraMap (PowerSeries A) (PowerSeries B)))
  (fun a ha=>by
   obtain ⟨r,rfl⟩:=mem_span_singleton.mp ha;rw [RingHom.comp_apply,map_mul,Ideal.Quotient.eq_zero_iff_mem]
   exact Ideal.mul_mem_right _ _ (subset_span rfl))
 let : Algebra R₀ S₀ := f₀.toAlgebra
 have q6:∀ r0:R₀,eB (algebraMap R₀ S₀ r0)=algebraMap A B (eA r0):=fun r0=>by
  obtain ⟨F,rfl⟩:=Ideal.Quotient.mk_surjective r0;change PowerSeries.constantCoeff (PowerSeries.map f F)=f (PowerSeries.constantCoeff F);rw [← PowerSeries.coeff_zero_eq_constantCoeff,PowerSeries.coeff_map,PowerSeries.coeff_zero_eq_constantCoeff]
 exact z74 eA eB q6
lemma z77 {V D:Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [CommRing D] [IsDomain D] [IsLocalRing D] [IsNoetherianRing D]
  (f:V →+* D) (p:V) (hp:maximalIdeal V=span {p})
  (q0:f p∈maximalIdeal D) (q1:f p≠0) :
  ∀ n : ℕ,
   letI : Algebra (z0 V n) (z0 D n):=(z15 f n).toAlgebra
   Module.Flat (z0 V n) (z0 D n):=by
 have q2:∀ v∈maximalIdeal V,f v∈maximalIdeal D:=fun v hv=>by
  rw [hp,mem_span_singleton] at hv;obtain ⟨a,rfl⟩:=hv;rw [map_mul];exact (maximalIdeal D).mul_mem_right _ q0
 have q3:Injective f:=by
  rw [RingHom.injective_iff_ker_eq_bot]
  by_contra hker
  obtain ⟨v,hv_ker,hv_ne⟩ : ∃ v∈RingHom.ker f,v≠0:=by
   by_contra h;push Not at h
   exact hker (le_antisymm (fun x hx=>h x hx) bot_le)
  obtain ⟨k,u,hv_eq⟩:=IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hv_ne
   ((IsDiscreteValuationRing.irreducible_iff_uniformizer p).mpr hp)
  rw [hv_eq,RingHom.mem_ker,map_mul,map_pow] at hv_ker
  have q4:f u≠0:=fun h0=>by
   have h1:f (u*u⁻¹)=0:=by rw [map_mul,h0,zero_mul]
   rw [Units.mul_inv,map_one] at h1;exact one_ne_zero h1
  exact (mul_ne_zero q4 (pow_ne_zero k q1)) hv_ker
 intro n
 induction n with
 | zero =>
  dsimp only [z0,z15];let : Algebra V D:=f.toAlgebra;exact z75 q3
 | succ n ih =>
  exact z76 (z15 f n) (fun a ha=>z23 q2 n ha) ih
end TorAndFlatness
section KoszulComplex
open CategoryTheory
lemma z78 {R:Type} [CommRing R]
  (K:ChainComplex (ModuleCat.{0} R) ℕ) :
  Nonempty (K.homology 0 ≃ₗ[R] (K.X 0⧸LinearMap.range (K.d 1 0).hom)):=by
 have hg0:(K.sc' 1 0 0).g=0:=K.shape 0 0 (by simp);have _:IsIso (K.sc' 1 0 0).homologyι := ShortComplex.isIso_homologyι (K.sc' 1 0 0) hg0;let e1:K.homology 0 ≅ (K.sc' 1 0 0).homology:=K.homologyIsoSc' 1 0 0 (ChainComplex.prev ℕ 0) ChainComplex.next_nat_zero;let e2:(K.sc' 1 0 0).homology ≅ (K.sc' 1 0 0).opcycles:=asIso (K.sc' 1 0 0).homologyι
 let e3:(K.sc' 1 0 0).opcycles ≅ ModuleCat.of R (K.X 0⧸LinearMap.range (K.d 1 0).hom):=(K.sc' 1 0 0).moduleCatOpcyclesIso;exact ⟨(e1 ≪≫ e2 ≪≫ e3).toLinearEquiv⟩
lemma z79 {R:Type} [CommRing R]
  (K:ChainComplex (ModuleCat.{0} R) ℕ) (k : ℕ) :
  Nonempty (K.homology (k+1) ≃ₗ[R]
   (LinearMap.ker (K.d (k+1) k).hom ⧸
    (LinearMap.range (K.d (k+2) (k+1)).hom).comap
     (LinearMap.ker (K.d (k+1) k).hom).subtype)):=by
 let eH:K.homology (k+1) ≅ (K.sc' (k+2) (k+1) k).moduleCatLeftHomologyData.H :=
  K.homologyIsoSc' (k+2) (k+1) k (ChainComplex.prev ℕ (k+1)) (ChainComplex.next_nat_succ k) ≪≫
   (K.sc' (k+2) (k+1) k).moduleCatHomologyIso
 have q0:(LinearMap.range (K.d (k+2) (k+1)).hom).comap
   (LinearMap.ker (K.d (k+1) k).hom).subtype =
   LinearMap.range (K.sc' (k+2) (k+1) k).moduleCatToCycles:=by
  ext ⟨y,hy⟩;constructor
  ·
   rintro ⟨a,ha⟩;exact ⟨a,Subtype.ext ha⟩
  ·
   rintro ⟨a,ha⟩;exact ⟨a,congrArg Subtype.val ha⟩
 exact ⟨eH.toLinearEquiv.trans (Submodule.quotEquivOfEq _ _ q0.symm)⟩
abbrev z80 (R M:Type) : List R → ℕ → Type
 | [],0=>M
 | [],_+1=>PUnit
 | _ :: zs,0=>z80 R M zs 0
 | _ :: zs,i+1=>z80 R M zs (i+1)×z80 R M zs i
instance instAddCommGroupKoszulObj (R M:Type) [AddCommGroup M] :
  ∀ (zs:List R) (k : ℕ),AddCommGroup (z80 R M zs k)
 | [],0=>inferInstance
 | [],_+1=>inferInstance
 | _ :: zs,0=>instAddCommGroupKoszulObj R M zs 0
 | _ :: zs,i+1 =>
  letI:=instAddCommGroupKoszulObj R M zs (i+1)
  letI:=instAddCommGroupKoszulObj R M zs i
  inferInstance
instance instModuleKoszulObj (R M:Type) [CommRing R] [AddCommGroup M] [Module R M] :
  ∀ (zs:List R) (k : ℕ),Module R (z80 R M zs k)
 | [],0=>inferInstance
 | [],_+1=>inferInstance
 | _ :: zs,0=>instModuleKoszulObj R M zs 0
 | _ :: zs,i+1 =>
  letI:=instModuleKoszulObj R M zs (i+1)
  letI:=instModuleKoszulObj R M zs i
  inferInstance
def z81 (R M:Type) [CommRing R] [AddCommGroup M] [Module R M] :
  ∀ (zs:List R),z80 R M zs 0 ≃ₗ[R] M
 | []=>LinearEquiv.refl R M
 | _ :: zs=>z81 R M zs
def z82 (R M:Type) [CommRing R] [AddCommGroup M] [Module R M] :
  ∀ (zs:List R) (k : ℕ),z80 R M zs (k+1) →ₗ[R] z80 R M zs k
 | [],_=>0
 | z :: zs,0 =>
  {
   toFun:=fun p=>z82 R M zs 0 p.1+z•p.2
   map_add':=fun p q=>by
    change z82 R M zs 0 (p.1+q.1)+z•(p.2+q.2)=(z82 R M zs 0 p.1+z•p.2)+(z82 R M zs 0 q.1+z•q.2);rw [map_add,smul_add];abel
   map_smul':=fun r p=>by
    change z82 R M zs 0 (r•p.1)+z•(r•p.2)=r•(z82 R M zs 0 p.1+z•p.2)
    rw [map_smul,smul_add,smul_comm] }
 | z :: zs,i+1 =>
  {
   toFun:=fun p=>(z82 R M zs (i+1) p.1+z•p.2,-(z82 R M zs i p.2))
   map_add':=fun p q=>by
    apply Prod.ext
    ·
     change z82 R M zs (i+1) (p.1+q.1)+z•(p.2+q.2)=(z82 R M zs (i+1) p.1+z•p.2)+(z82 R M zs (i+1) q.1+z•q.2);rw [map_add,smul_add];abel
    ·
     change -(z82 R M zs i (p.2+q.2)) = -(z82 R M zs i p.2) + -(z82 R M zs i q.2);rw [map_add,neg_add]
   map_smul':=fun r p=>by
    apply Prod.ext
    ·
     change z82 R M zs (i+1) (r•p.1)+z•(r•p.2)=r•(z82 R M zs (i+1) p.1+z•p.2);rw [map_smul,smul_add,smul_comm]
    ·
     change -(z82 R M zs i (r•p.2))=r • -(z82 R M zs i p.2)
     rw [map_smul,smul_neg] }
lemma z83 {R M:Type} [CommRing R] [AddCommGroup M] [Module R M] :
  ∀ (zs:List R) (k : ℕ) (x:z80 R M zs (k+2)),z82 R M zs k (z82 R M zs (k+1) x)=0
 | [],_,_=>rfl
 | z :: zs,0,(a,b)=>by
  change z82 R M zs 0 (z82 R M zs 1 a+z•b)+z•(-(z82 R M zs 0 b))=0;rw [map_add,map_smul,z83 zs 0 a,zero_add,smul_neg,add_neg_cancel]
 | z :: zs,i+1,(a,b)=>by
  apply Prod.ext
  ·
   change z82 R M zs (i+1) (z82 R M zs (i+2) a+z•b)+z•(-(z82 R M zs (i+1) b))=0;rw [map_add,map_smul,z83 zs (i+1) a,zero_add,smul_neg,add_neg_cancel]
  ·
   change -(z82 R M zs i (-(z82 R M zs (i+1) b)))=0;rw [map_neg,z83 zs i b,neg_zero,neg_zero]
def z84 {R M N:Type} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (f:M →ₗ[R] N) :
  ∀ (zs:List R) (k : ℕ),z80 R M zs k →ₗ[R] z80 R N zs k
 | [],0=>f
 | [],_+1=>0
 | _ :: zs,0=>z84 f zs 0
 | _ :: zs,i+1=>LinearMap.prodMap (z84 f zs (i+1)) (z84 f zs i)
lemma z85 {R M N:Type} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (f:M →ₗ[R] N) :
  ∀ (zs:List R) (k : ℕ) (x:z80 R M zs (k+1)),z84 f zs k (z82 R M zs k x)=z82 R N zs k (z84 f zs (k+1) x)
 | [],_,_=>by simp [z82,z84]
 | z :: zs,0,(a,b)=>by
  change z84 f zs 0 (z82 R M zs 0 a+z•b)=z82 R N zs 0 (z84 f zs 1 a)+z•z84 f zs 0 b;rw [map_add,map_smul,z85 f zs 0 a]
 | z :: zs,i+1,(a,b)=>by
  apply Prod.ext
  ·
   change z84 f zs (i+1) (z82 R M zs (i+1) a+z•b)=z82 R N zs (i+1) (z84 f zs (i+2) a)+z•z84 f zs (i+1) b;rw [map_add,map_smul,z85 f zs (i+1) a]
  ·
   change z84 f zs i (-(z82 R M zs i b)) = -(z82 R N zs i (z84 f zs (i+1) b));rw [map_neg,z85 f zs i b]
lemma z86 {R M N:Type} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {f:M →ₗ[R] N} (hf:Injective f) :
  ∀ (zs:List R) (k : ℕ),Injective (z84 f zs k)
 | [],0=>hf
 | [],_+1=>fun _ _ _=>rfl
 | _ :: zs,0=>z86 hf zs 0
 | _ :: zs,i+1=>Prod.map_injective.mpr
   ⟨z86 hf zs (i+1),z86 hf zs i⟩
lemma z87 {R M N:Type} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {f:M →ₗ[R] N} (hf:Surjective f) :
  ∀ (zs:List R) (k : ℕ),Surjective (z84 f zs k)
 | [],0=>hf
 | [],_+1=>fun _=>⟨PUnit.unit,rfl⟩
 | _ :: zs,0=>z87 hf zs 0
 | _ :: zs,i+1=>Prod.map_surjective.mpr
   ⟨z87 hf zs (i+1),z87 hf zs i⟩
lemma z88 {R A B C:Type} [CommRing R] [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
  {i:A →ₗ[R] B} {p:B →ₗ[R] C} (hip:LinearMap.range i=LinearMap.ker p) :
  ∀ (zs:List R) (k : ℕ),LinearMap.range (z84 i zs k)=LinearMap.ker (z84 p zs k)
 | [],0=>hip
 | [],_+1=>by ext ⟨⟩;simp [z84]
 | _ :: zs,0=>z88 hip zs 0
 | _ :: zs,k+1=>by
  have h1:=z88 hip zs (k+1);have h2:=z88 hip zs k;ext ⟨b₁,b₂⟩;simp only [LinearMap.mem_range,LinearMap.mem_ker,z84,LinearMap.prodMap_apply,Prod.mk.injEq,Prod.ext_iff,Prod.fst_zero,Prod.snd_zero];constructor
  ·
   rintro ⟨⟨a₁,a₂⟩,ha₁,ha₂⟩;exact ⟨LinearMap.mem_ker.mp (h1▸⟨a₁,ha₁⟩),LinearMap.mem_ker.mp (h2▸⟨a₂,ha₂⟩)⟩
  ·
   rintro ⟨hb₁,hb₂⟩;obtain ⟨a₁,ha₁⟩:=(LinearMap.mem_range.mp (h1.symm▸LinearMap.mem_ker.mpr hb₁));obtain ⟨a₂,ha₂⟩:=(LinearMap.mem_range.mp (h2.symm▸LinearMap.mem_ker.mpr hb₂));exact ⟨(a₁,a₂),ha₁,ha₂⟩
lemma z89 {R M:Type} :
  ∀ (zs:List R) (k : ℕ),zs.length < k→Subsingleton (z80 R M zs k)
 | [],0,h=>by omega
 | [],_+1,_=>inferInstance
 | _ :: zs,0,h=>by omega
 | _ :: zs,i+1,h=>by
  simp only [List.length_cons] at h;have : Subsingleton (z80 R M zs (i+1)):=z89 zs (i+1) (by omega);have : Subsingleton (z80 R M zs i):=z89 zs i (by omega);exact inferInstance
lemma z90 {R M:Type} [CommRing R] [AddCommGroup M] [Module R M]
  [Module.Finite R M] :
  ∀ (zs:List R) (k : ℕ),Module.Finite R (z80 R M zs k)
 | [],0=>inferInstance
 | [],_+1=>inferInstance
 | _ :: zs,0=>z90 zs 0
 | _ :: zs,i+1=>by
  have : Module.Finite R (z80 R M zs (i+1)):=z90 zs (i+1);have : Module.Finite R (z80 R M zs i):=z90 zs i;exact inferInstance
lemma z91 {R M:Type} [CommRing R] [AddCommGroup M] [Module R M]
  [Module.Projective R M] :
  ∀ (zs:List R) (k : ℕ),Module.Projective R (z80 R M zs k)
 | [],0=>inferInstance
 | [],_+1 =>
  Module.Projective.of_split (0:PUnit →ₗ[R] (Fin 0→R)) 0 (by ext ⟨⟩)
 | _ :: zs,0=>z91 zs 0
 | _ :: zs,i+1=>by
  have : Module.Projective R (z80 R M zs (i+1)):=z91 zs (i+1);have : Module.Projective R (z80 R M zs i):=z91 zs i;exact inferInstance
lemma z92 {R M:Type} [CommRing R] [AddCommGroup M] [Module R M]
  {z:R} (hz:IsSMulRegular M z) :
  ∀ (zs:List R) (k : ℕ),IsSMulRegular (z80 R M zs k) z
 | [],0=>hz
 | [],_+1=>fun _ _ _=>rfl
 | _ :: zs,0=>z92 hz zs 0
 | _ :: zs,i+1=>fun ⟨a₁,b₁⟩ ⟨a₂,b₂⟩ h=>Prod.ext
   (z92 hz zs (i+1) (congrArg Prod.fst h))
   (z92 hz zs i (congrArg Prod.snd h))
lemma z93 {R M:Type} [CommRing R] [AddCommGroup M] [Module R M]
  {a:R} (ha:∀ m:M,a•m=0) :
  ∀ (zs:List R) (k : ℕ) (x:z80 R M zs k),a•x=0
 | [],0,m=>ha m
 | [],_+1,_=>rfl
 | _ :: zs,0,x=>z93 ha zs 0 x
 | _ :: zs,i+1,(x,y)=>Prod.ext
   (z93 ha zs (i+1) x)
   (z93 ha zs i y)
abbrev z94 (R M:Type) [CommRing R] [AddCommGroup M] [Module R M] (zs:List R) : ℕ → Type
 | 0=>z80 R M zs 0⧸LinearMap.range (z82 R M zs 0)
 | i+1 =>
  LinearMap.ker (z82 R M zs i) ⧸
   (LinearMap.range (z82 R M zs (i+1))).comap (LinearMap.ker (z82 R M zs i)).subtype
instance instAddCommGroupKoszulH (R M:Type) [CommRing R] [AddCommGroup M] [Module R M]
  (zs:List R) : ∀ k : ℕ,AddCommGroup (z94 R M zs k)
 | 0=>inferInstance
 | _+1=>inferInstance
instance instModuleKoszulH (R M:Type) [CommRing R] [AddCommGroup M] [Module R M]
  (zs:List R) : ∀ k : ℕ,Module R (z94 R M zs k)
 | 0=>inferInstance
 | _+1=>inferInstance
lemma z95 {R M:Type} [CommRing R] [AddCommGroup M] [Module R M]
  (zs:List R) (k : ℕ) (h:zs.length < k) :
  Subsingleton (z94 R M zs k):=by
 cases k with
 | zero=>omega
 | succ i =>
  have : Subsingleton (z80 R M zs (i+1)):=z89 zs (i+1) h;have : Subsingleton (LinearMap.ker (z82 R M zs i)):=inferInstance;exact inferInstance
lemma z96 {R M:Type} [CommRing R] [IsNoetherianRing R]
  [AddCommGroup M] [Module R M] [Module.Finite R M] (zs:List R) (k : ℕ) :
  Module.Finite R (z94 R M zs k):=by
 cases k with
 | zero =>
  have : Module.Finite R (z80 R M zs 0):=z90 zs 0;exact inferInstance
 | succ i =>
  have : Module.Finite R (z80 R M zs (i+1)):=z90 zs (i+1);have : Module.Finite R (LinearMap.ker (z82 R M zs i)):=Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _);exact inferInstance
def z97 (R M:Type) [CommRing R] [AddCommGroup M] [Module R M] (zs:List R) :
  ChainComplex (ModuleCat.{0} R) ℕ :=
 ChainComplex.of
  (fun k=>ModuleCat.of R (z80 R M zs k))
  (fun k=>ModuleCat.ofHom (z82 R M zs k))
  (fun k=>by
   apply ModuleCat.hom_ext;apply LinearMap.ext;intro x
   exact z83 zs k x)
lemma z98 {R M:Type} [CommRing R] [AddCommGroup M] [Module R M]
  (zs:List R) (k : ℕ) :
  ((z97 R M zs).d (k+1) k).hom=z82 R M zs k:=by
 simp [z97];rfl
lemma z99 {R M:Type} [CommRing R] [AddCommGroup M] [Module R M]
  (zs:List R) (k : ℕ) :
  Nonempty ((z97 R M zs).homology k ≃ₗ[R] z94 R M zs k):=by
 cases k with
 | zero =>
  obtain ⟨e⟩:=z78 (z97 R M zs)
  have hr:LinearMap.range ((z97 R M zs).d 1 0).hom=LinearMap.range (z82 R M zs 0):=by
   rw [z98];rfl
  exact ⟨e.trans (Submodule.quotEquivOfEq _ _ hr)⟩
 | succ i =>
  obtain ⟨e⟩:=z79 (z97 R M zs) i;have hd0:=z98 (R:=R) (M:=M) zs i;have hd1:=z98 (R:=R) (M:=M) zs (i+1)
  have q1:LinearMap.ker ((z97 R M zs).d (i+1) i).hom=LinearMap.ker (z82 R M zs i):=by rw [hd0];rfl
  let q0:LinearMap.ker ((z97 R M zs).d (i+1) i).hom ≃ₗ[R]
    LinearMap.ker (z82 R M zs i):=LinearEquiv.ofEq _ _ q1
  have q2:Submodule.map q0.toLinearMap
    ((LinearMap.range ((z97 R M zs).d (i+2) (i+1)).hom).comap
     (LinearMap.ker ((z97 R M zs).d (i+1) i).hom).subtype) =
    (LinearMap.range (z82 R M zs (i+1))).comap (LinearMap.ker (z82 R M zs i)).subtype:=by
   ext ⟨y,hy⟩;simp only [Submodule.mem_map,Submodule.mem_comap,Submodule.coe_subtype,hd1]
   exact ⟨fun ⟨⟨x,hx⟩,hmem,hxy⟩=>by
     have hxy':x=y:=congrArg Subtype.val hxy
     exact hxy'▸hmem,
    fun hmem=>⟨⟨y,q1.symm▸hy⟩,hmem,rfl⟩⟩
  exact ⟨e.trans (Submodule.Quotient.equiv _ _ q0 q2)⟩
lemma z100 {R M:Type} [CommRing R] [AddCommGroup M] [Module R M] :
  ∀ (zs:List R),
   Submodule.map (z81 R M zs).toLinearMap
    (LinearMap.range (z82 R M zs 0)) =
   ofList zs•(⊤ : Submodule R M)
 | []=>by
  rw [Ideal.ofList_nil,Submodule.bot_smul];ext m;simp [z82,z81]
 | z :: zs=>by
  have ih:=z100 (M:=M) zs;rw [Ideal.ofList_cons,Submodule.sup_smul]
  have q0:span {z}•(⊤ : Submodule R M)=LinearMap.range (z•LinearMap.id (R:=R) (M:=M)):=by
   refine le_antisymm ?_ ?_
   ·
    rw [Submodule.smul_le];intro r hr m _;obtain ⟨a,rfl⟩:=mem_span_singleton.mp hr;exact ⟨a•m,by change z•(a•m)=(z*a)•m;rw [mul_smul]⟩
   ·
    rintro _ ⟨m,rfl⟩;exact Submodule.smul_mem_smul (subset_span rfl) Submodule.mem_top
  rw [q0,← ih];ext m;constructor
  ·
   rintro ⟨_,⟨⟨a,b⟩,rfl⟩,rfl⟩;rw [Submodule.mem_sup]
   refine ⟨z•(z81 R M zs b),⟨z81 R M zs b,rfl⟩,z81 R M zs (z82 R M zs 0 a),⟨z82 R M zs 0 a,⟨a,rfl⟩,rfl⟩,?_⟩
   change z•z81 R M zs b+z81 R M zs (z82 R M zs 0 a)=z81 R M zs (z82 R M zs 0 a+z•b);rw [map_add,map_smul,add_comm]
  ·
   intro hm;rw [Submodule.mem_sup] at hm;obtain ⟨_,⟨m₁,rfl⟩,_,⟨_,⟨a,rfl⟩,rfl⟩,rfl⟩:=hm
   refine ⟨z82 R M (z :: zs) 0 (a,(z81 R M zs).symm m₁),⟨_,rfl⟩,?_⟩
   change z81 R M zs (z82 R M zs 0 a+z•(z81 R M zs).symm m₁)=z•m₁ + z81 R M zs (z82 R M zs 0 a);rw [map_add,map_smul,LinearEquiv.apply_symm_apply,add_comm]
lemma z101 {R M:Type} [CommRing R] [AddCommGroup M] [Module R M] (zs:List R) :
  Nonempty (z94 R M zs 0 ≃ₗ[R] (M⧸(ofList zs•(⊤ : Submodule R M)))) :=
 ⟨Submodule.Quotient.equiv (LinearMap.range (z82 R M zs 0))
  (ofList zs•(⊤ : Submodule R M)) (z81 R M zs) (z100 zs)⟩
lemma z102 {R M:Type} [CommRing R] [AddCommGroup M] [Module R M]
  (zs:List R) (k : ℕ) {a:R} (ha:∀ m:M,a•m=0) (x:z94 R M zs k) :
  a•x=0:=by
 cases k with
 | zero =>
  obtain ⟨u,rfl⟩:=Submodule.Quotient.mk_surjective _ x;change Submodule.Quotient.mk (a•u)=0;rw [z93 ha zs 0 u,Submodule.Quotient.mk_zero]
 | succ i =>
  obtain ⟨⟨u,hu⟩,rfl⟩:=Submodule.Quotient.mk_surjective _ x;have hau:a•u∈LinearMap.ker (z82 R M zs i):=LinearMap.mem_ker.mpr (by rw [map_smul,LinearMap.mem_ker.mp hu,smul_zero]);change Submodule.Quotient.mk (⟨a•u,hau⟩ : LinearMap.ker (z82 R M zs i))=0;have h0:(⟨a•u,hau⟩ : LinearMap.ker (z82 R M zs i))=0:=Subtype.ext (z93 ha zs (i+1) u)
  rw [h0,Submodule.Quotient.mk_zero]
private noncomputable def z103 {R M:Type} [CommRing R] [AddCommGroup M] [Module R M] :
  ∀ (zs:List R) (w:R),w∈zs→∀ k : ℕ,z80 R M zs k →ₗ[R] z80 R M zs (k+1)
 | [],_,hw,_=>absurd hw (List.not_mem_nil)
 | z :: zs,w,hw,k =>
  letI:=Classical.dec (w=z)
  if h:w=z then
   match k with
   | 0=>{ toFun:=fun a=>(0,a),map_add':=fun _ _=>by simp,map_smul':=fun _ _=>by simp }
   | _+1=>{ toFun:=fun p=>(0,p.1),map_add':=fun _ _=>by simp,map_smul':=fun _ _=>by simp }
  else
   have hw':w∈zs:=(List.mem_cons.mp hw).resolve_left h
   match k with
   | 0 =>
    {
     toFun:=fun a=>(z103 (M:=M) zs w hw' 0 a,0)
     map_add':=fun _ _=>by simp [map_add]
     map_smul':=fun _ _=>by simp [map_smul] }
   | i+1 =>
    {
     toFun:=fun p=>(z103 (M:=M) zs w hw' (i+1) p.1,-(z103 (M:=M) zs w hw' i p.2))
     map_add':=fun _ _=>by simp [map_add];abel
     map_smul':=fun _ _=>by simp [map_smul,smul_neg] }
private lemma z104 {R M:Type} [CommRing R] [AddCommGroup M] [Module R M] :
  ∀ (zs:List R) (w:R) (hw:w∈zs) (x:z80 R M zs 0),z82 R M zs 0 (z103 (M:=M) zs w hw 0 x)=w•x
 | [],_,hw,_=>absurd hw List.not_mem_nil
 | z :: zs,w,hw,x=>by
  unfold z103
  split_ifs with h
  ·
   subst h;change z82 R M zs 0 0+w•x=w•x;rw [map_zero,zero_add]
  ·
   have hw':w∈zs:=(List.mem_cons.mp hw).resolve_left h
   change z82 R M zs 0 (z103 (M:=M) zs w hw' 0 x)+z•(0:z80 R M zs 0)=w•x
   rw [smul_zero,add_zero];exact z104 zs w hw' x
private lemma z105 {R M:Type} [CommRing R] [AddCommGroup M] [Module R M] :
  ∀ (zs:List R) (w:R) (hw:w∈zs) (i : ℕ) (x:z80 R M zs (i+1)),
   z82 R M zs (i+1) (z103 (M:=M) zs w hw (i+1) x)+z103 (M:=M) zs w hw i (z82 R M zs i x)=w•x
 | [],_,hw,_,_=>absurd hw List.not_mem_nil
 | z :: zs,w,hw,i,(a,b)=>by
  unfold z103
  split_ifs with h
  ·
   subst h
   cases i with
   | zero =>
    apply Prod.ext
    ·
     change (z82 R M zs 1 0+w•a)+0=w•a;rw [map_zero,zero_add,add_zero]
    ·
     change (-(z82 R M zs 0 a))+(z82 R M zs 0 a+w•b)=w•b;abel
   | succ j =>
    apply Prod.ext
    ·
     change (z82 R M zs (j+2) 0+w•a)+0=w•a;rw [map_zero,zero_add,add_zero]
    ·
     change (-(z82 R M zs (j+1) a))+(z82 R M zs (j+1) a+w•b)=w•b;abel
  ·
   have hw':w∈zs:=(List.mem_cons.mp hw).resolve_left h
   cases i with
   | zero =>
    apply Prod.ext
    ·
     change (z82 R M zs 1 (z103 (M:=M) zs w hw' 1 a)+z•(-(z103 (M:=M) zs w hw' 0 b)))+z103 (M:=M) zs w hw' 0 (z82 R M zs 0 a+z•b)=w•a
     rw [map_add,map_smul,smul_neg];have h1:=z105 zs w hw' 0 a;rw [← h1];abel
    ·
     change (-(z82 R M zs 0 (-(z103 (M:=M) zs w hw' 0 b))))+0=w•b
     rw [map_neg,neg_neg,add_zero];exact z104 zs w hw' b
   | succ j =>
    apply Prod.ext
    ·
     change (z82 R M zs (j+2) (z103 (M:=M) zs w hw' (j+2) a)+z•(-(z103 (M:=M) zs w hw' (j+1) b)))+z103 (M:=M) zs w hw' (j+1) (z82 R M zs (j+1) a+z•b)=w•a
     rw [map_add,map_smul,smul_neg];have h1:=z105 zs w hw' (j+1) a;rw [← h1];abel
    ·
     change (-(z82 R M zs (j+1) (-(z103 (M:=M) zs w hw' (j+1) b))))+(-(z103 (M:=M) zs w hw' j (-(z82 R M zs j b))))=w•b
     rw [map_neg,neg_neg,map_neg,neg_neg];exact z105 zs w hw' j b
lemma z106 {R M:Type} [CommRing R] [AddCommGroup M] [Module R M]
  (zs:List R) (k : ℕ) {w:R} (hw:w∈zs) (x:z94 R M zs k) :
  w•x=0:=by
 cases k with
 | zero =>
  obtain ⟨u,rfl⟩:=Submodule.Quotient.mk_surjective _ x;change Submodule.Quotient.mk (w•u)=0;rw [Submodule.Quotient.mk_eq_zero]
  exact ⟨z103 (M:=M) zs w hw 0 u,z104 zs w hw u⟩
 | succ i =>
  obtain ⟨⟨u,hu⟩,rfl⟩:=Submodule.Quotient.mk_surjective _ x;have hwu:w•u∈LinearMap.ker (z82 R M zs i):=LinearMap.mem_ker.mpr (by rw [map_smul,LinearMap.mem_ker.mp hu,smul_zero]);change Submodule.Quotient.mk (⟨w•u,hwu⟩ : LinearMap.ker (z82 R M zs i))=0;rw [Submodule.Quotient.mk_eq_zero,Submodule.mem_comap,Submodule.coe_subtype]
  refine ⟨z103 (M:=M) zs w hw (i+1) u,?_⟩
  have h1:=z105 zs w hw i u;rw [LinearMap.mem_ker.mp hu,map_zero,add_zero] at h1;exact h1
lemma z107 {R M:Type} [CommRing R] [AddCommGroup M] [Module R M]
  (z:R) (zs:List R) (hz:∀ m:M,z•m=0) :
  Nonempty (z94 R M (z :: zs) 0 ≃ₗ[R] z94 R M zs 0):=by
 have q0:LinearMap.range (z82 R M (z :: zs) 0)=LinearMap.range (z82 R M zs 0):=by
  ext x;constructor
  ·
   rintro ⟨⟨a,b⟩,rfl⟩
   refine ⟨a,?_⟩
   change z82 R M zs 0 a=z82 R M zs 0 a+z•b;rw [z93 hz zs 0 b,add_zero]
  ·
   rintro ⟨a,rfl⟩
   refine ⟨(a,0),?_⟩
   change z82 R M zs 0 a+z•0=z82 R M zs 0 a;rw [smul_zero,add_zero]
 exact ⟨Submodule.quotEquivOfEq _ _ q0⟩
lemma z108 {R M:Type} [CommRing R] [AddCommGroup M] [Module R M]
  (z:R) (zs:List R) (hz:∀ m:M,z•m=0) (i : ℕ) :
  Nonempty (z94 R M (z :: zs) (i+1) ≃ₗ[R] (z94 R M zs (i+1)×z94 R M zs i)):=by
 have hd:∀ (k : ℕ) (a:z80 R M zs (k+2)) (b:z80 R M zs (k+1)),z82 R M (z :: zs) (k+1) (a,b)=(z82 R M zs (k+1) a,-(z82 R M zs k b)):=by
  intro k a b;apply Prod.ext
  ·
   change z82 R M zs (k+1) a+z•b=z82 R M zs (k+1) a;rw [z93 hz zs (k+1) b,add_zero]
  · rfl
 cases i with
 | zero =>
  have q0:∀ p:z80 R M zs 1×z80 R M zs 0,p∈LinearMap.ker (z82 R M (z :: zs) 0)↔p.1∈LinearMap.ker (z82 R M zs 0):=by
   intro ⟨a,b⟩;simp only [LinearMap.mem_ker];change z82 R M zs 0 a+z•b=0↔z82 R M zs 0 a=0;rw [z93 hz zs 0 b,add_zero]
  let Φ : LinearMap.ker (z82 R M (z :: zs) 0) →ₗ[R]
    (z94 R M zs 1×z94 R M zs 0) :=
   {
    toFun:=fun p =>
     (Submodule.Quotient.mk ⟨p.1.1,(q0 p.1).mp p.2⟩,Submodule.Quotient.mk p.1.2)
    map_add':=fun _ _=>rfl
    map_smul':=fun _ _=>rfl }
  have hΦ_surj:Surjective Φ := by
   rintro ⟨x,y⟩;obtain ⟨⟨a,ha⟩,rfl⟩:=Submodule.Quotient.mk_surjective _ x;obtain ⟨b,rfl⟩:=Submodule.Quotient.mk_surjective _ y;exact ⟨⟨(a,b),(q0 (a,b)).mpr ha⟩,rfl⟩
  have hΦ_ker:LinearMap.ker Φ =
    (LinearMap.range (z82 R M (z :: zs) 1)).comap
     (LinearMap.ker (z82 R M (z :: zs) 0)).subtype:=by
   ext ⟨⟨a,b⟩,hab⟩;rw [LinearMap.mem_ker];change (Submodule.Quotient.mk _,Submodule.Quotient.mk _)=0↔_;rw [Prod.mk_eq_zero,Submodule.Quotient.mk_eq_zero,Submodule.Quotient.mk_eq_zero];simp only [Submodule.mem_comap,Submodule.coe_subtype,LinearMap.mem_range];constructor
   ·
    rintro ⟨⟨u,hu⟩,⟨v,hv⟩⟩
    refine ⟨(u,-v),?_⟩
    rw [hd 0 u (-v),map_neg,neg_neg,hu,hv]
   ·
    rintro ⟨⟨u,v⟩,huv⟩;rw [hd 0 u v,Prod.mk.injEq] at huv;exact ⟨⟨u,huv.1⟩,⟨-v,by rw [map_neg,huv.2]⟩⟩
  exact ⟨(Submodule.quotEquivOfEq _ _ hΦ_ker.symm).trans (Φ.quotKerEquivOfSurjective hΦ_surj)⟩
 | succ j =>
  have q0:∀ p:z80 R M zs (j+2)×z80 R M zs (j+1),
    p∈LinearMap.ker (z82 R M (z :: zs) (j+1))↔p.1∈LinearMap.ker (z82 R M zs (j+1))∧p.2∈LinearMap.ker (z82 R M zs j):=by
   intro ⟨a,b⟩;simp only [LinearMap.mem_ker,hd j a b,Prod.mk_eq_zero,neg_eq_zero]
  let Φ : LinearMap.ker (z82 R M (z :: zs) (j+1)) →ₗ[R]
    (z94 R M zs (j+2)×z94 R M zs (j+1)) :=
   {
    toFun:=fun p =>
     (Submodule.Quotient.mk ⟨p.1.1,((q0 p.1).mp p.2).1⟩,Submodule.Quotient.mk ⟨p.1.2,((q0 p.1).mp p.2).2⟩)
    map_add':=fun _ _=>rfl
    map_smul':=fun _ _=>rfl }
  have hΦ_surj:Surjective Φ := by
   rintro ⟨x,y⟩;obtain ⟨⟨a,ha⟩,rfl⟩:=Submodule.Quotient.mk_surjective _ x;obtain ⟨⟨b,hb⟩,rfl⟩:=Submodule.Quotient.mk_surjective _ y;exact ⟨⟨(a,b),(q0 (a,b)).mpr ⟨ha,hb⟩⟩,rfl⟩
  have hΦ_ker:LinearMap.ker Φ =
    (LinearMap.range (z82 R M (z :: zs) (j+2))).comap
     (LinearMap.ker (z82 R M (z :: zs) (j+1))).subtype:=by
   ext ⟨⟨a,b⟩,hab⟩;rw [LinearMap.mem_ker];change (Submodule.Quotient.mk _,Submodule.Quotient.mk _)=0↔_;rw [Prod.mk_eq_zero,Submodule.Quotient.mk_eq_zero,Submodule.Quotient.mk_eq_zero];simp only [Submodule.mem_comap,Submodule.coe_subtype,LinearMap.mem_range];constructor
   ·
    rintro ⟨⟨u,hu⟩,⟨v,hv⟩⟩
    refine ⟨(u,-v),?_⟩
    rw [hd (j+1) u (-v),map_neg,neg_neg,hu,hv]
   ·
    rintro ⟨⟨u,v⟩,huv⟩;rw [hd (j+1) u v,Prod.mk.injEq] at huv;exact ⟨⟨u,huv.1⟩,⟨-v,by rw [map_neg,huv.2]⟩⟩
  exact ⟨(Submodule.quotEquivOfEq _ _ hΦ_ker.symm).trans (Φ.quotKerEquivOfSurjective hΦ_surj)⟩
lemma z109 {R M:Type} [CommRing R] [AddCommGroup M] [Module R M]
  (z:R) (zs:List R) (hz:IsSMulRegular M z) (k : ℕ) :
  Nonempty (z94 R M (z :: zs) k ≃ₗ[R]
   z94 R (M⧸LinearMap.range (z•LinearMap.id (R:=R) (M:=M))) zs k):=by
 let zM:Submodule R M:=LinearMap.range (z•LinearMap.id (R:=R) (M:=M));let Mbar:=M⧸zM;let π : M →ₗ[R] Mbar:=zM.mkQ;have hπ_surj:Surjective π := Submodule.mkQ_surjective zM
 have hπ_ker:∀ (k' : ℕ) (x:z80 R M zs k'),z84 π zs k' x=0↔∃ y:z80 R M zs k',z•y=x:=by
  intro k' x
  have h1:=z88 (R:=R) (i:=z•LinearMap.id (R:=R) (M:=M)) (p := π)
   (Submodule.ker_mkQ zM).symm zs k'
  have h2:z84 (z•LinearMap.id (R:=R) (M:=M)) zs k'=z•LinearMap.id:=by
   clear x h1
   induction zs generalizing k' with
   | nil =>
    cases k' with
    | zero=>rfl
    | succ _=>ext ⟨⟩
   | cons w ws ih =>
    cases k' with
    | zero=>exact ih 0
    | succ j =>
     apply LinearMap.ext;rintro ⟨a,b⟩
     exact Prod.ext (congrFun (congrArg DFunLike.coe (ih (j+1))) a)
      (congrFun (congrArg DFunLike.coe (ih j)) b)
  rw [← LinearMap.mem_ker,← h1,h2];simp [LinearMap.mem_range]
 cases k with
 | zero =>
  let Φ : z80 R M zs 0 →ₗ[R] z94 R Mbar zs 0:=(LinearMap.range (z82 R Mbar zs 0)).mkQ.comp (z84 π zs 0);have hΦ_surj:Surjective Φ := (Submodule.mkQ_surjective _).comp (z87 hπ_surj zs 0)
  have hΦ_ker:LinearMap.ker Φ = LinearMap.range (z82 R M (z :: zs) 0):=by
   ext a;simp only [LinearMap.mem_ker,Φ,LinearMap.comp_apply,Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero,LinearMap.mem_range];constructor
   ·
    rintro ⟨ubar,hubar⟩;obtain ⟨u,rfl⟩:=z87 hπ_surj zs 1 ubar;rw [← z85 π zs 0 u,← sub_eq_zero,← map_sub] at hubar;obtain ⟨b,hb⟩:=(hπ_ker 0 (a - z82 R M zs 0 u)).mp (by rw [← neg_eq_zero,← map_neg,neg_sub];exact hubar)
    refine ⟨(u,b),?_⟩
    change z82 R M zs 0 u+z•b=a;rw [hb];abel
   ·
    rintro ⟨⟨u,b⟩,rfl⟩
    refine ⟨z84 π zs 1 u,?_⟩
    change z82 R Mbar zs 0 (z84 π zs 1 u)=z84 π zs 0 (z82 R M zs 0 u+z•b);rw [map_add,z85 π zs 0 u];have hzb:z84 π zs 0 (z•b)=0:=(hπ_ker 0 (z•b)).mpr ⟨b,rfl⟩;rw [hzb,add_zero]
  exact ⟨(Submodule.quotEquivOfEq _ _ hΦ_ker.symm).trans (Φ.quotKerEquivOfSurjective hΦ_surj)⟩
 | succ i =>
  have q0:∀ p:LinearMap.ker (z82 R M (z :: zs) i),z84 π zs (i+1) p.1.1∈LinearMap.ker (z82 R Mbar zs i):=by
   intro ⟨⟨a,b⟩,hab⟩;rw [LinearMap.mem_ker,← z85 π zs i a]
   have h1:z82 R M zs i a+z•b=0:=by
    cases i with
    | zero=>exact LinearMap.mem_ker.mp hab
    | succ j=>exact congrArg Prod.fst (LinearMap.mem_ker.mp hab)
   have ha:z82 R M zs i a = -(z•b):=eq_neg_of_add_eq_zero_left h1;rw [ha,map_neg,neg_eq_zero];exact (hπ_ker i (z•b)).mpr ⟨b,rfl⟩
  let Φ : LinearMap.ker (z82 R M (z :: zs) i) →ₗ[R] z94 R Mbar zs (i+1) :=
   {
    toFun:=fun p=>Submodule.Quotient.mk ⟨z84 π zs (i+1) p.1.1,q0 p⟩
    map_add':=fun _ _=>by simp [map_add];rfl
    map_smul':=fun _ _=>by simp [map_smul];rfl }
  have hΦ_surj:Surjective Φ := by
   intro x;obtain ⟨⟨abar,habar⟩,rfl⟩:=Submodule.Quotient.mk_surjective _ x;obtain ⟨a,ha⟩:=z87 hπ_surj zs (i+1) abar
   have q4:z84 π zs i (z82 R M zs i a)=0:=by
    rw [z85 π zs i a,ha];exact LinearMap.mem_ker.mp habar
   obtain ⟨b',hb'⟩:=(hπ_ker i (z82 R M zs i a)).mp q4
   have hab:(a,-b')∈LinearMap.ker (z82 R M (z :: zs) i):=by
    rw [LinearMap.mem_ker]
    cases i with
    | zero =>
     change z82 R M zs 0 a+z•(-b')=0;rw [smul_neg,hb',add_neg_cancel]
    | succ j =>
     apply Prod.ext
     ·
      change z82 R M zs (j+1) a+z•(-b')=0;rw [smul_neg,hb',add_neg_cancel]
     ·
      change -(z82 R M zs j (-b'))=0;rw [map_neg,neg_neg];apply z92 hz zs j;dsimp only;rw [smul_zero,← map_smul,hb',z83 zs j a]
   refine ⟨⟨(a,-b'),hab⟩,?_⟩
   change Submodule.Quotient.mk (⟨z84 π zs (i+1) a,q0 ⟨(a,-b'),hab⟩⟩ : LinearMap.ker (z82 R Mbar zs i))=Submodule.Quotient.mk (⟨abar,habar⟩ : LinearMap.ker (z82 R Mbar zs i));congr 1;exact Subtype.ext ha
  have hΦ_ker:LinearMap.ker Φ =
    (LinearMap.range (z82 R M (z :: zs) (i+1))).comap
     (LinearMap.ker (z82 R M (z :: zs) i)).subtype:=by
   ext ⟨⟨a,b⟩,hab⟩;simp only [LinearMap.mem_ker,Φ,LinearMap.coe_mk,AddHom.coe_mk,Submodule.Quotient.mk_eq_zero,Submodule.mem_comap,Submodule.coe_subtype,LinearMap.mem_range];constructor
   ·
    rintro ⟨ubar,hubar⟩;obtain ⟨u,rfl⟩:=z87 hπ_surj zs (i+2) ubar;rw [← z85 π zs (i+1) u] at hubar
    have q3:z84 π zs (i+1) (a - z82 R M zs (i+1) u)=0:=by
     rw [map_sub,hubar,sub_self]
    obtain ⟨v,hv⟩:=(hπ_ker (i+1) (a - z82 R M zs (i+1) u)).mp q3
    have q1:a=z82 R M zs (i+1) u+z•v:=by rw [hv];abel
    have h1:z82 R M zs i a+z•b=0:=by
     cases i with
     | zero=>exact LinearMap.mem_ker.mp hab
     | succ j=>exact congrArg Prod.fst (LinearMap.mem_ker.mp hab)
    have q2 : -(z82 R M zs i v)=b:=by
     apply z92 hz zs i;dsimp only;rw [smul_neg,← map_smul]
     have h2:z82 R M zs i a=z82 R M zs i (z•v):=by
      rw [q1,map_add,z83 zs i u,zero_add]
     rw [← h2];exact (eq_neg_of_add_eq_zero_right h1).symm
    refine ⟨(u,v),?_⟩
    apply Prod.ext
    · exact q1.symm
    · exact q2
   ·
    rintro ⟨⟨u,v⟩,huv⟩;have h1:z82 R M zs (i+1) u+z•v=a:=congrArg Prod.fst huv
    refine ⟨z84 π zs (i+2) u,?_⟩
    rw [← z85 π zs (i+1) u,← h1,map_add];have hzv:z84 π zs (i+1) (z•v)=0:=(hπ_ker (i+1) (z•v)).mpr ⟨v,rfl⟩;rw [hzv,add_zero]
  exact ⟨(Submodule.quotEquivOfEq _ _ hΦ_ker.symm).trans (Φ.quotKerEquivOfSurjective hΦ_surj)⟩
def z110 {R:Type} [CommRing R] :
  (M:Type) → [AddCommGroup M] → [Module R M]→List R→Prop
 | _,_,_,[]=>True
 | M,_,_,z :: zs =>
  IsSMulRegular M z∧z110 (M⧸LinearMap.range (z•LinearMap.id (R:=R) (M:=M))) zs
lemma z111 {R:Type} [CommRing R] :
  ∀ (zs:List R) (M:Type) [AddCommGroup M] [Module R M],z110 M zs→∀ i : ℕ,Subsingleton (z94 R M zs (i+1))
 | [],M,_,_,_,i=>z95 [] (i+1) (by simp)
 | z :: zs,M,_,_,⟨hz,hrest⟩,i=>by
  obtain ⟨e⟩:=z109 z zs hz (i+1);have : Subsingleton (z94 R (M⧸LinearMap.range (z•LinearMap.id (R:=R) (M:=M))) zs (i+1)):=z111 zs _ hrest i;exact e.toEquiv.subsingleton
private def z112 {R M:Type} [CommRing R] [AddCommGroup M] [Module R M] :
  ∀ (zs:List R) (k : ℕ),(M ⊗[R] z80 R R zs k) ≃ₗ[R] z80 R M zs k
 | [],0=>TensorProduct.rid R M
 | [],_+1 =>
  {
   toFun:=fun _=>PUnit.unit
   invFun:=fun _=>0
   map_add':=fun _ _=>rfl
   map_smul':=fun _ _=>rfl
   left_inv:=fun t=>by
    induction t using TensorProduct.induction_on with
    | zero=>rfl
    | tmul m u =>
     have : u=0:=Subsingleton.elim u 0;rw [this,tmul_zero]
    | add t₁ t₂ ih₁ ih₂=>rw [← ih₁,← ih₂,add_zero]
   right_inv:=fun _=>rfl }
 | _ :: zs,0=>z112 zs 0
 | _ :: zs,i+1 =>
  (TensorProduct.prodRight R R M (z80 R R zs (i+1)) (z80 R R zs i)).trans
   (LinearEquiv.prodCongr (z112 zs (i+1)) (z112 zs i))
private lemma z113 {R M:Type} [CommRing R] [AddCommGroup M] [Module R M] :
  ∀ (zs:List R) (k : ℕ) (t:M ⊗[R] z80 R R zs (k+1)),
   z112 (M:=M) zs k (LinearMap.lTensor M (z82 R R zs k) t)=z82 R M zs k (z112 (M:=M) zs (k+1) t)
 | [],0,t=>by
  induction t using TensorProduct.induction_on with
  | zero=>simp [z82]
  | tmul m u=>simp [z82,z112]
  | add t₁ t₂ ih₁ ih₂=>simp [map_add,ih₁,ih₂]
 | [],_+1,_=>rfl
 | z :: zs,0,t=>by
  induction t using TensorProduct.induction_on with
  | zero=>simp
  | tmul m p =>
   rcases p with ⟨a,b⟩
   have ih0:=z113 (M:=M) zs 0 (m ⊗ₜ[R] a);simp only [LinearMap.lTensor_tmul] at ih0 ⊢
   change z112 (M:=M) zs 0 (m ⊗ₜ[R] (z82 R R zs 0 a+z•b)) =
    z82 R M zs 0 (z112 (M:=M) zs 1 (m ⊗ₜ[R] a))+z•z112 (M:=M) zs 0 (m ⊗ₜ[R] b)
   rw [tmul_add,map_add,TensorProduct.tmul_smul,map_smul,ih0]
  | add t₁ t₂ ih₁ ih₂=>simp [map_add,ih₁,ih₂]
 | z :: zs,i+1,t=>by
  induction t using TensorProduct.induction_on with
  | zero=>simp
  | tmul m p =>
   rcases p with ⟨a,b⟩
   have ih1:=z113 (M:=M) zs (i+1) (m ⊗ₜ[R] a);have ih2:=z113 (M:=M) zs i (m ⊗ₜ[R] b);simp only [LinearMap.lTensor_tmul] at ih1 ih2 ⊢;apply Prod.ext
   ·
    change z112 (M:=M) zs (i+1) (m ⊗ₜ[R] (z82 R R zs (i+1) a+z•b)) =
     z82 R M zs (i+1) (z112 (M:=M) zs (i+2) (m ⊗ₜ[R] a))+z•z112 (M:=M) zs (i+1) (m ⊗ₜ[R] b)
    rw [tmul_add,map_add,TensorProduct.tmul_smul,map_smul,ih1]
   ·
    change z112 (M:=M) zs i (m ⊗ₜ[R] (-(z82 R R zs i b))) = -(z82 R M zs i (z112 (M:=M) zs (i+1) (m ⊗ₜ[R] b)))
    rw [tmul_neg,map_neg,ih2]
  | add t₁ t₂ ih₁ ih₂=>simp [map_add,ih₁,ih₂]
lemma z114 {R:Type} [CommRing R]
  (zs:List R) (q3:z110 R zs)
  (M:Type) [AddCommGroup M] [Module R M] (i : ℕ) :
  Nonempty (z56 R M (R⧸ofList zs) i ≃ₗ[R] z94 R M zs i):=by
 let KR:=z97 R R zs;let ε : z80 R R zs 0 →ₗ[R] (R⧸ofList zs):=(ofList zs).mkQ.comp (z81 R R zs).toLinearMap;have hε_surj:Surjective ε := (Submodule.mkQ_surjective _).comp (z81 R R zs).surjective
 have hε_ker:LinearMap.range (z82 R R zs 0)=LinearMap.ker ε := by
  have hr:=z100 (R:=R) (M:=R) zs;rw [smul_eq_mul,mul_top] at hr;ext x;rw [LinearMap.mem_ker];change x∈(z82 R R zs 0).range↔Submodule.Quotient.mk (z81 R R zs x)=0;rw [Submodule.Quotient.mk_eq_zero,← hr,Submodule.mem_map]
  exact ⟨fun hx=>⟨x,hx,rfl⟩,fun ⟨y,hy,hyx⟩=>((z81 R R zs).injective hyx)▸hy⟩
 have q1:∀ k : ℕ,Module.Projective R (KR.X k):=fun k=>z91 zs k
 have hε_comp:∀ x:KR.X 1,ε ((KR.d 1 0).hom x)=0:=fun x=>by
  let x':z80 R R zs 1:=x;change ε (z82 R R zs 0 x')=0;rw [← LinearMap.mem_ker,← hε_ker];exact ⟨x',rfl⟩
 have hε_exact:∀ x:KR.X 0,ε x=0→∃ y:KR.X 1,(KR.d 1 0).hom y=x:=fun x hx=>by
  let x':z80 R R zs 0:=x;have hx' : ε x'=0:=hx;obtain ⟨y,hy⟩:=LinearMap.mem_range.mp (hε_ker.symm▸LinearMap.mem_ker.mpr hx');exact ⟨y,by rw [z98];exact hy⟩
 have q0:∀ n : ℕ,∀ x:KR.X (n+1),(KR.d (n+1) n).hom x=0→∃ y:KR.X (n+2),(KR.d (n+2) (n+1)).hom y=x:=fun n x hx=>by
  let x':z80 R R zs (n+1):=x
  have hx':z82 R R zs n x'=0:=by rw [← z98];exact hx
  have hsub:Subsingleton (z94 R R zs (n+1)):=z111 zs R q3 n;have hq0:(Submodule.Quotient.mk ⟨x',LinearMap.mem_ker.mpr hx'⟩ : z94 R R zs (n+1))=0:=Subsingleton.elim _ 0;rw [Submodule.Quotient.mk_eq_zero,Submodule.mem_comap,Submodule.coe_subtype,LinearMap.mem_range] at hq0;obtain ⟨y,hy⟩:=hq0;exact ⟨y,by rw [z98];exact hy⟩
 let P:ProjectiveResolution (ModuleCat.of R (R⧸ofList zs)):=z62 (R⧸ofList zs) KR q1 ε hε_surj hε_comp hε_exact q0;let F:=(tensoringLeft (ModuleCat.{0} R)).obj (ModuleCat.of R M);let e1:z56 R M (R⧸ofList zs) i ≅ ((F.mapHomologicalComplex _).obj P.complex).homology i:=P.isoLeftDerivedObj F i;have hPK:P.complex=KR:=rfl
 let q2:(F.mapHomologicalComplex _).obj KR ≅ z97 R M zs :=
  HomologicalComplex.Hom.isoOfComponents
   (fun k=>(z112 (R:=R) (M:=M) zs k).toModuleIso)
   (fun k l hkl=>by
    have hk:k=l+1:=by
     change l+1=k at hkl;exact hkl.symm
    subst hk;apply ModuleCat.hom_ext;apply LinearMap.ext;intro t
    change ((z97 R M zs).d (l+1) l).hom (z112 (M:=M) zs (l+1) t)=z112 (M:=M) zs l (LinearMap.lTensor M ((KR.d (l+1) l).hom) t)
    rw [z98,z98]
    exact (z113 (M:=M) zs l t).symm)
 let e2:((F.mapHomologicalComplex _).obj P.complex).homology i ≅ (z97 R M zs).homology i:=(HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ) i).mapIso q2;obtain ⟨e3⟩:=z99 (R:=R) (M:=M) zs i;exact ⟨(e1 ≪≫ e2).toLinearEquiv.trans e3⟩
noncomputable def z115 (R M:Type) [CommRing R] [AddCommGroup M] [Module R M]
  (zs:List R) : ℤ :=
 ∑ i∈Finset.range (zs.length+1),(-1 : ℤ) ^ i*(Module.length R (z94 R M zs i)).toNat
lemma z116 {R A B C:Type} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
  (i:A →ₗ[R] B) (p:B →ₗ[R] C)
  (hi:Injective i) (hp:Surjective p)
  (hip:LinearMap.range i=LinearMap.ker p) (zs:List R) :
  ∃ (f:∀ n,z94 R A zs n →ₗ[R] z94 R B zs n)
   (g:∀ n,z94 R B zs n →ₗ[R] z94 R C zs n)
   (δ : ∀ n,z94 R C zs (n+1) →ₗ[R] z94 R A zs n),
   (∀ n,Function.Exact (δ n) (f n)) ∧
   (∀ n,Function.Exact (f n) (g n)) ∧
   (∀ n,Function.Exact (g (n+1)) (δ n)) ∧
   Surjective (g 0):=by
 let KA:=z97 R A zs;let KB:=z97 R B zs;let KC:=z97 R C zs
 let fi:KA ⟶ KB :=
  {
   f:=fun n=>ModuleCat.ofHom (z84 i zs n)
   comm':=fun k l hkl=>by
    have hk:k=l+1:=by change l+1=k at hkl;exact hkl.symm
    subst hk;apply ModuleCat.hom_ext;apply LinearMap.ext;intro x;change ((KB.d (l+1) l).hom) (z84 i zs (l+1) x)=z84 i zs l (((KA.d (l+1) l).hom) x);rw [z98,z98]
    exact (z85 i zs l x).symm }
 let fp:KB ⟶ KC :=
  {
   f:=fun n=>ModuleCat.ofHom (z84 p zs n)
   comm':=fun k l hkl=>by
    have hk:k=l+1:=by change l+1=k at hkl;exact hkl.symm
    subst hk;apply ModuleCat.hom_ext;apply LinearMap.ext;intro x;change ((KC.d (l+1) l).hom) (z84 p zs (l+1) x)=z84 p zs l (((KB.d (l+1) l).hom) x);rw [z98,z98]
    exact (z85 p zs l x).symm }
 have q4:CategoryStruct.comp fi fp=0:=by
  apply HomologicalComplex.hom_ext;intro n;apply ModuleCat.hom_ext;apply LinearMap.ext;intro x;change z84 p zs n (z84 i zs n x)=0;rw [← LinearMap.mem_ker,← z88 hip zs n];exact ⟨x,rfl⟩
 let S:ShortComplex (ChainComplex (ModuleCat.{0} R) ℕ):=ShortComplex.mk fi fp q4
 have hS:S.ShortExact:=by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact;intro n
  have q3:Mono (S.map (HomologicalComplex.eval _ _ n)).f:=by
   rw [ModuleCat.mono_iff_injective];exact z86 hi zs n
  have q7:Epi (S.map (HomologicalComplex.eval _ _ n)).g:=by
   rw [ModuleCat.epi_iff_surjective];exact z87 hp zs n
  have hex:(S.map (HomologicalComplex.eval _ _ n)).Exact:=by
   rw [ShortComplex.moduleCat_exact_iff];intro x hx;let x':z80 R B zs n:=x;have hx':z84 p zs n x'=0:=hx;obtain ⟨a,ha⟩:=LinearMap.mem_range.mp ((z88 hip zs n).symm▸LinearMap.mem_ker.mpr hx');exact ⟨a,ha⟩
  exact { exact:=hex,mono_f:=q3,epi_g:=q7 }
 let eA (n : ℕ) : KA.homology n ≃ₗ[R] z94 R A zs n:=(z99 (R:=R) (M:=A) zs n).some;let eB (n : ℕ) : KB.homology n ≃ₗ[R] z94 R B zs n:=(z99 (R:=R) (M:=B) zs n).some;let eC (n : ℕ) : KC.homology n ≃ₗ[R] z94 R C zs n:=(z99 (R:=R) (M:=C) zs n).some
 let f (n : ℕ) : z94 R A zs n →ₗ[R] z94 R B zs n:=(eB n).toLinearMap.comp ((HomologicalComplex.homologyMap S.f n).hom.comp (eA n).symm.toLinearMap);let g (n : ℕ) : z94 R B zs n →ₗ[R] z94 R C zs n:=(eC n).toLinearMap.comp ((HomologicalComplex.homologyMap S.g n).hom.comp (eB n).symm.toLinearMap)
 let δ (n : ℕ) : z94 R C zs (n+1) →ₗ[R] z94 R A zs n:=(eA n).toLinearMap.comp ((hS.δ (n+1) n rfl).hom.comp (eC (n+1)).symm.toLinearMap)
 refine ⟨f,g,δ,?_,?_,?_,?_⟩
 ·
  intro n x;have hex:=(ShortComplex.moduleCat_exact_iff _).mp (hS.homology_exact₁ (n+1) n rfl);constructor
  ·
   intro hx;have hx':(HomologicalComplex.homologyMap S.f n).hom ((eA n).symm x)=0:=(eB n).injective (by simpa [f] using hx);obtain ⟨y,hy⟩:=hex ((eA n).symm x) hx';exact ⟨eC (n+1) y,by simp [δ,hy]⟩
  ·
   rintro ⟨z,rfl⟩
   have q6:=congrArg (fun φ : S.X₃.homology (n+1) ⟶ S.X₂.homology n =>
    φ.hom ((eC (n+1)).symm z)) (hS.δ_comp (n+1) n rfl)
   simp only [f,δ,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,LinearEquiv.symm_apply_apply]
   rw [show (HomologicalComplex.homologyMap S.f n).hom ((hS.δ (n+1) n rfl).hom ((eC (n+1)).symm z))=0
    from q6,map_zero]
 ·
  intro n x;have hex:=(ShortComplex.moduleCat_exact_iff _).mp (hS.homology_exact₂ n);constructor
  ·
   intro hx;have hx':(HomologicalComplex.homologyMap S.g n).hom ((eB n).symm x)=0:=(eC n).injective (by simpa [g] using hx);obtain ⟨y,hy⟩:=hex ((eB n).symm x) hx';exact ⟨eA n y,by simp [f,hy]⟩
  ·
   rintro ⟨z,rfl⟩
   have h0:CategoryStruct.comp (HomologicalComplex.homologyMap S.f n)
     (HomologicalComplex.homologyMap S.g n)=0:=by
    rw [← HomologicalComplex.homologyMap_comp,S.zero,HomologicalComplex.homologyMap_zero]
   have q6:=congrArg (fun φ : S.X₁.homology n ⟶ S.X₃.homology n =>
    φ.hom ((eA n).symm z)) h0
   simp only [g,f,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,LinearEquiv.symm_apply_apply]
   rw [show (HomologicalComplex.homologyMap S.g n).hom
     ((HomologicalComplex.homologyMap S.f n).hom ((eA n).symm z))=0 from q6,map_zero]
 ·
  intro n x;have hex:=(ShortComplex.moduleCat_exact_iff _).mp (hS.homology_exact₃ (n+1) n rfl);constructor
  ·
   intro hx;have hx':(hS.δ (n+1) n rfl).hom ((eC (n+1)).symm x)=0:=(eA n).injective (by simpa [δ] using hx);obtain ⟨y,hy⟩:=hex ((eC (n+1)).symm x) hx';exact ⟨eB (n+1) y,by simp [g,hy]⟩
  ·
   rintro ⟨z,rfl⟩
   have q6:=congrArg (fun φ : S.X₂.homology (n+1) ⟶ S.X₁.homology n =>
    φ.hom ((eB (n+1)).symm z)) (hS.comp_δ (n+1) n rfl)
   simp only [δ,g,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,LinearEquiv.symm_apply_apply]
   rw [show (hS.δ (n+1) n rfl).hom
     ((HomologicalComplex.homologyMap S.g (n+1)).hom ((eB (n+1)).symm z))=0 from q6,map_zero]
 ·
  intro c
  have q0:Epi (S.g.f 0):=by
   rw [ModuleCat.epi_iff_surjective];exact z87 hp zs 0
  have q1:Epi (HomologicalComplex.opcyclesMap S.g 0):=epi_of_epi_fac (HomologicalComplex.p_opcyclesMap S.g 0)
  have q2:CategoryStruct.comp (HomologicalComplex.homologyMap S.g 0)
    (ChainComplex.isoHomologyι₀ KC).hom =
    CategoryStruct.comp (ChainComplex.isoHomologyι₀ KB).hom
     (HomologicalComplex.opcyclesMap S.g 0) :=
   HomologicalComplex.homologyι_naturality S.g 0
  have q5:Epi (HomologicalComplex.homologyMap S.g 0):=by
   have h1:=congrArg (fun φ=>CategoryStruct.comp φ (ChainComplex.isoHomologyι₀ KC).inv) q2
   simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id] at h1;rw [h1];exact epi_comp _ _
  obtain ⟨b,hb⟩:=(ModuleCat.epi_iff_surjective _).mp q5 ((eC 0).symm c);exact ⟨eB 0 b,by simp [g,hb]⟩
private lemma z117 {R M N:Type} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (f:M →ₗ[R] N) (hM:IsFiniteLength R M) :
  (Module.length R M).toNat=(Module.length R (LinearMap.ker f)).toNat+(Module.length R (LinearMap.range f)).toNat:=by
 have h1:Module.length R M=Module.length R (LinearMap.ker f)+Module.length R (LinearMap.range f):=by
  have hq:=Module.length_eq_add_of_exact (LinearMap.ker f).subtype (LinearMap.ker f).mkQ
   Subtype.val_injective (Submodule.mkQ_surjective _)
   (LinearMap.exact_iff.mpr (by rw [Submodule.ker_mkQ,Submodule.range_subtype]))
  rw [hq,(f.quotKerEquivRange).length_eq]
 have q2:Module.length R M ≠ ⊤ := Module.length_ne_top_iff.mpr hM;have q1:Module.length R (LinearMap.ker f) ≠ ⊤ := ne_top_of_le_ne_top q2 (Module.length_le_of_injective (LinearMap.ker f).subtype Subtype.val_injective);have q0:Module.length R (LinearMap.range f) ≠ ⊤ := ne_top_of_le_ne_top q2 (Module.length_le_of_surjective f.rangeRestrict (LinearMap.surjective_rangeRestrict f))
 rw [h1,ENat.toNat_add q1 q0]
lemma z118 {R A B C:Type} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
  (i:A →ₗ[R] B) (p:B →ₗ[R] C)
  (hi:Injective i) (hp:Surjective p)
  (hip:LinearMap.range i=LinearMap.ker p) (zs:List R)
  (hA:∀ k,IsFiniteLength R (z94 R A zs k))
  (hB:∀ k,IsFiniteLength R (z94 R B zs k))
  (hC:∀ k,IsFiniteLength R (z94 R C zs k)) :
  z115 R B zs=z115 R A zs+z115 R C zs:=by
 obtain ⟨f,g,δ,h1,h2,h3,hg0⟩:=z116 i p hi hp hip zs;let r (n : ℕ) : ℤ := (Module.length R (LinearMap.range (δ n))).toNat
 have q4:((Module.length R (z94 R B zs 0)).toNat : ℤ) -
   ((Module.length R (z94 R A zs 0)).toNat : ℤ) -
   ((Module.length R (z94 R C zs 0)).toNat : ℤ) = - r 0:=by
  have hA0:=z117 (f 0) (hA 0);have hB0:=z117 (g 0) (hB 0);have hkA:LinearMap.ker (f 0)=LinearMap.range (δ 0):=LinearMap.exact_iff.mp (h1 0);have hkB:LinearMap.ker (g 0)=LinearMap.range (f 0):=LinearMap.exact_iff.mp (h2 0);have hrC:LinearMap.range (g 0) = ⊤ := LinearMap.range_eq_top.mpr hg0;rw [hkA] at hA0;rw [hkB,hrC,Module.length_top] at hB0;dsimp only [r];omega
 have q3:∀ n : ℕ,
   ((Module.length R (z94 R B zs (n+1))).toNat : ℤ) -
    ((Module.length R (z94 R A zs (n+1))).toNat : ℤ) -
    ((Module.length R (z94 R C zs (n+1))).toNat : ℤ) =
   - r (n+1) - r n:=by
  intro n;have hAn:=z117 (f (n+1)) (hA (n+1));have hBn:=z117 (g (n+1)) (hB (n+1));have hCn:=z117 (δ n) (hC (n+1));have hkA:LinearMap.ker (f (n+1))=LinearMap.range (δ (n+1)):=LinearMap.exact_iff.mp (h1 (n+1));have hkB:LinearMap.ker (g (n+1))=LinearMap.range (f (n+1)):=LinearMap.exact_iff.mp (h2 (n+1))
  have hkC:LinearMap.ker (δ n)=LinearMap.range (g (n+1)):=LinearMap.exact_iff.mp (h3 n);rw [hkA] at hAn;rw [hkB] at hBn;rw [hkC] at hCn;dsimp only [r];omega
 have q2:∀ m : ℕ,
   ∑ k∈Finset.range (m+1),
    (-1 : ℤ) ^ k *
     (((Module.length R (z94 R B zs k)).toNat : ℤ) -
      ((Module.length R (z94 R A zs k)).toNat : ℤ) -
      ((Module.length R (z94 R C zs k)).toNat : ℤ)) =
   (-1 : ℤ) ^ (m+1)*r m:=by
  intro m
  induction m with
  | zero =>
   rw [Finset.sum_range_one,pow_zero,one_mul,pow_one,q4];ring
  | succ m ih =>
   rw [Finset.sum_range_succ,ih,q3 m];ring
 have q0:r zs.length=0:=by
  have : Subsingleton (z94 R C zs (zs.length+1)):=z95 zs (zs.length+1) (Nat.lt_succ_self _)
  have : Subsingleton (LinearMap.range (δ zs.length)) :=
   subsingleton_iff_forall_eq 0 |>.mpr fun z=>by
    rcases z with ⟨y,⟨x,rfl⟩⟩
    apply Subtype.ext;change δ zs.length x=0;rw [Subsingleton.elim x 0,map_zero]
  dsimp only [r];rw [Module.length_eq_zero];rfl
 have q5:=q2 zs.length;rw [q0,mul_zero] at q5;unfold z115
 have q1 :
   ∑ k∈Finset.range (zs.length+1),
    (-1 : ℤ) ^ k *
     (((Module.length R (z94 R B zs k)).toNat : ℤ) -
      ((Module.length R (z94 R A zs k)).toNat : ℤ) -
      ((Module.length R (z94 R C zs k)).toNat : ℤ)) =
   (∑ k∈Finset.range (zs.length+1),(-1 : ℤ) ^ k*(Module.length R (z94 R B zs k)).toNat) -
   (∑ k∈Finset.range (zs.length+1),(-1 : ℤ) ^ k*(Module.length R (z94 R A zs k)).toNat) -
   (∑ k∈Finset.range (zs.length+1),(-1 : ℤ) ^ k*(Module.length R (z94 R C zs k)).toNat):=by
  simp only [mul_sub,Finset.sum_sub_distrib]
 linarith
end KoszulComplex
section KoszulPositivity
open IsLocalRing
lemma z119 {A M:Type} [CommRing A]
  [IsLocalRing A] [IsNoetherianRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
  (h:(annihilator A M).radical=maximalIdeal A∨Subsingleton M) :
  IsFiniteLength A M:=by
 rcases h with hrad | q4
 ·
  have hfg:(maximalIdeal A).FG:=IsNoetherian.noetherian (maximalIdeal A)
  have q5:∃ k : ℕ,maximalIdeal A ^ k ≤ annihilator A M:=by
   have hle:maximalIdeal A ≤ (annihilator A M).radical:=hrad.symm.le;exact Ideal.exists_pow_le_of_le_radical_of_fg hle hfg
  obtain ⟨k,hk⟩:=q5
  suffices ∀ (k : ℕ) (N:Type) [AddCommGroup N] [Module A N] [Module.Finite A N],maximalIdeal A ^ k ≤ annihilator A N→IsFiniteLength A N from
   this k M hk
  intro k
  induction k with
  | zero =>
   intro N _ _ _ hN;have h1:(1:A)∈annihilator A N:=hN (by simp)
   have : Subsingleton N:=subsingleton_iff_forall_eq 0 |>.mpr fun x=>by
    have:=Module.mem_annihilator.mp h1 x;simpa using this
   rw [← Module.length_ne_top_iff,Module.length_eq_zero];exact ENat.zero_ne_top
  | succ k ih =>
   intro N _ _ _ hN;let J:Submodule A N:=maximalIdeal A•(⊤ : Submodule A N);have : Module.Finite A J:=Module.Finite.iff_fg.mpr (IsNoetherian.noetherian J)
   have q1:IsFiniteLength A J:=ih J (fun a ha=>by
    rw [Module.mem_annihilator];intro ⟨y,hy⟩;apply Subtype.ext;change a•y=0
    refine Submodule.smul_induction_on hy ?_ ?_
    ·
     intro r hr z _;rw [smul_smul]
     have q6:a*r∈maximalIdeal A ^ (k+1):=by
      rw [pow_succ];exact mul_mem_mul ha hr
     exact Module.mem_annihilator.mp (hN q6) z
    ·
     intro u v hu hv
     rw [smul_add,hu,hv,add_zero])
   let kA:=A⧸maximalIdeal A
   letI : Field kA:=Ideal.Quotient.field (maximalIdeal A)
   have q0:∀ a∈maximalIdeal A,∀ q:N⧸J,a•q=0:=fun a ha q=>by
    obtain ⟨x,rfl⟩:=Submodule.Quotient.mk_surjective J q
    change Submodule.Quotient.mk (p:=J) (a•x)=0
    rw [Submodule.Quotient.mk_eq_zero];exact Submodule.smul_mem_smul ha Submodule.mem_top
   letI : Module kA (N⧸J) :=
    {
     smul:=fun r q=>Quotient.liftOn' r (fun a=>a•q) (fun a b hab=>by
      have q4:b - a∈maximalIdeal A:=by
       simpa [sub_eq_neg_add] using QuotientAddGroup.leftRel_apply.mp hab
      have hba:b=a+(b - a):=by ring
      rw [hba,add_smul,q0 _ q4 q,add_zero])
     one_smul:=fun q=>one_smul A q
     mul_smul:=fun r s q=>Quotient.inductionOn₂' r s fun a b=>mul_smul a b q
     smul_zero:=fun r=>Quotient.inductionOn' r fun a=>smul_zero a
     smul_add:=fun r q₁ q₂=>Quotient.inductionOn' r fun a=>smul_add a q₁ q₂
     add_smul:=fun r s q=>Quotient.inductionOn₂' r s fun a b=>add_smul a b q
     zero_smul:=fun q=>zero_smul A q }
   haveI : IsScalarTower A kA (N⧸J):=⟨fun a r q=>Quotient.inductionOn' r fun b=>mul_smul a b q⟩
   have : Module.Finite kA (N⧸J):=Module.Finite.of_restrictScalars_finite A kA (N⧸J);have q2:Module.length A (N⧸J)=Module.length kA (N⧸J):=Module.length_eq_of_surjective Ideal.Quotient.mk_surjective
   have q3:IsFiniteLength A (N⧸J):=by
    rw [← Module.length_ne_top_iff,q2,Module.length_eq_finrank];exact ENat.coe_ne_top _
   rw [← Module.length_ne_top_iff]
   rw [Module.length_eq_add_of_exact J.subtype J.mkQ Subtype.val_injective
    (Submodule.mkQ_surjective J) (LinearMap.exact_iff.mpr (by rw [Submodule.ker_mkQ,Submodule.range_subtype]))]
   exact WithTop.add_ne_top.mpr ⟨Module.length_ne_top_iff.mpr q1,Module.length_ne_top_iff.mpr q3⟩
 ·
  rw [← Module.length_ne_top_iff,Module.length_eq_zero];exact ENat.zero_ne_top
lemma z120 {A M:Type} [CommRing A] [IsNoetherianRing A]
  [AddCommGroup M] [Module A M] [Module.Finite A M]
  (Pred:∀ (N:Type) [AddCommGroup N] [Module A N],Prop)
  (q8:∀ (N₁ N₂ : Type) [AddCommGroup N₁] [Module A N₁] [AddCommGroup N₂] [Module A N₂],(N₁ ≃ₗ[A] N₂)→Pred N₁ → Pred N₂)
  (q11:∀ (N:Type) [AddCommGroup N] [Module A N],Subsingleton N→Pred N)
  (q7:∀ (P:Ideal A),P.IsPrime→annihilator A M ≤ P→Pred (A⧸P))
  (q12:∀ (N₁ N₂ N₃ : Type) [AddCommGroup N₁] [Module A N₁] [AddCommGroup N₂] [Module A N₂]
   [AddCommGroup N₃] [Module A N₃] (i:N₁ →ₗ[A] N₂) (p:N₂ →ₗ[A] N₃),
   Injective i→Surjective p→LinearMap.range i=LinearMap.ker p →
   Module.Finite A N₁ → Module.Finite A N₂ → Module.Finite A N₃ →
   annihilator A M ≤ annihilator A N₁ →
   annihilator A M ≤ annihilator A N₂ →
   annihilator A M ≤ annihilator A N₃ →
   Pred N₁ → Pred N₃ → Pred N₂) :
  Pred M:=by
 let S:Set (Submodule A M):={ N:Submodule A M | Pred N };have q14:(⊥ : Submodule A M)∈S:=q11 (⊥ : Submodule A M) inferInstance;obtain ⟨N₀,hN₀_mem,hN₀_max⟩:=set_has_maximal_iff_noetherian.mpr (inferInstance:IsNoetherian A M) S ⟨⊥,q14⟩
 by_cases htop:N₀ = ⊤
 ·
  subst htop;exact q8 (⊤ : Submodule A M) M Submodule.topEquiv hN₀_mem
 ·
  have hnt:∃ x:M⧸N₀,x≠0:=by
   by_contra h;push Not at h
   apply htop;rw [eq_top_iff];intro m _;exact (Submodule.Quotient.mk_eq_zero N₀).mp (h (Submodule.Quotient.mk m))
  let elAnn (x:M⧸N₀) : Ideal A :=
   {
    carrier:={ a:A | a•x=0 }
    add_mem':=fun {a b} ha hb=>by simp only [Set.mem_setOf_eq] at ha hb ⊢;rw [add_smul,ha,hb,add_zero]
    zero_mem':=by simp
    smul_mem':=fun r {a} ha=>by simp only [Set.mem_setOf_eq] at ha ⊢;rw [smul_eq_mul,mul_smul,ha,smul_zero] }
  let T:Set (Ideal A):={ I:Ideal A | ∃ x:M⧸N₀,x≠0∧I=elAnn x };obtain ⟨x_init,hx_init⟩:=hnt
  obtain ⟨P,⟨x₀,hx₀_ne,rfl⟩,hP_max⟩ :=
   set_has_maximal_iff_noetherian.mpr (inferInstance:IsNoetherian A A) T
    ⟨elAnn x_init,x_init,hx_init,rfl⟩
  have q1:(elAnn x₀).IsPrime:=by
   refine ⟨?_,?_⟩
   ·
    intro h1;have q13:(1:A)∈elAnn x₀ := h1.symm▸Submodule.mem_top;exact hx₀_ne (by simpa [elAnn] using q13)
   ·
    intro a b hab
    by_contra hnot
    push Not at hnot
    rcases hnot with ⟨ha,hb⟩
    have hbx:b•x₀ ≠ 0:=hb
    have hle:elAnn x₀ ≤ elAnn (b•x₀):=fun r hr=>by
     change r•(b•x₀)=0;rw [smul_comm,hr,smul_zero]
    have heq:elAnn x₀ = elAnn (b•x₀):=eq_of_le_of_not_lt hle (hP_max (elAnn (b•x₀)) ⟨b•x₀,hbx,rfl⟩)
    have q5:a∈elAnn (b•x₀):=by
     change a•(b•x₀)=0;rw [← mul_smul];exact hab
    exact ha (heq▸q5)
  have q2:annihilator A M ≤ elAnn x₀ := fun a ha=>by
   obtain ⟨m,rfl⟩:=Submodule.Quotient.mk_surjective N₀ x₀
   change Submodule.Quotient.mk (p:=N₀) (a•m)=0
   rw [Module.mem_annihilator.mp ha m,Submodule.Quotient.mk_zero]
  have q3:Pred (A⧸elAnn x₀):=q7 (elAnn x₀) q1 q2;obtain ⟨m₀,hm₀⟩:=Submodule.Quotient.mk_surjective N₀ x₀;let N₁ : Submodule A M:=N₀ ⊔ Submodule.span A {m₀}
  have hN₀_lt:N₀ < N₁ := by
   refine lt_of_le_of_ne le_sup_left fun heq=>hx₀_ne ?_
   rw [← hm₀,Submodule.Quotient.mk_eq_zero,heq];exact Submodule.mem_sup_right (Submodule.subset_span rfl)
  let q10:N₀ →ₗ[A] N₁ := Submodule.inclusion le_sup_left;let K:Submodule A N₁ := N₀.comap N₁.subtype
  let ψ : A →ₗ[A] (N₁ ⧸ K) :=
   {
    toFun:=fun a=>Submodule.Quotient.mk
     ⟨a•m₀,Submodule.mem_sup_right (Submodule.smul_mem _ a (Submodule.subset_span rfl))⟩
    map_add':=fun a b=>by
     change Submodule.Quotient.mk _=Submodule.Quotient.mk _+Submodule.Quotient.mk _;rw [← Submodule.Quotient.mk_add];congr 1;apply Subtype.ext;exact add_smul a b m₀
    map_smul':=fun r a=>by
     change Submodule.Quotient.mk _=r•Submodule.Quotient.mk _;rw [← Submodule.Quotient.mk_smul]
     congr 1;apply Subtype.ext;exact mul_smul r a m₀ }
  have hψ_surj:Surjective ψ := fun q=>by
   obtain ⟨⟨y,hy⟩,rfl⟩:=Submodule.Quotient.mk_surjective K q;rw [Submodule.mem_sup] at hy;obtain ⟨n,hn,z,hz,rfl⟩:=hy;rw [Submodule.mem_span_singleton] at hz;obtain ⟨a,rfl⟩:=hz
   refine ⟨a,?_⟩
   change Submodule.Quotient.mk (p:=K) ⟨a•m₀,_⟩=Submodule.Quotient.mk (p:=K) ⟨n+a•m₀,_⟩
   rw [Submodule.Quotient.eq];change a•m₀ - (n+a•m₀)∈N₀
   have : a•m₀ - (n+a•m₀) = -n:=by abel
   rw [this];exact N₀.neg_mem hn
  have hψ_ker:LinearMap.ker ψ = elAnn x₀ := by
   ext a;simp only [LinearMap.mem_ker,ψ,LinearMap.coe_mk,AddHom.coe_mk,Submodule.Quotient.mk_eq_zero,K,Submodule.mem_comap,Submodule.coe_subtype];change a•m₀ ∈ N₀ ↔ a•x₀ = 0;rw [← hm₀]
   change a•m₀ ∈ N₀ ↔ Submodule.Quotient.mk (p:=N₀) (a•m₀)=0
   rw [Submodule.Quotient.mk_eq_zero]
  let eQ:(A⧸elAnn x₀) ≃ₗ[A] (N₁ ⧸ K):=(Submodule.quotEquivOfEq _ _ hψ_ker.symm).trans (ψ.quotKerEquivOfSurjective hψ_surj);have q4:Pred (N₁ ⧸ K):=q8 (A⧸elAnn x₀) (N₁ ⧸ K) eQ q3;have : Module.Finite A N₀ := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian N₀);have : Module.Finite A N₁ := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian N₁)
  have : Module.Finite A (N₁ ⧸ K):=inferInstance
  have hAnn_N₀ : annihilator A M ≤ annihilator A N₀ := fun a ha =>
   Module.mem_annihilator.mpr fun ⟨y,_⟩=>Subtype.ext (Module.mem_annihilator.mp ha y)
  have hAnn_N₁ : annihilator A M ≤ annihilator A N₁ := fun a ha =>
   Module.mem_annihilator.mpr fun ⟨y,_⟩=>Subtype.ext (Module.mem_annihilator.mp ha y)
  have q9:annihilator A M ≤ annihilator A (N₁ ⧸ K):=fun a ha =>
   Module.mem_annihilator.mpr fun q=>by
    obtain ⟨⟨y,hy⟩,rfl⟩:=Submodule.Quotient.mk_surjective K q;have h0:(⟨a•y,N₁.smul_mem a hy⟩ : N₁)=0:=Subtype.ext (Module.mem_annihilator.mp ha y)
    change Submodule.Quotient.mk (p:=K) (⟨a•y,N₁.smul_mem a hy⟩ : N₁)=0
    rw [h0,Submodule.Quotient.mk_zero]
  have q0:Injective q10:=Submodule.inclusion_injective le_sup_left
  have q6:LinearMap.range q10=LinearMap.ker K.mkQ:=by
   rw [Submodule.ker_mkQ];ext ⟨y,hy⟩
   exact ⟨fun ⟨⟨z,hz⟩,h⟩=>by
     have hzy:z=y:=congrArg (fun u:N₁=>(u:M)) h
     exact hzy▸hz,
    fun h=>⟨⟨y,h⟩,rfl⟩⟩
  have hPred_N₁ : Pred N₁ :=
   q12 N₀ N₁ (N₁ ⧸ K) q10 K.mkQ q0 (Submodule.mkQ_surjective K) q6
    inferInstance inferInstance inferInstance hAnn_N₀ hAnn_N₁ q9 hN₀_mem q4
  exact absurd hN₀_lt (hN₀_max N₁ hPred_N₁)
private lemma z121 {R M₁ M₂ M₃ : Type} [CommRing R]
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
  (f:M₁ →ₗ[R] M₂) (g:M₂ →ₗ[R] M₃) :
  ∀ (zs:List R) (k : ℕ) (x:z80 R M₁ zs k),z84 g zs k (z84 f zs k x)=z84 (g.comp f) zs k x
 | [],0,_=>rfl
 | [],_+1,_=>rfl
 | _ :: zs,0,x=>z121 f g zs 0 x
 | _ :: zs,i+1,(a,b)=>Prod.ext (z121 f g zs (i+1) a) (z121 f g zs i b)
private lemma z122 {R M:Type} [CommRing R] [AddCommGroup M] [Module R M] :
  ∀ (zs:List R) (k : ℕ) (x:z80 R M zs k),z84 (LinearMap.id:M →ₗ[R] M) zs k x=x
 | [],0,_=>rfl
 | [],_+1,_=>rfl
 | _ :: zs,0,x=>z122 zs 0 x
 | _ :: zs,i+1,(a,b)=>Prod.ext (z122 zs (i+1) a) (z122 zs i b)
lemma z123 {A:Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] :
  ∀ (zs:List A),(∀ z∈zs,z∈maximalIdeal A) →
  ∀ (M:Type) [AddCommGroup M] [Module A M] [Module.Finite A M],((annihilator A M⊔ofList zs).radical=maximalIdeal A∨Subsingleton M)→(∀ k,IsFiniteLength A (z94 A M zs k))∧(supportDim A M < (zs.length:WithBot ℕ∞)→z115 A M zs=0)∧(supportDim A M=(zs.length:WithBot ℕ∞)→0 < z115 A M zs):=by
 intro zs hzs
 induction zs with
 | nil =>
  intro M _ _ _ hM
  have q59:∀ k,IsFiniteLength A (z94 A M [] k):=fun k=>by
   have : Module.Finite A (z94 A M [] k):=z96 [] k
   refine z119 ?_
   rcases hM with hrad | hsub
   ·
    simp only [Ideal.ofList_nil,sup_bot_eq] at hrad
    by_cases hnt:Subsingleton (z94 A M [] k)
    · exact Or.inr hnt
    ·
     left
     refine le_antisymm ?_ ?_
     ·
      rw [(maximalIdeal.isMaximal A).isPrime.radical_le_iff]
      have hne:annihilator A (z94 A M [] k) ≠ ⊤ := fun h1=>hnt <|
       subsingleton_iff_forall_eq 0 |>.mpr fun x=>by
        simpa using Module.mem_annihilator.mp (h1▸Submodule.mem_top:(1:A)∈_) x
      exact le_maximalIdeal hne
     ·
      rw [← hrad]
      exact Ideal.radical_mono fun a ha =>
       Module.mem_annihilator.mpr (z102 [] k (Module.mem_annihilator.mp ha))
   ·
    right
    cases k with
    | zero=>exact inferInstance
    | succ i=>exact z95 [] (i+1) (by simp)
  refine ⟨q59,?_,?_⟩
  ·
   intro hlt
   have q58:supportDim A M = ⊥ := by
    cases hd:supportDim A M with
    | bot=>rfl
    | coe d =>
     rw [hd] at hlt;simp only [List.length_nil,Nat.cast_zero] at hlt;exact absurd hlt (not_lt.mpr (WithBot.coe_le_coe.mpr (OrderBot.bot_le d)))
   have : Subsingleton M:=(Module.supportDim_eq_bot_iff_subsingleton A M).mp q58;have : Subsingleton (z94 A M [] 0):=inferInstance;unfold z115;simp [Module.length_eq_zero]
  ·
   intro heq;have hnt:Nontrivial M:=(Module.supportDim_ne_bot_iff_nontrivial A M).mp (by rw [heq];simp);obtain ⟨e0⟩:=z101 (R:=A) (M:=M) []
   have q6:ofList ([] : List A)•(⊤ : Submodule A M) = ⊥ := by simp
   let eM:z94 A M [] 0 ≃ₗ[A] M:=e0.trans ((Submodule.quotEquivOfEq _ _ q6).trans (Submodule.quotEquivOfEqBot ⊥ rfl))
   have q17:0 < Module.length A (z94 A M [] 0):=by
    rw [eM.length_eq];exact Module.length_pos
   have q0:Module.length A (z94 A M [] 0) ≠ ⊤ := Module.length_ne_top_iff.mpr (q59 0)
   have q5:0 < (Module.length A (z94 A M [] 0)).toNat:=by
    cases hL:Module.length A (z94 A M [] 0) with
    | top=>exact absurd hL q0
    | coe n =>
     rw [hL] at q17;simpa using q17
   unfold z115;simp only [List.length_nil,zero_add,Finset.sum_range_one,pow_zero,one_mul];exact Int.natCast_pos.mpr q5
 | cons z zs ih =>
  have q34:z∈maximalIdeal A:=hzs z List.mem_cons_self
  have hzs':∀ w∈zs,w∈maximalIdeal A:=fun w hw=>hzs w (List.mem_cons_of_mem z hw)
  intro M _ _ _ hM
  have q24:∀ (N:Type) [AddCommGroup N] [Module A N] [Module.Finite A N],annihilator A M ≤ annihilator A N→∀ k,IsFiniteLength A (z94 A N (z :: zs) k):=fun N _ _ _ hAnn k=>by
   have : Module.Finite A (z94 A N (z :: zs) k):=z96 (z :: zs) k
   refine z119 ?_
   by_cases hsub:Subsingleton (z94 A N (z :: zs) k)
   · exact Or.inr hsub
   ·
    rcases hM with hrad | hMsub
    ·
     left
     refine le_antisymm ?_ ?_
     ·
      rw [(maximalIdeal.isMaximal A).isPrime.radical_le_iff]
      have hne:annihilator A (z94 A N (z :: zs) k) ≠ ⊤ := fun h1=>hsub <|
       subsingleton_iff_forall_eq 0 |>.mpr fun x=>by
        simpa using Module.mem_annihilator.mp (h1▸Submodule.mem_top:(1:A)∈_) x
      exact le_maximalIdeal hne
     ·
      rw [← hrad]
      refine Ideal.radical_mono (sup_le ?_ ?_)
      ·
       intro a ha
       exact Module.mem_annihilator.mpr
        (z102 (z :: zs) k (Module.mem_annihilator.mp (hAnn ha)))
      ·
       rw [ofList,span_le];intro w hw;exact Module.mem_annihilator.mpr (z106 (z :: zs) k hw)
    ·
     right
     have h1:(1:A)∈annihilator A M:=Module.mem_annihilator.mpr fun m=>Subsingleton.elim _ _
     have : Subsingleton N:=subsingleton_iff_forall_eq 0 |>.mpr fun x=>by
      simpa using Module.mem_annihilator.mp (hAnn h1) x
     have h0:∀ x:z94 A N (z :: zs) k,(1:A)•x=0:=z102 (z :: zs) k fun n=>Subsingleton.elim _ _
     exact subsingleton_iff_forall_eq 0 |>.mpr fun x=>by simpa using h0 x
  let Pred (N:Type) [AddCommGroup N] [Module A N] : Prop:=(supportDim A N < ((z :: zs).length:WithBot ℕ∞)→z115 A N (z :: zs)=0)∧(supportDim A N=((z :: zs).length:WithBot ℕ∞)→0 < z115 A N (z :: zs))
  have q46:Pred M:=by
   refine z120 (A:=A) (M:=M) Pred ?_ ?_ ?_ ?_
   ·
    intro N₁ N₂ _ _ _ _ e ⟨h1,h2⟩;have q50:supportDim A N₁ = supportDim A N₂ := Module.supportDim_eq_of_equiv e
    have q54:z115 A N₁ (z :: zs)=z115 A N₂ (z :: zs):=by
     unfold z115
     refine Finset.sum_congr rfl fun k _ => ?_
     congr 2
     let q52:z97 A N₁ (z :: zs) ≅ z97 A N₂ (z :: zs) :=
      HomologicalComplex.Hom.isoOfComponents
       (fun j =>
        {
         hom:=ModuleCat.ofHom (z84 e.toLinearMap (z :: zs) j)
         inv:=ModuleCat.ofHom (z84 e.symm.toLinearMap (z :: zs) j)
         hom_inv_id:=by
          apply ModuleCat.hom_ext;apply LinearMap.ext;intro x;let x':z80 A N₁ (z :: zs) j:=x;change z84 e.symm.toLinearMap (z :: zs) j (z84 e.toLinearMap (z :: zs) j x')=x';rw [z121,LinearEquiv.symm_comp,z122]
         inv_hom_id:=by
          apply ModuleCat.hom_ext;apply LinearMap.ext;intro x;let x':z80 A N₂ (z :: zs) j:=x;change z84 e.toLinearMap (z :: zs) j (z84 e.symm.toLinearMap (z :: zs) j x')=x'
          rw [z121,LinearEquiv.comp_symm,z122] })
       (fun j l hjl=>by
        have hj:j=l+1:=by change l+1=j at hjl;exact hjl.symm
        subst hj;apply ModuleCat.hom_ext;apply LinearMap.ext;intro x;change ((z97 A N₂ (z :: zs)).d (l+1) l).hom (z84 e.toLinearMap (z :: zs) (l+1) x)=z84 e.toLinearMap (z :: zs) l (((z97 A N₁ (z :: zs)).d (l+1) l).hom x);rw [z98,z98]
        exact (z85 e.toLinearMap (z :: zs) l x).symm)
     obtain ⟨eH1⟩:=z99 (R:=A) (M:=N₁) (z :: zs) k;obtain ⟨eH2⟩:=z99 (R:=A) (M:=N₂) (z :: zs) k
     let eH:=eH1.symm.trans (((HomologicalComplex.homologyFunctor (ModuleCat.{0} A)
      (ComplexShape.down ℕ) k).mapIso q52).toLinearEquiv.trans eH2)
     exact congrArg ENat.toNat eH.length_eq
    exact ⟨fun hlt=>q54▸h1 (q50▸hlt),fun heq=>q54▸h2 (q50▸heq)⟩
   ·
    intro N _ _ hsub
    have q45:z115 A N (z :: zs)=0:=by
     unfold z115
     refine Finset.sum_eq_zero fun k _ => ?_
     have : Subsingleton (z94 A N (z :: zs) k) :=
      subsingleton_iff_forall_eq 0 |>.mpr fun x=>by
       have:=z102 (z :: zs) k (a:=(1:A)) (fun n=>Subsingleton.elim _ _) x
       simpa using this
     simp [Module.length_eq_zero]
    exact ⟨fun _=>q45,fun heq=>by
     rw [Module.supportDim_eq_bot_of_subsingleton] at heq
     exact absurd heq WithBot.bot_ne_coe⟩
   ·
    intro P hP hAnnP
    have q38:(P⊔ofList (z :: zs)).radical=maximalIdeal A:=by
     rcases hM with hrad | hMsub
     ·
      refine le_antisymm ?_ ?_
      ·
       rw [(maximalIdeal.isMaximal A).isPrime.radical_le_iff]
       refine sup_le (le_maximalIdeal hP.ne_top) ?_
       rw [ofList,span_le]
       exact fun w hw=>hzs w hw
      ·
       rw [← hrad];exact Ideal.radical_mono (sup_le_sup_right hAnnP _)
     ·
      exfalso
      have h1:(1:A)∈annihilator A M:=Module.mem_annihilator.mpr fun m=>Subsingleton.elim _ _
      exact hP.ne_top (Ideal.eq_top_of_isUnit_mem P (hAnnP h1) isUnit_one)
    have q16:supportDim A (A⧸P)=ringKrullDim (A⧸P):=Module.supportDim_quotient_eq_ringKrullDim P
    by_cases hzP:z∈P
    ·
     have q31:∀ x:A⧸P,z•x=0:=fun x=>by
      obtain ⟨a,rfl⟩:=Ideal.Quotient.mk_surjective x;change Ideal.Quotient.mk P (z*a)=0;rw [Ideal.Quotient.eq_zero_iff_mem];exact P.mul_mem_right a hzP
     have hradP':(P⊔ofList zs).radical=maximalIdeal A:=by
      have q57:P⊔ofList (z :: zs)=P⊔ofList zs:=by
       rw [Ideal.ofList_cons,← sup_assoc,sup_eq_left.mpr (span_le.mpr (Set.singleton_subset_iff.mpr hzP))]
      rwa [← q57]
     have q23:∀ k,IsFiniteLength A (z94 A (A⧸P) zs k):=(ih hzs' (A⧸P) (Or.inl (by rwa [Ideal.annihilator_quotient]))).1
     have q43:z115 A (A⧸P) (z :: zs)=0:=by
      unfold z115;simp only [List.length_cons];rw [Finset.sum_range_succ'];obtain ⟨e0⟩:=z107 (R:=A) (M:=A⧸P) z zs q31
      have q42:∀ i : ℕ,
        (Module.length A (z94 A (A⧸P) (z :: zs) (i+1))).toNat =
         (Module.length A (z94 A (A⧸P) zs (i+1))).toNat+(Module.length A (z94 A (A⧸P) zs i)).toNat:=fun i=>by
       obtain ⟨ei⟩:=z108 (R:=A) (M:=A⧸P) z zs q31 i
       rw [ei.length_eq,Module.length_prod,
        ENat.toNat_add (Module.length_ne_top_iff.mpr (q23 (i+1)))
         (Module.length_ne_top_iff.mpr (q23 i))]
      have q2:∀ m : ℕ,
        (∑ i∈Finset.range (m+1),
         (-1 : ℤ) ^ (i+1) *
          (((Module.length A (z94 A (A⧸P) zs (i+1))).toNat : ℤ)+((Module.length A (z94 A (A⧸P) zs i)).toNat : ℤ))) +
         (-1 : ℤ) ^ 0*((Module.length A (z94 A (A⧸P) zs 0)).toNat : ℤ) =
        (-1 : ℤ) ^ (m+1)*((Module.length A (z94 A (A⧸P) zs (m+1))).toNat : ℤ):=by
       intro m
       induction m with
       | zero=>simp
       | succ m ihm =>
        rw [Finset.sum_range_succ];push_cast at ihm ⊢;ring_nf at ihm ⊢
        linarith
      have q47:(Module.length A (z94 A (A⧸P) (z :: zs) 0)).toNat=(Module.length A (z94 A (A⧸P) zs 0)).toNat:=by rw [e0.length_eq]
      have q30 : ∑ i∈Finset.range (zs.length+1),(-1 : ℤ) ^ (i+1)*(Module.length A (z94 A (A⧸P) (z :: zs) (i+1))).toNat =
        ∑ i∈Finset.range (zs.length+1),
         (-1 : ℤ) ^ (i+1) *
          (((Module.length A (z94 A (A⧸P) zs (i+1))).toNat : ℤ)+((Module.length A (z94 A (A⧸P) zs i)).toNat : ℤ)):=by
       refine Finset.sum_congr rfl fun i _ => ?_
       rw [q42 i,Nat.cast_add]
      rw [q30,q47,q2 zs.length];have : Subsingleton (z94 A (A⧸P) zs (zs.length+1)):=z95 zs (zs.length+1) (Nat.lt_succ_self _);rw [Module.length_eq_zero];simp
     have q20:ringKrullDim (A⧸P) ≤ (zs.length:WithBot ℕ∞):=by
      classical
      let : IsLocalRing (A⧸P):=z36 P;let s:Finset (A⧸P):=(zs.map (Ideal.Quotient.mk P)).toFinset;have q22:s.card ≤ zs.length:=(List.toFinset_card_le _).trans (by rw [List.length_map]);let J:Ideal (A⧸P):=span (s:Set (A⧸P))
      have q39:J=(ofList zs).map (Ideal.Quotient.mk P):=by
       change span (s:Set (A⧸P))=_;rw [ofList,map_span];congr 1;ext y;change y∈(s:Set (A⧸P))↔_;rw [Finset.mem_coe,List.mem_toFinset,List.mem_map,Set.mem_image];rfl
      have q35:(maximalIdeal (A⧸P)).comap (Ideal.Quotient.mk P)=maximalIdeal A:=by
       have : (maximalIdeal (A⧸P)).IsMaximal:=maximalIdeal.isMaximal _;have : ((maximalIdeal (A⧸P)).comap (Ideal.Quotient.mk P)).IsMaximal:=comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective;exact eq_maximalIdeal ‹_›
      have q32:J.radical=maximalIdeal (A⧸P):=by
       rw [q39];ext x;obtain ⟨a,rfl⟩:=Ideal.Quotient.mk_surjective x;change (Ideal.Quotient.mk P a∈((ofList zs).map (Ideal.Quotient.mk P)).radical)↔a∈(maximalIdeal (A⧸P)).comap (Ideal.Quotient.mk P);rw [q35,← hradP'];constructor
       ·
        rintro ⟨k,hk⟩;rw [← map_pow,mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hk;obtain ⟨b,hb,hab⟩:=hk;have q48:a ^ k - b∈P:=Ideal.Quotient.eq.mp hab.symm
        refine ⟨k,?_⟩
        have : a ^ k=(a ^ k - b)+b:=by ring
        rw [this];exact Ideal.add_mem _ (mem_sup_left q48) (mem_sup_right hb)
       ·
        rintro ⟨k,hk⟩;rw [Submodule.mem_sup] at hk;obtain ⟨p,hp,q,hq,ha⟩:=hk
        refine ⟨k,?_⟩
        rw [← map_pow,← ha,map_add,Ideal.Quotient.eq_zero_iff_mem.mpr hp,zero_add];exact mem_map_of_mem _ hq
      have q9:J ≠ ⊤ := fun h=>(maximalIdeal.isMaximal (A⧸P)).ne_top
       (by rw [← q32,h,Ideal.radical_top])
      have q41:ringKrullDim ((A⧸P)⧸J)=0:=by
       have : Nontrivial ((A⧸P)⧸J):=Ideal.Quotient.nontrivial_iff.mpr q9;let : IsLocalRing ((A⧸P)⧸J):=z36 J
       refine le_antisymm ?_ (ringKrullDim_nonneg_of_nontrivial)
       have q33:∀ (q:Ideal ((A⧸P)⧸J)),q.IsPrime→q=maximalIdeal ((A⧸P)⧸J):=fun q hq=>by
        have hle:J ≤ q.comap (Ideal.Quotient.mk J):=by
         intro x hx;rw [mem_comap,Ideal.Quotient.eq_zero_iff_mem.mpr hx];exact q.zero_mem
        have q21:maximalIdeal (A⧸P) ≤ q.comap (Ideal.Quotient.mk J):=by
         rw [← q32];exact (Ideal.IsPrime.radical_le_iff (Ideal.comap_isPrime _ q)).mpr hle
        have q4:q.comap (Ideal.Quotient.mk J)=maximalIdeal (A⧸P):=le_antisymm (le_maximalIdeal (Ideal.comap_isPrime _ q).ne_top) q21;have q44:=Ideal.Quotient.mk_surjective (I:=J)
        have q3:(maximalIdeal ((A⧸P)⧸J)).comap (Ideal.Quotient.mk J)=maximalIdeal (A⧸P):=by
         have : (maximalIdeal ((A⧸P)⧸J)).IsMaximal:=maximalIdeal.isMaximal _;have : ((maximalIdeal ((A⧸P)⧸J)).comap (Ideal.Quotient.mk J)).IsMaximal:=comap_isMaximal_of_surjective _ q44;exact eq_maximalIdeal ‹_›
        exact Ideal.comap_injective_of_surjective _ q44 (q4.trans q3.symm)
       rw [ringKrullDim,Order.krullDim_eq_iSup_length];simp only [WithBot.coe_iSup (OrderTop.bddAbove _),iSup_le_iff];intro c
       have q53:c.length=0:=by
        by_contra hne
        have hlt:c ⟨0,by omega⟩ < c ⟨1,by omega⟩:=c.strictMono (Fin.mk_lt_mk.mpr (by omega));have h0:=q33 (c ⟨0,by omega⟩).asIdeal (c ⟨0,by omega⟩).isPrime;have h1:=q33 (c ⟨1,by omega⟩).asIdeal (c ⟨1,by omega⟩).isPrime;exact hlt.ne (PrimeSpectrum.ext (h0.trans h1.symm))
       simp [q53]
      have hkr:=ringKrullDim_le_ringKrullDim_quotient_add_card (R:=A⧸P) s
       (fun y hy=>by
        rw [IsLocalRing.ringJacobson_eq_maximalIdeal];simp only [s,Finset.mem_coe,List.mem_toFinset,List.mem_map] at hy;obtain ⟨w,hw,rfl⟩:=hy;change w∈(maximalIdeal (A⧸P)).comap (Ideal.Quotient.mk P);rw [q35]
        exact hzs' w hw)
      rw [q41,zero_add] at hkr;exact hkr.trans (WithBot.coe_le_coe.mpr (ENat.natCast_le_natCast.mpr q22))
     refine ⟨fun _=>q43,fun heq => ?_⟩
     exfalso;rw [q16] at heq
     have hlt:ringKrullDim (A⧸P) < ((z :: zs).length:WithBot ℕ∞):=by
      refine lt_of_le_of_lt q20 ?_
      simp only [List.length_cons,Nat.cast_add,Nat.cast_one];exact WithBot.coe_lt_coe.mpr (ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self _))
     exact hlt.ne heq
    ·
     have q28:IsSMulRegular (A⧸P) z:=fun a b hab=>by
      obtain ⟨x,rfl⟩:=Ideal.Quotient.mk_surjective a;obtain ⟨y,rfl⟩:=Ideal.Quotient.mk_surjective b;change Ideal.Quotient.mk P (z*x)=Ideal.Quotient.mk P (z*y) at hab;rw [Ideal.Quotient.eq] at hab ⊢
      have q61:z*(x - y)∈P:=by simpa [mul_sub] using hab
      exact (hP.mem_or_mem q61).resolve_left hzP
     let zAP:Submodule A (A⧸P):=LinearMap.range (z•LinearMap.id (R:=A) (M:=A⧸P));let Qz:=(A⧸P)⧸zAP;let q56:A →ₗ[A] Qz:=zAP.mkQ.comp P.mkQ;have q1:Surjective q56:=(Submodule.mkQ_surjective _).comp (Submodule.mkQ_surjective _)
     have q7:LinearMap.ker q56=P⊔span {z}:=by
      ext a;rw [LinearMap.mem_ker]
      change Submodule.Quotient.mk (p:=zAP) (Ideal.Quotient.mk P a)=0↔a∈P⊔span {z}
      rw [Submodule.Quotient.mk_eq_zero];constructor
      ·
       rintro ⟨q,hq⟩;obtain ⟨b,rfl⟩:=Ideal.Quotient.mk_surjective q;have hq':Ideal.Quotient.mk P (z*b)=Ideal.Quotient.mk P a:=hq;have q48:a - z*b∈P:=Ideal.Quotient.eq.mp hq'.symm
       have : a=(a - z*b)+z*b:=by ring
       rw [this]
       exact Ideal.add_mem _ (mem_sup_left q48)
        (mem_sup_right (Ideal.mul_mem_right b _ (subset_span rfl)))
      ·
       intro ha;rw [Submodule.mem_sup] at ha;obtain ⟨p,hp,r,hr,rfl⟩:=ha;obtain ⟨b,rfl⟩:=mem_span_singleton.mp hr
       refine ⟨Ideal.Quotient.mk P b,?_⟩
       change Ideal.Quotient.mk P (z*b)=Ideal.Quotient.mk P (p+z*b);rw [Ideal.Quotient.eq]
       have : z*b - (p+z*b) = -p:=by ring
       rw [this];exact P.neg_mem hp
     let eQz:(A⧸(P⊔span {z})) ≃ₗ[A] Qz:=(Submodule.quotEquivOfEq _ _ q7.symm).trans (q56.quotKerEquivOfSurjective q1)
     have q36:(annihilator A Qz⊔ofList zs).radical=maximalIdeal A:=by
      have q27:annihilator A Qz=P⊔span {z}:=by
       rw [← Ideal.annihilator_quotient (I:=P⊔span {z})]
       ext a;simp only [Module.mem_annihilator]
       exact ⟨fun h x=>eQz.injective (by rw [map_smul,map_zero];exact h (eQz x)),
        fun h y=>by
         have:=h (eQz.symm y);rw [← map_smul,map_eq_zero_iff eQz.symm eQz.symm.injective] at this
         exact this⟩
      rw [q27,sup_assoc,← Ideal.ofList_cons];exact q38
     have q18:z115 A (A⧸P) (z :: zs)=z115 A Qz zs:=by
      unfold z115;simp only [List.length_cons];rw [Finset.sum_range_succ]
      have q55:(Module.length A (z94 A (A⧸P) (z :: zs) (zs.length+1))).toNat=0:=by
       obtain ⟨e⟩:=z109 z zs q28 (zs.length+1);have : Subsingleton (z94 A Qz zs (zs.length+1)):=z95 zs (zs.length+1) (Nat.lt_succ_self _);rw [e.length_eq,Module.length_eq_zero];rfl
      rw [q55,Nat.cast_zero,mul_zero,add_zero]
      refine Finset.sum_congr rfl fun k _ => ?_
      obtain ⟨ek⟩:=z109 z zs q28 k;rw [ek.length_eq]
     have q25:supportDim A Qz+1=supportDim A (A⧸P):=by
      rw [← Module.supportDim_eq_of_equiv eQz,Module.supportDim_quotient_eq_ringKrullDim,q16];let : IsLocalRing (A⧸P):=z36 P;have q10:IsSMulRegular (A⧸P) (Ideal.Quotient.mk P z):=q28
      have q11:Ideal.Quotient.mk P z∈maximalIdeal (A⧸P):=by
       have q35:(maximalIdeal (A⧸P)).comap (Ideal.Quotient.mk P)=maximalIdeal A:=by
        have : (maximalIdeal (A⧸P)).IsMaximal:=maximalIdeal.isMaximal _;have : ((maximalIdeal (A⧸P)).comap (Ideal.Quotient.mk P)).IsMaximal:=comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective;exact eq_maximalIdeal ‹_›
       rw [← mem_comap,q35];exact q34
      have q14:ringKrullDim ((A⧸P)⧸span {Ideal.Quotient.mk P z})+1 =
        ringKrullDim (A⧸P) :=
       ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim q10 q11
      let mkD:A →+* ((A⧸P)⧸span {Ideal.Quotient.mk P z}):=(Ideal.Quotient.mk _).comp (Ideal.Quotient.mk P);have q8:Surjective mkD:=Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
      have q12:RingHom.ker mkD=P⊔span {z}:=by
       ext a;simp only [mkD,RingHom.mem_ker,RingHom.comp_apply,Ideal.Quotient.eq_zero_iff_mem,mem_span_singleton];constructor
       ·
        rintro ⟨q,hq⟩;obtain ⟨b,rfl⟩:=Ideal.Quotient.mk_surjective q;have q48:a - z*b∈P:=Ideal.Quotient.eq.mp hq
        have : a=(a - z*b)+z*b:=by ring
        rw [this]
        exact Ideal.add_mem _ (mem_sup_left q48)
         (mem_sup_right (Ideal.mul_mem_right b _ (subset_span rfl)))
       ·
        intro ha;rw [Submodule.mem_sup] at ha;obtain ⟨p,hp,r,hr,rfl⟩:=ha;obtain ⟨b,rfl⟩:=mem_span_singleton.mp hr
        refine ⟨Ideal.Quotient.mk P b,?_⟩
        change Ideal.Quotient.mk P (p+z*b)=Ideal.Quotient.mk P (z*b);rw [Ideal.Quotient.eq]
        have : p+z*b - z*b=p:=by ring
        rw [this];exact hp
      let q37:(A⧸(P⊔span {z})) ≃+* ((A⧸P)⧸span {Ideal.Quotient.mk P z}):=(Ideal.quotEquivOfEq q12.symm).trans (RingHom.quotientKerEquivOfSurjective q8);rw [RingEquiv.ringKrullDim q37,q14]
     obtain ⟨_,ih_lt,ih_eq⟩:=ih hzs' Qz (Or.inl q36);dsimp only [Pred];rw [q18]
     refine ⟨fun hlt=>ih_lt ?_,fun heq=>ih_eq ?_⟩
     ·
      rw [← q25,List.length_cons,Nat.cast_add,Nat.cast_one] at hlt
      cases hd:supportDim A Qz with
      | bot=>simp
      | coe d =>
       rw [hd] at hlt
       cases d with
       | top =>
        exfalso
        have q55:(↑(⊤ : ℕ∞) : WithBot ℕ∞)+1=(⊤ : WithBot ℕ∞):=by
         change (↑((⊤ : ℕ∞)+1) : WithBot ℕ∞)=↑(⊤ : ℕ∞);simp
        rw [q55] at hlt;exact not_lt.mpr le_top hlt
       | coe m =>
        have hm:(↑(m : ℕ∞) : WithBot ℕ∞)+1=((m+1 : ℕ) : WithBot ℕ∞):=by push_cast;rfl
        have hz:((zs.length : ℕ) : WithBot ℕ∞)+1=((zs.length+1 : ℕ) : WithBot ℕ∞):=by push_cast;rfl
        rw [hm,hz] at hlt
        have hlt':m+1 < zs.length+1:=by exact_mod_cast hlt
        have hlt'':m < zs.length:=by omega
        exact_mod_cast hlt''
     ·
      rw [← q25,List.length_cons,Nat.cast_add,Nat.cast_one] at heq
      cases hd:supportDim A Qz with
      | bot =>
       exfalso
       have hz:((zs.length : ℕ) : WithBot ℕ∞)+1=((zs.length+1 : ℕ) : WithBot ℕ∞):=by push_cast;rfl
       rw [hd,WithBot.bot_add,hz] at heq;exact WithBot.bot_ne_coe heq
      | coe d =>
       rw [hd] at heq
       cases d with
       | top =>
        exfalso
        have hz:((zs.length : ℕ) : WithBot ℕ∞)+1=((zs.length+1 : ℕ) : WithBot ℕ∞):=by push_cast;rfl
        have q55:(↑(⊤ : ℕ∞) : WithBot ℕ∞)+1=(↑(⊤ : ℕ∞) : WithBot ℕ∞):=by
         change (↑((⊤ : ℕ∞)+1) : WithBot ℕ∞)=↑(⊤ : ℕ∞);simp
        rw [q55,hz] at heq;exact ENat.natCast_ne_top _ (WithBot.coe_inj.mp heq).symm
       | coe m =>
        have hm:(↑(m : ℕ∞) : WithBot ℕ∞)+1=((m+1 : ℕ) : WithBot ℕ∞):=by push_cast;rfl
        have hz:((zs.length : ℕ) : WithBot ℕ∞)+1=((zs.length+1 : ℕ) : WithBot ℕ∞):=by push_cast;rfl
        rw [hm,hz] at heq
        have heq':m+1=zs.length+1:=by exact_mod_cast heq
        have heq'':m=zs.length:=by omega
        exact_mod_cast heq''
   ·
    intro N₁ N₂ N₃ _ _ _ _ _ _ fi fp hfi hfp hker _ _ _ hAnn1 hAnn2 hAnn3 ⟨h1_lt,h1_eq⟩ ⟨h3_lt,h3_eq⟩;have q54:z115 A N₂ (z :: zs)=z115 A N₁ (z :: zs)+z115 A N₃ (z :: zs):=z118 fi fp hfi hfp hker (z :: zs) (q24 N₁ hAnn1) (q24 N₂ hAnn2) (q24 N₃ hAnn3);have q40:supportDim A N₁ ≤ supportDim A N₂ := Module.supportDim_le_of_injective fi hfi
    have q49:supportDim A N₃ ≤ supportDim A N₂ := Module.supportDim_le_of_surjective fp hfp
    have q13:supportDim A N₂ ≤ max (supportDim A N₁) (supportDim A N₃):=by
     by_cases hsub2:Subsingleton N₂
     · rw [Module.supportDim_eq_bot_of_subsingleton];exact bot_le
     ·
      have hnt2:Nontrivial N₂ := not_subsingleton_iff_nontrivial.mp hsub2
      have q15:annihilator A N₂ ≠ ⊤ := fun h1=>hsub2 <|
       subsingleton_iff_forall_eq 0 |>.mpr fun y=>by
        simpa using Module.mem_annihilator.mp (h1▸Submodule.mem_top:(1:A)∈_) y
      haveI : Nonempty (PrimeSpectrum.zeroLocus (annihilator A N₂ : Set A)) :=
       ⟨⟨⟨maximalIdeal A,(maximalIdeal.isMaximal A).isPrime⟩,by
        rw [PrimeSpectrum.mem_zeroLocus]
        exact le_maximalIdeal q15⟩⟩
      have q26:annihilator A N₁ * annihilator A N₃ ≤ annihilator A N₂ := by
       rw [Ideal.mul_le];intro a ha b hb;rw [Module.mem_annihilator];intro y
       have hpy:fp (b•y)=0:=by
        rw [map_smul];exact Module.mem_annihilator.mp hb (fp y)
       obtain ⟨x,hx⟩:=LinearMap.mem_range.mp (hker.symm▸LinearMap.mem_ker.mpr hpy);rw [mul_smul,← hx,← map_smul,Module.mem_annihilator.mp ha x,map_zero]
      rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator,Module.supportDim_eq_ringKrullDim_quotient_annihilator,Module.supportDim_eq_ringKrullDim_quotient_annihilator,
       ringKrullDim_quotient,ringKrullDim_quotient,ringKrullDim_quotient]
      rw [Order.krullDim_eq_iSup_length];simp only [WithBot.coe_iSup (OrderTop.bddAbove _),iSup_le_iff];intro c
      have q29:annihilator A N₂ ≤ (c 0).1.asIdeal:=by
       have:=(c 0).2;rwa [PrimeSpectrum.mem_zeroLocus] at this
      have hor:annihilator A N₁ ≤ (c 0).1.asIdeal∨annihilator A N₃ ≤ (c 0).1.asIdeal:=(c 0).1.isPrime.mul_le.mp (q26.trans q29)
      rcases hor with h1 | h3
      ·
       refine le_trans ?_ (le_max_left _ _)
       let c1:LTSeries (PrimeSpectrum.zeroLocus (annihilator A N₁ : Set A)) :=
        {
         length:=c.length
         toFun:=fun j=>⟨(c j).1,by
          rw [PrimeSpectrum.mem_zeroLocus]
          exact h1.trans (c.monotone (Fin.zero_le j))⟩
         step:=fun j=>c.step j }
       haveI : Nonempty (PrimeSpectrum.zeroLocus (annihilator A N₁ : Set A)):=⟨c1 0⟩
       rw [Order.krullDim_eq_iSup_length]
       exact WithBot.coe_le_coe.mpr (le_iSup (fun s:LTSeries _=>(s.length : ℕ∞)) c1)
      ·
       refine le_trans ?_ (le_max_right _ _)
       let c3:LTSeries (PrimeSpectrum.zeroLocus (annihilator A N₃ : Set A)) :=
        {
         length:=c.length
         toFun:=fun j=>⟨(c j).1,by
          rw [PrimeSpectrum.mem_zeroLocus]
          exact h3.trans (c.monotone (Fin.zero_le j))⟩
         step:=fun j=>c.step j }
       haveI : Nonempty (PrimeSpectrum.zeroLocus (annihilator A N₃ : Set A)):=⟨c3 0⟩
       rw [Order.krullDim_eq_iSup_length]
       exact WithBot.coe_le_coe.mpr (le_iSup (fun s:LTSeries _=>(s.length : ℕ∞)) c3)
    refine ⟨fun hlt => ?_,fun heq => ?_⟩
    · rw [q54,h1_lt (lt_of_le_of_lt q40 hlt),h3_lt (lt_of_le_of_lt q49 hlt),add_zero]
    ·
     rw [q54];have q60:supportDim A N₁ ≤ ((z :: zs).length:WithBot ℕ∞):=heq▸q40;have q51:supportDim A N₃ ≤ ((z :: zs).length:WithBot ℕ∞):=heq▸q49
     rcases q60.eq_or_lt with h1e | h1l
     ·
      rcases q51.eq_or_lt with h3e | h3l
      · linarith [h1_eq h1e,h3_eq h3e]
      · rw [h3_lt h3l,add_zero];exact h1_eq h1e
     ·
      rcases q51.eq_or_lt with h3e | h3l
      · rw [h1_lt h1l,zero_add];exact h3_eq h3e
      ·
       exfalso;have q19:max (supportDim A N₁) (supportDim A N₃) < ((z :: zs).length:WithBot ℕ∞):=max_lt h1l h3l;exact (lt_of_le_of_lt q13 q19).ne heq
  exact ⟨q24 M le_rfl,q46.1,q46.2⟩
end KoszulPositivity
section DiagonalTorAndPositivity
noncomputable def z124 (D:Type) [CommRing D] : (n : ℕ)→List (z0 D n)
 | 0=>[]
 | n+1=>PowerSeries.X :: (z124 D n).map PowerSeries.C
lemma z125 (D:Type) [CommRing D] :
  ∀ n : ℕ,(z124 D n).length=n
 | 0=>rfl
 | n+1=>by simp [z124,z125 D n]
lemma z126 (D:Type) [CommRing D] :
  ∀ n : ℕ,ofList (z124 D n)=span (Set.range (z14 D (n:=n)))
 | 0=>by
  simp [z124,ofList,Set.range_eq_empty]
 | n+1=>by
  rw [z124,Ideal.ofList_cons]
  have q0:ofList ((z124 D n).map PowerSeries.C)=(ofList (z124 D n)).map PowerSeries.C:=by
   rw [ofList,ofList,map_span];congr 1;ext y;simp
  rw [q0,z126 D n,map_span]
  refine le_antisymm (sup_le ?_ ?_) ?_
  ·
   rw [span_singleton_le_iff_mem];exact subset_span ⟨Fin.last n,by simp [z14]⟩
  ·
   rw [span_le];rintro _ ⟨_,⟨j,rfl⟩,rfl⟩;exact subset_span ⟨j.castSucc,by simp [z14]⟩
  ·
   rw [span_le];rintro _ ⟨i,rfl⟩
   refine Fin.lastCases ?_ ?_ i
   · exact mem_sup_left (by simp [z14])
   ·
    intro j;exact mem_sup_right (subset_span ⟨z14 D j,⟨j,rfl⟩,by simp [z14]⟩)
lemma z127 (D:Type) [CommRing D] [IsLocalRing D] :
  ∀ (n : ℕ) (z:z0 D n),z∈z124 D n→z∈maximalIdeal (z0 D n)
 | 0,_,hz=>absurd hz List.not_mem_nil
 | n+1,z,hz=>by
  rw [z124,List.mem_cons] at hz
  rcases hz with rfl | hz'
  · exact z4
  ·
   rw [List.mem_map] at hz';obtain ⟨w,hw,rfl⟩:=hz';rw [z3,PowerSeries.constantCoeff_C];exact z127 D n w hw
lemma z128 {R S:Type} [CommRing R] [CommRing S] (eR:R ≃+* S) :
  ∀ (zs:List R) {M' N':Type} [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module S N']
   (eM:M' ≃+ N'),(∀ (r:R) (x:M'),eM (r•x)=eR r•eM x) →
   z110 M' zs→z110 N' (zs.map eR)
 | [],_,_,_,_,_,_,_,_,_=>trivial
 | z :: zs,M',N',_,_,_,_,eM,hsmul,⟨hz,hrest⟩=>by
  have q0:∀ (s:S) (y:N'),eM.symm (s•y)=eR.symm s•eM.symm y:=fun s y=>by
   apply eM.injective;rw [eM.apply_symm_apply,hsmul,eR.apply_symm_apply,eM.apply_symm_apply]
  have hzN:IsSMulRegular N' (eR z):=fun y₁ y₂ hy=>by
   apply eM.symm.injective;apply hz;have h1:eM.symm (eR z•y₁)=eM.symm (eR z•y₂):=congrArg eM.symm hy;rw [q0,q0,eR.symm_apply_apply] at h1;exact h1
  refine ⟨hzN,?_⟩
  let zM:Submodule R M':=LinearMap.range (z•LinearMap.id (R:=R) (M:=M'));let zN:Submodule S N':=LinearMap.range (eR z•LinearMap.id (R:=S) (M:=N'))
  have q2:∀ x:M',x∈zM↔eM x∈zN:=fun x=>by
   simp only [zM,zN,LinearMap.mem_range,LinearMap.smul_apply,LinearMap.id_apply];constructor
   ·
    rintro ⟨a,rfl⟩;exact ⟨eM a,(hsmul z a).symm⟩
   ·
    rintro ⟨b,hb⟩
    refine ⟨eM.symm b,eM.injective ?_⟩
    rw [hsmul z (eM.symm b),eM.apply_symm_apply,hb]
  let eQ:(M'⧸zM) ≃+ (N'⧸zN) :=
   {
    toFun:=QuotientAddGroup.lift zM.toAddSubgroup
     ((QuotientAddGroup.mk' zN.toAddSubgroup).comp eM.toAddMonoidHom) (fun x hx=>by
      rw [AddMonoidHom.mem_ker,AddMonoidHom.comp_apply,QuotientAddGroup.mk'_apply,QuotientAddGroup.eq_zero_iff]
      exact (q2 x).mp hx)
    invFun:=QuotientAddGroup.lift zN.toAddSubgroup
     ((QuotientAddGroup.mk' zM.toAddSubgroup).comp eM.symm.toAddMonoidHom) (fun y hy=>by
      rw [AddMonoidHom.mem_ker,AddMonoidHom.comp_apply,QuotientAddGroup.mk'_apply,QuotientAddGroup.eq_zero_iff];change eM.symm y∈zM;rw [q2,eM.apply_symm_apply]
      exact hy)
    map_add':=fun a b=>by
     obtain ⟨x,rfl⟩:=Submodule.Quotient.mk_surjective zM a;obtain ⟨y,rfl⟩:=Submodule.Quotient.mk_surjective zM b;change Submodule.Quotient.mk (eM (x+y))=Submodule.Quotient.mk (eM x)+Submodule.Quotient.mk (eM y);rw [map_add,Submodule.Quotient.mk_add]
    left_inv:=fun a=>by
     obtain ⟨x,rfl⟩:=Submodule.Quotient.mk_surjective zM a;change Submodule.Quotient.mk (eM.symm (eM x))=Submodule.Quotient.mk x;rw [eM.symm_apply_apply]
    right_inv:=fun b=>by
     obtain ⟨y,rfl⟩:=Submodule.Quotient.mk_surjective zN b;change Submodule.Quotient.mk (eM (eM.symm y))=Submodule.Quotient.mk y
     rw [eM.apply_symm_apply] }
  have q1:∀ (r:R) (a:M'⧸zM),eQ (r•a)=eR r•eQ a:=fun r a=>by
   obtain ⟨x,rfl⟩:=Submodule.Quotient.mk_surjective zM a;change Submodule.Quotient.mk (eM (r•x))=eR r•Submodule.Quotient.mk (eM x);rw [hsmul,Submodule.Quotient.mk_smul]
  exact z128 eR zs eQ q1 hrest
lemma z129 {A B:Type} [CommRing A] [CommRing B]
  (e:A ≃+* B) (zs:List A) (h:z110 A zs) :
  z110 B (zs.map e) :=
 z128 e zs e.toAddEquiv (fun r x=>e.map_mul r x) h
lemma z130 {T S:Type} [CommRing T] [CommRing S] [Algebra T S] :
  ∀ (zs:List T) (M:Type) [AddCommGroup M] [Module T M] [Module S M] [IsScalarTower T S M],z110 (R:=S) M (zs.map (algebraMap T S))→z110 (R:=T) M zs
 | [],_,_,_,_,_,_=>trivial
 | z :: zs,M,_,_,_,_,⟨hz,hrest⟩=>by
  have hzT:IsSMulRegular M z:=fun x y hxy =>
   hz (by simpa [algebraMap_smul] using hxy)
  refine ⟨hzT,?_⟩
  let zMT:Submodule T M:=LinearMap.range (z•LinearMap.id (R:=T) (M:=M));let zMS:Submodule S M:=LinearMap.range ((algebraMap T S z)•LinearMap.id (R:=S) (M:=M))
  have q0:(zMT:Set M)=(zMS:Set M):=by
   ext m;simp only [SetLike.mem_coe,zMT,zMS,LinearMap.mem_range,LinearMap.smul_apply,LinearMap.id_apply,algebraMap_smul]
  let eQ:(M⧸zMS) ≃+ (M⧸zMT) :=
   {
    toFun:=QuotientAddGroup.lift zMS.toAddSubgroup (QuotientAddGroup.mk' zMT.toAddSubgroup) (fun x hx=>by
     rw [AddMonoidHom.mem_ker,QuotientAddGroup.mk'_apply,QuotientAddGroup.eq_zero_iff]
     change x∈(zMT:Set M);rw [q0];exact hx)
    invFun:=QuotientAddGroup.lift zMT.toAddSubgroup (QuotientAddGroup.mk' zMS.toAddSubgroup) (fun x hx=>by
     rw [AddMonoidHom.mem_ker,QuotientAddGroup.mk'_apply,QuotientAddGroup.eq_zero_iff]
     change x∈(zMS:Set M);rw [← q0];exact hx)
    map_add':=fun a b=>by
     obtain ⟨x,rfl⟩:=Submodule.Quotient.mk_surjective zMS a;obtain ⟨y,rfl⟩:=Submodule.Quotient.mk_surjective zMS b;rfl
    left_inv:=fun a=>by
     obtain ⟨x,rfl⟩:=Submodule.Quotient.mk_surjective zMS a;rfl
    right_inv:=fun b=>by
     obtain ⟨x,rfl⟩:=Submodule.Quotient.mk_surjective zMT b;rfl }
  have q1:∀ (t:T) (a:M⧸zMS),eQ (t•a)=t•eQ a:=fun t a=>by
   obtain ⟨x,rfl⟩:=Submodule.Quotient.mk_surjective zMS a
   change Submodule.Quotient.mk (p:=zMT) (t•x)=t•Submodule.Quotient.mk (p:=zMT) x
   rfl
  have q2:z110 (R:=T) (M⧸zMS) zs:=z130 zs (M⧸zMS) hrest;simpa [List.map_id] using z128 (RingEquiv.refl T) zs eQ q1 q2
lemma z131 (D:Type) [CommRing D] :
  ∀ n : ℕ,z110 (z0 D n) (z124 D n)
 | 0=>trivial
 | n+1=>by
  let S:=z0 D n;let PS:=PowerSeries S
  have q3:IsSMulRegular PS (PowerSeries.X:PS):=fun a b hab=>by
   ext k;have hk:=congrArg (PowerSeries.coeff (k+1)) hab;simpa [smul_eq_mul,PowerSeries.coeff_succ_X_mul] using hk
  refine ⟨q3,?_⟩
  let : Algebra PS S:=PowerSeries.constantCoeff.toAlgebra
  let cc:PS →ₗ[PS] S :=
   {
    toFun:=PowerSeries.constantCoeff
    map_add':=map_add _
    map_smul':=fun f g=>map_mul PowerSeries.constantCoeff f g }
  have q0:Surjective cc:=PowerSeries.constantCoeff_surj
  have q1:LinearMap.ker cc=LinearMap.range ((PowerSeries.X:PS)•LinearMap.id):=by
   ext f;simp only [LinearMap.mem_ker,cc,LinearMap.coe_mk,AddHom.coe_mk,LinearMap.mem_range,LinearMap.smul_apply,LinearMap.id_apply,smul_eq_mul];constructor
   ·
    intro hf
    have h1:=z6 1 f fun i hi=>by
     have hi0:i=0:=by omega
     subst hi0;simpa using hf
    obtain ⟨q,hq⟩:=mem_span_singleton.mp (by simpa using h1);exact ⟨q,hq.symm⟩
   ·
    rintro ⟨q,rfl⟩;rw [map_mul,PowerSeries.constantCoeff_X,zero_mul]
  let eQ:(PS⧸LinearMap.range ((PowerSeries.X:PS)•LinearMap.id)) ≃ₗ[PS] S:=(Submodule.quotEquivOfEq _ _ q1.symm).trans (cc.quotKerEquivOfSurjective q0)
  have q2:((z124 D n).map PowerSeries.C).map (algebraMap PS S)=z124 D n:=by
   rw [List.map_map]
   have q5:(algebraMap PS S)∘PowerSeries.C=id:=by
    ext a;exact PowerSeries.constantCoeff_C a
   rw [q5,List.map_id]
  have : IsScalarTower PS S S:=IsScalarTower.right
  have q4:z110 (R:=PS) S ((z124 D n).map PowerSeries.C) :=
   z130 ((z124 D n).map PowerSeries.C) S
    (q2.symm▸z131 D n)
  simpa [List.map_id] using z128 (RingEquiv.refl PS)
   ((z124 D n).map PowerSeries.C) eQ.symm.toAddEquiv (fun r x=>eQ.symm.map_smul r x) q4
private def z132 {T S M:Type} [CommRing T] [CommRing S] [Algebra T S]
  [AddCommGroup M] [Module T M] [Module S M] [IsScalarTower T S M] :
  ∀ (zs:List T) (k : ℕ),z80 T M zs k ≃+ z80 S M (zs.map (algebraMap T S)) k
 | [],0=>AddEquiv.refl M
 | [],_+1=>AddEquiv.refl PUnit
 | _ :: zs,0=>z132 (T:=T) (S:=S) (M:=M) zs 0
 | _ :: zs,i+1 =>
  AddEquiv.prodCongr
   (z132 (T:=T) (S:=S) (M:=M) zs (i+1))
   (z132 (T:=T) (S:=S) (M:=M) zs i)
private lemma z133 {T S M:Type} [CommRing T] [CommRing S] [Algebra T S]
  [AddCommGroup M] [Module T M] [Module S M] [IsScalarTower T S M] :
  ∀ (zs:List T) (k : ℕ) (t:T) (x:z80 T M zs k),
   z132 (T:=T) (S:=S) (M:=M) zs k (t•x)=algebraMap T S t•z132 (T:=T) (S:=S) (M:=M) zs k x
 | [],0,t,m=>(algebraMap_smul S t m).symm
 | [],_+1,_,_=>rfl
 | _ :: zs,0,t,x=>z133 (T:=T) (S:=S) (M:=M) zs 0 t x
 | _ :: zs,i+1,t,(a,b) =>
  Prod.ext (z133 (T:=T) (S:=S) (M:=M) zs (i+1) t a)
   (z133 (T:=T) (S:=S) (M:=M) zs i t b)
private lemma z134 {T S M:Type} [CommRing T] [CommRing S] [Algebra T S]
  [AddCommGroup M] [Module T M] [Module S M] [IsScalarTower T S M] :
  ∀ (zs:List T) (k : ℕ) (x:z80 T M zs (k+1)),
   z132 (T:=T) (S:=S) (M:=M) zs k (z82 T M zs k x) =
    z82 S M (zs.map (algebraMap T S)) k
     (z132 (T:=T) (S:=S) (M:=M) zs (k+1) x)
 | [],0,_=>rfl
 | [],_+1,_=>rfl
 | z :: zs,0,(a,b)=>by
  change z132 (T:=T) (S:=S) (M:=M) zs 0 (z82 T M zs 0 a+z•b) =
   z82 S M (zs.map (algebraMap T S)) 0 (z132 (T:=T) (S:=S) (M:=M) zs 1 a)+algebraMap T S z•z132 (T:=T) (S:=S) (M:=M) zs 0 b
  rw [map_add,z133,z134 (T:=T) (S:=S) (M:=M) zs 0 a]
 | z :: zs,i+1,(a,b)=>by
  apply Prod.ext
  ·
   change z132 (T:=T) (S:=S) (M:=M) zs (i+1) (z82 T M zs (i+1) a+z•b) =
    z82 S M (zs.map (algebraMap T S)) (i+1)
     (z132 (T:=T) (S:=S) (M:=M) zs (i+2) a) +
     algebraMap T S z•z132 (T:=T) (S:=S) (M:=M) zs (i+1) b
   rw [map_add,z133,z134 (T:=T) (S:=S) (M:=M) zs (i+1) a]
  ·
   change z132 (T:=T) (S:=S) (M:=M) zs i (-(z82 T M zs i b)) =
    -(z82 S M (zs.map (algebraMap T S)) i
     (z132 (T:=T) (S:=S) (M:=M) zs (i+1) b))
   rw [map_neg,z134 (T:=T) (S:=S) (M:=M) zs i b]
lemma z135 {T S M:Type} [CommRing T] [CommRing S] [Algebra T S]
    [AddCommGroup M] [Module T M] [Module S M] [IsScalarTower T S M]
    (zs:List T) (k : ℕ) :
    Nonempty (z94 T M zs k ≃ₗ[T] RestrictScalars T S (z94 S M (zs.map (algebraMap T S)) k)):=by
  let zS:=zs.map (algebraMap T S)
  cases k with
  | zero =>
    let e0:=z132 (T:=T) (S:=S) (M:=M) zs 0;let e1:=z132 (T:=T) (S:=S) (M:=M) zs 1
    have q0:∀ x:z80 T M zs 0,x∈LinearMap.range (z82 T M zs 0)↔e0 x∈LinearMap.range (z82 S M zS 0):=fun x=>by
      constructor
      · rintro ⟨a,rfl⟩
        exact ⟨e1 a,(z134 (T:=T) (S:=S) (M:=M) zs 0 a).symm⟩
      · rintro ⟨b,hb⟩
        refine ⟨e1.symm b,e0.injective ?_⟩
        rw [z134 (T:=T) (S:=S) (M:=M) zs 0 (e1.symm b)]
        change z82 S M zS 0 (e1 (e1.symm b))=e0 x;rw [e1.apply_symm_apply,hb]
    let dT:=LinearMap.range (z82 T M zs 0);let dS:=LinearMap.range (z82 S M zS 0)
    let f0 :=
      QuotientAddGroup.lift dT.toAddSubgroup
        ((QuotientAddGroup.mk' dS.toAddSubgroup).comp e0.toAddMonoidHom)
        (fun x hx=>by
          rw [AddMonoidHom.mem_ker,AddMonoidHom.comp_apply,QuotientAddGroup.mk'_apply,QuotientAddGroup.eq_zero_iff]
          exact (q0 x).mp hx)
    let g0 :=
      QuotientAddGroup.lift dS.toAddSubgroup
        ((QuotientAddGroup.mk' dT.toAddSubgroup).comp e0.symm.toAddMonoidHom)
        (fun y hy=>by
          rw [AddMonoidHom.mem_ker,AddMonoidHom.comp_apply,QuotientAddGroup.mk'_apply,QuotientAddGroup.eq_zero_iff];change e0.symm y∈LinearMap.range (z82 T M zs 0);rw [q0,e0.apply_symm_apply]
          exact hy)
    exact ⟨{
      toFun:=fun a=>(RestrictScalars.addEquiv T S _).symm (f0 a)
      invFun:=fun b=>g0 (RestrictScalars.addEquiv T S _ b)
      map_add':=fun a b=>f0.map_add a b
      map_smul':=fun t a=>by
        obtain ⟨x,rfl⟩:=Submodule.Quotient.mk_surjective dT a;apply (RestrictScalars.addEquiv T S _).injective
        change Submodule.Quotient.mk (p:=dS) (e0 (t•x))=Submodule.Quotient.mk (p:=dS) (algebraMap T S t•e0 x)
        rw [z133]
      left_inv:=fun a=>by
        obtain ⟨x,rfl⟩:=Submodule.Quotient.mk_surjective dT a
        change Submodule.Quotient.mk (p:=dT) (e0.symm (e0 x))=Submodule.Quotient.mk (p:=dT) x
        rw [e0.symm_apply_apply]
      right_inv:=fun b=>by
        apply (RestrictScalars.addEquiv T S _).injective;let b':z94 S M zS 0:=RestrictScalars.addEquiv T S _ b;obtain ⟨y,hy⟩:=Submodule.Quotient.mk_surjective dS b';change f0 (g0 b')=b';rw [← hy]
        change Submodule.Quotient.mk (p:=dS) (e0 (e0.symm y))=Submodule.Quotient.mk (p:=dS) y
        rw [e0.apply_symm_apply] }⟩
  | succ i =>
    let e0:=z132 (T:=T) (S:=S) (M:=M) zs i;let e1:=z132 (T:=T) (S:=S) (M:=M) zs (i+1);let e2:=z132 (T:=T) (S:=S) (M:=M) zs (i+2)
    have q4:∀ x:z80 T M zs (i+1),x∈LinearMap.ker (z82 T M zs i)↔e1 x∈LinearMap.ker (z82 S M zS i):=fun x=>by
      simp only [LinearMap.mem_ker];have hc:=z134 (T:=T) (S:=S) (M:=M) zs i x;change e0 (z82 T M zs i x)=z82 S M zS i (e1 x) at hc;rw [← hc];exact (e0.map_eq_zero_iff).symm
    have q0:∀ x:z80 T M zs (i+1),
        x∈LinearMap.range (z82 T M zs (i+1))↔e1 x∈LinearMap.range (z82 S M zS (i+1)):=fun x=>by
      constructor
      · rintro ⟨a,rfl⟩
        exact ⟨e2 a,(z134 (T:=T) (S:=S) (M:=M) zs (i+1) a).symm⟩
      · rintro ⟨b,hb⟩
        refine ⟨e2.symm b,e1.injective ?_⟩
        rw [z134 (T:=T) (S:=S) (M:=M) zs (i+1) (e2.symm b)]
        change z82 S M zS (i+1) (e2 (e2.symm b))=e1 x;rw [e2.apply_symm_apply,hb]
    let q3:LinearMap.ker (z82 T M zs i) ≃+ LinearMap.ker (z82 S M zS i) :=
      { toFun:=fun p=>⟨e1 p.1,(q4 p.1).mp p.2⟩
        invFun:=fun q=>⟨e1.symm q.1,(q4 (e1.symm q.1)).mpr (by rw [e1.apply_symm_apply];exact q.2)⟩
        map_add':=fun p₁ p₂=>Subtype.ext (e1.map_add p₁.1 p₂.1)
        left_inv:=fun p=>Subtype.ext (e1.symm_apply_apply p.1)
        right_inv:=fun q=>Subtype.ext (e1.apply_symm_apply q.1) }
    let q2:=(LinearMap.range (z82 T M zs (i+1))).comap (LinearMap.ker (z82 T M zs i)).subtype;let q1:=(LinearMap.range (z82 S M zS (i+1))).comap (LinearMap.ker (z82 S M zS i)).subtype
    let fS0 :=
      QuotientAddGroup.lift q2.toAddSubgroup
        ((QuotientAddGroup.mk' q1.toAddSubgroup).comp q3.toAddMonoidHom)
        (fun p hp=>by
          rw [AddMonoidHom.mem_ker,AddMonoidHom.comp_apply,QuotientAddGroup.mk'_apply,QuotientAddGroup.eq_zero_iff]
          exact (q0 p.1).mp hp)
    let gS0 :=
      QuotientAddGroup.lift q1.toAddSubgroup
        ((QuotientAddGroup.mk' q2.toAddSubgroup).comp q3.symm.toAddMonoidHom)
        (fun q hq=>by
          rw [AddMonoidHom.mem_ker,AddMonoidHom.comp_apply,QuotientAddGroup.mk'_apply,QuotientAddGroup.eq_zero_iff];change e1.symm q.1∈LinearMap.range (z82 T M zs (i+1))
          rw [q0,e1.apply_symm_apply];exact hq)
    let fS:z94 T M zs (i+1)→z94 S M zS (i+1):=fun a=>fS0 a
    let gS:z94 S M zS (i+1)→z94 T M zs (i+1):=fun b=>gS0 b
    exact ⟨{
      toFun:=fun a=>(RestrictScalars.addEquiv T S _).symm (fS a)
      invFun:=fun b=>gS (RestrictScalars.addEquiv T S _ b)
      map_add':=fun a b=>fS0.map_add a b
      map_smul':=fun t a=>by
        obtain ⟨x,rfl⟩:=Submodule.Quotient.mk_surjective q2 a;apply (RestrictScalars.addEquiv T S _).injective
        change Submodule.Quotient.mk (p:=q1) (q3 (t•x))=Submodule.Quotient.mk (p:=q1) (algebraMap T S t•q3 x)
        have hsm:q3 (t•x)=algebraMap T S t•q3 x:=Subtype.ext (z133 (T:=T) (S:=S) (M:=M) zs (i+1) t x.1);rw [hsm]
      left_inv:=fun a=>by
        obtain ⟨x,rfl⟩:=Submodule.Quotient.mk_surjective q2 a
        change Submodule.Quotient.mk (p:=q2) (q3.symm (q3 x))=Submodule.Quotient.mk (p:=q2) x
        rw [q3.symm_apply_apply]
      right_inv:=fun b=>by
        apply (RestrictScalars.addEquiv T S _).injective;let b':z94 S M zS (i+1):=RestrictScalars.addEquiv T S _ b;obtain ⟨y,hy⟩:=Submodule.Quotient.mk_surjective q1 b';change fS (gS b')=b';rw [← hy]
        change Submodule.Quotient.mk (p:=q1) (q3 (q3.symm y))=Submodule.Quotient.mk (p:=q1) y
        rw [q3.apply_symm_apply] }⟩
private def z136 (R T:Type) [CommRing R] [CommRing T] [Algebra R T]
  {X Y:Type} [AddCommMonoid X] [Module T X] [AddCommMonoid Y] [Module T Y]
  (e:X ≃ₗ[T] Y) : RestrictScalars R T X ≃ₗ[R] RestrictScalars R T Y :=
 { e.toAddEquiv with map_smul':=fun r x=>e.map_smul (algebraMap R T r) x }
private lemma z137 {T S N:Type} [CommRing T] [AddCommGroup S] [Module T S]
  [AddCommGroup N] [Module T N]
  (hS:∀ q : ℕ,Subsingleton (z56 T S N (q+1))) :
  ∀ (r q : ℕ),Subsingleton (z56 T (Fin r→S) N (q+1))
 | 0,q=>by
  have : Module.Projective T (Fin 0→S) :=
   Module.Projective.of_split (0:(Fin 0→S) →ₗ[T] (Fin 0→T)) 0
    (LinearMap.ext fun _=>funext fun i=>Fin.elim0 i)
  exact z67 (Fin 0→S) N q
 | r+1,q=>by
  let i0:S →ₗ[T] (Fin (r+1)→S) :=
   {
    toFun:=fun a=>Fin.cons a 0
    map_add':=fun a b=>by ext i;refine Fin.cases rfl (fun _=>by simp) i
    map_smul':=fun t a=>by ext i;refine Fin.cases rfl (fun _=>by simp) i }
  let p0:(Fin (r+1)→S) →ₗ[T] (Fin r→S) :=
   {
    toFun:=fun f j=>f j.succ
    map_add':=fun _ _=>rfl
    map_smul':=fun _ _=>rfl }
  have hi0:Injective i0:=fun a b h=>congrFun h 0
  have hp0:Surjective p0:=fun f=>⟨Fin.cons 0 f,by ext j;rfl⟩
  have q0:LinearMap.range i0=LinearMap.ker p0:=by
   ext f;simp only [LinearMap.mem_range,LinearMap.mem_ker,i0,p0,LinearMap.coe_mk,AddHom.coe_mk];constructor
   · rintro ⟨a,rfl⟩;ext j;rfl
   ·
    intro hf;refine ⟨f 0,?_⟩;ext i
    refine Fin.cases rfl (fun j=>(congrFun hf j).symm) i
  obtain ⟨_,_,h2,_⟩:=z65 i0 p0 hi0 hp0 q0 N;have : Subsingleton (z56 T S N (q+1)):=hS q;have : Subsingleton (z56 T (Fin r→S) N (q+1)):=z137 hS r q
  refine subsingleton_iff_forall_eq 0 |>.mpr fun z => ?_
  have hpz:z58 p0 N (q+1) z=0:=Subsingleton.elim _ 0;obtain ⟨w,rfl⟩:=(h2 (q+1) z).mp hpz;rw [Subsingleton.elim w 0,map_zero]
private noncomputable def z138 {R T S M₁ M₂ : Type} [CommRing R] [CommRing T] [CommRing S]
  [Algebra R S] [Algebra T S] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
  (f:M₁ →ₗ[R] M₂) : (S ⊗[R] M₁) →ₗ[T] (S ⊗[R] M₂) :=
 {
  toFun:=LinearMap.lTensor S f
  map_add':=map_add _
  map_smul':=fun t x=>by
   induction x using TensorProduct.induction_on with
   | zero=>simp
   | tmul s m =>
    change LinearMap.lTensor S f ((t•s) ⊗ₜ[R] m)=t•(LinearMap.lTensor S f (s ⊗ₜ[R] m));simp [LinearMap.lTensor_tmul,smul_tmul']
   | add x₁ x₂ ih₁ ih₂=>simp [map_add,smul_add,ih₁,ih₂] }
private noncomputable def z139 {R T S N B:Type}
  [CommRing R] [CommRing T] [CommRing S]
  [Algebra R T] [Algebra R S] [Algebra T S] [IsScalarTower R T S]
  [AddCommGroup N] [Module T N] [AddCommGroup B] [Module R B]
  (e₀ : RestrictScalars R T (S ⊗[T] N) ≃ₗ[R] B)
  (M:Type) [AddCommGroup M] [Module R M] :
  (M ⊗[R] B) ≃ₗ[R] RestrictScalars R T ((S ⊗[R] M) ⊗[T] N):=by
 let toF0 (m:M) : (S ⊗[T] N) →ₗ[T] ((S ⊗[R] M) ⊗[T] N) :=
  TensorProduct.lift
   {
    toFun:=fun s =>
     {
      toFun:=fun n=>(s ⊗ₜ[R] m) ⊗ₜ[T] n
      map_add':=fun n₁ n₂=>tmul_add _ _ _
      map_smul':=fun t n=>by
       change (s ⊗ₜ[R] m) ⊗ₜ[T] (t•n)=t•((s ⊗ₜ[R] m) ⊗ₜ[T] n)
       rw [TensorProduct.tmul_smul] }
    map_add':=fun s₁ s₂=>by
     apply LinearMap.ext;intro n;simp [add_tmul]
    map_smul':=fun t s=>by
     apply LinearMap.ext;intro n;change ((t•s) ⊗ₜ[R] m) ⊗ₜ[T] n=t•((s ⊗ₜ[R] m) ⊗ₜ[T] n)
     rw [smul_tmul',smul_tmul'] }
 let q3:M →ₗ[R] (RestrictScalars R T (S ⊗[T] N)) →ₗ[R] RestrictScalars R T ((S ⊗[R] M) ⊗[T] N) :=
  {
   toFun:=fun m =>
    {
     toFun:=fun u=>toF0 m u
     map_add':=fun u₁ u₂=>(toF0 m).map_add u₁ u₂
     map_smul':=fun r u=>(toF0 m).map_smul (algebraMap R T r) u }
   map_add':=fun m₁ m₂=>by
    apply LinearMap.ext;intro u;change toF0 (m₁ + m₂) u=toF0 m₁ u+toF0 m₂ u
    induction u using TensorProduct.induction_on with
    | zero=>simp
    | tmul s n =>
     change (s ⊗ₜ[R] (m₁ + m₂)) ⊗ₜ[T] n=(s ⊗ₜ[R] m₁) ⊗ₜ[T] n+(s ⊗ₜ[R] m₂) ⊗ₜ[T] n;rw [tmul_add,add_tmul]
    | add u₁ u₂ ih₁ ih₂=>simp only [map_add] at ih₁ ih₂ ⊢;rw [ih₁,ih₂];abel
   map_smul':=fun r m=>by
    apply LinearMap.ext;intro u;change toF0 (r•m) u=algebraMap R T r•toF0 m u
    induction u using TensorProduct.induction_on with
    | zero=>simp
    | tmul s n =>
     change (s ⊗ₜ[R] (r•m)) ⊗ₜ[T] n=algebraMap R T r•((s ⊗ₜ[R] m) ⊗ₜ[T] n)
     have q1:r•s=algebraMap R T r•s:=by
      rw [Algebra.smul_def,Algebra.smul_def,IsScalarTower.algebraMap_apply R T S]
     have h1:s ⊗ₜ[R] (r•m)=algebraMap R T r•(s ⊗ₜ[R] m):=by
      rw [← smul_tmul,q1];rfl
     rw [h1];exact smul_tmul' (algebraMap R T r) (s ⊗ₜ[R] m) n
    | add u₁ u₂ ih₁ ih₂ =>
     simp only [map_add,smul_add] at ih₁ ih₂ ⊢
     rw [ih₁,ih₂] }
 let fwd:(M ⊗[R] B) →ₗ[R] RestrictScalars R T ((S ⊗[R] M) ⊗[T] N) :=
  TensorProduct.lift
   {
    toFun:=fun m=>(q3 m).comp e₀.symm.toLinearMap
    map_add':=fun m₁ m₂=>by
     apply LinearMap.ext;intro b;change q3 (m₁ + m₂) (e₀.symm b)=q3 m₁ (e₀.symm b)+q3 m₂ (e₀.symm b);rw [map_add];rfl
    map_smul':=fun r m=>by
     apply LinearMap.ext;intro b;change q3 (r•m) (e₀.symm b)=r•q3 m (e₀.symm b)
     rw [map_smul];rfl }
 letI : SMulCommClass R T (S ⊗[T] N) :=
  ⟨fun r t u=>by
   induction u using TensorProduct.induction_on with
   | zero=>simp
   | tmul s n =>
    change (r•(t•s)) ⊗ₜ[T] n=(t•(r•s)) ⊗ₜ[T] n;rw [smul_comm]
   | add u₁ u₂ ih₁ ih₂=>simp [smul_add,ih₁,ih₂]⟩
 let bwd_atom (n:N) : (S ⊗[R] M) →ₗ[R] ((S ⊗[T] N) ⊗[R] M) :=
  TensorProduct.lift
   {
    toFun:=fun s =>
     {
      toFun:=fun m=>(s ⊗ₜ[T] n) ⊗ₜ[R] m
      map_add':=fun m₁ m₂=>tmul_add _ _ _
      map_smul':=fun r m=>by
       change (s ⊗ₜ[T] n) ⊗ₜ[R] (r•m)=r•((s ⊗ₜ[T] n) ⊗ₜ[R] m)
       rw [TensorProduct.tmul_smul] }
    map_add':=fun s₁ s₂=>by
     apply LinearMap.ext;intro m;simp [add_tmul]
    map_smul':=fun r s=>by
     apply LinearMap.ext;intro m;change ((r•s) ⊗ₜ[T] n) ⊗ₜ[R] m=r•((s ⊗ₜ[T] n) ⊗ₜ[R] m);have h1:(r•s) ⊗ₜ[T] n=r•(s ⊗ₜ[T] n):=rfl;rw [h1]
     exact smul_tmul' r (s ⊗ₜ[T] n) m }
 let q0:((S ⊗[R] M) ⊗[T] N) →ₗ[T] ((S ⊗[T] N) ⊗[R] M) :=
  TensorProduct.lift
   {
    toFun:=fun sm =>
     {
      toFun:=fun n=>bwd_atom n sm
      map_add':=fun n₁ n₂=>by
       induction sm using TensorProduct.induction_on with
       | zero=>simp
       | tmul s m =>
        change (s ⊗ₜ[T] (n₁ + n₂)) ⊗ₜ[R] m=(s ⊗ₜ[T] n₁) ⊗ₜ[R] m+(s ⊗ₜ[T] n₂) ⊗ₜ[R] m;rw [tmul_add,add_tmul]
       | add u₁ u₂ ih₁ ih₂=>simp only [map_add] at ih₁ ih₂ ⊢;rw [ih₁,ih₂];abel
      map_smul':=fun t n=>by
       induction sm using TensorProduct.induction_on with
       | zero=>simp
       | tmul s m =>
        change (s ⊗ₜ[T] (t•n)) ⊗ₜ[R] m=(t•(s ⊗ₜ[T] n)) ⊗ₜ[R] m;rw [TensorProduct.tmul_smul]
       | add u₁ u₂ ih₁ ih₂=>simp only [map_add,smul_add] at ih₁ ih₂ ⊢;rw [ih₁,ih₂] }
    map_add':=fun sm₁ sm₂=>by
     apply LinearMap.ext;intro n;change bwd_atom n (sm₁ + sm₂)=bwd_atom n sm₁ + bwd_atom n sm₂;rw [map_add]
    map_smul':=fun t sm=>by
     apply LinearMap.ext;intro n;change bwd_atom n (t•sm)=t•bwd_atom n sm
     induction sm using TensorProduct.induction_on with
     | zero=>simp
     | tmul s m =>
      change ((t•s) ⊗ₜ[T] n) ⊗ₜ[R] m=(t•(s ⊗ₜ[T] n)) ⊗ₜ[R] m;rw [smul_tmul']
     | add u₁ u₂ ih₁ ih₂=>simp only [smul_add,map_add] at ih₁ ih₂ ⊢;rw [ih₁,ih₂] }
 let e₀':(S ⊗[T] N) →ₗ[R] B :=
  {
   toFun:=fun u=>e₀ ((RestrictScalars.addEquiv R T _).symm u)
   map_add':=fun u₁ u₂=>e₀.map_add _ _
   map_smul':=fun r u=>by
    have hsm:r•u=algebraMap R T r•u:=by
     induction u using TensorProduct.induction_on with
     | zero=>simp
     | tmul s n =>
      change (r•s) ⊗ₜ[T] n=(algebraMap R T r•s) ⊗ₜ[T] n;congr 1;rw [Algebra.smul_def,Algebra.smul_def,IsScalarTower.algebraMap_apply R T S]
     | add u₁ u₂ ih₁ ih₂=>rw [smul_add,smul_add,ih₁,ih₂]
    change e₀ ((RestrictScalars.addEquiv R T _).symm (r•u))=r•e₀ ((RestrictScalars.addEquiv R T _).symm u);rw [hsm]
    exact e₀.map_smul r ((RestrictScalars.addEquiv R T _).symm u) }
 let q2:((S ⊗[T] N) ⊗[R] M) →ₗ[R] (M ⊗[R] B):=(LinearMap.lTensor M e₀').comp (TensorProduct.comm R (S ⊗[T] N) M).toLinearMap
 let bwd:RestrictScalars R T ((S ⊗[R] M) ⊗[T] N) →ₗ[R] (M ⊗[R] B) :=
  {
   toFun:=fun x=>q2 (q0 (RestrictScalars.addEquiv R T _ x))
   map_add':=fun x₁ x₂=>by rw [map_add,map_add,map_add]
   map_smul':=fun r x=>by
    change q2 (q0 (algebraMap R T r•RestrictScalars.addEquiv R T _ x))=r•q2 (q0 (RestrictScalars.addEquiv R T _ x));rw [map_smul]
    have h:∀ y:(S ⊗[T] N) ⊗[R] M,q2 (algebraMap R T r•y)=r•q2 y:=fun y=>by
     induction y using TensorProduct.induction_on with
     | zero=>simp
     | tmul u m =>
      change m ⊗ₜ[R] e₀ ((RestrictScalars.addEquiv R T _).symm (algebraMap R T r•u))=r•(m ⊗ₜ[R] e₀ ((RestrictScalars.addEquiv R T _).symm u));rw [← TensorProduct.tmul_smul];congr 1;exact e₀.map_smul r ((RestrictScalars.addEquiv R T _).symm u)
     | add y₁ y₂ ih₁ ih₂=>simp only [smul_add,map_add] at ih₁ ih₂ ⊢;rw [ih₁,ih₂]
    exact h (q0 (RestrictScalars.addEquiv R T _ x)) }
 refine LinearEquiv.ofLinearMap fwd bwd ?_ ?_
 ·
  apply LinearMap.ext;intro x;apply (RestrictScalars.addEquiv R T _).injective;let x':(S ⊗[R] M) ⊗[T] N:=RestrictScalars.addEquiv R T _ x;change (RestrictScalars.addEquiv R T _) (fwd (q2 (q0 x')))=x'
  induction x' using TensorProduct.induction_on with
  | zero=>rw [map_zero,map_zero,map_zero,map_zero]
  | tmul sm n =>
   induction sm using TensorProduct.induction_on with
   | zero=>rw [zero_tmul,map_zero,map_zero,map_zero,map_zero]
   | tmul s m =>
    change (RestrictScalars.addEquiv R T _) (fwd (m ⊗ₜ[R] e₀ ((RestrictScalars.addEquiv R T _).symm (s ⊗ₜ[T] n))))=(s ⊗ₜ[R] m) ⊗ₜ[T] n;change toF0 m (RestrictScalars.addEquiv R T _ (e₀.symm (e₀ ((RestrictScalars.addEquiv R T _).symm (s ⊗ₜ[T] n)))))=(s ⊗ₜ[R] m) ⊗ₜ[T] n;rw [e₀.symm_apply_apply];rfl
   | add u₁ u₂ ih₁ ih₂ =>
    rw [add_tmul,map_add,map_add,map_add,map_add,ih₁,ih₂]
  | add x₁ x₂ ih₁ ih₂ =>
   rw [map_add,map_add,map_add,map_add,ih₁,ih₂]
 ·
  apply LinearMap.ext;intro y;change bwd (fwd y)=y
  induction y using TensorProduct.induction_on with
  | zero=>rw [map_zero,map_zero]
  | tmul m b =>
   obtain ⟨u,rfl⟩:=e₀.surjective b;let u':S ⊗[T] N:=RestrictScalars.addEquiv R T _ u;change bwd (fwd (m ⊗ₜ[R] e₀ ((RestrictScalars.addEquiv R T _).symm u')))=m ⊗ₜ[R] e₀ ((RestrictScalars.addEquiv R T _).symm u')
   induction u' using TensorProduct.induction_on with
   | zero =>
    have h0:e₀ ((RestrictScalars.addEquiv R T _).symm 0)=0:=by rw [map_zero,map_zero]
    rw [h0,tmul_zero,map_zero,map_zero]
   | tmul s n =>
    change q2 (q0 (toF0 m (RestrictScalars.addEquiv R T _
     (e₀.symm (e₀ ((RestrictScalars.addEquiv R T _).symm (s ⊗ₜ[T] n))))))) =
     m ⊗ₜ[R] e₀ ((RestrictScalars.addEquiv R T _).symm (s ⊗ₜ[T] n))
    rw [e₀.symm_apply_apply];rfl
   | add u₁ u₂ ih₁ ih₂ =>
    have he:e₀ ((RestrictScalars.addEquiv R T _).symm (u₁ + u₂))=e₀ ((RestrictScalars.addEquiv R T _).symm u₁)+e₀ ((RestrictScalars.addEquiv R T _).symm u₂):=by
     rw [map_add,map_add]
    rw [he,tmul_add,map_add,map_add,ih₁,ih₂]
  | add y₁ y₂ ih₁ ih₂ =>
   rw [map_add,map_add,ih₁,ih₂]
private lemma z140 {R T S N B M₁ M₂ : Type}
  [CommRing R] [CommRing T] [CommRing S]
  [Algebra R T] [Algebra R S] [Algebra T S] [IsScalarTower R T S]
  [AddCommGroup N] [Module T N] [AddCommGroup B] [Module R B]
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
  (e₀ : RestrictScalars R T (S ⊗[T] N) ≃ₗ[R] B) (f:M₁ →ₗ[R] M₂) (t:M₁ ⊗[R] B) :
  (RestrictScalars.addEquiv R T _) (z139 e₀ M₂ (LinearMap.rTensor B f t))=LinearMap.rTensor N (z138 f) ((RestrictScalars.addEquiv R T _) (z139 e₀ M₁ t)):=by
 induction t using TensorProduct.induction_on with
 | zero=>simp
 | tmul m b =>
  obtain ⟨u,rfl⟩:=e₀.surjective b
  induction u using TensorProduct.induction_on with
  | zero =>
   have h0:e₀ 0=0:=map_zero e₀;change (RestrictScalars.addEquiv R T _) (z139 e₀ M₂ (LinearMap.rTensor B f (m ⊗ₜ[R] e₀ 0)))=LinearMap.rTensor N (z138 f) ((RestrictScalars.addEquiv R T _) (z139 e₀ M₁ (m ⊗ₜ[R] e₀ 0)));rw [h0,tmul_zero,map_zero,map_zero,map_zero,map_zero,map_zero,map_zero]
  | tmul s n =>
   simp only [LinearMap.rTensor_tmul]
   have h1:∀ {X:Type} [AddCommGroup X] [Module R X] (x:X),
     (RestrictScalars.addEquiv R T _) (z139 e₀ X (x ⊗ₜ[R] e₀ ((RestrictScalars.addEquiv R T _).symm (s ⊗ₜ[T] n))))=(s ⊗ₜ[R] x) ⊗ₜ[T] n:=fun {X} _ _ x=>by
    unfold z139;rw [LinearEquiv.coe_ofLinearMap]
    change (TensorProduct.lift _:S ⊗[T] N →ₗ[T] (S ⊗[R] X) ⊗[T] N)
     (e₀.symm (e₀ ((RestrictScalars.addEquiv R T _).symm (s ⊗ₜ[T] n))))=(s ⊗ₜ[R] x) ⊗ₜ[T] n
    rw [e₀.symm_apply_apply];rfl
   have hfm:=h1 (f m);have hm:=h1 m;exact (hfm.trans (by rw [LinearMap.rTensor_tmul];rfl)).trans (congrArg (LinearMap.rTensor N (z138 f)) hm.symm)
  | add u₁ u₂ ih₁ ih₂ =>
   have he:e₀ (u₁ + u₂)=e₀ u₁ + e₀ u₂ := e₀.map_add u₁ u₂;change (RestrictScalars.addEquiv R T _) (z139 e₀ M₂ (LinearMap.rTensor B f (m ⊗ₜ[R] e₀ (u₁ + u₂))))=LinearMap.rTensor N (z138 f) ((RestrictScalars.addEquiv R T _) (z139 e₀ M₁ (m ⊗ₜ[R] e₀ (u₁ + u₂))));rw [he,tmul_add,map_add,map_add,map_add,map_add,map_add,map_add,ih₁,ih₂]
 | add t₁ t₂ ih₁ ih₂ =>
  rw [map_add,map_add,map_add,map_add,map_add,map_add,ih₁,ih₂]
private lemma z141 {R T S N B K F M:Type}
  [CommRing R] [CommRing T] [CommRing S]
  [Algebra R T] [Algebra R S] [Algebra T S] [IsScalarTower R T S] [Module.Flat R S]
  [AddCommGroup N] [Module T N] [AddCommGroup B] [Module R B]
  [AddCommGroup K] [Module R K] [AddCommGroup F] [Module R F] [Module.Flat R F]
  [AddCommGroup M] [Module R M]
  (e₀ : RestrictScalars R T (S ⊗[T] N) ≃ₗ[R] B)
  (i:K →ₗ[R] F) (p:F →ₗ[R] M)
  (hi:Injective i) (hp:Surjective p)
  (q2:LinearMap.range i=LinearMap.ker p)
  (hSF:Subsingleton (z56 T (S ⊗[R] F) N 1)) :
  Nonempty (z56 R M B 1 ≃ₗ[R] RestrictScalars R T (z56 T (S ⊗[R] M) N 1)):=by
 have : Subsingleton (z56 R F B 1):=z67 F B 0;obtain ⟨δR,hR1,_,hR3⟩:=z65 i p hi hp q2 B
 have hδR_inj:Injective (δR 0) :=
  (injective_iff_map_eq_zero _).mpr fun x hx=>by
   obtain ⟨y,rfl⟩:=(hR3 0 x).mp hx;rw [Subsingleton.elim y 0,map_zero]
 have hδR_rng:LinearMap.range (δR 0)=LinearMap.ker (z58 i B 0):=LinearMap.exact_iff.mp (hR1 0) |>.symm;let e1R:z56 R M B 1 ≃ₗ[R] LinearMap.ker (z58 i B 0):=(LinearEquiv.ofInjective (δR 0) hδR_inj).trans (LinearEquiv.ofEq _ _ hδR_rng);have hiS:Injective (z138 (T:=T) (S:=S) i):=Module.Flat.lTensor_preserves_injective_linearMap i hi
 have hpS:Surjective (z138 (T:=T) (S:=S) p):=LinearMap.lTensor_surjective S hp
 have q0:LinearMap.range (z138 (T:=T) (S:=S) i)=LinearMap.ker (z138 (T:=T) (S:=S) p):=by
  ext x;exact (lTensor_exact S (LinearMap.exact_iff.mpr q2.symm) hp x).symm
 obtain ⟨δT,hT1,_,hT3⟩:=z65 (z138 (T:=T) (S:=S) i) (z138 (T:=T) (S:=S) p)
  hiS hpS q0 N
 have hδT_inj:Injective (δT 0) :=
  (injective_iff_map_eq_zero _).mpr fun x hx=>by
   obtain ⟨y,rfl⟩:=(hT3 0 x).mp hx;rw [Subsingleton.elim y 0,map_zero]
 have hδT_rng:LinearMap.range (δT 0)=LinearMap.ker (z58 (z138 (T:=T) (S:=S) i) N 0):=LinearMap.exact_iff.mp (hT1 0) |>.symm
 let e1T:z56 T (S ⊗[R] M) N 1 ≃ₗ[T]
   LinearMap.ker (z58 (z138 (T:=T) (S:=S) i) N 0) :=
  (LinearEquiv.ofInjective (δT 0) hδT_inj).trans (LinearEquiv.ofEq _ _ hδT_rng)
 let eK:z56 R K B 0 ≃ₗ[R] RestrictScalars R T (z56 T (S ⊗[R] K) N 0) :=
  ((z59 R K B).trans (z139 e₀ K)).trans
   (z136 R T (z59 T (S ⊗[R] K) N).symm)
 let eF:z56 R F B 0 ≃ₗ[R] RestrictScalars R T (z56 T (S ⊗[R] F) N 0) :=
  ((z59 R F B).trans (z139 e₀ F)).trans
   (z136 R T (z59 T (S ⊗[R] F) N).symm)
 have hsq:∀ x:z56 R K B 0,
   (RestrictScalars.addEquiv R T _) (eF (z58 i B 0 x))=z58 (z138 (T:=T) (S:=S) i) N 0 ((RestrictScalars.addEquiv R T _) (eK x)):=fun x=>by
  apply (z59 T (S ⊗[R] F) N).injective;rw [z66]
  change (z59 T (S ⊗[R] F) N) ((z59 T (S ⊗[R] F) N).symm
   ((RestrictScalars.addEquiv R T _) (z139 e₀ F (z59 R F B (z58 i B 0 x))))) =
   LinearMap.rTensor N (z138 (T:=T) (S:=S) i)
    ((z59 T (S ⊗[R] K) N) ((z59 T (S ⊗[R] K) N).symm
     ((RestrictScalars.addEquiv R T _) (z139 e₀ K (z59 R K B x)))))
  rw [LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply,z66];exact z140 e₀ i (z59 R K B x)
 let q1:LinearMap.ker (z58 i B 0) ≃ₗ[R]
   RestrictScalars R T (LinearMap.ker (z58 (z138 (T:=T) (S:=S) i) N 0)) :=
  {
   toFun:=fun p=>⟨(RestrictScalars.addEquiv R T _) (eK p.1),by
    rw [LinearMap.mem_ker,← hsq p.1,LinearMap.mem_ker.mp p.2,map_zero,map_zero]⟩
   invFun:=fun q=>⟨eK.symm ((RestrictScalars.addEquiv R T _).symm q.1),by
    rw [LinearMap.mem_ker];apply eF.injective;apply (RestrictScalars.addEquiv R T _).injective;rw [map_zero,map_zero,hsq]
    have hq':(RestrictScalars.addEquiv R T _) (eK (eK.symm ((RestrictScalars.addEquiv R T _).symm q.1)))=q.1:=by
     rw [eK.apply_symm_apply];rfl
    rw [hq']
    exact LinearMap.mem_ker.mp q.2⟩
   map_add':=fun p₁ p₂=>Subtype.ext (by
    change (RestrictScalars.addEquiv R T _) (eK (p₁.1+p₂.1))=(RestrictScalars.addEquiv R T _) (eK p₁.1)+(RestrictScalars.addEquiv R T _) (eK p₂.1)
    rw [map_add,map_add])
   map_smul':=fun r p=>Subtype.ext (by
    change (RestrictScalars.addEquiv R T _) (eK (r•p.1))=algebraMap R T r•(RestrictScalars.addEquiv R T _) (eK p.1)
    rw [eK.map_smul];rfl)
   left_inv:=fun p=>Subtype.ext (eK.symm_apply_apply p.1)
   right_inv:=fun q=>Subtype.ext (by
    change (RestrictScalars.addEquiv R T _) (eK (eK.symm ((RestrictScalars.addEquiv R T _).symm q.1)))=q.1
    rw [eK.apply_symm_apply];rfl) }
 exact ⟨(e1R.trans q1).trans (z136 R T e1T.symm)⟩
private lemma z142 {R T S N B K F M:Type}
  [CommRing R] [CommRing T] [CommRing S]
  [Algebra R T] [Algebra R S] [Algebra T S] [IsScalarTower R T S] [Module.Flat R S]
  [AddCommGroup N] [Module T N] [AddCommGroup B] [Module R B]
  [AddCommGroup K] [Module R K] [AddCommGroup F] [Module R F] [Module.Flat R F]
  [AddCommGroup M] [Module R M]
  (i:K →ₗ[R] F) (p:F →ₗ[R] M)
  (hi:Injective i) (hp:Surjective p)
  (q1:LinearMap.range i=LinearMap.ker p) (j : ℕ)
  (hSF1:Subsingleton (z56 T (S ⊗[R] F) N (j+1)))
  (hSF2:Subsingleton (z56 T (S ⊗[R] F) N (j+2)))
  (eIH:z56 R K B (j+1) ≃ₗ[R] RestrictScalars R T (z56 T (S ⊗[R] K) N (j+1))) :
  Nonempty (z56 R M B (j+2) ≃ₗ[R] RestrictScalars R T (z56 T (S ⊗[R] M) N (j+2))):=by
 have : Subsingleton (z56 R F B (j+1)):=z67 F B j;have : Subsingleton (z56 R F B (j+2)):=z67 F B (j+1);obtain ⟨δR,hR1,_,hR3⟩:=z65 i p hi hp q1 B
 have hδR_bij:Bijective (δR (j+1)):=by
  refine ⟨(injective_iff_map_eq_zero _).mpr fun x hx => ?_,fun y => ?_⟩
  ·
   obtain ⟨z,rfl⟩:=(hR3 (j+1) x).mp hx;rw [Subsingleton.elim z 0,map_zero]
  · exact (hR1 (j+1) y).mp (Subsingleton.elim _ 0)
 have hiS:Injective (z138 (T:=T) (S:=S) i):=Module.Flat.lTensor_preserves_injective_linearMap i hi;have hpS:Surjective (z138 (T:=T) (S:=S) p):=LinearMap.lTensor_surjective S hp
 have q0:LinearMap.range (z138 (T:=T) (S:=S) i)=LinearMap.ker (z138 (T:=T) (S:=S) p):=by
  ext x;exact (lTensor_exact S (LinearMap.exact_iff.mpr q1.symm) hp x).symm
 obtain ⟨δT,hT1,_,hT3⟩:=z65 (z138 (T:=T) (S:=S) i) (z138 (T:=T) (S:=S) p)
  hiS hpS q0 N
 have hδT_bij:Bijective (δT (j+1)):=by
  refine ⟨(injective_iff_map_eq_zero _).mpr fun x hx => ?_,fun y => ?_⟩
  ·
   obtain ⟨z,rfl⟩:=(hT3 (j+1) x).mp hx;rw [Subsingleton.elim z 0,map_zero]
  · exact (hT1 (j+1) y).mp (Subsingleton.elim _ 0)
 let eR:z56 R M B (j+2) ≃ₗ[R] z56 R K B (j+1):=LinearEquiv.ofBijective (δR (j+1)) hδR_bij;let eT:z56 T (S ⊗[R] M) N (j+2) ≃ₗ[T] z56 T (S ⊗[R] K) N (j+1):=LinearEquiv.ofBijective (δT (j+1)) hδT_bij;exact ⟨(eR.trans eIH).trans (z136 R T eT.symm)⟩
private noncomputable def z143 {R T S:Type} [CommRing R] [CommRing T] [CommRing S]
  [Algebra R S] [Algebra T S] (r : ℕ) :
  (S ⊗[R] (Fin r→R)) ≃ₗ[T] (Fin r→S):=by
 let q0:(S ⊗[R] (Fin r→R)) →ₗ[R] (Fin r→S) :=
  TensorProduct.lift
   {
    toFun:=fun s =>
     {
      toFun:=fun g i=>g i•s
      map_add':=fun g₁ g₂=>by ext i;simp [add_smul]
      map_smul':=fun a g=>by ext i;simp [mul_smul] }
    map_add':=fun s₁ s₂=>by apply LinearMap.ext;intro g;ext i;simp [smul_add]
    map_smul':=fun a s=>by apply LinearMap.ext;intro g;ext i;exact (smul_comm a (g i) s).symm }
 let fwd:(S ⊗[R] (Fin r→R)) →ₗ[T] (Fin r→S) :=
  {
   toFun:=q0
   map_add':=q0.map_add
   map_smul':=fun t x=>by
    induction x using TensorProduct.induction_on with
    | zero=>simp
    | tmul s g =>
     ext i;change g i•(t•s)=t•(g i•s);rw [smul_comm]
    | add x₁ x₂ ih₁ ih₂=>simp only [smul_add,map_add] at ih₁ ih₂ ⊢;rw [ih₁,ih₂] }
 let bwd:(Fin r→S) →ₗ[T] (S ⊗[R] (Fin r→R)) :=
  {
   toFun:=fun f => ∑ i:Fin r,f i ⊗ₜ[R] Pi.single i (1:R)
   map_add':=fun f₁ f₂=>by simp [add_tmul,Finset.sum_add_distrib]
   map_smul':=fun t f=>by simp [smul_tmul',Finset.smul_sum] }
 refine LinearEquiv.ofLinearMap fwd bwd ?_ ?_
 ·
  apply LinearMap.ext;intro f;ext j
  simp only [LinearMap.comp_apply,LinearMap.id_apply,bwd,fwd,q0,LinearMap.coe_mk,AddHom.coe_mk,
   map_sum,TensorProduct.lift.tmul,Finset.sum_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij;simp [Pi.single_eq_of_ne (Ne.symm hij)]
  · intro hj;exact absurd (Finset.mem_univ j) hj
 ·
  apply LinearMap.ext;intro x
  induction x using TensorProduct.induction_on with
  | zero=>simp
  | tmul s g =>
   simp only [LinearMap.comp_apply,LinearMap.id_apply,bwd,fwd,q0,LinearMap.coe_mk,AddHom.coe_mk,TensorProduct.lift.tmul]
   have hg:g = ∑ i:Fin r,g i•Pi.single i (1:R):=by
    ext j;rw [Finset.sum_apply,Finset.sum_eq_single j]
    · simp
    · intro i _ hij;simp [Pi.single_eq_of_ne (Ne.symm hij)]
    · intro hj;exact absurd (Finset.mem_univ j) hj
   conv_rhs=>rw [hg]
   rw [TensorProduct.tmul_sum]
   refine Finset.sum_congr rfl fun i _ => ?_
   rw [smul_tmul]
  | add x₁ x₂ ih₁ ih₂ =>
   simp only [LinearMap.comp_apply,LinearMap.id_apply,map_add] at ih₁ ih₂ ⊢;rw [ih₁,ih₂]
private lemma z144 {T A B N:Type} [CommRing T]
  [AddCommGroup A] [Module T A] [AddCommGroup B] [Module T B] [AddCommGroup N] [Module T N]
  (e:A ≃ₗ[T] B) (k : ℕ) :
  Nonempty (z56 T A N k ≃ₗ[T] z56 T B N k):=by
 let iso:ModuleCat.of T A ≅ ModuleCat.of T B:=e.toModuleIso;exact ⟨(((Tor (ModuleCat.{0} T) k).mapIso iso).app (ModuleCat.of T N)).toLinearEquiv⟩
lemma z145 {R T S N B:Type}
  [CommRing R] [IsNoetherianRing R] [CommRing T] [CommRing S]
  [Algebra R T] [Algebra R S] [Algebra T S] [IsScalarTower R T S] [Module.Flat R S]
  [AddCommGroup N] [Module T N] [AddCommGroup B] [Module R B]
  (q0:∀ q : ℕ,Subsingleton (z56 T S N (q+1)))
  (e₀ : RestrictScalars R T (S ⊗[T] N) ≃ₗ[R] B) :
  ∀ (i : ℕ) (M:Type) [AddCommGroup M] [Module R M] [Module.Finite R M],Nonempty (z56 R M B i ≃ₗ[R] RestrictScalars R T (z56 T (S ⊗[R] M) N i))
 | 0,M,_,_,_ =>
  ⟨((z59 R M B).trans (z139 e₀ M)).trans
   (z136 R T (z59 T (S ⊗[R] M) N).symm)⟩
 | 1,M,_,_,_=>by
  obtain ⟨r,f,hf⟩:=Module.Finite.exists_fin (R:=R) (M:=M)
  let p:(Fin r→R) →ₗ[R] M :=
   {
    toFun:=fun g => ∑ i:Fin r,g i•f i
    map_add':=fun g₁ g₂=>by simp [add_smul,Finset.sum_add_distrib]
    map_smul':=fun a g=>by simp [Finset.smul_sum,mul_smul] }
  have hp:Surjective p:=fun m=>by
   have hm:m∈Submodule.span R (Set.range f):=hf▸Submodule.mem_top;rw [Submodule.mem_span_range_iff_exists_fun] at hm;obtain ⟨c,rfl⟩:=hm;exact ⟨c,rfl⟩
  let K:=LinearMap.ker p;have : Module.Finite R K:=Module.Finite.iff_fg.mpr (IsNoetherian.noetherian K);have q1:LinearMap.range K.subtype=LinearMap.ker p:=Submodule.range_subtype K;obtain ⟨eT⟩:=z144 (T:=T) (N:=N) (z143 (R:=R) (T:=T) (S:=S) r) 1
  have q3:Subsingleton (z56 T (S ⊗[R] (Fin r→R)) N 1):=by
   have : Subsingleton (z56 T (Fin r→S) N 1):=z137 q0 r 0;exact eT.toEquiv.subsingleton
  exact z141 e₀ K.subtype p Subtype.val_injective hp q1 q3
 | j+2,M,_,_,_=>by
  obtain ⟨r,f,hf⟩:=Module.Finite.exists_fin (R:=R) (M:=M)
  let p:(Fin r→R) →ₗ[R] M :=
   {
    toFun:=fun g => ∑ i:Fin r,g i•f i
    map_add':=fun g₁ g₂=>by simp [add_smul,Finset.sum_add_distrib]
    map_smul':=fun a g=>by simp [Finset.smul_sum,mul_smul] }
  have hp:Surjective p:=fun m=>by
   have hm:m∈Submodule.span R (Set.range f):=hf▸Submodule.mem_top;rw [Submodule.mem_span_range_iff_exists_fun] at hm;obtain ⟨c,rfl⟩:=hm;exact ⟨c,rfl⟩
  let K:=LinearMap.ker p;have : Module.Finite R K:=Module.Finite.iff_fg.mpr (IsNoetherian.noetherian K);have q1:LinearMap.range K.subtype=LinearMap.ker p:=Submodule.range_subtype K;obtain ⟨eT1⟩:=z144 (T:=T) (N:=N) (z143 (R:=R) (T:=T) (S:=S) r) (j+1);obtain ⟨eT2⟩:=z144 (T:=T) (N:=N) (z143 (R:=R) (T:=T) (S:=S) r) (j+2)
  have q3:Subsingleton (z56 T (S ⊗[R] (Fin r→R)) N (j+1)):=by
   have : Subsingleton (z56 T (Fin r→S) N (j+1)):=z137 q0 r j;exact eT1.toEquiv.subsingleton
  have q2:Subsingleton (z56 T (S ⊗[R] (Fin r→R)) N (j+2)):=by
   have : Subsingleton (z56 T (Fin r→S) N (j+2)):=z137 q0 r (j+1);exact eT2.toEquiv.subsingleton
  obtain ⟨eIH⟩:=z145 q0 e₀ (j+1) K;exact z142 K.subtype p Subtype.val_injective hp q1 j q3 q2 eIH
private lemma z146 {R A E M:Type}
  [CommRing R] [IsLocalRing R] [CommRing A] [IsLocalRing A]
  [Algebra R A] [IsLocalHom (algebraMap R A)]
  [AddCommGroup E] [Module A E] [AddCommGroup M] [Module R M]
  (e:M ≃+ E) (q1:∀ (r:R) (x:M),e (r•x)=algebraMap R A r•e x)
  (q0:Module.length (ResidueField R) (ResidueField A)=1) :
  Module.length R M=Module.length A E:=by
 letI : Module R E:=Module.restrictScalars R A E
 haveI : IsScalarTower R A E:=IsScalarTower.restrictScalars R A E
 let q2:M ≃ₗ[R] E:={ e with map_smul':=q1 };rw [q2.length_eq];have h1:=IsLocalRing.length_restrictScalars R A E;rw [q0,mul_one] at h1;exact h1
private lemma z147 {R T:Type}
  [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
  [Algebra R T]
  (P Q:Ideal R) (Q₂ I:Ideal T) (hI:I=P.map (algebraMap R T)⊔Q₂)
  [IsLocalRing (T⧸I)]
  (Δ_list:List T)
  (π : T →+* R) (hπ_alg:∀ r:R,π (algebraMap R T r)=r)
  (hker_π : RingHom.ker π = ofList Δ_list)
  (hQ₂_le:Q₂ ≤ RingHom.ker ((Ideal.Quotient.mk Q).comp π))
  (q6:∀ q∈Q,∃ d∈ofList Δ_list,Ideal.Quotient.mk Q₂ (algebraMap R T q)=Ideal.Quotient.mk Q₂ d)
  (hΔ_reg:z110 T Δ_list)
  (q7:Module.Flat R (T⧸Q₂))
  (q8:∀ q : ℕ,Subsingleton (z56 T (T⧸Q₂) (T⧸ofList Δ_list) (q+1)))
  (q3:∀ r∈maximalIdeal R,algebraMap R T r∈maximalIdeal T)
  (q2:Surjective
   ((residue (T⧸I)).comp ((Ideal.Quotient.mk I).comp (algebraMap R T)))) :
  ∀ i : ℕ,Module.length R (z56 R (R⧸P) (R⧸Q) i)=Module.length (T⧸I) (z94 (T⧸I) (T⧸I) (Δ_list.map (Ideal.Quotient.mk I)) i):=by
 intro i;let A:=T⧸I;let Δ : Ideal T:=ofList Δ_list;let S:=T⧸Q₂;let qS:T →+* S:=Ideal.Quotient.mk Q₂;let qA:T →+* A:=Ideal.Quotient.mk I;let fRS:R →+* S:=algebraMap R S
 let ψ : S →+* R⧸Q:=Ideal.Quotient.lift Q₂ ((Ideal.Quotient.mk Q).comp π) (fun t ht=>hQ₂_le ht)
 let πQ:(T ⧸ Δ) →+* R⧸Q:=Ideal.Quotient.lift Δ ((Ideal.Quotient.mk Q).comp π) (fun t ht=>by
  have ht0 : π t=0:=RingHom.mem_ker.mp (hker_π.symm▸ht)
  rw [RingHom.comp_apply,ht0,map_zero])
 have hψ_fRS:∀ r:R,ψ (fRS r)=Ideal.Quotient.mk Q r:=fun r=>by
  change Ideal.Quotient.mk Q (π (algebraMap R T r))=Ideal.Quotient.mk Q r;rw [hπ_alg]
 have hψ_qS:∀ t:T,ψ (qS t)=Ideal.Quotient.mk Q (π t):=fun _=>rfl
 let e₀ : RestrictScalars R T (S ⊗[T] (T ⧸ Δ)) ≃ₗ[R] (R⧸Q):=by
  letI : Algebra T (R⧸Q):=((Ideal.Quotient.mk Q).comp π).toAlgebra
  let e₀_fwdT:(S ⊗[T] (T ⧸ Δ)) →ₗ[T] (R⧸Q) :=
   TensorProduct.lift
    {
     toFun:=fun s =>
      {
       toFun:=fun u => ψ s * πQ u
       map_add':=fun u₁ u₂=>by rw [map_add,mul_add]
       map_smul':=fun t u=>by
        change ψ s * πQ (Ideal.Quotient.mk Δ t*u)=Ideal.Quotient.mk Q (π t)*(ψ s * πQ u);rw [map_mul];change ψ s*(Ideal.Quotient.mk Q (π t) * πQ u)=_
        ring }
     map_add':=fun s₁ s₂=>by apply LinearMap.ext;intro u;simp [map_add,add_mul]
     map_smul':=fun t s=>by
      apply LinearMap.ext;intro u;change ψ (qS t*s) * πQ u=Ideal.Quotient.mk Q (π t)*(ψ s * πQ u)
      rw [map_mul,hψ_qS];ring }
  let e₀_fwd:RestrictScalars R T (S ⊗[T] (T ⧸ Δ)) →ₗ[R] (R⧸Q) :=
   {
    toFun:=fun x=>e₀_fwdT (RestrictScalars.addEquiv R T _ x)
    map_add':=fun x₁ x₂=>e₀_fwdT.map_add _ _
    map_smul':=fun r x=>by
     change e₀_fwdT (algebraMap R T r•RestrictScalars.addEquiv R T _ x)=r•e₀_fwdT (RestrictScalars.addEquiv R T _ x);rw [e₀_fwdT.map_smul];change Ideal.Quotient.mk Q (π (algebraMap R T r))*e₀_fwdT _=Ideal.Quotient.mk Q r*e₀_fwdT _
     rw [hπ_alg] }
  let e₀_bwd0:(R⧸Q) →+ (S ⊗[T] (T ⧸ Δ)) :=
   QuotientAddGroup.lift Q.toAddSubgroup
    {
     toFun:=fun r=>fRS r ⊗ₜ[T] (1:T ⧸ Δ)
     map_zero':=by rw [map_zero,zero_tmul]
     map_add':=fun r₁ r₂=>by rw [map_add,add_tmul] }
    (fun q hq=>by
     rw [AddMonoidHom.mem_ker];change qS (algebraMap R T q) ⊗ₜ[T] (1:T ⧸ Δ)=0;obtain ⟨d,hd,hqd⟩:=q6 q hq;rw [hqd]
     have h2:qS d ⊗ₜ[T] (1:T ⧸ Δ)=(1:S) ⊗ₜ[T] (d•(1:T ⧸ Δ)):=by
      have : qS d=d•(1:S):=by change qS d=qS d*1;rw [mul_one]
      rw [this,smul_tmul]
     rw [h2]
     have h3:d•(1:T ⧸ Δ)=0:=by
      change Ideal.Quotient.mk Δ d*1=0;rw [mul_one,Ideal.Quotient.eq_zero_iff_mem];exact hd
     rw [h3,tmul_zero])
  let e₀_bwd:(R⧸Q) →ₗ[R] RestrictScalars R T (S ⊗[T] (T ⧸ Δ)) :=
   {
    toFun:=fun y=>(RestrictScalars.addEquiv R T _).symm (e₀_bwd0 y)
    map_add':=fun y₁ y₂=>e₀_bwd0.map_add y₁ y₂
    map_smul':=fun a y=>by
     obtain ⟨r,rfl⟩:=Ideal.Quotient.mk_surjective y;apply (RestrictScalars.addEquiv R T _).injective;change fRS (a*r) ⊗ₜ[T] (1:T ⧸ Δ)=algebraMap R T a•(fRS r ⊗ₜ[T] (1:T ⧸ Δ))
     rw [smul_tmul',map_mul];rfl }
  refine LinearEquiv.ofLinearMap e₀_fwd e₀_bwd ?_ ?_
  ·
   apply LinearMap.ext;intro y;obtain ⟨r,rfl⟩:=Ideal.Quotient.mk_surjective y;change ψ (fRS r) * πQ 1=Ideal.Quotient.mk Q r;rw [hψ_fRS,map_one,mul_one]
  ·
   apply LinearMap.ext;intro x;apply (RestrictScalars.addEquiv R T _).injective;let x':S ⊗[T] (T ⧸ Δ):=RestrictScalars.addEquiv R T _ x;change e₀_bwd0 (e₀_fwdT x')=x'
   induction x' using TensorProduct.induction_on with
   | zero=>rw [map_zero,map_zero]
   | tmul s u =>
    obtain ⟨t₁,rfl⟩:=Ideal.Quotient.mk_surjective s;obtain ⟨t₂,rfl⟩:=Ideal.Quotient.mk_surjective u;change e₀_bwd0 (Ideal.Quotient.mk Q (π t₁)*Ideal.Quotient.mk Q (π t₂))=qS t₁ ⊗ₜ[T] Ideal.Quotient.mk Δ t₂;rw [← map_mul (Ideal.Quotient.mk Q)];change fRS (π t₁ * π t₂) ⊗ₜ[T] (1:T ⧸ Δ)=qS t₁ ⊗ₜ[T] Ideal.Quotient.mk Δ t₂
    have q15:algebraMap R T (π (t₁ * t₂)) - t₁ * t₂ ∈ Δ := by
     change _∈ofList Δ_list;rw [← hker_π,RingHom.mem_ker,map_sub,hπ_alg,sub_self]
    have q11:Ideal.Quotient.mk Δ (algebraMap R T (π (t₁ * t₂)))=Ideal.Quotient.mk Δ (t₁ * t₂):=Ideal.Quotient.eq.mpr q15
    have hL:fRS (π t₁ * π t₂) ⊗ₜ[T] (1:T ⧸ Δ)=(1:S) ⊗ₜ[T] Ideal.Quotient.mk Δ (algebraMap R T (π (t₁ * t₂))):=by
     rw [← map_mul π]
     have : fRS (π (t₁ * t₂))=algebraMap R T (π (t₁ * t₂))•(1:S):=by
      change qS (algebraMap R T (π (t₁ * t₂)))=qS (algebraMap R T (π (t₁ * t₂)))*1;rw [mul_one]
     rw [this,smul_tmul];congr 1;change Ideal.Quotient.mk Δ (algebraMap R T (π (t₁ * t₂)))*1=_;rw [mul_one]
    have hR:qS t₁ ⊗ₜ[T] Ideal.Quotient.mk Δ t₂ = (1:S) ⊗ₜ[T] Ideal.Quotient.mk Δ (t₁ * t₂):=by
     have : qS t₁ = t₁ • (1:S):=by change qS t₁ = qS t₁ * 1;rw [mul_one]
     rw [this,smul_tmul];congr 1
    rw [hL,hR,q11]
   | add x₁ x₂ ih₁ ih₂=>rw [map_add,map_add,ih₁,ih₂]
 let qSA:S →+* A:=Ideal.Quotient.lift Q₂ qA (fun t ht =>
  Ideal.Quotient.eq_zero_iff_mem.mpr (hI.symm▸mem_sup_right ht))
 let qPA:(R⧸P) →+* A:=Ideal.Quotient.lift P (algebraMap R A) (fun r hr =>
  Ideal.Quotient.eq_zero_iff_mem.mpr (hI.symm▸mem_sup_left (mem_map_of_mem (algebraMap R T) hr)))
 let q5:(S ⊗[R] (R⧸P)) →ₗ[R] A :=
  TensorProduct.lift
   {
    toFun:=fun s =>
     {
      toFun:=fun u=>qSA s*qPA u
      map_add':=fun u₁ u₂=>by rw [map_add,mul_add]
      map_smul':=fun r u=>by
       rw [Algebra.smul_def,RingHom.id_apply,Algebra.smul_def,map_mul];change qSA s*(algebraMap R A r*qPA u)=algebraMap R A r*(qSA s*qPA u)
       ring }
    map_add':=fun s₁ s₂=>by apply LinearMap.ext;intro u;simp [map_add,add_mul]
    map_smul':=fun r s=>by
     apply LinearMap.ext;intro u;simp only [LinearMap.coe_mk,AddHom.coe_mk,LinearMap.smul_apply,RingHom.id_apply,Algebra.smul_def,map_mul];change (algebraMap R A r*qSA s)*qPA u=algebraMap R A r*(qSA s*qPA u)
     ring }
 let q12:(S ⊗[R] (R⧸P)) →ₗ[T] A :=
  {
   toFun:=q5
   map_add':=q5.map_add
   map_smul':=fun t x=>by
    induction x using TensorProduct.induction_on with
    | zero=>simp
    | tmul s u =>
     change qSA (qS t*s)*qPA u=qA t*(qSA s*qPA u);rw [map_mul];change (qA t*qSA s)*qPA u=_;ring
    | add x₁ x₂ ih₁ ih₂=>simp only [smul_add,map_add] at ih₁ ih₂ ⊢;rw [ih₁,ih₂] }
 let q10:A →ₗ[T] (S ⊗[R] (R⧸P)) :=
  Submodule.liftQ I
   {
    toFun:=fun t=>qS t ⊗ₜ[R] (1:R⧸P)
    map_add':=fun t₁ t₂=>by rw [map_add,add_tmul]
    map_smul':=fun t₁ t₂=>by
     change (t₁ • qS t₂) ⊗ₜ[R] (1:R⧸P)=t₁ • (qS t₂ ⊗ₜ[R] (1:R⧸P))
     rw [smul_tmul'] }
   (by
    rw [hI]
    refine sup_le ?_ ?_
    ·
     rw [map_le_iff_le_comap];intro r hr;rw [mem_comap,LinearMap.mem_ker];change qS (algebraMap R T r) ⊗ₜ[R] (1:R⧸P)=0
     have : qS (algebraMap R T r)=r•(1:S):=by rw [Algebra.smul_def,mul_one];rfl
     rw [this,smul_tmul]
     have h0:r•(1:R⧸P)=0:=by
      rw [Algebra.smul_def,mul_one];exact Ideal.Quotient.eq_zero_iff_mem.mpr hr
     rw [h0,tmul_zero]
    ·
     intro x hx;rw [LinearMap.mem_ker];change qS x ⊗ₜ[R] (1:R⧸P)=0
     rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx,zero_tmul])
 let eA:(S ⊗[R] (R⧸P)) ≃ₗ[T] A :=
  LinearEquiv.ofLinearMap q12 q10
   (by
    apply LinearMap.ext;intro a;obtain ⟨t,rfl⟩:=Ideal.Quotient.mk_surjective a;change qSA (qS t)*qPA 1=qA t
    rw [map_one,mul_one];rfl)
   (by
    apply LinearMap.ext;intro x
    induction x using TensorProduct.induction_on with
    | zero=>simp
    | tmul s u =>
     obtain ⟨t,rfl⟩:=Ideal.Quotient.mk_surjective s;obtain ⟨r,rfl⟩:=Ideal.Quotient.mk_surjective u;change q10 (qA t*qA (algebraMap R T r))=qS t ⊗ₜ[R] Ideal.Quotient.mk P r;rw [← map_mul];change qS (t*algebraMap R T r) ⊗ₜ[R] (1:R⧸P)=qS t ⊗ₜ[R] Ideal.Quotient.mk P r;rw [map_mul]
     have : qS t*qS (algebraMap R T r)=r•qS t:=by rw [Algebra.smul_def,mul_comm];rfl
     rw [this,smul_tmul];congr 1;rw [Algebra.smul_def,mul_one];rfl
    | add x₁ x₂ ih₁ ih₂ =>
     simp only [LinearMap.comp_apply,LinearMap.id_apply,map_add] at ih₁ ih₂ ⊢
     rw [ih₁,ih₂])
 have q1:(maximalIdeal A).comap qA=maximalIdeal T:=eq_maximalIdeal (comap_isMaximal_of_surjective qA Ideal.Quotient.mk_surjective)
 haveI : IsLocalHom (algebraMap R A):=by
  refine ⟨fun r hr => ?_⟩
  by_contra hnu
  have hrm:r∈maximalIdeal R:=(mem_maximalIdeal r).mpr hnu
  have ham:algebraMap R A r∈maximalIdeal A:=by
   change algebraMap R T r∈(maximalIdeal A).comap qA;rw [q1];exact q3 r hrm
  exact (mem_maximalIdeal (algebraMap R A r)).mp ham hr
 have hres_surj':Surjective (algebraMap (ResidueField R) (ResidueField A)):=fun y=>by
  obtain ⟨r,hr⟩:=q2 y;exact ⟨residue R r,hr⟩
 have q4:Module.length (ResidueField R) (ResidueField A)=1:=by
  let q14:ResidueField R ≃ₗ[ResidueField R] ResidueField A :=
   LinearEquiv.ofBijective (Algebra.linearMap (ResidueField R) (ResidueField A))
    ⟨(algebraMap (ResidueField R) (ResidueField A)).injective,hres_surj'⟩
  rw [← q14.length_eq,Module.length_eq_one]
 obtain ⟨e1⟩:=z145 (R:=R) (T:=T) (S:=S) (N:=T ⧸ Δ) (B:=R⧸Q)
  q8 e₀ i (R⧸P)
 obtain ⟨e2⟩:=z144 (T:=T) (N:=T ⧸ Δ) eA i;obtain ⟨e3⟩:=z114 Δ_list hΔ_reg A i;obtain ⟨e4⟩:=z135 (T:=T) (S:=A) (M:=A) Δ_list i
 let q13:z56 T (S ⊗[R] (R⧸P)) (T ⧸ Δ) i ≃ₗ[T]
   RestrictScalars T A (z94 A A (Δ_list.map qA) i) :=
  (e2.trans e3).trans e4
 let q9:z56 R (R⧸P) (R⧸Q) i ≃+ z94 A A (Δ_list.map qA) i :=
  (e1.toAddEquiv.trans (RestrictScalars.addEquiv R T _)).trans
   (q13.toAddEquiv.trans (RestrictScalars.addEquiv T A _))
 have q0:∀ (r:R) (x:z56 R (R⧸P) (R⧸Q) i),q9 (r•x)=algebraMap R A r•q9 x:=fun r x=>by
  change (RestrictScalars.addEquiv T A _) (q13 ((RestrictScalars.addEquiv R T _) (e1 (r•x))))=algebraMap R A r•(RestrictScalars.addEquiv T A _) (q13 ((RestrictScalars.addEquiv R T _) (e1 x)));rw [e1.map_smul];change (RestrictScalars.addEquiv T A _) (q13 (algebraMap R T r•(RestrictScalars.addEquiv R T _) (e1 x)))=_;rw [q13.map_smul];rfl
 exact z146 q9 q0 q4
private lemma z148
    {V:Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (maximalIdeal V) V] (p:V) (hp:maximalIdeal V=span {p})
    (n : ℕ) (P Q:Ideal (z0 V n)) [P.IsPrime] [Q.IsPrime]
    (hPQ:(P⊔Q).radical=maximalIdeal (z0 V n))
    (hpQ:z13 V n p∉Q) :
    0 ≤ intersectionMultiplicity (z0 V n) (z0 V n⧸P) (z0 V n⧸Q) ∧
    (ringKrullDim (z0 (z0 V n) n ⧸
      (P.map (z15 (z13 V n) n)⊔Q.map (z13 (z0 V n) n))) =
      (n:WithBot ℕ∞) →
      0 < intersectionMultiplicity (z0 V n) (z0 V n⧸P) (z0 V n⧸Q)):=by
  let R:=z0 V n;let T:=z0 R n;let i₁ : R →+* T:=z15 (z13 V n) n;let i₂ : R →+* T:=z13 R n;let I:Ideal T:=P.map i₁ ⊔ Q.map i₂;let A:=T⧸I;let qA:T →+* A:=Ideal.Quotient.mk I;let S:=T⧸Q.map i₂;let qS:T →+* S:=Ideal.Quotient.mk (Q.map i₂);have : IsLocalRing (R⧸Q):=z36 Q;have : IsAdicComplete (maximalIdeal (R⧸Q)) (R⧸Q):=z43 Q
  obtain ⟨eT,heT_C,heT_var,heT_symm_C,heT_symm_var⟩:=z47 R n (fun j=>z14 V j) (fun j=>z18 j)
  let Δ_list:List T:=(z124 R n).map eT.symm;let Δ : Ideal T:=ofList Δ_list
  have hΔ_reg:z110 T Δ_list:=z129 eT.symm (z124 R n)
    (z131 R n)
  let π : T →+* R:=(z48 R n).comp eT.toRingHom
  have hπ_i₂ : ∀ r:R,π (i₂ r)=r:=fun r=>by
    change z48 R n (eT (z13 R n r))=r;rw [heT_C,z49]
  have hπ_var:∀ j:Fin n,π (z14 R j)=z14 V j:=fun j=>by
    change z48 R n (eT (z14 R j))=z14 V j;rw [heT_var,map_add,z50,zero_add,z49]
  have hπ_i₁ : ∀ r:R,π (i₁ r)=r:=by
    have q29 : π.comp i₁ = RingHom.id R:=by
      refine z45 (C:=V) (n:=n) (π.comp i₁) (RingHom.id R)
        (fun c=>by
          change π (z15 (z13 V n) n (z13 V n c))=z13 V n c
          rw [z19];exact hπ_i₂ (z13 V n c))
        (fun j=>by
          change π (z15 (z13 V n) n (z14 V j))=z14 V j
          rw [z20];exact hπ_var j)
        (fun j=>by
          change π (z15 (z13 V n) n (z14 V j))∈maximalIdeal R
          rw [z20,hπ_var j];exact z18 j)
    exact fun r=>RingHom.congr_fun q29 r
  have hker_π : RingHom.ker π = Δ := by
    ext t;rw [RingHom.mem_ker];change eT t∈RingHom.ker (z48 R n)↔t∈ofList ((z124 R n).map eT.symm);rw [z51 R n,← z126 R n]
    have q32:ofList ((z124 R n).map eT.symm)=(ofList (z124 R n)).map eT.symm.toRingHom:=by
      rw [ofList,ofList,map_span];congr 1;ext y;simp
    rw [q32,mem_map_iff_of_surjective eT.symm.toRingHom eT.symm.surjective]
    exact ⟨fun ht=>⟨eT t,ht,eT.symm_apply_apply t⟩,fun ⟨u,hu,hut⟩=>by
      have hu':eT.symm u=t:=hut
      rw [← hu',eT.apply_symm_apply];exact hu⟩
  let eS:S ≃+* z0 (R⧸Q) n:=z27 Q n;let fRS:R →+* S:=qS.comp i₁
  have q5:letI : Algebra R S:=fRS.toAlgebra;Module.Flat R S:=by
    letI : Algebra R S:=fRS.toAlgebra
    let gV:V →+* R⧸Q:=(Ideal.Quotient.mk Q).comp (z13 V n)
    have q8:gV p∈maximalIdeal (R⧸Q):=by
      have q25:(maximalIdeal (R⧸Q)).comap (Ideal.Quotient.mk Q)=maximalIdeal R:=eq_maximalIdeal (comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective);change z13 V n p∈(maximalIdeal (R⧸Q)).comap (Ideal.Quotient.mk Q);rw [q25];exact z17 n (hp▸subset_span rfl)
    have q12:gV p≠0:=fun h0=>hpQ (Ideal.Quotient.eq_zero_iff_mem.mp h0)
    letI : Algebra R (z0 (R⧸Q) n):=(z15 gV n).toAlgebra
    have : Module.Flat R (z0 (R⧸Q) n):=z77 gV p hp q8 q12 n
    have q30:∀ r:R,eS (algebraMap R S r)=algebraMap R (z0 (R⧸Q) n) r:=by
      have heq:(eS.toRingHom.comp fRS)=z15 gV n:=by
        refine z45 (C:=V) (n:=n) (eS.toRingHom.comp fRS) (z15 gV n)
          (fun c=>by
            change eS (qS (i₁ (z13 V n c)))=z15 gV n (z13 V n c);rw [z19,z19];change z15 (Ideal.Quotient.mk Q) n (z13 R n (z13 V n c))=_
            rw [z19];rfl)
          (fun j=>by
            change eS (qS (i₁ (z14 V j)))=z15 gV n (z14 V j);rw [z20,z20];change z15 (Ideal.Quotient.mk Q) n (z14 R j)=_
            rw [z20])
          (fun j=>by
            change eS (qS (i₁ (z14 V j)))∈maximalIdeal (z0 (R⧸Q) n)
            rw [show eS (qS (i₁ (z14 V j)))=z14 (R⧸Q) j from by
              change z15 (Ideal.Quotient.mk Q) n (i₁ (z14 V j))=_
              rw [z20,z20]]
            exact z18 j)
      exact fun r=>RingHom.congr_fun heq r
    exact z74 (RingEquiv.refl R) eS q30
  have q23:∀ q : ℕ,Subsingleton (z56 T S (T ⧸ Δ) (q+1)):=by
    have q27:(maximalIdeal (R⧸Q)).comap (Ideal.Quotient.mk Q)=maximalIdeal R:=eq_maximalIdeal (comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
    have q7:∀ j:Fin n,Ideal.Quotient.mk Q (z14 V j)∈maximalIdeal (R⧸Q):=fun j=>by
      change z14 V j∈(maximalIdeal (R⧸Q)).comap (Ideal.Quotient.mk Q);rw [q27];exact z18 j
    obtain ⟨eS_shift,heSs_C,_,heSs_symm_C,heSs_symm_var⟩:=z47 (R⧸Q) n (fun j=>Ideal.Quotient.mk Q (z14 V j)) q7
    have q6:∀ t:T,eS (qS (eT.symm t))=eS_shift.symm (eS (qS t)):=by
      have heq:(eS.toRingHom.comp qS).comp eT.symm.toRingHom=eS_shift.symm.toRingHom.comp (eS.toRingHom.comp qS):=by
        refine z45 (C:=R) (n:=n) _ _
          (fun r=>by
            simp only [RingHom.comp_apply,RingEquiv.toRingHom_eq_coe,RingHom.coe_coe,heT_symm_C];change z15 (Ideal.Quotient.mk Q) n (z13 R n r)=eS_shift.symm (z15 (Ideal.Quotient.mk Q) n (z13 R n r))
            rw [z19,heSs_symm_C])
          (fun j=>by
            simp only [RingHom.comp_apply,RingEquiv.toRingHom_eq_coe,RingHom.coe_coe,heT_symm_var,
              map_sub]
            change z15 (Ideal.Quotient.mk Q) n (z14 R j) -
                z15 (Ideal.Quotient.mk Q) n (z13 R n (z14 V j)) =
              eS_shift.symm (z15 (Ideal.Quotient.mk Q) n (z14 R j))
            rw [z20,z19,heSs_symm_var])
          (fun j=>by
            simp only [RingHom.comp_apply,RingEquiv.toRingHom_eq_coe,RingHom.coe_coe,heT_symm_var,
              map_sub]
            change z15 (Ideal.Quotient.mk Q) n (z14 R j) -
                z15 (Ideal.Quotient.mk Q) n (z13 R n (z14 V j)) ∈
              maximalIdeal (z0 (R⧸Q) n)
            rw [z20,z19]
            exact (maximalIdeal (z0 (R⧸Q) n)).sub_mem (z18 j)
              (z17 n (q7 j)))
      exact fun t=>RingHom.congr_fun heq t
    have q0:∀ m : ℕ,(z124 R m).map (z15 (Ideal.Quotient.mk Q) m)=z124 (R⧸Q) m:=by
      intro m
      induction m with
      | zero=>rfl
      | succ m ihm =>
        simp only [z124,List.map_cons,List.map_map];congr 1
        · exact PowerSeries.map_X _
        · rw [← ihm,List.map_map]
          congr 1;funext x;change PowerSeries.map (z15 (Ideal.Quotient.mk Q) m) (PowerSeries.C x)=PowerSeries.C (z15 (Ideal.Quotient.mk Q) m x);exact PowerSeries.map_C (z15 (Ideal.Quotient.mk Q) m) x
    have hΔS_eq : Δ_list.map qS=(z124 (R⧸Q) n).map (eS_shift.symm.trans eS.symm):=by
      have h1:(z124 R n).map (fun t=>eS (qS (eT.symm t)))=(z124 (R⧸Q) n).map eS_shift.symm:=by
        rw [← q0 n,List.map_map]
        refine List.map_congr_left fun t _ => ?_
        exact q6 t
      calc Δ_list.map qS=(z124 R n).map (fun t=>eS.symm (eS (qS (eT.symm t)))):=by
            simp only [Δ_list,List.map_map];refine List.map_congr_left fun t _ => ?_;simp
        _=((z124 R n).map (fun t=>eS (qS (eT.symm t)))).map eS.symm:=by rw [List.map_map];rfl
        _=((z124 (R⧸Q) n).map eS_shift.symm).map eS.symm:=by rw [h1]
        _=(z124 (R⧸Q) n).map (eS_shift.symm.trans eS.symm):=by rw [List.map_map];rfl
    have q14:z110 S (Δ_list.map qS):=by
      rw [hΔS_eq]
      exact z129 (eS_shift.symm.trans eS.symm) (z124 (R⧸Q) n)
        (z131 (R⧸Q) n)
    have q13:z110 (R:=T) S Δ_list:=z130 Δ_list S q14;intro q;obtain ⟨e⟩:=z114 Δ_list hΔ_reg S (q+1);have : Subsingleton (z94 T S Δ_list (q+1)):=z111 Δ_list S q13 q;exact e.toEquiv.subsingleton
  have hi₁_loc:∀ r∈maximalIdeal R,i₁ r∈maximalIdeal T:=fun r hr =>
    z23 (fun c hc=>z17 n hc) n hr
  have q3:I ≤ maximalIdeal T:=by
    refine sup_le ?_ ?_
    · rw [map_le_iff_le_comap]
      intro r hr;exact hi₁_loc r (le_maximalIdeal ‹P.IsPrime›.ne_top hr)
    · rw [map_le_iff_le_comap]
      intro r hr;exact z17 n (le_maximalIdeal ‹Q.IsPrime›.ne_top hr)
  have q2:I ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal T).ne_top q3;have : Nontrivial A:=Ideal.Quotient.nontrivial_iff.mpr q2;have : IsLocalRing A:=z36 I;have q1:(maximalIdeal A).comap qA=maximalIdeal T:=eq_maximalIdeal (comap_isMaximal_of_surjective qA Ideal.Quotient.mk_surjective)
  have q4:Surjective ((residue A).comp (qA.comp i₁)):=by
    intro y;obtain ⟨a,rfl⟩:=residue_surjective y;obtain ⟨t,rfl⟩:=Ideal.Quotient.mk_surjective a;obtain ⟨r,hr⟩:=z35 (C:=R) n (residue T t)
    refine ⟨r,?_⟩
    change residue A (qA (i₁ r))=residue A (qA t);rw [← sub_eq_zero,← map_sub,residue_eq_zero_iff,← map_sub,← mem_comap,q1]
    have q18:i₁ r - i₂ r∈maximalIdeal T:=by
      have hΔ_le : Δ ≤ maximalIdeal T:=by
        change ofList Δ_list ≤ maximalIdeal T;rw [ofList,span_le];intro w hw;rw [Set.mem_setOf_eq,List.mem_map] at hw;obtain ⟨v,hv,rfl⟩:=hw;have q22:v∈maximalIdeal T:=z127 R n v hv
        by_contra hnu
        have hu:IsUnit (eT.symm v):=by
          by_contra h;exact hnu ((mem_maximalIdeal (eT.symm v)).mpr h)
        have q33:IsUnit v:=by
          have:=hu.map eT.toRingHom;simpa using this
        exact (mem_maximalIdeal v).mp q22 q33
      exact hΔ_le (by rw [← hker_π,RingHom.mem_ker,map_sub,hπ_i₁,hπ_i₂,sub_self])
    have q24:i₂ r - t∈maximalIdeal T:=by
      rw [← residue_eq_zero_iff,map_sub];change ((residue T).comp (z13 R n)) r - residue T t=0;rw [hr,sub_self]
    have : i₁ r - t=(i₁ r - i₂ r)+(i₂ r - t):=by ring
    rw [this];exact (maximalIdeal T).add_mem q18 q24
  let Δ_A:List A := Δ_list.map qA
  have hΔ_A_len : Δ_A.length=n:=by simp [Δ_A,Δ_list,z125]
  have hΔ_A_max:∀ z ∈ Δ_A,z∈maximalIdeal A:=fun z hz=>by
    rw [List.mem_map] at hz;obtain ⟨w,hw,rfl⟩:=hz;rw [List.mem_map] at hw;obtain ⟨v,hv,rfl⟩:=hw;have q22:v∈maximalIdeal T:=z127 R n v hv
    have q21:eT.symm v∈maximalIdeal T:=by
      by_contra hnu
      have hu:IsUnit (eT.symm v):=by
        by_contra h;exact hnu ((mem_maximalIdeal (eT.symm v)).mpr h)
      have q33:IsUnit v:=by
        have:=hu.map eT.toRingHom;simpa using this
      exact (mem_maximalIdeal v).mp q22 q33
    change eT.symm v∈(maximalIdeal A).comap qA;rw [q1];exact q21
  have hΔ_A_rad:(annihilator A A⊔ofList Δ_A).radical=maximalIdeal A:=by
    have q26:annihilator A A = ⊥ := by
      ext a;simp only [Module.mem_annihilator,Ideal.mem_bot]
      exact ⟨fun h=>by simpa using h 1,fun h x=>by rw [h,zero_smul]⟩
    rw [q26,bot_sup_eq]
    refine le_antisymm ?_ ?_
    · rw [(maximalIdeal.isMaximal A).isPrime.radical_le_iff,ofList,span_le]
      exact fun z hz=>hΔ_A_max z hz
    · intro a ha
      obtain ⟨t,rfl⟩:=Ideal.Quotient.mk_surjective a;have q20:t∈maximalIdeal T:=q1▸ha
      have hπt_max : π t∈maximalIdeal R:=by
        have q17:eT t∈maximalIdeal T:=by
          by_contra hnu
          have hu:IsUnit (eT t):=by
            by_contra h;exact hnu ((mem_maximalIdeal (eT t)).mpr h)
          have q31:IsUnit t:=by
            have:=hu.map eT.symm.toRingHom;simpa using this
          exact (mem_maximalIdeal t).mp q20 q31
        have q15:∀ m : ℕ,∀ f∈maximalIdeal (z0 R m),z48 R m f∈maximalIdeal R:=by
          intro m
          induction m with
          | zero=>exact fun f hf=>hf
          | succ m ihm =>
            intro f hf;exact ihm (PowerSeries.constantCoeff f) ((z3 f).mp hf)
        exact q15 n (eT t) q17
      rw [← hPQ] at hπt_max;obtain ⟨k,hk⟩:=hπt_max;rw [Submodule.mem_sup] at hk;obtain ⟨p',hp',q',hq',hpq⟩:=hk;let d:T:=t ^ k - (i₁ p'+i₂ q')
      have q19:d ∈ Δ := by
        rw [← hker_π,RingHom.mem_ker];dsimp only [d];rw [map_sub,map_add,map_pow,hπ_i₁,hπ_i₂,← hpq,sub_self]
      have hmap_Δ : ofList Δ_A = Δ.map qA:=by
        change ofList Δ_A=(ofList Δ_list).map qA;rw [ofList,ofList,map_span];congr 1;ext y;simp [Δ_A]
      refine ⟨k,?_⟩
      rw [hmap_Δ,← map_pow]
      have q35:qA (t ^ k)=qA d:=by
        dsimp only [d];rw [map_sub,map_add,Ideal.Quotient.eq_zero_iff_mem.mpr (mem_sup_left (mem_map_of_mem i₁ hp')),Ideal.Quotient.eq_zero_iff_mem.mpr (mem_sup_right (mem_map_of_mem i₂ hq')),add_zero,sub_zero]
      rw [q35];exact mem_map_of_mem qA q19
  have hQ₂_le:Q.map i₂ ≤ RingHom.ker ((Ideal.Quotient.mk Q).comp π):=by
    rw [map_le_iff_le_comap];intro q hq;rw [mem_comap,RingHom.mem_ker,RingHom.comp_apply,hπ_i₂];exact Ideal.Quotient.eq_zero_iff_mem.mpr hq
  have q11:∀ q∈Q,∃ d∈ofList Δ_list,qS (i₁ q)=qS d:=fun q hq =>
    ⟨i₁ q - i₂ q,by change i₁ q - i₂ q ∈ Δ;rw [← hker_π,RingHom.mem_ker,map_sub,hπ_i₁,hπ_i₂,sub_self],by
      rw [map_sub,Ideal.Quotient.eq_zero_iff_mem.mpr (mem_map_of_mem i₂ hq),sub_zero]⟩
  have q16:∀ i : ℕ,Module.length R (z56 R (R⧸P) (R⧸Q) i)=Module.length A (z94 A A Δ_A i) :=
    @z147 R T _ _ _ _ _ _ i₁.toAlgebra P Q (Q.map i₂) I rfl ‹IsLocalRing A›
      Δ_list π hπ_i₁ hker_π hQ₂_le q11 hΔ_reg q5 q23 hi₁_loc q4
  obtain ⟨_,hchi_zero,hchi_pos⟩:=z123 Δ_A hΔ_A_max A (Or.inl hΔ_A_rad)
  have q10:intersectionMultiplicity R (R⧸P) (R⧸Q)=z115 A A Δ_A:=by
    unfold intersectionMultiplicity z115;rw [hΔ_A_len]
    rw [finsum_eq_sum_of_support_subset _ (s:=Finset.range (n+1))]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [q16 i]
    · intro i hi
      simp only [Function.mem_support,ne_eq] at hi;rw [Finset.coe_range,Set.mem_Iio]
      by_contra hge
      push Not at hge
      have hgt : Δ_A.length < i:=by omega
      have : Subsingleton (z94 A A Δ_A i):=z95 Δ_A i hgt
      have h0:Module.length R (z56 R (R⧸P) (R⧸Q) i)=0:=by
        rw [q16 i,Module.length_eq_zero]
      exact hi (by rw [h0];simp)
  rw [q10]
  refine ⟨?_, fun q28 => hchi_pos (by rw [hΔ_A_len, Module.supportDim_self_eq_ringKrullDim, q28])⟩
  have hleA : supportDim A A ≤ (Δ_A.length : WithBot ℕ∞) := by
    rw [hΔ_A_len, Module.supportDim_self_eq_ringKrullDim]
    exact z53 (Λ := V) n P Q hPQ
  rcases hleA.lt_or_eq with hlt | heq
  · rw [hchi_zero hlt]
  · exact (hchi_pos heq).le
lemma z149 {V:Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [IsAdicComplete (maximalIdeal V) V] (p:V) (hp:maximalIdeal V=span {p})
  (n : ℕ) (P Q:Ideal (z0 V n)) [P.IsPrime] [Q.IsPrime]
  (hPQ:(P⊔Q).radical=maximalIdeal (z0 V n)) :
  ringKrullDim (z0 V n⧸P)+ringKrullDim (z0 V n⧸Q) ≤
   ringKrullDim (z0 V n) ∧
  (ringKrullDim (z0 V n⧸P)+ringKrullDim (z0 V n⧸Q) =
   ringKrullDim (z0 V n) →
   0 < intersectionMultiplicity (z0 V n)
    (z0 V n⧸P) (z0 V n⧸Q)):=by
 have h1:=z55 p hp n P Q hPQ
 refine ⟨h1.1,fun heq => ?_⟩
 obtain ⟨hor,hdimA⟩:=h1.2 heq
 rcases hor with hpP | hpQ
 ·
  have hQP:(Q⊔P).radical=maximalIdeal (z0 V n):=by rwa [sup_comm]
  have heq':ringKrullDim (z0 V n⧸Q)+ringKrullDim (z0 V n⧸P) =
    ringKrullDim (z0 V n):=by rw [add_comm];exact heq
  have hdimA':=((z55 p hp n Q P hQP).2 heq').2;rw [z72];exact (z148 p hp n Q P hQP hpP).2 hdimA'
 · exact (z148 p hp n P Q hPQ hpQ).2 hdimA
end DiagonalTorAndPositivity
private lemma z228 {R' R M' M:Type}
  [CommRing R'] [CommRing R] [AddCommGroup M'] [Module R' M'] [AddCommGroup M] [Module R M]
  (e:R' ≃+* R) (f:M' ≃+ M) (q0:∀ (r:R') (x:M'),f (r•x)=e r•f x) :
  Module.length R' M'=Module.length R M:=by
 letI : Algebra R' R:=e.toRingHom.toAlgebra
 letI : Module R' M:=Module.restrictScalars R' R M
 haveI : IsScalarTower R' R M:=IsScalarTower.restrictScalars R' R M
 let fL:M' ≃ₗ[R'] M :=
  {
   toFun:=f
   invFun:=f.symm
   left_inv:=f.left_inv
   right_inv:=f.right_inv
   map_add':=f.map_add
   map_smul':=fun r x=>q0 r x }
 rw [fL.length_eq]
 exact Module.length_eq_of_surjective (S:=R') (R:=R) (M:=M) e.surjective
private lemma z229 {R' R:Type}
  [CommRing R'] [IsNoetherianRing R'] [CommRing R]
  (e:R' ≃+* R) (P Q:Ideal R) :
  intersectionMultiplicity R' (R'⧸P.comap e.toRingHom) (R'⧸Q.comap e.toRingHom) =
  intersectionMultiplicity R (R⧸P) (R⧸Q):=by
 let P':Ideal R':=P.comap e.toRingHom;let Q':Ideal R':=Q.comap e.toRingHom
 letI : Algebra R' R:=e.toRingHom.toAlgebra
 let q6:R' ≃ₗ[R'] R :=
  {
   toFun:=e
   invFun:=e.symm
   left_inv:=e.left_inv
   right_inv:=e.right_inv
   map_add':=e.map_add
   map_smul':=fun r x=>by
    change e (r*x)=e r*e x
    rw [map_mul] }
 haveI : Module.Flat R' R:=Module.Flat.of_linearEquiv q6.symm
 have q2:∀ q : ℕ,Subsingleton (z56 R R (R⧸Q) (q+1)):=fun q=>z67 (R:=R) (M:=R) (N:=R⧸Q) q
 have hQ_eq:Q'=Q.comap e.toRingHom:=rfl;let q1:(R'⧸Q') ≃+* (R⧸Q):=Ideal.quotientEquiv Q' Q e (Ideal.map_comap_of_surjective e.toRingHom e.surjective Q).symm
 let e₀_aux:RestrictScalars R' R (R⧸Q) ≃ₗ[R'] (R'⧸Q') :=
  {
   toFun:=fun x=>q1.symm (RestrictScalars.addEquiv R' R (R⧸Q) x)
   invFun:=fun y=>(RestrictScalars.addEquiv R' R (R⧸Q)).symm (q1 y)
   left_inv:=fun x=>by
    apply (RestrictScalars.addEquiv R' R (R⧸Q)).injective;simp
   right_inv:=fun y=>by simp
   map_add':=fun x₁ x₂=>by simp
   map_smul':=fun r x=>by
    have h1:∀ y:R⧸Q,q1.symm (e r•y)=r•q1.symm y:=fun y=>by
     obtain ⟨a,rfl⟩:=Ideal.Quotient.mk_surjective y;apply q1.injective;rw [q1.apply_symm_apply];change Ideal.Quotient.mk Q (e r)*Ideal.Quotient.mk Q a=q1 (Ideal.Quotient.mk Q' r*q1.symm (Ideal.Quotient.mk Q a));rw [map_mul,q1.apply_symm_apply];rfl
    exact h1 (RestrictScalars.addEquiv R' R (R⧸Q) x) }
 let e₀ : RestrictScalars R' R (R ⊗[R] (R⧸Q)) ≃ₗ[R'] (R'⧸Q'):=(z136 R' R (TensorProduct.lid R (R⧸Q))).trans e₀_aux
 haveI : Module.Finite R' (R'⧸P'):=Module.Finite.of_surjective (Ideal.Quotient.mkₐ R' P').toLinearMap Ideal.Quotient.mk_surjective
 let q0:(R'⧸P') ≃+* (R⧸P):=Ideal.quotientEquiv P' P e (Ideal.map_comap_of_surjective e.toRingHom e.surjective P).symm
 let eP_fwdR':(R ⊗[R'] (R'⧸P')) →ₗ[R'] (R⧸P) :=
  TensorProduct.lift
   {
    toFun:=fun r =>
     {
      toFun:=fun u=>Ideal.Quotient.mk P r*q0 u
      map_add':=fun u₁ u₂=>by rw [map_add,mul_add]
      map_smul':=fun a u=>by
       change Ideal.Quotient.mk P r*q0 (Ideal.Quotient.mk P' a*u)=Ideal.Quotient.mk P (e a)*(Ideal.Quotient.mk P r*q0 u);rw [map_mul];change Ideal.Quotient.mk P r*(Ideal.Quotient.mk P (e a)*q0 u)=_
       ring }
    map_add':=fun r₁ r₂=>by apply LinearMap.ext;intro u;simp [map_add,add_mul]
    map_smul':=fun a r=>by
     apply LinearMap.ext;intro u;change Ideal.Quotient.mk P (e a*r)*q0 u=Ideal.Quotient.mk P (e a)*(Ideal.Quotient.mk P r*q0 u)
     rw [map_mul,mul_assoc] }
 let q3:(R ⊗[R'] (R'⧸P')) →ₗ[R] (R⧸P) :=
  {
   toFun:=eP_fwdR'
   map_add':=eP_fwdR'.map_add
   map_smul':=fun r x=>by
    induction x using TensorProduct.induction_on with
    | zero=>simp
    | tmul s u =>
     change Ideal.Quotient.mk P (r*s)*q0 u=Ideal.Quotient.mk P r*(Ideal.Quotient.mk P s*q0 u);rw [map_mul,mul_assoc]
    | add x₁ x₂ ih₁ ih₂=>simp only [smul_add,map_add] at ih₁ ih₂ ⊢;rw [ih₁,ih₂] }
 let q4:(R⧸P) →ₗ[R] (R ⊗[R'] (R'⧸P')) :=
  Submodule.liftQ P
   {
    toFun:=fun r=>r ⊗ₜ[R'] (1:R'⧸P')
    map_add':=fun r₁ r₂=>add_tmul r₁ r₂ 1
    map_smul':=fun r₁ r₂=>by
     change (r₁ * r₂) ⊗ₜ[R'] (1:R'⧸P')=r₁ • (r₂ ⊗ₜ[R'] (1:R'⧸P'))
     rw [smul_tmul'];rfl }
   (fun r hr=>by
    rw [LinearMap.mem_ker];change r ⊗ₜ[R'] (1:R'⧸P')=0
    have hr':e.symm r∈P':=by
     change e (e.symm r)∈P;rwa [e.apply_symm_apply]
    have h1:r=e.symm r•(1:R):=by
     change r=e (e.symm r)*1;rw [mul_one,e.apply_symm_apply]
    rw [h1,smul_tmul]
    have h2:e.symm r•(1:R'⧸P')=0:=by
     change Ideal.Quotient.mk P' (e.symm r)*1=0;rw [mul_one,Ideal.Quotient.eq_zero_iff_mem];exact hr'
    rw [h2,tmul_zero])
 let eP:(R ⊗[R'] (R'⧸P')) ≃ₗ[R] (R⧸P) :=
  LinearEquiv.ofLinearMap q3 q4
   (by
    apply LinearMap.ext;intro y;obtain ⟨r,rfl⟩:=Ideal.Quotient.mk_surjective y;change Ideal.Quotient.mk P r*q0 1=Ideal.Quotient.mk P r
    rw [map_one,mul_one])
   (by
    apply LinearMap.ext;intro x
    induction x using TensorProduct.induction_on with
    | zero=>simp
    | tmul r u =>
     obtain ⟨a,rfl⟩:=Ideal.Quotient.mk_surjective u;change (r*e a) ⊗ₜ[R'] (1:R'⧸P')=r ⊗ₜ[R'] Ideal.Quotient.mk P' a
     have h1:r*e a=a•r:=by change r*e a=e a*r;ring
     rw [h1,smul_tmul];congr 1;change Ideal.Quotient.mk P' a*1=Ideal.Quotient.mk P' a;rw [mul_one]
    | add x₁ x₂ ih₁ ih₂=>simp only [map_add] at ih₁ ih₂ ⊢;rw [ih₁,ih₂])
 have q7:∀ i : ℕ,Module.length R' (z56 R' (R'⧸P') (R'⧸Q') i)=Module.length R (z56 R (R⧸P) (R⧸Q) i):=fun i=>by
  obtain ⟨e1⟩:=z145 (R:=R') (T:=R) (S:=R) (N:=R⧸Q) (B:=R'⧸Q')
   q2 e₀ i (R'⧸P')
  obtain ⟨e2⟩:=z144 (T:=R) (N:=R⧸Q) eP i;let q5:z56 R' (R'⧸P') (R'⧸Q') i ≃+ z56 R (R⧸P) (R⧸Q) i:=(e1.toAddEquiv.trans (RestrictScalars.addEquiv R' R _)).trans e2.toAddEquiv
  refine z228 e q5 fun r x => ?_
  change e2 (RestrictScalars.addEquiv R' R _ (e1 (r•x)))=e r•e2 (RestrictScalars.addEquiv R' R _ (e1 x));rw [e1.map_smul];change e2 (e r•RestrictScalars.addEquiv R' R _ (e1 x))=_;exact e2.map_smul (e r) _
 unfold intersectionMultiplicity
 refine finsum_congr fun i => ?_
 rw [q7 i]
noncomputable def powerSeriesMapEquiv {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) :
    PowerSeries A ≃+* PowerSeries B where
  toFun := PowerSeries.map e.toRingHom
  invFun := PowerSeries.map e.symm.toRingHom
  left_inv f := by ext k; simp
  right_inv g := by ext k; simp
  map_mul' := map_mul _
  map_add' := map_add _
noncomputable def mvPowerSeriesIterEquiv (V : Type) [CommRing V] :
    ∀ n : ℕ, MvPowerSeries (Fin n) V ≃+* z0 V n
  | 0 => (MvPowerSeries.isEmptyEquiv (Fin 0) V).toRingEquiv
  | n + 1 =>
    (MvPowerSeries.finSuccEquiv V n).toRingEquiv.trans
      (powerSeriesMapEquiv (mvPowerSeriesIterEquiv V n))
theorem serre_h4_unramified_main :
    OMA.R_SerreMultiplicityConjectures_intersectionMultiplicity_pos_of_unramified_R1.H4 := by
  intro V _ _ _ _ n _ P Q _ _ hfin
  let T := MvPowerSeries (Fin n) V
  obtain ⟨p, hp_irr⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hp : maximalIdeal V = Ideal.span {p} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer p).mp hp_irr
  have hPQ : (P ⊔ Q).radical = maximalIdeal T := by
    refine le_antisymm ?_ ?_
    · rw [← Ideal.IsPrime.radical (IsLocalRing.maximalIdeal.isMaximal T).isPrime]
      exact Ideal.radical_mono (sup_le (IsLocalRing.le_maximalIdeal ‹P.IsPrime›.ne_top)
        (IsLocalRing.le_maximalIdeal ‹Q.IsPrime›.ne_top))
    · rw [Ideal.radical_eq_sInf, le_sInf_iff]
      intro r ⟨hPQr, hrPrime⟩
      let rp : PrimeSpectrum T := ⟨r, hrPrime⟩
      have _ : Module.Finite T (T ⧸ P) :=
        Module.Finite.of_surjective (Submodule.mkQ P) (Submodule.mkQ_surjective P)
      have _ : Module.Finite T (T ⧸ Q) :=
        Module.Finite.of_surjective (Submodule.mkQ Q) (Submodule.mkQ_surjective Q)
      have hrP : rp ∈ Module.support T (T ⧸ P) := by
        rw [Module.mem_support_iff_of_finite, Ideal.annihilator_quotient]
        exact le_sup_left.trans hPQr
      have hrQ : rp ∈ Module.support T (T ⧸ Q) := by
        rw [Module.mem_support_iff_of_finite, Ideal.annihilator_quotient]
        exact le_sup_right.trans hPQr
      have hrPQ : rp ∈ Module.support T ((T ⧸ P) ⊗[T] (T ⧸ Q)) :=
        mem_support_tensorProduct_of_mem hrP hrQ
      have hr_eq : rp = IsLocalRing.closedPoint T :=
        support_subset_closedPoint_of_isFiniteLength hfin hrPQ
      exact (congrArg PrimeSpectrum.asIdeal hr_eq).ge
  let R := z0 V n
  let e : R ≃+* T := (mvPowerSeriesIterEquiv V n).symm
  have _ : IsRegularLocalRing R := IsRegularLocalRing.of_ringEquiv e.symm
  let P' : Ideal R := P.comap e.toRingHom
  let Q' : Ideal R := Q.comap e.toRingHom
  have _ : P'.IsPrime := Ideal.IsPrime.comap e.toRingHom
  have _ : Q'.IsPrime := Ideal.IsPrime.comap e.toRingHom
  have hmax_comap : (maximalIdeal T).comap e.toRingHom = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective e.toRingHom e.surjective)
  have hPQ' : (P' ⊔ Q').radical = maximalIdeal R := by
    have hsup : P' ⊔ Q' = (P ⊔ Q).comap e.toRingHom := by
      ext x
      simp only [Ideal.mem_comap, Submodule.mem_sup, P', Q']
      constructor
      · rintro ⟨a, ha, b, hb, rfl⟩
        exact ⟨e a, ha, e b, hb, (map_add e a b).symm⟩
      · rintro ⟨a, ha, b, hb, hab⟩
        refine ⟨e.symm a, by simpa using ha, e.symm b, by simpa using hb, ?_⟩
        apply e.injective
        rw [map_add, e.apply_symm_apply, e.apply_symm_apply, hab]; rfl
    rw [hsup, ← Ideal.comap_radical, hPQ, hmax_comap]
  have hmapP : P'.map e.toRingHom = P :=
    Ideal.map_comap_of_surjective e.toRingHom e.surjective P
  have hmapQ : Q'.map e.toRingHom = Q :=
    Ideal.map_comap_of_surjective e.toRingHom e.surjective Q
  have hdP : ringKrullDim (R ⧸ P') = ringKrullDim (T ⧸ P) :=
    ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv P' P e hmapP.symm)
  have hdQ : ringKrullDim (R ⧸ Q') = ringKrullDim (T ⧸ Q) :=
    ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv Q' Q e hmapQ.symm)
  have hdR : ringKrullDim R = ringKrullDim T :=
    ringKrullDim_eq_of_ringEquiv e
  have hchi_eq :
      Module.intersectionMultiplicity R (R ⧸ P') (R ⧸ Q') =
        Module.intersectionMultiplicity T (T ⧸ P) (T ⧸ Q) :=
    z229 e P Q
  rw [← hchi_eq, ← hdP, ← hdQ, ← hdR]
  refine ⟨?_, (z149 p hp n P' Q' hPQ').2⟩
  by_cases hgQ : z13 V n p ∈ Q'
  · by_cases hgP : z13 V n p ∈ P'
    · let g : R := z13 V n p
      have hg_mem : g ∈ maximalIdeal R := z17 n (hp ▸ subset_span rfl)
      have hg_ne : g ≠ 0 := fun h0 =>
        hp_irr.ne_zero (z16 V n (h0.trans (map_zero _).symm))
      have hspan_eq : Ideal.span {g} = (maximalIdeal V).map (z13 V n) := by
        rw [hp, Ideal.map_span, Set.image_singleton]
      let k := V ⧸ maximalIdeal V
      let _ : Field k := Ideal.Quotient.field (maximalIdeal V)
      let eBar : (R ⧸ Ideal.span {g}) ≃+* z0 k n :=
        (Ideal.quotEquivOfEq hspan_eq).trans (z27 (maximalIdeal V) n)
      have hRbar_reg : IsRegularLocalRing (R ⧸ Ideal.span {g}) :=
        IsRegularLocalRing.of_ringEquiv eBar.symm
      have hzero := SerreHypersurfaceVanishing.serre_h4_main R g hg_mem hg_ne hRbar_reg
        P' Q' hgP hgQ hPQ'
      rw [hzero]
    · have hQP' : (Q' ⊔ P').radical = maximalIdeal R := by rwa [sup_comm]
      rw [z72 (R ⧸ P') (R ⧸ Q')]
      exact (z148 p hp n Q' P' hQP' hgP).1
  · exact (z148 p hp n P' Q' hPQ' hgQ).1
end SerrePositivity
theorem OMA.solution :
    OMA.R_SerreMultiplicityConjectures_intersectionMultiplicity_pos_of_unramified_R1.H4 :=
  SerrePositivity.serre_h4_unramified_main
