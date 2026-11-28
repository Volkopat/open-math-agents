import OMAReductions.R_SerreMultiplicityConjectures_intersectionMultiplicity_pos_of_equalCharacteristic_R1
import Mathlib

-- Port of proofs/SerreMultiplicityConjectures.intersectionMultiplicity_pos_of_unramified.R1.H2.lean by its author onto the identical hypothesis statement of this step.

/-!
Additivity of Serre intersection multiplicity on short exact sequences of finite modules
over a regular local ring.
-/

open IsLocalRing Module Ideal CategoryTheory Limits MonoidalCategory TensorProduct Function

namespace SerreTorSESAdditivity


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

/-- Every regular local ring is an integral domain. -/
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

/-- Existence of a finite projective resolution of length at most `d`. -/
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

/-- Schanuel's Lemma for two surjective linear maps from projective modules. -/
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

/-- Helper equivalence `S ⊗[R] (Fin r → R) ≃ₗ[S] (Fin r → S)`. -/
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

/-- Helper map `(R ⧸ I) ⊗[R] M →ₗ[R] M ⧸ (I • ⊤)` detecting membership in `I • ⊤`. -/
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

/-- Tensoring with `ResidueField R` detects zero finitely generated modules over a local ring. -/
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

/-- Over a local ring, a finitely generated projective module is isomorphic to `Fin r → R`. -/
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

/-- Every finitely generated module over a regular local ring has a finite projective resolution
of length at most `dim R`. -/
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
    -- Step 1: Cover N by a finite free R-module F, with kernel K (which is x-regular!)
    obtain ⟨r₀, f₀, hf₀⟩ := exists_finite_free_surj (R := R) N
    let F₀ := Fin r₀ → R
    let K := LinearMap.ker f₀
    let _ : IsNoetherian R F₀ := isNoetherian_of_isNoetherianRing_of_finite R F₀
    let _ : Module.Finite R K := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
    have hK_reg : ∀ y : K, x • y = 0 → y = 0 := fun y hy => by
      ext i
      have hi : x * y.val i = 0 := congrFun (congrArg Subtype.val hy) i
      exact (mul_eq_zero.mp hi).resolve_left hx_ne
    -- Step 2: Prove by inner induction on m that any f.g. x-regular R-module M with
    -- HasFiniteProjRes (R ⧸ I) m ((R ⧸ I) ⊗[R] M) satisfies HasFiniteProjRes R m M!
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

/-- Abbreviation for `Tor_i^R(M, N)` in `ModuleCat.{0} R`. -/
noncomputable abbrev torMod (R : Type) [CommRing R]
    (M N : Type) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (i : ℕ) : ModuleCat.{0} R :=
  ((Tor (ModuleCat.{0} R) i).obj (ModuleCat.of R M)).obj (ModuleCat.of R N)

/-- Functorial map on `Tor_i^R(M, -)` induced by a linear map `f : A →ₗ[R] B`. -/
noncomputable def torMap {R : Type} [CommRing R]
    (M : Type) [AddCommGroup M] [Module R M]
    {A B : Type} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (f : A →ₗ[R] B) (i : ℕ) :
    torMod R M A i →ₗ[R] torMod R M B i :=
  (((Tor (ModuleCat.{0} R) i).obj (ModuleCat.of R M)).map (ModuleCat.ofHom f)).hom

/-- `Tor_0^R(M, N) ≃ₗ[R] M ⊗[R] N`. -/
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

/-- Build a `ProjectiveResolution` from a projective chain complex whose `H_0` is `B` via `ε`
and `H_{n+1} = 0`. -/
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
      -- In degree 0, both K.sc 0 and single₀.sc 0 have g = 0, so homologyι is an iso to opcycles!
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

/-- Exactness of `torMap` and connecting homomorphism for a short exact sequence `0 → A → B → C → 0`. -/
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
    -- Since PX.isColimitCokernelCofork is a colimit, the canonical quotient map factors through π.f 0!
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
  -- Lift εC to s0 : PC.X 0 → B with p ∘ s0 = εC
  let _ := hPC_proj 0
  obtain ⟨s0, hs0⟩ := Module.projective_lifting_property p εC hp
  let εB : (PA.complex.X 0 × PC.complex.X 0) →ₗ[R] B := (i.comp εA).coprod s0
  -- Base lift h0 : PC.X 1 → PA.X 0
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
  -- Inductive lift step
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
  -- Build h n : PC.X (n + 1) → PA.X n together with the preimage invariant
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
  -- Build the chain complex KB with KB.X n = PA.X n × PC.X n
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
  -- Short exact sequence of chain complexes 0 → PA → KB → PC → 0
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
  -- Check KB is a ProjectiveResolution of B via εB!
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

/-- If `a : R` annihilates `M`, then `a` annihilates `Tor_i^R(M, N)`. -/
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

/-- If `b : R` annihilates `N`, then `b` annihilates `Tor_i^R(M, N)`. -/
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

/-- If `(P ⊔ Q).radical = maximalIdeal S`, then any finitely generated `S`-module annihilated
by `P ⊔ Q` has finite length. -/
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

/-- Finite-length additivity in `ℕ` for a short exact sequence. -/
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

/-- If `A → B → C` is exact at `B` and both `A` and `C` have finite length, then `B` has finite
length equal to `ℓ(range f) + ℓ(range g)`. -/
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


end ChangeOfRings


noncomputable def z58 {R:Type} [CommRing R]
  {A B:Type} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  (f:A →ₗ[R] B) (N:Type) [AddCommGroup N] [Module R N] (i : ℕ) :
  torMod R A N i →ₗ[R] torMod R B N i :=
 (((Tor (ModuleCat.{0} R) i).map (ModuleCat.ofHom f)).app (ModuleCat.of R N)).hom
lemma z65 {R:Type} [CommRing R]
  {A B C:Type} [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
  (i:A →ₗ[R] B) (p:B →ₗ[R] C)
  (hi:Injective i) (hp:Surjective p)
  (hip:LinearMap.range i=LinearMap.ker p)
  (N:Type) [AddCommGroup N] [Module R N] :
  ∃ δ : ∀ n : ℕ,torMod R C N (n+1) →ₗ[R] torMod R A N n,(∀ n,Function.Exact (δ n) (z58 i N n))∧(∀ n,Function.Exact (z58 i N n) (z58 p N n))∧(∀ n,Function.Exact (z58 p N (n+1)) (δ n)):=by
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
 let eA (n : ℕ) : torMod R A N n ≅ KA.homology n:=PN.isoLeftDerivedObj FA n;let eB (n : ℕ) : torMod R B N n ≅ KB.homology n:=PN.isoLeftDerivedObj FB n;let eC (n : ℕ) : torMod R C N n ≅ KC.homology n:=PN.isoLeftDerivedObj FC n;let δ (n : ℕ) : torMod R C N (n+1) →ₗ[R] torMod R A N n:=((eC (n+1)).hom ≫ q3.δ (n+1) n rfl ≫ (eA n).inv).hom
 have q0:∀ {X Y:Type} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
   (f:X →ₗ[R] Y) (n : ℕ) (x:torMod R X N n),
   let FX:=(tensoringLeft (ModuleCat.{0} R)).obj (ModuleCat.of R X);let FY:=(tensoringLeft (ModuleCat.{0} R)).obj (ModuleCat.of R Y);let η : FX ⟶ FY:=(tensoringLeft (ModuleCat.{0} R)).map (ModuleCat.ofHom f);let φ := (NatTrans.mapHomologicalComplex η (ComplexShape.down ℕ)).app PN.complex
   (PN.isoLeftDerivedObj FY n).hom.hom (z58 f N n x)=(HomologicalComplex.homologyMap φ n).hom ((PN.isoLeftDerivedObj FX n).hom.hom x):=by
  intro X Y _ _ _ _ f n x FX FY η φ;have h0:=ProjectiveResolution.leftDerived_app_eq η PN n
  have h1:CategoryStruct.comp ((NatTrans.leftDerived η n).app (ModuleCat.of R N))
    (PN.isoLeftDerivedObj FY n).hom =
    CategoryStruct.comp (PN.isoLeftDerivedObj FX n).hom
     ((HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ) n).map φ):=by
   rw [h0,Category.assoc,Category.assoc,Iso.inv_hom_id,Category.comp_id]
  exact congrArg (fun ψ : torMod R X N n ⟶ ((FY.mapHomologicalComplex _).obj PN.complex).homology n =>
   ψ.hom x) h1
 have htor_i (n : ℕ) (x:torMod R A N n) :
   (eB n).hom.hom (z58 i N n x)=(HomologicalComplex.homologyMap S.f n).hom ((eA n).hom.hom x) :=
  q0 i n x
 have htor_p (n : ℕ) (x:torMod R B N n) :
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
  (f:A →ₗ[R] B) (N:Type) [AddCommGroup N] [Module R N] (x:torMod R A N 0) :
  torZeroEquiv R B N (z58 f N 0 x)=LinearMap.rTensor N f (torZeroEquiv R A N x):=by
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
 exact congrArg (fun φ : torMod R A N 0 ⟶ ModuleCat.of R (B ⊗[R] N) => φ.hom x) h1
lemma z67 {R:Type} [CommRing R]
  (M N:Type) [AddCommGroup M] [Module R M] [Module.Flat R M]
  [AddCommGroup N] [Module R N] (i : ℕ) :
  Subsingleton (torMod R M N (i+1)):=by
 let PN:=projectiveResolution (ModuleCat.of R N);let F:=(tensoringLeft (ModuleCat.{0} R)).obj (ModuleCat.of R M);let e:torMod R M N (i+1) ≅ ((F.mapHomologicalComplex _).obj PN.complex).homology (i+1):=PN.isoLeftDerivedObj F (i+1)
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
  Nonempty (torMod R M N 1 ≃ₗ[R] torMod R N M 1) ∧
  (∀ k : ℕ,Nonempty (torMod R K N (k+1) ≃ₗ[R] torMod R N K (k+1))→Nonempty (torMod R M N (k+2) ≃ₗ[R] torMod R N M (k+2))):=by
 obtain ⟨δL,hL1,_,hL3⟩:=z65 incl p q1 hp hex N;obtain ⟨δR,hR1,_,hR3⟩:=horseshoe_tor_les N incl p q1 hp hex;constructor
 ·
  have : Subsingleton (torMod R F N 1):=z67 F N 0;have : Subsingleton (torMod R N F 1):=tor_succ_subsingleton_of_projective N F 0
  have hδL_inj:Injective (δL 0):=by
   rw [injective_iff_map_eq_zero];intro x hx;obtain ⟨y,rfl⟩:=(hL3 0 x).mp hx;rw [Subsingleton.elim y 0,map_zero]
  have hδR_inj:Injective (δR 0):=by
   rw [injective_iff_map_eq_zero];intro x hx;obtain ⟨y,rfl⟩:=(hR3 0 x).mp hx;rw [Subsingleton.elim y 0,map_zero]
  obtain ⟨eL1⟩:=z68 (δL 0) (z58 incl N 0) hδL_inj (hL1 0);obtain ⟨eR1⟩:=z68 (δR 0) (torMap N incl 0) hδR_inj (hR1 0);let q2:torMod R K N 0 ≃ₗ[R] torMod R N K 0:=(torZeroEquiv R K N).trans ((TensorProduct.comm R K N).trans (torZeroEquiv R N K).symm);let q0:torMod R F N 0 ≃ₗ[R] torMod R N F 0:=(torZeroEquiv R F N).trans ((TensorProduct.comm R F N).trans (torZeroEquiv R N F).symm)
  have hsq:∀ x:torMod R K N 0,q0 (z58 incl N 0 x)=torMap N incl 0 (q2 x):=fun x=>by
   apply (torZeroEquiv R N F).injective;rw [torZeroEquiv_naturality];simp only [q0,q2,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply,z66]
   generalize torZeroEquiv R K N x=t
   induction t using TensorProduct.induction_on with
   | zero=>simp
   | tmul k n=>simp
   | add t₁ t₂ ih₁ ih₂=>simp [ih₁,ih₂]
  obtain ⟨eKer⟩:=z69 (z58 incl N 0) (torMap N incl 0) q2 q0 hsq;exact ⟨eL1.trans (eKer.trans eR1.symm)⟩
 ·
  intro k ⟨eIH⟩;have : Subsingleton (torMod R F N (k+2)):=z67 F N (k+1);have : Subsingleton (torMod R N F (k+2)):=tor_succ_subsingleton_of_projective N F (k+1);have : Subsingleton (torMod R F N (k+1)):=z67 F N k;have : Subsingleton (torMod R N F (k+1)):=tor_succ_subsingleton_of_projective N F k
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
  ∀ (i : ℕ) (M N:Type) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N],Nonempty (torMod R M N i ≃ₗ[R] torMod R N M i):=by
 intro i
 induction i with
 | zero =>
  intro M N _ _ _ _;exact ⟨(torZeroEquiv R M N).trans ((TensorProduct.comm R M N).trans (torZeroEquiv R N M).symm)⟩
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
  Module.intersectionMultiplicity R M N=Module.intersectionMultiplicity R N M:=by
 unfold Module.intersectionMultiplicity
 refine finsum_congr fun i => ?_
 obtain ⟨e⟩:=z71 (R:=R) i M N;rw [e.length_eq]

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

private lemma support_tensor_subset_inter
    {T : Type} [CommRing T]
    {M N : Type} [AddCommGroup M] [Module T M] [Module.Finite T M]
    [AddCommGroup N] [Module T N] [Module.Finite T N] :
    Module.support T (M ⊗[T] N) ⊆ Module.support T M ∩ Module.support T N := by
  intro q hq
  rw [Module.mem_support_iff_of_finite] at hq
  refine ⟨?_, ?_⟩
  · rw [Module.mem_support_iff_of_finite]
    intro r hr
    apply hq
    rw [Module.mem_annihilator]
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact smul_zero r
    | add x₁ x₂ hx₁ hx₂ => rw [smul_add, hx₁, hx₂, add_zero]
    | tmul m n =>
      rw [TensorProduct.smul_tmul', Module.mem_annihilator.mp hr m, TensorProduct.zero_tmul]
  · rw [Module.mem_support_iff_of_finite]
    intro r hr
    apply hq
    rw [Module.mem_annihilator]
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact smul_zero r
    | add x₁ x₂ hx₁ hx₂ => rw [smul_add, hx₁, hx₂, add_zero]
    | tmul m n =>
      rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul,
        Module.mem_annihilator.mp hr n, TensorProduct.tmul_zero]

private lemma inter_subset_support_tensor
    {T : Type} [CommRing T]
    {M N : Type} [AddCommGroup M] [Module T M] [Module.Finite T M]
    [AddCommGroup N] [Module T N] [Module.Finite T N] :
    Module.support T M ∩ Module.support T N ⊆ Module.support T (M ⊗[T] N) := by
  rintro q ⟨hqM, hqN⟩
  let Rq := Localization.AtPrime q.asIdeal
  let k := IsLocalRing.ResidueField Rq
  have nt_of_equiv : ∀ {α β : Type} (e : α ≃ β), Nontrivial α → Nontrivial β := fun e h =>
    ⟨let ⟨a, b, hab⟩ := h.exists_pair_ne; ⟨e a, e b, fun h' => hab (e.injective h')⟩⟩
  have hntM : Nontrivial (LocalizedModule q.asIdeal.primeCompl M) :=
    (Module.mem_support_iff (R := T) (M := M)).mp hqM
  have hntN : Nontrivial (LocalizedModule q.asIdeal.primeCompl N) :=
    (Module.mem_support_iff (R := T) (M := N)).mp hqN
  let Mq := Rq ⊗[T] M
  let Nq := Rq ⊗[T] N
  have _ : Nontrivial Mq :=
    nt_of_equiv (IsLocalizedModule.iso q.asIdeal.primeCompl (TensorProduct.mk T Rq M 1)).toEquiv hntM
  have _ : Nontrivial Nq :=
    nt_of_equiv (IsLocalizedModule.iso q.asIdeal.primeCompl (TensorProduct.mk T Rq N 1)).toEquiv hntN
  have _ : Nontrivial (k ⊗[Rq] Mq) := by
    let eMk : k ⊗[Rq] Mq ≃ₗ[Rq] Mq ⧸ (maximalIdeal Rq • (⊤ : Submodule Rq Mq)) :=
      TensorProduct.quotTensorEquivQuotSMul Mq (maximalIdeal Rq)
    have hqnt : Nontrivial (Mq ⧸ (maximalIdeal Rq • (⊤ : Submodule Rq Mq))) := by
      rw [Submodule.Quotient.nontrivial_iff, ne_comm]
      exact Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator (IsLocalRing.maximalIdeal_le_jacobson _)
    exact nt_of_equiv eMk.symm.toEquiv hqnt
  have _ : Nontrivial (k ⊗[Rq] Nq) := by
    let eNk : k ⊗[Rq] Nq ≃ₗ[Rq] Nq ⧸ (maximalIdeal Rq • (⊤ : Submodule Rq Nq)) :=
      TensorProduct.quotTensorEquivQuotSMul Nq (maximalIdeal Rq)
    have hqnt : Nontrivial (Nq ⧸ (maximalIdeal Rq • (⊤ : Submodule Rq Nq))) := by
      rw [Submodule.Quotient.nontrivial_iff, ne_comm]
      exact Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator (IsLocalRing.maximalIdeal_le_jacobson _)
    exact nt_of_equiv eNk.symm.toEquiv hqnt
  have hntMNk : Nontrivial ((k ⊗[Rq] Mq) ⊗[k] (k ⊗[Rq] Nq)) := by
    obtain ⟨x, hx⟩ := exists_ne (0 : k ⊗[Rq] Mq)
    obtain ⟨y, hy⟩ := exists_ne (0 : k ⊗[Rq] Nq)
    let bM := Module.Basis.ofVectorSpace k (k ⊗[Rq] Mq)
    let bN := Module.Basis.ofVectorSpace k (k ⊗[Rq] Nq)
    have hneM : Nonempty (Module.Basis.ofVectorSpaceIndex k (k ⊗[Rq] Mq)) := by
      by_contra hempty
      rw [not_nonempty_iff] at hempty
      exact hx (bM.repr.injective (Subsingleton.elim _ _))
    have hneN : Nonempty (Module.Basis.ofVectorSpaceIndex k (k ⊗[Rq] Nq)) := by
      by_contra hempty
      rw [not_nonempty_iff] at hempty
      exact hy (bN.repr.injective (Subsingleton.elim _ _))
    obtain ⟨i⟩ := hneM
    obtain ⟨j⟩ := hneN
    exact ⟨⟨(bM.tensorProduct bN) (i, j), 0, (bM.tensorProduct bN).ne_zero (i, j)⟩⟩
  let e1 : k ⊗[Rq] (Mq ⊗[Rq] Nq) ≃ₗ[k] (k ⊗[Rq] Mq) ⊗[k] (k ⊗[Rq] Nq) :=
    ((AlgebraTensorModule.assoc Rq Rq k k Mq Nq).symm).trans
      ((AlgebraTensorModule.cancelBaseChange Rq k k (k ⊗[Rq] Mq) Nq).symm)
  let e2 : Rq ⊗[T] (M ⊗[T] N) ≃ₗ[Rq] Mq ⊗[Rq] Nq :=
    ((AlgebraTensorModule.assoc T T Rq Rq M N).symm).trans
      ((AlgebraTensorModule.cancelBaseChange T Rq Rq Mq N).symm)
  let e3 : k ⊗[Rq] (Rq ⊗[T] (M ⊗[T] N)) ≃ₗ[k] (k ⊗[Rq] Mq) ⊗[k] (k ⊗[Rq] Nq) :=
    (AlgebraTensorModule.congr (LinearEquiv.refl k k) e2).trans e1
  have _ : Nontrivial (k ⊗[Rq] (Rq ⊗[T] (M ⊗[T] N))) := nt_of_equiv e3.symm.toEquiv hntMNk
  rw [Module.mem_support_iff_of_finite]
  intro r hr
  by_contra hrq
  have hunit : IsUnit (algebraMap T Rq r) :=
    IsLocalization.map_units Rq (⟨r, hrq⟩ : q.asIdeal.primeCompl)
  have hunitk : IsUnit (algebraMap Rq k (algebraMap T Rq r)) :=
    hunit.map (algebraMap Rq k)
  obtain ⟨z, hz⟩ := exists_ne (0 : k ⊗[Rq] (Rq ⊗[T] (M ⊗[T] N)))
  have hkill : (algebraMap Rq k (algebraMap T Rq r)) • z = 0 := by
    clear hz
    induction z using TensorProduct.induction_on with
    | zero => exact smul_zero _
    | add z₁ z₂ hz₁ hz₂ => rw [smul_add, hz₁, hz₂, add_zero]
    | tmul c w =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add w₁ w₂ hw₁ hw₂ => rw [TensorProduct.tmul_add, smul_add, hw₁, hw₂, add_zero]
      | tmul s u =>
        calc (algebraMap Rq k (algebraMap T Rq r)) • (c ⊗ₜ[Rq] (s ⊗ₜ[T] u))
            = (algebraMap Rq k (algebraMap T Rq r) * c) ⊗ₜ[Rq] (s ⊗ₜ[T] u) := rfl
          _ = ((algebraMap T Rq r) • c) ⊗ₜ[Rq] (s ⊗ₜ[T] u) := by rw [Algebra.smul_def]
          _ = c ⊗ₜ[Rq] ((algebraMap T Rq r) • (s ⊗ₜ[T] u)) := TensorProduct.smul_tmul _ c _
          _ = c ⊗ₜ[Rq] ((algebraMap T Rq r * s) ⊗ₜ[T] u) := rfl
          _ = c ⊗ₜ[Rq] ((r • s) ⊗ₜ[T] u) := by rw [Algebra.smul_def]
          _ = c ⊗ₜ[Rq] (s ⊗ₜ[T] (r • u)) := by rw [TensorProduct.smul_tmul]
          _ = 0 := by rw [Module.mem_annihilator.mp hr u, TensorProduct.tmul_zero, TensorProduct.tmul_zero]
  exact hz (by
    have hinv := congrArg (fun v => ((hunitk.unit⁻¹ : kˣ) : k) • v) hkill
    rw [smul_zero, smul_smul] at hinv
    have hmul1 : ((hunitk.unit⁻¹ : kˣ) : k) * algebraMap Rq k (algebraMap T Rq r) = 1 := by
      have hu : (hunitk.unit : k) = algebraMap Rq k (algebraMap T Rq r) := hunitk.unit_spec
      calc ((hunitk.unit⁻¹ : kˣ) : k) * algebraMap Rq k (algebraMap T Rq r)
          = ((hunitk.unit⁻¹ : kˣ) : k) * (hunitk.unit : k) := by rw [hu]
        _ = 1 := Units.inv_mul hunitk.unit
    rw [hmul1, one_smul] at hinv
    exact hinv)

private lemma isFiniteLength_iff_supportDim_le_zero
    {T : Type} [CommRing T] [IsNoetherianRing T]
    {X : Type} [AddCommGroup X] [Module T X] [Module.Finite T X] :
    IsFiniteLength T X ↔ Module.supportDim T X ≤ 0 := by
  rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator]
  constructor
  · intro hfin
    have hArtX : IsArtinian T X := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfin).2
    obtain ⟨s, hs⟩ := ‹Module.Finite T X›
    let φ : T →ₗ[T] (s → X) := {
      toFun := fun t i => t • (i : X)
      map_add' := fun a b => by ext i; exact add_smul a b (i : X)
      map_smul' := fun a b => by ext i; exact mul_smul a b (i : X)
    }
    have hker : LinearMap.ker φ = Module.annihilator T X := by
      ext t
      simp only [LinearMap.mem_ker, funext_iff, Pi.zero_apply, Module.mem_annihilator, φ,
        LinearMap.coe_mk, AddHom.coe_mk]
      constructor
      · intro h x
        have hx : x ∈ Submodule.span T (s : Set X) := by rw [hs]; trivial
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
        · intro y hy; exact h ⟨y, hy⟩
        · exact smul_zero t
        · intro y z _ _ hy hz; rw [smul_add, hy, hz, add_zero]
        · intro c y _ hy; rw [smul_comm, hy, smul_zero]
      · intro h i; exact h (i : X)
    let emb : (T ⧸ Module.annihilator T X) →ₗ[T] (s → X) :=
      (Module.annihilator T X).liftQ φ (le_of_eq hker.symm)
    have hemb_inj : Function.Injective emb := by
      rw [← LinearMap.ker_eq_bot, Submodule.ker_liftQ, hker, Submodule.mkQ_map_self]
    have hArtQ_T : IsArtinian T (T ⧸ Module.annihilator T X) :=
      isArtinian_of_injective emb hemb_inj
    have hArtQ : IsArtinianRing (T ⧸ Module.annihilator T X) := by
      rw [IsArtinianRing]
      exact isArtinian_of_tower T hArtQ_T
    have hdimLE : Ring.KrullDimLE 0 (T ⧸ Module.annihilator T X) :=
      (isArtinianRing_iff_krullDimLE_zero (R := T ⧸ Module.annihilator T X)).mp hArtQ
    exact (Ring.krullDimLE_iff (R := T ⧸ Module.annihilator T X) (n := 0)).mp hdimLE
  · intro hdim0
    have hdimLE : Ring.KrullDimLE 0 (T ⧸ Module.annihilator T X) :=
      (Ring.krullDimLE_iff (R := T ⧸ Module.annihilator T X) (n := 0)).mpr hdim0
    have hArtQ : IsArtinianRing (T ⧸ Module.annihilator T X) :=
      (isArtinianRing_iff_krullDimLE_zero (R := T ⧸ Module.annihilator T X)).mpr hdimLE
    let actHom : (T ⧸ Module.annihilator T X) →+* AddMonoid.End X :=
      Ideal.Quotient.lift (Module.annihilator T X) (Module.toAddMonoidEnd T X) (by
        intro t ht
        ext x
        exact Module.mem_annihilator.mp ht x)
    let _ : Module (T ⧸ Module.annihilator T X) X := {
      smul := fun r x => actHom r x
      one_smul := fun x => by change actHom 1 x = x; rw [map_one]; rfl
      mul_smul := fun r s x => by change actHom (r * s) x = actHom r (actHom s x); rw [map_mul]; rfl
      smul_zero := fun r => (actHom r).map_zero
      smul_add := fun r x y => (actHom r).map_add x y
      add_smul := fun r s x => by change actHom (r + s) x = actHom r x + actHom s x; rw [map_add]; rfl
      zero_smul := fun x => by change actHom 0 x = 0; rw [map_zero]; rfl
    }
    have hsmul_mk : ∀ (t : T) (x : X),
        (Ideal.Quotient.mk (Module.annihilator T X) t) • x = t • x := fun _ _ => rfl
    have hfinQ : Module.Finite (T ⧸ Module.annihilator T X) X := by
      obtain ⟨s, hs⟩ := ‹Module.Finite T X›
      refine ⟨s, ?_⟩
      rw [eq_top_iff]
      intro x _
      have hx : x ∈ Submodule.span T (s : Set X) := by rw [hs]; trivial
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
      · intro y hy; exact Submodule.subset_span hy
      · exact Submodule.zero_mem _
      · intro y z _ _ hy hz; exact Submodule.add_mem _ hy hz
      · intro t y _ hy
        rw [← hsmul_mk t y]
        exact Submodule.smul_mem _ _ hy
    have hArtQX : IsArtinian (T ⧸ Module.annihilator T X) X := inferInstance
    have hArtX : IsArtinian T X := by
      let e : Submodule T X ≃o Submodule (T ⧸ Module.annihilator T X) X := {
        toFun := fun N => {
          carrier := N
          add_mem' := N.add_mem
          zero_mem' := N.zero_mem
          smul_mem' := fun r x hx => by
            obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective r
            rw [hsmul_mk t x]
            exact N.smul_mem t hx
        }
        invFun := fun N => {
          carrier := N
          add_mem' := N.add_mem
          zero_mem' := N.zero_mem
          smul_mem' := fun t x hx => by
            rw [← hsmul_mk t x]
            exact N.smul_mem (Ideal.Quotient.mk (Module.annihilator T X) t) hx
        }
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_rel_iff' := Iff.rfl
      }
      let embLT : ((· < ·) : Submodule T X → Submodule T X → Prop) ↪r
          ((· < ·) : Submodule (T ⧸ Module.annihilator T X) X →
            Submodule (T ⧸ Module.annihilator T X) X → Prop) := {
        toFun := e
        inj' := e.injective
        map_rel_iff' := e.lt_iff_lt
      }
      exact (isArtinian_iff T X).mpr (RelEmbedding.wellFounded embLT ((isArtinian_iff _ X).mp hArtQX))
    exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, hArtX⟩

private lemma isFiniteLength_tensor_of_injective
    {T : Type} [CommRing T] [IsNoetherianRing T]
    {L₁ L₂ N : Type} [AddCommGroup L₁] [Module T L₁] [Module.Finite T L₁]
    [AddCommGroup L₂] [Module T L₂] [Module.Finite T L₂]
    [AddCommGroup N] [Module T N] [Module.Finite T N]
    (f : L₁ →ₗ[T] L₂) (hf : Function.Injective f)
    (hfin : IsFiniteLength T (L₂ ⊗[T] N)) :
    IsFiniteLength T (L₁ ⊗[T] N) := by
  rw [isFiniteLength_iff_supportDim_le_zero] at hfin ⊢
  have hsub : Module.support T (L₁ ⊗[T] N) ⊆ Module.support T (L₂ ⊗[T] N) :=
    support_tensor_subset_inter.trans
      ((Set.inter_subset_inter_left _ (Module.support_subset_of_injective f hf)).trans
        inter_subset_support_tensor)
  exact (Order.krullDim_le_of_strictMono (fun a => ⟨a.1, hsub a.2⟩) (fun _ _ h => h)).trans hfin

private lemma isFiniteLength_tensor_of_surjective
    {T : Type} [CommRing T]
    {L₂ L₃ N : Type} [AddCommGroup L₂] [Module T L₂] [AddCommGroup L₃] [Module T L₃]
    [AddCommGroup N] [Module T N]
    (g : L₂ →ₗ[T] L₃) (hg : Function.Surjective g)
    (hfin : IsFiniteLength T (L₂ ⊗[T] N)) :
    IsFiniteLength T (L₃ ⊗[T] N) :=
  hfin.of_surjective (LinearMap.rTensor_surjective N hg)



section SESAdditivity

private lemma tor_length_ne_top_of_isFiniteLength_tensor
    {R : Type} [CommRing R] [IsRegularLocalRing R]
    (N A : Type) [AddCommGroup N] [Module R N] [Module.Finite R N]
    [AddCommGroup A] [Module R A] [Module.Finite R A]
    (hfin : IsFiniteLength R (N ⊗[R] A)) (i : ℕ) :
    Module.length R (torMod R N A i) ≠ ⊤ := by
  have hresA : HasFiniteProjRes R (maximalIdeal R).spanFinrank A :=
    hasFiniteProjRes_of_isRegularLocalRing R A
  let _ : Module.Finite R (torMod R N A i) :=
    tor_finite_of_hasFiniteProjRes N (maximalIdeal R).spanFinrank A hresA i
  let J : Ideal R := Module.annihilator R N ⊔ Module.annihilator R A
  have hann : ∀ r ∈ J, ∀ x : torMod R N A i, r • x = 0 := by
    intro r hr x
    rw [Submodule.mem_sup] at hr
    obtain ⟨u, hu, v, hv, rfl⟩ := hr
    rw [add_smul,
      tor_smul_eq_zero_left N A (Module.mem_annihilator.mp hu) i x,
      tor_smul_eq_zero_right N A (Module.mem_annihilator.mp hv) i x,
      add_zero]
  by_cases hJtop : J = ⊤
  · have h1 : (1 : R) ∈ J := hJtop ▸ Submodule.mem_top
    have _ : Subsingleton (torMod R N A i) :=
      ⟨fun x y => by
        have hx := hann 1 h1 x
        have hy := hann 1 h1 y
        rw [one_smul] at hx hy
        exact hx.trans hy.symm⟩
    simp
  · have hJrad : J.radical = maximalIdeal R := by
      refine le_antisymm ?_ ?_
      · exact (maximalIdeal.isMaximal R).isPrime.radical_le_iff.mpr
          (IsLocalRing.le_maximalIdeal hJtop)
      · rw [Ideal.radical_eq_sInf]
        refine le_sInf ?_
        rintro p ⟨hJp, hp⟩
        let q : PrimeSpectrum R := ⟨p, hp⟩
        have hqN : q ∈ Module.support R N :=
          (Module.mem_support_iff_of_finite (R := R) (M := N) (p := q)).mpr
            (le_sup_left.trans hJp)
        have hqA : q ∈ Module.support R A :=
          (Module.mem_support_iff_of_finite (R := R) (M := A) (p := q)).mpr
            (le_sup_right.trans hJp)
        have hqNA : q ∈ Module.support R (N ⊗[R] A) :=
          mem_support_tensorProduct_of_mem hqN hqA
        have hqc : q = IsLocalRing.closedPoint R :=
          Set.mem_singleton_iff.mp (support_subset_closedPoint_of_isFiniteLength hfin hqNA)
        have hp_eq : p = maximalIdeal R := congrArg PrimeSpectrum.asIdeal hqc
        exact hp_eq.symm.le
    exact length_ne_top_of_annihilated_radical_eq_maximalIdeal hJrad hann

private lemma interMult_eq_sum_range
    {R : Type} [CommRing R] [IsRegularLocalRing R]
    (N A : Type) [AddCommGroup N] [Module R N]
    [AddCommGroup A] [Module R A] [Module.Finite R A] :
    Module.intersectionMultiplicity R N A =
      ∑ n ∈ Finset.range ((maximalIdeal R).spanFinrank + 1),
        (-1 : ℤ) ^ n * ((Module.length R (torMod R N A n)).toNat : ℤ) := by
  let d : ℕ := (maximalIdeal R).spanFinrank
  have hres : HasFiniteProjRes R d A := hasFiniteProjRes_of_isRegularLocalRing R A
  unfold Module.intersectionMultiplicity
  rw [finsum_eq_sum_of_support_subset (s := Finset.range (d + 1))]
  intro i hi
  simp only [Function.mem_support, ne_eq, Finset.mem_coe, Finset.mem_range] at hi ⊢
  by_contra hle
  have hlt : d < i := by omega
  have _ : Subsingleton (torMod R N A i) :=
    tor_subsingleton_of_hasFiniteProjRes N d A hres i hlt
  exact hi (by simp)

theorem serre_h2_right
    (R : Type) [CommRing R] [IsRegularLocalRing R]
    (M₁ M₂ M₃ N : Type) [AddCommGroup M₁] [Module R M₁] [Module.Finite R M₁]
    [AddCommGroup M₂] [Module R M₂] [Module.Finite R M₂]
    [AddCommGroup M₃] [Module R M₃] [Module.Finite R M₃]
    [AddCommGroup N] [Module R N] [Module.Finite R N]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃)
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (hfin : IsFiniteLength R (M₂ ⊗[R] N)) :
    Module.intersectionMultiplicity R N M₂ =
      Module.intersectionMultiplicity R N M₁ + Module.intersectionMultiplicity R N M₃ := by
  have hfin1 : IsFiniteLength R (M₁ ⊗[R] N) := isFiniteLength_tensor_of_injective f hf hfin
  have hfin3 : IsFiniteLength R (M₃ ⊗[R] N) := isFiniteLength_tensor_of_surjective g hg hfin
  have hfinN1 : IsFiniteLength R (N ⊗[R] M₁) := (TensorProduct.comm R M₁ N).isFiniteLength hfin1
  have hfinN2 : IsFiniteLength R (N ⊗[R] M₂) := (TensorProduct.comm R M₂ N).isFiniteLength hfin
  have hfinN3 : IsFiniteLength R (N ⊗[R] M₃) := (TensorProduct.comm R M₃ N).isFiniteLength hfin3
  have hL1 : ∀ i, Module.length R (torMod R N M₁ i) ≠ ⊤ :=
    tor_length_ne_top_of_isFiniteLength_tensor N M₁ hfinN1
  have hL2 : ∀ i, Module.length R (torMod R N M₂ i) ≠ ⊤ :=
    tor_length_ne_top_of_isFiniteLength_tensor N M₂ hfinN2
  have hL3 : ∀ i, Module.length R (torMod R N M₃ i) ≠ ⊤ :=
    tor_length_ne_top_of_isFiniteLength_tensor N M₃ hfinN3
  have hip : LinearMap.range f = LinearMap.ker g := (LinearMap.exact_iff.mp hfg).symm
  obtain ⟨δ, hδ_f, hf_g, hg_δ⟩ := horseshoe_tor_les N f g hf hg hip
  have hg0_surj : Function.Surjective (torMap N g 0) := by
    intro y
    obtain ⟨t, ht⟩ := LinearMap.lTensor_surjective N hg (torZeroEquiv R N M₃ y)
    refine ⟨(torZeroEquiv R N M₂).symm t, ?_⟩
    apply (torZeroEquiv R N M₃).injective
    rw [torZeroEquiv_naturality, LinearEquiv.apply_symm_apply, ht]
  let d : ℕ := (maximalIdeal R).spanFinrank
  let a (i : ℕ) : ℤ := ((Module.length R (torMod R N M₁ i)).toNat : ℤ)
  let b (i : ℕ) : ℤ := ((Module.length R (torMod R N M₂ i)).toNat : ℤ)
  let c (i : ℕ) : ℤ := ((Module.length R (torMod R N M₃ i)).toNat : ℤ)
  let r (k : ℕ) : ℤ := ((Module.length R (LinearMap.range (δ k))).toNat : ℤ)
  have h0 : b 0 - (a 0 + c 0) = - r 0 := by
    have hA0 := length_nat_of_exact_middle (δ 0) (torMap N f 0) (hδ_f 0) (hL3 1) (hL2 0)
    have hB0 := length_nat_of_exact_middle (torMap N f 0) (torMap N g 0) (hf_g 0) (hL1 0) (hL3 0)
    have hrg0 : Module.length R (LinearMap.range (torMap N g 0)) =
        Module.length R (torMod R N M₃ 0) :=
      (LinearEquiv.ofTop _ (LinearMap.range_eq_top.mpr hg0_surj)).length_eq
    have hrg0_nat : (Module.length R (LinearMap.range (torMap N g 0))).toNat =
        (Module.length R (torMod R N M₃ 0)).toNat := congrArg ENat.toNat hrg0
    dsimp only [a, b, c, r]
    omega
  have hstep (m : ℕ) : b (m + 1) - (a (m + 1) + c (m + 1)) = - r (m + 1) - r m := by
    have hCm := length_nat_of_exact_middle (torMap N g (m + 1)) (δ m) (hg_δ m)
      (hL2 (m + 1)) (hL1 m)
    have hBm := length_nat_of_exact_middle (torMap N f (m + 1)) (torMap N g (m + 1))
      (hf_g (m + 1)) (hL1 (m + 1)) (hL3 (m + 1))
    have hAm := length_nat_of_exact_middle (δ (m + 1)) (torMap N f (m + 1))
      (hδ_f (m + 1)) (hL3 (m + 2)) (hL2 (m + 1))
    dsimp only [a, b, c, r]
    omega
  have htele (k : ℕ) :
      ∑ n ∈ Finset.range (k + 1), (-1 : ℤ) ^ n * (b n - (a n + c n)) =
        (-1 : ℤ) ^ (k + 1) * r k := by
    induction k with
    | zero =>
      rw [Finset.sum_range_one, pow_zero, one_mul, zero_add, pow_one, neg_one_mul]
      exact h0
    | succ m ih =>
      rw [Finset.sum_range_succ, ih, hstep m]
      have hp : (-1 : ℤ) ^ (m + 2) = -((-1 : ℤ) ^ (m + 1)) := by rw [pow_succ]; ring
      rw [hp]
      ring
  have hrd : r d = 0 := by
    have hres3 : HasFiniteProjRes R d M₃ := hasFiniteProjRes_of_isRegularLocalRing R M₃
    have _ : Subsingleton (torMod R N M₃ (d + 1)) :=
      tor_subsingleton_of_hasFiniteProjRes N d M₃ hres3 (d + 1) (Nat.lt_succ_self d)
    have _ : Subsingleton (LinearMap.range (δ d)) :=
      ⟨fun ⟨_, ⟨u, hu⟩⟩ ⟨_, ⟨v, hv⟩⟩ =>
        Subtype.ext (hu.symm.trans ((congrArg (δ d) (Subsingleton.elim u v)).trans hv))⟩
    simp [r]
  have hsum0 : ∑ n ∈ Finset.range (d + 1), (-1 : ℤ) ^ n * (b n - (a n + c n)) = 0 := by
    rw [htele d, hrd, mul_zero]
  rw [interMult_eq_sum_range N M₂, interMult_eq_sum_range N M₁, interMult_eq_sum_range N M₃]
  change ∑ n ∈ Finset.range (d + 1), (-1 : ℤ) ^ n * b n =
    (∑ n ∈ Finset.range (d + 1), (-1 : ℤ) ^ n * a n) +
    (∑ n ∈ Finset.range (d + 1), (-1 : ℤ) ^ n * c n)
  have hlin :
      (∑ n ∈ Finset.range (d + 1), (-1 : ℤ) ^ n * b n) -
      ((∑ n ∈ Finset.range (d + 1), (-1 : ℤ) ^ n * a n) +
       (∑ n ∈ Finset.range (d + 1), (-1 : ℤ) ^ n * c n)) =
      ∑ n ∈ Finset.range (d + 1), (-1 : ℤ) ^ n * (b n - (a n + c n)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  linarith

theorem serre_h2_main :
    OMA.R_SerreMultiplicityConjectures_intersectionMultiplicity_pos_of_equalCharacteristic_R1.H2 := by
  intro R _ _ M₁ M₂ M₃ N _ _ _ _ _ _ _ _ _ _ _ _ f g hf hfg hg hfin
  have hright := serre_h2_right R M₁ M₂ M₃ N f g hf hfg hg hfin
  refine ⟨?_, hright⟩
  rw [z72 M₂ N, z72 M₁ N, z72 M₃ N]
  exact hright

end SESAdditivity

end SerreTorSESAdditivity

theorem OMA.solution :
    OMA.R_SerreMultiplicityConjectures_intersectionMultiplicity_pos_of_equalCharacteristic_R1.H2 :=
  SerreTorSESAdditivity.serre_h2_main
