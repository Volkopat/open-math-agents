import OMAReductions.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1_H2_R2_H1_R1
import Mathlib

/-! A covering of nilpotent permutation groups by the partitions of their degree. -/

open scoped BigOperators Pointwise
open Equiv

namespace NCover

variable {G : Type} [Group G] [Finite G]

-- Project onto one Sylow factor of the finite nilpotent group.
private theorem projection [Group.IsNilpotent G] {p : ℕ} [Fact p.Prime]
    (hp : p ∈ (Nat.card G).primeFactors) :
    ∃ (P : Sylow p G) (f : G →* P), Function.Surjective f ∧ ¬ p ∣ Nat.card f.ker := by
  classical
  let i : (Nat.card G).primeFactors := ⟨p, hp⟩
  let P : Sylow p G := default
  let e := (Sylow.directProductOfNormal (G := G) (fun _ => inferInstance)).symm
  let f := ((Pi.evalMonoidHom (fun Q : Sylow p G => Q) P).comp
    (Pi.evalMonoidHom (fun j : (Nat.card G).primeFactors => ∀ Q : Sylow (j : ℕ) G, Q) i)).comp
    e.toMonoidHom
  have hs : Function.Surjective f := by
    intro x
    exact ⟨e.symm (Pi.mulSingle i (Pi.mulSingle P x)), by simp [f]⟩
  refine ⟨P, f, hs, ?_⟩
  have hi : f.ker.index = Nat.card P := by
    rw [Subgroup.index_ker, f.range_eq_top_of_surjective hs, Nat.card_congr Subgroup.topEquiv.toEquiv]
  have hc := f.ker.card_mul_index
  rw [hi, ← P.1.index_mul_card] at hc
  have he : Nat.card f.ker = P.1.index := Nat.eq_of_mul_eq_mul_right Nat.card_pos hc
  rw [he]
  exact P.not_dvd_index

-- The kernel has order prime to p, also after restriction to H.
-- Thus projecting H preserves the p-part of its order.
private theorem coordSize {p : ℕ} [hp : Fact p.Prime] (P : Sylow p G)
    (f : G →* P) (hf : Function.Surjective f) (hk : ¬ p ∣ Nat.card f.ker)
    (H : Subgroup G) :
    (H.map f).index = p ^ H.index.factorization p := by
  classical
  let k := f.ker.subgroupOf H
  have hn : ¬ p ∣ Nat.card k := by
    intro h
    apply hk
    have he : Nat.card k = Nat.card ((H ⊓ f.ker : Subgroup G)) := by
      change Nat.card (f.ker.subgroupOf H) = _
      rw [← Subgroup.inf_subgroupOf_left f.ker H]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    rw [he] at h
    exact h.trans (Subgroup.card_dvd_of_le inf_le_right)
  have h1 := f.ker.card_mul_index
  rw [Subgroup.index_ker, f.range_eq_top_of_surjective hf, Nat.card_congr Subgroup.topEquiv.toEquiv] at h1
  have h2 := k.card_mul_index
  change Nat.card k * f.ker.relIndex H = _ at h2
  rw [Subgroup.relIndex_ker] at h2
  obtain ⟨b, hb, he⟩ := (Nat.dvd_prime_pow hp.out).mp
    (P.card_eq_multiplicity ▸ (H.map f).index_dvd_card)
  rw [he, ← Nat.factorization_pow_self hp.out (n := b), ← he]
  congr 1
  have val (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
      (a*b).factorization p = a.factorization p + b.factorization p := by
    simp [Nat.factorization_mul ha hb]
  have eqv := congrArg (fun n : ℕ => n.factorization p)
    (show Nat.card k * Nat.card (H.map f) * H.index =
      Nat.card f.ker * (Nat.card (H.map f) * (H.map f).index) by
        rw [h2, H.card_mul_index, (H.map f).card_mul_index, h1])
  rw [val _ _ (mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne') H.index_ne_zero_of_finite,
    val _ _ Nat.card_pos.ne' Nat.card_pos.ne',
    val _ _ Nat.card_pos.ne' (mul_ne_zero Nat.card_pos.ne' (H.map f).index_ne_zero_of_finite),
    val _ _ Nat.card_pos.ne' (H.map f).index_ne_zero_of_finite,
    Nat.factorization_eq_zero_of_not_dvd hn, Nat.factorization_eq_zero_of_not_dvd hk] at eqv
  omega


private abbrev Axis (m p : ℕ) := Fin (p ^ m.factorization p)
private abbrev Grid (m : ℕ) := ∀ p : m.primeFactors, Axis m p
private noncomputable def selected (m : ℕ) (p : m.primeFactors) :
    Sylow (p : ℕ) (Perm (Axis m p)) := default
private abbrev Actors (m : ℕ) := ∀ p : m.primeFactors, selected m p

private theorem nilActors (m : ℕ) : Group.IsNilpotent (Actors m) := by
  have (p : m.primeFactors) : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
  have (p : m.primeFactors) : Group.IsNilpotent (selected m p) :=
    (selected m p).isPGroup'.isNilpotent
  exact Group.isNilpotent_pi

private def actGrid (m : ℕ) : Actors m →* Perm (Grid m) where
  toFun u := Equiv.piCongrRight fun p => (u p).val
  map_one' := rfl
  map_mul' _ _ := rfl

private noncomputable def cardEquiv {A B : Type} [Finite A] [Finite B]
    (h : Nat.card A = Nat.card B) : A ≃ B := by
  letI := Fintype.ofFinite A
  letI := Fintype.ofFinite B
  exact Fintype.equivOfCardEq (by simpa only [Nat.card_eq_fintype_card] using h)

private theorem fitAxis {p : ℕ} [Fact p.Prime] {P : Type} [Group P] (hP : IsPGroup p P)
    {A B : Type} [MulAction P A] [Finite A] [Finite B] (h : Nat.card A = Nat.card B)
    (L : Sylow p (Perm B)) :
    ∃ e : A ≃ B, ∀ g : P, ∃ u : L, ∀ x : A, e (g • x) = u.val (e x) := by
  classical
  let e := cardEquiv h
  let rho := e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom P A)
  obtain ⟨Q, hQ⟩ := (hP.of_surjective rho.rangeRestrict rho.rangeRestrict_surjective).exists_le_sylow
  obtain ⟨b, hb⟩ := MulAction.exists_smul_eq (Perm B) Q L
  refine ⟨e.trans b, fun g => ?_⟩
  have hu : (MulAut.conj b) (rho g) ∈ L := by
    rw [← hb]
    exact ⟨rho g, hQ ⟨g, rfl⟩, rfl⟩
  refine ⟨⟨_, hu⟩, fun x => ?_⟩
  change b (e (g • x)) = b (e (g • e.symm (b.symm (b (e x)))))
  simp

private theorem oneAxis [Group.IsNilpotent G] (H : Subgroup G)
    (p : H.index.primeFactors) :
    ∃ (K : Subgroup G) (c : G ⧸ H → Axis H.index p),
      H ≤ K ∧ K.index = (p : ℕ) ^ H.index.factorization p ∧
      (∀ x y : G, c x = c y ↔ x⁻¹*y ∈ K) ∧
      ∀ g : G, ∃ u : selected H.index p, ∀ z, c (g • z) = u.val (c z) := by
  classical
  have : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
  have hd := (Nat.dvd_of_mem_primeFactors p.2).trans H.index_dvd_card
  obtain ⟨P, f, hf, hk⟩ := projection (G := G) (Nat.mem_primeFactors.mpr ⟨Fact.out, hd, Nat.card_pos.ne'⟩)
  let J := H.map f
  have hsize := coordSize P f hf hk H
  obtain ⟨e, he⟩ := fitAxis (A := P ⧸ J) P.isPGroup'
    (by rw [Nat.card_fin]; exact hsize) (selected H.index p)
  let t : G ⧸ H → P ⧸ J := Quotient.map' f (fun a b hab => by
    apply (QuotientGroup.leftRel_apply).2
    rw [← map_inv, ← map_mul]
    exact Subgroup.mem_map_of_mem f (QuotientGroup.leftRel_apply.mp hab))
  refine ⟨J.comap f, e ∘ t, Subgroup.le_comap_map f H, (J.index_comap_of_surjective hf).trans hsize, ?_, ?_⟩
  · intro x y
    change e (QuotientGroup.mk (f x)) = e (QuotientGroup.mk (f y)) ↔ f (x⁻¹*y) ∈ J
    rw [e.injective.eq_iff, QuotientGroup.eq, map_mul, map_inv]
  · intro g
    obtain ⟨u, hu⟩ := he (f g)
    refine ⟨u, fun z => Quotient.inductionOn' z (fun x => ?_)⟩
    change e (QuotientGroup.mk (f (g*x))) = u.val (e (QuotientGroup.mk (f x)))
    rw [map_mul]
    exact hu (QuotientGroup.mk (f x))

private theorem fitCosets [Group.IsNilpotent G] (H : Subgroup G) :
    ∃ e : G ⧸ H ≃ Grid H.index, ∀ g : G, ∃ u : Actors H.index,
      ∀ z, e (g • z) = actGrid _ u (e z) := by
  classical
  choose K c hle hsize hsame hact using oneAxis H
  let J := iInf K
  have hHJ : H ≤ J := le_iInf hle
  -- Every prime-power factor of the original index divides the intersection index.
  have hJI : H.index ∣ J.index := by
    apply (Nat.factorization_le_iff_dvd H.index_ne_zero_of_finite J.index_ne_zero_of_finite).mp
    intro p
    by_cases hp : p ∈ H.index.primeFactors
    · have hd := Subgroup.index_dvd_of_le (iInf_le K ⟨p, hp⟩)
      rw [hsize] at hd
      exact ((Nat.prime_of_mem_primeFactors hp).pow_dvd_iff_le_factorization J.index_ne_zero_of_finite).mp hd
    · have hz : H.index.factorization p = 0 := by
        simpa [Nat.support_factorization] using (Finsupp.notMem_support_iff.mp
          (show p ∉ H.index.factorization.support by simpa using hp))
      rw [hz]
      exact Nat.zero_le _
  have hEq : H = J := by
    by_contra hn
    exact (not_lt_of_ge (Nat.le_of_dvd J.index_ne_zero_of_finite.bot_lt hJI)) (Subgroup.index_strictAnti (lt_of_le_of_ne hHJ hn))
  let t : G ⧸ H → Grid H.index := fun z p => c p z
  have hinj : Function.Injective t := by
    intro a b
    induction a using Quotient.inductionOn' with
    | _ x =>
      induction b using Quotient.inductionOn' with
      | _ y =>
        intro h
        apply QuotientGroup.eq.mpr
        rw [hEq]
        exact Subgroup.mem_iInf.mpr fun p => (hsame p x y).mp (congrFun h p)
  refine ⟨Equiv.ofBijective t ((Nat.bijective_iff_injective_and_card t).mpr ⟨hinj, ?_⟩), ?_⟩
  · change H.index = Nat.card (∀ p : H.index.primeFactors, Axis H.index p)
    rw [Nat.card_pi]
    simpa only [Axis, Nat.card_fin] using Nat.prod_primeFactors_coe_pow_factorization H.index_ne_zero_of_finite
  · intro g
    choose u hu using fun p => hact p g
    exact ⟨u, fun z => funext fun p => hu p z⟩


private abbrev Block {n : ℕ} (a : Nat.Partition n) := ↥a.parts.toEnumFinset
private abbrev degree {n : ℕ} {a : Nat.Partition n} (j : Block a) := j.val.1
private abbrev Model {n : ℕ} (a : Nat.Partition n) := Σ j : Block a, Grid (degree j)
private abbrev BlockActors {n : ℕ} (a : Nat.Partition n) := ∀ j : Block a, Actors (degree j)

private noncomputable def blockAct {n : ℕ} (a : Nat.Partition n) : BlockActors a →* Perm (Model a) :=
  (Perm.sigmaCongrRightHom _).comp (MonoidHom.pi fun j =>
    (actGrid (degree j)).comp (Pi.evalMonoidHom _ j))

private theorem matchIndices {I J : Type} [Fintype I] [Fintype J] (m : I → ℕ) (d : J → ℕ)
    (h : Finset.univ.val.map m = Finset.univ.val.map d) :
    ∃ r : I ≃ J, ∀ i, d (r i) = m i := by
  classical
  have hc {A : Type} [Fintype A] (f : A → ℕ) (k : ℕ) :
      Nat.card {i // f i = k} = (Finset.univ.val.map f).count k := by
    simp [Nat.card_eq_fintype_card, Fintype.card_subtype, Multiset.count_map,
      ← Finset.filter_val, eq_comm]
  let v (k : ℕ) : {i // m i = k} ≃ {j // d j = k} := cardEquiv (by rw [hc, hc, h])
  exact ⟨Equiv.ofFiberEquiv v, Equiv.ofFiberEquiv_map v⟩

private theorem fitCosetsOfSize [Group.IsNilpotent G] (H : Subgroup G) (m : ℕ)
    (hm : H.index = m) :
    ∃ e : G ⧸ H ≃ Grid m, ∀ g : G, ∃ u : Actors m, ∀ z, e (g • z) = actGrid m u (e z) := by
  subst m
  exact fitCosets H

private theorem modelAction {n : ℕ} (S : Subgroup (Perm (Fin n))) [Group.IsNilpotent S] :
    ∃ (a : Nat.Partition n) (E : Model a ≃ Fin n),
      ∀ g : S, ∃ u : BlockActors a, ∀ x, E (blockAct a u x) = g.val (E x) := by
  classical
  let I := Quotient (MulAction.orbitRel S (Fin n))
  let : Fintype I := Fintype.ofFinite _
  let H (i : I) := MulAction.stabilizer S i.out
  let m (i : I) := (H i).index
  let E₀ : Fin n ≃ Σ i : I, S ⧸ H i := MulAction.selfEquivSigmaOrbitsQuotientStabilizer S (Fin n)
  let a : Nat.Partition n := {
    parts := Finset.univ.val.map m
    parts_pos := by
      intro k hk
      obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hk
      exact (H i).index_ne_zero_of_finite.bot_lt
    parts_sum := by
      change ∑ i, m i = n
      simpa only [Nat.card_sigma, Nat.card_fin, m, Subgroup.index] using Nat.card_congr E₀.symm }
  have hD : Finset.univ.val.map (degree (a := a)) = a.parts := by
    change Finset.univ.val.map (Prod.fst ∘ (Subtype.val : Block a → ℕ × ℕ)) = _
    rw [← Multiset.map_map]
    rw [← Finset.attach_eq_univ, Finset.attach_val, Multiset.attach_map_val]
    exact a.parts.map_toEnumFinset_fst
  -- Match equal-sized orbits to the numbered occurrences of that part.
  obtain ⟨r, hr⟩ := matchIndices m (degree (a := a)) hD.symm
  choose e he using fun j : Block a => fitCosetsOfSize (H (r.symm j)) (degree j)
    (by simpa using (hr (r.symm j)).symm)
  let E : Model a ≃ Fin n := ((Equiv.sigmaCongrRight fun j => (e j).symm).trans
    (Equiv.sigmaCongrLeft (β := fun i => S ⧸ H i) r.symm)).trans E₀.symm
  refine ⟨a, E, fun g => ?_⟩
  choose u hu using fun j => he j g
  refine ⟨u, ?_⟩
  rintro ⟨j, x⟩
  have hx : (e j).symm (actGrid _ (u j) x) = g • (e j).symm x := by
    apply (e j).injective
    simpa using (hu j ((e j).symm x)).symm
  change MulAction.ofQuotientStabilizer S _ ((e j).symm (actGrid _ (u j) x)) =
    g • MulAction.ofQuotientStabilizer S _ ((e j).symm x)
  rw [hx, MulAction.ofQuotientStabilizer_smul]

private noncomputable def cover {n : ℕ} (a : Nat.Partition n) : Subgroup (Perm (Fin n)) := by
  classical
  exact if h : Nonempty (Model a ≃ Fin n) then
    (h.some.permCongrHom.toMonoidHom.comp (blockAct a)).range else ⊥

private theorem nilCover {n : ℕ} (a : Nat.Partition n) : Group.IsNilpotent (cover a) := by
  classical
  have (j : Block a) : Group.IsNilpotent (Actors (degree j)) := nilActors _
  have : Group.IsNilpotent (BlockActors a) := Group.isNilpotent_pi
  by_cases h : Nonempty (Model a ≃ Fin n)
  · let f := h.some.permCongrHom.toMonoidHom.comp (blockAct a)
    have he : cover a = f.range := dif_pos h
    rw [he]
    exact Group.nilpotent_of_surjective f.rangeRestrict f.rangeRestrict_surjective
  · have he : cover a = ⊥ := dif_neg h
    rw [he]
    infer_instance

end NCover

theorem OMA.solution : OMA.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1_H2_R2_H1_R1.H1 := by
  classical
  intro n _
  refine ⟨NCover.cover, NCover.nilCover, ?_⟩
  intro S hS
  obtain ⟨a, E, hE⟩ := NCover.modelAction S
  have h : Nonempty (NCover.Model a ≃ Fin n) := ⟨E⟩
  let b := h.some
  let g := b.symm.trans E
  refine ⟨a, g, ?_⟩
  intro x hx
  obtain ⟨u, hu⟩ := hE ⟨x, hx⟩
  refine ⟨b.permCongrHom (NCover.blockAct a u), ?_, ?_⟩
  · unfold NCover.cover
    rw [dif_pos h]
    exact ⟨u, rfl⟩
  · apply Equiv.ext
    intro y
    change E (b.symm (b (NCover.blockAct a u (b.symm (b (E.symm y)))))) = x y
    simpa using hu (E.symm y)

