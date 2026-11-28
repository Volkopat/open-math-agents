import OMAStatements.S_arxiv_2107_09327
namespace OMA.P_arxiv_2107_09327

open OMA.S_arxiv_2107_09327

private abbrev Vec3 := ZMod 3 × ZMod 3 × ZMod 3

private def vzero : Vec3 := (0, 0, 0)

private def vadd (u v : Vec3) : Vec3 := (u.1 + v.1, u.2.1 + v.2.1, u.2.2 + v.2.2)

private def vneg (u : Vec3) : Vec3 := (-u.1, -u.2.1, -u.2.2)

/-- Linear automorphism `A = C^2` of `(ZMod 3)^3` of order `13`, where `C` is the
companion matrix of the primitive cubic `x^3 + 2x + 1` over `F_3`. -/
private def stepA (u : Vec3) : Vec3 :=
  (u.2.2, 2 * u.1 + u.2.1, 2 * u.2.1 + u.2.2)

private def powA (n : ℕ) (u : Vec3) : Vec3 := stepA^[n] u

private lemma stepA_vadd (u v : Vec3) : stepA (vadd u v) = vadd (stepA u) (stepA v) := by
  rcases u with ⟨u0, u1, u2⟩
  rcases v with ⟨v0, v1, v2⟩
  simp only [stepA, vadd, Prod.mk.injEq]
  exact ⟨trivial, by ring, by ring⟩

private lemma stepA_vneg (u : Vec3) : stepA (vneg u) = vneg (stepA u) := by
  rcases u with ⟨u0, u1, u2⟩
  simp only [stepA, vneg, Prod.mk.injEq]
  exact ⟨trivial, by ring, by ring⟩

private lemma stepA_vzero : stepA vzero = vzero := by
  decide

private lemma powA_vadd (n : ℕ) (u v : Vec3) : powA n (vadd u v) = vadd (powA n u) (powA n v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [powA, Function.iterate_succ_apply']
    exact (congrArg stepA ih).trans (stepA_vadd _ _)

private lemma powA_vneg (n : ℕ) (u : Vec3) : powA n (vneg u) = vneg (powA n u) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [powA, Function.iterate_succ_apply']
    exact (congrArg stepA ih).trans (stepA_vneg _)

private lemma powA_vzero (n : ℕ) : powA n vzero = vzero := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [powA, Function.iterate_succ_apply']
    exact (congrArg stepA ih).trans stepA_vzero

private lemma powA_13 : ∀ u : Vec3, powA 13 u = u := by
  decide

private lemma powA_add (m n : ℕ) (u : Vec3) : powA m (powA n u) = powA (m + n) u := by
  simp only [powA, Function.iterate_add_apply]

private lemma powA_mod_13 (n : ℕ) (u : Vec3) : powA n u = powA (n % 13) u := by
  have hq : ∀ q r : ℕ, powA (13 * q + r) u = powA r u := by
    intro q
    induction q with
    | zero => intro r; simp
    | succ q ih =>
      intro r
      have h1 : 13 * (q + 1) + r = 13 + (13 * q + r) := by omega
      rw [h1, ← powA_add, ih, powA_13]
  have hdiv : 13 * (n / 13) + n % 13 = n := Nat.div_add_mod n 13
  conv_lhs => rw [← hdiv]
  exact hq (n / 13) (n % 13)

private def powAZ (k : ZMod 13) (u : Vec3) : Vec3 := powA k.val u

private lemma powAZ_zero (u : Vec3) : powAZ 0 u = u := by
  simp [powAZ, powA]

private lemma powAZ_add (j k : ZMod 13) (u : Vec3) :
    powAZ j (powAZ k u) = powAZ (j + k) u := by
  unfold powAZ
  rw [powA_add, ZMod.val_add, ← powA_mod_13]

private lemma powAZ_vadd (k : ZMod 13) (u v : Vec3) :
    powAZ k (vadd u v) = vadd (powAZ k u) (powAZ k v) :=
  powA_vadd k.val u v

private lemma powAZ_vneg (k : ZMod 13) (u : Vec3) :
    powAZ k (vneg u) = vneg (powAZ k u) :=
  powA_vneg k.val u

private lemma powAZ_vzero (k : ZMod 13) : powAZ k vzero = vzero :=
  powA_vzero k.val

/-- The `[13, 3]_3` equidistant cyclic simplex code over `F_3`. -/
private def cw (u : Vec3) (i : ZMod 13) : ZMod 3 := (powAZ i u).1

private lemma cw_vzero (i : ZMod 13) : cw vzero i = 0 := by
  simp only [cw, powAZ_vzero]; rfl

private lemma cw_vadd (u v : Vec3) (i : ZMod 13) : cw (vadd u v) i = cw u i + cw v i := by
  simp only [cw, powAZ_vadd]; rfl

private lemma cw_vneg (u : Vec3) (i : ZMod 13) : cw (vneg u) i = -cw u i := by
  simp only [cw, powAZ_vneg]; rfl

private lemma cw_shift (u : Vec3) (i k : ZMod 13) : cw u (i + k) = cw (powAZ k u) i := by
  simp only [cw, powAZ_add]

private lemma cw_zero_at_0 (u : Vec3) : cw u 0 = u.1 := by
  simp [cw, powAZ_zero]

/-- Every codeword in the `[13, 3]_3` simplex code has at least one zero coordinate
(every nonzero codeword has Hamming weight `9 < 13`). -/
private lemma cw_has_zero : ∀ u : Vec3, ∃ i : ZMod 13, cw u i = 0 := by
  decide

private lemma cw_eq_zero_imp : ∀ u : Vec3, (∀ i : ZMod 13, cw u i = 0) → u = vzero := by
  decide

private lemma vadd_vneg_self (u : Vec3) : vadd (vneg u) u = vzero := by
  rcases u with ⟨u0, u1, u2⟩
  simp [vadd, vneg, vzero]

private lemma vadd_eq_zero_iff (u v : Vec3) : vadd u (vneg v) = vzero ↔ u = v := by
  rcases u with ⟨u0, u1, u2⟩
  rcases v with ⟨v0, v1, v2⟩
  simp only [vadd, vneg, vzero, Prod.mk.injEq, add_neg_eq_zero]

/-- Explicit bijection `ZMod 13 × ZMod 3 ≃ Fin (13 * 3)`. -/
private def e39 : ZMod 13 × ZMod 3 ≃ Fin (13 * 3) where
  toFun p := ⟨3 * p.1.val + p.2.val, by
    have h1 : p.1.val < 13 := p.1.val_lt
    have h2 : p.2.val < 3 := p.2.val_lt
    omega⟩
  invFun m := ((m.val / 3 : ℕ), (m.val % 3 : ℕ))
  left_inv p := by
    rcases p with ⟨i, x⟩
    have h1 : i.val < 13 := i.val_lt
    have h2 : x.val < 3 := x.val_lt
    ext
    · have hdiv : (3 * i.val + x.val) / 3 = i.val := by omega
      simp [hdiv]
    · have hmod : (3 * i.val + x.val) % 3 = x.val := by omega
      simp [hmod]
  right_inv m := by
    have hm : m.val < 13 * 3 := m.isLt
    apply Fin.ext
    dsimp
    have h1 : ((m.val / 3 : ℕ) : ZMod 13).val = m.val / 3 := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    have h2 : ((m.val % 3 : ℕ) : ZMod 3).val = m.val % 3 := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    rw [h1, h2]
    omega

/-- Action of `(u, k) ∈ C ⋊ C_{13}` on `ZMod 13 × ZMod 3`. -/
private def permPair (u : Vec3) (k : ZMod 13) : Equiv.Perm (ZMod 13 × ZMod 3) where
  toFun p := (p.1 + k, p.2 + cw u p.1)
  invFun p := (p.1 - k, p.2 - cw u (p.1 - k))
  left_inv p := by
    rcases p with ⟨i, x⟩
    simp
  right_inv p := by
    rcases p with ⟨i, x⟩
    simp

private lemma permPair_one : permPair vzero 0 = 1 := by
  ext ⟨i, x⟩ <;> simp [permPair, cw_vzero]

private lemma permPair_mul (u₁ u₂ : Vec3) (k₁ k₂ : ZMod 13) :
    permPair u₁ k₁ * permPair u₂ k₂ = permPair (vadd u₂ (powAZ k₂ u₁)) (k₁ + k₂) := by
  ext ⟨i, x⟩
  · change i + k₂ + k₁ = i + (k₁ + k₂)
    ring
  · change x + cw u₂ i + cw u₁ (i + k₂) = x + cw (vadd u₂ (powAZ k₂ u₁)) i
    rw [cw_vadd, cw_shift, add_assoc]

private lemma permPair_inv (u : Vec3) (k : ZMod 13) :
    (permPair u k)⁻¹ = permPair (vneg (powAZ (-k) u)) (-k) := by
  apply inv_eq_of_mul_eq_one_right
  rw [permPair_mul, ← powAZ_vneg, ← powAZ_vadd, vadd_vneg_self, powAZ_vzero,
      add_neg_cancel, permPair_one]

private def perm39 (u : Vec3) (k : ZMod 13) : Equiv.Perm (Fin (13 * 3)) :=
  e39.symm.trans ((permPair u k).trans e39)

private lemma perm39_apply_e39 (u : Vec3) (k : ZMod 13) (p : ZMod 13 × ZMod 3) :
    perm39 u k (e39 p) = e39 (permPair u k p) := by
  simp [perm39]

private lemma perm39_one : perm39 vzero 0 = 1 := by
  ext m
  have h : m = e39 (e39.symm m) := (e39.apply_symm_apply m).symm
  rw [h, perm39_apply_e39, permPair_one]
  rfl

private lemma perm39_mul (u₁ u₂ : Vec3) (k₁ k₂ : ZMod 13) :
    perm39 u₁ k₁ * perm39 u₂ k₂ = perm39 (vadd u₂ (powAZ k₂ u₁)) (k₁ + k₂) := by
  apply Equiv.ext
  intro m
  have h : m = e39 (e39.symm m) := (e39.apply_symm_apply m).symm
  rw [h]
  change perm39 u₁ k₁ (perm39 u₂ k₂ (e39 (e39.symm m))) = _
  rw [perm39_apply_e39, perm39_apply_e39, perm39_apply_e39, ← permPair_mul]
  rfl

private lemma perm39_inv (u : Vec3) (k : ZMod 13) :
    (perm39 u k)⁻¹ = perm39 (vneg (powAZ (-k) u)) (-k) := by
  apply inv_eq_of_mul_eq_one_right
  rw [perm39_mul, ← powAZ_vneg, ← powAZ_vadd, vadd_vneg_self, powAZ_vzero,
      add_neg_cancel, perm39_one]

private lemma perm39_inj {u₁ u₂ : Vec3} {k₁ k₂ : ZMod 13}
    (h : perm39 u₁ k₁ = perm39 u₂ k₂) : u₁ = u₂ ∧ k₁ = k₂ := by
  have hp : ∀ p : ZMod 13 × ZMod 3, permPair u₁ k₁ p = permPair u₂ k₂ p := by
    intro p
    apply e39.injective
    rw [← perm39_apply_e39, ← perm39_apply_e39, h]
  have hk : k₁ = k₂ := by
    have h0 := congrArg Prod.fst (hp (0, 0))
    simpa [permPair] using h0
  have hu : u₁ = u₂ := by
    rw [← vadd_eq_zero_iff]
    apply cw_eq_zero_imp
    intro i
    have hi := congrArg Prod.snd (hp (i, 0))
    have hcw : cw u₁ i = cw u₂ i := by simpa [permPair] using hi
    rw [cw_vadd, cw_vneg, hcw, add_neg_cancel]
  exact ⟨hu, hk⟩

/-- The imprimitive transitive permutation group `G39 ≅ C ⋊ C_{13}` of degree `39 = 13 * 3`. -/
private def G39 : Subgroup (Equiv.Perm (Fin (13 * 3))) where
  carrier := { σ | ∃ u k, σ = perm39 u k }
  one_mem' := ⟨vzero, 0, perm39_one.symm⟩
  mul_mem' := by
    rintro _ _ ⟨u₁, k₁, rfl⟩ ⟨u₂, k₂, rfl⟩
    exact ⟨vadd u₂ (powAZ k₂ u₁), k₁ + k₂, perm39_mul u₁ u₂ k₁ k₂⟩
  inv_mem' := by
    rintro _ ⟨u, k, rfl⟩
    exact ⟨vneg (powAZ (-k) u), -k, perm39_inv u k⟩

private lemma G39_transitive : IsTransitivePermGroup G39 := by
  have hfrom0 : ∀ w : Fin (13 * 3), ∃ g ∈ G39, g (e39 (0, 0)) = w := by
    intro w
    let p := e39.symm w
    refine ⟨perm39 (p.2, 0, 0) p.1, ⟨(p.2, 0, 0), p.1, rfl⟩, ?_⟩
    rw [perm39_apply_e39]
    have hp : permPair (p.2, 0, 0) p.1 (0, 0) = p := by
      ext
      · simp [permPair]
      · simp [permPair, cw_zero_at_0]
    rw [hp]
    exact e39.apply_symm_apply w
  intro v w
  rcases hfrom0 v with ⟨g₁, hg₁, hv⟩
  rcases hfrom0 w with ⟨g₂, hg₂, hw⟩
  refine ⟨g₂ * g₁⁻¹, G39.mul_mem hg₂ (G39.inv_mem hg₁), ?_⟩
  change g₂ (g₁⁻¹ v) = w
  rw [← hv]
  exact (congrArg g₂ (Equiv.symm_apply_apply g₁ _)).trans hw

private lemma stabilizerCard_G39_le : stabilizerCard G39 (e39 (0, 0)) ≤ 9 := by
  unfold stabilizerCard
  let img : Finset (Equiv.Perm (Fin (13 * 3))) :=
    Finset.univ.image (fun q : ZMod 3 × ZMod 3 => perm39 (0, q.1, q.2) 0)
  have hsub :
      @Finset.filter (Equiv.Perm (Fin (13 * 3))) (fun g => g ∈ G39 ∧ g (e39 (0, 0)) = e39 (0, 0))
        (Classical.decPred _) Finset.univ ⊆ img := by
    intro g hg
    rw [@Finset.mem_filter _ _ (Classical.decPred _)] at hg
    rcases hg.2.1 with ⟨u, k, rfl⟩
    have hfix : permPair u k (0, 0) = (0, 0) := by
      apply e39.injective
      rw [← perm39_apply_e39]
      exact hg.2.2
    have hk : k = 0 := by
      have h1 := congrArg Prod.fst hfix
      simpa [permPair] using h1
    have hu1 : u.1 = 0 := by
      have h2 := congrArg Prod.snd hfix
      simpa [permPair, cw_zero_at_0] using h2
    rw [Finset.mem_image]
    refine ⟨(u.2.1, u.2.2), Finset.mem_univ _, ?_⟩
    rcases u with ⟨u0, u1, u2⟩
    dsimp at hu1
    subst hu1
    subst hk
    rfl
  calc
    (@Finset.filter (Equiv.Perm (Fin (13 * 3))) (fun g => g ∈ G39 ∧ g (e39 (0, 0)) = e39 (0, 0))
        (Classical.decPred _) Finset.univ).card
      ≤ img.card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (ZMod 3 × ZMod 3)).card := Finset.card_image_le
    _ = 9 := by decide

private def F27 : Finset (Equiv.Perm (Fin (13 * 3))) :=
  Finset.univ.image (fun u : Vec3 => perm39 u 0)

private lemma F27_card : F27.card = 27 := by
  unfold F27
  rw [Finset.card_image_of_injective]
  · decide
  · intro u₁ u₂ h
    exact (perm39_inj h).1

private lemma F27_intersecting : IsIntersecting G39 F27 := by
  refine ⟨?_, ?_⟩
  · intro g hg
    rw [F27, Finset.mem_image] at hg
    rcases hg with ⟨u, _, rfl⟩
    exact ⟨u, 0, rfl⟩
  · intro g hg h hh
    rw [F27, Finset.mem_image] at hg hh
    rcases hg with ⟨u, _, rfl⟩
    rcases hh with ⟨v, _, rfl⟩
    rcases cw_has_zero (vadd u (vneg v)) with ⟨i, hi⟩
    have hcw : cw u i = cw v i := by
      rw [cw_vadd, cw_vneg, add_neg_eq_zero] at hi
      exact hi
    refine ⟨e39 (i, 0), ?_⟩
    rw [perm39_apply_e39, perm39_apply_e39]
    congr 1
    ext
    · simp [permPair]
    · simp [permPair, hcw]

private lemma not_main : ¬ (type_of% @OMA.S_arxiv_2107_09327.main) := by
  intro hmain
  have h13 : Nat.Prime 13 := by decide
  have h3 : Nat.Prime 3 := by decide
  have hodd13 : Odd 13 := ⟨6, rfl⟩
  have hodd3 : Odd 3 := ⟨1, rfl⟩
  have hlt : 3 < 13 := by omega
  have hle := hmain 13 3 h13 h3 hodd13 hodd3 hlt G39 G39_transitive (e39 (0, 0)) F27 F27_intersecting
  have hst := stabilizerCard_G39_le
  rw [F27_card] at hle
  omega

end OMA.P_arxiv_2107_09327

theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2107_09327.main) :=
  OMA.P_arxiv_2107_09327.not_main
