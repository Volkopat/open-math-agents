import OMAReductions.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_degree_two_R1

-- Reduction SymbolLengthMilnorKTheory.symbol_length_problem.variants.degree_two.R1.H2.R1 of step SymbolLengthMilnorKTheory.symbol_length_problem.variants.degree_two.R1.H2
-- Credit: @hyprspacecoyote
--
-- Prime-power filtration. For every field F and all p, d: if every class of K_2(F)/p is a sum
-- of N symbols and every class of K_2(F)/d is a sum of M symbols, then every class of
-- K_2(F)/pd is a sum of N + M symbols. Iterating, N symbols mod p give t N symbols mod p^t,
-- so Matzri's bound mod p^t follows from the case t = 1 (H1 for odd p, H2 for p = 2).
--
-- Proof of the step, with L = pd and x in K_2/L. Reduce x mod p and write it as N symbols
-- {a_i, b_i}; then y = x - sum {a_i, b_i} dies mod p, so y = p z with z in K_2/L (kernel lemma).
-- Write z mod d as M symbols {c_j, e_j}; then u = z - sum {c_j, e_j} dies mod d, so u = d v and
-- p u = L v = 0. Hence x = sum {a_i, b_i} + sum {c_j ^ p, e_j}.
--
-- Kernel lemma: if y in K_2/L dies mod d, then y = d w with w in K_2/L. There is no grading API,
-- so we let K^M_*(F)/d act on V = G_0/d x G_1/d x G_2/d, where G_n is the degree n part of
-- K^M_*(F)/L: the class {a} acts by v -> (0, {a} v_0, {a} v_1). This kills the Steinberg
-- relations and d, so it is a ring map out of K^M_*(F)/d, and the image of y sends (1, 0, 0)
-- to (0, 0, y mod d G_2).

namespace OMA.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_degree_two_R1_H2_R1

def H1 : Prop := ∀ m : ℕ, 1 ≤ m → ∀ p : ℕ, p.Prime → p ≠ 2 →
  p ^ (m - 1) - 1 ∈ MilnorK.symbolLengthBounds (MvRatFunc (Fin m) ℂ) p 2

def H2 : Prop := ∀ m : ℕ, 1 ≤ m →
  2 ^ (m - 1) - 1 ∈ MilnorK.symbolLengthBounds (MvRatFunc (Fin m) ℂ) 2 2

section

variable {F : Type*} [Field F]

/-- Ring maps out of `MilnorK F ℓ`: an additive map from `Fˣ` into a ring that kills the
Steinberg relations and `ℓ`. -/
theorem exists_lift (ℓ : ℕ) {R : Type*} [Ring R] (f : Additive Fˣ →+ R)
    (hst : ∀ a b : Fˣ, (a : F) + (b : F) = 1 → f (Additive.ofMul a) * f (Additive.ofMul b) = 0)
    (hℓ : (ℓ : R) = 0) :
    ∃ θ : MilnorK F ℓ →+* R, ∀ a : Fˣ, θ (MilnorK.of ℓ a) = f (Additive.ofMul a) := by
  refine ⟨RingQuot.lift ⟨(TensorAlgebra.lift ℤ f.toIntLinearMap).toRingHom, ?_⟩, ?_⟩
  · intro x y h
    cases h with
    | steinberg a b h => simpa using hst a b h
    | natCast => simpa using hℓ
  · intro a
    simp [MilnorK.of, RingQuot.lift_mkRingHom_apply]

/-- The reduction map `K^M_*(F)/L → K^M_*(F)/d` for `d ∣ L`. -/
theorem exists_red (L d : ℕ) (h : d ∣ L) :
    ∃ π : MilnorK F L →+* MilnorK F d, ∀ a : Fˣ, π (MilnorK.of L a) = MilnorK.of d a := by
  obtain ⟨θ, hθ⟩ := exists_lift (F := F) L (MilnorK.ofHom d)
    (fun a b hab => by simpa using MilnorK.of_mul_of_eq_zero d a b hab) (by
      obtain ⟨k, rfl⟩ := h
      push_cast
      rw [MilnorK.natCast_eq_zero, zero_mul])
  exact ⟨θ, fun a => by simpa using hθ a⟩

theorem map_symbol {L d : ℕ} (π : MilnorK F L →+* MilnorK F d)
    (hπ : ∀ a : Fˣ, π (MilnorK.of L a) = MilnorK.of d a) {n : ℕ} (s : Fin n → Fˣ) :
    π (MilnorK.symbol L s) = MilnorK.symbol d s := by
  simp [MilnorK.symbol, map_list_prod, List.map_ofFn, Function.comp_def, hπ]

theorem map_mem_grade {L d : ℕ} (π : MilnorK F L →+* MilnorK F d)
    (hπ : ∀ a : Fˣ, π (MilnorK.of L a) = MilnorK.of d a) {n : ℕ} {x : MilnorK F L}
    (hx : x ∈ MilnorK.grade F L n) : π x ∈ MilnorK.grade F d n := by
  have key : MilnorK.grade F L n ≤ (MilnorK.grade F d n).comap π.toAddMonoidHom :=
    (AddSubgroup.closure_le _).mpr (by
      rintro _ ⟨s, rfl⟩
      show π (MilnorK.symbol L s) ∈ MilnorK.grade F d n
      rw [map_symbol π hπ]
      exact MilnorK.symbol_mem_grade F d s)
  exact key hx

theorem of_mul_mem_grade (L : ℕ) (a : Fˣ) {n : ℕ} {x : MilnorK F L}
    (hx : x ∈ MilnorK.grade F L n) : MilnorK.of L a * x ∈ MilnorK.grade F L (n + 1) := by
  refine AddSubgroup.closure_induction
    (p := fun x _ => MilnorK.of L a * x ∈ MilnorK.grade F L (n + 1)) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨s, rfl⟩
    have := MilnorK.symbol_mem_grade F L (Fin.cons a s : Fin (n + 1) → Fˣ)
    simpa [MilnorK.symbol_succ] using this
  · simp
  · intro x y _ _ hx hy
    rw [mul_add]
    exact add_mem hx hy
  · intro x _ hx
    convert neg_mem hx using 1
    exact mul_neg (MilnorK.of L a) x

theorem symbol_two (ℓ : ℕ) (s : Fin 2 → Fˣ) :
    MilnorK.symbol ℓ s = MilnorK.of ℓ (s 0) * MilnorK.of ℓ (s 1) := by
  simp [MilnorK.symbol_succ]

theorem symbol_cons_pow (ℓ k : ℕ) {n : ℕ} (a : Fˣ) (s : Fin n → Fˣ) :
    MilnorK.symbol ℓ (Fin.cons (a ^ k) s : Fin (n + 1) → Fˣ) =
      k • MilnorK.symbol ℓ (Fin.cons a s : Fin (n + 1) → Fˣ) := by
  simp [MilnorK.symbol_succ, MilnorK.of_pow, mul_assoc]

end

theorem nsmul_quot_eq_zero {B : Type*} [AddCommGroup B] (d : ℕ)
    (q : B ⧸ (nsmulAddMonoidHom (α := B) d).range) : d • q = 0 := by
  induction q using QuotientAddGroup.induction_on with
  | H x =>
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    exact ⟨x, rfl⟩

/-- Left multiplication, as a map between the quotients `G / d G → H / d H`, additive in the
multiplier. -/
theorem exists_shift {M A : Type*} [AddCommGroup M] [Ring A] (G H : AddSubgroup A) (d : ℕ)
    (c : M →+ A) (hc : ∀ a x, x ∈ G → c a * x ∈ H) :
    ∃ g : M →+ ((↥G ⧸ (nsmulAddMonoidHom (α := ↥G) d).range) →+
        (↥H ⧸ (nsmulAddMonoidHom (α := ↥H) d).range)),
      ∀ a (x : ↥G), g a (QuotientAddGroup.mk x) = QuotientAddGroup.mk ⟨c a * x, hc a x x.2⟩ := by
  let h : M → (↥G →+ ↥H) := fun a =>
    { toFun := fun x => ⟨c a * x, hc a x x.2⟩
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp [mul_add] }
  have hD : ∀ a, (nsmulAddMonoidHom (α := ↥G) d).range ≤
      ((nsmulAddMonoidHom (α := ↥H) d).range).comap (h a) := by
    rintro a _ ⟨y, rfl⟩
    exact ⟨h a y, by simp [map_nsmul]⟩
  refine ⟨AddMonoidHom.mk' (fun a => QuotientAddGroup.map _ _ (h a) (hD a)) ?_, fun a x => rfl⟩
  intro a b
  refine QuotientAddGroup.addMonoidHom_ext _ (AddMonoidHom.ext fun x => ?_)
  show ((h (a + b) x : ↥H) : ↥H ⧸ (nsmulAddMonoidHom (α := ↥H) d).range) =
    ((h a x : ↥H) : ↥H ⧸ (nsmulAddMonoidHom (α := ↥H) d).range) +
      ((h b x : ↥H) : ↥H ⧸ (nsmulAddMonoidHom (α := ↥H) d).range)
  have : h (a + b) x = h a x + h b x := by ext; simp [h, add_mul]
  rw [this, QuotientAddGroup.mk_add]

/-- The truncated action `v ↦ (0, g0 a v.1, g1 a v.2.1)` on `Q0 × Q1 × Q2`. -/
theorem exists_rep {M Q0 Q1 Q2 : Type*} [AddCommGroup M] [AddCommGroup Q0] [AddCommGroup Q1]
    [AddCommGroup Q2] (g0 : M →+ Q0 →+ Q1) (g1 : M →+ Q1 →+ Q2) :
    ∃ f : M →+ AddMonoid.End (Q0 × Q1 × Q2), ∀ a v, f a v = (0, g0 a v.1, g1 a v.2.1) := by
  refine ⟨AddMonoidHom.mk' (fun a => AddMonoidHom.mk' (fun v => (0, g0 a v.1, g1 a v.2.1))
    (fun v w => by simp)) (fun a b => DFunLike.ext _ _ fun v => by
      show ((0 : Q0), g0 (a + b) v.1, g1 (a + b) v.2.1) =
        ((0 : Q0), g0 a v.1, g1 a v.2.1) + ((0 : Q0), g0 b v.1, g1 b v.2.1)
      simp), fun a v => rfl⟩

section

variable {F : Type*} [Field F]

/-- Kernel lemma, in a general ring `A` with subgroups `G0, G1, G2` playing the parts of the
degree `0, 1, 2` pieces: an element of `G2` in the span of the products `c a * c b` that dies
under `π : A → K^M_*(F)/d` is `d` times an element of `G2`. -/
theorem ker_generic {A : Type*} [Ring A] (G0 G1 G2 : AddSubgroup A) (d : ℕ)
    (c : Additive Fˣ →+ A) (hc1 : ∀ a x, x ∈ G0 → c a * x ∈ G1)
    (hc2 : ∀ a x, x ∈ G1 → c a * x ∈ G2)
    (hst : ∀ a b : Fˣ, (a : F) + (b : F) = 1 → c (Additive.ofMul a) * c (Additive.ofMul b) = 0)
    (h1 : (1 : A) ∈ G0) (π : A →+* MilnorK F d)
    (hπ : ∀ a : Fˣ, π (c (Additive.ofMul a)) = MilnorK.of d a) {y : A}
    (hy : y ∈ AddSubgroup.closure
      (Set.range fun ab : Fˣ × Fˣ => c (Additive.ofMul ab.1) * c (Additive.ofMul ab.2)))
    (h0 : π y = 0) : ∃ w ∈ G2, y = d • w := by
  obtain ⟨g0, hg0⟩ := exists_shift G0 G1 d c hc1
  obtain ⟨g1, hg1⟩ := exists_shift G1 G2 d c hc2
  obtain ⟨f, hf⟩ := exists_rep
    (Q0 := ↥G0 ⧸ (nsmulAddMonoidHom (α := ↥G0) d).range)
    (Q1 := ↥G1 ⧸ (nsmulAddMonoidHom (α := ↥G1) d).range)
    (Q2 := ↥G2 ⧸ (nsmulAddMonoidHom (α := ↥G2) d).range) g0 g1
  have hmul : ∀ u v : AddMonoid.End ((↥G0 ⧸ (nsmulAddMonoidHom (α := ↥G0) d).range) ×
      (↥G1 ⧸ (nsmulAddMonoidHom (α := ↥G1) d).range) ×
        (↥G2 ⧸ (nsmulAddMonoidHom (α := ↥G2) d).range)), ∀ w, (u * v) w = u (v w) :=
    fun _ _ _ => rfl
  obtain ⟨θ, hθ⟩ := exists_lift (F := F)
    (R := AddMonoid.End ((↥G0 ⧸ (nsmulAddMonoidHom (α := ↥G0) d).range) ×
      (↥G1 ⧸ (nsmulAddMonoidHom (α := ↥G1) d).range) ×
        (↥G2 ⧸ (nsmulAddMonoidHom (α := ↥G2) d).range))) d f (by
    intro a b hab
    refine DFunLike.ext _ _ fun v => ?_
    rw [hmul, hf, hf, AddMonoid.End.zero_apply, map_zero]
    refine Prod.ext rfl (Prod.ext rfl ?_)
    show g1 (Additive.ofMul a) (g0 (Additive.ofMul b) v.1) = 0
    induction v.1 using QuotientAddGroup.induction_on with
    | H x =>
      rw [hg0, hg1, QuotientAddGroup.eq_zero_iff]
      refine ⟨0, ?_⟩
      ext
      simp [← mul_assoc, hst a b hab]) (by
    refine DFunLike.ext _ _ fun v => ?_
    rw [AddMonoid.End.natCast_apply, AddMonoid.End.zero_apply]
    exact Prod.ext (nsmul_quot_eq_zero d _)
      (Prod.ext (nsmul_quot_eq_zero d _) (nsmul_quot_eq_zero d _)))
  have hcl : AddSubgroup.closure
      (Set.range fun ab : Fˣ × Fˣ => c (Additive.ofMul ab.1) * c (Additive.ofMul ab.2)) ≤ G2 := by
    rw [AddSubgroup.closure_le]
    rintro _ ⟨ab, rfl⟩
    simpa using hc2 _ _ (hc1 (Additive.ofMul ab.2) 1 h1)
  have key : ∀ (z : A) (hz : z ∈ AddSubgroup.closure
      (Set.range fun ab : Fˣ × Fˣ => c (Additive.ofMul ab.1) * c (Additive.ofMul ab.2))),
      θ (π z) (((⟨1, h1⟩ : ↥G0) : ↥G0 ⧸ (nsmulAddMonoidHom (α := ↥G0) d).range), 0, 0) =
        (0, 0, ((⟨z, hcl hz⟩ : ↥G2) : ↥G2 ⧸ (nsmulAddMonoidHom (α := ↥G2) d).range)) := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨⟨a, b⟩, rfl⟩ := hz
      rw [map_mul, map_mul, hπ, hπ, hθ, hθ, hmul, hf, hf]
      refine Prod.ext rfl (Prod.ext (map_zero _) ?_)
      show g1 (Additive.ofMul a) (g0 (Additive.ofMul b) _) = _
      rw [hg0, hg1]
      congr 1
      ext
      simp
    | zero =>
      rw [map_zero, map_zero, AddMonoid.End.zero_apply]
      rfl
    | add x y hx hy ihx ihy =>
      have e1 : θ (π (x + y)) (((⟨1, h1⟩ : ↥G0) : ↥G0 ⧸ (nsmulAddMonoidHom (α := ↥G0) d).range),
          0, 0) =
          θ (π x) (((⟨1, h1⟩ : ↥G0) : ↥G0 ⧸ (nsmulAddMonoidHom (α := ↥G0) d).range), 0, 0) +
            θ (π y) (((⟨1, h1⟩ : ↥G0) : ↥G0 ⧸ (nsmulAddMonoidHom (α := ↥G0) d).range), 0, 0) := by
        rw [map_add, map_add]
        rfl
      rw [e1, ihx, ihy]
      exact Prod.ext (add_zero 0) (Prod.ext (add_zero 0) (QuotientAddGroup.mk_add _ _ _).symm)
    | neg x hx ih =>
      have e1 : θ (π (-x)) (((⟨1, h1⟩ : ↥G0) : ↥G0 ⧸ (nsmulAddMonoidHom (α := ↥G0) d).range),
          0, 0) =
          -θ (π x) (((⟨1, h1⟩ : ↥G0) : ↥G0 ⧸ (nsmulAddMonoidHom (α := ↥G0) d).range), 0, 0) := by
        rw [map_neg, map_neg]
        rfl
      rw [e1, ih]
      exact Prod.ext neg_zero (Prod.ext neg_zero (QuotientAddGroup.mk_neg _ _).symm)
  have h2 := congrArg (fun v => v.2.2) (key y hy)
  rw [h0, map_zero, AddMonoid.End.zero_apply] at h2
  obtain ⟨w, hw⟩ := (QuotientAddGroup.eq_zero_iff _).mp h2.symm
  refine ⟨w, w.2, ?_⟩
  have := congrArg Subtype.val hw
  simpa using this.symm

/-- Kernel lemma: an element of `K_2(F)/L` that dies in `K_2(F)/d` is `d` times an element of
`K_2(F)/L`. -/
theorem ker_lemma (L d : ℕ) (π : MilnorK F L →+* MilnorK F d)
    (hπ : ∀ a : Fˣ, π (MilnorK.of L a) = MilnorK.of d a)
    {y : MilnorK F L} (hy : y ∈ MilnorK.grade F L 2) (h0 : π y = 0) :
    ∃ w ∈ MilnorK.grade F L 2, y = d • w := by
  refine ker_generic (MilnorK.grade F L 0) (MilnorK.grade F L 1) (MilnorK.grade F L 2) d
    (MilnorK.ofHom L) (fun a x hx => of_mul_mem_grade L a.toMul hx)
    (fun a x hx => of_mul_mem_grade L a.toMul hx)
    (fun a b hab => by simpa using MilnorK.of_mul_of_eq_zero L a b hab)
    (MilnorK.one_mem_grade_zero F L) π (fun a => by simpa using hπ a) ?_ h0
  refine AddSubgroup.closure_mono ?_ hy
  rintro _ ⟨s, rfl⟩
  exact ⟨(s 0, s 1), by simp [symbol_two]⟩

/-- One step of the filtration: `N` symbols mod `p` and `M` symbols mod `d` give `N + M`
symbols mod `p d`. -/
theorem add_mem_symbolLengthBounds_mul {p d N M : ℕ}
    (hN : N ∈ MilnorK.symbolLengthBounds F p 2) (hM : M ∈ MilnorK.symbolLengthBounds F d 2) :
    N + M ∈ MilnorK.symbolLengthBounds F (p * d) 2 := by
  intro x hx
  obtain ⟨π₁, hπ₁⟩ := exists_red (F := F) (p * d) p (dvd_mul_right p d)
  obtain ⟨π₂, hπ₂⟩ := exists_red (F := F) (p * d) d (dvd_mul_left d p)
  have hsum : ∀ {k : ℕ} (s : Fin k → Fin 2 → Fˣ),
      ∑ i, MilnorK.symbol (p * d) (s i) ∈ MilnorK.grade F (p * d) 2 :=
    fun s => AddSubgroup.sum_mem _ fun i _ => MilnorK.symbol_mem_grade F _ (s i)
  obtain ⟨k, hk, s, hs⟩ := hN (π₁ x) (map_mem_grade π₁ hπ₁ hx)
  have hy0 : π₁ (x - ∑ i, MilnorK.symbol (p * d) (s i)) = 0 := by
    rw [map_sub, map_sum, hs]
    simp [map_symbol π₁ hπ₁]
  obtain ⟨z, hz, hyz⟩ := ker_lemma (p * d) p π₁ hπ₁ (sub_mem hx (hsum s)) hy0
  obtain ⟨k', hk', r, hr⟩ := hM (π₂ z) (map_mem_grade π₂ hπ₂ hz)
  have hu0 : π₂ (z - ∑ j, MilnorK.symbol (p * d) (r j)) = 0 := by
    rw [map_sub, map_sum, hr]
    simp [map_symbol π₂ hπ₂]
  obtain ⟨v, -, huv⟩ := ker_lemma (p * d) d π₂ hπ₂ (sub_mem hz (hsum r)) hu0
  have hpu : p • (z - ∑ j, MilnorK.symbol (p * d) (r j)) = 0 := by
    rw [huv, smul_smul, nsmul_eq_mul, MilnorK.natCast_eq_zero, zero_mul]
  let r' : Fin k' → Fin 2 → Fˣ := fun j => Fin.cons ((r j 0) ^ p) (Fin.tail (r j))
  have hpz : p • z = ∑ j, MilnorK.symbol (p * d) (r' j) := by
    rw [smul_sub, sub_eq_zero] at hpu
    rw [hpu, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [r']
    rw [symbol_cons_pow, Fin.cons_self_tail]
  refine ⟨k + k', add_le_add hk hk', Fin.append s r', ?_⟩
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  rw [← hpz, ← hyz]
  abel

/-- The filtration: `N` symbols mod `p` give `t N` symbols mod `p ^ t`. -/
theorem mul_mem_symbolLengthBounds_pow {p N : ℕ} (hN : N ∈ MilnorK.symbolLengthBounds F p 2) :
    ∀ t : ℕ, 1 ≤ t → t * N ∈ MilnorK.symbolLengthBounds F (p ^ t) 2 := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => simpa using hN
  | succ t _ ih =>
    have e : (t + 1) * N = N + t * N := by ring
    rw [e, pow_succ']
    exact add_mem_symbolLengthBounds_mul hN ih

end

theorem main : H1 → H2 → OMA.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_degree_two_R1.H2 := by
  intro h1 h2 m hm p t hp ht _
  by_cases hp2 : p = 2
  · subst hp2
    exact mul_mem_symbolLengthBounds_pow (h2 m hm) t ht
  · exact mul_mem_symbolLengthBounds_pow (h1 m hm p hp hp2) t ht

end OMA.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_degree_two_R1_H2_R1
