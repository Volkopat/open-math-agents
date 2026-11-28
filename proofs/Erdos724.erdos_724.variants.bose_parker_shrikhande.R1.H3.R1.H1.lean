import OMAReductions.R_Erdos724_erdos_724_variants_bose_parker_shrikhande_R1_H3_R1

-- Step Erdos724.erdos_724.variants.bose_parker_shrikhande.R1.H3.R1.H1: hypothesis H1 of reduction Erdos724.erdos_724.variants.bose_parker_shrikhande.R1.H3.R1
-- Credit: @ptc-prover-bot
-- H1 := ∀ p : ℕ, p.Prime → 5 ≤ p →   ∃ L M : LatinSquare (2*p), L ≠ M ∧ IsOrthogonal L M  /-- The base order when the odd part is a power of three. -/

/-! Study: Erdős 724 — odd case, n ≡ 0 (mod 4) via Kronecker products of GF(4)/GF(8) squares, and the
    T9 split down to n ≡ 2 (mod 4). -/

open Finset Fin.CommRing

namespace Study724

/-- The Latin square (i, j) ↦ i + c j over ℤ/(m+1), for a unit c. -/
def affineSq (m : ℕ) (c : Fin (m + 1)) (hc : IsUnit c) : LatinSquare (m + 1) where
  mat i j := i + c * j
  row_injective i := fun j j' h => hc.mul_left_cancel (add_left_cancel h)
  col_injective j := fun a b h => by
    change a + c * j = b + c * j at h
    exact add_right_cancel h

lemma orth_one_two (m : ℕ) (h1 : IsUnit (1 : Fin (m + 1))) (h2 : IsUnit (2 : Fin (m + 1))) :
    Erdos724.IsOrthogonal (affineSq m 1 h1) (affineSq m 2 h2) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  simp only [affineSq, Prod.mk.injEq] at h
  obtain ⟨ha, hb⟩ := h
  have hj : j = j' := by linear_combination hb - ha
  subst hj
  have hi : i = i' := by linear_combination ha
  rw [hi]

lemma odd_pair (m : ℕ) (hodd : Odd (m + 1)) :
    ∃ L M : LatinSquare (m + 1), Erdos724.IsOrthogonal L M := by
  have hcop : Nat.Coprime 2 (m + 1) := (Nat.coprime_two_left).mpr hodd
  have h2 : IsUnit (2 : Fin (m + 1)) := by
    have := (ZMod.isUnit_iff_coprime 2 (m + 1)).mpr hcop
    exact_mod_cast this
  exact ⟨_, _, orth_one_two m isUnit_one h2⟩

/-- Kronecker product of Latin squares, through `Fin a × Fin b ≃ Fin (a * b)`. -/
def prodSq {a b : ℕ} (L : LatinSquare a) (M : LatinSquare b) : LatinSquare (a * b) where
  mat x y := finProdFinEquiv (L.mat (finProdFinEquiv.symm x).1 (finProdFinEquiv.symm y).1,
    M.mat (finProdFinEquiv.symm x).2 (finProdFinEquiv.symm y).2)
  row_injective x := by
    intro y y' h
    have h' := finProdFinEquiv.injective h
    simp only [Prod.mk.injEq] at h'
    apply finProdFinEquiv.symm.injective
    exact Prod.ext (L.row_injective _ h'.1) (M.row_injective _ h'.2)
  col_injective y := by
    intro x x' h
    change finProdFinEquiv _ = finProdFinEquiv _ at h
    have h' := finProdFinEquiv.injective h
    simp only [Prod.mk.injEq] at h'
    apply finProdFinEquiv.symm.injective
    exact Prod.ext (L.col_injective _ h'.1) (M.col_injective _ h'.2)

lemma prod_orth {a b : ℕ} {L L' : LatinSquare a} {M M' : LatinSquare b}
    (h1 : Erdos724.IsOrthogonal L L') (h2 : Erdos724.IsOrthogonal M M') :
    Erdos724.IsOrthogonal (prodSq L M) (prodSq L' M') := by
  rintro ⟨x, y⟩ ⟨x', y'⟩ h
  simp only [prodSq, Prod.mk.injEq] at h
  obtain ⟨ha, hb⟩ := h
  have ha' := finProdFinEquiv.injective ha
  have hb' := finProdFinEquiv.injective hb
  simp only [Prod.mk.injEq] at ha' hb'
  have e1 : ((finProdFinEquiv.symm x).1, (finProdFinEquiv.symm y).1)
      = ((finProdFinEquiv.symm x').1, (finProdFinEquiv.symm y').1) := h1 (Prod.ext ha'.1 hb'.1)
  have e2 : ((finProdFinEquiv.symm x).2, (finProdFinEquiv.symm y).2)
      = ((finProdFinEquiv.symm x').2, (finProdFinEquiv.symm y').2) := h2 (Prod.ext ha'.2 hb'.2)
  simp only [Prod.mk.injEq] at e1 e2
  have hx : x = x' := finProdFinEquiv.symm.injective (Prod.ext e1.1 e2.1)
  have hy : y = y' := finProdFinEquiv.symm.injective (Prod.ext e1.2 e2.2)
  rw [hx, hy]

/-- A Latin square of order ≥ 2 is not orthogonal to itself. -/
lemma not_orth_self {n : ℕ} (hn : 2 ≤ n) (L : LatinSquare n) : ¬ Erdos724.IsOrthogonal L L := by
  intro h
  obtain ⟨j, hj⟩ := (Finite.injective_iff_surjective.mp (L.row_injective ⟨1, by omega⟩))
    (L.mat ⟨0, by omega⟩ ⟨0, by omega⟩)
  have e : ((⟨1, by omega⟩ : Fin n), j) = (⟨0, by omega⟩, ⟨0, by omega⟩) := h (by simp only [hj])
  have := congrArg (fun p => p.1.val) e
  simp at this

end Study724


open Fin.CommRing

namespace Study724W

def IsOA {α : Type*} (k : ℕ) (S : Set (Fin k → α)) : Prop :=
  ∀ a b : Fin k, a ≠ b → Set.BijOn (fun r => (r a, r b)) S Set.univ

variable {T U : Type*}

def rowA (β : Fin 5 → T) (r : Fin 4 → Fin 3) : Fin 4 → (T × Fin 3) ⊕ U :=
  fun g => Sum.inl (β g.castSucc, r g)

def rowB (β : Fin 5 → T) (k : U) (r : Fin 4 → Option (Fin 3)) : Fin 4 → (T × Fin 3) ⊕ U :=
  fun g => match r g with
    | none => Sum.inr k
    | some s => Sum.inl (β g.castSucc, s)

def rowC (r : Fin 4 → U) : Fin 4 → (T × Fin 3) ⊕ U := fun g => Sum.inr (r g)

def W (S5 : Set (Fin 5 → T)) (S3 : Set (Fin 4 → Fin 3)) (S4 : Set (Fin 4 → Option (Fin 3)))
    (SU : Set (Fin 4 → U)) (ι : U → T) : Set (Fin 4 → (T × Fin 3) ⊕ U) :=
  {x | ∃ β ∈ S5, (∀ k, ι k ≠ β (Fin.last 4)) ∧ ∃ r ∈ S3, x = rowA β r} ∪
  {x | ∃ β ∈ S5, ∃ k, ι k = β (Fin.last 4) ∧ ∃ r ∈ S4, r ≠ (fun _ => none) ∧ x = rowB β k r} ∪
  {x | ∃ r ∈ SU, x = rowC r}

lemma rowB_eq_inl {β : Fin 5 → T} {k : U} {r : Fin 4 → Option (Fin 3)} {g : Fin 4} {p : T × Fin 3} :
    rowB β k r g = Sum.inl p ↔ ∃ s, r g = some s ∧ p = (β g.castSucc, s) := by
  unfold rowB
  cases r g <;> simp [eq_comm]

lemma rowB_eq_inr {β : Fin 5 → T} {k : U} {r : Fin 4 → Option (Fin 3)} {g : Fin 4} {k' : U} :
    rowB β k r g = Sum.inr k' ↔ r g = none ∧ k = k' := by
  unfold rowB
  cases r g <;> simp

lemma inj_of {α : Type*} {k : ℕ} {S : Set (Fin k → α)} (h : IsOA k S) {a b : Fin k} (hab : a ≠ b)
    {r r' : Fin k → α} (hr : r ∈ S) (hr' : r' ∈ S) (h1 : r a = r' a) (h2 : r b = r' b) : r = r' :=
  (h a b hab).injOn hr hr' (Prod.ext h1 h2)

lemma ex_of {α : Type*} {k : ℕ} {S : Set (Fin k → α)} (h : IsOA k S) {a b : Fin k} (hab : a ≠ b)
    (x y : α) : ∃ r ∈ S, r a = x ∧ r b = y := by
  obtain ⟨r, hr, he⟩ := (h a b hab).surjOn (Set.mem_univ (x, y))
  exact ⟨r, hr, (Prod.ext_iff.mp he).1, (Prod.ext_iff.mp he).2⟩

theorem wilson_OA {S5 : Set (Fin 5 → T)} {S3 : Set (Fin 4 → Fin 3)}
    {S4 : Set (Fin 4 → Option (Fin 3))} {SU : Set (Fin 4 → U)} {ι : U → T}
    (h5 : IsOA 5 S5) (h3 : IsOA 4 S3) (h4 : IsOA 4 S4) (hnone : (fun _ => none) ∈ S4)
    (hU : IsOA 4 SU) (hι : Function.Injective ι) : IsOA 4 (W S5 S3 S4 SU ι) := by
  classical
  intro a b hab
  have hab' : a.castSucc ≠ b.castSucc := fun h => hab (Fin.castSucc_injective _ h)
  have ha4 : a.castSucc ≠ Fin.last 4 := Fin.castSucc_ne_last a
  have hb4 : b.castSucc ≠ Fin.last 4 := Fin.castSucc_ne_last b
  -- a row of S4 with two `none` entries at a, b is the all-none row
  have allnone : ∀ r ∈ S4, r a = none → r b = none → r = fun _ => none := fun r hr h1 h2 =>
    inj_of h4 hab hr hnone h1 h2
  refine ⟨fun _ _ => Set.mem_univ _, ?_, ?_⟩
  · -- injectivity
    rintro x hx y hy hxy
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨hxa, hxb⟩ := hxy
    rcases hx with (⟨β, hβ, hβι, r, hr, rfl⟩ | ⟨β, hβ, k, hk, r, hr, hrn, rfl⟩) | ⟨r, hr, rfl⟩ <;>
    rcases hy with (⟨γ, hγ, hγι, s, hs, rfl⟩ | ⟨γ, hγ, k', hk', s, hs, hsn, rfl⟩) | ⟨s, hs, rfl⟩
    -- A A
    · simp only [rowA, Sum.inl.injEq, Prod.mk.injEq] at hxa hxb
      rw [inj_of h5 hab' hβ hγ hxa.1 hxb.1, inj_of h3 hab hr hs hxa.2 hxb.2]
    -- A B
    · exfalso
      obtain ⟨s1, hs1, e1⟩ := rowB_eq_inl.mp hxa.symm
      obtain ⟨s2, hs2, e2⟩ := rowB_eq_inl.mp hxb.symm
      simp only [rowA, Prod.mk.injEq] at e1 e2
      have := inj_of h5 hab' hβ hγ e1.1 e2.1
      exact hβι k' (this ▸ hk')
    -- A C
    · simp [rowA, rowC] at hxa
    -- B A
    · exfalso
      obtain ⟨s1, hs1, e1⟩ := rowB_eq_inl.mp hxa
      obtain ⟨s2, hs2, e2⟩ := rowB_eq_inl.mp hxb
      simp only [rowA, Prod.mk.injEq] at e1 e2
      have := inj_of h5 hab' hβ hγ e1.1.symm e2.1.symm
      exact hγι k (this ▸ hk)
    -- B B
    · cases hra : r a with
      | none =>
        cases hrb : r b with
        | none => exact absurd (allnone r hr hra hrb) hrn
        | some v =>
          have xa : rowB β k r a = Sum.inr k := by simp [rowB, hra]
          have xb : rowB β k r b = Sum.inl (β b.castSucc, v) := by simp [rowB, hrb]
          rw [xa] at hxa; rw [xb] at hxb
          obtain ⟨hsa, rfl⟩ := rowB_eq_inr.mp hxa.symm
          obtain ⟨w, hsb, e⟩ := rowB_eq_inl.mp hxb.symm
          simp only [Prod.mk.injEq] at e
          have hβγ : β = γ := inj_of h5 hb4 hβ hγ e.1 (hk.symm.trans hk')
          subst hβγ
          rw [inj_of h4 hab hr hs (hra.trans hsa.symm) (hrb.trans (by rw [hsb, e.2]))]
      | some v =>
        have xa : rowB β k r a = Sum.inl (β a.castSucc, v) := by simp [rowB, hra]
        rw [xa] at hxa
        obtain ⟨w, hsa, e⟩ := rowB_eq_inl.mp hxa.symm
        simp only [Prod.mk.injEq] at e
        cases hrb : r b with
        | none =>
          have xb : rowB β k r b = Sum.inr k := by simp [rowB, hrb]
          rw [xb] at hxb
          obtain ⟨hsb, rfl⟩ := rowB_eq_inr.mp hxb.symm
          have hβγ : β = γ := inj_of h5 ha4 hβ hγ e.1 (hk.symm.trans hk')
          subst hβγ
          rw [inj_of h4 hab hr hs (hra.trans (by rw [hsa, e.2])) (hrb.trans hsb.symm)]
        | some v' =>
          have xb : rowB β k r b = Sum.inl (β b.castSucc, v') := by simp [rowB, hrb]
          rw [xb] at hxb
          obtain ⟨w', hsb, e'⟩ := rowB_eq_inl.mp hxb.symm
          simp only [Prod.mk.injEq] at e'
          have hβγ : β = γ := inj_of h5 hab' hβ hγ e.1 e'.1
          subst hβγ
          have hkk : k = k' := hι (hk.trans hk'.symm)
          subst hkk
          rw [inj_of h4 hab hr hs (hra.trans (by rw [hsa, e.2])) (hrb.trans (by rw [hsb, e'.2]))]
    -- B C
    · exfalso
      obtain ⟨h1, -⟩ := rowB_eq_inr.mp hxa
      obtain ⟨h2, -⟩ := rowB_eq_inr.mp hxb
      exact hrn (allnone r hr h1 h2)
    -- C A
    · simp [rowA, rowC] at hxa
    -- C B
    · exfalso
      obtain ⟨h1, -⟩ := rowB_eq_inr.mp hxa.symm
      obtain ⟨h2, -⟩ := rowB_eq_inr.mp hxb.symm
      exact hsn (allnone s hs h1 h2)
    -- C C
    · simp only [rowC, Sum.inr.injEq] at hxa hxb
      rw [inj_of hU hab hr hs hxa hxb]
  · -- surjectivity
    rintro ⟨P, Q⟩ -
    rcases P with ⟨p, α⟩ | k <;> rcases Q with ⟨q, α'⟩ | k'
    · obtain ⟨β, hβ, e1, e2⟩ := ex_of h5 hab' p q
      by_cases hι' : ∃ k, ι k = β (Fin.last 4)
      · obtain ⟨k, hk⟩ := hι'
        obtain ⟨r, hr, r1, r2⟩ := ex_of h4 hab (some α) (some α')
        refine ⟨rowB β k r, Or.inl (Or.inr ⟨β, hβ, k, hk, r, hr, fun h => by simp [h] at r1, rfl⟩), ?_⟩
        simp [rowB, r1, r2, e1, e2]
      · push_neg at hι'
        obtain ⟨r, hr, r1, r2⟩ := ex_of h3 hab α α'
        exact ⟨rowA β r, Or.inl (Or.inl ⟨β, hβ, hι', r, hr, rfl⟩), by simp [rowA, r1, r2, e1, e2]⟩
    · obtain ⟨β, hβ, e1, e2⟩ := ex_of h5 ha4 p (ι k')
      obtain ⟨r, hr, r1, r2⟩ := ex_of h4 hab (some α) none
      refine ⟨rowB β k' r, Or.inl (Or.inr ⟨β, hβ, k', e2.symm, r, hr, fun h => by simp [h] at r1, rfl⟩), ?_⟩
      simp [rowB, r1, r2, e1]
    · obtain ⟨β, hβ, e1, e2⟩ := ex_of h5 hb4 q (ι k)
      obtain ⟨r, hr, r1, r2⟩ := ex_of h4 hab none (some α')
      refine ⟨rowB β k r, Or.inl (Or.inr ⟨β, hβ, k, e2.symm, r, hr, fun h => by simp [h] at r2, rfl⟩), ?_⟩
      simp [rowB, r1, r2, e1]
    · obtain ⟨r, hr, r1, r2⟩ := ex_of hU hab k k'
      exact ⟨rowC r, Or.inr ⟨r, hr, rfl⟩, by simp [rowC, r1, r2]⟩


/-- An OA(4) on a finite type of size `n` gives an orthogonal pair of Latin squares of order `n`. -/
theorem pair_of_OA [Fintype α] {n : ℕ} (e : α ≃ Fin n) {S : Set (Fin 4 → α)} (h : IsOA 4 S) :
    ∃ L M : LatinSquare n, Erdos724.IsOrthogonal L M := by
  classical
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  let row : Fin n → Fin n → (Fin 4 → α) := fun i j => (ex_of h h01 (e.symm i) (e.symm j)).choose
  have hrow : ∀ i j, row i j ∈ S ∧ row i j 0 = e.symm i ∧ row i j 1 = e.symm j := fun i j =>
    (ex_of h h01 (e.symm i) (e.symm j)).choose_spec
  have key : ∀ (a b : Fin 4), a ≠ b → ∀ i j i' j', row i j a = row i' j' a → row i j b = row i' j' b →
      i = i' ∧ j = j' := by
    intro a b hab i j i' j' ha hb
    have := inj_of h hab (hrow i j).1 (hrow i' j').1 ha hb
    have h0 := congrFun this 0
    have h1 := congrFun this 1
    rw [(hrow i j).2.1, (hrow i' j').2.1] at h0
    rw [(hrow i j).2.2, (hrow i' j').2.2] at h1
    exact ⟨e.symm.injective h0, e.symm.injective h1⟩
  refine ⟨⟨fun i j => e (row i j 2), fun i j j' hj => ?_, fun j i i' hi => ?_⟩,
    ⟨fun i j => e (row i j 3), fun i j j' hj => ?_, fun j i i' hi => ?_⟩, ?_⟩
  · have hj : row i j 2 = row i j' 2 := e.injective hj
    exact (key 0 2 (by decide) i j i j' (by rw [(hrow i j).2.1, (hrow i j').2.1]) hj).2
  · have hi : row i j 2 = row i' j 2 := e.injective hi
    exact (key 1 2 (by decide) i j i' j (by rw [(hrow i j).2.2, (hrow i' j).2.2]) hi).1
  · have hj : row i j 3 = row i j' 3 := e.injective hj
    exact (key 0 3 (by decide) i j i j' (by rw [(hrow i j).2.1, (hrow i j').2.1]) hj).2
  · have hi : row i j 3 = row i' j 3 := e.injective hi
    exact (key 1 3 (by decide) i j i' j (by rw [(hrow i j).2.2, (hrow i' j).2.2]) hi).1
  · rintro ⟨i, j⟩ ⟨i', j'⟩ hp
    simp only [Prod.mk.injEq] at hp
    obtain ⟨hi, hj⟩ := key 2 3 (by decide) i j i' j' (e.injective hp.1) (e.injective hp.2)
    rw [hi, hj]


/-! ## Instantiation -/

lemma oa_of_range {ι α : Type*} [Fintype ι] [Fintype α] {k : ℕ} (f : ι → Fin k → α)
    (hcard : Fintype.card ι = Fintype.card α * Fintype.card α)
    (h : ∀ a b : Fin k, a ≠ b → Function.Injective fun i => (f i a, f i b)) :
    IsOA k (Set.range f) := by
  intro a b hab
  refine ⟨fun _ _ => Set.mem_univ _, ?_, ?_⟩
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
    rw [h a b hab hij]
  · intro xy _
    have hb : Function.Bijective fun i => (f i a, f i b) :=
      (Fintype.bijective_iff_injective_and_card _).mpr ⟨h a b hab, by rw [hcard, Fintype.card_prod]⟩
    obtain ⟨i, hi⟩ := hb.2 xy
    exact ⟨f i, ⟨i, rfl⟩, hi⟩

lemma lin_inj {t : ℕ} (p q r s : ZMod t) (hd : IsUnit (p * s - q * r)) {i j i' j' : ZMod t}
    (h1 : p * i + q * j = p * i' + q * j') (h2 : r * i + s * j = r * i' + s * j') :
    i = i' ∧ j = j' := by
  constructor
  · have : (p * s - q * r) * (i - i') = 0 := by linear_combination s * h1 - q * h2
    exact sub_eq_zero.mp ((hd.mul_right_eq_zero).mp this)
  · have : (p * s - q * r) * (j - j') = 0 := by linear_combination p * h2 - r * h1
    exact sub_eq_zero.mp ((hd.mul_right_eq_zero).mp this)

def cycRow {t k : ℕ} (c : Fin k → ZMod t × ZMod t) (ij : ZMod t × ZMod t) : Fin k → ZMod t :=
  fun a => (c a).1 * ij.1 + (c a).2 * ij.2

lemma cyc_OA {t k : ℕ} [NeZero t] (c : Fin k → ZMod t × ZMod t)
    (hc : ∀ a b, a ≠ b → IsUnit ((c a).1 * (c b).2 - (c a).2 * (c b).1)) :
    IsOA k (Set.range (cycRow c)) := by
  apply oa_of_range _ (by simp [Fintype.card_prod])
  intro a b hab
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  simp only [cycRow, Prod.mk.injEq] at h
  obtain ⟨hi, hj⟩ := lin_inj _ _ _ _ (hc a b hab) h.1 h.2
  rw [hi, hj]

def c5 {t : ℕ} : Fin 5 → ZMod t × ZMod t := ![(1, 0), (0, 1), (1, 1), (1, 2), (1, 3)]
def c4 {t : ℕ} : Fin 4 → ZMod t × ZMod t := ![(1, 0), (0, 1), (1, 1), (1, 2)]

lemma c5_det {t : ℕ} (h2 : IsUnit (2 : ZMod t)) (h3 : IsUnit (3 : ZMod t)) (a b : Fin 5)
    (hab : a ≠ b) : IsUnit ((c5 a).1 * (c5 b).2 - (c5 a).2 * (c5 b).1 : ZMod t) := by
  fin_cases a <;> fin_cases b <;> simp_all [c5] <;> norm_num <;>
    first | exact h2 | exact h3 | exact h2.neg | exact h3.neg | exact isUnit_one.neg | skip

lemma c4_det {t : ℕ} (h2 : IsUnit (2 : ZMod t)) (a b : Fin 4)
    (hab : a ≠ b) : IsUnit ((c4 a).1 * (c4 b).2 - (c4 a).2 * (c4 b).1 : ZMod t) := by
  fin_cases a <;> fin_cases b <;> simp_all [c4] <;> norm_num <;>
    first | exact h2 | exact h2.neg | exact isUnit_one.neg | skip

def T4 : Fin 4 → Fin 4 → Fin 4 → Fin 4 :=
  ![![![0, 0, 3, 0], ![0, 1, 1, 3], ![0, 2, 2, 2], ![0, 3, 0, 1]],
    ![![1, 0, 1, 1], ![1, 1, 3, 2], ![1, 2, 0, 3], ![1, 3, 2, 0]],
    ![![2, 0, 2, 3], ![2, 1, 0, 0], ![2, 2, 3, 1], ![2, 3, 1, 2]],
    ![![3, 0, 0, 2], ![3, 1, 2, 1], ![3, 2, 1, 0], ![3, 3, 3, 3]]]

def toOpt (x : Fin 4) : Option (Fin 3) := if h : x.val < 3 then some ⟨x.val, h⟩ else none

def f4 (p : Fin 4 × Fin 4) : Fin 4 → Option (Fin 3) := fun g => toOpt (T4 p.1 p.2 g)

lemma S4_OA : IsOA 4 (Set.range f4) :=
  oa_of_range f4 (by simp) (by decide +kernel)

lemma S4_none : (fun _ => none) ∈ Set.range f4 := ⟨(3, 3), by decide +kernel⟩

def ιtu (t u : ℕ) (k : ZMod u) : ZMod t := (k.val : ZMod t)

lemma ιtu_inj {t u : ℕ} [NeZero u] (hut : u ≤ t) : Function.Injective (ιtu t u) := by
  intro k k' h
  have hk := ZMod.val_cast_of_lt (n := t) (lt_of_lt_of_le (ZMod.val_lt k) hut)
  have hk' := ZMod.val_cast_of_lt (n := t) (lt_of_lt_of_le (ZMod.val_lt k') hut)
  apply ZMod.val_injective
  rw [← hk, ← hk']
  exact congrArg ZMod.val h

lemma unit_of_coprime {t m : ℕ} (h : Nat.Coprime m t) : IsUnit (m : ZMod t) :=
  (ZMod.isUnit_iff_coprime m t).mpr h

/-- Wilson (m = 3): 3 MOLS of order t (gcd(t,6) = 1) and a pair of odd order u ≤ t give a pair of
order 3t + u. -/
theorem pair_3t_u (t u : ℕ) (ht : Nat.Coprime 6 t) (hu : Odd u) (hut : u ≤ t) :
    ∃ L M : LatinSquare (3 * t + u), Erdos724.IsOrthogonal L M := by
  have : NeZero u := ⟨by rintro rfl; simp at hu⟩
  have : NeZero t := ⟨by rintro rfl; simp at ht⟩
  have h2t : IsUnit (2 : ZMod t) := by
    have := unit_of_coprime (Nat.Coprime.coprime_dvd_left (by norm_num : 2 ∣ 6) ht)
    exact_mod_cast this
  have h3t : IsUnit (3 : ZMod t) := by
    have := unit_of_coprime (Nat.Coprime.coprime_dvd_left (by norm_num : 3 ∣ 6) ht)
    exact_mod_cast this
  have h2u : IsUnit (2 : ZMod u) := by
    have := unit_of_coprime (t := u) (Nat.coprime_two_left.mpr hu)
    exact_mod_cast this
  have h23 : IsUnit (2 : ZMod 3) := by
    have := unit_of_coprime (t := 3) (m := 2) (by norm_num)
    exact_mod_cast this
  have hW := wilson_OA (T := ZMod t) (U := ZMod u)
    (cyc_OA (t := t) c5 (c5_det h2t h3t)) (cyc_OA (t := 3) c4 (c4_det h23)) S4_OA S4_none
    (cyc_OA (t := u) c4 (c4_det h2u)) (ιtu_inj hut)
  have e : ((ZMod t × Fin 3) ⊕ ZMod u) ≃ Fin (3 * t + u) :=
    Fintype.equivFinOfCardEq (by simp [Fintype.card_sum, Fintype.card_prod, ZMod.card]; ring)
  exact pair_of_OA e hW

end Study724W


namespace Study724

/-- Order 10, from the problem file's explicit squares. -/
lemma pair10 : ∃ L M : LatinSquare 10, Erdos724.IsOrthogonal L M :=
  ⟨Erdos724.latinSquare10, Erdos724.orthogonalMate10, by
    show Function.Injective fun p : Fin 10 × Fin 10 =>
      (Erdos724.latinSquare10Mat p.1 p.2, Erdos724.orthogonalMate10Mat p.1 p.2)
    decide +kernel⟩

lemma pair30 : ∃ L M : LatinSquare 30, Erdos724.IsOrthogonal L M := by
  obtain ⟨L, M, h⟩ := odd_pair 2 (by decide)
  obtain ⟨L', M', h'⟩ := pair10
  exact ⟨prodSq L L', prodSq M M', prod_orth h h'⟩

lemma coprime6 {t : ℕ} (h2 : t % 2 = 1) (h3 : t % 3 ≠ 0) : Nat.Coprime 6 t := by
  rw [show (6 : ℕ) = 2 * 3 by norm_num, Nat.coprime_mul_iff_left]
  exact ⟨Nat.coprime_two_left.mpr (Nat.odd_iff.mpr h2),
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by omega)⟩

/-- Every n ≡ 2 (mod 4), n ≥ 10, other than 10, 14, 30, is 3t + u with gcd(t,6) = 1, u odd, u ≤ t. -/
lemma split_3t_u (n : ℕ) (hn : 10 ≤ n) (h2 : n % 4 = 2) (h10 : n ≠ 10) (h14 : n ≠ 14)
    (h30 : n ≠ 30) : ∃ t u, t % 2 = 1 ∧ t % 3 ≠ 0 ∧ u % 2 = 1 ∧ u ≤ t ∧ n = 3 * t + u := by
  have hr : n % 24 = 2 ∨ n % 24 = 6 ∨ n % 24 = 10 ∨ n % 24 = 14 ∨ n % 24 = 18 ∨ n % 24 = 22 := by
    omega
  rcases hr with hr | hr | hr | hr | hr | hr
  · exact ⟨6 * (n / 24) + 1, n - 3 * (6 * (n / 24) + 1), by omega, by omega, by omega, by omega,
      by omega⟩
  · exact ⟨6 * (n / 24) + 5, n - 3 * (6 * (n / 24) + 5), by omega, by omega, by omega, by omega,
      by omega⟩
  · exact ⟨6 * (n / 24) + 5, n - 3 * (6 * (n / 24) + 5), by omega, by omega, by omega, by omega,
      by omega⟩
  · exact ⟨6 * (n / 24) + 5, n - 3 * (6 * (n / 24) + 5), by omega, by omega, by omega, by omega,
      by omega⟩
  · exact ⟨6 * (n / 24) + 5, n - 3 * (6 * (n / 24) + 5), by omega, by omega, by omega, by omega,
      by omega⟩
  · exact ⟨6 * (n / 24) + 7, n - 3 * (6 * (n / 24) + 7), by omega, by omega, by omega, by omega,
      by omega⟩

def L14Mat : Matrix (Fin 14) (Fin 14) (Fin 14) :=
  !![12, 4, 8, 1, 6, 2, 13, 0, 7, 9, 11, 10, 5, 3;
    11, 12, 5, 9, 2, 7, 3, 13, 1, 8, 10, 0, 6, 4;
    0, 11, 12, 6, 10, 3, 8, 4, 13, 2, 9, 1, 7, 5;
    10, 1, 11, 12, 7, 0, 4, 9, 5, 13, 3, 2, 8, 6;
    4, 0, 2, 11, 12, 8, 1, 5, 10, 6, 13, 3, 9, 7;
    13, 5, 1, 3, 11, 12, 9, 2, 6, 0, 7, 4, 10, 8;
    8, 13, 6, 2, 4, 11, 12, 10, 3, 7, 1, 5, 0, 9;
    2, 9, 13, 7, 3, 5, 11, 12, 0, 4, 8, 6, 1, 10;
    9, 3, 10, 13, 8, 4, 6, 11, 12, 1, 5, 7, 2, 0;
    6, 10, 4, 0, 13, 9, 5, 7, 11, 12, 2, 8, 3, 1;
    3, 7, 0, 5, 1, 13, 10, 6, 8, 11, 12, 9, 4, 2;
    5, 6, 7, 8, 9, 10, 0, 1, 2, 3, 4, 11, 12, 13;
    7, 8, 9, 10, 0, 1, 2, 3, 4, 5, 6, 12, 13, 11;
    1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 13, 11, 12]

def M14Mat : Matrix (Fin 14) (Fin 14) (Fin 14) :=
  !![3, 12, 1, 13, 8, 2, 7, 9, 11, 5, 4, 0, 10, 6;
    5, 4, 12, 2, 13, 9, 3, 8, 10, 11, 6, 1, 0, 7;
    7, 6, 5, 12, 3, 13, 10, 4, 9, 0, 11, 2, 1, 8;
    11, 8, 7, 6, 12, 4, 13, 0, 5, 10, 1, 3, 2, 9;
    2, 11, 9, 8, 7, 12, 5, 13, 1, 6, 0, 4, 3, 10;
    1, 3, 11, 10, 9, 8, 12, 6, 13, 2, 7, 5, 4, 0;
    8, 2, 4, 11, 0, 10, 9, 12, 7, 13, 3, 6, 5, 1;
    4, 9, 3, 5, 11, 1, 0, 10, 12, 8, 13, 7, 6, 2;
    13, 5, 10, 4, 6, 11, 2, 1, 0, 12, 9, 8, 7, 3;
    10, 13, 6, 0, 5, 7, 11, 3, 2, 1, 12, 9, 8, 4;
    12, 0, 13, 7, 1, 6, 8, 11, 4, 3, 2, 10, 9, 5;
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 12;
    6, 7, 8, 9, 10, 0, 1, 2, 3, 4, 5, 12, 11, 13;
    9, 10, 0, 1, 2, 3, 4, 5, 6, 7, 8, 13, 12, 11]

lemma pair14 : ∃ L M : LatinSquare 14, Erdos724.IsOrthogonal L M :=
  ⟨⟨L14Mat, by show ∀ i, Function.Injective fun j => L14Mat i j; decide +kernel,
      by show ∀ j, Function.Injective fun i => L14Mat i j; decide +kernel⟩,
    ⟨M14Mat, by show ∀ i, Function.Injective fun j => M14Mat i j; decide +kernel,
      by show ∀ j, Function.Injective fun i => M14Mat i j; decide +kernel⟩,
    by show Function.Injective fun p : Fin 14 × Fin 14 => (L14Mat p.1 p.2, M14Mat p.1 p.2)
       decide +kernel⟩


lemma pair_two_mod_four (n : ℕ) (h2 : n % 4 = 2) (h10 : 10 ≤ n) :
    ∃ L M : LatinSquare n, L ≠ M ∧ Erdos724.IsOrthogonal L M := by
  have hp : ∃ L M : LatinSquare n, Erdos724.IsOrthogonal L M := by
    by_cases ha : n = 10
    · subst ha; exact pair10
    by_cases hb : n = 14
    · subst hb; exact pair14
    by_cases hc : n = 30
    · subst hc; exact pair30
    obtain ⟨t, u, ht2, ht3, hu, hut, rfl⟩ := split_3t_u n h10 h2 ha hb hc
    exact Study724W.pair_3t_u t u (coprime6 ht2 ht3) (Nat.odd_iff.mpr hu) hut
  obtain ⟨L, M, h⟩ := hp
  exact ⟨L, M, fun heq => not_orth_self (by omega) L (by rwa [← heq] at h), h⟩

end Study724


theorem OMA.solution : OMA.R_Erdos724_erdos_724_variants_bose_parker_shrikhande_R1_H3_R1.H1 := by
  intro p hp h5
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  obtain ⟨r, rfl⟩ := hodd
  exact Study724.pair_two_mod_four (2 * (2 * r + 1)) (by omega) (by omega)
