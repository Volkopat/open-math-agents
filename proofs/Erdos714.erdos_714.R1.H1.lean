import OMAReductions.R_Erdos714_erdos_714_R1
import Mathlib

namespace OMA.E714H1

open Filter SimpleGraph

variable {F : Type*} [Field F]

/-- The quadratic form `Q v = v1 v2 + v3^2`. -/
def Qf (v : F × F × F) : F := v.1 * v.2.1 + v.2.2 ^ 2

/-- Its polar form `β v w = Q (v + w) - Q v - Q w`. -/
def Bf (v w : F × F × F) : F := v.1 * w.2.1 + v.2.1 * w.1 + 2 * v.2.2 * w.2.2

/-- `β d u = d · P u` for the standard dot product. -/
def Pm (v : F × F × F) : F × F × F := (v.2.1, v.1, 2 * v.2.2)

def dt (v w : F × F × F) : F := v.1 * w.1 + v.2.1 * w.2.1 + v.2.2 * w.2.2

def cr (v w : F × F × F) : F × F × F :=
  (v.2.1 * w.2.2 - v.2.2 * w.2.1, v.2.2 * w.1 - v.1 * w.2.2, v.1 * w.2.1 - v.2.1 * w.1)

lemma Qf_add (v w : F × F × F) : Qf (v + w) = Qf v + Bf v w + Qf w := by
  obtain ⟨_, _, _⟩ := v; obtain ⟨_, _, _⟩ := w
  simp only [Qf, Bf, Prod.mk_add_mk]; ring

lemma Qf_smul (s : F) (v : F × F × F) : Qf (s • v) = s ^ 2 * Qf v := by
  obtain ⟨_, _, _⟩ := v
  simp only [Qf, Prod.smul_mk, smul_eq_mul]; ring

lemma Bf_smul (s : F) (v w : F × F × F) : Bf v (s • w) = s * Bf v w := by
  obtain ⟨_, _, _⟩ := v; obtain ⟨_, _, _⟩ := w
  simp only [Bf, Prod.smul_mk, smul_eq_mul]; ring

lemma Bf_sub (v v' w : F × F × F) : Bf (v - v') w = Bf v w - Bf v' w := by
  obtain ⟨_, _, _⟩ := v; obtain ⟨_, _, _⟩ := v'; obtain ⟨_, _, _⟩ := w
  simp only [Bf, Prod.mk_sub_mk]; ring

lemma Bf_eq (d u : F × F × F) : Bf d u = dt d (Pm u) := by
  obtain ⟨_, _, _⟩ := d; obtain ⟨_, _, _⟩ := u
  simp only [Bf, dt, Pm]; ring

lemma cr_cr (d a b : F × F × F) : cr d (cr a b) = dt d b • a - dt d a • b := by
  obtain ⟨_, _, _⟩ := d; obtain ⟨_, _, _⟩ := a; obtain ⟨_, _, _⟩ := b
  simp only [cr, dt, Prod.smul_mk, Prod.mk_sub_mk, smul_eq_mul, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

lemma Qf_neg (v : F × F × F) : Qf (-v) = Qf v := by
  obtain ⟨_, _, _⟩ := v
  simp only [Qf, Prod.neg_mk]; ring

/-- The sphere `Q = a` contains no isotropic line when `a` is a nonsquare. -/
lemma noline (a : F) (ha : ¬ IsSquare a) (e y : F × F × F) (he : e ≠ 0)
    (hQ : Qf e = 0) (hB : Bf y e = 0) (hy : Qf y = a) : False := by
  obtain ⟨e1, e2, e3⟩ := e
  obtain ⟨y1, y2, y3⟩ := y
  simp only [Qf, Bf] at hQ hB hy
  by_cases h1 : e1 = 0
  · by_cases h2 : e2 = 0
    · subst h1 h2
      have h3 : e3 = 0 := by
        have : e3 ^ 2 = 0 := by linear_combination hQ
        exact pow_eq_zero_iff (two_ne_zero) |>.1 this
      exact he (by rw [h3]; rfl)
    · apply ha
      have key : a * e2 ^ 2 = (y3 * e2 - y2 * e3) ^ 2 := by
        linear_combination (-y2 ^ 2) * hQ + y2 * e2 * hB - e2 ^ 2 * hy
      refine ⟨(y3 * e2 - y2 * e3) / e2, ?_⟩
      field_simp
      linear_combination key
  · apply ha
    have key : a * e1 ^ 2 = (y3 * e1 - y1 * e3) ^ 2 := by
      linear_combination (-y1 ^ 2) * hQ + y1 * e1 * hB - e1 ^ 2 * hy
    refine ⟨(y3 * e1 - y1 * e3) / e1, ?_⟩
    field_simp
    linear_combination key

/-- A vector whose cross product with a nonzero `n` vanishes is a multiple of `n`. -/
lemma par (n d : F × F × F) (hn : n ≠ 0) (h : cr d n = 0) : ∃ s : F, d = s • n := by
  obtain ⟨n1, n2, n3⟩ := n
  obtain ⟨d1, d2, d3⟩ := d
  simp only [cr, Prod.mk_eq_zero] at h
  obtain ⟨c1, c2, c3⟩ := h
  by_cases h1 : n1 = 0
  · by_cases h2 : n2 = 0
    · have h3 : n3 ≠ 0 := by
        rintro rfl; subst h1 h2; exact hn rfl
      refine ⟨d3 / n3, ?_⟩
      simp only [Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]
      refine ⟨?_, ?_, ?_⟩ <;> field_simp
      · linear_combination -c2
      · linear_combination c1
    · refine ⟨d2 / n2, ?_⟩
      simp only [Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]
      refine ⟨?_, ?_, ?_⟩ <;> field_simp
      · linear_combination c3
      · linear_combination -c1
  · refine ⟨d1 / n1, ?_⟩
    simp only [Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩ <;> field_simp
    · linear_combination -c3
    · linear_combination c2

/-- Core: three distinct points cannot all lie on three distinct spheres `Q (x - w) = a`. -/
lemma core (a : F) (h2 : (2 : F) ≠ 0) (ha : ¬ IsSquare a) (x1 x2 x3 w1 w2 w3 : F × F × F)
    (hx12 : x1 ≠ x2) (hx13 : x1 ≠ x3) (hx23 : x2 ≠ x3)
    (hw12 : w1 ≠ w2) (hw13 : w1 ≠ w3) (hw23 : w2 ≠ w3)
    (h11 : Qf (x1 - w1) = a) (h12 : Qf (x1 - w2) = a) (h13 : Qf (x1 - w3) = a)
    (h21 : Qf (x2 - w1) = a) (h22 : Qf (x2 - w2) = a) (h23 : Qf (x2 - w3) = a)
    (h31 : Qf (x3 - w1) = a) (h32 : Qf (x3 - w2) = a) (h33 : Qf (x3 - w3) = a) : False := by
  set y1 := x1 - w1 with hy1
  set y2 := x1 - w2 with hy2
  set y3 := x1 - w3 with hy3
  set u := x2 - x1 with hu
  set v := x3 - x1 with hv
  have hu0 : u ≠ 0 := fun h => hx12 (sub_eq_zero.1 h).symm
  have hv0 : v ≠ 0 := fun h => hx13 (sub_eq_zero.1 h).symm
  have huv : u ≠ v := fun h => hx23 (by simpa [hu, hv] using h)
  have e1 : ∀ w : F × F × F, x2 - w = (x1 - w) + u := fun w => by rw [hu]; abel
  have e2 : ∀ w : F × F × F, x3 - w = (x1 - w) + v := fun w => by rw [hv]; abel
  have fu : ∀ y, Qf y = a → Qf (y + u) = a → Bf y u + Qf u = 0 := fun y h h' => by
    rw [Qf_add, h] at h'; linear_combination h'
  have fv : ∀ y, Qf y = a → Qf (y + v) = a → Bf y v + Qf v = 0 := fun y h h' => by
    rw [Qf_add, h] at h'; linear_combination h'
  have u1 := fu y1 h11 (by rw [← e1]; exact h21)
  have u2 := fu y2 h12 (by rw [← e1]; exact h22)
  have u3 := fu y3 h13 (by rw [← e1]; exact h23)
  have v1 := fv y1 h11 (by rw [← e2]; exact h31)
  have v2 := fv y2 h12 (by rw [← e2]; exact h32)
  have v3 := fv y3 h13 (by rw [← e2]; exact h33)
  by_cases hn : cr (Pm u) (Pm v) = 0
  · -- u and v are parallel
    have hPu : Pm u ≠ 0 := by
      intro h
      apply hu0
      obtain ⟨u1', u2', u3'⟩ := u
      simp only [Pm, Prod.mk_eq_zero, mul_eq_zero, h2, false_or] at h
      obtain ⟨a1, a2, a3⟩ := h
      rw [a1, a2, a3]; rfl
    have hc : cr (Pm v) (Pm u) = 0 := by
      have : cr (Pm v) (Pm u) = - cr (Pm u) (Pm v) := by
        simp only [cr, Prod.neg_mk, Prod.mk.injEq]; refine ⟨by ring, by ring, by ring⟩
      rw [this, hn, neg_zero]
    obtain ⟨l, hl⟩ := par (Pm u) (Pm v) hPu hc
    have hvl : v = l • u := by
      clear_value u v
      obtain ⟨p1, p2, p3⟩ := u
      obtain ⟨q1, q2, q3⟩ := v
      simp only [Pm, Prod.smul_mk, smul_eq_mul, Prod.mk.injEq] at hl ⊢
      obtain ⟨b1, b2, b3⟩ := hl
      refine ⟨b2, b1, ?_⟩
      apply mul_left_cancel₀ h2
      linear_combination b3
    rw [hvl, Bf_smul, Qf_smul] at v1
    have hl0 : l ≠ 0 := by
      rintro rfl; apply hv0; rw [hvl, zero_smul]
    have hl1 : l ≠ 1 := by
      rintro rfl; apply huv; rw [hvl, one_smul]
    have hq : l * (l - 1) * Qf u = 0 := by linear_combination v1 - l * u1
    have hQu : Qf u = 0 := by
      rcases mul_eq_zero.1 hq with h | h
      · rcases mul_eq_zero.1 h with h | h
        · exact absurd h hl0
        · exact absurd (sub_eq_zero.1 h) hl1
      · exact h
    exact noline a ha u y1 hu0 hQu (by linear_combination u1 - hQu) h11
  · -- u and v independent: the difference vectors are parallel to n
    set n := cr (Pm u) (Pm v) with hndef
    have pd : ∀ d, Bf d u = 0 → Bf d v = 0 → ∃ s : F, d = s • n := by
      intro d hdu hdv
      apply par n d hn
      rw [hndef, cr_cr, ← Bf_eq, ← Bf_eq, hdu, hdv, zero_smul, zero_smul, sub_zero]
    obtain ⟨s, hs⟩ := pd (y2 - y1) (by rw [Bf_sub]; linear_combination u2 - u1)
      (by rw [Bf_sub]; linear_combination v2 - v1)
    obtain ⟨s', hs'⟩ := pd (y3 - y1) (by rw [Bf_sub]; linear_combination u3 - u1)
      (by rw [Bf_sub]; linear_combination v3 - v1)
    have hd : y2 - y1 = w1 - w2 := by rw [hy1, hy2]; abel
    have hd' : y3 - y1 = w1 - w3 := by rw [hy1, hy3]; abel
    have hs0 : s ≠ 0 := by
      rintro rfl; apply hw12; rw [zero_smul, hd] at hs; exact sub_eq_zero.1 hs
    have hss : s ≠ s' := by
      rintro rfl; apply hw23
      have : w1 - w2 = w1 - w3 := by rw [← hd, ← hd', hs, hs']
      exact sub_right_injective this
    have q2 : Qf (y1 + s • n) = a := by rw [← hs]; simpa using h12
    have q3 : Qf (y1 + s' • n) = a := by rw [← hs']; simpa using h13
    rw [Qf_add, Bf_smul, Qf_smul, h11] at q2 q3
    have r2 : Bf y1 n + s * Qf n = 0 := by
      have : s * (Bf y1 n + s * Qf n) = 0 := by linear_combination q2
      exact (mul_eq_zero.1 this).resolve_left hs0
    have hs'0 : s' ≠ 0 := by
      rintro rfl; apply hw13; rw [zero_smul, hd'] at hs'; exact sub_eq_zero.1 hs'
    have r3 : Bf y1 n + s' * Qf n = 0 := by
      have : s' * (Bf y1 n + s' * Qf n) = 0 := by linear_combination q3
      exact (mul_eq_zero.1 this).resolve_left hs'0
    have hQn : Qf n = 0 := by
      have : (s - s') * Qf n = 0 := by linear_combination r2 - r3
      exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hss)
    exact noline a ha n y1 hn hQn (by linear_combination r2 - s * hQn) h11

/-- The bipartite unit-sphere graph over `ZMod p` (`p` an odd prime), padded with `k` isolated
vertices, is `K_{3,3}`-free with at least `p^4 (p - 1)` edges. -/
theorem graph_bound3 (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (k : ℕ) :
    p ^ 4 * (p - 1) ≤
      extremalNumber (2 * p ^ 3 + k) (completeBipartiteGraph (Fin 3) (Fin 3)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    rcases (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h' with h''
    exact hp2 h''
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by
    rw [ZMod.ringChar_zmod_n]; exact hp2)
  let V := ZMod p × ZMod p × ZMod p
  let r : (V ⊕ V) ⊕ Fin k → (V ⊕ V) ⊕ Fin k → Prop :=
    fun u v => ∃ x y : V, u = Sum.inl (Sum.inl x) ∧ v = Sum.inl (Sum.inr y) ∧ Qf (x - y) = a
  let G := SimpleGraph.fromRel r
  have hcard : Fintype.card ((V ⊕ V) ⊕ Fin k) = 2 * p ^ 3 + k := by
    simp [V, ZMod.card]; ring
  have adjP : ∀ (x : V) z, G.Adj (Sum.inl (Sum.inl x)) z →
      ∃ y : V, z = Sum.inl (Sum.inr y) ∧ Qf (x - y) = a := by
    intro x z h
    simp only [G, r, fromRel_adj] at h
    obtain ⟨-, ⟨x', y', h1, rfl, h3⟩ | ⟨x', y', h1, h2, h3⟩⟩ := h
    · simp only [Sum.inl.injEq] at h1
      subst h1
      exact ⟨y', rfl, h3⟩
    · simp at h2
  have adjL : ∀ (y : V) z, G.Adj (Sum.inl (Sum.inr y)) z →
      ∃ x : V, z = Sum.inl (Sum.inl x) ∧ Qf (x - y) = a := by
    intro y z h
    simp only [G, r, fromRel_adj] at h
    obtain ⟨-, ⟨x', y', h1, h2, h3⟩ | ⟨x', y', rfl, h2, h3⟩⟩ := h
    · simp at h1
    · simp only [Sum.inl.injEq, Sum.inr.injEq] at h2
      subst h2
      exact ⟨x', rfl, h3⟩
  have adjI : ∀ (i : Fin k) z, ¬ G.Adj (Sum.inr i) z := by
    intro i z h
    simp only [G, r, fromRel_adj] at h
    obtain ⟨-, ⟨x', y', h1, h2, h3⟩ | ⟨x', y', h1, h2, h3⟩⟩ := h
    · simp at h1
    · simp at h2
  have PP : ∀ (x y : V), G.Adj (Sum.inl (Sum.inl x)) (Sum.inl (Sum.inr y)) → Qf (x - y) = a := by
    intro x y h
    obtain ⟨y', e, h'⟩ := adjP x _ h
    simp only [Sum.inl.injEq, Sum.inr.injEq] at e
    subst e; exact h'
  have key : ∀ u1 u2 u3 w1 w2 w3, u1 ≠ u2 → u1 ≠ u3 → u2 ≠ u3 → w1 ≠ w2 → w1 ≠ w3 → w2 ≠ w3 →
      G.Adj u1 w1 → G.Adj u1 w2 → G.Adj u1 w3 → G.Adj u2 w1 → G.Adj u2 w2 → G.Adj u2 w3 →
      G.Adj u3 w1 → G.Adj u3 w2 → G.Adj u3 w3 → False := by
    intro u1 u2 u3 w1 w2 w3 d12 d13 d23 e12 e13 e23 a11 a12 a13 a21 a22 a23 a31 a32 a33
    rcases u1 with ((x1 | y1) | i)
    · obtain ⟨y1, rfl, -⟩ := adjP _ _ a11
      obtain ⟨y2, rfl, -⟩ := adjP _ _ a12
      obtain ⟨y3, rfl, -⟩ := adjP _ _ a13
      obtain ⟨x2, rfl, -⟩ := adjL _ _ a21.symm
      obtain ⟨x3, rfl, -⟩ := adjL _ _ a31.symm
      exact core a h2 ha x1 x2 x3 y1 y2 y3 (fun h => d12 (by rw [h])) (fun h => d13 (by rw [h]))
        (fun h => d23 (by rw [h])) (fun h => e12 (by rw [h])) (fun h => e13 (by rw [h]))
        (fun h => e23 (by rw [h])) (PP _ _ a11) (PP _ _ a12) (PP _ _ a13) (PP _ _ a21)
        (PP _ _ a22) (PP _ _ a23) (PP _ _ a31) (PP _ _ a32) (PP _ _ a33)
    · obtain ⟨x1, rfl, -⟩ := adjL _ _ a11
      obtain ⟨x2, rfl, -⟩ := adjL _ _ a12
      obtain ⟨x3, rfl, -⟩ := adjL _ _ a13
      obtain ⟨y2, rfl, -⟩ := adjP _ _ a21.symm
      obtain ⟨y3, rfl, -⟩ := adjP _ _ a31.symm
      exact core a h2 ha x1 x2 x3 y1 y2 y3 (fun h => e12 (by rw [h])) (fun h => e13 (by rw [h]))
        (fun h => e23 (by rw [h])) (fun h => d12 (by rw [h])) (fun h => d13 (by rw [h]))
        (fun h => d23 (by rw [h])) (PP _ _ a11.symm) (PP _ _ a21.symm) (PP _ _ a31.symm)
        (PP _ _ a12.symm) (PP _ _ a22.symm) (PP _ _ a32.symm) (PP _ _ a13.symm)
        (PP _ _ a23.symm) (PP _ _ a33.symm)
    · exact adjI i w1 a11
  have hfree : (completeBipartiteGraph (Fin 3) (Fin 3)).Free G := by
    rintro ⟨f⟩
    have hadj : ∀ i j : Fin 3, G.Adj (f (Sum.inl i)) (f (Sum.inr j)) := fun i j =>
      f.toHom.map_adj (by simp [completeBipartiteGraph])
    have hinj := f.injective
    exact key (f (Sum.inl 0)) (f (Sum.inl 1)) (f (Sum.inl 2)) (f (Sum.inr 0)) (f (Sum.inr 1))
      (f (Sum.inr 2))
      (fun h => absurd (hinj h) (by simp)) (fun h => absurd (hinj h) (by simp))
      (fun h => absurd (hinj h) (by simp)) (fun h => absurd (hinj h) (by simp))
      (fun h => absurd (hinj h) (by simp)) (fun h => absurd (hinj h) (by simp))
      (hadj 0 0) (hadj 0 1) (hadj 0 2) (hadj 1 0) (hadj 1 1) (hadj 1 2)
      (hadj 2 0) (hadj 2 1) (hadj 2 2)
  have hedge : p ^ 4 * (p - 1) ≤ G.edgeFinset.card := by
    let zf : ZMod p × ZMod p → V := fun t => (t.1, (a - t.2 ^ 2) / t.1, t.2)
    let φ : V × ZMod p × ZMod p → Sym2 ((V ⊕ V) ⊕ Fin k) :=
      fun t => s(Sum.inl (Sum.inl t.1), Sum.inl (Sum.inr (t.1 - zf t.2)))
    let D : Finset (V × ZMod p × ZMod p) :=
      (Finset.univ : Finset V) ×ˢ ((Finset.univ.erase (0 : ZMod p)) ×ˢ Finset.univ)
    have h1 : D.card = p ^ 4 * (p - 1) := by
      simp only [D, Finset.card_product, Finset.card_univ, Finset.card_erase_of_mem
        (Finset.mem_univ _), V, Fintype.card_prod, ZMod.card]
      ring
    rw [← h1]
    refine Finset.card_le_card_of_injOn φ ?_ ?_
    · rintro ⟨x, z1, z3⟩ ht
      simp only [D, Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_erase,
        Finset.mem_univ, and_true, true_and] at ht
      simp only [Finset.mem_coe, mem_edgeFinset, φ, mem_edgeSet, G, r, fromRel_adj]
      refine ⟨by simp, Or.inl ⟨x, _, rfl, rfl, ?_⟩⟩
      rw [sub_sub_cancel]
      simp only [zf, Qf]
      field_simp
      ring
    · rintro ⟨x, z1, z3⟩ _ ⟨x', z1', z3'⟩ _ h
      simp only [φ, Sym2.eq_iff, Sum.inl.injEq, Sum.inr.injEq,
        reduceCtorEq, and_false, or_false] at h
      obtain ⟨rfl, h'⟩ := h
      have h'' : zf (z1, z3) = zf (z1', z3') := sub_right_injective h'
      have e1 : z1 = z1' := congrArg Prod.fst h''
      have e3 : z3 = z3' := congrArg (fun q : V => q.2.2) h''
      rw [e1, e3]
  calc p ^ 4 * (p - 1) ≤ G.edgeFinset.card := hedge
    _ ≤ extremalNumber (Fintype.card ((V ⊕ V) ⊕ Fin k))
          (completeBipartiteGraph (Fin 3) (Fin 3)) := card_edgeFinset_le_extremalNumber hfree
    _ = _ := by rw [hcard]

end OMA.E714H1

theorem OMA.solution : OMA.R_Erdos714_erdos_714_R1.H1 := by
  refine ⟨1 / 4096, by norm_num, Filter.eventually_atTop.2 ⟨512, fun n hn => ?_⟩⟩
  set t : ℝ := (n : ℝ) ^ ((1 : ℝ) / 3) with ht
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have ht0 : 0 ≤ t := Real.rpow_nonneg hn0 _
  have ht3 : t ^ 3 = n := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hn0]; norm_num
  have ht5 : (n : ℝ) ^ ((2 : ℝ) - 1 / (3 : ℝ)) = t ^ 5 := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hn0]; norm_num
  have ht8 : 8 ≤ t := by
    by_contra h
    push Not at h
    have : t ^ 3 < 8 ^ 3 := pow_lt_pow_left₀ h ht0 (by norm_num)
    have h512 : (512 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  set m := ⌊t / 4⌋₊ with hm
  have hm2 : 2 ≤ m := by
    rw [hm]; exact Nat.le_floor (by push_cast; linarith)
  obtain ⟨p, hp, hmp, hp2m⟩ := Nat.exists_prime_lt_and_le_two_mul m (by omega)
  have hmt : (m : ℝ) ≤ t / 4 := Nat.floor_le (by positivity)
  have hmt' : t / 4 < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hpR : (p : ℝ) ≤ 2 * m := by exact_mod_cast hp2m
  have hmpR : (m : ℝ) + 1 ≤ p := by exact_mod_cast hmp
  have hp3 : 3 ≤ p := by omega
  have hp3R : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hpn : 2 * p ^ 3 ≤ n := by
    have h1 : (p : ℝ) ≤ t / 2 := by linarith
    have h2 : (p : ℝ) ^ 3 ≤ (t / 2) ^ 3 := pow_le_pow_left₀ (by positivity) h1 3
    have h3 : (2 : ℝ) * p ^ 3 ≤ n := by nlinarith
    exact_mod_cast h3
  have hex := OMA.E714H1.graph_bound3 p hp (by omega) (n - 2 * p ^ 3)
  rw [show 2 * p ^ 3 + (n - 2 * p ^ 3) = n by omega] at hex
  have hexR : (p : ℝ) ^ 4 * ((p : ℝ) - 1) ≤
      (SimpleGraph.extremalNumber n (completeBipartiteGraph (Fin 3) (Fin 3)) : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).2 hex
    push_cast [Nat.cast_sub hp.one_le] at this
    exact this
  rw [ht5]
  have htp : t < 4 * p := by linarith
  have h5 : t ^ 5 ≤ (4 * p) ^ 5 := pow_le_pow_left₀ ht0 htp.le 5
  have hp0 : (0 : ℝ) ≤ (p : ℝ) ^ 4 := by positivity
  have hhalf : (p : ℝ) ^ 4 * (p / 2) ≤ (p : ℝ) ^ 4 * ((p : ℝ) - 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hp0
  calc 1 / 4096 * t ^ 5 ≤ 1 / 4096 * (4 * p) ^ 5 := by linarith
    _ ≤ (p : ℝ) ^ 4 * (p / 2) := by ring_nf; nlinarith [pow_nonneg (Nat.cast_nonneg p : (0:ℝ) ≤ p) 5]
    _ ≤ _ := hhalf.trans hexR
