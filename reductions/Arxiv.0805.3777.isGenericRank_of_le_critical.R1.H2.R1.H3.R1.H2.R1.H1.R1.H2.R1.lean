import OMAReductions.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1_H1_R1

namespace OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1_H1_R1_H2_R1

private theorem pad {a b r h : ℕ}
    (mark : Fin h ↪ Fin r) (x : Fin r → Fin (a + 1) → ℂ) (y : Fin r → Fin b → ℂ)
    (nonzero : ∀ t, x (mark t) 0 ≠ 0)
    (independent : ∀ F : Fin h → Fin (a + 1) × Fin b → ℂ,
      (∀ t s, ∑ ij : Fin (a + 1) × Fin b, (x s ij.1 * y s ij.2) * F t ij = 0) →
      (∀ t i, ∑ j, y (mark t) j * F t (i,j) = 0) →
      (∀ t j, ∑ i, x (mark t) i * F t (i,j) = 0) →
      (∑ t, F t) = 0 → F = 0) :
    (∃ mark : Fin h ↪ (Fin r ⊕ Fin a), ∃ x : (Fin r ⊕ Fin a) → Fin (a + 1) → ℂ, ∃ y : (Fin r ⊕ Fin a) → (Fin b ⊕ Unit) → ℂ,
      ∀ F : Fin h → Fin (a + 1) × (Fin b ⊕ Unit) → ℂ,
        (∀ t s, ∑ ij : Fin (a + 1) × (Fin b ⊕ Unit), (x s ij.1 * y s ij.2) * F t ij = 0) →
        (∀ t i, ∑ j, y (mark t) j * F t (i,j) = 0) →
        (∀ t j, ∑ i, x (mark t) i * F t (i,j) = 0) →
        (∑ t, F t) = 0 → F = 0) := by
  classical
  let X : Fin r ⊕ Fin a → Fin (a + 1) → ℂ :=
    Sum.elim x (fun p i => if i = p.succ then 1 else 0)
  let Y : Fin r ⊕ Fin a → Fin b ⊕ Unit → ℂ :=
    Sum.elim (fun s => Sum.elim (y s) (fun _ => 0)) (fun _ => Sum.elim (fun _ => 0) (fun _ => 1))
  refine ⟨mark.trans Function.Embedding.inl, X, Y, ?_⟩
  intro F prod rows cols total
  let G (t : Fin h) (ij : Fin (a + 1) × Fin b) := F t (ij.1, Sum.inl ij.2)
  have leftZero : G = 0 := by
    apply independent
    · intro t s
      have he := prod t (.inl s)
      rw [Fintype.sum_prod_type] at he ⊢
      simpa [X, Y, G, Fintype.sum_sum_type] using he
    · intro t i
      simpa [Y, G, Fintype.sum_sum_type] using rows t i
    · intro t j
      simpa [X, G] using cols t (.inl j)
    · funext ij
      simpa [G, Finset.sum_apply] using congrFun total (ij.1, Sum.inl ij.2)
  have rightZero (t : Fin h) (i : Fin (a + 1)) : F t (i, .inr ()) = 0 := by
    have high (p : Fin a) : F t (p.succ, .inr ()) = 0 := by
      have he := prod t (.inr p)
      rw [Fintype.sum_prod_type] at he
      simpa [X, Y, Fintype.sum_sum_type, ite_mul] using he
    refine Fin.cases ?_ high i
    have he := cols t (.inr ())
    change (∑ j : Fin (a + 1), x (mark t) j * F t (j, .inr ())) = 0 at he
    rw [Fin.sum_univ_succ] at he
    simp only [high, mul_zero, Finset.sum_const_zero, add_zero] at he
    exact (mul_eq_zero.mp he).resolve_left (nonzero t)
  funext t ij
  obtain ⟨i, j|j⟩ := ij
  · exact congrFun (congrFun leftZero t) (i, j)
  · cases j
    exact rightZero t i

private theorem transport {A B P Q A' B' P' Q' : Type*}
    [Fintype A] [Fintype B] [Fintype P] [Fintype Q]
    [Fintype A'] [Fintype B'] [Fintype P'] [Fintype Q']
    (ea : A ≃ A') (eb : B ≃ B') (ep : P ≃ P') (eq : Q ≃ Q') :
    (∃ mark : Q ↪ P, ∃ x : P → A → ℂ, ∃ y : P → B → ℂ,
      ∀ F : Q → A × B → ℂ,
        (∀ t s, ∑ ij : A × B, (x s ij.1 * y s ij.2) * F t ij = 0) →
        (∀ t i, ∑ j, y (mark t) j * F t (i,j) = 0) →
        (∀ t j, ∑ i, x (mark t) i * F t (i,j) = 0) →
        (∑ t, F t) = 0 → F = 0) → (∃ mark : Q' ↪ P', ∃ x : P' → A' → ℂ, ∃ y : P' → B' → ℂ,
      ∀ F : Q' → A' × B' → ℂ,
        (∀ t s, ∑ ij : A' × B', (x s ij.1 * y s ij.2) * F t ij = 0) →
        (∀ t i, ∑ j, y (mark t) j * F t (i,j) = 0) →
        (∀ t j, ∑ i, x (mark t) i * F t (i,j) = 0) →
        (∑ t, F t) = 0 → F = 0) := by
  rintro ⟨mark, x, y, indep⟩
  let newMark := (eq.symm.toEmbedding.trans mark).trans ep.toEmbedding
  let X (s : P') (i : A') := x (ep.symm s) (ea.symm i)
  let Y (s : P') (j : B') := y (ep.symm s) (eb.symm j)
  refine ⟨newMark, X, Y, ?_⟩
  intro F prods rows cols total
  let G (t : Q) (ij : A × B) := F (eq t) (ea ij.1, eb ij.2)
  have hprod (t : Q) (s : P) :
      ∑ ij : A × B, (x s ij.1 * y s ij.2) * G t ij = 0 := by
    have h := prods (eq t) (ep s)
    rw [← (ea.prodCongr eb).sum_comp] at h
    simpa [X, Y, G, Equiv.prodCongr_apply, Prod.map] using h
  have hrows (t : Q) (i : A) : ∑ j, y (mark t) j * G t (i,j) = 0 := by
    have h := rows (eq t) (ea i)
    rw [← eb.sum_comp] at h
    simpa [newMark, Y, G] using h
  have hcols (t : Q) (j : B) : ∑ i, x (mark t) i * G t (i,j) = 0 := by
    have h := cols (eq t) (eb j)
    rw [← ea.sum_comp] at h
    simpa [newMark, X, G] using h
  have htotal : (∑ t, G t) = 0 := by
    rw [← eq.sum_comp] at total
    funext ij
    simpa [G, Finset.sum_apply] using congrFun total (ea ij.1, eb ij.2)
  have z := indep G hprod hrows hcols htotal
  funext t ij
  simpa [G] using congrFun (congrFun z (eq.symm t)) (ea.symm ij.1, eb.symm ij.2)

/-- Square witnesses with a nonzero first coordinate at each mark also
supply the one-column rectangles by padding. -/
def H1 : Prop :=
  ∀ (a : ℕ) (_ha : 4 ≤ a),
    let r := (a-1)*(a-1)-1
    ∃ mark : Fin a ↪ Fin r, ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin a → ℂ,
      (∀ t, x (mark t) ⟨0, by omega⟩ ≠ 0) ∧
      ∀ F : Fin a → Fin a × Fin a → ℂ,
        (∀ t s, ∑ ij : Fin a × Fin a, (x s ij.1*y s ij.2)*F t ij=0) →
        (∀ t i, ∑ j, y (mark t) j*F t (i,j)=0) →
        (∀ t j, ∑ i, x (mark t) i*F t (i,j)=0) → (∑ t,F t)=0 → F=0

/-- In the two-column-gap family, all a+1 marks are needed. -/
def H2 : Prop :=
  ∀ a : ℕ, 4 ≤ a →
    let r := (a-1)*(a+1)-1
    ∃ mark : Fin (a+1) ↪ Fin r, ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin (a+2) → ℂ,
      ∀ F : Fin (a+1) → Fin a × Fin (a+2) → ℂ,
        (∀ t s, ∑ ij : Fin a × Fin (a+2), (x s ij.1 * y s ij.2) * F t ij = 0) →
        (∀ t i, ∑ j, y (mark t) j * F t (i,j) = 0) →
        (∀ t j, ∑ i, x (mark t) i * F t (i,j) = 0) →
        (∑ t, F t) = 0 → F = 0

/-- A square core with one more independent normal line than the
unperturbed conic construction provides. The cross construction
extends this core to the b=3a-2 family. -/
def H3 : Prop :=
  ∀ a : ℕ, 4 ≤ a →
    let r := (a-1)*(a-1)
    let m := 2*a-1
    ∃ mark : Fin m ↪ Fin r, ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin a → ℂ,
      (∀ t, x (mark t) ≠ 0) ∧
      (∀ s t, s ≠ t → x (mark s) ∉ Submodule.span ℂ {x (mark t)}) ∧
      ∀ F : Fin m → Fin a × Fin a → ℂ,
        (∀ t s, ∑ ij : Fin a × Fin a, (x s ij.1*y s ij.2)*F t ij=0) →
        (∀ t i, ∑ j, y (mark t) j*F t (i,j)=0) →
        (∀ t j, ∑ i, x (mark t) i*F t (i,j)=0) → (∑ t,F t)=0 → F=0

theorem main : H1 → H2 → H3 → OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1_H1_R1.H2 := by
  intro square two core a b ha _ formats
  rcases formats with ⟨eq, _⟩ | rfl | rfl | tall
  · subst b
    dsimp only
    rw [show (a+a)/2=a by omega]
    obtain ⟨mark,x,y,_,h⟩ := square a ha
    exact ⟨mark,x,y,h⟩
  · obtain ⟨d,rfl⟩ : ∃ d, a=d+1 := ⟨a-1,by omega⟩
    dsimp only
    rw [show (d+1+(d+1+1))/2=d+1 by omega]
    obtain ⟨mark,x,y,nz,h⟩ := square (d+1) ha
    have cardCols : Fintype.card (Fin (d+1) ⊕ Unit) = d+1+1 := by simp
    have hr : ((d+1-1)*(d+1-1)-1)+d=(d+1-1)*(d+1+1-1)-1 := by
      simp only [Nat.add_sub_cancel]
      have hpos : 1 ≤ d*d := Nat.mul_pos (by omega) (by omega)
      rw [Nat.mul_add]
      omega
    exact transport (Equiv.refl _) (Fintype.equivFinOfCardEq cardCols)
      (finSumFinEquiv.trans (finCongr hr)) (Equiv.refl _) (pad mark x y nz h)
  · dsimp only
    rw [show (a+(a+2))/2=a+1 by omega,show a+2-1=a+1 by omega]
    exact two a ha
  · have hb : b = a+(2*a-2) := by omega
    subst b
    dsimp only
    rw [show (a+(a+(2*a-2)))/2=2*a-1 by omega]
    obtain ⟨mark,x,y,nz,sep,h⟩ := core a ha
    exact CriticalLastSlice.TwoPlanes.Cross.split_marked
      (by omega) (by omega) (by omega) (by omega) mark x y h nz sep

end OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1_H1_R1_H2_R1
