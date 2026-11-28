import OMAStatements.S_oeis_a187157

/-!
Count the placements of each simple three-move bishop path by independent horizontal
and vertical intervals. The one-dimensional path bijection builds on @Salofe's proof
for the asymmetric piece in open-math-agents PR #18044.
-/

namespace OMA.BishopPaths

open OMA.S_oeis_a187157 Finset

/-- A step: `+1` for `true` and `-1` for `false`. -/
def sd (b : Bool) : ℤ := if b then 1 else -1

/-- The positions reached by a word of three steps, relative to the start. -/
def off (w : Bool × Bool × Bool) : Fin 4 → ℤ :=
  ![0, sd w.1, sd w.1 + sd w.2.1, sd w.1 + sd w.2.1 + sd w.2.2]

/-- A one-dimensional path of three steps `-1` or `+1`. -/
def Step {n : ℕ} (q : Fin 4 → Fin n) : Prop :=
  (((q 1 : ℤ) - q 0 = -1 ∨ (q 1 : ℤ) - q 0 = 1) ∧
    ((q 2 : ℤ) - q 1 = -1 ∨ (q 2 : ℤ) - q 1 = 1) ∧
    ((q 3 : ℤ) - q 2 = -1 ∨ (q 3 : ℤ) - q 2 = 1))

instance decStep {n : ℕ} : DecidablePred (@Step n) := fun q => by
  unfold Step; infer_instance

/-- The word of a path. -/
def word {n : ℕ} (q : Fin 4 → Fin n) : Bool × Bool × Bool :=
  (decide ((q 1 : ℤ) - q 0 = 1), decide ((q 2 : ℤ) - q 1 = 1), decide ((q 3 : ℤ) - q 2 = 1))

theorem pos_eq {n : ℕ} (q : Fin 4 → Fin n) (h : Step q) (k : Fin 4) :
    (q k : ℤ) = q 0 + off (word q) k := by
  obtain ⟨h1, h2, h3⟩ := h
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
    fin_cases k <;> simp [off, word, sd, h1, h2, h3] <;> omega

/-- The starts that keep the word `w` inside a line of `n` positions. -/
def win (n : ℕ) (w : Bool × Bool × Bool) : Finset (Fin n) :=
  univ.filter (fun s : Fin n => ∀ k, 0 ≤ (s : ℤ) + off w k ∧ (s : ℤ) + off w k < n)

theorem fiber_card (n : ℕ) (w : Bool × Bool × Bool) :
    (univ.filter (fun q : Fin 4 → Fin n => Step q ∧ word q = w)).card = (win n w).card := by
  refine Finset.card_bij (fun q _ => q 0) ?_ ?_ ?_
  · intro q hq
    simp only [mem_filter, mem_univ, true_and] at hq
    simp only [win, mem_filter, mem_univ, true_and]
    intro k
    have e := pos_eq q hq.1 k
    rw [hq.2] at e
    have := (q k).isLt
    omega
  · intro q hq q' hq' h0
    simp only [mem_filter, mem_univ, true_and] at hq hq'
    funext k
    have e := pos_eq q hq.1 k
    have e' := pos_eq q' hq'.1 k
    rw [hq.2] at e
    rw [hq'.2] at e'
    rw [h0] at e
    apply Fin.ext
    omega
  · intro s hs
    simp only [win, mem_filter, mem_univ, true_and] at hs
    let q : Fin 4 → Fin n := fun k => ⟨((s : ℤ) + off w k).toNat, by have := hs k; omega⟩
    have hq : ∀ k, ((q k : ℕ) : ℤ) = (s : ℤ) + off w k := by
      intro k
      have := hs k
      simp only [q]
      omega
    refine ⟨q, ?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and]
      have e1 := hq 1
      have e2 := hq 2
      have e3 := hq 3
      have e0 := hq 0
      obtain ⟨b1, b2, b3⟩ := w
      simp only [off, Matrix.cons_val, sd] at e0 e1 e2 e3
      refine ⟨?_, ?_⟩
      · unfold Step
        cases b1 <;> cases b2 <;> cases b3 <;> simp at e0 e1 e2 e3 <;> omega
      · unfold word
        cases b1 <;> cases b2 <;> cases b3 <;> simp at e0 e1 e2 e3 <;> simp <;> omega
    · apply Fin.ext
      have := hq 0
      simp [off] at this
      omega

theorem card_window (n lo hi : ℕ) (P : Fin n → Prop) [DecidablePred P]
    (hP : ∀ s : Fin n, P s ↔ lo ≤ s.val ∧ s.val + hi < n) :
    (univ.filter P).card = n - (lo + hi) := by
  rw [← card_map Fin.valEmbedding]
  have : (univ.filter P).map Fin.valEmbedding = Ico lo (n - hi) := by
    ext t
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_Ico]
    constructor
    · rintro ⟨s, hs, rfl⟩
      rw [hP] at hs
      omega
    · intro ht
      exact ⟨⟨t, by omega⟩, (hP _).2 (by simp only; omega), rfl⟩
  rw [this, Nat.card_Ico]
  omega

theorem win_card (n : ℕ) (w : Bool × Bool × Bool) (lo hi : ℕ)
    (h : ∀ s : Fin n, (∀ k, 0 ≤ (s : ℤ) + off w k ∧ (s : ℤ) + off w k < n) ↔
      lo ≤ s.val ∧ s.val + hi < n) : (win n w).card = n - (lo + hi) :=
  card_window n lo hi _ h


private def span (w : Bool × Bool × Bool) : ℕ :=
  if w.1 = w.2.1 ∧ w.2.1 = w.2.2 then 3 else
    if w.1 ≠ w.2.1 ∧ w.2.1 ≠ w.2.2 then 1 else 2

private theorem placements (n : ℕ) (w : Bool × Bool × Bool) :
    (win n w).card = n - span w := by
  obtain ⟨i,j,k⟩ := w
  cases i <;> cases j <;> cases k
  · exact win_card n _ 3 0 (by intro s; simp [Fin.forall_fin_succ, off, sd]; omega)
  · exact win_card n _ 2 0 (by intro s; simp [Fin.forall_fin_succ, off, sd]; omega)
  · exact win_card n _ 1 0 (by intro s; simp [Fin.forall_fin_succ, off, sd])
  · exact win_card n _ 1 1 (by intro s; simp [Fin.forall_fin_succ, off, sd]; omega)
  · exact win_card n _ 1 1 (by intro s; simp [Fin.forall_fin_succ, off, sd]; omega)
  · exact win_card n _ 0 1 (by intro s; simp [Fin.forall_fin_succ, off, sd]; omega)
  · exact win_card n _ 0 2 (by intro s; simp [Fin.forall_fin_succ, off, sd]; omega)
  · exact win_card n _ 0 3 (by intro s; simp [Fin.forall_fin_succ, off, sd]; omega)

private def good (u v : Bool × Bool × Bool) : Prop :=
  (u.1 = u.2.1 ∨ v.1 = v.2.1) ∧ (u.2.1 = u.2.2 ∨ v.2.1 = v.2.2)

private instance (u v : Bool × Bool × Bool) : Decidable (good u v) := by unfold good; infer_instance

private theorem shape_injective (u v : Bool × Bool × Bool) :
    Function.Injective (fun k : Fin 4 => (off u k, off v k)) ↔ good u v := by
  obtain ⟨i,j,k⟩ := u
  obtain ⟨l,m,n⟩ := v
  cases i <;> cases j <;> cases k <;> cases l <;> cases m <;> cases n <;> decide

private theorem moves_iff (d : ℤ × ℤ) :
    d ∈ moves ↔ (d.1 = -1 ∨ d.1 = 1) ∧ (d.2 = -1 ∨ d.2 = 1) := by
  obtain ⟨x, y⟩ := d
  simp only [moves, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
  omega

private theorem is_tour {n : ℕ} (p : Fin 4 → Fin n × Fin n) :
    IsTour n 4 p ↔ Step (fun k => (p k).1) ∧ Step (fun k => (p k).2) ∧
      good (word fun k => (p k).1) (word fun k => (p k).2) := by
  let x := fun k => (p k).1
  let y := fun k => (p k).2
  have moves_equiv :
      (∀ i j : Fin 4, j.val = i.val + 1 → toZ (p j) - toZ (p i) ∈ moves) ↔ Step x ∧ Step y := by
    constructor
    · intro h
      have h1 := (moves_iff _).1 (h 0 1 rfl)
      have h2 := (moves_iff _).1 (h 1 2 rfl)
      have h3 := (moves_iff _).1 (h 2 3 rfl)
      exact ⟨⟨h1.1,h2.1,h3.1⟩,⟨h1.2,h2.2,h3.2⟩⟩
    · rintro ⟨⟨h1,h2,h3⟩,⟨g1,g2,g3⟩⟩ i j hij
      apply (moves_iff _).2
      fin_cases i <;> fin_cases j <;> simp at hij <;>
        first | exact ⟨h1,g1⟩ | exact ⟨h2,g2⟩ | exact ⟨h3,g3⟩
  unfold IsTour
  rw [moves_equiv]
  change _ ↔ Step x ∧ Step y ∧ good (word x) (word y)
  have eq_iff (hx : Step x) (hy : Step y) (i j : Fin 4) :
      p i = p j ↔ (off (word x) i, off (word y) i) = (off (word x) j, off (word y) j) := by
    have x1 := pos_eq x hx i
    have x2 := pos_eq x hx j
    have y1 := pos_eq y hy i
    have y2 := pos_eq y hy j
    constructor
    · intro h
      have ex : ((x i : ℕ) : ℤ) = x j := congrArg (fun t : Fin n × Fin n => ((t.1 : ℕ) : ℤ)) h
      have ey : ((y i : ℕ) : ℤ) = y j := congrArg (fun t : Fin n × Fin n => ((t.2 : ℕ) : ℤ)) h
      exact Prod.ext (by omega) (by omega)
    · intro h
      have ex := congrArg Prod.fst h
      have ey := congrArg Prod.snd h
      simp only at ex ey
      exact Prod.ext (Fin.ext (show (x i).val = (x j).val by omega))
        (Fin.ext (show (y i).val = (y j).val by omega))
  constructor
  · rintro ⟨inj,hx,hy⟩
    exact ⟨hx,hy,(shape_injective _ _).1 (fun {i j} h => inj ((eq_iff hx hy i j).2 h))⟩
  · rintro ⟨hx,hy,goodShape⟩
    exact ⟨fun {i j} h => (shape_injective _ _).2 goodShape ((eq_iff hx hy i j).1 h),hx,hy⟩


private theorem a_count (n : ℕ) :
    a n = ∑ u : Bool × Bool × Bool, ∑ v : Bool × Bool × Bool,
      if good u v then (n - span u) * (n - span v) else 0 := by
  let walks := univ.filter (fun pq : (Fin 4 → Fin n) × (Fin 4 → Fin n) =>
    Step pq.1 ∧ Step pq.2 ∧ good (word pq.1) (word pq.2))
  have hwalking : a n = walks.card := by
    unfold a
    apply Finset.card_equiv (Equiv.arrowProdEquivProdArrow (Fin 4) (fun _ => Fin n) (fun _ => Fin n))
    intro p
    simp only [walks, mem_filter, mem_univ, true_and]
    rw [is_tour]
    rfl
  rw [hwalking, card_eq_sum_card_fiberwise (f := fun pq => (word pq.1, word pq.2)) (t := univ)
    (fun _ _ => mem_univ _), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : good u v
  · rw [if_pos h, ← placements, ← placements, ← fiber_card, ← fiber_card, ← card_product]
    congr 1
    ext ⟨x,y⟩
    simp only [walks, mem_filter, mem_univ, true_and, mem_product, Prod.mk.injEq]
    constructor
    · tauto
    · rintro ⟨⟨hx,hu⟩,⟨hy,hv⟩⟩
      exact ⟨⟨hx,hy,hu ▸ hv ▸ h⟩,hu,hv⟩
  · rw [if_neg h, card_eq_zero, filter_eq_empty_iff]
    intro q hq he
    simp only [walks, mem_filter, mem_univ, true_and] at hq
    obtain ⟨hu,hv⟩ := Prod.mk.inj he
    exact h (hu ▸ hv ▸ hq.2.2)

private theorem count (n : ℕ) : a n =
    4*(n-3)*(n-3) + 16*(n-3)*(n-2) + 8*(n-2)*(n-2) + 8*(n-3)*(n-1) := by
  rw [a_count]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  simp [good, span]
  ring

private theorem quadratic (n : ℕ) (hn : 2 < n) : (a n : ℤ) = 36*n^2 - 168*n + 188 := by
  rw [count]
  push_cast [show 3 ≤ n by omega, show 2 ≤ n by omega, show 1 ≤ n by omega]
  ring

private theorem recurrence (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = 3*a (n-1) - 3*a (n-2) + a (n-3) := by
  rw [quadratic n (by omega), quadratic (n-1) (by omega),
    quadratic (n-2) (by omega), quadratic (n-3) (by omega)]
  push_cast [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega]
  ring

open PowerSeries in
private theorem gf :
    mk (fun n => (a n : ℤ)) * (1 - X)^3 = 4*X^3*(2+17*X-X^2) := by
  let A : ℤ⟦X⟧ := mk fun n => (a n : ℤ)
  change A * _ = _
  have den : A*(1-X)^3 = A - (A*X^1 + A*X^1 + A*X^1) +
      (A*X^2 + A*X^2 + A*X^2) - A*X^3 := by ring
  have num : 4*(X : ℤ⟦X⟧)^3*(2+17*X-X^2) = C (8 : ℤ)*X^3+C (68 : ℤ)*X^4-C (4 : ℤ)*X^5 := by
    simp only [map_ofNat]; ring
  rw [den,num]
  ext n
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_mul_X_pow', A, coeff_mk]
  by_cases hn : n ≤ 5
  · interval_cases n <;> norm_num [count]
  · have hr := recurrence n (by omega)
    simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
      show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega, if_true, if_false]
    linarith

end OMA.BishopPaths

theorem OMA.solution : type_of% @OMA.S_oeis_a187157.main :=
  ⟨OMA.BishopPaths.quadratic, OMA.BishopPaths.gf, OMA.BishopPaths.recurrence⟩
