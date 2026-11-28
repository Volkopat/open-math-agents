import OMAReductions.R_wpc_vp_vs_vnp_R1

-- Step wpc-vp-vs-vnp.R1.H1: hypothesis H1 of reduction wpc-vp-vs-vnp.R1
-- Credit: @my-other-github-account

/-!
The directed Hamiltonian-cycle family is in VNP.

The witness is a Boolean `n × n` matrix `y`, read as an ordering `k ↦ σ k` of the
vertices. The verifier checks that `y` is the graph of a permutation fixing the root `0`
(every row and every column meets `y`, rows meet it at most once) and multiplies the
edges `σ k → σ (k + 1)` of the cyclic tour. Tours starting at `0` correspond bijectively
to directed Hamiltonian cycles via `σ ↦ σ * finRotate n * σ⁻¹`. The verifier has `O(n³)`
gates and degree `O(n³)`. The cycle family is the one of OpenAI math
`lean/OAI/Computability/VPVNP/Hamiltonian.lean` (commit 3344da59, Apache-2.0); this
verifier is a short direct construction rather than the source's machine compiler.
-/

namespace OMA.P_wpc_vp_vs_vnp_R1_H1

open MvPolynomial OMA.S_wpc_vp_vs_vnp Equiv
open scoped Classical

noncomputable section

/-! ## Polynomial bounds -/

theorem pb_of_le {f g : ℕ → ℕ} (h : ∀ n, f n ≤ g n) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded f := by
  obtain ⟨A, d, N, hN⟩ := hg
  exact ⟨A, d, N, fun n hn => (h n).trans (hN n hn)⟩

theorem pb_const (c : ℕ) : PolynomiallyBounded (fun _ => c) := ⟨c, 0, 0, fun n _ => by simp⟩

theorem pb_id : PolynomiallyBounded (fun n => n) := ⟨1, 1, 0, fun n _ => by simp⟩

theorem pb_add {f g : ℕ → ℕ} (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n => f n + g n) := by
  obtain ⟨A, d, N, hN⟩ := hf
  obtain ⟨B, e, M, hM⟩ := hg
  refine ⟨A + B, d + e, max (max N M) 1, fun n hn => ?_⟩
  have h1 : 1 ≤ n := le_of_max_le_right hn
  have hn' := le_of_max_le_left hn
  have hd : n ^ d ≤ n ^ (d + e) := Nat.pow_le_pow_right h1 (by omega)
  have he : n ^ e ≤ n ^ (d + e) := Nat.pow_le_pow_right h1 (by omega)
  calc f n + g n ≤ A * n ^ d + B * n ^ e :=
        Nat.add_le_add (hN n (le_of_max_le_left hn')) (hM n (le_of_max_le_right hn'))
    _ ≤ A * n ^ (d + e) + B * n ^ (d + e) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ hd) (Nat.mul_le_mul_left _ he)
    _ = (A + B) * n ^ (d + e) := by ring

theorem pb_mul {f g : ℕ → ℕ} (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n => f n * g n) := by
  obtain ⟨A, d, N, hN⟩ := hf
  obtain ⟨B, e, M, hM⟩ := hg
  refine ⟨A * B, d + e, max N M, fun n hn => ?_⟩
  calc f n * g n ≤ (A * n ^ d) * (B * n ^ e) :=
        Nat.mul_le_mul (hN n (le_of_max_le_left hn)) (hM n (le_of_max_le_right hn))
    _ = A * B * n ^ (d + e) := by ring

/-! ## Straight-line programs with a size and degree budget -/

section Circuits

variable {F σ : Type*} [Field F]

/-- Operands available after the gates `B`. -/
def Av (B : List (MvPolynomial σ F)) (x : MvPolynomial σ F) : Prop :=
  (∃ j, X j = x) ∨ (∃ a, C a = x) ∨ x ∈ B

/-- `x` is one binary gate applied to operands available after `B`. -/
def Gt (B : List (MvPolynomial σ F)) (x : MvPolynomial σ F) : Prop :=
  ∃ a b, Av B a ∧ Av B b ∧ (x = a + b ∨ x = a - b ∨ x = a * b)

/-- The gates `L`, listed oldest first, are legal after the gates `B`. -/
def Ok : List (MvPolynomial σ F) → List (MvPolynomial σ F) → Prop
  | _, [] => True
  | B, x :: L => Gt B x ∧ Ok (B ++ [x]) L

theorem av_mono {B B' : List (MvPolynomial σ F)} (h : B ⊆ B') {x} (hx : Av B x) : Av B' x := by
  rcases hx with hx | hx | hx
  · exact Or.inl hx
  · exact Or.inr (Or.inl hx)
  · exact Or.inr (Or.inr (h hx))

theorem gt_mono {B B' : List (MvPolynomial σ F)} (h : B ⊆ B') {x} (hx : Gt B x) : Gt B' x := by
  obtain ⟨a, b, ha, hb, hx⟩ := hx
  exact ⟨a, b, av_mono h ha, av_mono h hb, hx⟩

theorem ok_mono (L : List (MvPolynomial σ F)) :
    ∀ {B B' : List (MvPolynomial σ F)}, B ⊆ B' → Ok B L → Ok B' L := by
  induction L with
  | nil => intros; trivial
  | cons x L ih =>
    intro B B' h hL
    refine ⟨gt_mono h hL.1, ih ?_ hL.2⟩
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact List.mem_append_left _ (h ha)
    · exact List.mem_append_right _ ha

theorem ok_append (L₁ : List (MvPolynomial σ F)) :
    ∀ {B L₂}, Ok B (L₁ ++ L₂) ↔ Ok B L₁ ∧ Ok (B ++ L₁) L₂ := by
  induction L₁ with
  | nil => intros; simp [Ok]
  | cons x L ih =>
    intro B L₂
    simp only [List.cons_append, Ok, ih, List.append_assoc,
      List.nil_append, and_assoc]

theorem ok_gate (L : List (MvPolynomial σ F)) :
    ∀ {B}, Ok B L → ∀ i (h : i < L.length), Gt (B ++ L.take i) L[i] := by
  induction L with
  | nil => intro B _ i h; simp at h
  | cons x L ih =>
    intro B hL i h
    cases i with
    | zero => simpa using hL.1
    | succ i =>
      have := ih hL.2 i (by simpa using h)
      simpa [List.take_succ_cons] using this

theorem ok_replicate (k : ℕ) :
    ∀ {B : List (MvPolynomial σ F)}, Ok B (List.replicate k (C 0 + C 0)) := by
  induction k with
  | zero => intro; trivial
  | succ k ih =>
    intro B
    exact ⟨⟨C 0, C 0, Or.inr (Or.inl ⟨0, rfl⟩), Or.inr (Or.inl ⟨0, rfl⟩), Or.inl rfl⟩, ih⟩

theorem mem_take_iff' {α} {L : List α} {k : ℕ} {x : α} :
    x ∈ L.take k ↔ ∃ j : Fin L.length, j.val < k ∧ L[j.val] = x := by
  rw [List.mem_take_iff_getElem]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨j, by omega⟩, show j < k by omega, rfl⟩
  · rintro ⟨⟨j, hj⟩, hk, rfl⟩
    change j < k at hk
    exact ⟨j, by omega, rfl⟩

theorem computes_of_ok {L : List (MvPolynomial σ F)} {p : MvPolynomial σ F} (hL : Ok [] L)
    (hp : Av L p) : Computes L.length p := by
  refine ⟨fun i => L[i.val], ?_⟩
  dsimp only
  have hav : ∀ k x, Av (L.take k) x → ((∃ j, X j = x) ∨ (∃ a, C a = x) ∨
      ∃ j : Fin L.length, j.val < k ∧ L[j.val] = x) := by
    intro k x hx
    rcases hx with hx | hx | hx
    · exact Or.inl hx
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr (mem_take_iff'.mp hx))
  refine ⟨hav _ _ (by simpa using hp), fun i => ?_⟩
  obtain ⟨a, b, ha, hb, hx⟩ := ok_gate L hL i.val i.isLt
  exact ⟨a, b, hav _ _ (by simpa using ha), hav _ _ (by simpa using hb), hx⟩

/-- `p` has a program of at most `s` gates. -/
def CC (s : ℕ) (p : MvPolynomial σ F) : Prop := ∃ L, Ok [] L ∧ L.length ≤ s ∧ Av L p

theorem CC.computes {s : ℕ} {p : MvPolynomial σ F} (h : CC s p) : Computes s p := by
  obtain ⟨L, hL, hs, hp⟩ := h
  have hlen : (L ++ List.replicate (s - L.length) (C 0 + C 0)).length = s := by
    simp; omega
  rw [← hlen]
  refine computes_of_ok ((ok_append L).mpr ⟨hL, ok_replicate _⟩) ?_
  exact av_mono (List.subset_append_left _ _) hp

theorem cc_op {s t : ℕ} {p q r : MvPolynomial σ F} (hp : CC s p) (hq : CC t q)
    (hr : r = p + q ∨ r = p - q ∨ r = p * q) : CC (s + t + 1) r := by
  obtain ⟨L₁, h₁, s₁, a₁⟩ := hp
  obtain ⟨L₂, h₂, s₂, a₂⟩ := hq
  refine ⟨L₁ ++ L₂ ++ [r], ?_, by simp; omega, Or.inr (Or.inr (by simp))⟩
  rw [ok_append, ok_append]
  refine ⟨⟨h₁, ok_mono _ (List.nil_subset _) h₂⟩, ⟨?_, trivial⟩⟩
  simp only [List.nil_append]
  exact ⟨p, q, av_mono (List.subset_append_left _ _) a₁,
    av_mono (List.subset_append_right _ _) a₂, hr⟩

/-- A program with at most `s` gates computing a polynomial of degree at most `d`. -/
def Cir (s d : ℕ) (p : MvPolynomial σ F) : Prop := CC s p ∧ p.totalDegree ≤ d

theorem cir_X (j : σ) : Cir 0 1 (X j : MvPolynomial σ F) :=
  ⟨⟨[], trivial, le_rfl, Or.inl ⟨j, rfl⟩⟩, (totalDegree_X j).le⟩

theorem cir_C (a : F) : Cir 0 0 (C a : MvPolynomial σ F) :=
  ⟨⟨[], trivial, le_rfl, Or.inr (Or.inl ⟨a, rfl⟩)⟩, by simp⟩

theorem cir_one : Cir 0 0 (1 : MvPolynomial σ F) := by simpa using cir_C (σ := σ) (1 : F)

theorem cir_zero : Cir 0 0 (0 : MvPolynomial σ F) := by simpa using cir_C (σ := σ) (0 : F)

theorem cir_mono {s d s' d' : ℕ} {p : MvPolynomial σ F} (h : Cir s d p) (hs : s ≤ s')
    (hd : d ≤ d') : Cir s' d' p := by
  obtain ⟨⟨L, hL, hl, hp⟩, hdeg⟩ := h
  exact ⟨⟨L, hL, hl.trans hs, hp⟩, hdeg.trans hd⟩

theorem cir_add {s t d : ℕ} {p q : MvPolynomial σ F} (hp : Cir s d p) (hq : Cir t d q) :
    Cir (s + t + 1) d (p + q) :=
  ⟨cc_op hp.1 hq.1 (Or.inl rfl), (totalDegree_add p q).trans (max_le hp.2 hq.2)⟩

theorem cir_sub {s t d : ℕ} {p q : MvPolynomial σ F} (hp : Cir s d p) (hq : Cir t d q) :
    Cir (s + t + 1) d (p - q) :=
  ⟨cc_op hp.1 hq.1 (Or.inr (Or.inl rfl)), (totalDegree_sub p q).trans (max_le hp.2 hq.2)⟩

theorem cir_mul {s t d e : ℕ} {p q : MvPolynomial σ F} (hp : Cir s d p) (hq : Cir t e q) :
    Cir (s + t + 1) (d + e) (p * q) :=
  ⟨cc_op hp.1 hq.1 (Or.inr (Or.inr rfl)), (totalDegree_mul p q).trans (Nat.add_le_add hp.2 hq.2)⟩

theorem cir_one_sub {s d : ℕ} {p : MvPolynomial σ F} (hp : Cir s d p) :
    Cir (s + 1) d (1 - p) := by
  simpa using cir_sub (cir_mono cir_one le_rfl (Nat.zero_le d)) hp

theorem cir_prod {ι : Type*} (S : Finset ι) {c d : ℕ} {f : ι → MvPolynomial σ F}
    (h : ∀ i ∈ S, Cir c d (f i)) : Cir (S.card * (c + 1)) (S.card * d) (∏ i ∈ S, f i) := by
  induction S using Finset.induction_on with
  | empty => simpa using (cir_one : Cir 0 0 (1 : MvPolynomial σ F))
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    refine cir_mono (cir_mul (h a (by simp)) (ih fun i hi => h i (by simp [hi]))) ?_ ?_
    · exact le_of_eq (by ring)
    · exact le_of_eq (by ring)

theorem cir_sum {ι : Type*} (S : Finset ι) {c d : ℕ} {f : ι → MvPolynomial σ F}
    (h : ∀ i ∈ S, Cir c d (f i)) : Cir (S.card * (c + 1)) d (∑ i ∈ S, f i) := by
  induction S using Finset.induction_on with
  | empty =>
    simpa using cir_mono (cir_zero : Cir 0 0 (0 : MvPolynomial σ F)) le_rfl (Nat.zero_le d)
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
    refine cir_mono (cir_add (h a (by simp)) (ih fun i hi => h i (by simp [hi]))) ?_ le_rfl
    exact le_of_eq (by ring)

theorem cir_prod_fin {n c d : ℕ} {f : Fin n → MvPolynomial σ F} (h : ∀ i, Cir c d (f i)) :
    Cir (n * (c + 1)) (n * d) (∏ i, f i) := by
  simpa using cir_prod Finset.univ (fun i _ => h i)

theorem cir_sum_fin {n c d : ℕ} {f : Fin n → MvPolynomial σ F} (h : ∀ i, Cir c d (f i)) :
    Cir (n * (c + 1)) d (∑ i, f i) := by
  simpa using cir_sum Finset.univ (fun i _ => h i)

end Circuits

/-! ## The verifier -/

variable (F : Type*) [Field F]

/-- Edge variables on the left, witness bits `(position, vertex)` on the right. -/
abbrev V (n : ℕ) := (Fin n × Fin n) ⊕ (Fin n × Fin n)

/-- Witness bit: the `k`-th vertex of the tour is `v`. -/
abbrev yv {n : ℕ} (k v : Fin n) : MvPolynomial (V n) F := X (Sum.inr (k, v))

/-- The verifier for a tour rooted at `r`. -/
def body (n : ℕ) (r : Fin n) : MvPolynomial (V n) F :=
  yv F r r *
  (∏ k, (1 - ∏ v, (1 - yv F k v))) *
  (∏ v, (1 - ∏ k, (1 - yv F k v))) *
  (∏ k, ∏ v, ∏ w, (1 - (if v ≠ w then 1 else 0) * (yv F k v * yv F k w))) *
  ∏ k, ∑ u, ∑ v, yv F k u * yv F (finRotate n k) v * X (Sum.inl (u, v))

/-- The verifier family; the empty graph has no Hamiltonian cycle. -/
def verifier : (n : ℕ) → MvPolynomial (V n) F
  | 0 => 0
  | m + 1 => body F (m + 1) 0

theorem verifier_cir_of {S D : ℕ → ℕ} (h : ∀ n (r : Fin n), Cir (S n) (D n) (body F n r))
    (hS : PolynomiallyBounded S) (hD : PolynomiallyBounded D) :
    ∃ S D : ℕ → ℕ, PolynomiallyBounded S ∧ PolynomiallyBounded D ∧
      ∀ n, Cir (S n) (D n) (verifier F n) := by
  refine ⟨S, D, hS, hD, fun n => ?_⟩
  cases n with
  | zero => exact cir_mono cir_zero (Nat.zero_le _) (Nat.zero_le _)
  | succ m => exact h (m + 1) 0

theorem verifier_cir : ∃ S D : ℕ → ℕ, PolynomiallyBounded S ∧ PolynomiallyBounded D ∧
    ∀ n, Cir (S n) (D n) (verifier F n) := by
  have hite : ∀ n (v w : Fin n), Cir 0 0 (if v ≠ w then 1 else 0 : MvPolynomial (V n) F) := by
    intro n v w; split_ifs
    · exact cir_one
    · exact cir_zero
  refine verifier_cir_of F (fun n r =>
    cir_mul (cir_mul (cir_mul (cir_mul (cir_X _)
      (cir_prod_fin fun k => cir_one_sub (cir_prod_fin fun v => cir_one_sub (cir_X _))))
      (cir_prod_fin fun v => cir_one_sub (cir_prod_fin fun k => cir_one_sub (cir_X _))))
      (cir_prod_fin fun k => cir_prod_fin fun v => cir_prod_fin fun w =>
        cir_one_sub (cir_mul (hite n v w) (cir_mul (cir_X _) (cir_X _)))))
      (cir_prod_fin fun k => cir_sum_fin fun u => cir_sum_fin fun v =>
        cir_mul (cir_mul (cir_X _) (cir_X _)) (cir_X _))) ?_ ?_
  all_goals
    repeat (first | exact pb_id | exact pb_const _ | apply pb_add | apply pb_mul)

/-! ## Boolean evaluation -/

/-- Substituting a Boolean witness. -/
abbrev ev {n : ℕ} (y : Fin n × Fin n → Bool) :
    MvPolynomial (V n) F →+* MvPolynomial (Fin n × Fin n) F :=
  eval₂Hom C (Sum.elim X (fun i => C (if y i then 1 else 0)))

variable {F}

theorem C_bool {τ : Type*} (b : Bool) :
    (C (if b then (1 : F) else 0) : MvPolynomial τ F) = if b then 1 else 0 := by
  cases b <;> simp

theorem one_sub_ite {R : Type*} [CommRing R] (p : Prop) [Decidable p] :
    (1 : R) - (if p then 1 else 0) = if ¬p then 1 else 0 := by
  split_ifs <;> simp

theorem ite_mul_ite {R : Type*} [CommRing R] (p q : Prop) [Decidable p] [Decidable q] :
    (if p then (1 : R) else 0) * (if q then 1 else 0) = if p ∧ q then 1 else 0 := by
  rw [ite_zero_mul_ite_zero, mul_one]

/-- The graph of an ordering. -/
def graph {n : ℕ} (σ : Perm (Fin n)) : Fin n × Fin n → Bool := fun e => decide (σ e.1 = e.2)

theorem graph_injective {n : ℕ} : Function.Injective (graph (n := n)) := by
  intro σ τ h
  ext i
  have := congrFun h (i, σ i)
  simp [graph] at this
  rw [this]

/-- Orderings rooted at `r`. -/
def rooted {n : ℕ} (r : Fin n) : Finset (Perm (Fin n)) := Finset.univ.filter fun σ => σ r = r

theorem mem_image_iff {n : ℕ} (r : Fin n) (y : Fin n × Fin n → Bool) :
    y ∈ (rooted r).image graph ↔ y (r, r) = true ∧ (∀ k, ∃ v, y (k, v) = true) ∧
      (∀ v, ∃ k, y (k, v) = true) ∧
      (∀ k v w, y (k, v) = true → y (k, w) = true → v = w) := by
  constructor
  · intro hy
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hy
    simp only [rooted, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    refine ⟨by simp [graph, hσ], fun k => ⟨σ k, by simp [graph]⟩, fun v => ⟨σ.symm v, by simp [graph]⟩,
      fun k v w hv hw => ?_⟩
    simp only [graph, decide_eq_true_eq] at hv hw
    rw [← hv, hw]
  · rintro ⟨hr, hrow, hcol, huniq⟩
    choose f hf using hrow
    have hsurj : Function.Surjective f := by
      intro v
      obtain ⟨k, hk⟩ := hcol v
      exact ⟨k, huniq k _ _ (hf k) hk⟩
    let σ : Perm (Fin n) := Equiv.ofBijective f hsurj.bijective_of_finite
    have hgraph : graph σ = y := by
      funext ⟨k, v⟩
      change decide (f k = v) = y (k, v)
      by_cases h : y (k, v) = true
      · rw [h, huniq k _ _ (hf k) h]; simp
      · have : f k ≠ v := fun e => h (e ▸ hf k)
        simp [this, h]
    refine Finset.mem_image.mpr ⟨σ, ?_, hgraph⟩
    simp only [rooted, Finset.mem_filter, Finset.mem_univ, true_and]
    exact huniq r _ _ (hf r) hr

/-- The tour monomial selected by a witness. -/
def tour {n : ℕ} (y : Fin n × Fin n → Bool) : MvPolynomial (Fin n × Fin n) F :=
  ∏ k, ∑ u, ∑ v, (if y (k, u) then (1 : MvPolynomial (Fin n × Fin n) F) else 0) *
    (if y (finRotate n k, v) then 1 else 0) * X (u, v)

theorem tour_graph {n : ℕ} (σ : Perm (Fin n)) :
    tour (F := F) (graph σ) = ∏ k, X (σ k, σ (finRotate n k)) := by
  unfold tour graph
  refine Finset.prod_congr rfl fun k _ => ?_
  simp [ite_mul, Finset.sum_ite_eq]

theorem ev_body {n : ℕ} (r : Fin n) (y : Fin n × Fin n → Bool) :
    ev F y (body F n r) = if y ∈ (rooted r).image graph then tour y else 0 := by
  simp only [body, yv, map_mul, map_prod, map_sub, map_one, map_sum, eval₂Hom_X',
    Sum.elim_inr, Sum.elim_inl, C_bool, apply_ite (ev F y), map_zero, one_sub_ite,
    ite_mul_ite, Fintype.prod_boole]
  by_cases hy : y ∈ (rooted r).image graph
  · rw [if_pos hy]
    obtain ⟨hr, hrow, hcol, huniq⟩ := (mem_image_iff r y).mp hy
    have h1 : ∀ x, ¬∀ i, ¬ y (x, i) = true := fun x h => by
      obtain ⟨v, hv⟩ := hrow x; exact h v hv
    have h2 : ∀ x, ¬∀ i, ¬ y (i, x) = true := fun x h => by
      obtain ⟨k, hk⟩ := hcol x; exact h k hk
    have h3 : ∀ x x₁, ∀ i, ¬(x₁ ≠ i ∧ y (x, x₁) = true ∧ y (x, i) = true) :=
      fun x x₁ i h => h.1 (huniq _ _ _ h.2.1 h.2.2)
    simp only [hr, h1, h2, h3, if_true, not_false_eq_true, implies_true, Finset.prod_const_one,
      one_mul, tour, ite_mul_ite]
  · rw [if_neg hy, mem_image_iff] at *
    simp only [mul_eq_zero, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and,
      ite_eq_right_iff, one_ne_zero, imp_false, not_not]
    by_contra hne
    simp only [not_or, not_exists] at hne
    obtain ⟨⟨⟨⟨hr, h1⟩, h2⟩, h3⟩, -⟩ := hne
    refine hy ⟨not_not.mp hr, fun k => ?_, fun v => ?_, fun k v w hv hw => ?_⟩
    · by_contra h; exact h1 k fun i hi => h ⟨i, hi⟩
    · by_contra h; exact h2 v fun i hi => h ⟨i, hi⟩
    · by_contra h; exact h3 k v fun hall => hall w ⟨h, hv, hw⟩

/-! ## Tours and Hamiltonian cycles -/

theorem rot_val (m : ℕ) (i : Fin (m + 1)) :
    ((finRotate (m + 1)) i).val = (i.val + 1) % (m + 1) := by
  by_cases h : i = Fin.last m
  · subst h; simp
  · rw [coe_finRotate_of_ne_last h, Nat.mod_eq_of_lt]
    have := Fin.val_lt_last h
    omega

theorem rot_pow_val (m t : ℕ) (i : Fin (m + 1)) :
    ((finRotate (m + 1) ^ t) i).val = (i.val + t) % (m + 1) := by
  induction t with
  | zero => simp [Nat.mod_eq_of_lt i.isLt]
  | succ t ih => rw [pow_succ', Perm.mul_apply, rot_val, ih, Nat.mod_add_mod, Nat.add_assoc]

theorem rot_isCycleOn (m : ℕ) : (finRotate (m + 1)).IsCycleOn Set.univ := by
  refine ⟨(finRotate (m + 1)).bijective.bijOn_univ, fun i _ j _ =>
    ⟨((j.val + (m + 1 - i.val) : ℕ) : ℤ), ?_⟩⟩
  rw [zpow_natCast]
  ext
  rw [rot_pow_val, show i.val + (j.val + (m + 1 - i.val)) = j.val + (m + 1) by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]

theorem conj_root {m : ℕ} (σ : Perm (Fin (m + 1))) (h0 : σ 0 = 0) (k : Fin (m + 1)) :
    ((σ * finRotate (m + 1) * σ⁻¹) ^ k.val) 0 = σ k := by
  have hinv : σ⁻¹ 0 = 0 := by rw [Perm.inv_eq_iff_eq, h0]
  rw [conj_pow, Perm.mul_apply, Perm.mul_apply, hinv]
  congr 1
  ext
  rw [rot_pow_val, Fin.val_zero, zero_add, Nat.mod_eq_of_lt k.isLt]

theorem rooted_sum (m : ℕ) :
    ∑ σ ∈ rooted (0 : Fin (m + 1)), ∏ k, (X (σ k, σ (finRotate (m + 1) k)) :
        MvPolynomial (Fin (m + 1) × Fin (m + 1)) F) =
      ∑ π ∈ Finset.univ.filter (fun π : Perm (Fin (m + 1)) => 0 < m + 1 ∧ π.IsCycleOn Set.univ),
        ∏ i, (X (i, π i) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) F) := by
  refine Finset.sum_bij (fun σ _ => σ * finRotate (m + 1) * σ⁻¹) ?_ ?_ ?_ ?_
  · intro σ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨Nat.succ_pos m, ?_⟩
    have := (rot_isCycleOn m).conj (g := σ)
    rwa [Set.image_univ_of_surjective σ.surjective] at this
  · intro σ hσ τ hτ h
    simp only [rooted, Finset.mem_filter, Finset.mem_univ, true_and] at hσ hτ
    ext k
    rw [← conj_root σ hσ k, ← conj_root τ hτ k, h]
  · intro π hπ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ
    have hc : π.IsCycleOn ((Finset.univ : Finset (Fin (m + 1))) : Set (Fin (m + 1))) := by
      simpa using hπ.2
    let f : Fin (m + 1) → Fin (m + 1) := fun k => (π ^ k.val) 0
    have hsurj : Function.Surjective f := by
      intro j
      obtain ⟨t, ht, hj⟩ := hc.exists_pow_eq (Finset.mem_univ 0) (Finset.mem_univ j)
      exact ⟨⟨t, by simpa using ht⟩, hj⟩
    let σ : Perm (Fin (m + 1)) :=
      Equiv.ofBijective f hsurj.bijective_of_finite
    have hstep : ∀ k, σ (finRotate (m + 1) k) = π (σ k) := by
      intro k
      show (π ^ (finRotate (m + 1) k).val) 0 = π ((π ^ k.val) 0)
      rw [← Perm.mul_apply, ← pow_succ']
      by_cases hk : k = Fin.last m
      · subst hk
        rw [finRotate_last, Fin.val_zero, pow_zero, Fin.val_last]
        have := hc.pow_card_apply (Finset.mem_univ (0 : Fin (m + 1)))
        simpa using this.symm
      · rw [coe_finRotate_of_ne_last hk]
    refine ⟨σ, ?_, ?_⟩
    · simp only [rooted, Finset.mem_filter, Finset.mem_univ, true_and]
      show (π ^ (0 : Fin (m + 1)).val) 0 = 0
      simp
    · refine Equiv.ext fun i => ?_
      obtain ⟨k, rfl⟩ := σ.surjective i
      simp only [Perm.mul_apply, Perm.inv_def, Equiv.symm_apply_apply, hstep]
  · intro σ _
    refine Fintype.prod_equiv σ _ _ fun k => ?_
    simp only [Perm.mul_apply, Perm.inv_def, Equiv.symm_apply_apply]

/-! ## Membership -/

variable (F)

theorem identity (n : ℕ) :
    (∑ π ∈ Finset.univ.filter (fun π : Perm (Fin n) => 0 < n ∧ π.IsCycleOn Set.univ),
        ∏ i, (X (i, π i) : MvPolynomial (Fin n × Fin n) F)) =
      ∑ y : Fin n × Fin n → Bool, ev F y (verifier F n) := by
  cases n with
  | zero => simp [verifier]
  | succ m =>
    simp only [verifier, ev_body]
    rw [Fintype.sum_ite_mem, Finset.sum_image graph_injective.injOn]
    simp only [tour_graph]
    exact (rooted_sum m).symm

theorem target_degree (n : ℕ) :
    (∑ π ∈ Finset.univ.filter (fun π : Perm (Fin n) => 0 < n ∧ π.IsCycleOn Set.univ),
        ∏ i, (X (i, π i) : MvPolynomial (Fin n × Fin n) F)).totalDegree ≤ n := by
  refine totalDegree_finsetSum_le fun π _ => (totalDegree_finsetProd _ _).trans ?_
  calc ∑ i, (X (i, π i) : MvPolynomial (Fin n × Fin n) F).totalDegree ≤ ∑ _i : Fin n, 1 :=
        Finset.sum_le_sum fun i _ => (totalDegree_X _).le
    _ = n := by simp

theorem H1_proof : OMA.R_wpc_vp_vs_vnp_R1.H1 := by
  intro F _
  obtain ⟨S, D, hS, hD, hcir⟩ := verifier_cir F
  refine ⟨⟨?_, ?_⟩, fun n => Fin n × Fin n, fun _ => inferInstance, verifier F, ?_,
    ⟨⟨?_, ?_⟩, S, hS, fun n => (hcir n).1.computes⟩, fun n => ?_⟩
  · simpa using pb_mul pb_id pb_id
  · exact pb_of_le (target_degree F) pb_id
  · simpa using pb_mul pb_id pb_id
  · simpa using pb_add (pb_mul pb_id pb_id) (pb_mul pb_id pb_id)
  · exact pb_of_le (fun n => (hcir n).2) hD
  · convert identity F n

end

end OMA.P_wpc_vp_vs_vnp_R1_H1

theorem OMA.solution : OMA.R_wpc_vp_vs_vnp_R1.H1 := OMA.P_wpc_vp_vs_vnp_R1_H1.H1_proof
