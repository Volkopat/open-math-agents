import OMAReductions.R_oeis_a046747_R1

/-!
Elementary lower-bound ingredients for OEIS A046747. Hu, Song and Wu,
arXiv:2609.39463v2, Corollary 1.2, give the full singularity asymptotic.
Their proof of the corollary estimates overlaps by constraint rank. Here the
Boolean case uses coordinate-deletion bijections and the first Bonferroni bound.
-/
namespace BoolMatrixPairs

variable {ι κ X : Type*}

/-- Remove coordinate j from a function with f i = f j. The inverse copies i to j. -/
def deleteEqual [DecidableEq ι] {i j : ι} (h : i ≠ j) :
    {f : ι → X // f i = f j} ≃ ({t : ι // t ≠ j} → X) where
  toFun f t := f.1 t
  invFun g := ⟨fun t => if ht : t = j then g ⟨i,h⟩ else g ⟨t,ht⟩, by simp [h]⟩
  left_inv f := by
    apply Subtype.ext
    funext t
    by_cases ht : t = j
    · subst t
      simpa using f.property
    · simp [ht]
  right_inv g := by
    funext t
    simp [t.property]

theorem card_deleteEqual [Fintype ι] [DecidableEq ι] [Fintype X] [DecidableEq X]
    {i j : ι} (h : i ≠ j) :
    Fintype.card {f : ι → X // f i = f j} = Fintype.card X ^ (Fintype.card ι - 1) := by
  rw [Fintype.card_congr (deleteEqual h)]
  simp

abbrev BM (n : ℕ) := Matrix (Fin n) (Fin n) Bool

def rows {n : ℕ} (i j : Fin n) : Finset (BM n) :=
  Finset.univ.filter fun M => M i = M j

def cols {n : ℕ} (i j : Fin n) : Finset (BM n) :=
  Finset.univ.filter fun M => ∀ t, M t i = M t j

theorem card_rows {n : ℕ} {i j : Fin n} (h : i ≠ j) :
    (rows i j).card = 2 ^ (n * (n - 1)) := by
  classical
  rw [rows, ← Fintype.card_subtype]
  change Fintype.card {M : Fin n → (Fin n → Bool) // M i = M j} = _
  rw [card_deleteEqual h]
  simp [← pow_mul]

def transposeEqual {n : ℕ} (i j : Fin n) :
    {M : BM n // ∀ t, M t i = M t j} ≃ {M : BM n // M i = M j} where
  toFun M := ⟨M.val.transpose, funext M.property⟩
  invFun M := ⟨M.val.transpose, fun t => congrFun M.property t⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_cols {n : ℕ} {i j : Fin n} (h : i ≠ j) :
    (cols i j).card = 2 ^ (n * (n - 1)) := by
  classical
  rw [← card_rows h, cols, rows, ← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr (transposeEqual i j)

theorem det_zero_of_mem_rows {n : ℕ} {M : BM n} {i j : Fin n} (h : i ≠ j)
    (hM : M ∈ rows i j) :
    (M.map fun b => if b then (1 : ℝ) else 0).det = 0 := by
  apply Matrix.det_zero_of_row_eq h
  have eq := (Finset.mem_filter.mp hM).2
  funext t
  simp only [Matrix.map_apply, congrFun eq t]

theorem det_zero_of_mem_cols {n : ℕ} {M : BM n} {i j : Fin n} (h : i ≠ j)
    (hM : M ∈ cols i j) :
    (M.map fun b => if b then (1 : ℝ) else 0).det = 0 := by
  apply Matrix.det_zero_of_column_eq h
  intro t
  have eq := (Finset.mem_filter.mp hM).2 t
  simp only [Matrix.map_apply, eq]

end BoolMatrixPairs

namespace BoolMatrixPairs

variable {ι κ X : Type*}

/-- Regard a column equality as a constraint on the value type of each row. -/
def mixedEquiv {i j : ι} {k l : κ} :
    {M : ι → κ → X // M i = M j ∧ ∀ t, M t k = M t l} ≃
    {F : ι → {g : κ → X // g k = g l} // F i = F j} where
  toFun M := ⟨fun t => ⟨M.val t, M.property.2 t⟩, Subtype.ext M.property.1⟩
  invFun F := ⟨fun t => (F.val t).val, congrArg Subtype.val F.property, fun t => (F.val t).property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_mixed {n : ℕ} {i j k l : Fin n} (h : i ≠ j) (g : k ≠ l) :
    (rows i j ∩ cols k l).card = 2 ^ ((n - 1) * (n - 1)) := by
  classical
  have sets : rows i j ∩ cols k l =
      Finset.univ.filter (fun M : BM n => M i = M j ∧ ∀ t, M t k = M t l) := by
    ext M
    simp [rows, cols]
  rw [sets, ← Fintype.card_subtype]
  change Fintype.card {M : Fin n → Fin n → Bool // M i = M j ∧ ∀ t, M t k = M t l} = _
  rw [Fintype.card_congr mixedEquiv, card_deleteEqual h, card_deleteEqual g]
  simp [← pow_mul]

/-- If the deleted index j is outside the second pair, the second equality survives deletion. -/
def twoPairsEquiv [DecidableEq ι] {i j k l : ι} (h : i ≠ j) (hk : k ≠ j) (hl : l ≠ j) :
    {f : ι → X // f i = f j ∧ f k = f l} ≃
    {g : {t : ι // t ≠ j} → X // g ⟨k,hk⟩ = g ⟨l,hl⟩} :=
  (Equiv.subtypeSubtypeEquivSubtypeInter (fun f : ι → X => f i = f j)
    (fun f => f k = f l)).symm.trans ((deleteEqual h).subtypeEquiv fun _ => Iff.rfl)

theorem card_twoPairs_avoiding [Fintype ι] [DecidableEq ι] [Fintype X] [DecidableEq X]
    {i j k l : ι} (h : i ≠ j) (g : k ≠ l) (hk : k ≠ j) (hl : l ≠ j) :
    Fintype.card {f : ι → X // f i = f j ∧ f k = f l} =
      Fintype.card X ^ (Fintype.card ι - 2) := by
  rw [Fintype.card_congr (twoPairsEquiv h hk hl)]
  rw [card_deleteEqual (show (⟨k,hk⟩ : {t : ι // t ≠ j}) ≠ ⟨l,hl⟩ from
    fun e => g (congrArg Subtype.val e))]
  simp [Nat.sub_sub]

/-- Distinct unordered pairs can share either endpoint. The two final hypotheses
exclude the two possible orientations of the same pair. -/
theorem card_twoPairs [Fintype ι] [DecidableEq ι] [Fintype X] [DecidableEq X]
    {i j k l : ι} (h : i ≠ j) (g : k ≠ l)
    (hd : ¬(i = k ∧ j = l)) (hr : ¬(i = l ∧ j = k)) :
    Fintype.card {f : ι → X // f i = f j ∧ f k = f l} =
      Fintype.card X ^ (Fintype.card ι - 2) := by
  by_cases hj : k ≠ j ∧ l ≠ j
  · exact card_twoPairs_avoiding h g hj.1 hj.2
  · have hk : k ≠ i := by grind
    have hl : l ≠ i := by grind
    have e := Equiv.subtypeEquivRight (fun f : ι → X =>
      show (f i = f j ∧ f k = f l) ↔ (f j = f i ∧ f k = f l) from and_congr eq_comm Iff.rfl)
    exact (Fintype.card_congr e).trans (card_twoPairs_avoiding h.symm g hk hl)

theorem card_rows_inter {n : ℕ} {i j k l : Fin n} (h : i ≠ j) (g : k ≠ l)
    (hd : ¬(i = k ∧ j = l)) (hr : ¬(i = l ∧ j = k)) :
    (rows i j ∩ rows k l).card = 2 ^ (n * (n - 2)) := by
  classical
  have sets : rows i j ∩ rows k l =
      Finset.univ.filter (fun M : BM n => M i = M j ∧ M k = M l) := by
    ext M
    simp [rows]
  rw [sets, ← Fintype.card_subtype]
  change Fintype.card {M : Fin n → (Fin n → Bool) // M i = M j ∧ M k = M l} = _
  rw [card_twoPairs h g hd hr]
  simp [← pow_mul]

theorem card_cols_inter {n : ℕ} {i j k l : Fin n} (h : i ≠ j) (g : k ≠ l)
    (hd : ¬(i = k ∧ j = l)) (hr : ¬(i = l ∧ j = k)) :
    (cols i j ∩ cols k l).card = 2 ^ (n * (n - 2)) := by
  classical
  rw [← card_rows_inter h g hd hr]
  apply Finset.card_bij' (fun (M : BM n) _ => M.transpose) (fun (M : BM n) _ => M.transpose)
  · intro M hM
    obtain ⟨a,b⟩ := Finset.mem_inter.mp hM
    exact Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, funext (Finset.mem_filter.mp a).2⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, funext (Finset.mem_filter.mp b).2⟩⟩
  · intro M hM
    obtain ⟨a,b⟩ := Finset.mem_inter.mp hM
    exact Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, congrFun (Finset.mem_filter.mp a).2⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, congrFun (Finset.mem_filter.mp b).2⟩⟩
  · intros; rfl
  · intros; rfl

end BoolMatrixPairs

namespace BoolMatrixPairs

/-- The first two Bonferroni terms, with uniform single-event and overlap bounds. -/
theorem bonferroni {I Y : Type*} [DecidableEq I] [DecidableEq Y]
    (e : I → Finset Y) (s : Finset I) (A B : ℕ)
    (single : ∀ i ∈ s, (e i).card = A)
    (overlap : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (e i ∩ e j).card ≤ B) :
    s.card * A ≤ (s.biUnion e).card + s.card.choose 2 * B := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hi' := single i (Finset.mem_insert_self _ _)
    have prev := ih (fun j hj => single j (Finset.mem_insert_of_mem hj))
      (fun j hj k hk => overlap j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk))
    have inter : (e i ∩ s.biUnion e).card ≤ s.card * B := by
      rw [Finset.inter_biUnion]
      calc
        _ ≤ ∑ j ∈ s, (e i ∩ e j).card := Finset.card_biUnion_le
        _ ≤ ∑ _j ∈ s, B := Finset.sum_le_sum fun j hj =>
          overlap i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
            (fun eq => hi (eq ▸ hj))
        _ = _ := by simp
    have count := Finset.card_union_add_card_inter (e i) (s.biUnion e)
    rw [Finset.card_insert_of_notMem hi, Finset.biUnion_insert]
    simp only [Nat.choose_succ_succ, Nat.choose_one_right, Nat.add_mul, one_mul]
    have same_term : s.card.choose (Nat.succ 1) * B = s.card.choose 2 * B := rfl
    omega

abbrev IncreasingPair (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}
abbrev Collision (n : ℕ) := Bool × IncreasingPair n

theorem card_collisions (n : ℕ) : Fintype.card (Collision n) = 2 * n.choose 2 := by
  change Fintype.card (Bool × {p : Fin n × Fin n // p.1 < p.2}) = _
  rw [Fintype.card_prod, Fintype.card_subtype, Fintype.card_product_filter_lt]
  simp

def event {n : ℕ} (x : Collision n) : Finset (BM n) :=
  if x.1 then rows x.2.val.1 x.2.val.2 else cols x.2.val.1 x.2.val.2

theorem card_event {n : ℕ} (x : Collision n) : (event x).card = 2 ^ (n * (n - 1)) := by
  rcases x with ⟨b, ⟨⟨i,j⟩,h⟩⟩
  cases b
  · exact card_cols h.ne
  · exact card_rows h.ne

private theorem pow_same_le {n : ℕ} (hn : 2 ≤ n) :
    (2 : ℕ) ^ (n * (n - 2)) ≤ 2 ^ ((n - 1) * (n - 1)) := by
  apply Nat.pow_le_pow_right (by decide)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h1 : 2 + m - 1 = m + 1 := by omega
  have h2 : 2 + m - 2 = m := by omega
  rw [h1, h2]
  nlinarith

theorem overlap_event {n : ℕ} (hn : 2 ≤ n) {x y : Collision n} (hne : x ≠ y) :
    (event x ∩ event y).card ≤ 2 ^ ((n - 1) * (n - 1)) := by
  rcases x with ⟨b,⟨⟨i,j⟩,h⟩⟩
  rcases y with ⟨c,⟨⟨k,l⟩,g⟩⟩
  have reversed : ¬(i = l ∧ j = k) := by
    rintro ⟨rfl,rfl⟩
    exact (lt_asymm h g)
  cases b <;> cases c <;> dsimp [event] 
  · have hd : ¬(i = k ∧ j = l) := by rintro ⟨rfl,rfl⟩; exact hne rfl
    rw [card_cols_inter h.ne g.ne hd reversed]
    exact pow_same_le hn
  · rw [Finset.inter_comm, card_mixed g.ne h.ne]
  · rw [card_mixed h.ne g.ne]
  · have hd : ¬(i = k ∧ j = l) := by rintro ⟨rfl,rfl⟩; exact hne rfl
    rw [card_rows_inter h.ne g.ne hd reversed]
    exact pow_same_le hn

theorem event_singular {n : ℕ} {M : BM n} {x : Collision n} (hx : M ∈ event x) :
    (M.map fun b => if b then (1 : ℝ) else 0).det = 0 := by
  rcases x with ⟨b, ⟨⟨i,j⟩,h⟩⟩
  cases b
  · exact det_zero_of_mem_cols h.ne hx
  · exact det_zero_of_mem_rows h.ne hx

/-- A finite lower bound on the exact registered singular-matrix count. -/
theorem finite_lower {n : ℕ} (hn : 2 ≤ n) :
    (2 * n.choose 2) * 2 ^ (n * (n - 1)) ≤ OMA.S_oeis_a046747.a n +
      (2 * n.choose 2).choose 2 * 2 ^ ((n - 1) * (n - 1)) := by
  classical
  let s := (Finset.univ : Finset (Collision n))
  have inc : (s.biUnion event).card ≤ OMA.S_oeis_a046747.a n := by
    apply Finset.card_le_card
    intro M hM
    obtain ⟨x, _, hx⟩ := Finset.mem_biUnion.mp hM
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, event_singular hx⟩
  have count := bonferroni event s _ _ (fun x _ => card_event x) (fun _ _ _ _ => overlap_event hn)
  have hs : s.card = 2 * n.choose 2 := card_collisions n
  rw [hs] at count
  exact count.trans (Nat.add_le_add_right inc _)

end BoolMatrixPairs

namespace BoolMatrixPairs
open Filter
open scoped Topology

/-- Normalized finite lower estimate. Both explicit error terms tend to zero. -/
theorem normalized_lower {n : ℕ} (hn : 2 ≤ n) :
    1 - 2 * (1 / ((n : ℝ) + 1)) - 2 * ((n : ℝ)^4 / 2^n) ≤
      ((OMA.S_oeis_a046747.a n : ℝ) / 2^(n^2)) /
        (((n+1).choose 2 : ℝ) * (1/2)^(n-1)) := by
  let x : ℝ := n
  let S : ℝ := 2 ^ (n * (n - 1))
  let T : ℝ := 2 ^ ((n - 1) * (n - 1))
  let p : ℝ := 2 ^ (n - 1)
  let A : ℝ := OMA.S_oeis_a046747.a n
  have hx : 2 ≤ x := by dsimp [x]; exact_mod_cast hn
  have hS : 0 < S := by dsimp [S]; positivity
  have hT : 0 < T := by dsimp [T]; positivity
  have hp : 0 < p := by dsimp [p]; positivity
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x+1 := by linarith
  have hD : 1 ≤ x*(x+1) := by nlinarith
  have hden : 0 < (x*(x+1))*S := by positivity
  have nn : n = (n-1)+1 := by omega
  have total : (2:ℝ)^(n^2) = S * 2^n := by
    dsimp [S]; rw [← pow_add]; congr 1
    calc n ^ 2 = n * ((n-1)+1) := by rw [← nn, pow_two]
         _ = _ := by ring
  have power : (2:ℝ)^n = p*2 := by
    change (2:ℝ)^n = 2^(n-1)*2
    conv_lhs => rw [nn, pow_succ]
  have ST : S = T*p := by
    dsimp [S,T,p]; rw [← pow_add]; congr 1
    calc n*(n-1) = ((n-1)+1)*(n-1) := congrArg (fun u => u*(n-1)) nn
         _ = _ := by ring
  have singles : ((2 * n.choose 2 : ℕ) : ℝ) = x*(x-1) := by
    simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_choose_two]; dsimp [x]; ring
  have target : ((n+1).choose 2 : ℝ) = x*(x+1)/2 := by
    rw [Nat.cast_choose_two]; push_cast; dsimp [x]; ring
  have overlaps : (((2 * n.choose 2).choose 2 : ℕ) : ℝ) ≤ x^4 := by
    rw [Nat.cast_choose_two, singles]
    have hu : 0 ≤ x*(x-1) := mul_nonneg hx0.le (by linarith)
    have hv : x*(x-1) ≤ x^2 := by nlinarith
    have hw := mul_self_le_mul_self hu hv
    nlinarith [sq_nonneg (x^2)]
  have counted :
      ((2 * n.choose 2 : ℕ) : ℝ) * S ≤ A +
      (((2 * n.choose 2).choose 2 : ℕ) : ℝ) * T := by
    dsimp [S,A,T]
    exact_mod_cast finite_lower hn
  rw [singles] at counted
  have divided : (x*(x-1)*S)/((x*(x+1))*S) ≤
      A/((x*(x+1))*S) + x^4*T/((x*(x+1))*S) := by
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ hden.le
    exact counted.trans (add_le_add_right (mul_le_mul_of_nonneg_right overlaps hT.le) A)
  have lead : (x*(x-1)*S)/((x*(x+1))*S) = 1 - 2*(1/(x+1)) := by
    field_simp [ne_of_gt hx0, ne_of_gt hx1, ne_of_gt hS]
    ring
  have err : x^4*T/((x*(x+1))*S) ≤ 2*(x^4/(2:ℝ)^n) := by
    rw [ST, power]
    calc
      _ = (x^4/p)/(x*(x+1)) := by
        field_simp [ne_of_gt hx0, ne_of_gt hx1, ne_of_gt hT, ne_of_gt hp]
      _ ≤ x^4/p := div_le_self (by positivity) hD
      _ = _ := by field_simp
  have habs : ((OMA.S_oeis_a046747.a n : ℝ) / 2^(n^2)) /
      (((n+1).choose 2 : ℝ) * (1/2)^(n-1)) = A/((x*(x+1))*S) := by
    rw [total, power, target, div_pow, one_pow]
    change A / (S * (p * 2)) / (x * (x+1) / 2 * (1 / p)) = _
    field_simp [ne_of_gt hx0, ne_of_gt hx1, ne_of_gt hS, ne_of_gt hp]
  rw [habs]
  rw [lead] at divided
  change 1 - 2*(1/(x+1)) - 2*(x^4/(2:ℝ)^n) ≤ _
  linarith

/-- The lower hypothesis in the coordinator's reduction. -/
theorem lower_asymptotic :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, 1 - ε ≤
      ((OMA.S_oeis_a046747.a n : ℝ) / 2^(n^2)) /
        (((n+1).choose 2 : ℝ) * (1/2)^(n-1)) := by
  intro ε hε
  have reciprocal : Tendsto (fun n : ℕ => 1/((n : ℝ)+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have exp := tendsto_pow_const_div_const_pow_of_one_lt 4 (r := (2:ℝ)) (by norm_num)
  have tend : Tendsto (fun n : ℕ => 1 - 2*(1/((n:ℝ)+1)) - 2*((n:ℝ)^4 / 2^n))
      atTop (𝓝 1) := by
    simpa using ((tendsto_const_nhds (x := (1:ℝ))).sub (reciprocal.const_mul 2)).sub (exp.const_mul 2)
  filter_upwards [tend.eventually_const_lt (show 1-ε < 1 by linarith),
    eventually_ge_atTop (2:ℕ)] with n h hn
  exact h.le.trans (normalized_lower hn)

end BoolMatrixPairs

theorem OMA.solution : OMA.R_oeis_a046747_R1.H1 :=
  BoolMatrixPairs.lower_asymptotic
