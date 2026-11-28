import OMAStatements.S_oeis_a079267

-- Credit: @LDJAI
-- Count marked short pairs by compressing their ordered starts. Extend prescribed
-- disjoint pairs using a matching of the complement. The resulting binomial
-- moments have an explicit product ratio. Binomial inversion and Tannery's
-- theorem give the pointwise Poisson(1) limit.
open Filter Topology Real
open Filter Topology Real Finset
open scoped BigOperators Nat

namespace Adjacent
noncomputable section

def ratio (n k : ℕ) : ℝ :=
  if k ≤ n then ∏ i ∈ range k, (2 * (n : ℝ) - 2 * i) / (2 * (n : ℝ) - i) else 0

lemma ratio_nonneg (n k : ℕ) : 0 ≤ ratio n k := by
  unfold ratio
  split_ifs with h
  · apply Finset.prod_nonneg
    intro i hi
    have hi' : i < k := Finset.mem_range.mp hi
    have hi'' : (i : ℝ) ≤ n := by exact_mod_cast (show i ≤ n by omega)
    exact div_nonneg (by linarith) (by linarith)
  · exact le_rfl

lemma ratio_le_one (n k : ℕ) : ratio n k ≤ 1 := by
  unfold ratio
  split_ifs with h
  · apply Finset.prod_le_one
    · intro i hi
      have hi' : i < k := Finset.mem_range.mp hi
      have hi'' : (i : ℝ) ≤ n := by exact_mod_cast (show i ≤ n by omega)
      exact div_nonneg (by linarith) (by linarith)
    · intro i hi
      have hi' : i < k := Finset.mem_range.mp hi
      have hi'' : (i : ℝ) < n := by exact_mod_cast (show i < n by omega)
      rw [div_le_one (by linarith : 0 < 2 * (n : ℝ) - i)]
      linarith [show (0:ℝ) ≤ i by positivity]
  · norm_num

lemma ratio_tendsto (k : ℕ) : Tendsto (fun n => ratio n k) atTop (𝓝 1) := by
  have h (i : ℕ) : Tendsto (fun n : ℕ => (2 * (n : ℝ) - 2 * i) / (2 * (n : ℝ) - i)) atTop (𝓝 1) := by
    have h := tendsto_add_mul_div_add_mul_atTop_nhds (-(2 * (i : ℝ))) (-(i : ℝ)) (2 : ℝ) (d := 2) (by norm_num)
    convert h using 1
    · ext n; ring
    · norm_num
  have hp := tendsto_finsetProd (range k) (fun i _ => h i)
  simp only [Finset.prod_const_one] at hp
  apply hp.congr'
  filter_upwards [eventually_ge_atTop k] with n hn
  simp [ratio, hn]

lemma series_limit (s : ℕ) :
    Tendsto (fun n : ℕ => ∑' j : ℕ, ((-1 : ℝ)^j / j.factorial / s.factorial) * ratio n (s+j))
      atTop (𝓝 (Real.exp (-1) / s.factorial)) := by
  have hs : HasSum (fun j : ℕ => (-1 : ℝ)^j / j.factorial / s.factorial)
      (Real.exp (-1) / s.factorial) := by
    rw [Real.exp_eq_exp_ℝ]
    exact (NormedSpace.expSeries_div_hasSum_exp (-1 : ℝ)).div_const _
  rw [← hs.tsum_eq]
  apply tendsto_tsum_of_dominated_convergence (bound := fun j : ℕ => (1 : ℝ) / j.factorial / s.factorial)
  · exact ((NormedSpace.expSeries_div_hasSum_exp (1 : ℝ)).summable.div_const (s.factorial : ℝ)).congr (fun j => by simp)
  · intro j
    simpa using (ratio_tendsto (s+j)).const_mul (((-1 : ℝ)^j / j.factorial / s.factorial))
  · filter_upwards [] with n j
    rw [norm_mul, Real.norm_eq_abs, abs_div, abs_div, abs_pow]
    simp only [abs_neg, abs_one, one_pow, Nat.cast_nonneg, abs_of_nonneg]
    rw [show ‖ratio n (s+j)‖ = ratio n (s+j) by exact Real.norm_of_nonneg (ratio_nonneg _ _)]
    exact mul_le_of_le_one_right (by positivity) (ratio_le_one _ _)


def df (n : ℕ) : ℕ := Nat.doubleFactorial (2*n-1)

lemma df_pos (n : ℕ) : 0 < (df n : ℝ) := by
  exact_mod_cast Nat.doubleFactorial_pos (2*n-1)

lemma df_formula (n : ℕ) :
    (df n : ℝ) = ((2*n).factorial : ℝ) / ((2:ℝ)^n * n.factorial) := by
  apply (eq_div_iff (by positivity)).2
  cases n with
  | zero => norm_num [df, Nat.doubleFactorial]
  | succ n =>
    have h := Nat.factorial_eq_mul_doubleFactorial (2*n+1)
    rw [show 2*n+1+1 = 2*(n+1) by omega, show 2*n+1 = 2*(n+1)-1 by omega,
      Nat.doubleFactorial_two_mul] at h
    exact_mod_cast (by simpa [df, mul_comm, mul_assoc, mul_left_comm] using h.symm :
      df (n+1) * (2^(n+1) * (n+1).factorial) = (2*(n+1)).factorial)

lemma desc_formula (a k : ℕ) (h : k ≤ a) :
    (a.descFactorial k : ℝ) = (a.factorial : ℝ) / (a-k).factorial := by
  apply (eq_div_iff (by positivity)).2
  exact_mod_cast (by rw [mul_comm, Nat.factorial_mul_descFactorial h] :
    a.descFactorial k * (a-k).factorial = a.factorial)

lemma choose_formula (a k : ℕ) (h : k ≤ a) :
    (a.choose k : ℝ) = (a.factorial : ℝ) / ((k.factorial : ℝ) * (a-k).factorial) := by
  apply (eq_div_iff (by positivity)).2
  exact_mod_cast (by rw [← mul_assoc, Nat.choose_mul_factorial_mul_factorial h] :
    a.choose k * (k.factorial * (a-k).factorial) = a.factorial)

lemma ratio_formula (n k : ℕ) (h : k ≤ n) :
    ratio n k = (2:ℝ)^k * (n.descFactorial k : ℝ) / ((2*n).descFactorial k : ℝ) := by
  rw [ratio, if_pos h, Finset.prod_div_distrib]
  have hn : (∏ i ∈ range k, (2*(n:ℝ)-2*i)) = (2:ℝ)^k * (n.descFactorial k : ℝ) := by
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod, Finset.pow_eq_prod_const (2:ℝ) k]
    -- rewrite each term using the natural subtraction
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    have hi' : i ≤ n := by have := Finset.mem_range.mp hi; omega
    rw [Nat.cast_sub hi']
    ring
  have hd : (∏ i ∈ range k, (2*(n:ℝ)-i)) = ((2*n).descFactorial k : ℝ) := by
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i hi
    have hi' : i ≤ 2*n := by have := Finset.mem_range.mp hi; omega
    rw [Nat.cast_sub hi', Nat.cast_mul]
    norm_num
  rw [hn, hd]

lemma moment_ratio (n k : ℕ) :
    ((2*n-k).choose k : ℝ) * df (n-k) / df n = ratio n k / k.factorial := by
  by_cases h : k ≤ n
  · rw [ratio_formula n k h, desc_formula _ _ h, desc_formula _ _ (by omega : k ≤ 2*n),
        choose_formula _ _ (by omega : k ≤ 2*n-k), df_formula (n-k), df_formula n]
    rw [show 2*n-k-k = 2*(n-k) by omega, show (2:ℝ)^n = 2^(n-k)*2^k by
      rw [← pow_add, Nat.sub_add_cancel h]]
    field_simp
  · have h' : 2*n-k < k := by omega
    simp [ratio, h, Nat.choose_eq_zero_of_lt h']

end
end Adjacent
open Function Finset
open scoped BigOperators Nat Classical

namespace Adjacent
noncomputable section

abbrev Matching (α : Type) := {f : α → α // (∀ x, f x ≠ x) ∧ Involutive f}

def matchCongr {α β : Type} (e : α ≃ β) : Matching α ≃ Matching β where
  toFun m := ⟨fun x => e (m.1 (e.symm x)), by
    constructor
    · intro x h
      exact m.2.1 (e.symm x) (e.injective (h.trans (e.apply_symm_apply x).symm))
    · intro x
      simp [m.2.2 (e.symm x)]⟩
  invFun m := ⟨fun x => e.symm (m.1 (e x)), by
    constructor
    · intro x h
      exact m.2.1 (e x) (e.symm.injective (h.trans (e.symm_apply_apply x).symm))
    · intro x
      simp [m.2.2 (e x)]⟩
  left_inv m := by apply Subtype.ext; funext x; simp
  right_inv m := by apply Subtype.ext; funext x; simp

def matchSum {α β : Type} (p : Matching α) (q : Matching β) : Matching (α ⊕ β) :=
  ⟨Sum.map p.1 q.1, by
    constructor
    · intro x; cases x with
      | inl x => simpa using p.2.1 x
      | inr x => simpa using q.2.1 x
    · intro x; cases x with
      | inl x => simp [p.2.2 x]
      | inr x => simp [q.2.2 x]⟩

lemma right_closed {α β : Type} (p : Matching α)
    (m : {m : Matching (α ⊕ β) // ∀ x, m.1 (Sum.inl x) = Sum.inl (p.1 x)}) (x : β) :
    ∃ y : β, m.1.1 (Sum.inr x) = Sum.inr y := by
  cases h : m.1.1 (Sum.inr x) with
  | inl a =>
    have hh := m.1.2.2 (Sum.inr x)
    rw [h, m.2 a] at hh
    cases hh
  | inr b => exact ⟨b, rfl⟩

def restrictRight {α β : Type} (p : Matching α)
    (m : {m : Matching (α ⊕ β) // ∀ x, m.1 (Sum.inl x) = Sum.inl (p.1 x)}) :
    Matching β :=
  ⟨fun x => Classical.choose (right_closed p m x), by
    constructor
    · intro x h
      have hh := Classical.choose_spec (right_closed p m x)
      change Classical.choose (right_closed p m x) = x at h
      rw [h] at hh
      exact m.1.2.1 (Sum.inr x) hh
    · intro x
      have hx := Classical.choose_spec (right_closed p m x)
      have hy := Classical.choose_spec (right_closed p m (Classical.choose (right_closed p m x)))
      exact Sum.inr.inj (hy.symm.trans (hx ▸ m.1.2.2 (Sum.inr x)))⟩

def fixedSumEquiv {α β : Type} (p : Matching α) :
    {m : Matching (α ⊕ β) // ∀ x, m.1 (Sum.inl x) = Sum.inl (p.1 x)} ≃ Matching β where
  toFun := restrictRight p
  invFun q := ⟨matchSum p q, fun _ => rfl⟩
  left_inv m := by
    apply Subtype.ext; apply Subtype.ext; funext x
    cases x with
    | inl x => exact (m.2 x).symm
    | inr x => exact (Classical.choose_spec (right_closed p m x)).symm
  right_inv q := by
    apply Subtype.ext; funext x
    exact (Sum.inr.inj (Classical.choose_spec (right_closed p ⟨matchSum p q, fun _ => rfl⟩ x))).symm

def prefixEquiv {α β : Type} (e : β ↪ α) :
    β ⊕ {x : α // x ∉ Set.range e} ≃ α := by
  classical
  exact ((Equiv.ofInjective e e.injective).sumCongr (Equiv.refl _)).trans
    (Equiv.sumCompl (· ∈ Set.range e))

lemma prefixEquiv_left {α β : Type} (e : β ↪ α) (x : β) :
    prefixEquiv e (Sum.inl x) = e x := rfl

def fixedEquiv {α β : Type} (e : β ↪ α) (p : Matching β) :
    {m : Matching α // ∀ x, m.1 (e x) = e (p.1 x)} ≃ Matching {x : α // x ∉ Set.range e} := by
  classical
  let E := prefixEquiv e
  let C := matchCongr E.symm
  refine (Equiv.subtypeEquiv C ?_).trans (fixedSumEquiv p)
  intro m
  constructor
  · intro h x
    change E.symm (m.1 (E (Sum.inl x))) = Sum.inl (p.1 x)
    rw [prefixEquiv_left, h x, ← prefixEquiv_left e (p.1 x)]
    exact E.symm_apply_apply _
  · intro h x
    have hh := h x
    change E.symm (m.1 (E (Sum.inl x))) = Sum.inl (p.1 x) at hh
    have hh2 := congrArg E hh
    rw [E.apply_symm_apply, prefixEquiv_left, prefixEquiv_left] at hh2
    exact hh2

lemma fixed_count {α β : Type} [Fintype α] [Fintype β] (e : β ↪ α)
    (p : Matching β) :
    Fintype.card {m : Matching α // ∀ x, m.1 (e x) = e (p.1 x)} =
      Fintype.card (Matching (Fin (Fintype.card α - Fintype.card β))) := by
  classical
  have hc : Fintype.card {x : α // x ∉ Set.range e} =
      Fintype.card α - Fintype.card β := by
    rw [Fintype.card_subtype_compl, Fintype.card_range e]
  exact (Fintype.card_congr (fixedEquiv e p)).trans
    (Fintype.card_congr (matchCongr (Fintype.equivFinOfCardEq hc)))

def boolPair : Matching Bool := ⟨not, by
  constructor
  · intro x; cases x <;> decide
  · intro x; cases x <;> rfl⟩

def pairEmb {α : Type} (a b : α) (hab : a ≠ b) : Bool ↪ α where
  toFun x := if x then b else a
  inj' := by intro x y h; cases x <;> cases y <;> simp_all

lemma pair_count {α : Type} [Fintype α] (a b : α) (hab : a ≠ b) :
    Fintype.card {m : Matching α // m.1 a = b} =
    Fintype.card (Matching (Fin (Fintype.card α - 2))) := by
  classical
  have H (m : Matching α) : (m.1 a = b) ↔
      (∀ x, m.1 (pairEmb a b hab x) = pairEmb a b hab (boolPair.1 x)) := by
    constructor
    · intro h x
      cases x
      · exact h
      · have hh := m.2.2 a
        rwa [h] at hh
    · intro h; exact h false
  exact (Fintype.card_congr (Equiv.subtypeEquiv (Equiv.refl (Matching α)) (p := fun m => m.1 a = b)
      (q := fun m => ∀ x, m.1 (pairEmb a b hab x) = pairEmb a b hab (boolPair.1 x)) (fun m => H m))).trans
    (by simpa using fixed_count (pairEmb a b hab) boolPair)

set_option maxHeartbeats 2000000 in
lemma matching_card (n : ℕ) :
    Fintype.card (Matching (Fin (2*n))) = Nat.doubleFactorial (2*n-1) := by
  classical
  induction n with
  | zero =>
    let m : Matching (Fin (2*0)) := ⟨id, by
      constructor <;> intro x <;> exact Fin.elim0 x⟩
    haveI : Unique (Matching (Fin (2*0))) := ⟨⟨m⟩, fun x => by
      apply Subtype.ext; funext i; exact Fin.elim0 i⟩
    simp [Nat.doubleFactorial]
  | succ n ih =>
    let α := Fin (2*(n+1))
    let a : α := ⟨0, by change 0 < 2*(n+1); omega⟩
    let e : Matching α ≃ Σ b : {b : α // b ≠ a}, {m : Matching α // m.1 a = b.1} :=
      { toFun := fun m => ⟨⟨m.1 a, m.2.1 a⟩, ⟨m,rfl⟩⟩
        invFun := fun x => x.2.1
        left_inv := fun _ => rfl
        right_inv := by rintro ⟨⟨b,hb⟩,m,hm⟩; change m.1 a = b at hm; subst b; rfl }
    change Fintype.card (Matching α) = _
    rw [Fintype.card_congr e, Fintype.card_sigma]
    have H (b : {b : α // b ≠ a}) :
      Fintype.card {m : Matching α // m.1 a = b.1} =
        Fintype.card (Matching (Fin (Fintype.card α - 2))) :=
      by simpa only [← Nat.card_eq_fintype_card] using (@pair_count α _ a b.1 b.2.symm)
    simp_rw [H]
    have he : Fintype.card α - 2 = 2*n := by simp [α]; omega
    simp_rw [he, ih, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    have hb : Fintype.card {b : α // b ≠ a} = 2*(n+1)-1 := by
      rw [Fintype.card_subtype_compl]
      simp [α, Fintype.card_unique]
    rw [hb]
    cases n with
    | zero => decide
    | succ n =>
      have h : 2*(n+1+1)-1 = (2*(n+1)-1)+2 := by omega
      rw [h, Nat.doubleFactorial_add_two]

end
end Adjacent

open Function Finset
open scoped Classical
namespace Adjacent
noncomputable section

def Good (N k : ℕ) := {f : Fin k ↪o Fin N //
  (∀ i, (f i).val + 1 < N) ∧
  (∀ i j, i < j → (f i).val + 1 < (f j).val)}

instance (N k : ℕ) : Fintype (Good N k) := by
  classical
  unfold Good
  exact Fintype.ofFinite _

lemma order_index_le {N k : ℕ} (f : Fin k ↪o Fin N) (i : Fin k) : i.val ≤ (f i).val := by
  have H : ∀ a : ℕ, ∀ ha : a < k, a ≤ (f ⟨a,ha⟩).val := by
    intro a
    induction a with
    | zero => simp
    | succ a ih =>
      intro ha
      have h := ih (by omega : a < k)
      have h' := f.strictMono (show (⟨a, by omega⟩ : Fin k) < ⟨a+1,ha⟩ by exact Nat.lt_succ_self _)
      change (f ⟨a, by omega⟩).val < (f ⟨a+1, ha⟩).val at h'
      omega
  exact H i.val i.isLt

lemma compress_mono {N k : ℕ} (f : Good N k) :
    StrictMono (fun i : Fin k => (f.1 i).val - i.val) := by
  cases k with
  | zero => intro i; exact Fin.elim0 i
  | succ k =>
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    have h := f.2.2 i.castSucc i.succ (Fin.castSucc_lt_succ)
    have h' := order_index_le f.1 i.castSucc
    simp only [Fin.val_castSucc, Fin.val_succ] at *
    omega

def compress {N k : ℕ} (f : Good N k) : Fin k ↪o Fin (N-k) :=
  OrderEmbedding.ofStrictMono (fun i =>
    ⟨(f.1 i).val - i.val, by
      have hi := i.isLt
      have hk : 0 < k := by omega
      let j : Fin k := ⟨k-1, by omega⟩
      have h := (compress_mono f).monotone (show i ≤ j by change i.val ≤ k-1; omega)
      have h' := f.2.1 j
      have hj := order_index_le f.1 j
      have hjv : j.val = k-1 := rfl
      change (f.1 i).val - i.val ≤ (f.1 j).val - j.val at h
      omega⟩) (fun _ _ h => compress_mono f h)

def decompress {N k : ℕ} (f : Fin k ↪o Fin (N-k)) : Good N k := by
  let g : Fin k → Fin N := fun i => ⟨(f i).val+i.val, by have := (f i).isLt; omega⟩
  have hg (i j : Fin k) (h : i < j) : (g i).val+1 < (g j).val := by
    have hf := f.strictMono h
    change (f i).val < (f j).val at hf
    change i.val < j.val at h
    dsimp [g]
    omega
  exact ⟨OrderEmbedding.ofStrictMono g (fun i j h => by have := hg i j h; exact Nat.lt_of_succ_lt this),
    fun i => by change (f i).val + i.val + 1 < N; have := (f i).isLt; have := i.isLt; omega, hg⟩

def goodEquiv (N k : ℕ) : Good N k ≃ (Fin k ↪o Fin (N-k)) where
  toFun := compress
  invFun := decompress
  left_inv f := by
    apply Subtype.ext
    ext i
    change (f.1 i).val-i.val+i.val = (f.1 i).val
    exact Nat.sub_add_cancel (order_index_le f.1 i)
  right_inv f := by
    ext i
    change (f i).val+i.val-i.val = (f i).val
    omega

lemma orderEmbedding_card (N k : ℕ) :
    Fintype.card (Fin k ↪o Fin N) = N.choose k := by
  classical
  rw [Fintype.card_congr Set.powersetCard.ofFinEmbEquiv]
  -- The powersetCard subtype is the finsets of size k.
  rw [Fintype.card_of_subtype (Finset.univ.powersetCard k) (by intro s; simp)]
  simp

lemma good_card (N k : ℕ) : Fintype.card (Good N k) = (N-k).choose k := by
  classical
  rw [Fintype.card_congr (goodEquiv N k), orderEmbedding_card]

def edges {N k : ℕ} (f : Good N k) : (Fin k × Bool) ↪ Fin N where
  toFun := fun x => ⟨(f.1 x.1).val + (if x.2 then 1 else 0), by
    have := f.2.1 x.1
    cases x.2 <;> simp_all <;> omega⟩
  inj' := by
    rintro ⟨i,b⟩ ⟨j,c⟩ h
    have h' := congrArg Fin.val h
    change (f.1 i).val + (if b then 1 else 0) = (f.1 j).val + (if c then 1 else 0) at h'
    have hij : i=j := by
      rcases lt_trichotomy i j with h|h|h
      · have := f.2.2 i j h
        cases b <;> cases c <;> simp_all <;> omega
      · exact h
      · have := f.2.2 j i h
        cases b <;> cases c <;> simp_all <;> omega
    subst j
    have : b=c := by cases b <;> cases c <;> simp at h' ⊢ <;> omega
    subst c; rfl

end
end Adjacent
namespace Adjacent
open Function Finset Filter Topology Real
open scoped BigOperators Nat Classical
noncomputable section

def isShort {N : ℕ} (m : Matching (Fin N)) (i : Fin N) : Prop :=
  (m.1 i).val = i.val+1

def shortCount {N : ℕ} (m : Matching (Fin N)) : ℕ :=
  (Finset.univ.filter (fun i => (m.1 i).val = i.val+1)).card

def Marked {N : ℕ} (m : Matching (Fin N)) (k : ℕ) :=
  {f : Fin k ↪o Fin N // ∀ i, isShort m (f i)}

instance {N : ℕ} (m : Matching (Fin N)) (k : ℕ) : Fintype (Marked m k) := by
  classical
  unfold Marked
  exact Fintype.ofFinite _

def markedEquiv {N : ℕ} (m : Matching (Fin N)) (k : ℕ) :
    Marked m k ≃ (Fin k ↪o {i : Fin N // isShort m i}) where
  toFun f := OrderEmbedding.ofStrictMono (fun i => ⟨f.1 i, f.2 i⟩)
    (fun _ _ h => f.1.strictMono h)
  invFun f := ⟨OrderEmbedding.ofStrictMono (fun i => (f i).val)
    (fun _ _ h => f.strictMono h), fun i => (f i).property⟩
  left_inv f := by apply Subtype.ext; ext i; rfl
  right_inv f := by ext i; rfl

lemma marked_card {N : ℕ} (m : Matching (Fin N)) (k : ℕ) :
    Fintype.card (Marked m k) = (shortCount m).choose k := by
  classical
  rw [Fintype.card_congr (markedEquiv m k),
    Fintype.card_congr Set.powersetCard.ofFinEmbEquiv]
  rw [← Nat.card_eq_fintype_card, Set.powersetCard.card, Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype]
  unfold shortCount
  congr 1
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro i hi
  rfl

lemma marked_good {N k : ℕ} (m : Matching (Fin N)) (f : Marked m k) :
    (∀ i, (f.1 i).val + 1 < N) ∧
    (∀ i j, i < j → (f.1 i).val + 1 < (f.1 j).val) := by
  constructor
  · intro i
    have h := f.2 i
    unfold isShort at h
    rw [← h]
    exact (m.1 (f.1 i)).isLt
  · intro i j hij
    have hi := f.2 i
    have hj := f.2 j
    unfold isShort at hi hj
    have hlt := f.1.strictMono hij
    change (f.1 i).val < (f.1 j).val at hlt
    by_contra! hbad
    have hEq : m.1 (f.1 i) = f.1 j := Fin.ext (by omega)
    have hinv := m.2.2 (f.1 i)
    rw [hEq] at hinv
    have := congrArg Fin.val hinv
    omega

def pairFlip (k : ℕ) : Matching (Fin k × Bool) :=
  ⟨fun x => (x.1, !x.2), by
    constructor
    · rintro ⟨i,b⟩ h; cases b <;> simp_all
    · rintro ⟨i,b⟩; cases b <;> rfl⟩

lemma edges_false {N k : ℕ} (f : Good N k) (i : Fin k) :
    edges f (i,false) = f.1 i := by
  apply Fin.ext
  rfl

lemma edges_true_val {N k : ℕ} (f : Good N k) (i : Fin k) :
    (edges f (i,true)).val = (f.1 i).val+1 := rfl

lemma extend_iff {N k : ℕ} (f : Good N k) (m : Matching (Fin N)) :
    (∀ i, isShort m (f.1 i)) ↔
      (∀ x, m.1 (edges f x) = edges f ((pairFlip k).1 x)) := by
  constructor
  · intro h
    rintro ⟨i,b⟩
    cases b
    · change m.1 (edges f (i,false)) = edges f (i,true)
      apply Fin.ext
      rw [edges_false, edges_true_val]
      exact h i
    · change m.1 (edges f (i,true)) = edges f (i,false)
      have hi : m.1 (edges f (i,false)) = edges f (i,true) := by
        apply Fin.ext
        rw [edges_false, edges_true_val]
        exact h i
      have hinv := m.2.2 (edges f (i,false))
      rw [hi] at hinv
      exact hinv
  · intro h i
    have hi := congrArg Fin.val (h (i,false))
    change (m.1 (edges f (i,false))).val = (edges f (i,true)).val at hi
    rw [edges_false, edges_true_val] at hi
    exact hi

def swapMarked (N k : ℕ) :
    (Σ m : Matching (Fin N), Marked m k) ≃
      (Σ f : Good N k, {m : Matching (Fin N) // ∀ i, isShort m (f.1 i)}) where
  toFun x := ⟨⟨x.2.1, marked_good x.1 x.2⟩, ⟨x.1,x.2.2⟩⟩
  invFun x := ⟨x.2.1, ⟨x.1.1,x.2.2⟩⟩
  left_inv := by rintro ⟨m,f⟩; rfl
  right_inv := by rintro ⟨f,m⟩; rfl

set_option maxHeartbeats 2000000 in
lemma moment_count (n k : ℕ) :
    (∑ m : Matching (Fin (2*n)), (shortCount m).choose k) =
      (2*n-k).choose k * Nat.doubleFactorial (2*(n-k)-1) := by
  classical
  have h := Fintype.card_congr (swapMarked (2*n) k)
  simp only [Fintype.card_sigma, marked_card] at h
  have hf (f : Good (2*n) k) :
      Fintype.card {m : Matching (Fin (2*n)) // ∀ i, isShort m (f.1 i)} =
      Nat.doubleFactorial (2*(n-k)-1) := by
    rw [Fintype.card_congr (Equiv.subtypeEquiv (Equiv.refl (Matching (Fin (2*n))))
      (p := fun m => ∀ i, isShort m (f.1 i))
      (q := fun m => ∀ x, m.1 (edges f x) = edges f ((pairFlip k).1 x))
      (fun m => extend_iff f m))]
    calc
      _ = Fintype.card (Matching (Fin (Fintype.card (Fin (2*n)) - Fintype.card (Fin k × Bool)))) := by
        simpa only [← Nat.card_eq_fintype_card] using fixed_count (edges f) (pairFlip k)
      _ = _ := by
        have he : Fintype.card (Fin (2*n)) - Fintype.card (Fin k × Bool) = 2*(n-k) := by
          simp; omega
        rw [he, matching_card]
  simp_rw [hf, Finset.sum_const, Finset.card_univ, smul_eq_mul, good_card] at h
  exact h

lemma shortCount_le {N : ℕ} (m : Matching (Fin N)) : shortCount m ≤ N := by
  classical
  unfold shortCount
  exact (Finset.card_filter_le _ _).trans (by simp)

lemma binomial_inversion (r s L : ℕ) (hr : r ≤ L) :
    (∑ j ∈ range (L+1), (-1 : ℝ)^j * ((s+j).choose s : ℝ) * (r.choose (s+j) : ℝ)) =
      if r = s then 1 else 0 := by
  by_cases h : s ≤ r
  · have H (j : ℕ) : ((s+j).choose s : ℝ) * (r.choose (s+j) : ℝ) =
        (r.choose s : ℝ) * ((r-s).choose j : ℝ) := by
      rw [mul_comm]
      exact_mod_cast (by simpa using Nat.choose_mul (n := r) (k := s+j) (s := s) (by omega))
    simp_rw [mul_assoc, H, ← mul_left_comm (r.choose s : ℝ)]
    rw [← Finset.mul_sum]
    have hsub : range (r-s+1) ⊆ range (L+1) := by
      intro j hj; simp only [mem_range] at *; omega
    rw [← Finset.sum_subset hsub (fun j hj hnot => by
      have : r-s < j := by simp only [mem_range, not_lt] at hnot; omega
      simp [Nat.choose_eq_zero_of_lt this])]
    have hpow := add_pow (-1 : ℝ) 1 (r-s)
    simp only [neg_add_cancel, one_pow, mul_one] at hpow
    rw [← hpow]
    by_cases hEq : r=s
    · subst r; simp
    · have hne : r-s ≠ 0 := by omega
      simp [hEq,hne]
  · have hz (j : ℕ) : r.choose (s+j) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [hz, show r ≠ s by omega]

end
end Adjacent
namespace Adjacent
open Filter Topology Real Finset Function
open scoped BigOperators Nat Classical
noncomputable section

def permOfMatching {α : Type} (m : Matching α) : Equiv.Perm α :=
  ⟨m.1, m.1, m.2.2, m.2.2⟩

def countEquiv (n s : ℕ) :
    {m : Matching (Fin (2*n)) // shortCount m = s} ≃
      {p : Equiv.Perm (Fin (2*n)) //
        (∀ i, p i ≠ i) ∧ (∀ i, p (p i) = i) ∧
        (Finset.univ.filter fun i : Fin (2*n) => (p i).val = i.val+1).card = s} where
  toFun x := ⟨permOfMatching x.1, x.1.2.1, x.1.2.2, by
    exact x.2⟩
  invFun x := ⟨⟨x.1, x.2.1, x.2.2.1⟩, by exact x.2.2.2⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; ext i; rfl

lemma d_eq_count (n s : ℕ) :
    OMA.S_oeis_a079267.d n s = Fintype.card {m : Matching (Fin (2*n)) // shortCount m = s} := by
  classical
  rw [Fintype.card_congr (countEquiv n s), Fintype.card_subtype]
  rfl

lemma d_eq_sum (n s : ℕ) :
    (OMA.S_oeis_a079267.d n s : ℝ) =
      ∑ m : Matching (Fin (2*n)), if shortCount m = s then 1 else 0 := by
  classical
  rw [d_eq_count, Fintype.card_subtype, ← Finset.sum_filter]
  simp

lemma summand_identity (n s j : ℕ) :
    ((-1 : ℝ)^j * ((s+j).choose s : ℝ)) *
        (((2*n-(s+j)).choose (s+j) : ℝ) * df (n-(s+j)) / df n) =
      (((-1 : ℝ)^j / j.factorial / s.factorial) * ratio n (s+j)) := by
  rw [moment_ratio, choose_formula _ _ (by omega : s ≤ s+j), show s+j-s=j by omega]
  field_simp

lemma exact_series (n s : ℕ) :
    (OMA.S_oeis_a079267.d n s : ℝ) / df n =
      ∑' j : ℕ, ((-1 : ℝ)^j / j.factorial / s.factorial) * ratio n (s+j) := by
  classical
  rw [tsum_eq_sum (s := range (2*n+1)) (fun j hj => by
    have h : ¬ s+j ≤ n := by simp only [mem_range, not_lt] at hj; omega
    simp [ratio,h])]
  rw [d_eq_sum]
  simp_rw [← binomial_inversion _ s (2*n) (shortCount_le _)]
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Finset.mul_sum]
  have hm : (∑ m : Matching (Fin (2*n)), ((shortCount m).choose (s+j) : ℝ)) =
      ((2*n-(s+j)).choose (s+j) : ℝ) * df (n-(s+j)) := by
    exact_mod_cast moment_count n (s+j)
  rw [hm, mul_div_assoc]
  exact summand_identity n s j

end
end Adjacent

theorem Adjacent.final : ∀ s : ℕ, Tendsto
    (fun n : ℕ => (OMA.S_oeis_a079267.d n s : ℝ) / (Nat.doubleFactorial (2*n-1) : ℝ))
    atTop (𝓝 (Real.exp (-1) / s.factorial)) := by
  intro s
  have h := Adjacent.series_limit s
  apply h.congr
  intro n
  exact (Adjacent.exact_series n s).symm


theorem OMA.solution : type_of% @OMA.S_oeis_a079267.main := by
  exact Adjacent.final
