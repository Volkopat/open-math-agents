import OMAStatements.S_mo_158834
import Mathlib

/-!
For odd d = 2s+1, sum the d cyclic coordinate shifts on the ternary words of
length d. The shifts commute with one another's inverses, so the sum is normal.
Split the basis into the binary words of weight at most s and their complement.

Decrementing a zero in a low-weight binary word creates exactly one digit two.
Its location recovers the original word, so the rows of the small corner have
disjoint supports of size at most d. The opposite corner sends the indicator
of the binary layer of weight s to a vector with value s+1 throughout the layer
of weight s+1. Complementation makes the two layers equinumerous. The ratio is
therefore at least (s+1)/√d, unbounded as d grows.
-/

open Finset Matrix
open scoped BigOperators
namespace NormalCorners
abbrev Word (d : ℕ) := Fin d → ZMod 3

def unit {d : ℕ} (i : Fin d) : Word d := Pi.single i 1
def ones {d : ℕ} (w : Word d) := (univ.filter (fun j => w j = 1)).card
def inside {d : ℕ} (s : ℕ) (w : Word d) : Prop := (∀ j, w j ≠ 2) ∧ ones w ≤ s

lemma down_same {d : ℕ} (w : Word d) (i j : Fin d) (h : j ≠ i) :
    (w - unit i) j = w j := by simp [unit, Pi.single_eq_of_ne h]

lemma down_at {d : ℕ} (w : Word d) (i : Fin d) :
    (w - unit i) i = w i - 1 := by simp [unit]

lemma down_inside {d s : ℕ} {w : Word d} (hw : inside s w) {i : Fin d}
    (hi : w i = 1) : inside s (w - unit i) := by
  constructor
  · intro j
    by_cases h : j = i
    · subst j
      rw [down_at, hi]
      decide
    · simpa only [down_same _ _ _ h] using hw.1 j
  · refine le_trans (Finset.card_le_card ?_) hw.2
    intro j hj
    simp only [mem_filter, mem_univ, true_and] at hj ⊢
    by_cases h : j = i
    · simpa [h] using hi
    · simpa only [down_same _ _ _ h] using hj

lemma weak_unique {d s : ℕ} {x y : Word d} (hx : inside s x) (hy : inside s y)
    {i j : Fin d} (he : x - unit i = y - unit j) (ho : ¬ inside s (x - unit i)) :
    i = j ∧ x = y := by
  have hz : x i = 0 := by
    have h1 : x i ≠ 1 := fun h => ho (down_inside hx h)
    have h2 := hx.1 i
    exact (by decide : ∀ a : Fin 3, a ≠ 1 → a ≠ 2 → a = 0) (x i) h1 h2
  have hne : (x - unit i) i = 2 := by rw [down_at, hz]; decide
  have hij : i = j := by
    by_contra h
    rw [he, down_same _ _ _ h] at hne
    exact hy.1 i hne
  subst j
  exact ⟨rfl, sub_left_inj.mp he⟩

noncomputable def shift {d : ℕ} (i : Fin d) : Equiv.Perm (Word d) :=
  Equiv.subRight (unit i)

open scoped Matrix.Norms.L2Operator

-- A zero-one matrix with disjoint row supports has diagonal row Gram matrix.
lemma weak_bound {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (N : α → Finset β) (d : ℕ) (hd : ∀ i, (N i).card ≤ d)
    (dis : ∀ i j b, b ∈ N i → b ∈ N j → i = j) :
    let C : Matrix α β ℂ := fun i b => if b ∈ N i then 1 else 0
    ‖C‖ ^ 2 ≤ d := by
  classical
  intro C
  have diag : C * Cᴴ = diagonal (fun i => ((N i).card : ℂ)) := by
    ext i j
    by_cases he : i = j
    · subst j
      rw [Matrix.mul_apply, diagonal_apply_eq]
      simp_rw [Matrix.conjTranspose_apply]
      simp [C, apply_ite]
    · rw [diagonal_apply_ne _ he, mul_apply]
      apply Finset.sum_eq_zero
      intro b _
      have hn : ¬(b ∈ N i ∧ b ∈ N j) := fun h => he (dis i j b h.1 h.2)
      rw [Matrix.conjTranspose_apply]
      by_cases hb : b ∈ N i <;> simp_all [C]
  have hb : ‖(fun i => ((N i).card : ℂ))‖ ≤ (d : ℝ) := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro i
    simpa using (show ((N i).card : ℝ) ≤ d by exact_mod_cast hd i)
  calc
    ‖C‖ ^ 2 = ‖C * Cᴴ‖ := by
      simpa only [sq, conjTranspose_conjTranspose, l2_opNorm_conjTranspose] using
        (l2_opNorm_conjTranspose_mul_self Cᴴ).symm
    _ = _ := congrArg norm diag
    _ ≤ _ := by simpa using hb

-- Test the operator on the indicator vector of the input layer.
lemma strong_bound {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (B : Matrix α β ℂ) (U : Finset α) (V : Finset β) (k : ℕ) (hV : V.Nonempty)
    (hc : U.card = V.card) (h : ∀ i ∈ U, ∑ j ∈ V, B i j = (k : ℂ)) : (k : ℝ) ≤ ‖B‖ := by
  classical
  let v : EuclideanSpace ℂ β := WithLp.toLp 2 (fun j => if j ∈ V then 1 else 0)
  let w : EuclideanSpace ℂ α := WithLp.toLp 2 (B *ᵥ v)
  have hv : ‖v‖ ^ 2 = (V.card : ℝ) := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [v, apply_ite]
  have hw (i) (hi : i ∈ U) : w i = (k : ℂ) := by
    change (B *ᵥ (fun j => if j ∈ V then 1 else 0)) i = _
    simpa [Matrix.mulVec, dotProduct, mul_ite] using h i hi
  have bound : (k : ℝ)^2 * V.card ≤ ‖w‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      (k : ℝ)^2 * V.card = ∑ i ∈ U, ‖w i‖^2 := by
        rw [← hc, mul_comm]
        symm
        calc
          _ = ∑ _i ∈ U, (k : ℝ)^2 := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [hw i hi]
          _ = _ := by simp
      _ ≤ _ := Finset.sum_le_univ_sum_of_nonneg (fun _ => sq_nonneg _)
  have hm : ‖w‖ ≤ ‖B‖ * ‖v‖ := B.l2_opNorm_mulVec v
  have hs := pow_le_pow_left₀ (norm_nonneg w) hm 2
  rw [mul_pow, hv] at hs
  have hpos : (0 : ℝ) < V.card := by exact_mod_cast Finset.card_pos.mpr hV
  have hk := (mul_le_mul_iff_left₀ hpos).mp (bound.trans hs)
  nlinarith [norm_nonneg B]

variable {d n : ℕ}

-- Put each word into its chosen half. The extended permutations fix unused indices.
noncomputable def place (s : ℕ) (e : Word d ↪ Fin n) :
    Word d ↪ (Fin n ⊕ Fin n) := by
  classical
  exact ⟨fun w => if inside s w then Sum.inr (e w) else Sum.inl (e w), by
    intro x y h
    dsimp only at h
    split_ifs at h <;> simp_all⟩

lemma place_in (s : ℕ) (e : Word d ↪ Fin n) {w} (h : inside s w) :
    place s e w = Sum.inr (e w) := by classical exact if_pos h

lemma place_out (s : ℕ) (e : Word d ↪ Fin n) {w} (h : ¬inside s w) :
    place s e w = Sum.inl (e w) := by classical exact if_neg h

noncomputable def perm (s : ℕ) (e : Word d ↪ Fin n) (i : Fin d) :=
  Equiv.Perm.viaEmbeddingHom (place s e) (shift i)

noncomputable def full (s : ℕ) (e : Word d ↪ Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  ∑ i : Fin d, (perm s e i).permMatrix ℂ

lemma full_normal (s : ℕ) (e : Word d ↪ Fin n) : IsStarNormal (full s e) := by
  classical
  constructor
  change (full s e)ᴴ * full s e = full s e * (full s e)ᴴ
  simp only [full, conjTranspose_sum, conjTranspose_permMatrix, sum_mul, mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← permMatrix_mul, ← permMatrix_mul]
  congr 1
  simp only [perm, ← map_inv, ← map_mul]
  apply congrArg
  ext w k
  simp [shift, Equiv.Perm.mul_apply]
  abel

lemma on_word (s : ℕ) (e : Word d ↪ Fin n) (w : Word d) (i : Fin d) :
    perm s e i (place s e w) = place s e (w - unit i) := by
  exact Equiv.Perm.viaEmbedding_apply _ _ _

lemma off_word (s : ℕ) (e : Word d ↪ Fin n) (a) (ha : a ∉ Set.range (place s e)) (i : Fin d) :
    perm s e i a = a := by exact Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ ha

lemma full_entry (s : ℕ) (e : Word d ↪ Fin n) (a b) :
    full s e a b = ∑ i : Fin d, if perm s e i a = b then (1 : ℂ) else 0 := by
  classical
  simp [full, Matrix.sum_apply, Equiv.Perm.permMatrix, eq_comm]

lemma in_place (s : ℕ) (e : Word d ↪ Fin n) {w a} (h : place s e w = Sum.inr a) :
    inside s w ∧ e w = a := by
  by_cases h' : inside s w
  · exact ⟨h', Sum.inr.inj ((place_in _ _ h').symm.trans h)⟩
  · rw [place_out _ _ h'] at h
    contradiction

lemma out_place (s : ℕ) (e : Word d ↪ Fin n) {w a} (h : place s e w = Sum.inl a) :
    ¬inside s w ∧ e w = a := by
  by_cases h' : inside s w
  · rw [place_in _ _ h'] at h
    contradiction
  · exact ⟨h', Sum.inl.inj ((place_out _ _ h').symm.trans h)⟩

lemma crossing (s : ℕ) (e : Word d ↪ Fin n) {a b : Fin n} {i : Fin d}
    (h : perm s e i (Sum.inr a) = Sum.inl b) :
    ∃ x, inside s x ∧ e x = a ∧ ¬inside s (x - unit i) ∧ e (x - unit i) = b := by
  by_cases hr : Sum.inr a ∈ Set.range (place s e)
  · obtain ⟨x,hx⟩ := hr
    have ho := out_place s e ((on_word s e x i).symm.trans (hx ▸ h))
    exact ⟨x, (in_place s e hx).1, (in_place s e hx).2, ho⟩
  · rw [off_word _ _ _ hr] at h
    contradiction

lemma cross_unique (s : ℕ) (e : Word d ↪ Fin n) {a c b : Fin n} {i j : Fin d}
    (h : perm s e i (Sum.inr a) = Sum.inl b) (h' : perm s e j (Sum.inr c) = Sum.inl b) :
    i = j ∧ a = c := by
  obtain ⟨x,hx,rfl,ho,hb⟩ := crossing s e h
  obtain ⟨y,hy,rfl,_,hb'⟩ := crossing s e h'
  obtain ⟨rfl,rfl⟩ := weak_unique hx hy (e.injective (hb.trans hb'.symm)) ho
  exact ⟨rfl,rfl⟩

noncomputable def neighbors (s : ℕ) (e : Word d ↪ Fin n) (a : Fin n) : Finset (Fin n) := by
  classical exact univ.filter (fun b => ∃ i, perm s e i (Sum.inr a) = Sum.inl b)

lemma mem_neighbors (s : ℕ) (e : Word d ↪ Fin n) (a b : Fin n) :
    b ∈ neighbors s e a ↔ ∃ i, perm s e i (Sum.inr a) = Sum.inl b := by
  classical simp [neighbors]

lemma small_entry (s : ℕ) (e : Word d ↪ Fin n) (a b : Fin n) :
    (full s e).toBlocks₂₁ a b = if b ∈ neighbors s e a then 1 else 0 := by
  classical
  change full s e (Sum.inr a) (Sum.inl b) = _
  rw [full_entry]
  by_cases hb : b ∈ neighbors s e a
  · obtain ⟨i,hi⟩ := (mem_neighbors _ _ _ _).mp hb
    rw [if_pos hb, Finset.sum_eq_single i, if_pos hi]
    · intro j _ hji
      exact if_neg (fun hj => hji (cross_unique _ _ hj hi).1)
    · simp
  · have hh := mt (mem_neighbors s e a b).mpr hb
    push Not at hh
    simp [hb,hh]

lemma small_bound (s : ℕ) (e : Word d ↪ Fin n) :
    ‖(full s e).toBlocks₂₁‖ ^ 2 ≤ d := by
  classical
  have hc (a : Fin n) : (neighbors s e a).card ≤ d := by
    let f (b : ↥(neighbors s e a)) := ((mem_neighbors _ _ _ _).mp b.property).choose
    have hf : Function.Injective f := by
      intro b c h
      have h1 := ((mem_neighbors s e a b.val).mp b.property).choose_spec
      have h2 := ((mem_neighbors s e a c.val).mp c.property).choose_spec
      change perm s e (f b) _ = _ at h1
      rw [h] at h1
      exact Subtype.ext (Sum.inl.inj (h1.symm.trans h2))
    simpa using Fintype.card_le_of_injective f hf
  have hs (i j b : Fin n) (h : b ∈ neighbors s e i) (h' : b ∈ neighbors s e j) : i=j := by
    obtain ⟨k,hk⟩ := (mem_neighbors _ _ _ _).mp h
    obtain ⟨l,hl⟩ := (mem_neighbors _ _ _ _).mp h'
    exact (cross_unique s e hk hl).2
  convert weak_bound (neighbors s e) d hc hs using 3
  exact congrArg norm (Matrix.ext (small_entry s e))

def binary : Finset (Fin d) ↪ Word d where
  toFun Y i := if i ∈ Y then 1 else 0
  inj' := by
    intro X Y h
    ext i
    have h' := congrFun h i
    by_cases hx : i ∈ X <;> by_cases hy : i ∈ Y <;> simp_all

lemma binary_val (Y : Finset (Fin d)) (i : Fin d) :
    binary Y i = if i ∈ Y then 1 else 0 := rfl

lemma ones_binary (Y : Finset (Fin d)) : ones (binary Y) = Y.card := by
  unfold ones
  congr 1
  ext i
  by_cases h : i ∈ Y <;> simp [binary_val, h]

lemma binary_in (s : ℕ) (Y : Finset (Fin d)) : inside s (binary Y) ↔ Y.card ≤ s := by
  rw [inside, ones_binary, and_iff_right]
  intro i
  rw [binary_val]
  split <;> decide

lemma erase_step (Y : Finset (Fin d)) (i : Fin d) (hi : i ∈ Y) :
    binary Y - unit i = binary (Y.erase i) := by
  funext j
  by_cases h : j = i
  · subst j
    simp [unit, binary_val, hi]
  · simp [down_same _ _ _ h, binary_val, h]

def layer (s : ℕ) (e : Word d ↪ Fin n) : Finset (Fin n) :=
  (univ.powersetCard s).map (binary.trans e)

lemma layer_card (s : ℕ) (e : Word d ↪ Fin n) : (layer s e).card = d.choose s := by
  simp [layer, card_powersetCard]

lemma big_row (s : ℕ) (e : Word d ↪ Fin n) (Y : Finset (Fin d)) (hY : Y.card = s+1) :
    ∑ b ∈ layer s e, (full s e).toBlocks₁₂ (e (binary Y)) b = ((s+1:ℕ):ℂ) := by
  classical
  change ∑ b ∈ layer s e, full s e (Sum.inl (e (binary Y))) (Sum.inr b) = _
  simp_rw [full_entry]
  rw [Finset.sum_comm]
  have hplace := place_out s e (w := binary Y) (by rw [binary_in,hY]; omega)
  rw [← hplace]
  simp_rw [on_word]
  calc
    _ = ∑ i : Fin d, if i ∈ Y then (1:ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ Y
      · have he := card_erase_of_mem hi
        have hc : (Y.erase i).card = s := by omega
        rw [erase_step _ _ hi, place_in _ _ ((binary_in _ _).mpr hc.le), if_pos hi]
        have hm : e (binary (Y.erase i)) ∈ layer s e := by
          exact mem_map.mpr ⟨_,mem_powersetCard.mpr ⟨subset_univ _,hc⟩,rfl⟩
        simp [hm]
      · have ho : ¬inside s (binary Y - unit i) := by
          intro hin
          have hz := hin.1 i
          rw [down_at, binary_val, if_neg hi] at hz
          exact hz (by decide)
        simp [place_out _ _ ho, hi]
    _ = _ := by simp [hY]

lemma big_bound (s : ℕ) (e : Word (2*s+1) ↪ Fin n) :
    ((s+1:ℕ):ℝ) ≤ ‖(full s e).toBlocks₁₂‖ := by
  apply strong_bound _ (layer (s+1) e) (layer s e)
  · rw [← card_pos, layer_card]
    apply Nat.choose_pos
    omega
  · rw [layer_card, layer_card, Nat.choose_symm_half]
  · intro a ha
    obtain ⟨Y,hY,rfl⟩ := mem_map.mp ha
    exact big_row s e Y (mem_powersetCard.mp hY).2

lemma small_ne_zero (s : ℕ) (e : Word (2*s+1) ↪ Fin n) : (full s e).toBlocks₂₁ ≠ 0 := by
  let x := @binary (2*s+1) ∅
  let i : Fin (2*s+1) := ⟨0,by omega⟩
  have hin : inside s x := (binary_in _ _).mpr (by simp)
  have hout : ¬inside s (x - unit i) := by
    intro h
    have he := h.1 i
    rw [down_at] at he
    exact he (by change (0 : ZMod 3) - 1 = 2; decide)
  have hp := on_word s e x i
  rw [place_in _ _ hin, place_out _ _ hout] at hp
  have hm := (mem_neighbors s e _ _).mpr ⟨i,hp⟩
  intro hz
  have ha := small_entry s e (e x) (e (x-unit i))
  rw [hz, if_pos hm] at ha
  exact zero_ne_one ha

-- Choose the largest odd word length whose full ternary cube fits in one half.
def level (n : ℕ) : ℕ := (Nat.log 3 n - 1) / 2

noncomputable def embed (n : ℕ) (h : 3 ≤ n) : Word (2*level n+1) ↪ Fin n := by
  apply Classical.choice
  apply Function.Embedding.nonempty_of_card_le
  have hn : n ≠ 0 := by omega
  have hl : 1 ≤ Nat.log 3 n := (Nat.le_log_iff_pow_le (by decide) hn).mpr (by simpa using h)
  have he : 2 * level n + 1 ≤ Nat.log 3 n := by unfold level; omega
  simpa [Word, Fintype.card_pi] using
    (Nat.pow_le_pow_right (by decide : 0 < 3) he).trans (Nat.pow_log_le_self 3 hn)

noncomputable def family (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  if h : 3 ≤ n then full (level n) (embed n h) else 0

lemma family_normal (n : ℕ) : IsStarNormal (family n) := by
  unfold family
  split
  · exact full_normal _ _
  · infer_instance

lemma ratio_bound {s k : ℕ} {b c : ℝ} (hs : 4 * k ^ 2 ≤ s) (hc : 0 < c)
    (hu : c^2 ≤ 2*(s:ℝ)+1) (hl : (s:ℝ)+1 ≤ b) : (k:ℝ) ≤ b/c := by
  have hks : (4:ℝ) * k^2 ≤ s := by exact_mod_cast hs
  have bound : ((k:ℝ)*c)^2 ≤ ((s:ℝ)+1)^2 := by
    rw [mul_pow]
    calc
      (k:ℝ)^2*c^2 ≤ k^2*(2*(s:ℝ)+1) := by gcongr
      _ ≤ ((s:ℝ)/4)*(2*(s:ℝ)+1) := by gcongr; linarith
      _ ≤ _ := by nlinarith [sq_nonneg (s:ℝ)]
  apply (le_div_iff₀ hc).mpr
  apply le_trans _ hl
  nlinarith [show (0:ℝ) ≤ k*c by positivity]

end NormalCorners

open NormalCorners Filter Matrix
open scoped Matrix.Norms.L2Operator

theorem OMA.solution : type_of% @OMA.S_mo_158834.main := by
  classical
  refine ⟨fun n => (family n).toBlocks₁₁, fun n => (family n).toBlocks₁₂,
    fun n => (family n).toBlocks₂₁, fun n => (family n).toBlocks₂₂, ?_, ?_, ?_⟩
  · intro n
    rw [Matrix.fromBlocks_toBlocks]
    exact family_normal n
  · filter_upwards [eventually_ge_atTop 3] with n hn
    simpa [family,dif_pos hn] using small_ne_zero (level n) (embed n hn)
  · refine tendsto_atTop.mpr fun a => ?_
    obtain ⟨k,hk⟩ := exists_nat_gt a
    filter_upwards [eventually_ge_atTop (max 3 (3^(2*(4*k^2)+1)))] with n hn
    have h3 := (le_max_left _ _).trans hn
    have hn0 : n ≠ 0 := by omega
    have hlog : 2*(4*k^2)+1 ≤ Nat.log 3 n :=
      (Nat.le_log_iff_pow_le (by decide) hn0).mpr ((le_max_right _ _).trans hn)
    have hs : 4*k^2 ≤ level n := by unfold level; omega
    let e := embed n h3
    have hu := small_bound (level n) e
    have hl := big_bound (level n) e
    have hp := norm_pos_iff.mpr (small_ne_zero (level n) e)
    change a ≤ ‖(family n).toBlocks₁₂‖ / ‖(family n).toBlocks₂₁‖
    rw [family,dif_pos h3]
    apply hk.le.trans (ratio_bound hs hp ?_ ?_)
    · simpa using hu
    · simpa using hl
