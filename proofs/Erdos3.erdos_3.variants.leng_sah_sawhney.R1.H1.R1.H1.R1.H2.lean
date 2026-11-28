import OMAReductions.R_Erdos3_erdos_3_variants_leng_sah_sawhney_R1_H1_R1_H1_R1
import Mathlib

/-!
# Generalized von Neumann for the interval progression count

This proves the counting input of Leng, Sah and Sawhney, *Improved Bounds
for Szemerédi's Theorem*, Lemma 3.3, arXiv:2402.17995v2.
https://arxiv.org/html/2402.17995v2#S3.SS1

The normalized Cauchy–Schwarz induction generalizes the explicit
four-term argument of @skhakim in the merged PR
https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6175.
That proof is also the source of the supported-sum image lemma used below.

The prescribed modulus need not make every short coefficient a unit.
Unnormalized interval-supported cube sums transfer to the auxiliary
modulus `k! * L + 1`, where all those coefficients are units. Reversal
pairs the positive and negative differences in the cyclic count. The
remaining diagonal is controlled by the zero-increment cube slice.
-/

/-
Wrap-free cyclic lifting for the real-valued progression count in
Leng–Sah–Sawhney, arXiv:2402.17995v2, Lemma 3.3. The supported-sum image
lemma is adapted from @skhakim's merged proof of the four-term case,
https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6175.
-/

namespace OMA.Erdos3ProgressionCyclicLift

open Finset

theorem sum_eq_sum_of_injOn_nonzero {α β : Type*} [DecidableEq β]
    {s : Finset α} {t : Finset β} {f : α → ℝ} {g : β → ℝ} (i : α → β)
    (hmaps : ∀ a ∈ s, i a ∈ t) (hinj : Set.InjOn i s)
    (hsurj : ∀ b ∈ t, g b ≠ 0 → ∃ a ∈ s, i a = b)
    (hval : ∀ a ∈ s, f a = g (i a)) :
    ∑ a ∈ s, f a = ∑ b ∈ t, g b := by
  have hsub : s.image i ⊆ t := by simpa only [image_subset_iff] using hmaps
  calc
    _ = ∑ a ∈ s, g (i a) := sum_congr rfl hval
    _ = ∑ b ∈ s.image i, g b := (sum_image hinj).symm
    _ = _ := sum_subset hsub fun b hb hbnot => by
      by_contra hne
      obtain ⟨a, ha, rfl⟩ := hsurj b hb hne
      exact hbnot (mem_image.mpr ⟨a, ha, rfl⟩)

noncomputable def cyclicTerm (M k : ℕ) (f : ℕ → ℝ) (p : ZMod M × ZMod M) : ℝ :=
  ∏ i ∈ range k, f (p.1 + (i : ZMod M)*p.2).val

noncomputable def forwardCount (N k : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ d ∈ range (N+1), ∑ a ∈ range (N+1), ∏ i ∈ range k, f (a+i*d)

private theorem cast_val_of_lt {M u : ℕ} (hu : u < M) :
    (u : ZMod M).val = u := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt hu]

private theorem nonzero_vertex {M k N : ℕ} (f : ℕ → ℝ)
    (hzero : ∀ n ∉ Icc 1 N, f n = 0)
    {p : ZMod M × ZMod M} (hp : cyclicTerm M k f p ≠ 0)
    {i : ℕ} (hi : i < k) : (p.1 + (i : ZMod M)*p.2).val ∈ Icc 1 N := by
  by_contra hout
  exact hp (Finset.prod_eq_zero (mem_range.mpr hi) (hzero _ hout))

private theorem sum_small_steps {M N k : ℕ} [NeZero M]
    (hk : 2 ≤ k) (hM : k*N < M)
    (f : ℕ → ℝ) (hzero : ∀ n ∉ Icc 1 N, f n = 0) (C : ℕ → Prop) [DecidablePred C] :
    (∑ p ∈ (univ : Finset (ZMod M × ZMod M)).filter
      (fun p => p.2.val ≤ N ∧ C p.2.val), cyclicTerm M k f p) =
    ∑ d ∈ (range (N+1)).filter C, ∑ a ∈ range (N+1), ∏ i ∈ range k, f (a+i*d) := by
  let D := (range (N+1)).filter C
  let A := range (N+1)
  let U := (univ : Finset (ZMod M × ZMod M)).filter (fun p => p.2.val ≤ N ∧ C p.2.val)
  let j (p : ℕ × ℕ) : ZMod M × ZMod M := (p.2, p.1)
  have hNM : N < M := (by simpa using Nat.mul_le_mul_right N (show 1 ≤ k by omega) : N ≤ k*N).trans_lt hM
  have hval {v : ℕ} (hv : v ∈ A) : (v : ZMod M).val = v :=
    cast_val_of_lt ((Nat.lt_succ_iff.mp (mem_range.mp hv)).trans_lt hNM)
  change (∑ p ∈ U, cyclicTerm M k f p) =
    ∑ d ∈ D, ∑ a ∈ A, ∏ i ∈ range k, f (a+i*d)
  rw [← sum_product D A (fun p => ∏ i ∈ range k, f (p.2+i*p.1))]
  symm
  apply sum_eq_sum_of_injOn_nonzero j
  · rintro ⟨d, a⟩ hp
    obtain ⟨hd, _⟩ := mem_product.mp hp
    obtain ⟨hd', hC⟩ := mem_filter.mp hd
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    change (d : ZMod M).val ≤ N ∧ C (d : ZMod M).val
    rw [hval hd']
    exact ⟨Nat.lt_succ_iff.mp (mem_range.mp hd'), hC⟩
  · rintro ⟨d, a⟩ hd ⟨e, b⟩ he heq
    obtain ⟨hd, ha⟩ := mem_product.mp hd
    obtain ⟨he, hb⟩ := mem_product.mp he
    apply Prod.ext
    · have h := congrArg (fun p : ZMod M × ZMod M => p.2.val) heq
      simpa only [j, hval (mem_filter.mp hd).1, hval (mem_filter.mp he).1] using h
    · have h := congrArg (fun p : ZMod M × ZMod M => p.1.val) heq
      simpa only [j, hval ha, hval hb] using h
  · intro p hp hpne
    have h := (mem_filter.mp hp).2
    have hx := nonzero_vertex f hzero hpne (show 0 < k by omega)
    simp only [Nat.cast_zero, zero_mul, add_zero] at hx
    refine ⟨(p.2.val, p.1.val), mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    · exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_iff.mpr h.1), h.2⟩
    · exact mem_range.mpr (Nat.lt_succ_iff.mpr (mem_Icc.mp hx).2)
    · exact Prod.ext (ZMod.natCast_zmod_val _) (ZMod.natCast_zmod_val _)
  · rintro ⟨d, a⟩ hp
    obtain ⟨hd, ha⟩ := mem_product.mp hp
    have hdN : d ≤ N := Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp hd).1)
    have haN : a ≤ N := Nat.lt_succ_iff.mp (mem_range.mp ha)
    unfold cyclicTerm
    refine prod_congr rfl fun i hi => ?_
    have hi' := mem_range.mp hi
    have hadd : a + i*d ≤ k*N := calc
      _ ≤ N + i*N := Nat.add_le_add haN (Nat.mul_le_mul_left i hdN)
      _ = (i+1)*N := by ring
      _ ≤ _ := Nat.mul_le_mul_right N (by omega)
    change f (a + i*d) = f ((a : ZMod M) + (i : ZMod M)*(d : ZMod M)).val
    rw [← Nat.cast_mul, ← Nat.cast_add, cast_val_of_lt (hadd.trans_lt hM)]

private def reverseAP (M k : ℕ) (p : ZMod M × ZMod M) : ZMod M × ZMod M :=
  (p.1 + ((k-1 : ℕ) : ZMod M)*p.2, -p.2)

private theorem reverseAP_involutive (M k : ℕ) : Function.Involutive (reverseAP M k) := by
  intro p
  apply Prod.ext
  · dsimp [reverseAP]
    ring
  · simp [reverseAP]

private theorem reverse_term (M k : ℕ) (f : ℕ → ℝ) (p : ZMod M × ZMod M) :
    cyclicTerm M k f (reverseAP M k p) = cyclicTerm M k f p := by
  unfold cyclicTerm
  refine prod_bij (fun i _ => k-1-i) ?_ ?_ ?_ ?_
  · intro i hi
    have := mem_range.mp hi
    exact mem_range.mpr (by omega)
  · intro i hi j hj heq
    have := mem_range.mp hi
    have := mem_range.mp hj
    omega
  · intro j hj
    have hj' := mem_range.mp hj
    exact ⟨k-1-j, mem_range.mpr (by omega), by omega⟩
  · intro i hi
    have := mem_range.mp hi
    apply congrArg (fun z : ZMod M => f z.val)
    dsimp [reverseAP]
    rw [Nat.cast_sub (by omega : i ≤ k-1)]
    ring

private theorem small_or_neg_small {M N : ℕ} [NeZero M] {a b : ZMod M}
    (ha : a.val ≤ N) (hb : b.val ≤ N) (hM : N < M) :
    (b-a).val ≤ N ∨ (-(b-a)).val ≤ N := by
  rcases le_total a.val b.val with h | h
  · left
    have he : ((b.val-a.val : ℕ) : ZMod M) = b-a := by
      rw [Nat.cast_sub h, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    rw [← he, cast_val_of_lt (by omega)]
    omega
  · right
    have he : ((a.val-b.val : ℕ) : ZMod M) = -(b-a) := by
      rw [Nat.cast_sub h, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, neg_sub]
    rw [← he, cast_val_of_lt (by omega)]
    omega

private theorem sum_big_steps_eq_pos {M N k : ℕ} [NeZero M]
    (hk : 2 ≤ k) (hM : k*N < M) (f : ℕ → ℝ) (hzero : ∀ n ∉ Icc 1 N, f n = 0) :
    (∑ p ∈ (univ : Finset (ZMod M × ZMod M)).filter (fun p => N < p.2.val),
      cyclicTerm M k f p) =
    ∑ p ∈ (univ : Finset (ZMod M × ZMod M)).filter (fun p => p.2.val ≤ N ∧ 0 < p.2.val),
      cyclicTerm M k f p := by
  have h2M : 2*N < M := (Nat.mul_le_mul_right N hk).trans_lt hM
  have hNM : N < M := by omega
  symm
  apply sum_eq_sum_of_injOn_nonzero (reverseAP M k)
  · intro p hp
    obtain ⟨hN, hpos⟩ := (mem_filter.mp hp).2
    have hne : p.2 ≠ 0 := fun h => by simp [h] at hpos
    let _ : NeZero p.2 := ⟨hne⟩
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    change N < (-p.2).val
    rw [ZMod.val_neg_of_ne_zero]
    omega
  · exact (reverseAP_involutive M k).injective.injOn
  · intro p hp hn
    have hpos : N < p.2.val := (mem_filter.mp hp).2
    have hx := nonzero_vertex f hzero hn (show 0 < k by omega)
    have hy := nonzero_vertex f hzero hn (show 1 < k by omega)
    simp only [Nat.cast_zero, zero_mul, add_zero] at hx
    simp only [Nat.cast_one, one_mul] at hy
    have h := small_or_neg_small (mem_Icc.mp hx).2 (mem_Icc.mp hy).2 hNM
    have he : p.1 + p.2 - p.1 = p.2 := by abel
    rw [he] at h
    have hle := h.resolve_left (not_le.mpr hpos)
    have hne : (-p.2).val ≠ 0 := by
      intro hz
      have hn' : -p.2 = 0 := (ZMod.val_eq_zero _).mp hz
      simp at hn'
      simp [hn'] at hpos
    exact ⟨reverseAP M k p, mem_filter.mpr ⟨mem_univ _, hle, Nat.pos_of_ne_zero hne⟩,
      reverseAP_involutive M k p⟩
  · intro p _
    exact (reverse_term M k f p).symm

/-- The full cyclic count equals twice the forward count minus the stationary progressions. -/
theorem cyclic_count_eq_twice_forward_sub_diagonal {M N k : ℕ} [NeZero M]
    (hk : 2 ≤ k) (hM : k*N < M) (f : ℕ → ℝ) (hzero : ∀ n ∉ Icc 1 N, f n = 0) :
    (∑ x : ZMod M, ∑ d : ZMod M, cyclicTerm M k f (x,d)) =
      2 * forwardCount N k f - ∑ a ∈ range (N+1), (f a)^k := by
  classical
  let T : Finset (ZMod M × ZMod M) := univ
  let D := range (N+1)
  let G (d : ℕ) := ∑ a ∈ range (N+1), ∏ i ∈ range k, f (a+i*d)
  have hSplit := sum_filter_add_sum_filter_not T (fun p : ZMod M × ZMod M => p.2.val ≤ N)
    (cyclicTerm M k f)
  simp only [T, not_le] at hSplit
  have hSmall := sum_small_steps hk hM f hzero (fun _ => True)
  simp only [and_true, filter_true] at hSmall
  rw [← Fintype.sum_prod_type (cyclicTerm M k f), ← hSplit,
    sum_big_steps_eq_pos hk hM f hzero, hSmall,
    sum_small_steps hk hM f hzero (fun d => 0 < d)]
  have hSplitD := sum_filter_add_sum_filter_not D (fun d : ℕ => 0 < d) G
  have hcheck : D.filter (fun d : ℕ => ¬0 < d) = {0} := by
    ext d
    simp only [mem_filter, mem_range, not_lt, nonpos_iff_eq_zero, mem_singleton, D]
    omega
  rw [hcheck, sum_singleton] at hSplitD
  have hdiag : G 0 = ∑ a ∈ range (N+1), (f a)^k := by
    simp [G, prod_const]
  change (∑ d ∈ D, G d) + (∑ d ∈ D.filter (fun d => 0 < d), G d) =
    2 * (∑ d ∈ D, G d) - ∑ a ∈ range (N+1), (f a)^k
  linarith only [hSplitD, hdiag]

end OMA.Erdos3ProgressionCyclicLift

/-
A cube supported on an interval has the same weight in any sufficiently
large cyclic group. Use its base vertex and one-step vertices to give
integer representatives to all increments.
-/

namespace OMA.Erdos3CubeCyclicLift

open Finset OMA.Erdos3ProgressionCyclicLift

noncomputable def cyclicCubeTerm (M r : ℕ) (f : ℕ → ℝ)
    (q : ZMod M × (Fin r → ZMod M)) : ℝ :=
  ∏ ω : Fin r → Bool, f (q.1 + ∑ i : Fin r, if ω i then q.2 i else 0).val

noncomputable def intervalCubeTerm (N r : ℕ) (f : ℕ → ℝ)
    (p : Fin N × (Fin r → Fin N)) : ℝ :=
  let x : ℤ := (p.1.val + 1 : ℕ)
  ∏ ω : Fin r → Bool,
    f (x + ∑ i : Fin r, if ω i then ((p.2 i).val + 1 : ℕ) - x else 0).toNat

private theorem val_natCast_of_lt {M u : ℕ} (hu : u < M) :
    (u : ZMod M).val = u := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt hu]

private theorem val_intCast_of_nonneg {M : ℕ} [NeZero M] {x : ℤ} (h0 : 0 ≤ x) (hM : x < M) :
    (x : ZMod M).val = x.toNat := by
  have h := ZMod.val_intCast (n := M) x
  rw [Int.emod_eq_of_lt h0 hM] at h
  omega

private theorem eval_intCast {M N : ℕ} [NeZero M] (f : ℕ → ℝ)
    (hsupp : ∀ n ∉ Icc 1 N, f n = 0) {x : ℤ}
    (hlo : (N : ℤ) < x + (M : ℤ)) (hhi : x < M) :
    f (x : ZMod M).val = f x.toNat := by
  by_cases hx : 0 ≤ x
  · rw [val_intCast_of_nonneg hx hhi]
  have hexp : (x : ZMod M) = ((x + (M : ℤ) : ℤ) : ZMod M) := by
    push_cast
    simp
  rw [hexp, val_intCast_of_nonneg (by omega) (by omega)]
  have hneg : x.toNat = 0 := by omega
  have hout : (x + (M : ℤ)).toNat ∉ Icc 1 N := by
    intro hm
    have := (mem_Icc.mp hm).2
    omega
  rw [hneg, hsupp 0 (by simp), hsupp _ hout]

private def liftCube (M N r : ℕ) (p : Fin N × (Fin r → Fin N)) :
    ZMod M × (Fin r → ZMod M) :=
  (((p.1.val+1 : ℕ) : ZMod M),
    fun i => (((p.2 i).val+1 : ℕ) : ZMod M) - ((p.1.val+1 : ℕ) : ZMod M))

private theorem liftCube_injective {M N r : ℕ} (hM : N < M) :
    Function.Injective (liftCube M N r) := by
  intro p q h
  have hval' (a : Fin N) : ((a.val+1 : ℕ) : ZMod M).val = a.val+1 :=
    val_natCast_of_lt ((Nat.succ_le_iff.mpr a.isLt).trans_lt hM)
  apply Prod.ext
  · apply Fin.ext
    have h0 := congrArg (fun t : ZMod M × (Fin r → ZMod M) => t.1.val) h
    simpa only [liftCube, hval', Nat.add_left_inj] using h0
  · funext i
    apply Fin.ext
    have hi := congrArg (fun t : ZMod M × (Fin r → ZMod M) => (t.1 + t.2 i).val) h
    have hc (p : Fin N × (Fin r → Fin N)) :
        (liftCube M N r p).1 + (liftCube M N r p).2 i =
          (((p.2 i).val + 1 : ℕ) : ZMod M) := by
      dsimp [liftCube]
      abel
    change ((liftCube M N r p).1 + (liftCube M N r p).2 i).val =
      ((liftCube M N r q).1 + (liftCube M N r q).2 i).val at hi
    rw [hc, hc, hval', hval'] at hi
    omega

private theorem supported_cube_lifts {M N r : ℕ} [NeZero M] (f : ℕ → ℝ)
    (hsupp : ∀ n ∉ Icc 1 N, f n = 0)
    (q : ZMod M × (Fin r → ZMod M)) (hq : cyclicCubeTerm M r f q ≠ 0) :
    ∃ p : Fin N × (Fin r → Fin N), liftCube M N r p = q := by
  have hs (ω : Fin r → Bool) :
      (q.1 + ∑ i : Fin r, if ω i then q.2 i else 0).val ∈ Icc 1 N := by
    by_contra hz
    exact hq (prod_eq_zero (mem_univ ω) (hsupp _ hz))
  have hx : q.1.val ∈ Icc 1 N := by simpa using hs (fun _ => false)
  have hy (i : Fin r) : (q.1 + q.2 i).val ∈ Icc 1 N := by
    simpa [Finset.sum_ite_eq'] using hs (fun j => decide (j = i))
  let p0 : Fin N := ⟨q.1.val - 1, by have h := mem_Icc.mp hx; omega⟩
  let p1 (i : Fin r) : Fin N := ⟨(q.1 + q.2 i).val - 1, by
    have h := mem_Icc.mp (hy i)
    omega⟩
  have h0 : p0.val + 1 = q.1.val := by
    dsimp [p0]
    have h := mem_Icc.mp hx
    omega
  have h1 (i : Fin r) : (p1 i).val + 1 = (q.1 + q.2 i).val := by
    dsimp [p1]
    have h := mem_Icc.mp (hy i)
    omega
  refine ⟨(p0,p1), Prod.ext ?_ (funext fun i => ?_)⟩
  · change ((p0.val + 1 : ℕ) : ZMod M) = q.1
    rw [h0, ZMod.natCast_zmod_val]
  · change (((p1 i).val + 1 : ℕ) : ZMod M) - ((p0.val + 1 : ℕ) : ZMod M) = q.2 i
    rw [h1, h0, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    abel

private theorem summand_lifts {M N r : ℕ} [NeZero M] (hM : (r+1)*N < M)
    (f : ℕ → ℝ) (hsupp : ∀ n ∉ Icc 1 N, f n = 0) (p : Fin N × (Fin r → Fin N)) :
    intervalCubeTerm N r f p = cyclicCubeTerm M r f (liftCube M N r p) := by
  let x : ℤ := (p.1.val + 1 : ℕ)
  let y (i : Fin r) : ℤ := ((p.2 i).val + 1 : ℕ)
  have hx0 : 0 ≤ x := by positivity
  have hxN : x ≤ (N : ℤ) := by dsimp [x]; exact_mod_cast Nat.succ_le_iff.mpr p.1.isLt
  have hy0 (i : Fin r) : 0 ≤ y i := by dsimp [y]; positivity
  have hyN (i : Fin r) : y i ≤ (N : ℤ) := by dsimp [y]; exact_mod_cast Nat.succ_le_iff.mpr (p.2 i).isLt
  have hMr : ((r : ℤ)+1) * N < M := by exact_mod_cast hM
  unfold intervalCubeTerm cyclicCubeTerm
  refine prod_congr rfl fun ω _ => ?_
  let t (i : Fin r) : ℤ := if ω i then y i - x else 0
  let v := x + ∑ i : Fin r, t i
  have hlo (i : Fin r) : -(N : ℤ) ≤ t i := by
    dsimp [t]
    split_ifs
    · linarith [hy0 i]
    · exact neg_nonpos.mpr (by positivity)
  have hhi (i : Fin r) : t i ≤ (N : ℤ) := by
    dsimp [t]
    split_ifs
    · linarith [hyN i]
    · positivity
  have hL : (∑ i : Fin r, -(N : ℤ)) ≤ ∑ i : Fin r, t i :=
    sum_le_sum fun i _ => hlo i
  have hU : (∑ i : Fin r, t i) ≤ ∑ i : Fin r, (N : ℤ) :=
    sum_le_sum fun i _ => hhi i
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_neg] at hL hU
  have vLo : (N : ℤ) < v + (M : ℤ) := by dsimp [v]; nlinarith only [hMr, hL, hx0]
  have vHi : v < (M : ℤ) := by dsimp [v]; nlinarith only [hMr, hU, hxN]
  have hcast : (v : ZMod M) =
      (liftCube M N r p).1 + ∑ i : Fin r, if ω i then (liftCube M N r p).2 i else 0 := by
    dsimp only [v, liftCube]
    push_cast
    have hxc : (x : ZMod M) = (p.1.val : ZMod M) + 1 := by
      dsimp [x]
      push_cast
      rfl
    rw [hxc]
    congr 1
    apply sum_congr rfl
    intro i _
    dsimp [t, x, y]
    split_ifs <;> push_cast <;> rfl
  change f v.toNat = _
  rw [← hcast]
  exact (eval_intCast f hsupp vLo vHi).symm

/-- The unnormalized cube sum is independent of the ambient modulus once the
interval and all possible signed cube vertices fit without wrapping. -/
theorem cyclic_cube_sum_eq_interval {M N r : ℕ} [NeZero M] (hM : (r+1)*N < M)
    (f : ℕ → ℝ) (hsupp : ∀ n ∉ Icc 1 N, f n = 0) :
    (∑ x : ZMod M, ∑ t : Fin r → ZMod M, cyclicCubeTerm M r f (x,t)) =
      ∑ p : Fin N × (Fin r → Fin N), intervalCubeTerm N r f p := by
  classical
  have hNM : N < M := (by simpa using Nat.mul_le_mul_right N (show 1 ≤ r+1 by omega) :
      N ≤ (r+1)*N).trans_lt hM
  rw [← Fintype.sum_prod_type (cyclicCubeTerm M r f)]
  symm
  apply sum_eq_sum_of_injOn_nonzero (liftCube M N r)
  · intros; exact mem_univ _
  · exact (liftCube_injective hNM).injOn
  · intro q _ hq
    obtain ⟨p, hp⟩ := supported_cube_lifts f hsupp q hq
    exact ⟨p, mem_univ _, hp⟩
  · intro p _
    exact summand_lifts hM f hsupp p

/-- All coefficients of size at most k become units in the auxiliary modulus. -/
theorem short_coeff_isUnit (k L i : ℕ) (hi : 0 < i) (hik : i ≤ k) :
    IsUnit (i : ZMod (k.factorial * L + 1)) := by
  rw [ZMod.isUnit_iff_coprime]
  by_cases h1 : i = 1
  · simp [h1]
  have hi1 : 1 < i := by omega
  have hd : i ∣ k.factorial * L := (Nat.dvd_factorial hi hik).trans (dvd_mul_right _ _)
  have hmod : (k.factorial * L + 1) % i = 1 := by
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd, zero_add, Nat.mod_eq_of_lt hi1, Nat.mod_eq_of_lt hi1]
  rw [Nat.Coprime, Nat.gcd_rec, hmod]
  simp

end OMA.Erdos3CubeCyclicLift

/-
Finite normalized averages for generalized von Neumann. The pointwise
bounded Cauchy–Schwarz step follows @skhakim's four-term proof,
https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6175.
-/

namespace OMA.Erdos3FiniteAverages

open Finset

noncomputable def avg {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ x, f x) / (Fintype.card α : ℝ)

section
variable {α β : Type*} [Fintype α] [Fintype β]

theorem avg_congr {f g : α → ℝ} (h : ∀ x, f x = g x) : avg f = avg g :=
  congrArg avg (funext h)

theorem avg_mono {f g : α → ℝ} (h : ∀ x, f x ≤ g x) : avg f ≤ avg g :=
  div_le_div_of_nonneg_right (sum_le_sum (fun i _ => h i)) (Nat.cast_nonneg _)

theorem avg_nonneg {f : α → ℝ} (h : ∀ x, 0 ≤ f x) : 0 ≤ avg f :=
  div_nonneg (sum_nonneg fun x _ => h x) (Nat.cast_nonneg _)

theorem avg_const [Nonempty α] (c : ℝ) : avg (fun _ : α => c) = c := by
  have h : 0 < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
  simp only [avg, sum_const, card_univ, nsmul_eq_mul]
  field_simp

theorem avg_mul_left (c : ℝ) (f : α → ℝ) : avg (fun x => c * f x) = c * avg f := by
  rw [avg, ← Finset.mul_sum, mul_div_assoc]
  rfl

theorem avg_mul_right (c : ℝ) (f : α → ℝ) : avg (fun x => f x * c) = avg f * c := by
  simp only [avg, Finset.sum_mul, div_mul_eq_mul_div]

theorem avg_sub (f g : α → ℝ) : avg (fun x => f x - g x) = avg f - avg g := by
  simp only [avg, sum_sub_distrib, sub_div]

theorem avg_add (f g : α → ℝ) : avg (fun x => f x + g x) = avg f + avg g := by
  simp only [avg, sum_add_distrib, add_div]

theorem avg_comp_equiv (e : α ≃ β) (f : β → ℝ) : avg (fun x => f (e x)) = avg f := by
  unfold avg
  rw [Fintype.card_congr e, e.sum_comp]

theorem avg_comm (f : α → β → ℝ) : avg (fun x => avg (f x)) = avg (fun y => avg (fun x => f x y)) := by
  unfold avg
  simp_rw [Finset.sum_div]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun y _ => sum_congr rfl fun x _ => ?_
  rw [div_div, div_div, mul_comm (Fintype.card β : ℝ)]

theorem avg_prod (f : α × β → ℝ) : avg f = avg (fun x => avg (fun y => f (x,y))) := by
  unfold avg
  rw [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul]
  simp_rw [Finset.sum_div]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  rw [div_div, mul_comm (Fintype.card β : ℝ)]

theorem sq_avg_mul_le_avg_sq [Nonempty α] (g F : α → ℝ) (hg : ∀ x, |g x| ≤ 1) :
    (avg (fun x => g x * F x))^2 ≤ avg (fun x => (F x)^2) := by
  let m : ℝ := Fintype.card α
  have hm : 0 < m := by dsimp [m]; exact_mod_cast Fintype.card_pos
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset α) g F
  have hG : ∑ x : α, (g x)^2 ≤ m := by
    calc
      _ ≤ ∑ _x : α, (1 : ℝ) := by
        refine sum_le_sum fun x _ => ?_
        simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg _) (hg x) 2
      _ = _ := by simp [m]
  have hF : 0 ≤ ∑ x : α, (F x)^2 := sum_nonneg fun _ _ => sq_nonneg _
  have hb := hcs.trans (mul_le_mul_of_nonneg_right hG hF)
  change ((∑ x : α, g x * F x) / m)^2 ≤ (∑ x : α, (F x)^2) / m
  rw [div_pow]
  calc
    _ ≤ m * (∑ x : α, (F x)^2) / m^2 := div_le_div_of_nonneg_right hb (sq_nonneg _)
    _ = _ := by field_simp

theorem sq_avg_le_avg_sq [Nonempty α] (f : α → ℝ) : (avg f)^2 ≤ avg (fun x => (f x)^2) := by
  simpa only [one_mul] using sq_avg_mul_le_avg_sq (fun _ => 1) f (fun _ => by norm_num)

theorem avg_dyadic_pow_le [Nonempty α] (r : ℕ) (f : α → ℝ) :
    (avg f)^(2^r) ≤ avg (fun x => (f x)^(2^r)) := by
  induction r generalizing f with
  | zero => simp
  | succ r ih =>
    rw [pow_succ', pow_mul]
    refine (pow_le_pow_left₀ (sq_nonneg _) (sq_avg_le_avg_sq f) _).trans ?_
    simpa only [pow_mul] using ih (fun x => (f x)^2)

theorem abs_avg_le_avg_abs (f : α → ℝ) : |avg f| ≤ avg (fun x => |f x|) := by
  have h : 0 ≤ (Fintype.card α : ℝ) := by positivity
  simp only [avg, abs_div, abs_of_nonneg h]
  exact div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) h

end

theorem sq_avg_eq_shifted_avg {G : Type*} [Fintype G] [AddGroup G] (f : G → ℝ) :
    (avg f)^2 = avg (fun x => avg (fun h => f x * f (x+h))) := by
  have inner (x : G) : avg (fun h => f x * f (x+h)) = f x * avg f := by
    rw [avg_mul_left]
    congr 1
    exact avg_comp_equiv (Equiv.addLeft x) f
  have hs := avg_congr inner
  rw [hs, avg_mul_right, pow_two]

end OMA.Erdos3FiniteAverages

/-
Iterated real Gowers cube averages, together with the explicit Boolean-cube
formula and the single zero-increment bound used for a diagonal term.
-/

namespace OMA.Erdos3CubeAverages

open Finset OMA.Erdos3FiniteAverages

section
variable {G : Type*} [Fintype G] [AddCommGroup G]

def diff (f : G → ℝ) (h x : G) : ℝ := f x * f (x+h)

noncomputable def cubeMean : ℕ → (G → ℝ) → ℝ
  | 0, f => avg f
  | n+1, f => avg (fun h => cubeMean n (diff f h))

theorem cubeMean_one (f : G → ℝ) : cubeMean 1 f = (avg f)^2 := by
  rw [cubeMean]
  change avg (fun h => avg (fun x => f x * f (x+h))) = (avg f)^2
  rw [← avg_comm (fun x h => f x * f (x+h)), ← sq_avg_eq_shifted_avg]

theorem cubeMean_nonneg (r : ℕ) (hr : 1 ≤ r) (f : G → ℝ) : 0 ≤ cubeMean r f := by
  induction r generalizing f with
  | zero => omega
  | succ r ih =>
    cases r with
    | zero => rw [cubeMean_one]; positivity
    | succ r =>
      rw [cubeMean]
      exact avg_nonneg (fun h => ih (by omega) (diff f h))

theorem avg_pow_le_cubeMean (r : ℕ) (f : G → ℝ) : (avg f)^(2^r) ≤ cubeMean r f := by
  induction r generalizing f with
  | zero => simp [cubeMean]
  | succ r ih =>
    rw [pow_succ', pow_mul, cubeMean]
    have hs : (avg f)^2 = avg (fun h => avg (diff f h)) := by
      rw [sq_avg_eq_shifted_avg]
      exact avg_comm (fun x h => f x * f (x+h))
    rw [hs]
    exact (avg_dyadic_pow_le r _).trans (avg_mono fun h => ih (diff f h))

theorem pow_avg_abs_le_card_mul_cubeMean (r : ℕ) (hr : 2 ≤ r) (f : G → ℝ) :
    (avg (fun x => |f x|))^(2^r) ≤ (Fintype.card G : ℝ) * cubeMean r f := by
  cases r with
  | zero => omega
  | succ r =>
    have hr' : 1 ≤ r := by omega
    have hs := sq_avg_le_avg_sq (fun x => |f x|)
    rw [pow_succ', pow_mul]
    have hS : (avg (fun x => |f x|))^2 ≤ avg (diff f 0) := by
      refine hs.trans_eq (avg_congr fun x => ?_)
      rw [sq_abs]
      simp [diff, pow_two]
    have hT := (pow_le_pow_left₀ (sq_nonneg _) hS (2^r)).trans
      (avg_pow_le_cubeMean r (diff f 0))
    refine hT.trans ?_
    have hm : 0 < (Fintype.card G : ℝ) := by exact_mod_cast Fintype.card_pos
    rw [cubeMean, avg]
    calc
      _ ≤ ∑ h : G, cubeMean r (diff f h) :=
        single_le_sum (fun h _ => cubeMean_nonneg r hr' (diff f h)) (mem_univ (0:G))
      _ = _ := by field_simp

noncomputable def cubeProduct (r : ℕ) (f : G → ℝ) (x : G) (t : Fin r → G) : ℝ :=
  ∏ ω : Fin r → Bool, f (x + ∑ i : Fin r, if ω i then t i else 0)

omit [Fintype G] in
theorem cubeProduct_cons (r : ℕ) (f : G → ℝ) (x a : G) (t : Fin r → G) :
    cubeProduct (r+1) f x (Fin.cons a t) = cubeProduct r (diff f a) x t := by
  let e : Bool × (Fin r → Bool) ≃ (Fin (r+1) → Bool) := Fin.consEquiv (fun _ => Bool)
  let F (ω : Fin (r+1) → Bool) := f (x + ∑ i : Fin (r+1), if ω i then Fin.cons a t i else 0)
  change (∏ ω, F ω) = _
  rw [← Equiv.prod_comp e F, Fintype.prod_prod_type, Fintype.prod_bool]
  unfold cubeProduct
  rw [← prod_mul_distrib]
  refine prod_congr rfl fun ω _ => ?_
  simp [F, e, Fin.sum_univ_succ, diff]
  rw [mul_comm]
  congr 1
  abel_nf

theorem cubeMean_eq_nested_avg (r : ℕ) (f : G → ℝ) :
    cubeMean r f = avg (fun x => avg (fun t : Fin r → G => cubeProduct r f x t)) := by
  induction r generalizing f with
  | zero =>
    rw [cubeMean]
    apply avg_congr
    intro x
    have hc (t : Fin 0 → G) : cubeProduct 0 f x t = f x := by
      simp [cubeProduct]
    rw [avg_congr hc, avg_const]
  | succ r ih =>
    rw [cubeMean]
    simp_rw [ih]
    rw [avg_comm]
    apply avg_congr
    intro x
    let e : G × (Fin r → G) ≃ (Fin (r+1) → G) := Fin.consEquiv (fun _ => G)
    calc
      _ = avg (fun p : G × (Fin r → G) => cubeProduct (r+1) f x (e p)) := by
        rw [avg_prod]
        refine avg_congr (fun h => avg_congr (fun t => ?_))
        exact (cubeProduct_cons r f x h t).symm
      _ = _ := avg_comp_equiv e (cubeProduct (r+1) f x)

theorem cubeMean_eq_raw (r : ℕ) (f : G → ℝ) :
    cubeMean r f =
      (∑ x : G, ∑ t : Fin r → G, ∏ ω : Fin r → Bool,
        f (x + ∑ i : Fin r, if ω i then t i else 0)) / (Fintype.card G : ℝ)^(r+1) := by
  rw [cubeMean_eq_nested_avg]
  simp only [avg, cubeProduct, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow,
    ← sum_div, div_div, pow_succ]

end

end OMA.Erdos3CubeAverages

/-
The generalized von Neumann Cauchy–Schwarz induction for a finite ring.
This generalizes the three explicit rounds in @skhakim's four-term proof,
https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6175.
-/

namespace OMA.Erdos3GeneralGVN

open Finset OMA.Erdos3FiniteAverages OMA.Erdos3CubeAverages

section
variable {R I : Type*} [Fintype R] [CommRing R] [DecidableEq I]

private def mulUnitEquiv (u : Rˣ) : R ≃ R where
  toFun x := (u : R) * x
  invFun x := (↑u⁻¹ : R) * x
  left_inv x := by dsimp only; rw [← mul_assoc, Units.inv_mul, one_mul]
  right_inv x := by dsimp only; rw [← mul_assoc, Units.mul_inv, one_mul]

noncomputable def corr (s : Finset I) (f : R → ℝ) (c : I → R) (g : I → R → ℝ) : ℝ :=
  avg (fun x => avg (fun d => f x * ∏ j ∈ s, g j (x+c j*d)))

private theorem corr_step (s : Finset I) (i : I) (hi : i ∉ s) (f : R → ℝ)
    (c : I → R) (g : I → R → ℝ) (hc : IsUnit (c i)) (hg : ∀ x, |g i x| ≤ 1) :
    let u : Rˣ := -hc.unit
    (corr (insert i s) f c g)^2 ≤ avg (fun a =>
      corr s (diff f a) c (fun j => diff (g j) ((c j-c i)*((↑u⁻¹ : R)*a)))) := by
  intro u
  let Q (y d : R) : ℝ := f (y-c i*d) * ∏ j ∈ s, g j (y+(c j-c i)*d)
  have hQ₁ (x d : R) :
      Q (x+c i*d) d = f x * ∏ j ∈ s, g j (x+c j*d) := by
    have h (j : I) : x+c i*d+(c j-c i)*d = x+c j*d := by ring
    simp only [Q, add_sub_cancel_right, h]
  have hQ₂ (x d e : R) :
      Q (x+c i*d) (d+e) = f (x-c i*e) * ∏ j ∈ s, g j (x+c j*d+(c j-c i)*e) := by
    have h0 : x+c i*d-c i*(d+e) = x-c i*e := by ring
    have hj (j : I) : x+c i*d+(c j-c i)*(d+e) = x+c j*d+(c j-c i)*e := by ring
    simp only [Q, h0, hj]
  have hAlign : corr (insert i s) f c g = avg (fun y => g i y * avg (Q y)) := by
    unfold corr
    rw [avg_comm]
    calc
      _ = avg (fun d => avg (fun y => g i y * Q y d)) := by
        refine avg_congr fun d => ?_
        rw [← avg_comp_equiv (Equiv.addRight (c i*d)) (fun y => g i y * Q y d)]
        refine avg_congr fun x => ?_
        change f x * (∏ j ∈ insert i s, g j (x+c j*d)) =
          g i (x+c i*d) * Q (x+c i*d) d
        rw [hQ₁, prod_insert hi]
        ring
      _ = _ := by
        rw [avg_comm]
        exact avg_congr (fun y => avg_mul_left (g i y) (Q y))
  let P (e x d : R) : ℝ :=
    (f x * f (x-c i*e)) *
      ∏ j ∈ s, g j (x+c j*d) * g j (x+c j*d+(c j-c i)*e)
  have hP (d e : R) : avg (fun y => Q y d * Q y (d+e)) = avg (fun x => P e x d) := by
    rw [← avg_comp_equiv (Equiv.addRight (c i*d)) (fun y => Q y d * Q y (d+e))]
    refine avg_congr fun x => ?_
    change Q (x+c i*d) d * Q (x+c i*d) (d+e) = P e x d
    rw [hQ₁, hQ₂]
    dsimp [P]
    rw [prod_mul_distrib]
    ring
  let Z (y d e : R) := Q y d * Q y (d+e)
  have hSwap : avg (fun y => avg (fun d => avg (Z y d))) =
      avg (fun e => avg (fun d => avg (fun y => Z y d e))) := by
    calc
      _ = avg (fun y => avg (fun e => avg (fun d => Z y d e))) :=
        avg_congr (fun y => avg_comm (Z y))
      _ = avg (fun e => avg (fun y => avg (fun d => Z y d e))) :=
        avg_comm (fun y e => avg (fun d => Z y d e))
      _ = _ := avg_congr (fun e => avg_comm (fun y d => Z y d e))
  have hneg (a : R) : -(c i * ((↑u⁻¹ : R)*a)) = a := by
    have hu : (↑u : R) = -c i := by simp [u]
    calc
      _ = (↑u : R)*((↑u⁻¹ : R)*a) := by rw [hu]; ring
      _ = _ := by rw [← mul_assoc, Units.mul_inv, one_mul]
  rw [hAlign]
  calc
    _ ≤ avg (fun y => (avg (Q y))^2) := sq_avg_mul_le_avg_sq _ _ hg
    _ = avg (fun y => avg (fun d => avg (Z y d))) := by
      refine avg_congr fun y => ?_
      exact sq_avg_eq_shifted_avg (Q y)
    _ = avg (fun e => avg (fun d => avg (fun y => Z y d e))) := hSwap
    _ = avg (fun e => avg (fun d => avg (fun x => P e x d))) :=
      avg_congr (fun e => avg_congr (fun d => hP d e))
    _ = avg (fun e => avg (fun x => avg (fun d => P e x d))) :=
      avg_congr (fun e => avg_comm (fun d x => P e x d))
    _ = _ := by
      rw [← avg_comp_equiv (mulUnitEquiv (u⁻¹)) (fun e => avg (fun x => avg (fun d => P e x d)))]
      refine avg_congr (fun a => avg_congr (fun x => avg_congr (fun d => ?_)))
      change P ((↑u⁻¹ : R)*a) x d = _
      simp only [P, diff, sub_eq_add_neg, hneg]

/-- Remove one affine factor per Cauchy–Schwarz round to bound a multilinear
progression correlation by the cube mean of its distinguished factor. -/
theorem pow_corr_le_box (s : Finset I) (f : R → ℝ) (c : I → R) (g : I → R → ℝ)
    (hc : ∀ j ∈ s, IsUnit (c j)) (hg : ∀ j ∈ s, ∀ x, |g j x| ≤ 1) :
    (corr s f c g)^(2^s.card) ≤ cubeMean s.card f := by
  classical
  induction s using Finset.induction_on generalizing f g with
  | empty => simp [corr, avg_const, cubeMean]
  | insert i s hi ih =>
    let u : Rˣ := -(hc i (mem_insert_self i s)).unit
    let G (a : R) (j : I) := diff (g j) ((c j-c i)*((↑u⁻¹ : R)*a))
    have hstep : (corr (insert i s) f c g)^2 ≤ avg (fun a => corr s (diff f a) c (G a)) :=
      corr_step s i hi f c g (hc i (mem_insert_self i s)) (hg i (mem_insert_self i s))
    have hh (a : R) : (corr s (diff f a) c (G a))^(2^s.card) ≤ cubeMean s.card (diff f a) := by
      refine ih (diff f a) (G a) (fun j hj => hc j (mem_insert_of_mem hj)) ?_
      intro j hj x
      have h := hg j (mem_insert_of_mem hj)
      simp only [G, diff, abs_mul]
      exact mul_le_one₀ (h _) (abs_nonneg _) (h _)
    rw [card_insert_of_notMem hi, pow_succ', pow_mul, cubeMean]
    exact (pow_le_pow_left₀ (sq_nonneg _) hstep _).trans
      ((avg_dyadic_pow_le _ _).trans (avg_mono hh))

theorem pow_abs_corr_le_box (s : Finset I) (hs : s.Nonempty) (f : R → ℝ) (c : I → R) (g : I → R → ℝ)
    (hc : ∀ j ∈ s, IsUnit (c j)) (hg : ∀ j ∈ s, ∀ x, |g j x| ≤ 1) :
    |corr s f c g|^(2^s.card) ≤ cubeMean s.card f := by
  have he : |corr s f c g|^(2^s.card) = (corr s f c g)^(2^s.card) := by
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (card_pos.mpr hs).ne'
    rw [hn, pow_succ', pow_mul, pow_mul, sq_abs]
  rw [he]
  exact pow_corr_le_box s f c g hc hg

end

end OMA.Erdos3GeneralGVN

/-
Apply generalized von Neumann to the telescoping progression count, and
bound the stationary diagonal using the zero-increment cube estimate.
-/

namespace OMA.Erdos3CyclicProgressionEstimate

open Finset OMA.Erdos3FiniteAverages OMA.Erdos3CubeAverages OMA.Erdos3GeneralGVN

section
variable {R : Type*} [Fintype R] [CommRing R]

noncomputable def cyclicMean (k : ℕ) (f : R → ℝ) : ℝ :=
  avg (fun x => avg (fun d => ∏ i ∈ range k, f (x+(i:R)*d)))

private def mixed (f g : R → ℝ) (j i : ℕ) (x : R) : ℝ :=
  if i < j then f x else g x

private noncomputable def partialMean (k j : ℕ) (f g : R → ℝ) : ℝ :=
  avg (fun x => avg (fun d => ∏ i ∈ range k, mixed f g j i (x+(i:R)*d)))

private theorem partialMean_sub (k j : ℕ) (hj : j < k) (f g : R → ℝ) :
    partialMean k (j+1) f g - partialMean k j f g =
      corr ((range k).erase j) (f-g) (fun i => (i:R)-(j:R)) (mixed f g j) := by
  let S := range k
  have hjS : j ∈ S := mem_range.mpr hj
  have point (x d : R) :
      (∏ i ∈ S, mixed f g (j+1) i (x+(i:R)*d)) -
        (∏ i ∈ S, mixed f g j i (x+(i:R)*d)) =
      (f-g) (x+(j:R)*d) * ∏ i ∈ S.erase j, mixed f g j i (x+(i:R)*d) := by
    rw [← prod_erase_mul S (fun i => mixed f g (j+1) i (x+(i:R)*d)) hjS,
      ← prod_erase_mul S (fun i => mixed f g j i (x+(i:R)*d)) hjS]
    have hRest : (∏ i ∈ S.erase j, mixed f g (j+1) i (x+(i:R)*d)) =
        ∏ i ∈ S.erase j, mixed f g j i (x+(i:R)*d) := by
      refine prod_congr rfl fun i hi => ?_
      obtain ⟨hne, _⟩ := mem_erase.mp hi
      by_cases hij : i < j
      · simp [mixed, hij, hij.trans (Nat.lt_succ_self _)]
      · have hshift : ¬i < j+1 := by omega
        simp [mixed, hij, hshift]
    rw [hRest]
    simp only [mixed, if_pos (Nat.lt_succ_self _), if_neg (lt_irrefl _), Pi.sub_apply]
    ring
  have hpre : partialMean k (j+1) f g - partialMean k j f g =
      avg (fun x => avg (fun d =>
        (f-g) (x+(j:R)*d) * ∏ i ∈ S.erase j, mixed f g j i (x+(i:R)*d))) := by
    unfold partialMean
    rw [← avg_sub]
    refine avg_congr fun x => ?_
    rw [← avg_sub]
    exact avg_congr (point x)
  rw [hpre]
  unfold corr
  rw [avg_comm (fun x d => (f-g) (x+(j:R)*d) * ∏ i ∈ S.erase j, mixed f g j i (x+(i:R)*d)),
    avg_comm (fun x d => (f-g) x * ∏ i ∈ S.erase j, mixed f g j i (x+((i:R)-(j:R))*d))]
  refine avg_congr fun d => ?_
  rw [← avg_comp_equiv (Equiv.addRight ((j:R)*d))
      (fun x => (f-g) x * ∏ i ∈ S.erase j, mixed f g j i (x+((i:R)-(j:R))*d))]
  refine avg_congr fun x => ?_
  have hc (i : ℕ) : x+(j:R)*d+((i:R)-(j:R))*d = x+(i:R)*d := by ring
  change (f-g) (x+(j:R)*d) * (∏ i ∈ S.erase j, mixed f g j i (x+(i:R)*d)) =
    (f-g) (x+(j:R)*d) * ∏ i ∈ S.erase j, mixed f g j i (x+(j:R)*d+((i:R)-(j:R))*d)
  simp only [hc]

theorem pow_abs_cyclicMean_sub_le (k : ℕ) (hk : 2 ≤ k) (f g : R → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (hunit : ∀ i < k, ∀ j < k, i ≠ j → IsUnit ((i:R)-(j:R))) :
    |cyclicMean k f - cyclicMean k g|^(2^(k-1)) ≤
      (k:ℝ)^(2^(k-1)) * cubeMean (k-1) (f-g) := by
  let T (j : ℕ) := partialMean k j f g
  have hTf : T k = cyclicMean k f := by
    unfold T partialMean cyclicMean
    refine avg_congr (fun x => avg_congr (fun d => prod_congr rfl fun i hi => ?_))
    simp [mixed, mem_range.mp hi]
  have hTg : T 0 = cyclicMean k g := by simp [T, partialMean, cyclicMean, mixed]
  have telescope (n : ℕ) : (∑ j ∈ range n, (T (j+1)-T j)) = T n-T 0 := by
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ, ih]; ring
  let v (j : ℕ) := |T (j+1)-T j|
  obtain ⟨j, hj, hmax⟩ := exists_max_image (range k) v ⟨0, mem_range.mpr (by omega)⟩
  have hjk := mem_range.mp hj
  have hbound : |cyclicMean k f - cyclicMean k g| ≤ (k:ℝ)*v j := by
    rw [← hTf, ← hTg, ← telescope]
    calc
      _ ≤ ∑ i ∈ range k, v i := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ range k, v j := sum_le_sum hmax
      _ = _ := by simp [nsmul_eq_mul]
  have hv : (v j)^(2^(k-1)) ≤ cubeMean (k-1) (f-g) := by
    let S := (range k).erase j
    have hcard : S.card = k-1 := by simp [S, card_erase_of_mem hj]
    have hS : S.Nonempty := card_pos.mp (by rw [hcard]; omega)
    have hw := pow_abs_corr_le_box S hS (f-g) (fun i => (i:R)-(j:R)) (mixed f g j)
      (fun i hi => hunit i (mem_range.mp (mem_erase.mp hi).2) j hjk (mem_erase.mp hi).1)
      (fun i _ x => by
        unfold mixed
        split_ifs
        · rw [abs_of_nonneg (hf x).1]; exact (hf x).2
        · rw [abs_of_nonneg (hg x).1]; exact (hg x).2)
    rw [hcard] at hw
    simpa only [v, T, partialMean_sub k j hjk f g, S] using hw
  calc
    _ ≤ ((k:ℝ)*v j)^(2^(k-1)) := pow_le_pow_left₀ (abs_nonneg _) hbound _
    _ = (k:ℝ)^(2^(k-1)) * (v j)^(2^(k-1)) := mul_pow ..
    _ ≤ _ := mul_le_mul_of_nonneg_left hv (by positivity)

end

private theorem abs_pow_sub_pow_le {a b : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ 1) (hb : 0 ≤ b) (hb' : b ≤ 1) (k : ℕ) :
    |a^k - b^k| ≤ (k:ℝ)*|a-b| := by
  induction k with
  | zero => simp
  | succ k ih =>
    have he : a^(k+1)-b^(k+1) = (a^k-b^k)*a+b^k*(a-b) := by rw [pow_succ,pow_succ]; ring
    rw [he]
    calc
      _ ≤ |(a^k-b^k)*a|+|b^k*(a-b)| := abs_add_le ..
      _ = |a^k-b^k| * a + b^k * |a-b| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg (pow_nonneg hb _)]
      _ ≤ (k:ℝ) * |a-b| * 1 + 1 * |a-b| :=
        add_le_add (mul_le_mul ih ha' ha (by positivity))
          (mul_le_mul_of_nonneg_right (pow_le_one₀ hb hb') (abs_nonneg _))
      _ = _ := by push_cast; ring

theorem pow_abs_diagonal_sub_le {G : Type*} [Fintype G] [AddCommGroup G]
    (k r : ℕ) (hr : 2 ≤ r) (f g : G → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1) :
    |avg (fun x => (f x)^k) - avg (fun x => (g x)^k)|^(2^r) ≤
      (k:ℝ)^(2^r) * ((Fintype.card G : ℝ) * cubeMean r (f-g)) := by
  have hl : |avg (fun x => (f x)^k) - avg (fun x => (g x)^k)| ≤
      (k:ℝ)*avg (fun x => |(f-g) x|) := by
    rw [← avg_sub, ← avg_mul_left]
    exact (abs_avg_le_avg_abs _).trans (avg_mono fun x =>
      abs_pow_sub_pow_le (hf x).1 (hf x).2 (hg x).1 (hg x).2 k)
  calc
    _ ≤ ((k:ℝ)*avg (fun x => |(f-g) x|))^(2^r) := pow_le_pow_left₀ (abs_nonneg _) hl _
    _ = (k:ℝ)^(2^r) * (avg (fun x => |(f-g) x|))^(2^r) := mul_pow ..
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_avg_abs_le_card_mul_cubeMean r hr (f-g)) (by positivity)

end OMA.Erdos3CyclicProgressionEstimate

/-
The generalized von Neumann estimate for the exact positive-difference
interval count in the Leng–Sah–Sawhney reduction.
-/

namespace OMA.Erdos3ExactProgressionGVN

open Finset OMA.Erdos3FiniteAverages OMA.Erdos3CubeAverages
  OMA.Erdos3CyclicProgressionEstimate OMA.Erdos3ProgressionCyclicLift
  OMA.Erdos3CubeCyclicLift

private theorem diagonal_lift {M N k : ℕ} [NeZero M] (hM : N < M) (hk : 0 < k)
    (f : ℕ → ℝ) (hzero : ∀ n ∉ Icc 1 N, f n = 0) :
    (∑ x : ZMod M, (f x.val)^k) = ∑ a ∈ range (N+1), (f a)^k := by
  symm
  apply sum_eq_sum_of_injOn_nonzero (fun a : ℕ => (a : ZMod M))
  · intros; exact mem_univ _
  · intro a ha b hb h
    have haM : a < M := (Nat.lt_succ_iff.mp (mem_range.mp ha)).trans_lt hM
    have hbM : b < M := (Nat.lt_succ_iff.mp (mem_range.mp hb)).trans_lt hM
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt haM, Nat.mod_eq_of_lt hbM]
      using congrArg ZMod.val h
  · intro z _ hn
    have hz : z.val ∈ Icc 1 N := by
      by_contra hnz
      exact hn (by rw [hzero _ hnz, zero_pow hk.ne'])
    exact ⟨z.val, mem_range.mpr (Nat.lt_succ_iff.mpr (mem_Icc.mp hz).2), ZMod.natCast_zmod_val z⟩
  · intro a ha
    have haM : a < M := (Nat.lt_succ_iff.mp (mem_range.mp ha)).trans_lt hM
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt haM]

private theorem normalized_count_formula {M N k : ℕ} [NeZero M] (hk : 2 ≤ k) (hM : k*N < M)
    (f : ℕ → ℝ) (hzero : ∀ n ∉ Icc 1 N, f n = 0) :
    let F (x : ZMod M) := f x.val
    let D : ℝ := (N:ℝ) + 1
    2 * (forwardCount N k f / D^2) =
      ((M:ℝ)/D)^2 * cyclicMean k F + ((M:ℝ)/D^2) * avg (fun x => (F x)^k) := by
  intro F D
  have hNM : N < M := (by simpa using Nat.mul_le_mul_right N (show 1 ≤ k by omega) :
    N ≤ k*N).trans_lt hM
  have hcyc : cyclicMean k F =
      (∑ x : ZMod M, ∑ d : ZMod M, cyclicTerm M k f (x,d)) / ((M:ℝ)^2) := by
    simp only [cyclicMean, avg, cyclicTerm, F, ZMod.card, ← sum_div, div_div, pow_two]
  have hdiag : avg (fun x => (F x)^k) = (∑ a ∈ range (N+1), (f a)^k) / (M:ℝ) := by
    simp only [avg, F, ZMod.card, diagonal_lift hNM (by omega : 0 < k) f hzero]
  rw [hcyc, hdiag, cyclic_count_eq_twice_forward_sub_diagonal hk hM f hzero]
  have hD : D ≠ 0 := by dsimp [D]; positivity
  have hMr : (M:ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  field_simp
  ring

private theorem normalized_pair_bound (q : ℕ) (hq : 0 < q)
    (m d a k B x y : ℝ) (hm : 0 ≤ m) (hd : 1 ≤ d) (ha : 0 ≤ a) (hk : 0 ≤ k)
    (hcap : m ≤ a*d) (hB : 0 ≤ B)
    (hx : |x|^q ≤ k^q * B) (hy : |y|^q ≤ k^q * (m*B)) :
    |(((m/d)^2 * x + (m/d^2) * y)/2)|^q ≤
      ((a^2)^q * k^q + k^q * a^(q+1)) * B := by
  let X := (m/d)^2*x
  let Y := (m/d^2)*y
  have hd0 : 0 < d := by linarith
  have hr : m/d ≤ a := (div_le_iff₀ hd0).mpr hcap
  have hlambda : m/d^2 ≤ a/d := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hd0) hd0).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hcap hd0.le]
  have hu0 : 0 ≤ 1/d := by positivity
  have hu1 : 1/d ≤ 1 := (div_le_one hd0).mpr hd
  have hu : (1/d)^q ≤ 1/d := by
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
    rw [pow_succ]
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ hu0 hu1) hu0).trans_eq (one_mul _)
  have hmP : (m/d^2)^q * m ≤ a^(q+1) := calc
    _ ≤ (a/d)^q * m := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hlambda q) hm
    _ = a^q * (1/d)^q * m := by rw [div_pow, div_pow, one_pow]; ring
    _ ≤ a^q * (1/d) * m := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu (pow_nonneg ha _)) hm
    _ = a^q * (m/d) := by ring
    _ ≤ a^q * a := mul_le_mul_of_nonneg_left hr (pow_nonneg ha _)
    _ = _ := (pow_succ _ _).symm
  have hX : |X|^q ≤ ((a^2)^q * k^q)*B := by
    dsimp [X]
    rw [abs_mul, abs_of_nonneg (sq_nonneg _), mul_pow]
    calc
      _ ≤ (a^2)^q * (k^q*B) :=
        mul_le_mul (pow_le_pow_left₀ (sq_nonneg _) (pow_le_pow_left₀ (by positivity) hr 2) q)
          hx (pow_nonneg (abs_nonneg _) _) (pow_nonneg (sq_nonneg _) _)
      _ = _ := by ring
  have hY : |Y|^q ≤ (k^q * a^(q+1))*B := by
    dsimp [Y]
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ m/d^2), mul_pow]
    calc
      _ ≤ (m/d^2)^q * (k^q*(m*B)) := mul_le_mul_of_nonneg_left hy (by positivity)
      _ = (k^q*B)*((m/d^2)^q*m) := by ring
      _ ≤ (k^q*B)*a^(q+1) := mul_le_mul_of_nonneg_left hmP (by positivity)
      _ = _ := by ring
  have habs : |(X+Y)/2| ≤ max |X| |Y| := by
    rw [abs_div, abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
    apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    linarith only [abs_add_le X Y, le_max_left |X| |Y|, le_max_right |X| |Y|]
  change |(X+Y)/2|^q ≤ _
  refine (pow_le_pow_left₀ (abs_nonneg _) habs q).trans ?_
  rw [add_mul]
  rcases le_total |X| |Y| with h | h
  · rw [max_eq_right h]
    exact hY.trans (le_add_of_nonneg_left (by positivity))
  · rw [max_eq_left h]
    exact hX.trans (le_add_of_nonneg_right (by positivity))

set_option maxHeartbeats 800000 in
theorem exact_h2 :
    OMA.R_Erdos3_erdos_3_variants_leng_sah_sawhney_R1_H1_R1_H1_R1.H2 := by
  intro k hk
  let r := k-1
  let q := 2^r
  let A : ℝ := (k.factorial:ℝ)*((2:ℝ)^k+1)+1
  have h2k : 2 ≤ k := by omega
  have hr : 2 ≤ r := by dsimp [r]; omega
  have heq : r+1=k := by dsimp [r]; omega
  have hq : 0 < q := by dsimp [q]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hkr : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  refine ⟨(A^2)^q * (k:ℝ)^q + (k:ℝ)^q * A^(q+1), by positivity, ?_⟩
  intro N f g hN hfg hs L r₀ count
  let M := k.factorial * L + 1
  let D : ℝ := (N:ℝ)+1
  have hd : 1 ≤ D := by dsimp [D]; linarith [Nat.cast_nonneg (α := ℝ) N]
  have fzero (n : ℕ) (hn : n ∉ Icc 1 N) : f n = 0 := (hs n hn).1
  have gzero (n : ℕ) (hn : n ∉ Icc 1 N) : g n = 0 := (hs n hn).2
  have dzero (n : ℕ) (hn : n ∉ Icc 1 N) : (f-g) n = 0 := by
    simp only [Pi.sub_apply, fzero n hn, gzero n hn, sub_zero]
  have hWidthL : k*N < L := by
    have h := Nat.mul_le_mul_right N k.lt_two_pow_self.le
    dsimp [L]
    omega
  have hLleM : L ≤ M := by
    have h := Nat.mul_le_mul_right L (Nat.succ_le_iff.mpr (Nat.factorial_pos k))
    dsimp [M]
    simpa using h.trans (Nat.le_succ (k.factorial*L))
  have hWidthM : k*N < M := hWidthL.trans_le hLleM
  have hLcap : (L:ℝ) ≤ ((2:ℝ)^k+1)*D := by
    dsimp [L,D]
    push_cast
    nlinarith only [Nat.cast_nonneg (α := ℝ) N, pow_nonneg (show (0:ℝ) ≤ 2 by norm_num) k]
  have hMcap : (M:ℝ) ≤ A*D := by
    dsimp only [M,A]
    push_cast
    calc
      _ ≤ (k.factorial:ℝ)*(((2:ℝ)^k+1)*D)+D :=
        add_le_add (mul_le_mul_of_nonneg_left hLcap (by positivity)) hd
      _ = _ := by ring
  let F (x : ZMod M) := f x.val
  let G (x : ZMod M) := g x.val
  let U := cubeMean r (fun x : ZMod L => (f-g) x.val)
  have hU0 : 0 ≤ U := cubeMean_nonneg r (by omega) _
  let B := ∑ x : ZMod L, ∑ t : Fin r → ZMod L, cyclicCubeTerm L r (f-g) (x,t)
  have hRawL : U = B / ((L:ℝ)^k) := by
    dsimp only [U]
    rw [cubeMean_eq_raw, ZMod.card, heq]
    rfl
  have hLpos : (0:ℝ) < L := by dsimp [L]; positivity
  have hB0 : 0 ≤ B := by
    rw [hRawL, le_div_iff₀ (pow_pos hLpos _), zero_mul] at hU0
    exact hU0
  have hComp : cubeMean r (F-G) ≤ U := by
    have hLiftM := cyclic_cube_sum_eq_interval (M:=M) (N:=N) (r:=r)
      (by rw [heq]; exact hWidthM) (f-g) dzero
    have hLiftL := cyclic_cube_sum_eq_interval (M:=L) (N:=N) (r:=r)
      (by rw [heq]; exact hWidthL) (f-g) dzero
    rw [cubeMean_eq_raw, ZMod.card, heq, hRawL]
    change (∑ x : ZMod M, ∑ t : Fin r → ZMod M, cyclicCubeTerm M r (f-g) (x,t)) / ((M:ℝ)^k)
      ≤ B / ((L:ℝ)^k)
    rw [hLiftM, ← hLiftL]
    exact div_le_div_of_nonneg_left hB0 (pow_pos hLpos _)
      (pow_le_pow_left₀ hLpos.le (by exact_mod_cast hLleM) k)
  have hUnits (i : ℕ) (hi : i < k) (j : ℕ) (hj : j < k) (hne : i ≠ j) :
      IsUnit ((i : ZMod M)-(j : ZMod M)) := by
    rcases le_total j i with h | h
    · rw [← Nat.cast_sub h]
      exact short_coeff_isUnit k L (i-j) (by omega) (by omega)
    · rw [show (i : ZMod M)-(j : ZMod M) = -((j-i:ℕ):ZMod M) by rw [Nat.cast_sub h, neg_sub]]
      exact (short_coeff_isUnit k L (j-i) (by omega) (by omega)).neg
  let x := cyclicMean k F - cyclicMean k G
  let y := avg (fun z => (F z)^k) - avg (fun z => (G z)^k)
  have hx : |x|^q ≤ (k:ℝ)^q * U :=
    (pow_abs_cyclicMean_sub_le k h2k F G (fun z => (hfg z.val).1) (fun z => (hfg z.val).2) hUnits).trans
      (mul_le_mul_of_nonneg_left hComp (by positivity))
  have hy : |y|^q ≤ (k:ℝ)^q * ((M:ℝ)*U) := by
    have h := pow_abs_diagonal_sub_le k r hr F G (fun z => (hfg z.val).1) (fun z => (hfg z.val).2)
    rw [ZMod.card] at h
    exact h.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hComp (by positivity)) (by positivity))
  have hrel : forwardCount N k f / D^2 - forwardCount N k g / D^2 =
      (((M:ℝ)/D)^2*x + ((M:ℝ)/D^2)*y)/2 := by
    have hf := normalized_count_formula (M:=M) h2k hWidthM f fzero
    have hg := normalized_count_formula (M:=M) h2k hWidthM g gzero
    dsimp only at hf hg
    dsimp only [x,y,D,F,G]
    rw [mul_sub, mul_sub]
    linarith only [hf,hg]
  change |forwardCount N k f / D^2 - forwardCount N k g / D^2|^q ≤
    ((A^2)^q*(k:ℝ)^q + (k:ℝ)^q*A^(q+1)) * (B / ((L:ℝ)^k))
  rw [hrel, ← hRawL]
  exact normalized_pair_bound q hq M D A k U x y (by positivity) hd hA.le hkr.le hMcap hU0 hx hy

end OMA.Erdos3ExactProgressionGVN

theorem OMA.solution : OMA.R_Erdos3_erdos_3_variants_leng_sah_sawhney_R1_H1_R1_H1_R1.H2 :=
  OMA.Erdos3ExactProgressionGVN.exact_h2
