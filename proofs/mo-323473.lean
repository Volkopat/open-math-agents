import OMAStatements.S_mo_323473

/-!
Verified port of @connoranderson's complete companion proof, commit
06cd983bcd972606ad613cf1a7963fbaca5071ab, accompanying statement #26906.
Source: zotachidil, MathOverflow 323473 (CC BY-SA 4.0).
Mikael de la Salle supplied the real four-matrix tensor-product construction
in the source comments. Selecting positive transpose parity gives exactly
the full symmetric dimension; no general-k extremizing family is claimed.
-/
-- uses note #122767
namespace OMA.S_mo_323473
open Matrix Finset Filter
open scoped Matrix.Norms.L2Operator Topology

private abbrev Index (r : ℕ) := Fin r → Fin 2
private abbrev Word (r : ℕ) := Fin r → Fin 4

private def pauli : Fin 4 → Matrix (Fin 2) (Fin 2) ℝ :=
  ![!![1,0;0,1], !![1,0;0,-1], !![0,1;1,0], !![0,1;-1,0]]
private def sign (i : Fin 4) : ℝ := (![1,1,1,-1] : Fin 4 → ℝ) i
private noncomputable def parity {r : ℕ} (w : Word r) : ℝ := ∏ i, sign (w i)
private noncomputable def tensor {r : ℕ} (w : Word r) (x y : Index r) : ℝ :=
  ∏ i, pauli (w i) (x i) (y i)

private lemma ptrans (j : Fin 4) (a b : Fin 2) :
    pauli j b a = sign j * pauli j a b := by
  fin_cases j <;> fin_cases a <;> fin_cases b <;> norm_num [pauli,sign]
private lemma porth (j : Fin 4) (a b : Fin 2) :
    ∑ z, pauli j z a * pauli j z b = if a=b then 1 else 0 := by
  fin_cases j <;> fin_cases a <;> fin_cases b <;> norm_num [Fin.sum_univ_two,pauli]
private lemma pgram (j k : Fin 4) :
    ∑ a, ∑ b, pauli j a b * pauli k a b = if j=k then 2 else 0 := by
  fin_cases j <;> fin_cases k <;> norm_num [Fin.sum_univ_two,pauli]

private lemma tensor_trans {r : ℕ} (w : Word r) (x y : Index r) :
    tensor w y x = parity w * tensor w x y := by
  unfold tensor parity
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => ptrans (w i) (x i) (y i)

private lemma tensor_orth {r : ℕ} (w : Word r) (x y : Index r) :
    (∑ z : Index r, tensor w z x * tensor w z y) = if x=y then 1 else 0 := by
  classical
  simp only [tensor,← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : Fin r) (z : Fin 2) => pauli (w i) z (x i) * pauli (w i) z (y i))]
  rw [Finset.prod_congr rfl (fun i _ => porth (w i) (x i) (y i))]
  simp [Fintype.prod_ite_zero,← funext_iff]

private lemma tensor_gram {r : ℕ} (v w : Word r) :
    (∑ x : Index r, ∑ y : Index r, tensor v x y * tensor w x y) =
      if v=w then (2:ℝ)^r else 0 := by
  classical
  simp only [tensor,← Finset.prod_mul_distrib]
  have inner (x : Index r) := Fintype.prod_sum (fun (i : Fin r) (y : Fin 2) => pauli (v i) (x i) y * pauli (w i) (x i) y)
  simp_rw [← inner]
  rw [← Fintype.prod_sum (fun (i : Fin r) (x : Fin 2) => ∑ y : Fin 2, pauli (v i) x y * pauli (w i) x y)]
  rw [Finset.prod_congr rfl (fun i _ => pgram (v i) (w i))]
  simp [Fintype.prod_ite_zero,← funext_iff]

private lemma parity_sq {r : ℕ} (w : Word r) : parity w ^ 2 = 1 := by
  have hs (j : Fin 4) : sign j ^ 2 = 1 := by fin_cases j <;> norm_num [sign]
  rw [parity,← Finset.prod_pow]
  simp [hs]
private lemma parity_sum (r : ℕ) : (∑ w : Word r, parity w) = (2:ℝ)^r := by
  unfold parity
  rw [← Fintype.prod_sum]
  norm_num [Fin.sum_univ_succ,sign]

private lemma card_positive (r : ℕ) :
    Fintype.card {w : Word r // parity w = 1} = (2^r+1).choose 2 := by
  classical
  have identity (w : Word r) : (if parity w = 1 then (2:ℝ) else 0) = 1 + parity w := by
    rcases sq_eq_one_iff.mp (parity_sq w) with h|h <;> norm_num [h]
  have summed := congrArg (fun f : Word r → ℝ => ∑ w, f w) (funext identity)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Fintype.card_pi,
    Fintype.card_fin,Finset.card_univ,Finset.prod_const,nsmul_eq_mul,mul_one,parity_sum] at summed
  have cardid : (∑ w : Word r, if parity w = 1 then (2:ℝ) else 0) =
      (Fintype.card {w : Word r // parity w = 1} : ℝ)*2 := by
    rw [← Finset.sum_filter,Finset.sum_const]
    simp [Fintype.card_subtype]
  rw [cardid] at summed
  have cardnat : Fintype.card {w : Word r // parity w = 1} * 2 = 4^r+2^r := by
    exact_mod_cast summed
  rw [Nat.choose_two_right]
  have hpow : 4^r = 2^r * 2^r := by rw [← mul_pow]; norm_num
  rw [hpow] at cardnat
  exact Nat.eq_div_of_mul_eq_right (by decide) (by simp; nlinarith)
private theorem cutoff {n k : ℕ} (hn : (k+1).choose 2 < n) (A : Fin n → Mat k)
    (hA : ∀ i, (A i).IsSymm) : (gram A).det = 0 := by
  classical
  let T : Matrix (Fin n) (Fin k × Fin k) ℝ := fun i p => A i p.1 p.2
  let B : Matrix (Fin n) (Sym2 (Fin k)) ℝ := fun i =>
    Sym2.lift ⟨A i, fun a b => (hA i).apply b a⟩
  let C : Matrix (Sym2 (Fin k)) (Fin k × Fin k) ℝ :=
    fun s p => if s = Sym2.mk p.1 p.2 then 1 else 0
  have hT : B * C = T := by
    ext i p
    rw [Matrix.mul_apply]
    simp [B,C,T]
  have hG : gram A = T * T.transpose := by
    ext i j
    rw [Matrix.mul_apply,Fintype.sum_prod_type]
    rfl
  have hr : (gram A).rank ≤ (k+1).choose 2 := calc
    (gram A).rank = (T*T.transpose).rank := congrArg Matrix.rank hG
    _ ≤ T.rank := Matrix.rank_mul_le_left _ _
    _ = (B*C).rank := congrArg Matrix.rank hT.symm
    _ ≤ B.rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card (Sym2 (Fin k)) := B.rank_le_card_width
    _ = _ := by simp [Sym2.card]
  by_contra h
  have := Matrix.rank_of_det_ne_zero h
  simp only [Fintype.card_fin] at this
  omega
private theorem build_family (r n : ℕ) (hn : n ≤ (2^r+1).choose 2) :
    ∃ A : Fin n → Mat (2^r), admissible A ∧ gram A = (2^r : ℝ) • (1 : Mat n) := by
  classical
  let e : Fin (2^r) ≃ Index r := (Fintype.equivFinOfCardEq (by simp : Fintype.card (Index r) = 2^r)).symm
  let pos := {w : Word r // parity w = 1}
  let f : Fin n ↪ pos :=
    (Fin.castLEEmb hn).trans (Fintype.equivFinOfCardEq (card_positive r)).symm.toEmbedding
  let A (i : Fin n) : Mat (2^r) := fun x y => tensor (f i).val (e x) (e y)
  have horth (i : Fin n) : (A i).transpose * A i = 1 := by
    ext x y
    change (∑ z, tensor (f i).val (e z) (e x) * tensor (f i).val (e z) (e y)) = _
    rw [e.sum_comp (fun z => tensor (f i).val z (e x) * tensor (f i).val z (e y)),
      tensor_orth]
    simp [Matrix.one_apply]
  refine ⟨A,fun i => ⟨?_,?_⟩,?_⟩
  · ext x y
    change tensor (f i).val (e y) (e x) = tensor (f i).val (e x) (e y)
    rw [tensor_trans,(f i).property,one_mul]
  · have h : star (A i) * A i = 1 := by simpa [Matrix.star_eq_conjTranspose] using horth i
    have norm := congrArg (fun M : Mat (2^r) => ‖M‖) h
    rw [CStarRing.norm_star_mul_self] at norm
    rw [norm_one] at norm
    nlinarith [norm_nonneg (A i)]
  · ext i j
    change (∑ x, ∑ y, tensor (f i).val (e x) (e y) * tensor (f j).val (e x) (e y)) = _
    have inner (x : Fin (2^r)) := e.sum_comp (fun y => tensor (f i).val (e x) y * tensor (f j).val (e x) y)
    rw [Finset.sum_congr rfl (fun x _ => inner x)]
    rw [e.sum_comp (fun x => ∑ y, tensor (f i).val x y * tensor (f j).val x y),tensor_gram]
    have hinj : (f i).val = (f j).val ↔ i = j :=
      ⟨fun h => f.injective (Subtype.ext h),fun h => by subst j; rfl⟩
    by_cases h : i=j
    · subst j; simp
    · have hne : (f i).val ≠ (f j).val := fun he => h (hinj.mp he)
      simp [hne,h]
end OMA.S_mo_323473

open Set Filter OMA.S_mo_323473 in
theorem OMA.solution : type_of% @OMA.S_mo_323473.main := by
  refine ⟨build_family,fun _ _ => cutoff,fun C F hF => ?_⟩
  obtain ⟨b,hb⟩ := eventually_atTop.1 (hF.eventually_gt_atTop (max C 0))
  obtain ⟨r,hr⟩ := exists_nat_gt b
  let a := 2^r
  have ha : 0 < a := by dsimp [a]; positivity
  have hb' : b ≤ (a:ℝ) := hr.le.trans (by exact_mod_cast (Nat.le_of_lt (Nat.lt_two_pow_self : r < 2^r)))
  have hf := hb (a:ℝ) hb'
  have hf0 : 0 < F (a:ℝ) := lt_of_le_of_lt (le_max_right _ _) hf
  let k := 2^(r+1)
  have hk : k=2*a := by simp [k,a,pow_succ,mul_comm]
  have hk0 : 0 < k := by rw [hk]; positivity
  have hcard : k*a ≤ (k+1).choose 2 := by
    rw [Nat.choose_two_right,hk,Nat.le_div_iff_mul_le (by decide)]
    simp
    nlinarith
  obtain ⟨A,hA,hG⟩ := build_family (r+1) (k*a) hcard
  refine ⟨k,k*a,hk0,by nlinarith only [ha,hk],by nlinarith only [ha,hk],?_,A,hA,?_⟩
  · have hk' : (k:ℝ) ≠ 0 := by exact_mod_cast hk0.ne'
    rw [Nat.cast_mul,mul_div_cancel_left₀ _ hk',div_lt_iff₀ hf0]
    exact mul_comm C (k:ℝ) ▸ mul_lt_mul_of_pos_left
      ((le_max_left _ _).trans_lt hf) (by exact_mod_cast hk0)
  · simpa [k] using hG
