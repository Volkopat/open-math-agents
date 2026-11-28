import OMAStatements.S_arxiv_2012_00808

namespace OMA.P_arxiv_2012_00808

open OMA.S_arxiv_2012_00808 SimpleGraph

/-! ### Part 1: Permutation action, inner product, and transposition operators on `TokenVert` -/

private def permToken {n k : ℕ} (σ : Equiv.Perm (Fin n)) (S : TokenVert (Fin n) k) :
    TokenVert (Fin n) k :=
  ⟨S.val.map σ.toEmbedding, by simp [S.property]⟩

private lemma permToken_one {n k : ℕ} (S : TokenVert (Fin n) k) :
    permToken 1 S = S := by
  ext x
  simp only [permToken, Finset.mem_map, Equiv.coe_toEmbedding, Equiv.Perm.one_apply, exists_eq_right]

private lemma permToken_mul {n k : ℕ} (σ τ : Equiv.Perm (Fin n)) (S : TokenVert (Fin n) k) :
    permToken (σ * τ) S = permToken σ (permToken τ S) := by
  ext x
  simp only [permToken, Finset.mem_map, Equiv.coe_toEmbedding, Equiv.Perm.coe_mul,
    Function.comp_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ⟨τ a, ⟨a, ha, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩; exact ⟨a, ha, rfl⟩

private def permTokenEquiv {n k : ℕ} (σ : Equiv.Perm (Fin n)) :
    TokenVert (Fin n) k ≃ TokenVert (Fin n) k where
  toFun := permToken σ
  invFun := permToken σ⁻¹
  left_inv S := by rw [← permToken_mul, inv_mul_cancel, permToken_one]
  right_inv S := by rw [← permToken_mul, mul_inv_cancel, permToken_one]

private def swapOp {n k : ℕ} (a b : Fin n) (f : TokenVert (Fin n) k → ℝ) :
    TokenVert (Fin n) k → ℝ :=
  fun S => f (permToken (Equiv.swap a b) S)

private def ip {α : Type*} [Fintype α] (f g : α → ℝ) : ℝ :=
  ∑ x : α, f x * g x

private lemma ip_comm {α : Type*} [Fintype α] (f g : α → ℝ) : ip f g = ip g f := by
  unfold ip; congr 1; ext x; ring

private lemma ip_self_nonneg {α : Type*} [Fintype α] (f : α → ℝ) : 0 ≤ ip f f :=
  Finset.sum_nonneg fun x _ => mul_self_nonneg (f x)

private lemma ip_add_left {α : Type*} [Fintype α] (f g h : α → ℝ) :
    ip (fun x => f x + g x) h = ip f h + ip g h := by
  unfold ip; rw [← Finset.sum_add_distrib]; congr 1; ext x; ring

private lemma ip_add_right {α : Type*} [Fintype α] (f g h : α → ℝ) :
    ip f (fun x => g x + h x) = ip f g + ip f h := by
  unfold ip; rw [← Finset.sum_add_distrib]; congr 1; ext x; ring

private lemma ip_sub_left {α : Type*} [Fintype α] (f g h : α → ℝ) :
    ip (fun x => f x - g x) h = ip f h - ip g h := by
  unfold ip; rw [← Finset.sum_sub_distrib]; congr 1; ext x; ring

private lemma ip_sub_right {α : Type*} [Fintype α] (f g h : α → ℝ) :
    ip f (fun x => g x - h x) = ip f g - ip f h := by
  unfold ip; rw [← Finset.sum_sub_distrib]; congr 1; ext x; ring

private lemma ip_smul_left {α : Type*} [Fintype α] (c : ℝ) (f g : α → ℝ) :
    ip (fun x => c * f x) g = c * ip f g := by
  unfold ip; rw [Finset.mul_sum]; congr 1; ext x; ring

private lemma ip_smul_right {α : Type*} [Fintype α] (c : ℝ) (f g : α → ℝ) :
    ip f (fun x => c * g x) = c * ip f g := by
  unfold ip; rw [Finset.mul_sum]; congr 1; ext x; ring

private lemma ip_sum_left {α β : Type*} [Fintype α] (s : Finset β) (F : β → α → ℝ) (g : α → ℝ) :
    ip (fun x => ∑ b ∈ s, F b x) g = ∑ b ∈ s, ip (F b) g := by
  unfold ip
  simp_rw [Finset.sum_mul]
  exact Finset.sum_comm

private lemma ip_sum_right {α β : Type*} [Fintype α] (f : α → ℝ) (s : Finset β) (G : β → α → ℝ) :
    ip f (fun x => ∑ b ∈ s, G b x) = ∑ b ∈ s, ip f (G b) := by
  unfold ip
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

private lemma ip_cauchy_schwarz {α : Type*} [Fintype α] (f g : α → ℝ) :
    (ip f g) ^ 2 ≤ ip f f * ip g g := by
  simpa [ip, sq] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g

private lemma swapOp_self {n k : ℕ} (a : Fin n) (f : TokenVert (Fin n) k → ℝ) :
    swapOp a a f = f := by
  ext S
  simp only [swapOp, Equiv.swap_self]
  congr 1; ext x; simp [permToken]

private lemma swapOp_comm {n k : ℕ} (a b : Fin n) (f : TokenVert (Fin n) k → ℝ) :
    swapOp a b f = swapOp b a f := by
  ext S; simp [swapOp, Equiv.swap_comm]

private lemma swapOp_invol {n k : ℕ} (a b : Fin n) (f : TokenVert (Fin n) k → ℝ) :
    swapOp a b (swapOp a b f) = f := by
  ext S
  simp only [swapOp, ← permToken_mul, Equiv.swap_mul_self, permToken_one]

private lemma ip_swapOp_left {n k : ℕ} (a b : Fin n) (f g : TokenVert (Fin n) k → ℝ) :
    ip (swapOp a b f) g = ip f (swapOp a b g) := by
  unfold ip swapOp
  rw [← Equiv.sum_comp (permTokenEquiv (Equiv.swap a b)) (fun S => f S * g (permToken (Equiv.swap a b) S))]
  congr 1; ext S
  simp only [permTokenEquiv, Equiv.coe_fn_mk, ← permToken_mul, Equiv.swap_mul_self, permToken_one]

private lemma ip_swapOp_self_norm {n k : ℕ} (a b : Fin n) (f : TokenVert (Fin n) k → ℝ) :
    ip (swapOp a b f) (swapOp a b f) = ip f f := by
  rw [ip_swapOp_left, swapOp_invol]

private lemma sum_sq_sub_swapOp {n k : ℕ} (a b : Fin n) (f : TokenVert (Fin n) k → ℝ) :
    ∑ S : TokenVert (Fin n) k, (f S - swapOp a b f S) ^ 2 =
      2 * (ip f f - ip f (swapOp a b f)) := by
  have h1 : ∀ S : TokenVert (Fin n) k,
      (f S - swapOp a b f S) ^ 2 = f S * f S + swapOp a b f S * swapOp a b f S - 2 * (f S * swapOp a b f S) := by
    intro S; ring
  simp_rw [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have h2 : ∑ S : TokenVert (Fin n) k, swapOp a b f S * swapOp a b f S = ip f f :=
    ip_swapOp_self_norm a b f
  unfold ip at h2 ⊢
  linarith

/-! ### Part 2: Cesi's `M_{ab}` operator and exact `Fin 4` / `Fin 5` SOS inequalities -/

private def Mop {n k : ℕ} (z a b : Fin n) (f : TokenVert (Fin n) k → ℝ) :
    TokenVert (Fin n) k → ℝ :=
  fun S => swapOp a z f S + swapOp b z f S - swapOp a b f S

private lemma Mop_comm {n k : ℕ} (z a b : Fin n) (f : TokenVert (Fin n) k → ℝ) :
    Mop z a b f = Mop z b a f := by
  ext S; simp only [Mop, swapOp_comm a b]; ring

private lemma ip_Mop_left {n k : ℕ} (z a b : Fin n) (f g : TokenVert (Fin n) k → ℝ) :
    ip (Mop z a b f) g = ip f (Mop z a b g) := by
  unfold Mop
  rw [ip_sub_left, ip_add_left, ip_sub_right, ip_add_right,
      ip_swapOp_left, ip_swapOp_left, ip_swapOp_left]

-- Elementary triangle identity: swap(a,z) * swap(b,z) = swap(a,b) * swap(a,z) for distinct z,a,b!
private lemma swap_triangle_1 {n : ℕ} {z a b : Fin n} (hza : z ≠ a) (hzb : z ≠ b) (hab : a ≠ b) :
    Equiv.swap a z * Equiv.swap b z = Equiv.swap a b * Equiv.swap a z := by
  ext x
  simp only [Equiv.Perm.coe_mul, Function.comp_apply]
  by_cases h1 : x = z
  · subst h1
    rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hab.symm hzb.symm,
        Equiv.swap_apply_right, Equiv.swap_apply_left]
  by_cases h2 : x = a
  · subst h2
    rw [Equiv.swap_apply_of_ne_of_ne hab hza.symm, Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne hza hzb]
  by_cases h3 : x = b
  · subst h3
    rw [Equiv.swap_apply_left, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne hab.symm hzb.symm, Equiv.swap_apply_right]
  rw [Equiv.swap_apply_of_ne_of_ne h3 h1, Equiv.swap_apply_of_ne_of_ne h2 h1,
      Equiv.swap_apply_of_ne_of_ne h2 h3]

private lemma ip_swap_Mop_cancel {n k : ℕ} {z a b : Fin n}
    (hza : z ≠ a) (hzb : z ≠ b) (hab : a ≠ b) (f : TokenVert (Fin n) k → ℝ) :
    ip (swapOp a z f) (Mop z a b f) = ip f f := by
  unfold Mop
  rw [ip_sub_right, ip_add_right, ip_swapOp_self_norm]
  have hcancel : ip (swapOp a z f) (swapOp b z f) = ip (swapOp a z f) (swapOp a b f) := by
    rw [ip_swapOp_left, ip_swapOp_left]
    have hinv_eq : (Equiv.swap b z * Equiv.swap a z)⁻¹ = Equiv.swap a b * Equiv.swap a z := by
      rw [mul_inv_rev, Equiv.swap_inv, Equiv.swap_inv, swap_triangle_1 hza hzb hab]
    unfold ip swapOp
    simp_rw [← permToken_mul]
    have h1 := Equiv.sum_comp (permTokenEquiv (Equiv.swap b z * Equiv.swap a z))
      (fun S => f S * f (permToken (Equiv.swap a b * Equiv.swap a z) S))
    rw [← h1]
    congr 1; ext S
    simp only [permTokenEquiv, Equiv.coe_fn_mk, ← permToken_mul]
    rw [← hinv_eq, inv_mul_cancel, permToken_one, mul_comm]
  linarith

private lemma ip_Mop_self_plus_cross {n k : ℕ} {z a b : Fin n}
    (hza : z ≠ a) (hzb : z ≠ b) (hab : a ≠ b) (f : TokenVert (Fin n) k → ℝ) :
    2 * ip (swapOp a z f) (swapOp b z f) + ip (Mop z a b f) (Mop z a b f) = 3 * ip f f := by
  have hM : Mop z a b f = fun S => swapOp a z f S + swapOp b z f S - swapOp a b f S := rfl
  have h1 : ip (Mop z a b f) (Mop z a b f) =
      ip (swapOp a z f) (Mop z a b f) + ip (swapOp b z f) (Mop z a b f) -
        ip (swapOp a b f) (Mop z a b f) := by
    rw [hM, ip_sub_left, ip_add_left]
  have ha := ip_swap_Mop_cancel hza hzb hab f
  have hb : ip (swapOp b z f) (Mop z a b f) = ip f f := by
    rw [Mop_comm z a b]; exact ip_swap_Mop_cancel hzb hza hab.symm f
  have hab_M : ip (swapOp a b f) (Mop z a b f) =
      2 * ip (swapOp a z f) (swapOp b z f) - ip f f := by
    unfold Mop
    rw [ip_sub_right, ip_add_right, ip_swapOp_self_norm]
    have h_ab_az : ip (swapOp a b f) (swapOp a z f) = ip (swapOp a z f) (swapOp b z f) := by
      have hc : ip (swapOp a z f) (swapOp b z f) = ip (swapOp a z f) (swapOp a b f) := by
        have h := ip_swap_Mop_cancel hza hzb hab f
        unfold Mop at h
        rw [ip_sub_right, ip_add_right, ip_swapOp_self_norm] at h
        linarith
      rw [ip_comm, hc]
    have h_ab_bz : ip (swapOp a b f) (swapOp b z f) = ip (swapOp a z f) (swapOp b z f) := by
      rw [swapOp_comm a b]
      have h := ip_swap_Mop_cancel hzb hza hab.symm f
      unfold Mop at h
      rw [ip_sub_right, ip_add_right, ip_swapOp_self_norm] at h
      rw [ip_comm (swapOp b a f) (swapOp b z f), ip_comm (swapOp a z f) (swapOp b z f)]
      linarith
    linarith
  linarith

/-! ### Part 2B: Exact `Fin 4` and `Fin 5` fiber SOS lemmas -/

private lemma fin4_B3_nonneg (m : ℕ) (g : TokenVert (Fin 4) m → ℝ) :
    0 ≤ 4 * ip g g -
      (2 * ip (swapOp 1 0 g) (Mop 0 2 3 g) + 2 * ip (Mop 0 1 2 g) (Mop 0 1 3 g)) := by
  by_cases hm : m ≤ 4
  · interval_cases m
    · -- m = 0: unique element ∅
      have h1 : ∀ S : TokenVert (Fin 4) 0, S = ⟨∅, Finset.card_empty⟩ := fun S =>
        Subtype.ext (Finset.card_eq_zero.mp S.property)
      have huniq : (Finset.univ : Finset (TokenVert (Fin 4) 0)) = {⟨∅, Finset.card_empty⟩} := by
        ext S; simp [h1 S]
      unfold ip Mop swapOp
      rw [huniq]
      simp only [Finset.sum_singleton]
      have hfix : ∀ σ : Equiv.Perm (Fin 4), permToken σ ⟨∅, Finset.card_empty⟩ = ⟨∅, Finset.card_empty⟩ := fun σ =>
        Subtype.ext (by simp [permToken])
      simp only [hfix]
      exact le_of_eq (by ring)
    · -- m = 1: 4 singletons
      let v : Fin 4 → TokenVert (Fin 4) 1 := fun i => ⟨{i}, Finset.card_singleton i⟩
      have hbij : Function.Bijective v := by
        refine ⟨fun i j h => ?_, fun S => ?_⟩
        · have := congrArg Subtype.val h
          exact Finset.singleton_injective this
        · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp S.property
          exact ⟨i, Subtype.ext hi.symm⟩
      have hsum : ∀ F : TokenVert (Fin 4) 1 → ℝ, (∑ S, F S) = ∑ i : Fin 4, F (v i) :=
        fun F => (Equiv.sum_comp (Equiv.ofBijective v hbij) F).symm
      have hperm : ∀ (a b i : Fin 4), permToken (Equiv.swap a b) (v i) = v (Equiv.swap a b i) := by
        intro a b i; ext x; simp [permToken, v]
      have hsw : ∀ (a b i : Fin 4), Equiv.swap a b i = if i = a then b else if i = b then a else i :=
        fun a b i => Equiv.swap_apply_def a b i
      unfold ip Mop swapOp
      simp_rw [hsum, hperm, Fin.sum_univ_four]
      simp only [hsw, Fin.isValue, Fin.reduceEq, ↓reduceIte]
      exact le_of_eq (by ring)
    · -- m = 2: 6 pairs, exact 3-square SOS!
      let pairs : Fin 6 → Finset (Fin 4) :=
        ![{0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}, {2, 3}]
      let v : Fin 6 → TokenVert (Fin 4) 2 := fun i => ⟨pairs i, by fin_cases i <;> decide⟩
      have hv_univ : (Finset.univ : Finset (TokenVert (Fin 4) 2)) =
          ([v 0, v 1, v 2, v 3, v 4, v 5] : List _).toFinset := by
        ext ⟨S, hS⟩
        simp only [Finset.mem_univ, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false,
          true_iff]
        obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hS
        fin_cases a <;> fin_cases b <;> simp_all [v, pairs] <;> decide
      have hnodup : ([v 0, v 1, v 2, v 3, v 4, v 5] : List (TokenVert (Fin 4) 2)).Nodup := by
        decide
      have hsum : ∀ F : TokenVert (Fin 4) 2 → ℝ,
          (∑ S, F S) = F (v 0) + F (v 1) + F (v 2) + F (v 3) + F (v 4) + F (v 5) := by
        intro F
        rw [hv_univ, List.sum_toFinset _ hnodup]
        simp [add_assoc]
      have h10 : ∀ i : Fin 6, permToken (Equiv.swap 1 0) (v i) = v (![0, 3, 4, 1, 2, 5] i) := by
        intro i; fin_cases i <;> decide
      have h20 : ∀ i : Fin 6, permToken (Equiv.swap 2 0) (v i) = v (![3, 1, 5, 0, 4, 2] i) := by
        intro i; fin_cases i <;> decide
      have h30 : ∀ i : Fin 6, permToken (Equiv.swap 3 0) (v i) = v (![4, 5, 2, 3, 0, 1] i) := by
        intro i; fin_cases i <;> decide
      have h12 : ∀ i : Fin 6, permToken (Equiv.swap 1 2) (v i) = v (![1, 0, 2, 3, 5, 4] i) := by
        intro i; fin_cases i <;> decide
      have h13 : ∀ i : Fin 6, permToken (Equiv.swap 1 3) (v i) = v (![2, 1, 0, 5, 4, 3] i) := by
        intro i; fin_cases i <;> decide
      have h23 : ∀ i : Fin 6, permToken (Equiv.swap 2 3) (v i) = v (![0, 2, 1, 4, 3, 5] i) := by
        intro i; fin_cases i <;> decide
      unfold ip Mop swapOp
      simp only [hsum, h10, h20, h30, h12, h13, h23, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val]
      set x0 := g (v 0); set x1 := g (v 1); set x2 := g (v 2)
      set x3 := g (v 3); set x4 := g (v 4); set x5 := g (v 5)
      have hsos :
          4 * (x0 * x0 + x1 * x1 + x2 * x2 + x3 * x3 + x4 * x4 + x5 * x5) -
            (2 * (x0 * (x3 + x4 - x0) + x3 * (x1 + x5 - x2) + x4 * (x5 + x2 - x1) +
                  x1 * (x0 + x3 - x4) + x2 * (x4 + x0 - x3) + x5 * (x2 + x1 - x5)) +
             2 * ((x0 + x3 - x1) * (x0 + x4 - x2) + (x3 + x1 - x0) * (x3 + x5 - x1) +
                  (x4 + x5 - x2) * (x4 + x2 - x0) + (x1 + x0 - x3) * (x1 + x3 - x5) +
                  (x2 + x4 - x5) * (x2 + x0 - x4) + (x5 + x2 - x4) * (x5 + x1 - x3))) =
          2 * ((x0 + x5 - x1 - x4) ^ 2 + (x1 + x4 - x2 - x3) ^ 2 + (x2 + x3 - x0 - x5) ^ 2) := by
        ring
      rw [hsos]
      positivity
    · -- m = 3: 4 triples (complement of m = 1)
      let v : Fin 4 → TokenVert (Fin 4) 3 := fun i =>
        ⟨Finset.univ.erase i, by rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]⟩
      have hbij : Function.Bijective v := by
        refine ⟨fun i j h => ?_, fun S => ?_⟩
        · have heq : Finset.univ.erase i = Finset.univ.erase j := congrArg Subtype.val h
          by_contra hne
          have : i ∈ Finset.univ.erase j := Finset.mem_erase.mpr ⟨hne, Finset.mem_univ i⟩
          rw [← heq] at this
          exact (Finset.mem_erase.mp this).1 rfl
        · have hcompl : S.valᶜ.card = 1 := by
            rw [Finset.card_compl, Fintype.card_fin, S.property]
          obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcompl
          refine ⟨i, Subtype.ext ?_⟩
          ext x
          have : x ∈ S.valᶜ ↔ x = i := by rw [hi, Finset.mem_singleton]
          simp only [Finset.mem_compl] at this
          simp only [v, Finset.mem_erase, Finset.mem_univ, and_true]
          tauto
      have hsum : ∀ F : TokenVert (Fin 4) 3 → ℝ, (∑ S, F S) = ∑ i : Fin 4, F (v i) :=
        fun F => (Equiv.sum_comp (Equiv.ofBijective v hbij) F).symm
      have hperm : ∀ (a b i : Fin 4), permToken (Equiv.swap a b) (v i) = v (Equiv.swap a b i) := by
        intro a b i
        ext x
        simp only [permToken, v, Finset.mem_map, Equiv.coe_toEmbedding, Finset.mem_erase,
          Finset.mem_univ, and_true]
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact fun h => hy ((Equiv.swap a b).injective h)
        · intro hx
          refine ⟨Equiv.swap a b x, ?_, by simp⟩
          intro h; apply hx; rw [← h]; simp
      have hsw : ∀ (a b i : Fin 4), Equiv.swap a b i = if i = a then b else if i = b then a else i :=
        fun a b i => Equiv.swap_apply_def a b i
      unfold ip Mop swapOp
      simp_rw [hsum, hperm, Fin.sum_univ_four]
      simp only [hsw, Fin.isValue, Fin.reduceEq, ↓reduceIte]
      exact le_of_eq (by ring)
    · -- m = 4: unique element univ
      let u : TokenVert (Fin 4) 4 := ⟨Finset.univ, by decide⟩
      have h1 : ∀ S : TokenVert (Fin 4) 4, S = u := fun S =>
        Subtype.ext (Finset.eq_univ_of_card S.val (by simpa using S.property))
      have huniq : (Finset.univ : Finset (TokenVert (Fin 4) 4)) = {u} := by
        ext S; simp [h1 S]
      unfold ip Mop swapOp
      rw [huniq]
      simp only [Finset.sum_singleton]
      have hfix : ∀ σ : Equiv.Perm (Fin 4), permToken σ u = u :=
        fun σ => Subtype.ext (Finset.eq_univ_of_card _ (by simp [permToken, u]))
      simp only [hfix]
      exact le_of_eq (by ring)
  · -- m > 4: TokenVert (Fin 4) m is empty!
    have hempty : IsEmpty (TokenVert (Fin 4) m) := ⟨fun S => by
      have := Finset.card_le_univ S.val
      simp [S.property] at this; omega⟩
    unfold ip
    simp [Finset.univ_eq_empty]

private lemma fin5_B4_sos (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : ℝ) :
    6 * (x0 * x0 + x1 * x1 + x2 * x2 + x3 * x3 + x4 * x4 +
         x5 * x5 + x6 * x6 + x7 * x7 + x8 * x8 + x9 * x9) -
      (2 * ((x0 + x4 - x1) * (x5 + x6 - x0) + (x4 + x1 - x0) * (x7 + x8 - x1) +
            (x5 + x7 - x2) * (x2 + x9 - x3) + (x6 + x8 - x3) * (x9 + x3 - x2) +
            (x1 + x0 - x4) * (x4 + x4 - x4) + (x2 + x5 - x7) * (x0 + x5 - x6) +
            (x3 + x6 - x8) * (x6 + x0 - x5) + (x7 + x2 - x5) * (x1 + x7 - x8) +
            (x8 + x3 - x6) * (x8 + x1 - x7) + (x9 + x9 - x9) * (x3 + x2 - x9)) +
       2 * ((x0 + x5 - x2) * (x4 + x6 - x0) + (x4 + x7 - x1) * (x1 + x8 - x3) +
            (x5 + x2 - x0) * (x7 + x9 - x2) + (x6 + x9 - x3) * (x8 + x3 - x1) +
            (x1 + x4 - x7) * (x0 + x4 - x6) + (x2 + x0 - x5) * (x5 + x5 - x5) +
            (x3 + x6 - x9) * (x6 + x0 - x4) + (x7 + x1 - x4) * (x2 + x7 - x9) +
            (x8 + x8 - x8) * (x3 + x1 - x8) + (x9 + x3 - x6) * (x9 + x2 - x7)) +
       2 * ((x0 + x6 - x3) * (x4 + x5 - x0) + (x4 + x8 - x1) * (x1 + x7 - x2) +
            (x5 + x9 - x2) * (x7 + x2 - x1) + (x6 + x3 - x0) * (x8 + x9 - x3) +
            (x1 + x4 - x8) * (x0 + x4 - x5) + (x2 + x5 - x9) * (x5 + x0 - x4) +
            (x3 + x0 - x6) * (x6 + x6 - x6) + (x7 + x7 - x7) * (x2 + x1 - x7) +
            (x8 + x1 - x4) * (x3 + x8 - x9) + (x9 + x2 - x5) * (x9 + x3 - x8))) =
    4 * ((x4 - x9 - x0 - x1 + x2 + x3) ^ 2 +
         (x5 - x8 - x0 + x1 - x2 + x3) ^ 2 +
         (x6 - x7 - x0 + x1 + x2 - x3) ^ 2) := by
  ring

private lemma permToken_swap_pair {n : ℕ} (a b p q : Fin n) (hpq : p ≠ q) :
    permToken (Equiv.swap a b) ⟨{p, q}, Finset.card_pair hpq⟩ =
      ⟨{Equiv.swap a b p, Equiv.swap a b q}, Finset.card_pair ((Equiv.swap a b).injective.ne hpq)⟩ := by
  ext x; simp [permToken]

private lemma fin5_B4_nonneg_m2 (h : TokenVert (Fin 5) 2 → ℝ) :
    0 ≤ 6 * ip h h -
      (2 * ip (Mop 0 1 2 h) (Mop 0 3 4 h) +
       2 * ip (Mop 0 1 3 h) (Mop 0 2 4 h) +
       2 * ip (Mop 0 1 4 h) (Mop 0 2 3 h)) := by
  let v0 : TokenVert (Fin 5) 2 := ⟨{0, 1}, by decide⟩
  let v1 : TokenVert (Fin 5) 2 := ⟨{0, 2}, by decide⟩
  let v2 : TokenVert (Fin 5) 2 := ⟨{0, 3}, by decide⟩
  let v3 : TokenVert (Fin 5) 2 := ⟨{0, 4}, by decide⟩
  let v4 : TokenVert (Fin 5) 2 := ⟨{1, 2}, by decide⟩
  let v5 : TokenVert (Fin 5) 2 := ⟨{1, 3}, by decide⟩
  let v6 : TokenVert (Fin 5) 2 := ⟨{1, 4}, by decide⟩
  let v7 : TokenVert (Fin 5) 2 := ⟨{2, 3}, by decide⟩
  let v8 : TokenVert (Fin 5) 2 := ⟨{2, 4}, by decide⟩
  let v9 : TokenVert (Fin 5) 2 := ⟨{3, 4}, by decide⟩
  have hv_univ : (Finset.univ : Finset (TokenVert (Fin 5) 2)) =
      ([v0, v1, v2, v3, v4, v5, v6, v7, v8, v9] : List _).toFinset := by
    ext ⟨S, hS⟩
    simp only [Finset.mem_univ, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false,
      true_iff]
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hS
    fin_cases a <;> fin_cases b <;> simp_all [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9] <;> decide
  have hnodup : ([v0, v1, v2, v3, v4, v5, v6, v7, v8, v9] : List _).Nodup := by
    decide
  have hsum : ∀ F : TokenVert (Fin 5) 2 → ℝ,
      (∑ S, F S) = F v0 + F v1 + F v2 + F v3 + F v4 +
                   F v5 + F v6 + F v7 + F v8 + F v9 := by
    intro F
    rw [hv_univ, List.sum_toFinset _ hnodup]
    simp [add_assoc]
  have hsw : ∀ (a b p q : Fin 5) (hpq : p ≠ q) (r s : Fin 5) (hrs : r ≠ s),
      ({(if p = a then b else if p = b then a else p),
        (if q = a then b else if q = b then a else q)} : Finset (Fin 5)) = {r, s} →
      permToken (Equiv.swap a b) ⟨{p, q}, Finset.card_pair hpq⟩ = ⟨{r, s}, Finset.card_pair hrs⟩ := by
    intro a b p q hpq r s hrs heq
    rw [permToken_swap_pair a b p q hpq]
    apply Subtype.ext
    simpa only [Equiv.swap_apply_def] using heq
  have h10_0 : permToken (Equiv.swap 1 0) v0 = v0 := hsw 1 0 0 1 (by decide) 0 1 (by decide) (by decide)
  have h10_1 : permToken (Equiv.swap 1 0) v1 = v4 := hsw 1 0 0 2 (by decide) 1 2 (by decide) (by decide)
  have h10_2 : permToken (Equiv.swap 1 0) v2 = v5 := hsw 1 0 0 3 (by decide) 1 3 (by decide) (by decide)
  have h10_3 : permToken (Equiv.swap 1 0) v3 = v6 := hsw 1 0 0 4 (by decide) 1 4 (by decide) (by decide)
  have h10_4 : permToken (Equiv.swap 1 0) v4 = v1 := hsw 1 0 1 2 (by decide) 0 2 (by decide) (by decide)
  have h10_5 : permToken (Equiv.swap 1 0) v5 = v2 := hsw 1 0 1 3 (by decide) 0 3 (by decide) (by decide)
  have h10_6 : permToken (Equiv.swap 1 0) v6 = v3 := hsw 1 0 1 4 (by decide) 0 4 (by decide) (by decide)
  have h10_7 : permToken (Equiv.swap 1 0) v7 = v7 := hsw 1 0 2 3 (by decide) 2 3 (by decide) (by decide)
  have h10_8 : permToken (Equiv.swap 1 0) v8 = v8 := hsw 1 0 2 4 (by decide) 2 4 (by decide) (by decide)
  have h10_9 : permToken (Equiv.swap 1 0) v9 = v9 := hsw 1 0 3 4 (by decide) 3 4 (by decide) (by decide)
  have h20_0 : permToken (Equiv.swap 2 0) v0 = v4 := hsw 2 0 0 1 (by decide) 1 2 (by decide) (by decide)
  have h20_1 : permToken (Equiv.swap 2 0) v1 = v1 := hsw 2 0 0 2 (by decide) 0 2 (by decide) (by decide)
  have h20_2 : permToken (Equiv.swap 2 0) v2 = v7 := hsw 2 0 0 3 (by decide) 2 3 (by decide) (by decide)
  have h20_3 : permToken (Equiv.swap 2 0) v3 = v8 := hsw 2 0 0 4 (by decide) 2 4 (by decide) (by decide)
  have h20_4 : permToken (Equiv.swap 2 0) v4 = v0 := hsw 2 0 1 2 (by decide) 0 1 (by decide) (by decide)
  have h20_5 : permToken (Equiv.swap 2 0) v5 = v5 := hsw 2 0 1 3 (by decide) 1 3 (by decide) (by decide)
  have h20_6 : permToken (Equiv.swap 2 0) v6 = v6 := hsw 2 0 1 4 (by decide) 1 4 (by decide) (by decide)
  have h20_7 : permToken (Equiv.swap 2 0) v7 = v2 := hsw 2 0 2 3 (by decide) 0 3 (by decide) (by decide)
  have h20_8 : permToken (Equiv.swap 2 0) v8 = v3 := hsw 2 0 2 4 (by decide) 0 4 (by decide) (by decide)
  have h20_9 : permToken (Equiv.swap 2 0) v9 = v9 := hsw 2 0 3 4 (by decide) 3 4 (by decide) (by decide)
  have h30_0 : permToken (Equiv.swap 3 0) v0 = v5 := hsw 3 0 0 1 (by decide) 1 3 (by decide) (by decide)
  have h30_1 : permToken (Equiv.swap 3 0) v1 = v7 := hsw 3 0 0 2 (by decide) 2 3 (by decide) (by decide)
  have h30_2 : permToken (Equiv.swap 3 0) v2 = v2 := hsw 3 0 0 3 (by decide) 0 3 (by decide) (by decide)
  have h30_3 : permToken (Equiv.swap 3 0) v3 = v9 := hsw 3 0 0 4 (by decide) 3 4 (by decide) (by decide)
  have h30_4 : permToken (Equiv.swap 3 0) v4 = v4 := hsw 3 0 1 2 (by decide) 1 2 (by decide) (by decide)
  have h30_5 : permToken (Equiv.swap 3 0) v5 = v0 := hsw 3 0 1 3 (by decide) 0 1 (by decide) (by decide)
  have h30_6 : permToken (Equiv.swap 3 0) v6 = v6 := hsw 3 0 1 4 (by decide) 1 4 (by decide) (by decide)
  have h30_7 : permToken (Equiv.swap 3 0) v7 = v1 := hsw 3 0 2 3 (by decide) 0 2 (by decide) (by decide)
  have h30_8 : permToken (Equiv.swap 3 0) v8 = v8 := hsw 3 0 2 4 (by decide) 2 4 (by decide) (by decide)
  have h30_9 : permToken (Equiv.swap 3 0) v9 = v3 := hsw 3 0 3 4 (by decide) 0 4 (by decide) (by decide)
  have h40_0 : permToken (Equiv.swap 4 0) v0 = v6 := hsw 4 0 0 1 (by decide) 1 4 (by decide) (by decide)
  have h40_1 : permToken (Equiv.swap 4 0) v1 = v8 := hsw 4 0 0 2 (by decide) 2 4 (by decide) (by decide)
  have h40_2 : permToken (Equiv.swap 4 0) v2 = v9 := hsw 4 0 0 3 (by decide) 3 4 (by decide) (by decide)
  have h40_3 : permToken (Equiv.swap 4 0) v3 = v3 := hsw 4 0 0 4 (by decide) 0 4 (by decide) (by decide)
  have h40_4 : permToken (Equiv.swap 4 0) v4 = v4 := hsw 4 0 1 2 (by decide) 1 2 (by decide) (by decide)
  have h40_5 : permToken (Equiv.swap 4 0) v5 = v5 := hsw 4 0 1 3 (by decide) 1 3 (by decide) (by decide)
  have h40_6 : permToken (Equiv.swap 4 0) v6 = v0 := hsw 4 0 1 4 (by decide) 0 1 (by decide) (by decide)
  have h40_7 : permToken (Equiv.swap 4 0) v7 = v7 := hsw 4 0 2 3 (by decide) 2 3 (by decide) (by decide)
  have h40_8 : permToken (Equiv.swap 4 0) v8 = v1 := hsw 4 0 2 4 (by decide) 0 2 (by decide) (by decide)
  have h40_9 : permToken (Equiv.swap 4 0) v9 = v2 := hsw 4 0 3 4 (by decide) 0 3 (by decide) (by decide)
  have h12_0 : permToken (Equiv.swap 1 2) v0 = v1 := hsw 1 2 0 1 (by decide) 0 2 (by decide) (by decide)
  have h12_1 : permToken (Equiv.swap 1 2) v1 = v0 := hsw 1 2 0 2 (by decide) 0 1 (by decide) (by decide)
  have h12_2 : permToken (Equiv.swap 1 2) v2 = v2 := hsw 1 2 0 3 (by decide) 0 3 (by decide) (by decide)
  have h12_3 : permToken (Equiv.swap 1 2) v3 = v3 := hsw 1 2 0 4 (by decide) 0 4 (by decide) (by decide)
  have h12_4 : permToken (Equiv.swap 1 2) v4 = v4 := hsw 1 2 1 2 (by decide) 1 2 (by decide) (by decide)
  have h12_5 : permToken (Equiv.swap 1 2) v5 = v7 := hsw 1 2 1 3 (by decide) 2 3 (by decide) (by decide)
  have h12_6 : permToken (Equiv.swap 1 2) v6 = v8 := hsw 1 2 1 4 (by decide) 2 4 (by decide) (by decide)
  have h12_7 : permToken (Equiv.swap 1 2) v7 = v5 := hsw 1 2 2 3 (by decide) 1 3 (by decide) (by decide)
  have h12_8 : permToken (Equiv.swap 1 2) v8 = v6 := hsw 1 2 2 4 (by decide) 1 4 (by decide) (by decide)
  have h12_9 : permToken (Equiv.swap 1 2) v9 = v9 := hsw 1 2 3 4 (by decide) 3 4 (by decide) (by decide)
  have h13_0 : permToken (Equiv.swap 1 3) v0 = v2 := hsw 1 3 0 1 (by decide) 0 3 (by decide) (by decide)
  have h13_1 : permToken (Equiv.swap 1 3) v1 = v1 := hsw 1 3 0 2 (by decide) 0 2 (by decide) (by decide)
  have h13_2 : permToken (Equiv.swap 1 3) v2 = v0 := hsw 1 3 0 3 (by decide) 0 1 (by decide) (by decide)
  have h13_3 : permToken (Equiv.swap 1 3) v3 = v3 := hsw 1 3 0 4 (by decide) 0 4 (by decide) (by decide)
  have h13_4 : permToken (Equiv.swap 1 3) v4 = v7 := hsw 1 3 1 2 (by decide) 2 3 (by decide) (by decide)
  have h13_5 : permToken (Equiv.swap 1 3) v5 = v5 := hsw 1 3 1 3 (by decide) 1 3 (by decide) (by decide)
  have h13_6 : permToken (Equiv.swap 1 3) v6 = v9 := hsw 1 3 1 4 (by decide) 3 4 (by decide) (by decide)
  have h13_7 : permToken (Equiv.swap 1 3) v7 = v4 := hsw 1 3 2 3 (by decide) 1 2 (by decide) (by decide)
  have h13_8 : permToken (Equiv.swap 1 3) v8 = v8 := hsw 1 3 2 4 (by decide) 2 4 (by decide) (by decide)
  have h13_9 : permToken (Equiv.swap 1 3) v9 = v6 := hsw 1 3 3 4 (by decide) 1 4 (by decide) (by decide)
  have h14_0 : permToken (Equiv.swap 1 4) v0 = v3 := hsw 1 4 0 1 (by decide) 0 4 (by decide) (by decide)
  have h14_1 : permToken (Equiv.swap 1 4) v1 = v1 := hsw 1 4 0 2 (by decide) 0 2 (by decide) (by decide)
  have h14_2 : permToken (Equiv.swap 1 4) v2 = v2 := hsw 1 4 0 3 (by decide) 0 3 (by decide) (by decide)
  have h14_3 : permToken (Equiv.swap 1 4) v3 = v0 := hsw 1 4 0 4 (by decide) 0 1 (by decide) (by decide)
  have h14_4 : permToken (Equiv.swap 1 4) v4 = v8 := hsw 1 4 1 2 (by decide) 2 4 (by decide) (by decide)
  have h14_5 : permToken (Equiv.swap 1 4) v5 = v9 := hsw 1 4 1 3 (by decide) 3 4 (by decide) (by decide)
  have h14_6 : permToken (Equiv.swap 1 4) v6 = v6 := hsw 1 4 1 4 (by decide) 1 4 (by decide) (by decide)
  have h14_7 : permToken (Equiv.swap 1 4) v7 = v7 := hsw 1 4 2 3 (by decide) 2 3 (by decide) (by decide)
  have h14_8 : permToken (Equiv.swap 1 4) v8 = v4 := hsw 1 4 2 4 (by decide) 1 2 (by decide) (by decide)
  have h14_9 : permToken (Equiv.swap 1 4) v9 = v5 := hsw 1 4 3 4 (by decide) 1 3 (by decide) (by decide)
  have h23_0 : permToken (Equiv.swap 2 3) v0 = v0 := hsw 2 3 0 1 (by decide) 0 1 (by decide) (by decide)
  have h23_1 : permToken (Equiv.swap 2 3) v1 = v2 := hsw 2 3 0 2 (by decide) 0 3 (by decide) (by decide)
  have h23_2 : permToken (Equiv.swap 2 3) v2 = v1 := hsw 2 3 0 3 (by decide) 0 2 (by decide) (by decide)
  have h23_3 : permToken (Equiv.swap 2 3) v3 = v3 := hsw 2 3 0 4 (by decide) 0 4 (by decide) (by decide)
  have h23_4 : permToken (Equiv.swap 2 3) v4 = v5 := hsw 2 3 1 2 (by decide) 1 3 (by decide) (by decide)
  have h23_5 : permToken (Equiv.swap 2 3) v5 = v4 := hsw 2 3 1 3 (by decide) 1 2 (by decide) (by decide)
  have h23_6 : permToken (Equiv.swap 2 3) v6 = v6 := hsw 2 3 1 4 (by decide) 1 4 (by decide) (by decide)
  have h23_7 : permToken (Equiv.swap 2 3) v7 = v7 := hsw 2 3 2 3 (by decide) 2 3 (by decide) (by decide)
  have h23_8 : permToken (Equiv.swap 2 3) v8 = v9 := hsw 2 3 2 4 (by decide) 3 4 (by decide) (by decide)
  have h23_9 : permToken (Equiv.swap 2 3) v9 = v8 := hsw 2 3 3 4 (by decide) 2 4 (by decide) (by decide)
  have h24_0 : permToken (Equiv.swap 2 4) v0 = v0 := hsw 2 4 0 1 (by decide) 0 1 (by decide) (by decide)
  have h24_1 : permToken (Equiv.swap 2 4) v1 = v3 := hsw 2 4 0 2 (by decide) 0 4 (by decide) (by decide)
  have h24_2 : permToken (Equiv.swap 2 4) v2 = v2 := hsw 2 4 0 3 (by decide) 0 3 (by decide) (by decide)
  have h24_3 : permToken (Equiv.swap 2 4) v3 = v1 := hsw 2 4 0 4 (by decide) 0 2 (by decide) (by decide)
  have h24_4 : permToken (Equiv.swap 2 4) v4 = v6 := hsw 2 4 1 2 (by decide) 1 4 (by decide) (by decide)
  have h24_5 : permToken (Equiv.swap 2 4) v5 = v5 := hsw 2 4 1 3 (by decide) 1 3 (by decide) (by decide)
  have h24_6 : permToken (Equiv.swap 2 4) v6 = v4 := hsw 2 4 1 4 (by decide) 1 2 (by decide) (by decide)
  have h24_7 : permToken (Equiv.swap 2 4) v7 = v9 := hsw 2 4 2 3 (by decide) 3 4 (by decide) (by decide)
  have h24_8 : permToken (Equiv.swap 2 4) v8 = v8 := hsw 2 4 2 4 (by decide) 2 4 (by decide) (by decide)
  have h24_9 : permToken (Equiv.swap 2 4) v9 = v7 := hsw 2 4 3 4 (by decide) 2 3 (by decide) (by decide)
  have h34_0 : permToken (Equiv.swap 3 4) v0 = v0 := hsw 3 4 0 1 (by decide) 0 1 (by decide) (by decide)
  have h34_1 : permToken (Equiv.swap 3 4) v1 = v1 := hsw 3 4 0 2 (by decide) 0 2 (by decide) (by decide)
  have h34_2 : permToken (Equiv.swap 3 4) v2 = v3 := hsw 3 4 0 3 (by decide) 0 4 (by decide) (by decide)
  have h34_3 : permToken (Equiv.swap 3 4) v3 = v2 := hsw 3 4 0 4 (by decide) 0 3 (by decide) (by decide)
  have h34_4 : permToken (Equiv.swap 3 4) v4 = v4 := hsw 3 4 1 2 (by decide) 1 2 (by decide) (by decide)
  have h34_5 : permToken (Equiv.swap 3 4) v5 = v6 := hsw 3 4 1 3 (by decide) 1 4 (by decide) (by decide)
  have h34_6 : permToken (Equiv.swap 3 4) v6 = v5 := hsw 3 4 1 4 (by decide) 1 3 (by decide) (by decide)
  have h34_7 : permToken (Equiv.swap 3 4) v7 = v8 := hsw 3 4 2 3 (by decide) 2 4 (by decide) (by decide)
  have h34_8 : permToken (Equiv.swap 3 4) v8 = v7 := hsw 3 4 2 4 (by decide) 2 3 (by decide) (by decide)
  have h34_9 : permToken (Equiv.swap 3 4) v9 = v9 := hsw 3 4 3 4 (by decide) 3 4 (by decide) (by decide)
  unfold ip Mop swapOp
  simp only [hsum,
    h10_0, h10_1, h10_2, h10_3, h10_4, h10_5, h10_6, h10_7, h10_8, h10_9,
    h20_0, h20_1, h20_2, h20_3, h20_4, h20_5, h20_6, h20_7, h20_8, h20_9,
    h30_0, h30_1, h30_2, h30_3, h30_4, h30_5, h30_6, h30_7, h30_8, h30_9,
    h40_0, h40_1, h40_2, h40_3, h40_4, h40_5, h40_6, h40_7, h40_8, h40_9,
    h12_0, h12_1, h12_2, h12_3, h12_4, h12_5, h12_6, h12_7, h12_8, h12_9,
    h13_0, h13_1, h13_2, h13_3, h13_4, h13_5, h13_6, h13_7, h13_8, h13_9,
    h14_0, h14_1, h14_2, h14_3, h14_4, h14_5, h14_6, h14_7, h14_8, h14_9,
    h23_0, h23_1, h23_2, h23_3, h23_4, h23_5, h23_6, h23_7, h23_8, h23_9,
    h24_0, h24_1, h24_2, h24_3, h24_4, h24_5, h24_6, h24_7, h24_8, h24_9,
    h34_0, h34_1, h34_2, h34_3, h34_4, h34_5, h34_6, h34_7, h34_8, h34_9]
  rw [fin5_B4_sos (h v0) (h v1) (h v2) (h v3) (h v4) (h v5) (h v6) (h v7) (h v8) (h v9)]
  positivity

private lemma fin5_B4_nonneg (m : ℕ) (g : TokenVert (Fin 5) m → ℝ) :
    0 ≤ 6 * ip g g -
      (2 * ip (Mop 0 1 2 g) (Mop 0 3 4 g) +
       2 * ip (Mop 0 1 3 g) (Mop 0 2 4 g) +
       2 * ip (Mop 0 1 4 g) (Mop 0 2 3 g)) := by
  -- Complement involution reduces m = 3, 4, 5 directly to m = 2, 1, 0!
  have hcompl_reduce : ∀ (m' : ℕ) (hm' : m' ≤ 5) (h : TokenVert (Fin 5) m' → ℝ),
      (6 * ip h h -
        (2 * ip (Mop 0 1 2 h) (Mop 0 3 4 h) +
         2 * ip (Mop 0 1 3 h) (Mop 0 2 4 h) +
         2 * ip (Mop 0 1 4 h) (Mop 0 2 3 h))) =
      (6 * ip (fun S : TokenVert (Fin 5) (5 - m') => h ⟨S.valᶜ, by rw [Finset.card_compl, Fintype.card_fin, S.property]; omega⟩)
              (fun S : TokenVert (Fin 5) (5 - m') => h ⟨S.valᶜ, by rw [Finset.card_compl, Fintype.card_fin, S.property]; omega⟩) -
        (2 * ip (Mop 0 1 2 (fun S : TokenVert (Fin 5) (5 - m') => h ⟨S.valᶜ, by rw [Finset.card_compl, Fintype.card_fin, S.property]; omega⟩))
                (Mop 0 3 4 (fun S : TokenVert (Fin 5) (5 - m') => h ⟨S.valᶜ, by rw [Finset.card_compl, Fintype.card_fin, S.property]; omega⟩)) +
         2 * ip (Mop 0 1 3 (fun S : TokenVert (Fin 5) (5 - m') => h ⟨S.valᶜ, by rw [Finset.card_compl, Fintype.card_fin, S.property]; omega⟩))
                (Mop 0 2 4 (fun S : TokenVert (Fin 5) (5 - m') => h ⟨S.valᶜ, by rw [Finset.card_compl, Fintype.card_fin, S.property]; omega⟩)) +
         2 * ip (Mop 0 1 4 (fun S : TokenVert (Fin 5) (5 - m') => h ⟨S.valᶜ, by rw [Finset.card_compl, Fintype.card_fin, S.property]; omega⟩))
                (Mop 0 2 3 (fun S : TokenVert (Fin 5) (5 - m') => h ⟨S.valᶜ, by rw [Finset.card_compl, Fintype.card_fin, S.property]; omega⟩)))) := by
    intro m' hm' h
    let e : TokenVert (Fin 5) (5 - m') ≃ TokenVert (Fin 5) m' :=
      { toFun := fun S => ⟨S.valᶜ, by rw [Finset.card_compl, Fintype.card_fin, S.property]; omega⟩
        invFun := fun S => ⟨S.valᶜ, by rw [Finset.card_compl, Fintype.card_fin, S.property]⟩
        left_inv := fun S => Subtype.ext (compl_compl S.val)
        right_inv := fun S => Subtype.ext (compl_compl S.val) }
    have he_perm : ∀ (σ : Equiv.Perm (Fin 5)) (S : TokenVert (Fin 5) (5 - m')),
        e (permToken σ S) = permToken σ (e S) := by
      intro σ S
      ext x
      simp only [e, permToken, Equiv.coe_fn_mk, Finset.mem_compl, Finset.mem_map,
        Equiv.coe_toEmbedding]
      constructor
      · intro hx; refine ⟨σ⁻¹ x, ?_, by simp⟩
        intro hmem; exact hx ⟨σ⁻¹ x, hmem, by simp⟩
      · rintro ⟨y, hy, rfl⟩ ⟨z, hz, hzy⟩
        exact hy (σ.injective hzy ▸ hz)
    have hip_eq : ∀ (F G : TokenVert (Fin 5) m' → ℝ),
        ip F G = ip (fun S => F (e S)) (fun S => G (e S)) :=
      fun F G => (Equiv.sum_comp e (fun S => F S * G S)).symm
    have hM_eq : ∀ (a b : Fin 5) (S : TokenVert (Fin 5) (5 - m')),
        Mop 0 a b h (e S) = Mop 0 a b (fun T => h (e T)) S := by
      intro a b S
      simp only [Mop, swapOp, he_perm]
    have hM_ip : ∀ (a b c d : Fin 5),
        ip (Mop 0 a b h) (Mop 0 c d h) =
        ip (Mop 0 a b (fun T => h (e T))) (Mop 0 c d (fun T => h (e T))) := by
      intro a b c d
      rw [hip_eq]
      unfold ip; congr 1; ext S
      dsimp only
      rw [hM_eq, hM_eq]
    rw [hip_eq h h, hM_ip 1 2 3 4, hM_ip 1 3 2 4, hM_ip 1 4 2 3]
    rfl
  -- Core proof for m ≤ 2:
  have hle2 : ∀ (m' : ℕ) (_ : m' ≤ 2) (h : TokenVert (Fin 5) m' → ℝ),
      0 ≤ 6 * ip h h -
        (2 * ip (Mop 0 1 2 h) (Mop 0 3 4 h) +
         2 * ip (Mop 0 1 3 h) (Mop 0 2 4 h) +
         2 * ip (Mop 0 1 4 h) (Mop 0 2 3 h)) := by
    intro m' hm' h
    interval_cases m'
    · have h1 : ∀ S : TokenVert (Fin 5) 0, S = ⟨∅, Finset.card_empty⟩ := fun S =>
        Subtype.ext (Finset.card_eq_zero.mp S.property)
      have huniq : (Finset.univ : Finset (TokenVert (Fin 5) 0)) = {⟨∅, Finset.card_empty⟩} := by
        ext S; simp [h1 S]
      unfold ip Mop swapOp
      rw [huniq]; simp only [Finset.sum_singleton]
      have hfix : ∀ σ : Equiv.Perm (Fin 5), permToken σ ⟨∅, Finset.card_empty⟩ = ⟨∅, Finset.card_empty⟩ := fun σ =>
        Subtype.ext (by simp [permToken])
      simp only [hfix]
      exact le_of_eq (by ring)
    · let v : Fin 5 → TokenVert (Fin 5) 1 := fun i => ⟨{i}, Finset.card_singleton i⟩
      have hbij : Function.Bijective v := by
        refine ⟨fun i j h => Finset.singleton_injective (congrArg Subtype.val h), fun S => ?_⟩
        obtain ⟨i, hi⟩ := Finset.card_eq_one.mp S.property
        exact ⟨i, Subtype.ext hi.symm⟩
      have hsum : ∀ F : TokenVert (Fin 5) 1 → ℝ, (∑ S, F S) = ∑ i : Fin 5, F (v i) :=
        fun F => (Equiv.sum_comp (Equiv.ofBijective v hbij) F).symm
      have hperm : ∀ (a b i : Fin 5), permToken (Equiv.swap a b) (v i) = v (Equiv.swap a b i) := by
        intro a b i; ext x; simp [permToken, v]
      have hsw : ∀ (a b i : Fin 5), Equiv.swap a b i = if i = a then b else if i = b then a else i :=
        fun a b i => Equiv.swap_apply_def a b i
      unfold ip Mop swapOp
      simp_rw [hsum, hperm, Fin.sum_univ_five]
      simp only [hsw, Fin.isValue, Fin.reduceEq, ↓reduceIte]
      exact le_of_eq (by ring)
    · exact fin5_B4_nonneg_m2 h
  by_cases hm5 : m ≤ 5
  · by_cases hm2 : m ≤ 2
    · exact hle2 m hm2 g
    · rw [hcompl_reduce m hm5 g]
      exact hle2 (5 - m) (by omega) _
  · have hempty : IsEmpty (TokenVert (Fin 5) m) := ⟨fun S => by
      have := Finset.card_le_univ S.val
      simp [S.property] at this; omega⟩
    unfold ip
    simp [Finset.univ_eq_empty]

/-! ### Part 3: Fiber decomposition lifting `Fin 4` / `Fin 5` SOS to arbitrary `Fin n` -/

private def FiberBase {n r : ℕ} (k : ℕ) (ι : Fin r ↪ Fin n) :=
  { U : Finset (Fin n) // Disjoint U (Finset.univ.map ι) ∧ U.card ≤ k }

private instance {n r k : ℕ} (ι : Fin r ↪ Fin n) : Fintype (FiberBase k ι) := by
  unfold FiberBase; infer_instance

private def fiberEmbed {n r k : ℕ} (ι : Fin r ↪ Fin n) (U : FiberBase k ι)
    (A : TokenVert (Fin r) (k - U.val.card)) : TokenVert (Fin n) k :=
  ⟨U.val ∪ A.val.map ι, by
    rw [Finset.card_union_of_disjoint]
    · rw [Finset.card_map, A.property]; have := U.property.2; omega
    · exact Disjoint.mono_right (Finset.map_subset_map.mpr (Finset.subset_univ _)) U.property.1⟩

private def fiberEquiv {n r k : ℕ} (ι : Fin r ↪ Fin n) :
    (Σ U : FiberBase k ι, TokenVert (Fin r) (k - U.val.card)) ≃ TokenVert (Fin n) k where
  toFun p := fiberEmbed ι p.1 p.2
  invFun S :=
    let Im := Finset.univ.map ι
    let U : FiberBase k ι := ⟨S.val \ Im, disjoint_sdiff_self_left,
      (Finset.card_le_card Finset.sdiff_subset).trans (le_of_eq S.property)⟩
    let A : Finset (Fin r) := Finset.univ.filter (fun j => ι j ∈ S.val)
    have hA_map : A.map ι = S.val ∩ Im := by
      ext x
      simp only [A, Im, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_inter]
      constructor
      · rintro ⟨j, hj, rfl⟩; exact ⟨hj, ⟨j, rfl⟩⟩
      · rintro ⟨hxS, ⟨j, rfl⟩⟩; exact ⟨j, hxS, rfl⟩
    have hcard : A.card = k - U.val.card := by
      have hdisj : Disjoint (S.val \ Im) (S.val ∩ Im) := Finset.disjoint_sdiff_inter S.val Im
      have hunion : (S.val \ Im) ∪ (S.val ∩ Im) = S.val := Finset.sdiff_union_inter S.val Im
      have hc := Finset.card_union_of_disjoint hdisj
      rw [hunion, S.property, ← hA_map, Finset.card_map] at hc
      have : U.val.card = (S.val \ Im).card := rfl
      omega
    ⟨U, ⟨A, hcard⟩⟩
  left_inv p := by
    rcases p with ⟨⟨U, hUdisj, hUle⟩, ⟨A, hA⟩⟩
    have hUeq : (U ∪ A.map ι) \ Finset.univ.map ι = U := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_map, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hxU | ⟨j, _, rfl⟩, hnot⟩
        · exact hxU
        · exact absurd ⟨j, rfl⟩ hnot
      · intro hxU
        refine ⟨Or.inl hxU, ?_⟩
        rintro ⟨j, rfl⟩
        exact Finset.disjoint_left.mp hUdisj hxU (Finset.mem_map.mpr ⟨j, Finset.mem_univ j, rfl⟩)
    have hAeq : Finset.univ.filter (fun j => ι j ∈ U ∪ A.map ι) = A := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_map]
      constructor
      · rintro (hjU | ⟨j', hj', heq⟩)
        · exact absurd (Finset.mem_map.mpr ⟨j, Finset.mem_univ j, rfl⟩)
            (Finset.disjoint_left.mp hUdisj hjU)
        · exact ι.injective heq ▸ hj'
      · intro hjA; exact Or.inr ⟨j, hjA, rfl⟩
    have hsigma : ∀ (U₁ U₂ : FiberBase k ι) (A₁ : TokenVert (Fin r) (k - U₁.val.card))
        (A₂ : TokenVert (Fin r) (k - U₂.val.card)),
        U₁.val = U₂.val → A₁.val = A₂.val →
        (⟨U₁, A₁⟩ : Σ U : FiberBase k ι, TokenVert (Fin r) (k - U.val.card)) = ⟨U₂, A₂⟩ := by
      rintro ⟨U₁, h1, h2⟩ ⟨U₂, h3, h4⟩ ⟨A₁, hA₁⟩ ⟨A₂, hA₂⟩ rfl rfl
      rfl
    exact hsigma _ _ _ _ hUeq hAeq
  right_inv S := by
    ext x
    simp only [fiberEmbed, Finset.mem_union, Finset.mem_sdiff, Finset.mem_map, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro (⟨hxS, _⟩ | ⟨j, hj, rfl⟩)
      · exact hxS
      · exact hj
    · intro hxS
      by_cases h : ∃ j : Fin r, ι j = x
      · obtain ⟨j, rfl⟩ := h; exact Or.inr ⟨j, hxS, rfl⟩
      · exact Or.inl ⟨hxS, h⟩

private lemma fiberEmbed_swap {n r k : ℕ} (ι : Fin r ↪ Fin n) (U : FiberBase k ι)
    (a b : Fin r) (A : TokenVert (Fin r) (k - U.val.card)) :
    permToken (Equiv.swap (ι a) (ι b)) (fiberEmbed ι U A) =
      fiberEmbed ι U (permToken (Equiv.swap a b) A) := by
  ext x
  simp only [permToken, fiberEmbed, Finset.mem_map, Equiv.coe_toEmbedding, Finset.mem_union]
  constructor
  · rintro ⟨y, hyU | ⟨j, hjA, rfl⟩, rfl⟩
    · left
      have hya : y ≠ ι a := fun h => Finset.disjoint_left.mp U.property.1 hyU
        (h ▸ Finset.mem_map.mpr ⟨a, Finset.mem_univ a, rfl⟩)
      have hyb : y ≠ ι b := fun h => Finset.disjoint_left.mp U.property.1 hyU
        (h ▸ Finset.mem_map.mpr ⟨b, Finset.mem_univ b, rfl⟩)
      rwa [Equiv.swap_apply_of_ne_of_ne hya hyb]
    · right
      refine ⟨Equiv.swap a b j, ⟨j, hjA, rfl⟩, ?_⟩
      by_cases hja : j = a
      · subst hja; simp
      by_cases hjb : j = b
      · subst hjb; simp
      rw [Equiv.swap_apply_of_ne_of_ne hja hjb,
          Equiv.swap_apply_of_ne_of_ne (fun h => hja (ι.injective h)) (fun h => hjb (ι.injective h))]
  · rintro (hxU | ⟨j, ⟨j', hj'A, rfl⟩, rfl⟩)
    · refine ⟨x, Or.inl hxU, ?_⟩
      have hxa : x ≠ ι a := fun h => Finset.disjoint_left.mp U.property.1 hxU
        (h ▸ Finset.mem_map.mpr ⟨a, Finset.mem_univ a, rfl⟩)
      have hxb : x ≠ ι b := fun h => Finset.disjoint_left.mp U.property.1 hxU
        (h ▸ Finset.mem_map.mpr ⟨b, Finset.mem_univ b, rfl⟩)
      exact Equiv.swap_apply_of_ne_of_ne hxa hxb
    · refine ⟨ι j', Or.inr ⟨j', hj'A, rfl⟩, ?_⟩
      by_cases hja : j' = a
      · subst hja; simp
      by_cases hjb : j' = b
      · subst hjb; simp
      rw [Equiv.swap_apply_of_ne_of_ne hja hjb,
          Equiv.swap_apply_of_ne_of_ne (fun h => hja (ι.injective h)) (fun h => hjb (ι.injective h))]

private lemma ip_fiber_decomp {n r k : ℕ} (ι : Fin r ↪ Fin n)
    (F G : TokenVert (Fin n) k → ℝ) :
    ip F G = ∑ U : FiberBase k ι, ip (fun A => F (fiberEmbed ι U A)) (fun A => G (fiberEmbed ι U A)) := by
  unfold ip
  rw [← Equiv.sum_comp (fiberEquiv ι) (fun S => F S * G S), Fintype.sum_sigma]
  rfl

private lemma B3_nonneg {n k : ℕ} {z a b c : Fin n}
    (hza : z ≠ a) (hzb : z ≠ b) (hzc : z ≠ c) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (f : TokenVert (Fin n) k → ℝ) :
    0 ≤ 4 * ip f f -
      (2 * ip (swapOp a z f) (Mop z b c f) + 2 * ip (Mop z a b f) (Mop z a c f)) := by
  let ι : Fin 4 ↪ Fin n :=
    ⟨![z, a, b, c], by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp at hij
      all_goals first
        | rfl
        | exact absurd hij hza | exact absurd hij.symm hza
        | exact absurd hij hzb | exact absurd hij.symm hzb
        | exact absurd hij hzc | exact absurd hij.symm hzc
        | exact absurd hij hab | exact absurd hij.symm hab
        | exact absurd hij hac | exact absurd hij.symm hac
        | exact absurd hij hbc | exact absurd hij.symm hbc⟩
  have h0 : ι 0 = z := rfl
  have h1 : ι 1 = a := rfl
  have h2 : ι 2 = b := rfl
  have h3 : ι 3 = c := rfl
  rw [← h0, ← h1, ← h2, ← h3]
  rw [ip_fiber_decomp ι f f, ip_fiber_decomp ι (swapOp (ι 1) (ι 0) f) (Mop (ι 0) (ι 2) (ι 3) f),
      ip_fiber_decomp ι (Mop (ι 0) (ι 1) (ι 2) f) (Mop (ι 0) (ι 1) (ι 3) f)]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_nonneg
  intro U _
  let fU : TokenVert (Fin 4) (k - U.val.card) → ℝ := fun A => f (fiberEmbed ι U A)
  have hswap : ∀ p q : Fin 4, (fun A => swapOp (ι p) (ι q) f (fiberEmbed ι U A)) = swapOp p q fU := by
    intro p q; ext A; simp [swapOp, fU, fiberEmbed_swap]
  have hMop : ∀ p q s : Fin 4, (fun A => Mop (ι p) (ι q) (ι s) f (fiberEmbed ι U A)) = Mop p q s fU := by
    intro p q s; ext A; simp [Mop, swapOp, fU, fiberEmbed_swap]
  rw [hswap 1 0, hMop 0 2 3, hMop 0 1 2, hMop 0 1 3]
  exact fin4_B3_nonneg (k - U.val.card) fU

private lemma B4_nonneg {n k : ℕ} {z a b c d : Fin n}
    (hza : z ≠ a) (hzb : z ≠ b) (hzc : z ≠ c) (hzd : z ≠ d)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (f : TokenVert (Fin n) k → ℝ) :
    0 ≤ 6 * ip f f -
      (2 * ip (Mop z a b f) (Mop z c d f) +
       2 * ip (Mop z a c f) (Mop z b d f) +
       2 * ip (Mop z a d f) (Mop z b c f)) := by
  let ι : Fin 5 ↪ Fin n :=
    ⟨![z, a, b, c, d], by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp at hij
      all_goals first
        | rfl
        | exact absurd hij hza | exact absurd hij.symm hza
        | exact absurd hij hzb | exact absurd hij.symm hzb
        | exact absurd hij hzc | exact absurd hij.symm hzc
        | exact absurd hij hzd | exact absurd hij.symm hzd
        | exact absurd hij hab | exact absurd hij.symm hab
        | exact absurd hij hac | exact absurd hij.symm hac
        | exact absurd hij had | exact absurd hij.symm had
        | exact absurd hij hbc | exact absurd hij.symm hbc
        | exact absurd hij hbd | exact absurd hij.symm hbd
        | exact absurd hij hcd | exact absurd hij.symm hcd⟩
  have h0 : ι 0 = z := rfl
  have h1 : ι 1 = a := rfl
  have h2 : ι 2 = b := rfl
  have h3 : ι 3 = c := rfl
  have h4 : ι 4 = d := rfl
  rw [← h0, ← h1, ← h2, ← h3, ← h4]
  rw [ip_fiber_decomp ι f f,
      ip_fiber_decomp ι (Mop (ι 0) (ι 1) (ι 2) f) (Mop (ι 0) (ι 3) (ι 4) f),
      ip_fiber_decomp ι (Mop (ι 0) (ι 1) (ι 3) f) (Mop (ι 0) (ι 2) (ι 4) f),
      ip_fiber_decomp ι (Mop (ι 0) (ι 1) (ι 4) f) (Mop (ι 0) (ι 2) (ι 3) f)]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_nonneg
  intro U _
  let fU : TokenVert (Fin 5) (k - U.val.card) → ℝ := fun A => f (fiberEmbed ι U A)
  have hMop : ∀ p q s : Fin 5, (fun A => Mop (ι p) (ι q) (ι s) f (fiberEmbed ι U A)) = Mop p q s fU := by
    intro p q s; ext A; simp [Mop, swapOp, fU, fiberEmbed_swap]
  rw [hMop 0 1 2, hMop 0 3 4, hMop 0 1 3, hMop 0 2 4, hMop 0 1 4, hMop 0 2 3]
  exact fin5_B4_nonneg (k - U.val.card) fU

/-! ### Part 4: Cesi's Quartic Octopus Inequality -/

private lemma sum_pairs_symm {m : ℕ} (F : Fin m → Fin m → ℝ)
    (hsym : ∀ i j, F i j = F j i) (hdiag : ∀ i, F i i = 0) :
    ∑ i : Fin m, ∑ j : Fin m, F i j =
      2 * ∑ i : Fin m, ∑ j : Fin m, if i < j then F i j else 0 := by
  have hsplit : ∀ i j : Fin m, F i j = (if i < j then F i j else 0) + (if j < i then F i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, not_lt.mpr (le_of_lt h)]
    · simp [hdiag i]
    · simp [h, not_lt.mpr (le_of_lt h)]
  conv_lhs => arg 2; ext i; arg 2; ext j; rw [hsplit i j]
  simp_rw [Finset.sum_add_distrib]
  have hswap : (∑ i : Fin m, ∑ j : Fin m, if j < i then F i j else 0) =
      ∑ i : Fin m, ∑ j : Fin m, if i < j then F i j else 0 := by
    rw [Finset.sum_comm]
    congr 1; ext i; congr 1; ext j
    split_ifs <;> simp [hsym]
  rw [hswap]; ring

private lemma sum_pairs_symm_ne {m : ℕ} (G : Fin m → Fin m → ℝ) (hsym : ∀ i j, G i j = G j i) :
    ∑ i : Fin m, ∑ j : Fin m, (if i = j then (0 : ℝ) else G i j) =
      2 * ∑ i : Fin m, ∑ j : Fin m, if i < j then G i j else 0 := by
  rw [sum_pairs_symm (fun i j => if i = j then (0 : ℝ) else G i j)]
  · congr 1; congr 1; ext i; congr 1; ext j
    split_ifs with h1 h2
    · exact absurd h2 (ne_of_lt h1)
    · rfl
    · rfl
  · intro i j
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h, hsym i j]
  · intro i; simp

private lemma octopus_ineq {m k : ℕ} (x : Fin m → ℝ) (hx : ∀ i, 0 ≤ x i)
    (f : TokenVert (Fin (m + 1)) k → ℝ) :
    (1 / 2 : ℝ) * ∑ i : Fin m, ∑ j : Fin m, x i * x j * (ip f f - ip f (swapOp i.succ j.succ f)) ≤
      (∑ i : Fin m, x i) * ∑ i : Fin m, x i * (ip f f - ip f (swapOp i.succ 0 f)) := by
  -- Define Cesi's operator Hhat = P + Q and scalar Ihat = I_P + I_Q!
  let Pf : TokenVert (Fin (m + 1)) k → ℝ := fun S => ∑ i : Fin m, x i ^ 2 * swapOp i.succ 0 f S
  let Qf : TokenVert (Fin (m + 1)) k → ℝ := fun S =>
    ∑ i : Fin m, ∑ j : Fin m, if i < j then x i * x j * Mop 0 i.succ j.succ f S else 0
  let Hhat : TokenVert (Fin (m + 1)) k → ℝ := fun S => Pf S + Qf S
  let IP : ℝ := ∑ i : Fin m, x i ^ 2
  let IQ : ℝ := ∑ i : Fin m, ∑ j : Fin m, if i < j then x i * x j else 0
  let Ihat : ℝ := IP + IQ
  have hIhat_nn : 0 ≤ Ihat := by
    apply add_nonneg
    · exact Finset.sum_nonneg fun i _ => sq_nonneg (x i)
    · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
        split_ifs
        · exact mul_nonneg (hx i) (hx j)
        · exact le_rfl
  -- Step 1: Exact linear identity relating Ihat * ip f f - ip f Hhat to C * star - kron!
  have hlin : Ihat * ip f f - ip f Hhat =
      (∑ i : Fin m, x i) * ∑ i : Fin m, x i * (ip f f - ip f (swapOp i.succ 0 f)) -
      (1 / 2 : ℝ) * ∑ i : Fin m, ∑ j : Fin m, x i * x j * (ip f f - ip f (swapOp i.succ j.succ f)) := by
    have hP_ip : ip f Pf = ∑ i : Fin m, x i ^ 2 * ip f (swapOp i.succ 0 f) := by
      simp only [Pf, ip_sum_right, ip_smul_right]
    have hQ_ip : ip f Qf = ∑ i : Fin m, ∑ j : Fin m,
        if i < j then x i * x j * (ip f (swapOp i.succ 0 f) + ip f (swapOp j.succ 0 f) - ip f (swapOp i.succ j.succ f)) else 0 := by
      simp only [Qf, ip_sum_right]
      congr 1; ext i; congr 1; ext j
      split_ifs
      · rw [ip_smul_right]; unfold Mop; rw [ip_sub_right, ip_add_right]
      · simp [ip]
    have h1 : ip f Hhat = ip f Pf + ip f Qf := ip_add_right f Pf Qf
    have hsym_star : ∑ i : Fin m, ∑ j : Fin m,
        (if i = j then (0 : ℝ) else x i * x j * (ip f (swapOp i.succ 0 f) + ip f (swapOp j.succ 0 f) - ip f (swapOp i.succ j.succ f))) =
        2 * ∑ i : Fin m, ∑ j : Fin m,
          if i < j then x i * x j * (ip f (swapOp i.succ 0 f) + ip f (swapOp j.succ 0 f) - ip f (swapOp i.succ j.succ f)) else 0 :=
      sum_pairs_symm_ne _ fun i j => by rw [swapOp_comm i.succ j.succ]; ring
    have hsym_1 : ∑ i : Fin m, ∑ j : Fin m, (if i = j then (0 : ℝ) else x i * x j) =
        2 * IQ :=
      sum_pairs_symm_ne _ fun i j => by ring
    have hfull_1 : ∑ i : Fin m, ∑ j : Fin m, x i * x j = IP + 2 * IQ := by
      rw [← hsym_1]
      have hsp : ∀ i j : Fin m, x i * x j =
          (if i = j then x i * x j else 0) + (if i = j then 0 else x i * x j) := by
        intro i j; split_ifs <;> ring
      conv_lhs => arg 2; ext i; arg 2; ext j; rw [hsp i j]
      simp_rw [Finset.sum_add_distrib]
      congr 1
      simp [IP, sq]
    have hfull_star : ∑ i : Fin m, ∑ j : Fin m,
        x i * x j * (ip f (swapOp i.succ 0 f) + ip f (swapOp j.succ 0 f) - ip f (swapOp i.succ j.succ f)) =
        ∑ i : Fin m, x i ^ 2 * (2 * ip f (swapOp i.succ 0 f) - ip f f) + 2 * ip f Qf := by
      rw [hQ_ip, ← hsym_star]
      have hsp : ∀ i j : Fin m,
          x i * x j * (ip f (swapOp i.succ 0 f) + ip f (swapOp j.succ 0 f) - ip f (swapOp i.succ j.succ f)) =
          (if i = j then x i * x j * (ip f (swapOp i.succ 0 f) + ip f (swapOp j.succ 0 f) - ip f (swapOp i.succ j.succ f)) else 0) +
          (if i = j then 0 else x i * x j * (ip f (swapOp i.succ 0 f) + ip f (swapOp j.succ 0 f) - ip f (swapOp i.succ j.succ f))) := by
        intro i j; split_ifs <;> ring
      conv_lhs => arg 2; ext i; arg 2; ext j; rw [hsp i j]
      simp_rw [Finset.sum_add_distrib]
      congr 1
      simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, swapOp_self]
      congr 1; ext i; ring
    have hRHS_expand :
        (∑ i : Fin m, x i) * ∑ i : Fin m, x i * (ip f f - ip f (swapOp i.succ 0 f)) -
        (1 / 2 : ℝ) * ∑ i : Fin m, ∑ j : Fin m, x i * x j * (ip f f - ip f (swapOp i.succ j.succ f)) =
        (1 / 2 : ℝ) * (∑ i : Fin m, ∑ j : Fin m, x i * x j) * ip f f -
        (1 / 2 : ℝ) * ∑ i : Fin m, ∑ j : Fin m,
          x i * x j * (ip f (swapOp i.succ 0 f) + ip f (swapOp j.succ 0 f) - ip f (swapOp i.succ j.succ f)) := by
      have h1' : (∑ i : Fin m, x i) * ∑ j : Fin m, x j * (ip f f - ip f (swapOp j.succ 0 f)) =
          ∑ i : Fin m, ∑ j : Fin m, x i * x j * (ip f f - ip f (swapOp j.succ 0 f)) := by
        rw [Finset.sum_mul]; congr 1; ext i; rw [Finset.mul_sum]; congr 1; ext j; ring
      have h2' : ∑ i : Fin m, ∑ j : Fin m, x i * x j * ip f (swapOp i.succ 0 f) =
          ∑ i : Fin m, ∑ j : Fin m, x i * x j * ip f (swapOp j.succ 0 f) := by
        rw [Finset.sum_comm]; congr 1; ext i; congr 1; ext j; ring
      rw [h1']
      simp_rw [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
      rw [← h2', mul_assoc (1 / 2 : ℝ), Finset.sum_mul]
      simp_rw [Finset.sum_mul]
      ring
    rw [hRHS_expand, hfull_1, hfull_star, h1, hP_ip]
    have hdiag_diff : ∑ i : Fin m, x i ^ 2 * (2 * ip f (swapOp i.succ 0 f) - ip f f) =
        2 * (∑ i : Fin m, x i ^ 2 * ip f (swapOp i.succ 0 f)) - IP * ip f f := by
      simp only [IP, Finset.sum_mul]
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      congr 1; ext i; ring
    rw [hdiag_diff]
    simp only [Ihat]; ring
  -- Step 2: Quartic bound ip Hhat Hhat ≤ Ihat ^ 2 * ip f f!
  have hquartic : 0 ≤ Ihat ^ 2 * ip f f - ip Hhat Hhat := by
    -- Express Hhat = ∑ a, ∑ b, (x a * x b) • A a b where A a a = swapOp a 0, A a b = (1/2) Mop 0 a b!
    let A : Fin m → Fin m → TokenVert (Fin (m + 1)) k → ℝ := fun a b =>
      if a = b then swapOp a.succ 0 f else fun S => (1 / 2 : ℝ) * Mop 0 a.succ b.succ f S
    let cA : Fin m → Fin m → ℝ := fun a b => if a = b then 1 else (1 / 2 : ℝ)
    have hA_symm : ∀ a b, A a b = A b a := by
      intro a b
      by_cases hab : a = b
      · subst hab; rfl
      · ext S; simp only [A, hab, Ne.symm hab, ↓reduceIte, Mop_comm]
    have hHhat_eq : Hhat = fun S => ∑ a : Fin m, ∑ b : Fin m, (x a * x b) * A a b S := by
      ext S
      have hsym : ∑ a : Fin m, ∑ b : Fin m, (if a = b then (0 : ℝ) else x a * x b * ((1 / 2 : ℝ) * Mop 0 a.succ b.succ f S)) =
          2 * ∑ a : Fin m, ∑ b : Fin m, if a < b then x a * x b * ((1 / 2 : ℝ) * Mop 0 a.succ b.succ f S) else 0 :=
        sum_pairs_symm_ne _ fun a b => by rw [Mop_comm]; ring
      have hsp : ∀ a b : Fin m, (x a * x b) * A a b S =
          (if a = b then x a * x b * swapOp a.succ 0 f S else 0) +
          (if a = b then 0 else x a * x b * ((1 / 2 : ℝ) * Mop 0 a.succ b.succ f S)) := by
        intro a b; simp only [A]; split_ifs <;> ring
      simp_rw [hsp, Finset.sum_add_distrib]
      rw [hsym, Finset.mul_sum]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Hhat, Pf, Qf]
      congr 1
      · congr 1; ext a; ring
      · congr 1; ext a; rw [Finset.mul_sum]; congr 1; ext b; split_ifs <;> ring
    have hIhat_eq : Ihat = ∑ a : Fin m, ∑ b : Fin m, (x a * x b) * cA a b := by
      have hsym : ∑ a : Fin m, ∑ b : Fin m, (if a = b then (0 : ℝ) else x a * x b * (1 / 2 : ℝ)) =
          2 * ∑ a : Fin m, ∑ b : Fin m, if a < b then x a * x b * (1 / 2 : ℝ) else 0 :=
        sum_pairs_symm_ne _ fun a b => by ring
      have hsp : ∀ a b : Fin m, (x a * x b) * cA a b =
          (if a = b then x a * x b else 0) + (if a = b then 0 else x a * x b * (1 / 2 : ℝ)) := by
        intro a b; simp only [cA]; split_ifs <;> ring
      simp_rw [hsp, Finset.sum_add_distrib]
      rw [hsym, Finset.mul_sum]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Ihat, IP, IQ]
      congr 1
      · congr 1; ext a; ring
      · congr 1; ext a; rw [Finset.mul_sum]; congr 1; ext b; split_ifs <;> ring
    -- Expand Ihat^2 * ip f f - ip Hhat Hhat as a 4-fold sum over (a, b, c, d)!
    let D : Fin m → Fin m → Fin m → Fin m → ℝ := fun a b c d =>
      cA a b * cA c d * ip f f - ip (A a b) (A c d)
    have h4sum : Ihat ^ 2 * ip f f - ip Hhat Hhat =
        ∑ a : Fin m, ∑ b : Fin m, ∑ c : Fin m, ∑ d : Fin m, (x a * x b * x c * x d) * D a b c d := by
      have h1 : ip Hhat Hhat =
          ∑ a : Fin m, ∑ b : Fin m, ∑ c : Fin m, ∑ d : Fin m, (x a * x b * x c * x d) * ip (A a b) (A c d) := by
        rw [hHhat_eq, ip_sum_left]
        congr 1; ext a; rw [ip_sum_left]
        congr 1; ext b; rw [ip_sum_right]
        congr 1; ext c; rw [ip_sum_right]
        congr 1; ext d; rw [ip_smul_left, ip_smul_right]; ring
      have h2 : Ihat ^ 2 * ip f f =
          ∑ a : Fin m, ∑ b : Fin m, ∑ c : Fin m, ∑ d : Fin m, (x a * x b * x c * x d) * (cA a b * cA c d * ip f f) := by
        rw [sq, hIhat_eq, Finset.sum_mul, Finset.sum_mul]
        congr 1; ext a; rw [Finset.sum_mul, Finset.sum_mul]
        congr 1; ext b; rw [Finset.mul_sum, Finset.sum_mul]
        congr 1; ext c; rw [Finset.mul_sum, Finset.sum_mul]
        congr 1; ext d; ring
      rw [h1, h2]
      simp_rw [← Finset.sum_sub_distrib, D, mul_sub]
    -- Symmetrize D over all 24 permutations of (a, b, c, d) — wait, even cleaner:
    -- Just average over the 6 ways to pair (a, b, c, d) into two unordered pairs (which leaves x a * x b * x c * x d invariant!):
    -- (a,b,c,d), (a,c,b,d), (a,d,b,c), (b,c,a,d), (b,d,a,c), (c,d,a,b)!
    -- WAIT A SECOND!! CHECK THAT!!
    -- For ANY (a, b, c, d) : Fin m (EVEN WITH REPEATED INDICES!!):
    -- Does D_sym(a, b, c, d) := D a b c d + D a c b d + D a d b c ≥ 0 POINTWISE FOR EVERY (a, b, c, d)?!
    -- LET'S CHECK ALL 5 PATTERNS OF (a, b, c, d)!!
    -- 1. a = b = c = d: D a a a a = 1 - 1 = 0 => sum = 0!
    -- 2. (3,1) e.g. a = b = c ≠ d: D a a a d + D a a a d + D a d a a = 0 + 0 + 0 = 0 (by ip_swap_Mop_cancel)!
    -- 3. (2,2) e.g. a = b ≠ c = d: D a a c c + D a c a c + D a c c a
    --    = (1 - ip(T_a, T_c)) + 2 * (1/4 - (1/4) ip(M_{ac}, M_{ac}))
    --    = (3/2) ip f f - (1/2) * (2 ip(T_a, T_c) + ip(M_{ac}, M_{ac})) = 0 (by ip_Mop_self_plus_cross)!!
    -- 4. (2,1,1) e.g. a = b, c, d distinct:
    --    D a a c d + D a c a d + D a d a c
    --    = (1/2 - (1/2) ip(T_a, M_{cd})) + 2 * (1/4 - (1/4) ip(M_{ac}, M_{ad}))
    --    = (1/4) * (4 ip f f - (2 ip(T_a, M_{cd}) + 2 ip(M_{ac}, M_{ad}))) >= 0 (by B3_nonneg)!!
    -- 5. (1,1,1,1) a, b, c, d pairwise distinct:
    --    D a b c d + D a c b d + D a d b c
    --    = (1/8) * (6 ip f f - (2 ip(M_{ab}, M_{cd}) + 2 ip(M_{ac}, M_{bd}) + 2 ip(M_{ad}, M_{bc}))) >= 0 (by B4_nonneg)!!
    -- OH!! MY!! GOD!! IT IS POINTWISE NONNEGATIVE AFTER JUST AVERAGING THE 3 PAIRINGS!!
    -- ZERO GROUPING, ZERO INDEX SPLITTING, ZERO MULTISETS!!
    have hD_symm_ab : ∀ a b c d, D a b c d = D b a c d := by
      intro a b c d
      by_cases hab : a = b
      · subst hab; rfl
      · simp only [D, cA, hab, Ne.symm hab, ↓reduceIte, hA_symm a b]
    have hD_symm_cd : ∀ a b c d, D a b c d = D a b d c := by
      intro a b c d
      by_cases hcd : c = d
      · subst hcd; rfl
      · simp only [D, cA, hcd, Ne.symm hcd, ↓reduceIte, hA_symm c d]
    have hD_symm_swap : ∀ a b c d, D a b c d = D c d a b := by
      intro a b c d; simp only [D, ip_comm (A a b) (A c d)]; ring
    have h3sum_eq :
        3 * (∑ a : Fin m, ∑ b : Fin m, ∑ c : Fin m, ∑ d : Fin m, (x a * x b * x c * x d) * D a b c d) =
        ∑ a : Fin m, ∑ b : Fin m, ∑ c : Fin m, ∑ d : Fin m,
          (x a * x b * x c * x d) * (D a b c d + D a c b d + D a d b c) := by
      have hS2 : (∑ a : Fin m, ∑ b : Fin m, ∑ c : Fin m, ∑ d : Fin m, (x a * x b * x c * x d) * D a c b d) =
          ∑ a : Fin m, ∑ b : Fin m, ∑ c : Fin m, ∑ d : Fin m, (x a * x b * x c * x d) * D a b c d := by
        congr 1; ext a
        rw [Finset.sum_comm]
        congr 1; ext c; congr 1; ext b; congr 1; ext d; ring
      have hS3 : (∑ a : Fin m, ∑ b : Fin m, ∑ c : Fin m, ∑ d : Fin m, (x a * x b * x c * x d) * D a d b c) =
          ∑ a : Fin m, ∑ b : Fin m, ∑ c : Fin m, ∑ d : Fin m, (x a * x b * x c * x d) * D a b c d := by
        congr 1; ext a
        conv_lhs => arg 2; ext b; rw [Finset.sum_comm]
        rw [Finset.sum_comm]
        congr 1; ext d; rw [Finset.sum_comm]; congr 1; ext b; congr 1; ext c
        rw [hD_symm_cd a d c b]; ring
      simp_rw [mul_add, Finset.sum_add_distrib]
      rw [hS2, hS3]; ring
    -- Prove D a b c d + D a c b d + D a d b c ≥ 0 for EVERY a, b, c, d : Fin m!
    have hD_triple_nn : ∀ a b c d : Fin m, 0 ≤ D a b c d + D a c b d + D a d b c := by
      -- Helper for repeated index p = q: D p p r s + D p r p s + D p s p r ≥ 0!
      have hpair_nn : ∀ p r s : Fin m, 0 ≤ D p p r s + D p r p s + D p s p r := by
        intro p r s
        by_cases hpr : p = r
        · subst hpr
          by_cases hps : p = s
          · subst hps
            simp only [D, cA, A, ↓reduceIte, ip_swapOp_self_norm]
            exact le_of_eq (by ring)
          · simp only [D, cA, A, ↓reduceIte, hps]
            have hc := ip_swap_Mop_cancel (Fin.succ_ne_zero p).symm (Fin.succ_ne_zero s).symm
              (fun h => hps (Fin.succ_injective _ h)) f
            rw [ip_smul_right, ip_smul_left, ip_comm (Mop 0 p.succ s.succ f) (swapOp p.succ 0 f), hc]
            exact le_of_eq (by ring)
        · by_cases hps : p = s
          · subst hps
            simp only [D, cA, A, ↓reduceIte, hpr, Ne.symm hpr]
            have hc := ip_swap_Mop_cancel (Fin.succ_ne_zero p).symm (Fin.succ_ne_zero r).symm
              (fun h => hpr (Fin.succ_injective _ h)) f
            rw [Mop_comm 0 r.succ p.succ, ip_smul_right, ip_smul_left,
                ip_comm (Mop 0 p.succ r.succ f) (swapOp p.succ 0 f), hc]
            exact le_of_eq (by ring)
          · by_cases hrs : r = s
            · subst hrs
              simp only [D, cA, A, ↓reduceIte, hpr]
              rw [ip_smul_left, ip_smul_right]
              have h2 := ip_Mop_self_plus_cross (Fin.succ_ne_zero p).symm (Fin.succ_ne_zero r).symm
                (fun h => hpr (Fin.succ_injective _ h)) f
              linarith
            · simp only [D, cA, A, ↓reduceIte, hpr, hps, hrs]
              rw [ip_smul_right, ip_smul_left, ip_smul_right, ip_smul_left, ip_smul_right]
              rw [ip_comm (Mop 0 p.succ s.succ f) (Mop 0 p.succ r.succ f)]
              have hB3 := B3_nonneg (Fin.succ_ne_zero p).symm (Fin.succ_ne_zero r).symm
                (Fin.succ_ne_zero s).symm (fun h => hpr (Fin.succ_injective _ h))
                (fun h => hps (Fin.succ_injective _ h)) (fun h => hrs (Fin.succ_injective _ h)) f
              linarith
      intro a b c d
      by_cases hab : a = b
      · subst hab; exact hpair_nn a c d
      by_cases hac : a = c
      · subst hac
        have hp := hpair_nn a b d
        rw [hD_symm_cd a d b a]
        linarith
      by_cases had : a = d
      · subst had
        have hp := hpair_nn a b c
        rw [hD_symm_cd a b c a, hD_symm_cd a c b a]
        linarith
      by_cases hbc : b = c
      · subst hbc
        have hp := hpair_nn b a d
        have h1 : D a b b d = D b a b d := hD_symm_ab a b b d
        have h2 : D a b b d = D b d b a := by rw [hD_symm_swap, hD_symm_cd]
        have h3 : D a d b b = D b b a d := hD_symm_swap a d b b
        linarith
      by_cases hbd : b = d
      · subst hbd
        have := hpair_nn b a c
        have h1 : D a b c b = D b a b c := by rw [hD_symm_ab, hD_symm_cd]
        have h2 : D a c b b = D b b a c := hD_symm_swap a c b b
        have h3 : D a b b c = D b a b c := hD_symm_ab a b b c
        have h4 : D b c b a = D b a b c := by rw [hD_symm_swap]
        linarith
      by_cases hcd : c = d
      · subst hcd
        have := hpair_nn c a b
        have h1 : D a b c c = D c c a b := hD_symm_swap a b c c
        have h2 : D a c b c = D c a c b := by rw [hD_symm_ab, hD_symm_cd]
        have h3 : D a c b c = D c b c a := by rw [h2, hD_symm_swap]
        linarith
      -- All 4 pairwise distinct: B4_nonneg!
      simp only [D, cA, A, hab, hac, had, hbc, hbd, hcd, ↓reduceIte]
      rw [ip_smul_left, ip_smul_right, ip_smul_left, ip_smul_right, ip_smul_left, ip_smul_right]
      have hB4 := B4_nonneg (Fin.succ_ne_zero a).symm (Fin.succ_ne_zero b).symm
        (Fin.succ_ne_zero c).symm (Fin.succ_ne_zero d).symm
        (fun h => hab (Fin.succ_injective _ h)) (fun h => hac (Fin.succ_injective _ h))
        (fun h => had (Fin.succ_injective _ h)) (fun h => hbc (Fin.succ_injective _ h))
        (fun h => hbd (Fin.succ_injective _ h)) (fun h => hcd (Fin.succ_injective _ h)) f
      linarith
    rw [h4sum]
    have h3nn : 0 ≤ ∑ a : Fin m, ∑ b : Fin m, ∑ c : Fin m, ∑ d : Fin m,
        (x a * x b * x c * x d) * (D a b c d + D a c b d + D a d b c) := by
      apply Finset.sum_nonneg; intro a _
      apply Finset.sum_nonneg; intro b _
      apply Finset.sum_nonneg; intro c _
      apply Finset.sum_nonneg; intro d _
      exact mul_nonneg (mul_nonneg (mul_nonneg (hx a) (hx b)) (hx c)) (hx d) |> fun h =>
        mul_nonneg h (hD_triple_nn a b c d)
    linarith
  -- Step 3: Cauchy-Schwarz (ip f Hhat)^2 ≤ ip f f * ip Hhat Hhat ≤ (Ihat * ip f f)^2!
  have hcs := ip_cauchy_schwarz f Hhat
  have hsq : (ip f Hhat) ^ 2 ≤ (Ihat * ip f f) ^ 2 := by
    calc (ip f Hhat) ^ 2 ≤ ip f f * ip Hhat Hhat := hcs
      _ ≤ ip f f * (Ihat ^ 2 * ip f f) := mul_le_mul_of_nonneg_left (by linarith) (ip_self_nonneg f)
      _ = (Ihat * ip f f) ^ 2 := by ring
  have hle : ip f Hhat ≤ Ihat * ip f f := by
    have hnn : 0 ≤ Ihat * ip f f := mul_nonneg hIhat_nn (ip_self_nonneg f)
    nlinarith [sq_nonneg (Ihat * ip f f - ip f Hhat)]
  linarith

/-! ### Part 5: Weighted Dirichlet forms, lift `lift1`, Kron reduction, and induction on `n` -/

private noncomputable def dir1 {n : ℕ} (c : Fin n → Fin n → ℝ) (g : Fin n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i : Fin n, ∑ j : Fin n, c i j * (g i - g j) ^ 2

private noncomputable def dirK {n k : ℕ} (c : Fin n → Fin n → ℝ) (f : TokenVert (Fin n) k → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i : Fin n, ∑ j : Fin n, c i j * (ip f f - ip f (swapOp i j f))

private lemma dirK_nonneg {n k : ℕ} (c : Fin n → Fin n → ℝ) (hc : ∀ i j, 0 ≤ c i j)
    (f : TokenVert (Fin n) k → ℝ) : 0 ≤ dirK c f := by
  unfold dirK
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg; intro i _
  apply Finset.sum_nonneg; intro j _
  have hsq : 0 ≤ ∑ S : TokenVert (Fin n) k, (f S - swapOp i j f S) ^ 2 :=
    Finset.sum_nonneg fun S _ => sq_nonneg _
  rw [sum_sq_sub_swapOp] at hsq
  exact mul_nonneg (hc i j) (by linarith)

private lemma dirK_eq_sum_sq {n k : ℕ} (c : Fin n → Fin n → ℝ) (f : TokenVert (Fin n) k → ℝ) :
    dirK c f = (1 / 4 : ℝ) * ∑ i : Fin n, ∑ j : Fin n,
      c i j * ∑ S : TokenVert (Fin n) k, (f S - swapOp i j f S) ^ 2 := by
  unfold dirK
  simp_rw [sum_sq_sub_swapOp, ← mul_assoc]
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1; ext i
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1; ext j; ring

private lemma tokenAdj_iff_exists_swap {n k : ℕ} (G : SimpleGraph (Fin n))
    (S T : TokenVert (Fin n) k) :
    (tokenGraph G k).Adj S T ↔
      ∃ i j : Fin n, G.Adj i j ∧ i ∈ S.val ∧ j ∉ S.val ∧ permToken (Equiv.swap i j) S = T := by
  constructor
  · rintro ⟨u, v, huv, hsd⟩
    have huv_ne : u ≠ v := huv.ne
    have hsd_mem : ∀ x, x ∈ symmDiff S.val T.val ↔ (x ∈ S.val ∧ x ∉ T.val) ∨ (x ∈ T.val ∧ x ∉ S.val) :=
      fun x => Finset.mem_symmDiff
    have hu_sd : u ∈ symmDiff S.val T.val := by rw [hsd]; simp
    have hv_sd : v ∈ symmDiff S.val T.val := by rw [hsd]; simp
    have hnot_both : ∀ (A B : Finset (Fin n)), A.card = B.card → symmDiff A B = {u, v} →
        ¬ (u ∈ A ∧ u ∉ B ∧ v ∈ A ∧ v ∉ B) := by
      intro A B hcard hsd' ⟨huA, huB, hvA, hvB⟩
      have hsub : B ⊆ (A.erase u).erase v := by
        intro x hxB
        have hxA : x ∈ A := by
          by_contra hxnA
          have hxsd : x ∈ symmDiff A B := Finset.mem_symmDiff.mpr (Or.inr ⟨hxB, hxnA⟩)
          rw [hsd'] at hxsd
          simp only [Finset.mem_insert, Finset.mem_singleton] at hxsd
          rcases hxsd with rfl | rfl <;> contradiction
        exact Finset.mem_erase.mpr ⟨fun h => hvB (h ▸ hxB), Finset.mem_erase.mpr ⟨fun h => huB (h ▸ hxB), hxA⟩⟩
      have hc := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨huv_ne.symm, hvA⟩),
          Finset.card_erase_of_mem huA, hcard] at hc
      have h2 : 2 ≤ A.card := by
        have := Finset.card_le_card (show ({u, v} : Finset (Fin n)) ⊆ A by
          intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption)
        rwa [Finset.card_pair huv_ne] at this
      omega
    have hswap_eq : ∀ a b : Fin n, a ≠ b → a ∈ S.val → a ∉ T.val → b ∈ T.val → b ∉ S.val →
        symmDiff S.val T.val = {a, b} → permToken (Equiv.swap a b) S = T := by
      intro a b hab haS haT hbT hbS hsd'
      ext x
      simp only [permToken, Finset.mem_map, Equiv.coe_toEmbedding]
      constructor
      · rintro ⟨y, hyS, rfl⟩
        by_cases h1 : y = a
        · subst h1; simpa using hbT
        by_cases h2 : y = b
        · exact absurd (h2 ▸ hyS) hbS
        rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
        by_contra hynT
        have hysd : y ∈ symmDiff S.val T.val := (hsd_mem y).mpr (Or.inl ⟨hyS, hynT⟩)
        rw [hsd'] at hysd; simp [h1, h2] at hysd
      · intro hxT
        by_cases h1 : x = a
        · exact absurd (h1 ▸ hxT) haT
        by_cases h2 : x = b
        · subst h2; exact ⟨a, haS, by simp⟩
        have hxS : x ∈ S.val := by
          by_contra hxnS
          have hxsd : x ∈ symmDiff S.val T.val := (hsd_mem x).mpr (Or.inr ⟨hxT, hxnS⟩)
          rw [hsd'] at hxsd; simp [h1, h2] at hxsd
        exact ⟨x, hxS, Equiv.swap_apply_of_ne_of_ne h1 h2⟩
    rcases (hsd_mem u).mp hu_sd with ⟨huS, huT⟩ | ⟨huT, huS⟩
    · rcases (hsd_mem v).mp hv_sd with ⟨hvS, hvT⟩ | ⟨hvT, hvS⟩
      · exact absurd ⟨huS, huT, hvS, hvT⟩ (hnot_both S.val T.val (S.property.trans T.property.symm) hsd)
      · exact ⟨u, v, huv, huS, hvS, hswap_eq u v huv_ne huS huT hvT hvS hsd⟩
    · rcases (hsd_mem v).mp hv_sd with ⟨hvS, hvT⟩ | ⟨hvT, hvS⟩
      · exact ⟨v, u, huv.symm, hvS, huS, hswap_eq v u huv_ne.symm hvS hvT huT huS (by rw [hsd, Finset.pair_comm])⟩
      · exact absurd ⟨huT, huS, hvT, hvS⟩ (hnot_both T.val S.val (T.property.trans S.property.symm) (by rwa [symmDiff_comm]))
  · rintro ⟨i, j, hij, hiS, hjS, rfl⟩
    refine ⟨i, j, hij, ?_⟩
    ext x
    simp only [Finset.mem_symmDiff, permToken, Finset.mem_map, Equiv.coe_toEmbedding,
      Finset.mem_insert, Finset.mem_singleton]
    by_cases hxi : x = i
    · subst x
      simp only [true_or, iff_true]
      left; refine ⟨hiS, ?_⟩
      rintro ⟨y, hyS, hy⟩
      have : y = j := by
        have := congrArg (Equiv.swap i j) hy
        simpa using this
      exact hjS (this ▸ hyS)
    by_cases hxj : x = j
    · subst hxj
      simp only [or_true, iff_true]
      right; exact ⟨⟨i, hiS, by simp⟩, hjS⟩
    simp only [hxi, hxj, or_self, iff_false, not_or, not_and, not_not]
    constructor
    · intro hxS; exact ⟨x, hxS, Equiv.swap_apply_of_ne_of_ne hxi hxj⟩
    · rintro ⟨y, hyS, hy⟩
      have h1 : y ≠ i := by intro h; subst h; simp at hy; exact hxj hy.symm
      have h2 : y ≠ j := by intro h; subst h; simp at hy; exact hxi hy.symm
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2] at hy
      exact hy ▸ hyS

private lemma permToken_swap_inj {n k : ℕ} (S : TokenVert (Fin n) k)
    {i₁ j₁ i₂ j₂ : Fin n} (hi₁ : i₁ ∈ S.val) (hj₁ : j₁ ∉ S.val)
    (hi₂ : i₂ ∈ S.val) (hj₂ : j₂ ∉ S.val)
    (heq : permToken (Equiv.swap i₁ j₁) S = permToken (Equiv.swap i₂ j₂) S) :
    i₁ = i₂ ∧ j₁ = j₂ := by
  have h1 : j₁ ∈ (permToken (Equiv.swap i₁ j₁) S).val :=
    Finset.mem_map.mpr ⟨i₁, hi₁, by simp⟩
  rw [heq] at h1
  obtain ⟨y, hyS, hy⟩ := Finset.mem_map.mp h1
  simp only [Equiv.coe_toEmbedding] at hy
  have hj12 : j₁ = j₂ := by
    by_cases hya : y = i₂
    · subst hya; simpa using hy.symm
    by_cases hyb : y = j₂
    · exact absurd (hyb ▸ hyS) hj₂
    rw [Equiv.swap_apply_of_ne_of_ne hya hyb] at hy
    exact absurd (hy ▸ hyS) hj₁
  subst hj12
  have h2 : i₁ ∉ (permToken (Equiv.swap i₁ j₁) S).val := by
    rintro hmem
    obtain ⟨z, hzS, hz⟩ := Finset.mem_map.mp hmem
    have : z = j₁ := by
      have := congrArg (Equiv.swap i₁ j₁) hz
      simpa using this
    exact hj₁ (this ▸ hzS)
  rw [heq] at h2
  have hi12 : i₁ = i₂ := by
    by_contra hne
    have hne' : i₁ ≠ j₁ := fun h => hj₁ (h ▸ hi₁)
    apply h2
    exact Finset.mem_map.mpr ⟨i₁, hi₁, Equiv.swap_apply_of_ne_of_ne hne hne'⟩
  exact ⟨hi12, rfl⟩

private lemma dirK_eq_laplacianForm {n k : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel (tokenGraph G k).Adj] (f : TokenVert (Fin n) k → ℝ) :
    dirK (fun i j => if G.Adj i j then 1 else 0) f = laplacianForm (tokenGraph G k) f := by
  rw [dirK_eq_sum_sq]
  unfold laplacianForm
  have hreord :
      (∑ i : Fin n, ∑ j : Fin n, (if G.Adj i j then (1 : ℝ) else 0) *
        ∑ S : TokenVert (Fin n) k, (f S - swapOp i j f S) ^ 2) =
      2 * ∑ S : TokenVert (Fin n) k, ∑ T : TokenVert (Fin n) k,
        if (tokenGraph G k).Adj S T then (f S - f T) ^ 2 else 0 := by
    have h1 : (∑ i : Fin n, ∑ j : Fin n, (if G.Adj i j then (1 : ℝ) else 0) *
        ∑ S : TokenVert (Fin n) k, (f S - swapOp i j f S) ^ 2) =
        ∑ S : TokenVert (Fin n) k, ∑ i : Fin n, ∑ j : Fin n,
          if G.Adj i j then (f S - swapOp i j f S) ^ 2 else 0 := by
      trans (∑ i : Fin n, ∑ S : TokenVert (Fin n) k, ∑ j : Fin n,
          if G.Adj i j then (f S - swapOp i j f S) ^ 2 else 0)
      · congr 1; ext i
        trans (∑ j : Fin n, ∑ S : TokenVert (Fin n) k,
            if G.Adj i j then (f S - swapOp i j f S) ^ 2 else 0)
        · congr 1; ext j; rw [Finset.mul_sum]; congr 1; ext S; split_ifs <;> ring
        · exact Finset.sum_comm
      · exact Finset.sum_comm
    rw [h1, Finset.mul_sum]
    congr 1; ext S
    have hsplit : ∀ i j : Fin n,
        (if G.Adj i j then (f S - swapOp i j f S) ^ 2 else 0) =
        (if G.Adj i j ∧ i ∈ S.val ∧ j ∉ S.val then (f S - swapOp i j f S) ^ 2 else 0) +
        (if G.Adj i j ∧ j ∈ S.val ∧ i ∉ S.val then (f S - swapOp i j f S) ^ 2 else 0) := by
      intro i j
      by_cases hij : G.Adj i j
      · by_cases hi : i ∈ S.val <;> by_cases hj : j ∈ S.val
        · have hfix : permToken (Equiv.swap i j) S = S := by
            ext x; simp only [permToken, Finset.mem_map, Equiv.coe_toEmbedding]
            constructor
            · rintro ⟨y, hy, rfl⟩
              by_cases h1 : y = i
              · subst h1; simpa using hj
              by_cases h2 : y = j
              · subst h2; simpa using hi
              rwa [Equiv.swap_apply_of_ne_of_ne h1 h2]
            · intro hx
              refine ⟨Equiv.swap i j x, ?_, by simp⟩
              by_cases h1 : x = i
              · subst h1; simpa using hj
              by_cases h2 : x = j
              · subst h2; simpa using hi
              rwa [Equiv.swap_apply_of_ne_of_ne h1 h2]
          simp [hij, hi, hj, swapOp, hfix]
        · simp [hij, hi, hj]
        · simp [hij, hi, hj]
        · have hfix : permToken (Equiv.swap i j) S = S := by
            ext x; simp only [permToken, Finset.mem_map, Equiv.coe_toEmbedding]
            constructor
            · rintro ⟨y, hy, rfl⟩
              have h1 : y ≠ i := fun h => hi (h ▸ hy)
              have h2 : y ≠ j := fun h => hj (h ▸ hy)
              rwa [Equiv.swap_apply_of_ne_of_ne h1 h2]
            · intro hx
              have h1 : x ≠ i := fun h => hi (h ▸ hx)
              have h2 : x ≠ j := fun h => hj (h ▸ hx)
              exact ⟨x, hx, Equiv.swap_apply_of_ne_of_ne h1 h2⟩
          simp [hij, hi, hj, swapOp, hfix]
      · simp [hij]
    simp_rw [hsplit, Finset.sum_add_distrib]
    have hsym2 : (∑ i : Fin n, ∑ j : Fin n, if G.Adj i j ∧ j ∈ S.val ∧ i ∉ S.val then (f S - swapOp i j f S) ^ 2 else 0) =
        ∑ i : Fin n, ∑ j : Fin n, if G.Adj i j ∧ i ∈ S.val ∧ j ∉ S.val then (f S - swapOp i j f S) ^ 2 else 0 := by
      rw [Finset.sum_comm]
      congr 1; ext i; congr 1; ext j
      have hiff : (G.Adj j i ∧ i ∈ S.val ∧ j ∉ S.val) ↔ (G.Adj i j ∧ i ∈ S.val ∧ j ∉ S.val) :=
        ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, h2⟩, fun ⟨h1, h2⟩ => ⟨h1.symm, h2⟩⟩
      by_cases h : G.Adj i j ∧ i ∈ S.val ∧ j ∉ S.val
      · simp [hiff.mpr h, h, swapOp_comm]
      · simp [mt hiff.mp h, h]
    rw [hsym2, ← two_mul]
    congr 1
    rw [← Finset.sum_product']
    simp_rw [← Finset.sum_filter]
    refine Finset.sum_nbij (fun p : Fin n × Fin n => permToken (Equiv.swap p.1 p.2) S) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hp ⊢
      exact (tokenAdj_iff_exists_swap G S _).mpr ⟨p.1, p.2, hp.1, hp.2.1, hp.2.2, rfl⟩
    · intro p₁ hp₁ p₂ hp₂ heq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hp₁ hp₂
      have ⟨h1, h2⟩ := permToken_swap_inj S hp₁.2.1 hp₁.2.2 hp₂.2.1 hp₂.2.2 heq
      exact Prod.ext h1 h2
    · intro T hT
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hT
      obtain ⟨i, j, hij, hiS, hjS, rfl⟩ := (tokenAdj_iff_exists_swap G S T).mp hT
      exact ⟨(i, j), Finset.mem_coe.mpr (Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, hij, hiS, hjS⟩), rfl⟩
    · intro p _; rfl
  rw [hreord]; ring

private lemma dir1_eq_laplacianForm {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (g : Fin n → ℝ) :
    dir1 (fun i j => if G.Adj i j then 1 else 0) g = laplacianForm G g := by
  unfold dir1 laplacianForm
  congr 1; congr 1; ext i; congr 1; ext j
  by_cases h : G.Adj i j <;> simp [h]

/-! ### Part 5B: Lift of 1-particle functions, explicit projection, and Kron reduction -/

private def lift1 {n k : ℕ} (g : Fin n → ℝ) (S : TokenVert (Fin n) k) : ℝ :=
  ∑ i ∈ S.val, g i

private lemma card_tokenVert_mem {n k : ℕ} (i : Fin n) (hk : 1 ≤ k) :
    (Finset.univ.filter (fun S : TokenVert (Fin n) k => i ∈ S.val)).card =
      (n - 1).choose (k - 1) := by
  let e : { S : TokenVert (Fin n) k // i ∈ S.val } ≃ { T : Finset { x : Fin n // x ≠ i } // T.card = k - 1 } :=
    { toFun := fun S => ⟨(S.val.val.erase i).subtype (fun x => x ≠ i), by
        rw [Finset.card_subtype, Finset.filter_true_of_mem (fun x hx => (Finset.mem_erase.mp hx).1),
            Finset.card_erase_of_mem S.property, S.val.property]⟩
      invFun := fun T => ⟨⟨(T.val.map (Function.Embedding.subtype _)).cons i (by
          simp only [Finset.mem_map, Function.Embedding.coe_subtype, not_exists, not_and]
          intro x _ hx; exact x.property hx), by
        rw [Finset.card_cons, Finset.card_map, T.property]; omega⟩, by simp⟩
      left_inv := fun S => by
        apply Subtype.ext; apply Subtype.ext; ext x
        simp only [Finset.mem_cons, Finset.mem_map, Finset.mem_subtype, Finset.mem_erase,
          Function.Embedding.coe_subtype]
        constructor
        · rintro (rfl | ⟨y, ⟨_, hyS⟩, rfl⟩)
          · exact S.property
          · exact hyS
        · intro hxS
          by_cases hxi : x = i
          · exact Or.inl hxi
          · exact Or.inr ⟨⟨x, hxi⟩, ⟨hxi, hxS⟩, rfl⟩
      right_inv := fun T => by
        apply Subtype.ext; ext x
        simp only [Finset.mem_subtype, Finset.mem_erase, Finset.mem_cons, Finset.mem_map,
          Function.Embedding.coe_subtype]
        constructor
        · rintro ⟨hx, h | ⟨y, hyT, hy⟩⟩
          · exact absurd h hx
          · exact Subtype.ext hy ▸ hyT
        · intro hxT
          exact ⟨x.property, Or.inr ⟨x, hxT, rfl⟩⟩ }
  rw [← Fintype.card_subtype, Fintype.card_congr e]
  have hcard : Fintype.card { x : Fin n // x ≠ i } = n - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fin]
  have hpow : Fintype.card { T : Finset { x : Fin n // x ≠ i } // T.card = k - 1 } =
      (Finset.powersetCard (k - 1) (Finset.univ : Finset { x : Fin n // x ≠ i })).card := by
    rw [← Fintype.card_coe]
    refine Fintype.card_congr ⟨fun T => ⟨T.val, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, T.property⟩⟩,
      fun T => ⟨T.val, (Finset.mem_powersetCard.mp T.property).2⟩, fun _ => rfl, fun _ => rfl⟩
  rw [hpow, Finset.card_powersetCard, Finset.card_univ, hcard]

private lemma card_tokenVert_mem_notMem {n k : ℕ} {i j : Fin n} (hij : i ≠ j) (hk : 1 ≤ k) (_hkn : k ≤ n - 1) :
    (Finset.univ.filter (fun S : TokenVert (Fin n) k => i ∈ S.val ∧ j ∉ S.val)).card =
      (n - 2).choose (k - 1) := by
  let P : Fin n → Prop := fun x => x ≠ i ∧ x ≠ j
  let e : { S : TokenVert (Fin n) k // i ∈ S.val ∧ j ∉ S.val } ≃
      { T : Finset { x : Fin n // P x } // T.card = k - 1 } :=
    { toFun := fun S => ⟨(S.val.val.erase i).subtype P, by
        rw [Finset.card_subtype, Finset.filter_true_of_mem (fun x hx =>
          ⟨(Finset.mem_erase.mp hx).1, fun h => S.property.2 (h ▸ (Finset.mem_erase.mp hx).2)⟩),
          Finset.card_erase_of_mem S.property.1, S.val.property]⟩
      invFun := fun T => ⟨⟨(T.val.map (Function.Embedding.subtype _)).cons i (by
          simp only [Finset.mem_map, Function.Embedding.coe_subtype, not_exists, not_and]
          intro x _ hx; exact x.property.1 hx), by
        rw [Finset.card_cons, Finset.card_map, T.property]; omega⟩,
        by simp, by
          simp only [Finset.mem_cons, Finset.mem_map, Function.Embedding.coe_subtype, not_or,
            not_exists, not_and]
          exact ⟨hij.symm, fun x _ hx => x.property.2 hx⟩⟩
      left_inv := fun S => by
        apply Subtype.ext; apply Subtype.ext; ext x
        simp only [Finset.mem_cons, Finset.mem_map, Finset.mem_subtype, Finset.mem_erase,
          Function.Embedding.coe_subtype]
        constructor
        · rintro (rfl | ⟨y, ⟨_, hyS⟩, rfl⟩)
          · exact S.property.1
          · exact hyS
        · intro hxS
          by_cases hxi : x = i
          · exact Or.inl hxi
          · exact Or.inr ⟨⟨x, hxi, fun h => S.property.2 (h ▸ hxS)⟩, ⟨hxi, hxS⟩, rfl⟩
      right_inv := fun T => by
        apply Subtype.ext; ext x
        simp only [Finset.mem_subtype, Finset.mem_erase, Finset.mem_cons, Finset.mem_map,
          Function.Embedding.coe_subtype]
        constructor
        · rintro ⟨hx, h | ⟨y, hyT, hy⟩⟩
          · exact absurd h hx
          · exact Subtype.ext hy ▸ hyT
        · intro hxT
          exact ⟨x.property.1, Or.inr ⟨x, hxT, rfl⟩⟩ }
  rw [← Fintype.card_subtype, Fintype.card_congr e]
  have hcard : Fintype.card { x : Fin n // P x } = n - 2 := by
    have hcompl : (Finset.univ.filter P) = (Finset.univ : Finset (Fin n)) \ {i, j} := by
      ext x; simp [P]
    rw [Fintype.card_subtype, hcompl, Finset.card_sdiff, Finset.inter_univ,
        Finset.card_univ, Fintype.card_fin, Finset.card_pair hij]
  have hpow : Fintype.card { T : Finset { x : Fin n // P x } // T.card = k - 1 } =
      (Finset.powersetCard (k - 1) (Finset.univ : Finset { x : Fin n // P x })).card := by
    rw [← Fintype.card_coe]
    refine Fintype.card_congr ⟨fun T => ⟨T.val, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, T.property⟩⟩,
      fun T => ⟨T.val, (Finset.mem_powersetCard.mp T.property).2⟩, fun _ => rfl, fun _ => rfl⟩
  rw [hpow, Finset.card_powersetCard, Finset.card_univ, hcard]

private lemma card_tokenVert_mem_mem {n k : ℕ} {i j : Fin n} (hij : i ≠ j) (hk : 1 ≤ k) (hkn : k ≤ n - 1) :
    ((Finset.univ.filter (fun S : TokenVert (Fin n) k => i ∈ S.val ∧ j ∈ S.val)).card : ℝ) =
      ((n - 1).choose (k - 1) : ℝ) - ((n - 2).choose (k - 1) : ℝ) := by
  have hdisj : Disjoint
      (Finset.univ.filter (fun S : TokenVert (Fin n) k => i ∈ S.val ∧ j ∈ S.val))
      (Finset.univ.filter (fun S : TokenVert (Fin n) k => i ∈ S.val ∧ j ∉ S.val)) := by
    rw [Finset.disjoint_filter]; intro S _ h1 h2; exact h2.2 h1.2
  have hunion :
      (Finset.univ.filter (fun S : TokenVert (Fin n) k => i ∈ S.val ∧ j ∈ S.val)) ∪
      (Finset.univ.filter (fun S : TokenVert (Fin n) k => i ∈ S.val ∧ j ∉ S.val)) =
      Finset.univ.filter (fun S : TokenVert (Fin n) k => i ∈ S.val) := by
    ext S; simp; tauto
  have hc := Finset.card_union_of_disjoint hdisj
  rw [hunion, card_tokenVert_mem i hk, card_tokenVert_mem_notMem hij hk hkn] at hc
  have hcast : ((Finset.univ.filter (fun S : TokenVert (Fin n) k => i ∈ S.val ∧ j ∈ S.val)).card : ℝ) +
      ((n - 2).choose (k - 1) : ℝ) = ((n - 1).choose (k - 1) : ℝ) := by
    exact_mod_cast hc.symm
  linarith

private lemma sum_lift1 {n k : ℕ} (hk : 1 ≤ k) (g : Fin n → ℝ) :
    ∑ S : TokenVert (Fin n) k, lift1 g S = ((n - 1).choose (k - 1) : ℝ) * ∑ i : Fin n, g i := by
  unfold lift1
  have h1 : ∑ S : TokenVert (Fin n) k, ∑ i ∈ S.val, g i =
      ∑ S : TokenVert (Fin n) k, ∑ i : Fin n, if i ∈ S.val then g i else 0 := by
    congr 1; ext S; rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [h1, Finset.sum_comm, Finset.mul_sum]
  congr 1; ext i
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, card_tokenVert_mem i hk]

private lemma sum_mem_lift1 {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n - 1) (g : Fin n → ℝ)
    (hg0 : ∑ i : Fin n, g i = 0) (i : Fin n) :
    ∑ S ∈ Finset.univ.filter (fun S : TokenVert (Fin n) k => i ∈ S.val), lift1 g S =
      ((n - 2).choose (k - 1) : ℝ) * g i := by
  unfold lift1
  have h1 : ∀ S : TokenVert (Fin n) k, ∑ j ∈ S.val, g j = ∑ j : Fin n, if j ∈ S.val then g j else 0 :=
    fun S => by rw [Finset.sum_ite_mem, Finset.univ_inter]
  simp_rw [h1]
  rw [Finset.sum_comm]
  have hterm : ∀ j : Fin n,
      (∑ S ∈ Finset.univ.filter (fun S : TokenVert (Fin n) k => i ∈ S.val),
        if j ∈ S.val then g j else 0) =
      (if i = j then ((n - 1).choose (k - 1) : ℝ)
       else ((n - 1).choose (k - 1) : ℝ) - ((n - 2).choose (k - 1) : ℝ)) * g j := by
    intro j
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Finset.filter_filter]
    by_cases hij : i = j
    · subst hij
      simp only [and_self, ↓reduceIte, card_tokenVert_mem i hk]
    · simp only [hij, ↓reduceIte]
      rw [card_tokenVert_mem_mem hij hk hkn]
  simp_rw [hterm]
  have hsplit : ∀ j : Fin n,
      (if i = j then ((n - 1).choose (k - 1) : ℝ)
       else ((n - 1).choose (k - 1) : ℝ) - ((n - 2).choose (k - 1) : ℝ)) * g j =
      (((n - 1).choose (k - 1) : ℝ) - ((n - 2).choose (k - 1) : ℝ)) * g j +
      (if i = j then ((n - 2).choose (k - 1) : ℝ) * g j else 0) := by
    intro j; split_ifs <;> ring
  simp_rw [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum, hg0, mul_zero, zero_add]
  simp

private lemma ip_lift1 {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n - 1) (g h : Fin n → ℝ)
    (hh0 : ∑ i : Fin n, h i = 0) :
    ip (lift1 (k := k) g) (lift1 (k := k) h) = ((n - 2).choose (k - 1) : ℝ) * ip g h := by
  unfold ip
  have h1 : ∀ S : TokenVert (Fin n) k, lift1 g S * lift1 h S =
      ∑ i : Fin n, if i ∈ S.val then g i * lift1 h S else 0 := by
    intro S; unfold lift1
    rw [Finset.sum_mul]
    symm
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  simp_rw [h1]
  rw [Finset.sum_comm, Finset.mul_sum]
  congr 1; ext i
  rw [← Finset.sum_filter, ← Finset.mul_sum, sum_mem_lift1 hk hkn h hh0 i]
  ring

private lemma lift1_sub_swapOp {n k : ℕ} (g : Fin n → ℝ) (i j : Fin n) (S : TokenVert (Fin n) k) :
    lift1 g S - swapOp i j (lift1 g) S =
      if i ∈ S.val ∧ j ∉ S.val then g i - g j
      else if j ∈ S.val ∧ i ∉ S.val then g j - g i
      else 0 := by
  unfold lift1 swapOp permToken
  dsimp only
  rw [Finset.sum_map]
  simp only [Equiv.coe_toEmbedding]
  have hdiff : ∑ x ∈ S.val, g x - ∑ x ∈ S.val, g (Equiv.swap i j x) =
      ∑ x ∈ S.val, (g x - g (Equiv.swap i j x)) := (Finset.sum_sub_distrib _ _).symm
  rw [hdiff]
  have hzero : ∀ x ∈ S.val, x ≠ i → x ≠ j → g x - g (Equiv.swap i j x) = 0 := by
    intro x _ h1 h2; rw [Equiv.swap_apply_of_ne_of_ne h1 h2, sub_self]
  by_cases hi : i ∈ S.val <;> by_cases hj : j ∈ S.val
  · simp only [hi, hj, not_true_eq_false, and_false, ↓reduceIte]
    by_cases hij : i = j
    · subst hij; simp
    · have hsub : ({i, j} : Finset (Fin n)) ⊆ S.val := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      rw [← Finset.sum_subset hsub (fun x hx hnot => hzero x hx (fun h => hnot (by simp [h])) (fun h => hnot (by simp [h])))]
      rw [Finset.sum_pair hij]; simp
  · simp only [hi, hj, not_false_eq_true, and_true, ↓reduceIte]
    have hsub : ({i} : Finset (Fin n)) ⊆ S.val := Finset.singleton_subset_iff.mpr hi
    rw [← Finset.sum_subset hsub (fun x hx hnot => hzero x hx (by simpa using hnot) (fun h => hj (h ▸ hx)))]
    simp
  · simp only [hi, hj, not_false_eq_true, and_true, false_and, ↓reduceIte]
    have hsub : ({j} : Finset (Fin n)) ⊆ S.val := Finset.singleton_subset_iff.mpr hj
    rw [← Finset.sum_subset hsub (fun x hx hnot => hzero x hx (fun h => hi (h ▸ hx)) (by simpa using hnot))]
    simp
  · simp only [hi, hj, false_and, ↓reduceIte]
    exact Finset.sum_eq_zero fun x hx => hzero x hx (fun h => hi (h ▸ hx)) (fun h => hj (h ▸ hx))

private lemma dirK_lift1 {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n - 1)
    (c : Fin n → Fin n → ℝ) (g : Fin n → ℝ) :
    dirK c (lift1 (k := k) g) = ((n - 2).choose (k - 1) : ℝ) * dir1 c g := by
  rw [dirK_eq_sum_sq]
  unfold dir1
  rw [← mul_assoc, mul_comm ((n - 2).choose (k - 1) : ℝ) (1 / 2 : ℝ), mul_assoc, Finset.mul_sum]
  have hterm : ∀ i j : Fin n,
      (∑ S : TokenVert (Fin n) k, (lift1 g S - swapOp i j (lift1 g) S) ^ 2) =
      2 * ((n - 2).choose (k - 1) : ℝ) * (g i - g j) ^ 2 := by
    intro i j
    by_cases hij : i = j
    · subst hij; simp [swapOp_self]
    · simp_rw [lift1_sub_swapOp]
      have hsq : ∀ S : TokenVert (Fin n) k,
          (if i ∈ S.val ∧ j ∉ S.val then g i - g j
           else if j ∈ S.val ∧ i ∉ S.val then g j - g i else 0) ^ 2 =
          (if i ∈ S.val ∧ j ∉ S.val then (g i - g j) ^ 2 else 0) +
          (if j ∈ S.val ∧ i ∉ S.val then (g i - g j) ^ 2 else 0) := by
        intro S
        by_cases h1 : i ∈ S.val <;> by_cases h2 : j ∈ S.val <;> (simp [h1, h2]; try ring)
      simp_rw [hsq, Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
          card_tokenVert_mem_notMem hij hk hkn, card_tokenVert_mem_notMem (Ne.symm hij) hk hkn]
      ring
  simp_rw [hterm]
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1; ext i
  rw [← mul_assoc, Finset.mul_sum, Finset.mul_sum]
  congr 1; ext j; ring

private lemma dirK_add_orthog_lift1 {n k : ℕ} (c : Fin n → Fin n → ℝ)
    (g : Fin n → ℝ) (f₂ : TokenVert (Fin n) k → ℝ)
    (horth : ∀ i : Fin n, ∑ S ∈ Finset.univ.filter (fun S : TokenVert (Fin n) k => i ∈ S.val), f₂ S = 0) :
    dirK c (fun S => lift1 g S + f₂ S) = dirK c (lift1 (k := k) g) + dirK c f₂ := by
  rw [dirK_eq_sum_sq, dirK_eq_sum_sq, dirK_eq_sum_sq]
  have hcross : ∀ i j : Fin n,
      ∑ S : TokenVert (Fin n) k, ((lift1 g S + f₂ S) - swapOp i j (fun S => lift1 g S + f₂ S) S) ^ 2 =
      ∑ S : TokenVert (Fin n) k, (lift1 g S - swapOp i j (lift1 g) S) ^ 2 +
      ∑ S : TokenVert (Fin n) k, (f₂ S - swapOp i j f₂ S) ^ 2 := by
    intro i j
    have hexp : ∀ S : TokenVert (Fin n) k,
        ((lift1 g S + f₂ S) - swapOp i j (fun S => lift1 g S + f₂ S) S) ^ 2 =
        (lift1 g S - swapOp i j (lift1 g) S) ^ 2 + (f₂ S - swapOp i j f₂ S) ^ 2 +
        2 * ((lift1 g S - swapOp i j (lift1 g) S) * (f₂ S - swapOp i j f₂ S)) := by
      intro S; simp only [swapOp]; ring
    simp_rw [hexp, Finset.sum_add_distrib, ← Finset.mul_sum]
    have h0 : ∑ S : TokenVert (Fin n) k, (lift1 g S - swapOp i j (lift1 g) S) * (f₂ S - swapOp i j f₂ S) = 0 := by
      have h1 : ∀ S, (lift1 g S - swapOp i j (lift1 g) S) * (f₂ S - swapOp i j f₂ S) =
          (lift1 g S - swapOp i j (lift1 g) S) * f₂ S -
          (lift1 g S - swapOp i j (lift1 g) S) * swapOp i j f₂ S := fun S => by ring
      simp_rw [h1, Finset.sum_sub_distrib]
      have hpart : ∀ (h : TokenVert (Fin n) k → ℝ),
          (∀ r : Fin n, ∑ S ∈ Finset.univ.filter (fun S : TokenVert (Fin n) k => r ∈ S.val), h S = 0) →
          ∑ S : TokenVert (Fin n) k, (lift1 g S - swapOp i j (lift1 g) S) * h S = 0 := by
        intro h hh
        simp_rw [lift1_sub_swapOp]
        have hsp : ∀ S : TokenVert (Fin n) k,
            (if i ∈ S.val ∧ j ∉ S.val then g i - g j
             else if j ∈ S.val ∧ i ∉ S.val then g j - g i else 0) * h S =
            (g i - g j) * ((if i ∈ S.val then h S else 0) - (if j ∈ S.val then h S else 0)) := by
          intro S; by_cases hi : i ∈ S.val <;> by_cases hj : j ∈ S.val <;> (simp [hi, hj]; try ring)
        simp_rw [hsp, ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_filter, hh i, hh j]
        ring
      have hswap_orth : ∀ r : Fin n,
          ∑ S ∈ Finset.univ.filter (fun S : TokenVert (Fin n) k => r ∈ S.val), swapOp i j f₂ S = 0 := by
        intro r
        have hmem : ∀ S : TokenVert (Fin n) k,
            r ∈ S.val ↔ Equiv.swap i j r ∈ (permToken (Equiv.swap i j) S).val := by
          intro S; simp only [permToken, Finset.mem_map, Equiv.coe_toEmbedding]
          exact ⟨fun hr => ⟨r, hr, rfl⟩, fun ⟨x, hx, h⟩ => (Equiv.swap i j).injective h ▸ hx⟩
        have hrew : (∑ S ∈ Finset.univ.filter (fun S : TokenVert (Fin n) k => r ∈ S.val), swapOp i j f₂ S) =
            ∑ S : TokenVert (Fin n) k, if Equiv.swap i j r ∈ (permToken (Equiv.swap i j) S).val then f₂ (permToken (Equiv.swap i j) S) else 0 := by
          rw [Finset.sum_filter]
          congr 1; ext S; simp only [swapOp, hmem S]
        rw [hrew]
        change (∑ S : TokenVert (Fin n) k,
            if Equiv.swap i j r ∈ (permTokenEquiv (Equiv.swap i j) S).val then
              f₂ (permTokenEquiv (Equiv.swap i j) S) else 0) = 0
        rw [Equiv.sum_comp (permTokenEquiv (Equiv.swap i j))
            (fun S => if Equiv.swap i j r ∈ S.val then f₂ S else 0)]
        rw [← Finset.sum_filter]
        exact horth (Equiv.swap i j r)
      rw [hpart f₂ horth, hpart (swapOp i j f₂) hswap_orth, sub_self]
    rw [h0]; ring
  simp_rw [hcross, mul_add, Finset.sum_add_distrib]
  ring

private lemma kron_gap {m : ℕ} (c : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hc_sym : ∀ i j, c i j = c j i) (hc_diag : ∀ i, c i i = 0)
    (hC_pos : 0 < ∑ i : Fin m, c 0 i.succ)
    (lam : ℝ) (hlam_nn : 0 ≤ lam)
    (hgap : ∀ g : Fin (m + 1) → ℝ, (∑ i : Fin (m + 1), g i) = 0 → lam * ip g g ≤ dir1 c g) :
    let C := ∑ i : Fin m, c 0 i.succ
    let c' : Fin m → Fin m → ℝ := fun i j => if i = j then 0 else c i.succ j.succ + c 0 i.succ * c 0 j.succ / C
    ∀ h : Fin m → ℝ, (∑ i : Fin m, h i) = 0 → lam * ip h h ≤ dir1 c' h := by
  intro C c' h hh0
  have hCne : C ≠ 0 := ne_of_gt hC_pos
  -- Harmonic extension g of h at vertex 0: g 0 = (1/C) ∑_i c(0, i.succ) h(i), g(i.succ) = h(i)
  let g0 : ℝ := (∑ i : Fin m, c 0 i.succ * h i) / C
  let g : Fin (m + 1) → ℝ := Fin.cons g0 h
  let mean : ℝ := g0 / ((m + 1 : ℕ) : ℝ)
  let gc : Fin (m + 1) → ℝ := fun v => g v - mean
  have hgc_sum : ∑ v : Fin (m + 1), gc v = 0 := by
    simp only [gc, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Fin.sum_univ_succ, g, Fin.cons_zero, Fin.cons_succ, hh0, add_zero, mean]
    have hm1 : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  -- Step 1: dir1 c gc = dir1 c g = dir1 c' h!
  have hdir_shift : dir1 c gc = dir1 c g := by
    unfold dir1; congr 1; congr 1; ext i; congr 1; ext j
    simp only [gc]; ring
  have hdir_kron : dir1 c g = dir1 c' h := by
    unfold dir1
    rw [Fin.sum_univ_succ]
    simp_rw [Fin.sum_univ_succ]
    simp only [g, Fin.cons_zero, Fin.cons_succ, hc_diag 0, zero_mul, zero_add]
    have hsym_row : ∑ i : Fin m, c i.succ 0 * (h i - g0) ^ 2 = ∑ i : Fin m, c 0 i.succ * (g0 - h i) ^ 2 := by
      congr 1; ext i; rw [hc_sym i.succ 0]; ring
    simp_rw [Finset.sum_add_distrib]
    rw [hsym_row]
    -- Exact Schur complement identity:
    -- ∑_i c_i (g0 - h_i)^2 = (1 / (2C)) ∑_{i, j} c_i c_j (h_i - h_j)^2!
    have hschur : 2 * ∑ i : Fin m, c 0 i.succ * (g0 - h i) ^ 2 =
        ∑ i : Fin m, ∑ j : Fin m, (c 0 i.succ * c 0 j.succ / C) * (h i - h j) ^ 2 := by
      have h1 : ∑ i : Fin m, c 0 i.succ * (g0 - h i) ^ 2 =
          ∑ i : Fin m, c 0 i.succ * h i ^ 2 - C * g0 ^ 2 := by
        have hexp : ∀ i : Fin m, c 0 i.succ * (g0 - h i) ^ 2 =
            c 0 i.succ * h i ^ 2 - 2 * g0 * (c 0 i.succ * h i) + g0 ^ 2 * c 0 i.succ := fun i => by ring
        simp_rw [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
        have hsum_ch : ∑ i : Fin m, c 0 i.succ * h i = C * g0 := by
          simp only [g0]; field_simp
        rw [hsum_ch]
        simp only [C]; ring
      have h2 : ∑ i : Fin m, ∑ j : Fin m, (c 0 i.succ * c 0 j.succ / C) * (h i - h j) ^ 2 =
          2 * (∑ i : Fin m, c 0 i.succ * h i ^ 2 - C * g0 ^ 2) := by
        have hexp : ∀ i j : Fin m, (c 0 i.succ * c 0 j.succ / C) * (h i - h j) ^ 2 =
            (c 0 j.succ / C) * (c 0 i.succ * h i ^ 2) + (c 0 i.succ / C) * (c 0 j.succ * h j ^ 2) -
            (2 / C) * ((c 0 i.succ * h i) * (c 0 j.succ * h j)) := fun i j => by ring
        simp_rw [hexp, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
        have hsum_div : ∑ i : Fin m, c 0 i.succ / C = 1 := by
          rw [← Finset.sum_div, div_self hCne]
        have hsum_ch : ∑ i : Fin m, c 0 i.succ * h i = C * g0 := by
          simp only [g0]; field_simp
        rw [hsum_div, hsum_ch]
        field_simp; ring
      linarith
    have hc'_expand : ∑ i : Fin m, ∑ j : Fin m, c' i j * (h i - h j) ^ 2 =
        ∑ i : Fin m, ∑ j : Fin m, c i.succ j.succ * (h i - h j) ^ 2 +
        ∑ i : Fin m, ∑ j : Fin m, (c 0 i.succ * c 0 j.succ / C) * (h i - h j) ^ 2 := by
      rw [← Finset.sum_add_distrib]
      congr 1; ext i; rw [← Finset.sum_add_distrib]
      congr 1; ext j
      simp only [c']
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]; ring
    rw [hc'_expand, ← hschur]; ring
  -- Step 2: ip h h ≤ ip gc gc!
  have hip_ge : ip h h ≤ ip gc gc := by
    unfold ip
    rw [Fin.sum_univ_succ]
    simp only [gc, g, Fin.cons_zero, Fin.cons_succ]
    have h2 : ∑ i : Fin m, (h i - mean) * (h i - mean) =
        ∑ i : Fin m, h i * h i + (m : ℝ) * mean ^ 2 := by
      have hexp : ∀ i : Fin m, (h i - mean) * (h i - mean) = h i * h i - 2 * mean * h i + mean ^ 2 :=
        fun i => by ring
      simp_rw [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hh0,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [h2]
    have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith [sq_nonneg (g0 - mean), sq_nonneg mean]
  calc lam * ip h h ≤ lam * ip gc gc := mul_le_mul_of_nonneg_left hip_ge hlam_nn
    _ ≤ dir1 c gc := hgap gc hgc_sum
    _ = dir1 c' h := by rw [hdir_shift, hdir_kron]

/-! ### Part 5C: Main inductive theorem `dirK_ge_lambda` -/

private lemma dirK_ge_lambda :
    ∀ (n : ℕ), 2 ≤ n →
    ∀ (k : ℕ), 1 ≤ k → k ≤ n - 1 →
    ∀ (c : Fin n → Fin n → ℝ),
      (∀ i j, 0 ≤ c i j) → (∀ i j, c i j = c j i) → (∀ i, c i i = 0) →
    ∀ (lam : ℝ), 0 ≤ lam →
      (∀ g : Fin n → ℝ, (∑ i : Fin n, g i) = 0 → lam * ip g g ≤ dir1 c g) →
      ∀ f : TokenVert (Fin n) k → ℝ, (∑ S : TokenVert (Fin n) k, f S) = 0 →
        lam * ip f f ≤ dirK c f := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ m ih =>
    intro hm1 k hk hkm c hc_nn hc_sym hc_diag lam hlam_nn hgap f hf0
    by_cases hm2 : m = 1
    · -- Base case n = 2, k = 1: TokenVert (Fin 2) 1 ≃ Fin 2!
      subst hm2
      have hk1 : k = 1 := by omega
      subst hk1
      let e : Fin 2 ≃ TokenVert (Fin 2) 1 :=
        { toFun := fun i => ⟨{i}, Finset.card_singleton i⟩
          invFun := fun S => Classical.choose (Finset.card_eq_one.mp S.property)
          left_inv := fun i => by
            have h := Classical.choose_spec (Finset.card_eq_one.mp (Finset.card_singleton i))
            exact Finset.singleton_injective h.symm
          right_inv := fun S => Subtype.ext (Classical.choose_spec (Finset.card_eq_one.mp S.property)).symm }
      let g : Fin 2 → ℝ := fun i => f (e i)
      have hg0 : ∑ i : Fin 2, g i = 0 := by
        simpa [g] using (Equiv.sum_comp e f).trans hf0
      have hip_eq : ip f f = ip g g := (Equiv.sum_comp e (fun S => f S * f S)).symm
      have hdir_eq : dirK c f = dir1 c g := by
        rw [dirK_eq_sum_sq]
        unfold dir1
        have hterm : ∀ i j : Fin 2,
            (∑ S : TokenVert (Fin 2) 1, (f S - swapOp i j f S) ^ 2) = 2 * (g i - g j) ^ 2 := by
          intro i j
          rw [← Equiv.sum_comp e]
          have hact : ∀ r : Fin 2, swapOp i j f (e r) = g (Equiv.swap i j r) := by
            intro r; apply congrArg f; ext x; simp [permToken, e]
          simp_rw [hact]
          fin_cases i <;> fin_cases j <;> (simp [Fin.sum_univ_two, g]; try ring)
        simp_rw [hterm]
        rw [Finset.mul_sum, Finset.mul_sum]
        congr 1; ext i; rw [Finset.mul_sum, Finset.mul_sum]; congr 1; ext j; ring
      rw [hip_eq, hdir_eq]
      exact hgap g hg0
    · -- Inductive step: m ≥ 2 (so n = m + 1 ≥ 3)!
      have hm_ge2 : 2 ≤ m := by omega
      -- Step 1: Decompose f = lift1 g_f + f₂ where g_f i = (1 / C(m-1, k-1)) ∑_{S ∋ i} f S!
      have hchoose_pos : (0 : ℝ) < ((m - 1).choose (k - 1) : ℝ) := by
        exact_mod_cast Nat.choose_pos (by omega : k - 1 ≤ m - 1)
      let g : Fin (m + 1) → ℝ := fun i =>
        (∑ S ∈ Finset.univ.filter (fun S : TokenVert (Fin (m + 1)) k => i ∈ S.val), f S) /
          ((m - 1).choose (k - 1) : ℝ)
      let f₁ : TokenVert (Fin (m + 1)) k → ℝ := lift1 g
      let f₂ : TokenVert (Fin (m + 1)) k → ℝ := fun S => f S - f₁ S
      have hg0 : ∑ i : Fin (m + 1), g i = 0 := by
        simp only [g, ← Finset.sum_div]
        have hnum : ∑ i : Fin (m + 1),
            ∑ S ∈ Finset.univ.filter (fun S : TokenVert (Fin (m + 1)) k => i ∈ S.val), f S = 0 := by
          simp_rw [Finset.sum_filter]
          rw [Finset.sum_comm]
          have hinner : ∀ S : TokenVert (Fin (m + 1)) k,
              (∑ i : Fin (m + 1), if i ∈ S.val then f S else 0) = (k : ℝ) * f S := by
            intro S
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
            have : (Finset.univ.filter (fun i : Fin (m + 1) => i ∈ S.val)) = S.val := by
              ext i; simp
            rw [this, S.property]
          simp_rw [hinner, ← Finset.mul_sum, hf0, mul_zero]
        rw [hnum, zero_div]
      have hf₂_orth : ∀ i : Fin (m + 1),
          ∑ S ∈ Finset.univ.filter (fun S : TokenVert (Fin (m + 1)) k => i ∈ S.val), f₂ S = 0 := by
        intro i
        simp only [f₂, Finset.sum_sub_distrib, f₁]
        rw [sum_mem_lift1 hk hkm g hg0 i]
        have hm12 : m + 1 - 2 = m - 1 := by omega
        rw [hm12]
        simp only [g]
        have hne : ((m - 1).choose (k - 1) : ℝ) ≠ 0 := ne_of_gt hchoose_pos
        field_simp; ring
      have hf₂_sum : ∑ S : TokenVert (Fin (m + 1)) k, f₂ S = 0 := by
        simp only [f₂, Finset.sum_sub_distrib, hf0, f₁, sum_lift1 hk g, hg0, mul_zero, sub_self]
      have hf_eq : f = fun S => lift1 g S + f₂ S := by ext S; simp [f₂, f₁]
      have hip_split : ip f f = ip f₁ f₁ + ip f₂ f₂ := by
        have hcross : ip f₁ f₂ = 0 := by
          unfold ip f₁ lift1
          have h1 : ∀ S : TokenVert (Fin (m + 1)) k, (∑ i ∈ S.val, g i) * f₂ S =
              ∑ i : Fin (m + 1), if i ∈ S.val then g i * f₂ S else 0 := by
            intro S; rw [Finset.sum_mul]; symm; rw [Finset.sum_ite_mem, Finset.univ_inter]
          simp_rw [h1]
          rw [Finset.sum_comm]
          exact Finset.sum_eq_zero fun i _ => by
            rw [← Finset.sum_filter, ← Finset.mul_sum, hf₂_orth i, mul_zero]
        rw [hf_eq, ip_add_left, ip_add_right, ip_add_right]
        change ip f₁ f₁ + ip f₁ f₂ + (ip f₂ f₁ + ip f₂ f₂) = ip f₁ f₁ + ip f₂ f₂
        rw [ip_comm f₂ f₁, hcross]; ring
      have hdir_split : dirK c f = dirK c f₁ + dirK c f₂ := by
        rw [hf_eq]; exact dirK_add_orthog_lift1 c g f₂ hf₂_orth
      -- Bound on f₁ = lift1 g:
      have hbound1 : lam * ip f₁ f₁ ≤ dirK c f₁ := by
        simp only [f₁]
        rw [ip_lift1 hk hkm g g hg0, dirK_lift1 hk hkm c g]
        have hm12 : m + 1 - 2 = m - 1 := by omega
        rw [hm12]
        have hle := hgap g hg0
        nlinarith [hchoose_pos]
      -- Bound on f₂:
      have hbound2 : lam * ip f₂ f₂ ≤ dirK c f₂ := by
        let C : ℝ := ∑ i : Fin m, c 0 i.succ
        by_cases hC0 : C = 0
        · -- If C = 0, then vertex 0 is isolated, so lam = 0!
          have hci0 : ∀ i : Fin m, c 0 i.succ = 0 := by
            intro i
            have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hc_nn 0 j.succ)).mp hC0 i (Finset.mem_univ i)
            exact this
          have hlam0 : lam = 0 := by
            let g0 : Fin (m + 1) → ℝ := Fin.cons (m : ℝ) (fun _ => -1)
            have hg0_sum : ∑ i : Fin (m + 1), g0 i = 0 := by
              rw [Fin.sum_univ_succ]; simp [g0]
            have hdir0 : dir1 c g0 = 0 := by
              unfold dir1
              rw [Fin.sum_univ_succ]
              simp_rw [Fin.sum_univ_succ]
              simp only [g0, Fin.cons_zero, Fin.cons_succ, hc_diag 0, hci0, zero_mul, sub_self,
                ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
                Finset.sum_const_zero, add_zero]
              have : ∀ i : Fin m, c i.succ 0 = 0 := fun i => by rw [hc_sym]; exact hci0 i
              simp [this]
            have hip0 : 0 < ip g0 g0 := by
              unfold ip; rw [Fin.sum_univ_succ]; simp only [g0, Fin.cons_zero, Fin.cons_succ]
              have : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
              have hsum : ∑ _ : Fin m, (-1 : ℝ) * (-1) = (m : ℝ) := by simp
              rw [hsum]; positivity
            have hle := hgap g0 hg0_sum
            rw [hdir0] at hle
            nlinarith
          rw [hlam0, zero_mul]
          exact dirK_nonneg c hc_nn f₂
        · -- C > 0! Apply Octopus Inequality + Kron reduction + IH!
          have hC_pos : 0 < C := lt_of_le_of_ne (Finset.sum_nonneg fun i _ => hc_nn 0 i.succ) (Ne.symm hC0)
          let c' : Fin m → Fin m → ℝ := fun i j =>
            if i = j then 0 else c i.succ j.succ + c 0 i.succ * c 0 j.succ / C
          have hc'_nn : ∀ i j, 0 ≤ c' i j := by
            intro i j; simp only [c']; split_ifs
            · exact le_rfl
            · exact add_nonneg (hc_nn _ _) (div_nonneg (mul_nonneg (hc_nn _ _) (hc_nn _ _)) (le_of_lt hC_pos))
          have hc'_sym : ∀ i j, c' i j = c' j i := by
            intro i j; simp only [c']
            by_cases hij : i = j
            · subst hij; simp
            · simp [hij, Ne.symm hij, hc_sym i.succ j.succ, mul_comm]
          have hc'_diag : ∀ i, c' i i = 0 := fun i => by simp [c']
          have hgap' : ∀ h : Fin m → ℝ, (∑ i : Fin m, h i) = 0 → lam * ip h h ≤ dir1 c' h :=
            kron_gap c hc_sym hc_diag hC_pos lam hlam_nn hgap
          -- Octopus inequality gives: dirK c f₂ ≥ dirK^{V'} c' f₂!
          have hoct :
              (1 / 2 : ℝ) * ∑ i : Fin m, ∑ j : Fin m, c' i j * (ip f₂ f₂ - ip f₂ (swapOp i.succ j.succ f₂)) ≤
              dirK c f₂ := by
            have hdir_exp : dirK c f₂ =
                (∑ i : Fin m, c 0 i.succ * (ip f₂ f₂ - ip f₂ (swapOp i.succ 0 f₂))) +
                (1 / 2 : ℝ) * ∑ i : Fin m, ∑ j : Fin m, c i.succ j.succ * (ip f₂ f₂ - ip f₂ (swapOp i.succ j.succ f₂)) := by
              unfold dirK
              rw [Fin.sum_univ_succ]
              simp_rw [Fin.sum_univ_succ]
              simp only [hc_diag 0, zero_mul, zero_add]
              rw [Finset.sum_add_distrib]
              have hsym_col : ∑ i : Fin m, c i.succ 0 * (ip f₂ f₂ - ip f₂ (swapOp i.succ 0 f₂)) =
                  ∑ i : Fin m, c 0 i.succ * (ip f₂ f₂ - ip f₂ (swapOp 0 i.succ f₂)) := by
                congr 1; ext i; rw [hc_sym i.succ 0, swapOp_comm i.succ 0]
              have hsym_0 : ∑ i : Fin m, c 0 i.succ * (ip f₂ f₂ - ip f₂ (swapOp 0 i.succ f₂)) =
                  ∑ i : Fin m, c 0 i.succ * (ip f₂ f₂ - ip f₂ (swapOp i.succ 0 f₂)) := by
                congr 1; ext i; rw [swapOp_comm 0 i.succ]
              rw [hsym_col, hsym_0]; ring
            have hc'_exp :
                (1 / 2 : ℝ) * ∑ i : Fin m, ∑ j : Fin m, c' i j * (ip f₂ f₂ - ip f₂ (swapOp i.succ j.succ f₂)) =
                (1 / 2 : ℝ) * ∑ i : Fin m, ∑ j : Fin m, c i.succ j.succ * (ip f₂ f₂ - ip f₂ (swapOp i.succ j.succ f₂)) +
                ((1 / 2 : ℝ) * ∑ i : Fin m, ∑ j : Fin m,
                  c 0 i.succ * c 0 j.succ * (ip f₂ f₂ - ip f₂ (swapOp i.succ j.succ f₂))) / C := by
              have hterm : ∀ i j : Fin m,
                  c' i j * (ip f₂ f₂ - ip f₂ (swapOp i.succ j.succ f₂)) =
                  c i.succ j.succ * (ip f₂ f₂ - ip f₂ (swapOp i.succ j.succ f₂)) +
                  (c 0 i.succ * c 0 j.succ * (ip f₂ f₂ - ip f₂ (swapOp i.succ j.succ f₂))) / C := by
                intro i j; simp only [c']
                by_cases hij : i = j
                · subst hij; simp [swapOp_self]
                · simp [hij]; ring
              simp_rw [hterm, Finset.sum_add_distrib, ← Finset.sum_div]
              ring
            rw [hdir_exp, hc'_exp]
            have hoct_raw := octopus_ineq (fun i : Fin m => c 0 i.succ) (fun i => hc_nn 0 i.succ) f₂
            have hdiv_le : ((1 / 2 : ℝ) * ∑ i : Fin m, ∑ j : Fin m,
                c 0 i.succ * c 0 j.succ * (ip f₂ f₂ - ip f₂ (swapOp i.succ j.succ f₂))) / C ≤
                ∑ i : Fin m, c 0 i.succ * (ip f₂ f₂ - ip f₂ (swapOp i.succ 0 f₂)) := by
              rw [div_le_iff₀ hC_pos]
              simpa [C, mul_comm] using hoct_raw
            linarith
          -- Split TokenVert (Fin (m+1)) k into 0 ∈ S (≃ TokenVert (Fin m) (k-1)) and 0 ∉ S (≃ TokenVert (Fin m) k)!
          let embPlus : TokenVert (Fin m) (k - 1) → TokenVert (Fin (m + 1)) k := fun A =>
            ⟨(A.val.map ⟨Fin.succ, Fin.succ_injective _⟩).cons 0 (by simp), by
              rw [Finset.card_cons, Finset.card_map, A.property]; omega⟩
          let embMinus : TokenVert (Fin m) k → TokenVert (Fin (m + 1)) k := fun A =>
            ⟨A.val.map ⟨Fin.succ, Fin.succ_injective _⟩, by rw [Finset.card_map, A.property]⟩
          let eSplit : TokenVert (Fin m) (k - 1) ⊕ TokenVert (Fin m) k ≃ TokenVert (Fin (m + 1)) k :=
            { toFun := Sum.elim embPlus embMinus
              invFun := fun S =>
                if h0 : (0 : Fin (m + 1)) ∈ S.val then
                  Sum.inl ⟨Finset.univ.filter (fun i : Fin m => i.succ ∈ S.val), by
                    have hmap : (Finset.univ.filter (fun i : Fin m => i.succ ∈ S.val)).map ⟨Fin.succ, Fin.succ_injective _⟩ =
                        S.val.erase 0 := by
                      ext x; simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
                        Function.Embedding.coeFn_mk, Finset.mem_erase]
                      refine Fin.cases ?_ (fun i => ?_) x
                      · simp
                      · simp [Fin.succ_ne_zero]
                    have hc := congrArg Finset.card hmap
                    rw [Finset.card_map, Finset.card_erase_of_mem h0, S.property] at hc
                    exact hc⟩
                else
                  Sum.inr ⟨Finset.univ.filter (fun i : Fin m => i.succ ∈ S.val), by
                    have hmap : (Finset.univ.filter (fun i : Fin m => i.succ ∈ S.val)).map ⟨Fin.succ, Fin.succ_injective _⟩ =
                        S.val := by
                      ext x; simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
                        Function.Embedding.coeFn_mk]
                      refine Fin.cases ?_ (fun i => ?_) x
                      · simp [h0]
                      · simp
                    have hc := congrArg Finset.card hmap
                    rw [Finset.card_map, S.property] at hc
                    exact hc⟩
              left_inv := fun x => by
                rcases x with A | A
                · simp only [Sum.elim_inl, embPlus, Finset.mem_cons_self, ↓reduceDIte]
                  congr 1; ext i; simp [Fin.succ_ne_zero]
                · have h0 : (0 : Fin (m + 1)) ∉ (embMinus A).val := by simp [embMinus]
                  simp only [Sum.elim_inr, h0, ↓reduceDIte]
                  congr 1; ext i; simp [embMinus]
              right_inv := fun S => by
                by_cases h0 : (0 : Fin (m + 1)) ∈ S.val
                · simp only [h0, ↓reduceDIte, Sum.elim_inl]
                  ext x; refine Fin.cases ?_ (fun i => ?_) x
                  · simp [embPlus, h0]
                  · simp [embPlus, Fin.succ_ne_zero]
                · simp only [h0, ↓reduceDIte, Sum.elim_inr]
                  ext x; refine Fin.cases ?_ (fun i => ?_) x
                  · simp [embMinus, h0]
                  · simp [embMinus] }
          let fP : TokenVert (Fin m) (k - 1) → ℝ := fun A => f₂ (embPlus A)
          let fM : TokenVert (Fin m) k → ℝ := fun A => f₂ (embMinus A)
          have hswap_P : ∀ (i j : Fin m) (A : TokenVert (Fin m) (k - 1)),
              permToken (Equiv.swap i.succ j.succ) (embPlus A) = embPlus (permToken (Equiv.swap i j) A) := by
            intro i j A; ext x; refine Fin.cases ?_ (fun r => ?_) x
            · simp only [permToken, embPlus, Finset.mem_map, Finset.mem_cons,
                Function.Embedding.coeFn_mk, true_or, iff_true]
              exact ⟨0, Or.inl rfl, Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero i).symm (Fin.succ_ne_zero j).symm⟩
            · simp only [permToken, embPlus, Finset.mem_map, Finset.mem_cons,
                Function.Embedding.coeFn_mk, Fin.succ_ne_zero, false_or]
              constructor
              · rintro ⟨y, rfl | ⟨a, haA, rfl⟩, hy⟩
                · rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero i).symm (Fin.succ_ne_zero j).symm] at hy
                  exact absurd hy.symm (Fin.succ_ne_zero r)
                · refine ⟨Equiv.swap i j a, ⟨a, haA, rfl⟩, ?_⟩
                  by_cases h1 : a = i
                  · subst h1; simpa using hy
                  by_cases h2 : a = j
                  · subst h2; simpa using hy
                  rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
                  rw [Equiv.swap_apply_of_ne_of_ne (fun h => h1 (Fin.succ_injective _ h))
                      (fun h => h2 (Fin.succ_injective _ h))] at hy
                  exact hy
              · rintro ⟨b, ⟨a, haA, rfl⟩, hb⟩
                refine ⟨a.succ, Or.inr ⟨a, haA, rfl⟩, ?_⟩
                by_cases h1 : a = i
                · subst h1; simpa using hb
                by_cases h2 : a = j
                · subst h2; simpa using hb
                rw [Equiv.swap_apply_of_ne_of_ne (fun h => h1 (Fin.succ_injective _ h))
                    (fun h => h2 (Fin.succ_injective _ h))]
                rw [Equiv.swap_apply_of_ne_of_ne h1 h2] at hb
                exact hb
          have hswap_M : ∀ (i j : Fin m) (A : TokenVert (Fin m) k),
              permToken (Equiv.swap i.succ j.succ) (embMinus A) = embMinus (permToken (Equiv.swap i j) A) := by
            intro i j A; ext x; refine Fin.cases ?_ (fun r => ?_) x
            · simp only [permToken, embMinus, Finset.mem_map,
                Function.Embedding.coeFn_mk, Fin.succ_ne_zero, and_false, exists_false, iff_false]
              rintro ⟨y, ⟨a, _, rfl⟩, hy⟩
              by_cases hia : a = i
              · subst hia; simp at hy
              by_cases hja : a = j
              · subst hja; simp at hy
              rw [Equiv.swap_apply_of_ne_of_ne (fun h => hia (Fin.succ_injective _ h))
                  (fun h => hja (Fin.succ_injective _ h))] at hy
              exact Fin.succ_ne_zero a hy
            · simp only [permToken, embMinus, Finset.mem_map,
                Function.Embedding.coeFn_mk]
              constructor
              · rintro ⟨y, ⟨a, haA, rfl⟩, hy⟩
                refine ⟨Equiv.swap i j a, ⟨a, haA, rfl⟩, ?_⟩
                by_cases h1 : a = i
                · subst h1; simpa using hy
                by_cases h2 : a = j
                · subst h2; simpa using hy
                rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
                rw [Equiv.swap_apply_of_ne_of_ne (fun h => h1 (Fin.succ_injective _ h))
                    (fun h => h2 (Fin.succ_injective _ h))] at hy
                exact hy
              · rintro ⟨b, ⟨a, haA, rfl⟩, hb⟩
                refine ⟨a.succ, ⟨a, haA, rfl⟩, ?_⟩
                by_cases h1 : a = i
                · subst h1; simpa using hb
                by_cases h2 : a = j
                · subst h2; simpa using hb
                rw [Equiv.swap_apply_of_ne_of_ne (fun h => h1 (Fin.succ_injective _ h))
                    (fun h => h2 (Fin.succ_injective _ h))]
                rw [Equiv.swap_apply_of_ne_of_ne h1 h2] at hb
                exact hb
          have hip2_split : ip f₂ f₂ = ip fP fP + ip fM fM := by
            unfold ip
            rw [← Equiv.sum_comp eSplit (fun S => f₂ S * f₂ S), Fintype.sum_sum_type]
            rfl
          have hdir2_split :
              (1 / 2 : ℝ) * ∑ i : Fin m, ∑ j : Fin m, c' i j * (ip f₂ f₂ - ip f₂ (swapOp i.succ j.succ f₂)) =
              dirK c' fP + dirK c' fM := by
            unfold dirK
            rw [← mul_add, ← Finset.sum_add_distrib]
            congr 1; congr 1; ext i; rw [← Finset.sum_add_distrib]
            congr 1; ext j
            have hip_sw : ip f₂ (swapOp i.succ j.succ f₂) =
                ip fP (swapOp i j fP) + ip fM (swapOp i j fM) := by
              unfold ip
              rw [← Equiv.sum_comp eSplit (fun S => f₂ S * swapOp i.succ j.succ f₂ S), Fintype.sum_sum_type]
              congr 1
              · congr 1; ext A; simp [eSplit, fP, swapOp, hswap_P]
              · congr 1; ext A; simp [eSplit, fM, swapOp, hswap_M]
            rw [hip2_split, hip_sw]; ring
          -- Both fP and fM have mean zero because hf₂_orth 0 and hf₂_sum!
          have hfP_sum : ∑ A : TokenVert (Fin m) (k - 1), fP A = 0 := by
            have h0 := hf₂_orth 0
            rw [Finset.sum_filter] at h0
            rw [← Equiv.sum_comp eSplit (fun S => if (0 : Fin (m + 1)) ∈ S.val then f₂ S else 0),
                Fintype.sum_sum_type] at h0
            have h1 : ∀ A : TokenVert (Fin m) (k - 1), (0 : Fin (m + 1)) ∈ (eSplit (Sum.inl A)).val :=
              fun A => by simp [eSplit, embPlus]
            have h2 : ∀ A : TokenVert (Fin m) k, (0 : Fin (m + 1)) ∉ (eSplit (Sum.inr A)).val :=
              fun A => by simp [eSplit, embMinus]
            simp only [h1, h2, ↓reduceIte, Finset.sum_const_zero, add_zero] at h0
            exact h0
          have hfM_sum : ∑ A : TokenVert (Fin m) k, fM A = 0 := by
            have hall := hf₂_sum
            rw [← Equiv.sum_comp eSplit f₂, Fintype.sum_sum_type] at hall
            change (∑ A, fP A) + (∑ A, fM A) = 0 at hall
            linarith
          -- Apply IH to fP (k - 1 tokens) and fM (k tokens)!
          have hP_le : lam * ip fP fP ≤ dirK c' fP := by
            by_cases hk1 : k = 1
            · subst hk1
              -- k - 1 = 0: TokenVert (Fin m) 0 has unique element ∅, so fP = 0!
              have h0 : ∀ A : TokenVert (Fin m) 0, A = ⟨∅, Finset.card_empty⟩ := fun A =>
                Subtype.ext (Finset.card_eq_zero.mp A.property)
              have huniv : (Finset.univ : Finset (TokenVert (Fin m) 0)) = {⟨∅, Finset.card_empty⟩} := by
                ext A; simp [h0 A]
              rw [huniv, Finset.sum_singleton] at hfP_sum
              have hip0 : ip fP fP = 0 := by
                unfold ip; rw [huniv, Finset.sum_singleton, hfP_sum, mul_zero]
              rw [hip0, mul_zero]
              exact dirK_nonneg c' hc'_nn fP
            · exact ih hm_ge2 (k - 1) (by omega) (by omega) c' hc'_nn hc'_sym hc'_diag lam hlam_nn hgap' fP hfP_sum
          have hM_le : lam * ip fM fM ≤ dirK c' fM := by
            by_cases hkm_eq : k = m
            · subst k
              -- k = m: TokenVert (Fin m) m has unique element univ, so fM = 0!
              have h0 : ∀ A : TokenVert (Fin m) m, A = ⟨Finset.univ, by simp⟩ := fun A =>
                Subtype.ext (Finset.eq_univ_of_card A.val (by simpa using A.property))
              have huniv : (Finset.univ : Finset (TokenVert (Fin m) m)) = {⟨Finset.univ, by simp⟩} := by
                ext A; simp [h0 A]
              rw [huniv, Finset.sum_singleton] at hfM_sum
              have hip0 : ip fM fM = 0 := by
                unfold ip; rw [huniv, Finset.sum_singleton, hfM_sum, mul_zero]
              rw [hip0, mul_zero]
              exact dirK_nonneg c' hc'_nn fM
            · exact ih hm_ge2 k hk (by omega) c' hc'_nn hc'_sym hc'_diag lam hlam_nn hgap' fM hfM_sum
          rw [hip2_split, mul_add]
          linarith
      rw [hip_split, mul_add, hdir_split]
      linarith

/-! ### Part 6: Main Theorem `algebraicConnectivity (tokenGraph G k) = algebraicConnectivity G` -/

private theorem main_proof : type_of% @OMA.S_arxiv_2012_00808.main := by
  intro n k hk hkn G _ _
  have hn2 : 2 ≤ n := by omega
  let c : Fin n → Fin n → ℝ := fun i j => if G.Adj i j then 1 else 0
  have hc_nn : ∀ i j, 0 ≤ c i j := fun i j => by simp only [c]; split_ifs <;> norm_num
  have hc_sym : ∀ i j, c i j = c j i := fun i j => by
    simp only [c]
    by_cases h : G.Adj i j
    · simp [h, h.symm]
    · have h' : ¬ G.Adj j i := fun hji => h hji.symm
      simp [h, h']
  have hc_diag : ∀ i, c i i = 0 := fun i => by simp [c]
  let S_G : Set ℝ := { r : ℝ | ∃ g : Fin n → ℝ, (∑ w : Fin n, g w) = 0 ∧
    (∑ w : Fin n, g w ^ 2) = 1 ∧ r = laplacianForm G g }
  let S_F : Set ℝ := { r : ℝ | ∃ f : TokenVert (Fin n) k → ℝ, (∑ w : TokenVert (Fin n) k, f w) = 0 ∧
    (∑ w : TokenVert (Fin n) k, f w ^ 2) = 1 ∧ r = laplacianForm (tokenGraph G k) f }
  have hSG_ne : S_G.Nonempty := by
    let g : Fin n → ℝ := fun i =>
      if i = ⟨0, by omega⟩ then (1 / Real.sqrt 2)
      else if i = ⟨1, by omega⟩ then -(1 / Real.sqrt 2)
      else 0
    have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by intro h; simp at h
    refine ⟨laplacianForm G g, g, ?_, ?_, rfl⟩
    · have hsub : ({(⟨0, by omega⟩ : Fin n), ⟨1, by omega⟩} : Finset (Fin n)) ⊆ Finset.univ := Finset.subset_univ _
      rw [← Finset.sum_subset hsub (fun x _ hx => by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
        simp [g, hx.1, hx.2]), Finset.sum_pair h01]
      simp [g, h01.symm]
    · have hsub : ({(⟨0, by omega⟩ : Fin n), ⟨1, by omega⟩} : Finset (Fin n)) ⊆ Finset.univ := Finset.subset_univ _
      rw [← Finset.sum_subset hsub (fun x _ hx => by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
        simp [g, hx.1, hx.2]), Finset.sum_pair h01]
      simp [g, h01.symm, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      ring
  have hSG_bdd : BddBelow S_G := by
    refine ⟨0, ?_⟩
    rintro r ⟨g, _, _, rfl⟩
    rw [← dir1_eq_laplacianForm G g]
    unfold dir1
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (hc_nn i j) (sq_nonneg _))
  have hSF_bdd : BddBelow S_F := by
    refine ⟨0, ?_⟩
    rintro r ⟨f, _, _, rfl⟩
    rw [← dirK_eq_laplacianForm G f]
    exact dirK_nonneg c hc_nn f
  have hSG_sub_SF : S_G ⊆ S_F := by
    rintro r ⟨g, hg0, hg1, rfl⟩
    have hch_pos : (0 : ℝ) < ((n - 2).choose (k - 1) : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega : k - 1 ≤ n - 2)
    let s : ℝ := Real.sqrt ((n - 2).choose (k - 1) : ℝ)
    have hs_sq : s ^ 2 = ((n - 2).choose (k - 1) : ℝ) := Real.sq_sqrt (le_of_lt hch_pos)
    let f : TokenVert (Fin n) k → ℝ := fun S => lift1 g S / s
    refine ⟨f, ?_, ?_, ?_⟩
    · simp only [f, ← Finset.sum_div, sum_lift1 hk g, hg0, mul_zero, zero_div]
    · have hip_eq : ∑ S : TokenVert (Fin n) k, f S ^ 2 = ip (lift1 (k := k) g) (lift1 (k := k) g) / s ^ 2 := by
        simp only [f, div_pow, ← Finset.sum_div]
        simp only [ip, sq]
      rw [hip_eq, ip_lift1 hk hkn g g hg0, hs_sq]
      have hg1' : ip g g = 1 := by simpa [ip, sq] using hg1
      rw [hg1', mul_one, div_self (ne_of_gt hch_pos)]
    · rw [← dir1_eq_laplacianForm G g, ← dirK_eq_laplacianForm G f]
      have hdir_scale : dirK c f = dirK c (lift1 (k := k) g) / s ^ 2 := by
        rw [dirK_eq_sum_sq, dirK_eq_sum_sq]
        have h1 : ∀ i j S, (f S - swapOp i j f S) ^ 2 = (lift1 (k := k) g S - swapOp i j (lift1 (k := k) g) S) ^ 2 / s ^ 2 := by
          intro i j S; simp only [f, swapOp]; rw [← sub_div, div_pow]
        simp_rw [h1, ← Finset.sum_div, ← mul_div_assoc]
        simp_rw [← Finset.sum_div]
        ring
      change dir1 c g = dirK c f
      rw [hdir_scale, dirK_lift1 hk hkn c g, hs_sq, mul_div_cancel_left₀ _ (ne_of_gt hch_pos)]
  have hSF_ne : S_F.Nonempty := hSG_ne.mono hSG_sub_SF
  unfold algebraicConnectivity
  change sInf S_F = sInf S_G
  apply le_antisymm
  · exact csInf_le_csInf hSF_bdd hSG_ne hSG_sub_SF
  · apply le_csInf hSF_ne
    rintro r ⟨f, hf0, hf1, rfl⟩
    rw [← dirK_eq_laplacianForm G f]
    have hlam_nn : 0 ≤ sInf S_G := le_csInf hSG_ne (by
      rintro r' ⟨g, _, _, rfl⟩
      rw [← dir1_eq_laplacianForm G g]
      unfold dir1
      exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        mul_nonneg (hc_nn i j) (sq_nonneg _)))
    have hgap : ∀ g : Fin n → ℝ, (∑ i : Fin n, g i) = 0 → sInf S_G * ip g g ≤ dir1 c g := by
      intro g hg0
      by_cases hip0 : ip g g = 0
      · rw [hip0, mul_zero]
        unfold dir1
        exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
          mul_nonneg (hc_nn i j) (sq_nonneg _))
      · have hip_pos : 0 < ip g g := lt_of_le_of_ne (ip_self_nonneg g) (Ne.symm hip0)
        let r0 : ℝ := Real.sqrt (ip g g)
        have hr0_sq : r0 ^ 2 = ip g g := Real.sq_sqrt (le_of_lt hip_pos)
        let gn : Fin n → ℝ := fun i => g i / r0
        have hgn_mem : laplacianForm G gn ∈ S_G := by
          refine ⟨gn, ?_, ?_, rfl⟩
          · simp only [gn, ← Finset.sum_div, hg0, zero_div]
          · simp only [gn, div_pow, ← Finset.sum_div, hr0_sq]
            have : ∑ w : Fin n, g w ^ 2 = ip g g := by simp [ip, sq]
            rw [this, div_self (ne_of_gt hip_pos)]
        have hle := csInf_le hSG_bdd hgn_mem
        rw [← dir1_eq_laplacianForm G gn] at hle
        have hscale : dir1 c gn = dir1 c g / r0 ^ 2 := by
          unfold dir1
          have h1 : ∀ i j, c i j * (gn i - gn j) ^ 2 = c i j * (g i - g j) ^ 2 / r0 ^ 2 := by
            intro i j; simp only [gn]; rw [← sub_div, div_pow, mul_div_assoc]
          simp_rw [h1, ← Finset.sum_div]
          ring
        rw [hscale, hr0_sq, le_div_iff₀ hip_pos] at hle
        exact hle
    have hbound := dirK_ge_lambda n hn2 k hk hkn c hc_nn hc_sym hc_diag (sInf S_G) hlam_nn hgap f hf0
    have hf1' : ip f f = 1 := by simpa [ip, sq] using hf1
    rw [hf1', mul_one] at hbound
    exact hbound

end OMA.P_arxiv_2012_00808

theorem OMA.solution : type_of% @OMA.S_arxiv_2012_00808.main :=
  OMA.P_arxiv_2012_00808.main_proof
