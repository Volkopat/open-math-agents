import FormalConjectures.ErdosProblems.«490»

/-! Reduction by @Burntgogi. Trim small cofactors on the two sides and separate
their large prime supports. The resulting pairs admit a scale-transfer problem
and a uniform boundedness problem. Classical input: Szemerédi (1976) and
Erdős--Szemerédi (1976) on product-injective pairs. -/

open Filter
open scoped Topology

namespace OMA.R_Erdos490_erdos_490_variants_limit_R1

/-- Arbitrarily small normalized loss suffices to separate the large primes
and to bound each element's small-prime part. -/
def H1 : Prop :=
  let adm := fun (n : ℕ) (A B : Finset ℕ) => A ⊆ Finset.Icc 1 n ∧ B ⊆ Finset.Icc 1 n ∧
    ∀ a ∈ A, ∀ b ∈ B, ∀ a' ∈ A, ∀ b' ∈ B, a*b = a'*b' → a = a' ∧ b = b'
  let sep := fun (Y K : ℕ) (A B : Finset ℕ) =>
    (∀ a ∈ A, ∀ b ∈ B, ∀ p : ℕ, p.Prime → Y ≤ p → p ∣ a → ¬p ∣ b) ∧
    ∀ z ∈ A ∪ B, ∃ u : ℕ, u ≤ K ∧ u ∣ z ∧ ∀ p : ℕ, p.Prime → p ∣ z / u → Y ≤ p
  let val := fun (n : ℕ) (A B : Finset ℕ) => (A.card * B.card : ℝ) * Real.log n / (n : ℝ)^2
  ∀ ε : ℝ, 0 < ε → ∀ᶠ Y : ℕ in atTop, ∃ K : ℕ, ∀ᶠ n : ℕ in atTop,
    ∀ A B : Finset ℕ, adm n A B → ∃ a b : Finset ℕ,
      a ⊆ A ∧ b ⊆ B ∧ sep Y K a b ∧ val n A B ≤ val n a b + ε

/-- Every late separated pair with bounded cofactors can be recovered to the
prescribed accuracy at every sufficiently large new cutoff. -/
def H2 : Prop :=
  let adm := fun (n : ℕ) (A B : Finset ℕ) => A ⊆ Finset.Icc 1 n ∧ B ⊆ Finset.Icc 1 n ∧
    ∀ a ∈ A, ∀ b ∈ B, ∀ a' ∈ A, ∀ b' ∈ B, a*b = a'*b' → a = a' ∧ b = b'
  let sep := fun (Y K : ℕ) (A B : Finset ℕ) =>
    (∀ a ∈ A, ∀ b ∈ B, ∀ p : ℕ, p.Prime → Y ≤ p → p ∣ a → ¬p ∣ b) ∧
    ∀ z ∈ A ∪ B, ∃ u : ℕ, u ≤ K ∧ u ∣ z ∧ ∀ p : ℕ, p.Prime → p ∣ z / u → Y ≤ p
  let val := fun (n : ℕ) (A B : Finset ℕ) => (A.card * B.card : ℝ) * Real.log n / (n : ℝ)^2
  ∀ ε : ℝ, 0 < ε → ∀ᶠ Y : ℕ in atTop, ∀ K : ℕ, ∀ᶠ n : ℕ in atTop,
    ∀ A B : Finset ℕ, adm n A B → sep Y K A B →
      ∀ᶠ m : ℕ in atTop, ∃ a b : Finset ℕ, adm m a b ∧ val n A B ≤ val m a b + ε

/-- Uniform boundedness for each fixed separated class. -/
def H3 : Prop :=
  ∀ Y K : ℕ, ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, ∀ A B : Finset ℕ,
    A ⊆ Finset.Icc 1 n → B ⊆ Finset.Icc 1 n →
    (∀ a ∈ A, ∀ b ∈ B, ∀ p : ℕ, p.Prime → Y ≤ p → p ∣ a → ¬p ∣ b) →
    (∀ z ∈ A ∪ B, ∃ u : ℕ, u ≤ K ∧ u ∣ z ∧ ∀ p : ℕ, p.Prime → p ∣ z / u → Y ≤ p) →
    (A.card * B.card : ℝ) * Real.log n / (n : ℝ)^2 ≤ C

theorem converges_of_transfer (f : ℕ → ℝ) (hb : ∃ C : ℝ, ∀ᶠ n in atTop, f n ≤ C)
    (ht : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ᶠ m in atTop, f n ≤ f m + ε) :
    ∃ c : ℝ, Tendsto f atTop (𝓝 c) := by
  apply cauchySeq_tendsto_of_complete
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨C,hC⟩ := hb
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((ht (ε/3) (by linarith)).and hC)
  let S := {v : ℝ | ∃ n : ℕ, N ≤ n ∧ v = f n}
  have hne : S.Nonempty := ⟨f N,N,le_rfl,rfl⟩
  have hbd : BddAbove S := ⟨C,fun _ ⟨n,hn,he⟩ => he ▸ (hN n hn).2⟩
  obtain ⟨_,⟨n,hn,rfl⟩,hh⟩ := exists_lt_of_lt_csSup hne (show sSup S-ε/3 < sSup S by linarith)
  obtain ⟨M,hM⟩ := eventually_atTop.mp ((hN n hn).1)
  refine ⟨max M N,fun i hi j hj => ?_⟩
  have hi' := hM i ((le_max_left _ _).trans hi)
  have hj' := hM j ((le_max_left _ _).trans hj)
  have hui := le_csSup hbd (show f i ∈ S from ⟨i,(le_max_right _ _).trans hi,rfl⟩)
  have huj := le_csSup hbd (show f j ∈ S from ⟨j,(le_max_right _ _).trans hj,rfl⟩)
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

theorem main : H1 → H2 → H3 → type_of% @Erdos490.erdos_490.variants.limit := by
  classical
  intro trim transfer bound
  let adm := fun (n : ℕ) (A B : Finset ℕ) => A ⊆ Finset.Icc 1 n ∧ B ⊆ Finset.Icc 1 n ∧
    ∀ a ∈ A, ∀ b ∈ B, ∀ a' ∈ A, ∀ b' ∈ B, a*b = a'*b' → a = a' ∧ b = b'
  let sep := fun (Y K : ℕ) (A B : Finset ℕ) =>
    (∀ a ∈ A, ∀ b ∈ B, ∀ p : ℕ, p.Prime → Y ≤ p → p ∣ a → ¬p ∣ b) ∧
    ∀ z ∈ A ∪ B, ∃ u : ℕ, u ≤ K ∧ u ∣ z ∧ ∀ p : ℕ, p.Prime → p ∣ z / u → Y ≤ p
  let val := fun (n : ℕ) (A B : Finset ℕ) => (A.card * B.card : ℝ) * Real.log n / (n : ℝ)^2
  let S (n : ℕ) := {x : ℝ | ∃ A B : Finset ℕ, A ⊆ Finset.Icc 1 n ∧ B ⊆ Finset.Icc 1 n ∧
    (∀ a ∈ A, ∀ b ∈ B, ∀ a' ∈ A, ∀ b' ∈ B, a*b = a'*b' → a = a' ∧ b = b') ∧ x = A.card * B.card}
  have memS (n : ℕ) (x : ℝ) : x ∈ S n ↔ ∃ A B : Finset ℕ, adm n A B ∧ x = A.card * B.card := by
    simp only [S,Set.mem_ofPred_eq,adm,and_assoc]
  let f (n : ℕ) := sSup (S n) * Real.log n / (n : ℝ)^2
  change ∃ c : ℝ, Tendsto f atTop (𝓝 c)
  change ∀ ε : ℝ, 0 < ε → ∀ᶠ Y : ℕ in atTop, ∃ K : ℕ, ∀ᶠ n : ℕ in atTop,
    ∀ A B : Finset ℕ, adm n A B → ∃ a b : Finset ℕ,
      a ⊆ A ∧ b ⊆ B ∧ sep Y K a b ∧ val n A B ≤ val n a b + ε at trim
  change ∀ ε : ℝ, 0 < ε → ∀ᶠ Y : ℕ in atTop, ∀ K : ℕ, ∀ᶠ n : ℕ in atTop,
    ∀ A B : Finset ℕ, adm n A B → sep Y K A B →
      ∀ᶠ m : ℕ in atTop, ∃ a b : Finset ℕ, adm m a b ∧ val n A B ≤ val m a b + ε at transfer
  have small {n} {A B a b : Finset ℕ} (h : adm n A B) (ha : a ⊆ A) (hb : b ⊆ B) : adm n a b :=
    ⟨ha.trans h.1,hb.trans h.2.1,fun _ hx _ hy _ hz _ hw => h.2.2 _ (ha hx) _ (hb hy) _ (ha hz) _ (hb hw)⟩
  have fin (n : ℕ) : (S n).Finite := by
    let P := ((Finset.Icc 1 n).powerset ×ˢ (Finset.Icc 1 n).powerset)
    refine ((P.image (fun ab => ((ab.1.card : ℝ)*ab.2.card))).finite_toSet).subset ?_
    intro x hx
    obtain ⟨A,B,h,rfl⟩ := (memS n x).mp hx
    exact Finset.mem_image.mpr ⟨(A,B),Finset.mem_product.mpr
      ⟨Finset.mem_powerset.mpr h.1,Finset.mem_powerset.mpr h.2.1⟩,rfl⟩
  have attain (n : ℕ) : ∃ A B : Finset ℕ, adm n A B ∧ f n = val n A B := by
    have hem : adm n ∅ ∅ := by simp [adm]
    have hne : (S n).Nonempty := ⟨_,(memS n _).mpr ⟨∅,∅,hem,rfl⟩⟩
    obtain ⟨A,B,ha,hv⟩ := (memS n _).mp (hne.csSup_mem (fin n))
    exact ⟨A,B,ha,congrArg (fun v : ℝ => v * Real.log n / (n : ℝ)^2) hv⟩
  have le_best {n A B} (h : adm n A B) : val n A B ≤ f n := by
    have hle := le_csSup (fin n).bddAbove (show (A.card * B.card : ℝ) ∈ S n from (memS n _).mpr ⟨A,B,h,rfl⟩)
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hle (Real.log_natCast_nonneg n)) (sq_nonneg _)
  apply converges_of_transfer
  · obtain ⟨Y,hy⟩ := (trim 1 (by norm_num)).exists
    obtain ⟨K,hK⟩ := hy
    obtain ⟨C,hC⟩ := bound Y K
    refine ⟨C+1,?_⟩
    filter_upwards [hK,hC] with n ht hc
    obtain ⟨A,B,hab,he⟩ := attain n
    obtain ⟨a,b,ha,hb,hs,hv⟩ := ht A B hab
    have h := hc a b (ha.trans hab.1) (hb.trans hab.2.1) hs.1 hs.2
    change val n a b ≤ C at h
    linarith
  · intro ε hε
    have he : 0 < ε/2 := half_pos hε
    obtain ⟨Y,⟨ht,hr⟩⟩ := ((trim _ he).and (transfer _ he)).exists
    obtain ⟨K,hK⟩ := ht
    filter_upwards [hK,hr K] with n ht hr
    obtain ⟨A,B,hab,hf⟩ := attain n
    obtain ⟨a,b,ha,hb,hs,hv⟩ := ht A B hab
    filter_upwards [hr a b (small hab ha hb) hs] with m hm
    obtain ⟨c,d,hcd,hw⟩ := hm
    linarith [le_best hcd]

end OMA.R_Erdos490_erdos_490_variants_limit_R1
