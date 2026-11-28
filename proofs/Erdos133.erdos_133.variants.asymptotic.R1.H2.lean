import OMAReductions.R_Erdos133_erdos_133_variants_asymptotic_R1

-- Step Erdos133.erdos_133.variants.asymptotic.R1.H2: hypothesis H2 of reduction Erdos133.erdos_133.variants.asymptotic.R1
-- Credit: @sobrien032
-- H2 := ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (Erdos133.f n : ℝ) ≤ (1 + ε) * Real.sqrt (n : ℝ)

/-
The upper half of f(n) ~ sqrt(n) for Erdős Problem 133: for every ε > 0 and all large n there is a
triangle-free graph on n vertices with diameter 2 and maximum degree at most (1 + ε) sqrt(n).

Mathematics: Samuel Korsky (with GPT Astra), The Minimum Maximum Degree Of Triangle-Free Graphs Of
Diameter Two, preprint, September 15, 2026, Theorem 1. The preprint is unrefereed; this file checks
the argument in Lean. Its construction: the Erdős–Rényi orthogonal polarity graph on PG(2, p), each
vertex blown up into a copy of the plane over ZMod q, local triangle-free graphs from a random-graph
lemma and random labellings of parallel lines (done here as finite counting), a maximal triangle-free
extension, and duplication of vertices to reach every order. Here the duplication is done along whole
rows, deterministically.

Lean formalization, November 27, 2026, for sobrien032: Claude Fable 5.2 wrote part A; Claude Opus 5.5
wrote parts B and C and assembled this file.

Structure. Three statements fixed in advance (namespace Korsky133): PartA, the local graph (Korsky,
Lemmas 2 and 3); PartB, the global graph (Section 3); ShortPrimes, primes in short intervals. Then
partA_holds : PartA, partB_of_partA : PartA → PartB and h2_of_parts : ShortPrimes → PartB → H2
(Section 4). ShortPrimes is OMA.PNT.h1, proved in the block after the three parts, which is a port of
the PrimeNumberTheoremAnd weak prime number theorem under the Apache License 2.0 with its own
credits and modification notes.
-/

namespace Korsky133

open Filter

/-- Primes in short multiplicative intervals: the statement of `OMA.PNT.h1`. -/
def ShortPrimes : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∃ p : ℕ, p.Prime ∧ n < p ∧ (p : ℝ) ≤ (1 + δ) * (n : ℝ)

/-- Part A, the local graph (Korsky, Lemmas 2 and 3): for every `ε > 0` and every large prime `q`,
and every set `C` of at most `q / 2` slopes, a triangle-free graph on the plane `ZMod q × ZMod q`
whose edges join points with different values under every form `x.1 + c * x.2` with `c ∈ C`, in
which every point reaches every other value of every such form in one step, and whose independent
sets have at most `ε q²` points. -/
def PartA : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ Q : ℕ, ∀ q : ℕ, q.Prime → Q ≤ q →
    ∀ C : Finset (ZMod q), 2 * C.card ≤ q →
      ∃ H : SimpleGraph (ZMod q × ZMod q),
        H.CliqueFree 3 ∧
        (∀ x y, H.Adj x y → ∀ c ∈ C, x.1 + c * x.2 ≠ y.1 + c * y.2) ∧
        (∀ x, ∀ c ∈ C, ∀ b : ZMod q, b ≠ x.1 + c * x.2 →
          ∃ y, H.Adj x y ∧ y.1 + c * y.2 = b) ∧
        (∀ s : Set (ZMod q × ZMod q), (∀ x ∈ s, ∀ y ∈ s, ¬ H.Adj x y) →
          (s.ncard : ℝ) ≤ ε * (q : ℝ) ^ 2)

/-- Part B, the global graph (Korsky, Section 3): for every `ε > 0`, all primes `p` and `q` with
`q` large and `2 (p + 1) ≤ q`, a triangle-free graph on `(p² + p + 1) q²` vertices in which any two
distinct nonadjacent vertices have a common neighbour, together with a row function taking each
value on `(p² + p + 1) q` vertices, such that each vertex has at most `p + 1` neighbours in each
row, up to `ε q²` exceptional neighbours. -/
def PartB : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ Q : ℕ, ∀ p q : ℕ, p.Prime → q.Prime → Q ≤ q → 2 * (p + 1) ≤ q →
    ∃ (V : Type) (G : SimpleGraph V) (row : V → ZMod q),
      Finite V ∧
      Nat.card V = (p ^ 2 + p + 1) * q ^ 2 ∧
      (∀ c : ZMod q, {z | row z = c}.ncard = (p ^ 2 + p + 1) * q) ∧
      G.CliqueFree 3 ∧
      (∀ x y : V, x ≠ y → ¬ G.Adj x y → ∃ z, G.Adj x z ∧ G.Adj z y) ∧
      (∀ (x : V) (R : Set (ZMod q)),
        ({z | G.Adj x z ∧ row z ∈ R}.ncard : ℝ) ≤
          (R.ncard : ℝ) * ((p : ℝ) + 1) + ε * (q : ℝ) ^ 2)

/-
Erdős 133, asymptotic upper bound, part A: the local graph.

Part A builder (Claude Fable 5.2), November 27, 2026, for the Lane B lead.

Mathematics: S. Korsky (with GPT Astra), The Minimum Maximum Degree Of Triangle-Free Graphs Of
Diameter Two, unrefereed preprint, September 15, 2026, Lemmas 2 and 3, with the simplifications
proposed by the referee: integer counting, powers of two, random cyclic shifts of the rows.

* Lemma 2 (`A.exists_F`). Colour the pairs of `Fin (2 * m)` with `k` colours and join the pairs
  of one colour. For `m = t ^ 3`, `k = 4 * t ^ 2`, `t = 2 ^ j` and `s = 2 * k * (3 * j + 2) + 1`,
  a first moment count gives a colouring with fewer than `m` triangles (as ordered triples) and
  no independent set of `s` vertices. Deleting a vertex of each triangle, keeping `m` vertices
  and extending to a maximal triangle-free graph `F` on `ZMod m` keeps the independent sets
  below `s`, and maximality gives `m ≤ deg v * s` for every vertex `v`. Hence every vertex has at
  most `a` non-neighbours, where `2 * a ^ s ≤ m ^ s`.
* Lemma 3 (`A.exists_H`). For a prime `q ≤ m` and `τ : ZMod q → ZMod m`, label `(x₁, x₂)` by
  `x₁.val + τ x₂`, and join two points when their labels are adjacent in `F` and they differ
  under every form `x.1 + c * x.2` with `c ∈ C`. Each row is labelled injectively, so an
  independent set has at most `s * q` points. For a fixed point, form and value, at least
  `q - C.card` rows of the target line can be used, so at most `m * a ^ r * m ^ (q - r)`
  labellings fail there, with `r = q - C.card`. The union bound over `q ^ 4` triples leaves a
  labelling with no failure.
* `A.main_step` checks the inequalities when `q ≤ t ^ 3 < 8 * q`, and `partA_holds` chooses `j`.
-/

namespace A

/-- Counting functions with prescribed sets of values on a set of coordinates. -/
lemma card_constr {ι κ : Type*} [Fintype ι] [Fintype κ] (T : Finset ι) (A : ι → Finset κ) (a : ℕ)
    (hA : ∀ i ∈ T, (A i).card ≤ a) (B : Finset (ι → κ)) (hB : ∀ f ∈ B, ∀ i ∈ T, f i ∈ A i) :
    B.card * Fintype.card κ ^ T.card ≤ a ^ T.card * Fintype.card κ ^ Fintype.card ι := by
  classical
  have h1 : B ⊆ Fintype.piFinset (fun i => if i ∈ T then A i else Finset.univ) := by
    intro f hf
    rw [Fintype.mem_piFinset]
    intro i
    split_ifs with h
    · exact hB f hf i h
    · exact Finset.mem_univ _
  have h2 := Finset.card_le_card h1
  rw [Fintype.card_piFinset] at h2
  calc B.card * Fintype.card κ ^ T.card
      ≤ (∏ i, (if i ∈ T then A i else Finset.univ).card) *
          ∏ i, (if i ∈ T then Fintype.card κ else 1) := by
        rw [Fintype.prod_ite_mem, Finset.prod_const]
        exact Nat.mul_le_mul_right _ h2
    _ = ∏ i, ((if i ∈ T then A i else Finset.univ).card * (if i ∈ T then Fintype.card κ else 1)) :=
        Finset.prod_mul_distrib.symm
    _ ≤ ∏ i, ((if i ∈ T then a else 1) * Fintype.card κ) := by
        refine Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => ?_)
        split_ifs with h
        · exact Nat.mul_le_mul_right _ (hA i h)
        · simp
    _ = a ^ T.card * Fintype.card κ ^ Fintype.card ι := by
        rw [Finset.prod_mul_distrib, Fintype.prod_ite_mem, Finset.prod_const, Finset.prod_const,
          Finset.card_univ]

lemma bern (a d : ℕ) : ∀ n : ℕ, a ^ (n + 1) + (n + 1) * d * a ^ n ≤ (a + d) ^ (n + 1)
  | 0 => by simp
  | n + 1 => by
    have h := bern a d n
    have e : (a + d) * (a ^ (n + 1) + (n + 1) * d * a ^ n) =
        a ^ (n + 1 + 1) + (n + 1 + 1) * d * a ^ (n + 1) + (n + 1) * d * d * a ^ n := by ring
    calc a ^ (n + 1 + 1) + (n + 1 + 1) * d * a ^ (n + 1)
        ≤ (a + d) * (a ^ (n + 1) + (n + 1) * d * a ^ n) := by rw [e]; exact Nat.le_add_right _ _
      _ ≤ (a + d) ^ (n + 1 + 1) := by
          rw [pow_succ' (a + d) (n + 1)]; exact Nat.mul_le_mul_left _ h

/-- Bernoulli: `w` steps of size `d` from `a` at least double the `w`-th power. -/
lemma two_mul_pow_le (a d w : ℕ) (hw : 0 < w) (h : a ≤ w * d) : 2 * a ^ w ≤ (a + d) ^ w := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hw.ne'
  have h1 := bern a d n
  have h2 : a * a ^ n ≤ (n + 1) * d * a ^ n := Nat.mul_le_mul_right _ h
  calc 2 * a ^ (n + 1) = a ^ (n + 1) + a * a ^ n := by ring
    _ ≤ a ^ (n + 1) + (n + 1) * d * a ^ n := by omega
    _ ≤ _ := h1

lemma pow_two_mul_le (a M w T r : ℕ) (h : 2 * a ^ w ≤ M ^ w) (haM : a ≤ M) (hr : w * T ≤ r) :
    2 ^ T * a ^ r ≤ M ^ r := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hr
  calc 2 ^ T * a ^ (w * T + e) = (2 * a ^ w) ^ T * a ^ e := by
        rw [pow_add, pow_mul, mul_pow]; ring
    _ ≤ (M ^ w) ^ T * M ^ e :=
        Nat.mul_le_mul (Nat.pow_le_pow_left h T) (Nat.pow_le_pow_left haM e)
    _ = M ^ (w * T + e) := by rw [pow_add, pow_mul]

lemma sq_le_two_pow (c j : ℕ) (h : 27 * c ≤ j) : c * (j + 1) ^ 2 ≤ 2 ^ j := by
  have h1 : j / 3 + 1 ≤ 2 ^ (j / 3) := Nat.lt_two_pow_self
  have h2 : (2 ^ (j / 3)) ^ 3 ≤ 2 ^ j := by
    rw [← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : j + 1 ≤ 3 * (j / 3 + 1) := by omega
  have h4 : 9 * c ≤ j / 3 + 1 := by omega
  calc c * (j + 1) ^ 2 ≤ c * (3 * (j / 3 + 1)) ^ 2 := by gcongr
    _ = 9 * c * (j / 3 + 1) ^ 2 := by ring
    _ ≤ (j / 3 + 1) * (j / 3 + 1) ^ 2 := by gcongr
    _ = (j / 3 + 1) ^ 3 := by ring
    _ ≤ (2 ^ (j / 3)) ^ 3 := by gcongr
    _ ≤ 2 ^ j := h2

lemma cf3_iff {V : Type*} (G : SimpleGraph V) :
    G.CliqueFree 3 ↔ ∀ x y z, G.Adj x y → G.Adj y z → G.Adj x z → False := by
  classical
  constructor
  · intro h x y z hxy hyz hxz
    exact h {x, y, z} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hxy, hxz, hyz⟩)
  · intro h s hs
    obtain ⟨a, b, c, hab, hac, hbc, -⟩ := SimpleGraph.is3Clique_iff.mp hs
    exact h a b c hab hbc hac

/-- The graph of colour `z` under a colouring of the pairs. -/
def colG {V κ : Type*} (z : κ) (c : Sym2 V → κ) : SimpleGraph V where
  Adj x y := x ≠ y ∧ c s(x, y) = z
  symm.symm x y h := ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩
  loopless.irrefl x h := h.1 rfl

lemma colG_adj {V κ : Type*} (z : κ) (c : Sym2 V → κ) (x y : V) :
    (colG z c).Adj x y ↔ x ≠ y ∧ c s(x, y) = z := Iff.rfl

/-- The triples of pairwise adjacent vertices. -/
def Tri {V κ : Type*} (z : κ) (c : Sym2 V → κ) (t : V × V × V) : Prop :=
  (colG z c).Adj t.1 t.2.1 ∧ (colG z c).Adj t.2.1 t.2.2 ∧ (colG z c).Adj t.1 t.2.2

lemma tri_count {V κ : Type*} [Fintype V] [DecidableEq V] [Fintype κ] (z : κ) (t : V × V × V)
    (B : Finset (Sym2 V → κ)) (hB : ∀ c ∈ B, Tri z c t) :
    B.card * Fintype.card κ ^ 3 ≤ Fintype.card κ ^ Fintype.card (Sym2 V) := by
  classical
  rcases B.eq_empty_or_nonempty with rfl | ⟨c0, hc0⟩
  · simp
  obtain ⟨x, y, w⟩ := t
  obtain ⟨⟨hxy, -⟩, ⟨hyw, -⟩, ⟨hxw, -⟩⟩ := hB c0 hc0
  have hT3 : ({s(x, y), s(y, w), s(x, w)} : Finset (Sym2 V)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [hxy.symm, hyw, hxw.symm]
    · simp [hxy, hxy.symm, hyw, hxw]
  have h := card_constr {s(x, y), s(y, w), s(x, w)} (fun _ => {z}) 1
    (by simp) B (by
      intro c hc i hi
      obtain ⟨⟨-, h1⟩, ⟨-, h2⟩, ⟨-, h3⟩⟩ := hB c hc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi ⊢
      rcases hi with rfl | rfl | rfl <;> assumption)
  rw [hT3] at h
  simpa using h

lemma indep_count {V κ : Type*} [Fintype V] [DecidableEq V] [Fintype κ] (z : κ) (S : Finset V)
    (B : Finset (Sym2 V → κ)) (hB : ∀ c ∈ B, ∀ x ∈ S, ∀ y ∈ S, ¬(colG z c).Adj x y) :
    B.card * Fintype.card κ ^ S.card.choose 2 ≤
      (Fintype.card κ - 1) ^ S.card.choose 2 * Fintype.card κ ^ Fintype.card (Sym2 V) := by
  classical
  have h := card_constr (S.offDiag.image (Function.uncurry Sym2.mk)) (fun _ => Finset.univ.erase z)
    (Fintype.card κ - 1)
    (fun _ _ => by rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]) B (by
      intro c hc e he
      obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp he
      rw [Finset.mem_offDiag] at hxy
      exact Finset.mem_erase.mpr ⟨fun h =>
        hB c hc x hxy.1 y hxy.2.1 ((colG_adj z c x y).mpr ⟨hxy.2.2, h⟩), Finset.mem_univ _⟩)
  rwa [Sym2.card_image_offDiag] at h

/-- First moment: some colouring has few triangles and no large independent set. -/
lemma exists_colouring (N m s k : ℕ) (hk : 0 < k) (hm : 0 < m) (hT : 8 * N ^ 3 ≤ m * k ^ 3)
    (hI : 2 * (N.choose s * (k - 1) ^ s.choose 2) ≤ k ^ s.choose 2) :
    ∃ G : SimpleGraph (Fin N),
      (∃ D : Finset (Fin N), D.card < m ∧
        ∀ x y z, G.Adj x y → G.Adj y z → G.Adj x z → x ∈ D) ∧
      ∀ S : Finset (Fin N), S.card = s → ∃ x ∈ S, ∃ y ∈ S, G.Adj x y := by
  classical
  have z : Fin k := ⟨0, hk⟩
  obtain ⟨n, hn⟩ : ∃ n, n = Fintype.card (Sym2 (Fin N)) := ⟨_, rfl⟩
  have hcard : Fintype.card (Fin k) = k := Fintype.card_fin k
  have hsum : ∑ c : Sym2 (Fin N) → Fin k, (Finset.univ.filter (Tri z c)).card =
      ∑ t : Fin N × Fin N × Fin N, (Finset.univ.filter (fun c => Tri z c t)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have h1 : 8 * (Finset.univ.filter (fun c : Sym2 (Fin N) → Fin k =>
      m ≤ (Finset.univ.filter (Tri z c)).card)).card ≤ k ^ n := by
    have ha : (Finset.univ.filter (fun c : Sym2 (Fin N) → Fin k =>
        m ≤ (Finset.univ.filter (Tri z c)).card)).card * m ≤
        ∑ c : Sym2 (Fin N) → Fin k, (Finset.univ.filter (Tri z c)).card := by
      rw [← smul_eq_mul]
      exact (Finset.card_nsmul_le_sum _ _ m (fun c hc => (Finset.mem_filter.mp hc).2)).trans
        (Finset.sum_le_sum_of_subset (Finset.subset_univ _))
    have hb : (∑ c : Sym2 (Fin N) → Fin k, (Finset.univ.filter (Tri z c)).card) * k ^ 3 ≤
        N ^ 3 * k ^ n := by
      rw [hsum, Finset.sum_mul]
      calc ∑ t : Fin N × Fin N × Fin N, (Finset.univ.filter (fun c => Tri z c t)).card * k ^ 3
          ≤ ∑ _t : Fin N × Fin N × Fin N, k ^ n := Finset.sum_le_sum (fun t _ => by
            have := tri_count z t (Finset.univ.filter (fun c => Tri z c t))
              (fun c hc => (Finset.mem_filter.mp hc).2)
            rwa [hcard, ← hn] at this)
        _ = N ^ 3 * k ^ n := by
            rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
            simp only [Fintype.card_prod, Fintype.card_fin]
            ring
    refine Nat.le_of_mul_le_mul_right ?_ (Nat.mul_pos hm (pow_pos hk 3))
    calc 8 * _ * (m * k ^ 3) = 8 * (_ * m * k ^ 3) := by ring
      _ ≤ 8 * (N ^ 3 * k ^ n) :=
          Nat.mul_le_mul_left _ ((Nat.mul_le_mul_right _ ha).trans hb)
      _ = 8 * N ^ 3 * k ^ n := by ring
      _ ≤ m * k ^ 3 * k ^ n := Nat.mul_le_mul_right _ hT
      _ = k ^ n * (m * k ^ 3) := by ring
  have h2 : 2 * (Finset.univ.filter (fun c : Sym2 (Fin N) → Fin k => ∃ S : Finset (Fin N),
      S.card = s ∧ ∀ x ∈ S, ∀ y ∈ S, ¬(colG z c).Adj x y)).card ≤ k ^ n := by
    have hsub : Finset.univ.filter (fun c : Sym2 (Fin N) → Fin k => ∃ S : Finset (Fin N),
        S.card = s ∧ ∀ x ∈ S, ∀ y ∈ S, ¬(colG z c).Adj x y) ⊆
        (Finset.powersetCard s Finset.univ).biUnion (fun S => Finset.univ.filter
          (fun c : Sym2 (Fin N) → Fin k => ∀ x ∈ S, ∀ y ∈ S, ¬(colG z c).Adj x y)) := by
      intro c hc
      obtain ⟨S, hS1, hS2⟩ := (Finset.mem_filter.mp hc).2
      exact Finset.mem_biUnion.mpr ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hS1⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS2⟩⟩
    have hle := Nat.mul_le_mul_right (k ^ s.choose 2)
      ((Finset.card_le_card hsub).trans Finset.card_biUnion_le)
    rw [Finset.sum_mul] at hle
    have hle2 : ∑ S ∈ Finset.powersetCard s (Finset.univ : Finset (Fin N)), (Finset.univ.filter
        (fun c : Sym2 (Fin N) → Fin k => ∀ x ∈ S, ∀ y ∈ S, ¬(colG z c).Adj x y)).card *
          k ^ s.choose 2 ≤ N.choose s * ((k - 1) ^ s.choose 2 * k ^ n) := by
      calc _ ≤ ∑ _S ∈ Finset.powersetCard s (Finset.univ : Finset (Fin N)),
            (k - 1) ^ s.choose 2 * k ^ n :=
            Finset.sum_le_sum (fun S hS => by
              have := indep_count z S (Finset.univ.filter (fun c : Sym2 (Fin N) → Fin k =>
                ∀ x ∈ S, ∀ y ∈ S, ¬(colG z c).Adj x y)) (fun c hc => (Finset.mem_filter.mp hc).2)
              rwa [hcard, ← hn, (Finset.mem_powersetCard.mp hS).2] at this)
        _ = N.choose s * ((k - 1) ^ s.choose 2 * k ^ n) := by simp [Finset.card_powersetCard]
    refine Nat.le_of_mul_le_mul_right ?_ (pow_pos hk (s.choose 2))
    calc 2 * _ * k ^ s.choose 2 = 2 * (_ * k ^ s.choose 2) := by ring
      _ ≤ 2 * (N.choose s * ((k - 1) ^ s.choose 2 * k ^ n)) :=
          Nat.mul_le_mul_left _ (hle.trans hle2)
      _ = 2 * (N.choose s * (k - 1) ^ s.choose 2) * k ^ n := by ring
      _ ≤ k ^ s.choose 2 * k ^ n := Nat.mul_le_mul_right _ hI
      _ = k ^ n * k ^ s.choose 2 := by ring
  have htot : (Finset.univ : Finset (Sym2 (Fin N) → Fin k)).card = k ^ n := by
    rw [Finset.card_univ, Fintype.card_fun, hcard, hn]
  have hne : ∃ c : Sym2 (Fin N) → Fin k, ¬ m ≤ (Finset.univ.filter (Tri z c)).card ∧
      ¬ ∃ S : Finset (Fin N), S.card = s ∧ ∀ x ∈ S, ∀ y ∈ S, ¬(colG z c).Adj x y := by
    by_contra hcon
    have hsub : (Finset.univ : Finset (Sym2 (Fin N) → Fin k)) ⊆
        Finset.univ.filter (fun c : Sym2 (Fin N) → Fin k =>
          m ≤ (Finset.univ.filter (Tri z c)).card) ∪
        Finset.univ.filter (fun c : Sym2 (Fin N) → Fin k => ∃ S : Finset (Fin N),
          S.card = s ∧ ∀ x ∈ S, ∀ y ∈ S, ¬(colG z c).Adj x y) := by
      intro c _
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      by_contra h
      exact hcon ⟨c, fun h' => h (Or.inl ⟨Finset.mem_univ _, h'⟩),
        fun h' => h (Or.inr ⟨Finset.mem_univ _, h'⟩)⟩
    have h3 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    rw [htot] at h3
    have : 0 < k ^ n := pow_pos hk n
    omega
  obtain ⟨c, hc1, hc2⟩ := hne
  refine ⟨colG z c, ⟨(Finset.univ.filter (Tri z c)).image (fun t => t.1), ?_, ?_⟩, ?_⟩
  · exact lt_of_le_of_lt Finset.card_image_le (not_le.mp hc1)
  · intro x y w hxy hyw hxw
    exact Finset.mem_image.mpr
      ⟨(x, y, w), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy, hyw, hxw⟩, rfl⟩
  · intro S hS
    by_contra hcon
    push Not at hcon
    exact hc2 ⟨S, hS, hcon⟩

/-- Alteration: remove a vertex of each triangle and keep `m` vertices. -/
lemma exists_base (m s : ℕ) [NeZero m] (G : SimpleGraph (Fin (2 * m)))
    (D : Finset (Fin (2 * m))) (hD : D.card < m)
    (hG : ∀ x y z, G.Adj x y → G.Adj y z → G.Adj x z → x ∈ D)
    (hS : ∀ S : Finset (Fin (2 * m)), S.card = s → ∃ x ∈ S, ∃ y ∈ S, G.Adj x y) :
    ∃ F : SimpleGraph (ZMod m), F.CliqueFree 3 ∧
      ∀ S : Finset (ZMod m), (∀ x ∈ S, ∀ y ∈ S, ¬F.Adj x y) → S.card < s := by
  classical
  have hc : Fintype.card (ZMod m) ≤ Fintype.card {x // x ∈ Dᶜ} := by
    rw [ZMod.card, Fintype.card_coe, Finset.card_compl, Fintype.card_fin]; omega
  obtain ⟨g⟩ := Function.Embedding.nonempty_of_card_le hc
  have hinj : Function.Injective (fun i => (g i).1) := Subtype.val_injective.comp g.injective
  refine ⟨G.comap (fun i => (g i).1), (cf3_iff _).mpr ?_, ?_⟩
  · intro x y z hxy hyz hxz
    exact (Finset.mem_compl.mp (g x).2) (hG _ _ _ hxy hyz hxz)
  · intro S hS'
    by_contra hcon
    obtain ⟨S', hS's, hcard⟩ := Finset.exists_subset_card_eq (not_lt.mp hcon)
    obtain ⟨x, hx, y, hy, hxy⟩ := hS (S'.image (fun i => (g i).1))
      (by rw [Finset.card_image_of_injective _ hinj, hcard])
    obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy
    exact hS' x' (hS's hx') y' (hS's hy') hxy

/-- Maximal extension: every vertex has few non-neighbours. -/
lemma exists_maximal_ext (m s : ℕ) [NeZero m] (hm : 2 ≤ m) (F₀ : SimpleGraph (ZMod m))
    (h3 : F₀.CliqueFree 3)
    (hS : ∀ S : Finset (ZMod m), (∀ x ∈ S, ∀ y ∈ S, ¬F₀.Adj x y) → S.card < s) :
    ∃ F : SimpleGraph (ZMod m), F.CliqueFree 3 ∧
      (∀ S : Finset (ZMod m), (∀ x ∈ S, ∀ y ∈ S, ¬F.Adj x y) → S.card < s) ∧
      ∃ a, a ≤ m ∧ (∀ v (M : Finset (ZMod m)), (∀ u ∈ M, ¬F.Adj v u) → M.card ≤ a) ∧
        2 * a ^ s ≤ m ^ s := by
  classical
  obtain ⟨F, hle, hmax⟩ :=
    Finite.exists_le_maximal (p := fun H : SimpleGraph (ZMod m) => H.CliqueFree 3) h3
  have hF3 := (cf3_iff F).mp hmax.1
  have hSF : ∀ S : Finset (ZMod m), (∀ x ∈ S, ∀ y ∈ S, ¬F.Adj x y) → S.card < s :=
    fun S h => hS S (fun x hx y hy hxy => h x hx y hy (hle hxy))
  have hcn : ∀ v w, v ≠ w → ¬F.Adj v w → ∃ u, F.Adj v u ∧ F.Adj w u := by
    intro v w hvw hn
    obtain ⟨t, hvt, hwt, h1, h2⟩ := SimpleGraph.exists_of_maximal_cliqueFree_not_adj hmax hvw hn
    have hcard : t.card = 1 := by
      have := h1.card_eq
      rw [Finset.card_insert_of_notMem hvt] at this
      omega
    obtain ⟨u, rfl⟩ := Finset.card_eq_one.mp hcard
    rw [Finset.mem_singleton] at hvt hwt
    exact ⟨u, h1.isClique (by simp) (by simp) hvt, h2.isClique (by simp) (by simp) hwt⟩
  have hdeg : ∀ u, (Finset.univ.filter (F.Adj u)).card + 1 ≤ s := fun u =>
    Nat.succ_le_of_lt (hSF _ (fun x hx y hy hxy =>
      hF3 u x y (Finset.mem_filter.mp hx).2 hxy (Finset.mem_filter.mp hy).2))
  have hcov : ∀ v, m ≤ (Finset.univ.filter (F.Adj v)).card * s := by
    intro v
    have : Nontrivial (ZMod m) :=
      Fintype.one_lt_card_iff_nontrivial.mp (by rw [ZMod.card]; omega)
    have hne : ∃ u, F.Adj v u := by
      obtain ⟨w, hw⟩ := exists_ne v
      by_cases hvw : F.Adj v w
      · exact ⟨w, hvw⟩
      · obtain ⟨u, hu, -⟩ := hcn v w hw.symm hvw
        exact ⟨u, hu⟩
    have hsub : (Finset.univ : Finset (ZMod m)) ⊆
        (Finset.univ.filter (F.Adj v)).biUnion
          (fun u => insert u (Finset.univ.filter (F.Adj u))) := by
      intro w _
      rw [Finset.mem_biUnion]
      rcases eq_or_ne w v with rfl | hwv
      · obtain ⟨u, hu⟩ := hne
        exact ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩,
          Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu.symm⟩)⟩
      · by_cases hvw : F.Adj v w
        · exact ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvw⟩, Finset.mem_insert_self _ _⟩
        · obtain ⟨u, hu1, hu2⟩ := hcn v w (Ne.symm hwv) hvw
          exact ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu1⟩,
            Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu2.symm⟩)⟩
    calc m = (Finset.univ : Finset (ZMod m)).card := by rw [Finset.card_univ, ZMod.card]
      _ ≤ _ := Finset.card_le_card hsub
      _ ≤ ∑ u ∈ Finset.univ.filter (F.Adj v), (insert u (Finset.univ.filter (F.Adj u))).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _u ∈ Finset.univ.filter (F.Adj v), s :=
          Finset.sum_le_sum (fun u _ => (Finset.card_insert_le _ _).trans (hdeg u))
      _ = (Finset.univ.filter (F.Adj v)).card * s := by simp
  obtain ⟨v₀, -, hv₀⟩ :=
    Finset.exists_min_image Finset.univ (fun v : ZMod m => (Finset.univ.filter (F.Adj v)).card)
      Finset.univ_nonempty
  have hle0 : (Finset.univ.filter (F.Adj v₀)).card ≤ m :=
    (Finset.card_le_univ _).trans_eq (ZMod.card m)
  refine ⟨F, hmax.1, hSF, m - (Finset.univ.filter (F.Adj v₀)).card, Nat.sub_le _ _, ?_, ?_⟩
  · intro v M hM
    have hdisj : Disjoint M (Finset.univ.filter (F.Adj v)) := by
      rw [Finset.disjoint_left]
      intro u hu hu'
      exact hM u hu (Finset.mem_filter.mp hu').2
    have h1 := Finset.card_union_of_disjoint hdisj
    have h2 : (M ∪ Finset.univ.filter (F.Adj v)).card ≤ m :=
      (Finset.card_le_univ _).trans_eq (ZMod.card m)
    have h3 := hv₀ v (Finset.mem_univ _)
    omega
  · have hs : 0 < s := by have := hdeg v₀; omega
    have := two_mul_pow_le (m - (Finset.univ.filter (F.Adj v₀)).card)
      (Finset.univ.filter (F.Adj v₀)).card s hs
      ((Nat.sub_le _ _).trans ((hcov v₀).trans (le_of_eq (mul_comm _ _))))
    rwa [Nat.sub_add_cancel hle0] at this

/-- Korsky, Lemma 2, as integer counting. -/
lemma exists_F (m s k : ℕ) [NeZero m] (hm : 2 ≤ m) (hk : 0 < k)
    (hT : 8 * (2 * m) ^ 3 ≤ m * k ^ 3)
    (hI : 2 * ((2 * m).choose s * (k - 1) ^ s.choose 2) ≤ k ^ s.choose 2) :
    ∃ F : SimpleGraph (ZMod m), F.CliqueFree 3 ∧
      (∀ S : Finset (ZMod m), (∀ x ∈ S, ∀ y ∈ S, ¬F.Adj x y) → S.card < s) ∧
      ∃ a, a ≤ m ∧ (∀ v (M : Finset (ZMod m)), (∀ u ∈ M, ¬F.Adj v u) → M.card ≤ a) ∧
        2 * a ^ s ≤ m ^ s := by
  obtain ⟨G, ⟨D, hD, hG⟩, hS⟩ := exists_colouring (2 * m) m s k hk (by omega) hT hI
  obtain ⟨F₀, h3, hS₀⟩ := exists_base m s G D hD hG hS
  exact exists_maximal_ext m s hm F₀ h3 hS₀

/-- The label of a point: its first coordinate, shifted by the value of `τ` on its row. -/
def lab {q m : ℕ} (τ : ZMod q → ZMod m) (x : ZMod q × ZMod q) : ZMod m :=
  (x.1.val : ZMod m) + τ x.2

/-- The local graph defined by a labelling of the rows. -/
def gH {q m : ℕ} (F : SimpleGraph (ZMod m)) (C : Finset (ZMod q)) (τ : ZMod q → ZMod m) :
    SimpleGraph (ZMod q × ZMod q) where
  Adj x y := F.Adj (lab τ x) (lab τ y) ∧ ∀ c ∈ C, x.1 + c * x.2 ≠ y.1 + c * y.2
  symm.symm _ _ h := ⟨h.1.symm, fun c hc => (h.2 c hc).symm⟩
  loopless.irrefl _ h := F.irrefl h.1

lemma gH_adj {q m : ℕ} (F : SimpleGraph (ZMod m)) (C : Finset (ZMod q)) (τ : ZMod q → ZMod m)
    (x y : ZMod q × ZMod q) : (gH F C τ).Adj x y ↔
      F.Adj (lab τ x) (lab τ y) ∧ ∀ c ∈ C, x.1 + c * x.2 ≠ y.1 + c * y.2 := Iff.rfl

lemma val_cast_inj {q m : ℕ} [NeZero q] (hqm : q ≤ m) {a b : ZMod q}
    (h : ((a.val : ℕ) : ZMod m) = (b.val : ZMod m)) : a = b := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (lt_of_lt_of_le a.val_lt hqm),
    Nat.mod_eq_of_lt (lt_of_lt_of_le b.val_lt hqm)] at h
  exact ZMod.val_injective q h

/-- Independent sets meet each row in a set whose labels are independent. -/
lemma gH_indep {q m : ℕ} [NeZero q] (hqm : q ≤ m) (F : SimpleGraph (ZMod m))
    (C : Finset (ZMod q)) (τ : ZMod q → ZMod m) (s : ℕ)
    (hF : ∀ S : Finset (ZMod m), (∀ x ∈ S, ∀ y ∈ S, ¬F.Adj x y) → S.card < s)
    (S : Finset (ZMod q × ZMod q)) (hS : ∀ x ∈ S, ∀ y ∈ S, ¬(gH F C τ).Adj x y) :
    S.card ≤ s * q := by
  classical
  have hfib : ∀ b ∈ S.image Prod.snd, (S.filter (fun x => x.2 = b)).card ≤ s := by
    intro b _
    have hinj : Set.InjOn (lab τ) (S.filter (fun x => x.2 = b) : Set (ZMod q × ZMod q)) := by
      intro x hx y hy hxy
      have hx2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
      have hy2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).2
      simp only [lab, hx2, hy2] at hxy
      exact Prod.ext (val_cast_inj hqm (add_right_cancel hxy)) (hx2.trans hy2.symm)
    rw [← Finset.card_image_of_injOn hinj]
    refine (hF _ ?_).le
    intro u hu v hv huv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
    rw [Finset.mem_filter] at hx hy
    refine hS x hx.1 y hy.1 ((gH_adj F C τ x y).mpr ⟨huv, fun c _ h => ?_⟩)
    rw [hx.2, hy.2] at h
    have hxy : x = y := Prod.ext (add_right_cancel h) (hx.2.trans hy.2.symm)
    rw [hxy] at huv
    exact F.irrefl huv
  calc S.card ≤ s * (S.image Prod.snd).card := Finset.card_le_mul_card_image S s hfib
    _ ≤ s * q := Nat.mul_le_mul_left _ ((Finset.card_le_univ _).trans_eq (ZMod.card q))

/-- On a target line, at most `C.card` rows are excluded. -/
lemma rows_card {q : ℕ} [Fact q.Prime] (C : Finset (ZMod q)) (x : ZMod q × ZMod q)
    (c b : ZMod q) (hc : c ∈ C) (hb : b ≠ x.1 + c * x.2) (R : Finset (ZMod q))
    (hR : ∀ y, y ∈ R ↔ (y ≠ x.2 ∧ ∀ c' ∈ C, x.1 + c' * x.2 ≠ (b - c * y) + c' * y)) :
    q - C.card ≤ R.card := by
  classical
  have hsub : Rᶜ ⊆
      C.image (fun c' => if c' = c then x.2 else (x.1 + c' * x.2 - b) / (c' - c)) := by
    intro y hy
    rw [Finset.mem_compl, hR] at hy
    rw [Finset.mem_image]
    by_cases hy2 : y = x.2
    · exact ⟨c, hc, by simp [hy2]⟩
    · push Not at hy
      obtain ⟨c', hc', h⟩ := hy hy2
      have hne : c' ≠ c := by
        rintro rfl
        apply hb
        rw [h]
        ring
      refine ⟨c', hc', ?_⟩
      rw [if_neg hne, div_eq_iff (sub_ne_zero.mpr hne)]
      linear_combination h
  have h1 := (Finset.card_le_card hsub).trans Finset.card_image_le
  rw [Finset.card_compl, ZMod.card] at h1
  omega

/-- The labellings that fail at one point, one form and one value. -/
lemma bad_card {q m : ℕ} [Fact q.Prime] [NeZero m] (F : SimpleGraph (ZMod m))
    (C : Finset (ZMod q)) (a : ℕ)
    (ha : ∀ v (M : Finset (ZMod m)), (∀ u ∈ M, ¬F.Adj v u) → M.card ≤ a)
    (x : ZMod q × ZMod q) (c b : ZMod q) (B : Finset (ZMod q → ZMod m))
    (hB : ∀ τ ∈ B, c ∈ C ∧ b ≠ x.1 + c * x.2 ∧
      ∀ y : ZMod q × ZMod q, y.1 + c * y.2 = b → ¬(gH F C τ).Adj x y) :
    B.card * m ^ (q - C.card) ≤ m * a ^ (q - C.card) * m ^ q := by
  classical
  rcases B.eq_empty_or_nonempty with rfl | ⟨τ₀, hτ₀⟩
  · simp
  obtain ⟨hc, hb, -⟩ := hB τ₀ hτ₀
  have hR := rows_card C x c b hc hb (Finset.univ.filter (fun y : ZMod q =>
    y ≠ x.2 ∧ ∀ c' ∈ C, x.1 + c' * x.2 ≠ (b - c * y) + c' * y)) (fun y => by simp)
  obtain ⟨R, hRR, hRcard⟩ := Finset.exists_subset_card_eq hR
  obtain ⟨A, hA⟩ : ∃ A : ZMod m → ZMod q → Finset (ZMod m), ∀ t₀ y t, t ∈ A t₀ y ↔
      ¬F.Adj ((x.1.val : ZMod m) + t₀) (((b - c * y).val : ZMod m) + t) :=
    ⟨fun t₀ y => Finset.univ.filter (fun t : ZMod m =>
      ¬F.Adj ((x.1.val : ZMod m) + t₀) (((b - c * y).val : ZMod m) + t)), fun t₀ y t => by simp⟩
  have hAcard : ∀ t₀ y, (A t₀ y).card ≤ a := by
    intro t₀ y
    have h := ha ((x.1.val : ZMod m) + t₀)
      ((A t₀ y).image (fun t => ((b - c * y).val : ZMod m) + t)) (by
        intro u hu
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
        exact (hA t₀ y t).mp ht)
    rwa [Finset.card_image_of_injective _ (add_right_injective _)] at h
  have hsub : B ⊆ Finset.univ.biUnion
      (fun t₀ : ZMod m => B.filter (fun τ => ∀ y ∈ R, τ y ∈ A t₀ y)) := by
    intro τ hτ
    refine Finset.mem_biUnion.mpr
      ⟨τ x.2, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hτ, fun y hy => ?_⟩⟩
    have hyR := (Finset.mem_filter.mp (hRR hy)).2
    refine (hA _ _ _).mpr (fun hadj => ?_)
    exact (hB τ hτ).2.2 (b - c * y, y) (by simp) ((gH_adj F C τ _ _).mpr ⟨hadj, hyR.2⟩)
  have hP : ∀ t₀ : ZMod m, (B.filter (fun τ => ∀ y ∈ R, τ y ∈ A t₀ y)).card *
      m ^ (q - C.card) ≤ a ^ (q - C.card) * m ^ q := by
    intro t₀
    have := card_constr R (A t₀) a (fun y _ => hAcard t₀ y)
      (B.filter (fun τ => ∀ y ∈ R, τ y ∈ A t₀ y)) (fun τ hτ => (Finset.mem_filter.mp hτ).2)
    rwa [hRcard, ZMod.card, ZMod.card] at this
  have hle := Nat.mul_le_mul_right (m ^ (q - C.card))
    ((Finset.card_le_card hsub).trans Finset.card_biUnion_le)
  rw [Finset.sum_mul] at hle
  refine hle.trans ((Finset.sum_le_sum (fun t₀ _ => hP t₀)).trans (le_of_eq ?_))
  rw [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]
  ring

/-- Korsky, Lemma 3, with random cyclic shifts of the rows. -/
lemma exists_H {q m : ℕ} [Fact q.Prime] [NeZero m] (hqm : q ≤ m) (F : SimpleGraph (ZMod m))
    (h3 : F.CliqueFree 3) (s a : ℕ)
    (hF : ∀ S : Finset (ZMod m), (∀ x ∈ S, ∀ y ∈ S, ¬F.Adj x y) → S.card < s)
    (ha : ∀ v (M : Finset (ZMod m)), (∀ u ∈ M, ¬F.Adj v u) → M.card ≤ a)
    (hU : ∀ r, q ≤ 2 * r → q ^ 4 * m * a ^ r < m ^ r)
    (C : Finset (ZMod q)) (hC : 2 * C.card ≤ q) :
    ∃ H : SimpleGraph (ZMod q × ZMod q),
      H.CliqueFree 3 ∧
      (∀ x y, H.Adj x y → ∀ c ∈ C, x.1 + c * x.2 ≠ y.1 + c * y.2) ∧
      (∀ x, ∀ c ∈ C, ∀ b : ZMod q, b ≠ x.1 + c * x.2 →
        ∃ y, H.Adj x y ∧ y.1 + c * y.2 = b) ∧
      (∀ S : Finset (ZMod q × ZMod q), (∀ x ∈ S, ∀ y ∈ S, ¬H.Adj x y) → S.card ≤ s * q) := by
  classical
  have hF3 := (cf3_iff F).mp h3
  have hm0 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hex : ∃ τ : ZMod q → ZMod m, ∀ i : (ZMod q × ZMod q) × ZMod q × ZMod q,
      ¬(i.2.1 ∈ C ∧ i.2.2 ≠ i.1.1 + i.2.1 * i.1.2 ∧
        ∀ y : ZMod q × ZMod q, y.1 + i.2.1 * y.2 = i.2.2 → ¬(gH F C τ).Adj i.1 y) := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset (ZMod q → ZMod m)) ⊆
        Finset.univ.biUnion (fun i : (ZMod q × ZMod q) × ZMod q × ZMod q => Finset.univ.filter
          (fun τ : ZMod q → ZMod m => i.2.1 ∈ C ∧ i.2.2 ≠ i.1.1 + i.2.1 * i.1.2 ∧
            ∀ y : ZMod q × ZMod q, y.1 + i.2.1 * y.2 = i.2.2 → ¬(gH F C τ).Adj i.1 y)) := by
      intro τ _
      obtain ⟨i, hi⟩ := hcon τ
      exact Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    have h1 := Nat.mul_le_mul_right (m ^ (q - C.card))
      ((Finset.card_le_card hsub).trans Finset.card_biUnion_le)
    rw [Finset.card_univ, Fintype.card_fun, ZMod.card, ZMod.card, Finset.sum_mul] at h1
    have h2 := h1.trans (Finset.sum_le_sum (fun i _ => bad_card F C a ha i.1 i.2.1 i.2.2 _
      (fun τ hτ => (Finset.mem_filter.mp hτ).2)))
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul] at h2
    simp only [Fintype.card_prod, ZMod.card] at h2
    have h3' := Nat.mul_lt_mul_of_pos_right (hU (q - C.card) (by omega)) (pow_pos hm0 q)
    have h4 : q * q * (q * q) * (m * a ^ (q - C.card) * m ^ q) =
        q ^ 4 * m * a ^ (q - C.card) * m ^ q := by ring
    rw [h4, mul_comm (m ^ q)] at h2
    exact absurd h2 (not_le.mpr h3')
  obtain ⟨τ, hτ⟩ := hex
  refine ⟨gH F C τ, (cf3_iff _).mpr ?_, ?_, ?_, ?_⟩
  · intro x y z hxy hyz hxz
    exact hF3 _ _ _ ((gH_adj F C τ _ _).mp hxy).1 ((gH_adj F C τ _ _).mp hyz).1
      ((gH_adj F C τ _ _).mp hxz).1
  · intro x y hxy
    exact ((gH_adj F C τ _ _).mp hxy).2
  · intro x c hc b hb
    by_contra hcon
    push Not at hcon
    exact hτ (x, c, b) ⟨hc, hb, fun y hy hadj => hcon y hadj hy⟩
  · exact fun S hS => gH_indep hqm F C τ s hF S hS

/-- The construction for one prime `q` and the scale `t = 2 ^ j` with `q ≤ t ^ 3 < 8 * q`. -/
lemma main_step (j q t : ℕ) [Fact q.Prime] (ht : t = 2 ^ j) (hj : 27 * 6480 ≤ j)
    (hq1 : q ≤ t ^ 3) (hq2 : t ^ 3 < 8 * q) (C : Finset (ZMod q)) (hC : 2 * C.card ≤ q) :
    ∃ H : SimpleGraph (ZMod q × ZMod q),
      H.CliqueFree 3 ∧
      (∀ x y, H.Adj x y → ∀ c ∈ C, x.1 + c * x.2 ≠ y.1 + c * y.2) ∧
      (∀ x, ∀ c ∈ C, ∀ b : ZMod q, b ≠ x.1 + c * x.2 →
        ∃ y, H.Adj x y ∧ y.1 + c * y.2 = b) ∧
      (∀ S : Finset (ZMod q × ZMod q), (∀ x ∈ S, ∀ y ∈ S, ¬H.Adj x y) →
        S.card ≤ 27 * t ^ 2 * (j + 1) * q) := by
  have hgrow : 6480 * (j + 1) ^ 2 ≤ t := ht ▸ sq_le_two_pow 6480 j hj
  have ht2 : 2 ≤ t := by nlinarith [sq_nonneg j]
  obtain ⟨k, hk⟩ : ∃ k, k = 4 * t ^ 2 := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = 2 * k * (3 * j + 2) + 1 := ⟨_, rfl⟩
  have : NeZero (t ^ 3) := ⟨by positivity⟩
  have hk0 : 0 < k := by rw [hk]; positivity
  have hsle : s ≤ 27 * t ^ 2 * (j + 1) := by
    rw [hs, hk]
    nlinarith [Nat.zero_le (t ^ 2 * j), Nat.pos_of_ne_zero (pow_ne_zero 2 (by omega : t ≠ 0))]
  have hI : 2 * ((2 * t ^ 3).choose s * (k - 1) ^ s.choose 2) ≤ k ^ s.choose 2 := by
    have hkk : 2 * (k - 1) ^ k ≤ k ^ k := by
      have := two_mul_pow_le (k - 1) 1 k hk0 (by omega)
      rwa [Nat.sub_add_cancel hk0] at this
    have hch : s.choose 2 = k * ((3 * j + 2) * s) := by
      rw [Nat.choose_two_right]
      apply Nat.div_eq_of_eq_mul_left (by norm_num)
      have : s - 1 = 2 * k * (3 * j + 2) := by rw [hs]; exact Nat.add_sub_cancel _ _
      rw [this]
      ring
    have h2 := pow_two_mul_le (k - 1) k k ((3 * j + 1) * s + 1) (s.choose 2) hkk
      (Nat.sub_le _ _) (by
        rw [hch]
        apply Nat.mul_le_mul_left
        have : 1 ≤ s := by rw [hs]; omega
        nlinarith)
    calc 2 * ((2 * t ^ 3).choose s * (k - 1) ^ s.choose 2)
        ≤ 2 * ((2 * t ^ 3) ^ s * (k - 1) ^ s.choose 2) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.choose_le_pow _ _))
      _ = 2 ^ ((3 * j + 1) * s + 1) * (k - 1) ^ s.choose 2 := by rw [ht]; ring
      _ ≤ k ^ s.choose 2 := h2
  have hU : ∀ a, a ≤ t ^ 3 → 2 * a ^ s ≤ (t ^ 3) ^ s →
      ∀ r, q ≤ 2 * r → q ^ 4 * t ^ 3 * a ^ r < (t ^ 3) ^ r := by
    intro a ha1 ha2 r hr
    have hsT : s * (15 * j + 1) ≤ r := by
      have : 16 * (s * (15 * j + 1)) ≤ t ^ 3 := by
        calc 16 * (s * (15 * j + 1))
            ≤ 16 * (27 * t ^ 2 * (j + 1) * (15 * (j + 1))) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul hsle (by omega))
          _ = t ^ 2 * (6480 * (j + 1) ^ 2) := by ring
          _ ≤ t ^ 2 * t := Nat.mul_le_mul_left _ hgrow
          _ = t ^ 3 := by ring
      omega
    have h1 := pow_two_mul_le a (t ^ 3) s (15 * j + 1) r ha2 ha1 hsT
    have h2 : 2 * (q ^ 4 * t ^ 3) ≤ 2 ^ (15 * j + 1) := by
      calc 2 * (q ^ 4 * t ^ 3) ≤ 2 * ((t ^ 3) ^ 4 * t ^ 3) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hq1 4))
        _ = 2 ^ (15 * j + 1) := by rw [ht]; ring
    have h3 : 0 < (t ^ 3) ^ r := pow_pos (pow_pos (by omega) 3) r
    have h4 : 2 * (q ^ 4 * t ^ 3 * a ^ r) ≤ (t ^ 3) ^ r := by
      calc 2 * (q ^ 4 * t ^ 3 * a ^ r) = 2 * (q ^ 4 * t ^ 3) * a ^ r := by ring
        _ ≤ 2 ^ (15 * j + 1) * a ^ r := Nat.mul_le_mul_right _ h2
        _ ≤ _ := h1
    omega
  obtain ⟨F, h3, hF, a, ha1, ha2, ha3⟩ := exists_F (t ^ 3) s k
    (ht2.trans (Nat.le_self_pow (by norm_num) t)) hk0 (by rw [hk]; exact le_of_eq (by ring)) hI
  obtain ⟨H, hH1, hH2, hH3, hH4⟩ := exists_H hq1 F h3 s a hF ha2 (hU a ha1 ha3) C hC
  exact ⟨H, hH1, hH2, hH3, fun S hS => (hH4 S hS).trans (Nat.mul_le_mul_right _ hsle)⟩

end A

/-- Part A: Korsky, Lemmas 2 and 3. -/
theorem partA_holds : PartA := by
  intro ε hε
  obtain ⟨c, hc⟩ := exists_nat_ge (216 / ε)
  have hc' : 216 ≤ ε * c := by
    rw [div_le_iff₀ hε] at hc
    linarith
  refine ⟨8 ^ (27 * (c + 6480)) + 2, fun q hq hQ C hC => ?_⟩
  have := Fact.mk hq
  obtain ⟨j, hj⟩ : ∃ j, j = Nat.clog 8 q := ⟨_, rfl⟩
  have h1 : q ≤ 8 ^ j := hj ▸ Nat.le_pow_clog (by norm_num) q
  have h2 : 8 ^ (j - 1) < q := hj ▸ Nat.pow_pred_clog_lt_self (by norm_num) hq.one_lt
  have hjJ : 27 * (c + 6480) < j := by
    by_contra hcon
    have : 8 ^ j ≤ 8 ^ (27 * (c + 6480)) := Nat.pow_le_pow_right (by norm_num) (not_lt.mp hcon)
    omega
  have h8 : (8 : ℕ) ^ j = 8 * 8 ^ (j - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hm : (8 : ℕ) ^ j = (2 ^ j) ^ 3 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  obtain ⟨H, hH1, hH2, hH3, hH4⟩ :=
    A.main_step j q (2 ^ j) rfl (by omega) (by omega) (by omega) C hC
  refine ⟨H, hH1, hH2, hH3, fun S hS => ?_⟩
  classical
  have hcard := hH4 S.toFinset (by simpa using hS)
  rw [← Set.ncard_eq_toFinset_card'] at hcard
  have hgrow := A.sq_le_two_pow c j (by omega)
  have key : c * S.ncard ≤ 216 * q * q := by
    calc c * S.ncard ≤ c * (27 * (2 ^ j) ^ 2 * (j + 1) * q) := Nat.mul_le_mul_left _ hcard
      _ ≤ c * (27 * (2 ^ j) ^ 2 * (j + 1) ^ 2 * q) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _
            (Nat.le_self_pow (by norm_num) _)))
      _ = 27 * (2 ^ j) ^ 2 * (c * (j + 1) ^ 2) * q := by ring
      _ ≤ 27 * (2 ^ j) ^ 2 * 2 ^ j * q :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hgrow)
      _ = 27 * (2 ^ j) ^ 3 * q := by ring
      _ ≤ 27 * (8 * q) * q := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
      _ = 216 * q * q := by ring
  have keyR : (c : ℝ) * (S.ncard : ℝ) ≤ 216 * (q : ℝ) * q := by exact_mod_cast key
  have hcpos : (0 : ℝ) < c := by
    by_contra h
    push Not at h
    nlinarith
  have hfin : (c : ℝ) * (S.ncard : ℝ) ≤ c * (ε * (q : ℝ) ^ 2) := by
    nlinarith [sq_nonneg (q : ℝ)]
  exact le_of_mul_le_mul_left hfin hcpos

/-
# Erdős 133 H2, part B: the global graph (Korsky, Section 3)

Part B builder (Claude Opus 5.5), November 27, 2026. We prove `Korsky133.partB_of_partA`.

The base graph is the Erdős–Rényi orthogonal polarity graph on the projective plane over `ZMod p`.
Every base vertex is replaced by a copy of the plane `ZMod q × ZMod q` carrying a local graph from
part A, and adjacent copies are joined along the lines of linear forms, oriented by a linear order of
the base. The resulting graph is triangle-free and any two vertices in different copies are at
distance at most two; a maximal triangle-free extension adds no edge between different copies.

Mathematics: S. Korsky (with GPT Astra), The Minimum Maximum Degree Of Triangle-Free Graphs Of
Diameter Two, unrefereed preprint, September 15, 2026, Section 3.
-/

namespace B

theorem cf3_of {V : Type} {G : SimpleGraph V}
    (h : ∀ a b c, G.Adj a b → G.Adj a c → G.Adj b c → False) : G.CliqueFree 3 := by
  classical
  intro t ht
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := SimpleGraph.is3Clique_iff.mp ht
  exact h a b c hab hac hbc

theorem cf3_use {V : Type} {G : SimpleGraph V} (h : G.CliqueFree 3) {a b c : V}
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) : False := by
  classical
  exact h {a, b, c} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hab, hac, hbc⟩)

/-- In a maximal triangle-free graph, distinct nonadjacent vertices have a common neighbour. -/
theorem max_cn {V : Type} {G : SimpleGraph V}
    (h : Maximal (fun H : SimpleGraph V => H.CliqueFree 3) G) {x y : V} (hxy : x ≠ y)
    (hn : ¬ G.Adj x y) : ∃ z, G.Adj x z ∧ G.Adj z y := by
  classical
  obtain ⟨s, hxs, hys, h1, h2⟩ := SimpleGraph.exists_of_maximal_cliqueFree_not_adj h hxy hn
  have hs : s.card = 1 := by
    have := h1.card_eq
    rw [Finset.card_insert_of_notMem hxs] at this
    omega
  obtain ⟨z, rfl⟩ := Finset.card_eq_one.mp hs
  have hxz : x ≠ z := fun e => hxs (by simp [e])
  have hyz : y ≠ z := fun e => hys (by simp [e])
  exact ⟨z, h1.1 (by simp) (by simp) hxz, (h2.1 (by simp) (by simp) hyz).symm⟩

open Projectivization

/-- Points of the projective plane over `ZMod p`. -/
abbrev Pt (p : ℕ) [Fact p.Prime] : Type := Projectivization (ZMod p) (Fin 3 → ZMod p)

/-- The Erdős–Rényi orthogonal polarity graph. -/
def polar (p : ℕ) [Fact p.Prime] : SimpleGraph (Pt p) where
  Adj u v := u ≠ v ∧ u.orthogonal v
  symm.symm _ _ h := ⟨h.1.symm, orthogonal_comm.mp h.2⟩
  loopless.irrefl _ h := h.1 rfl

variable {p : ℕ} [Fact p.Prime]

theorem polar_adj {u v : Pt p} : (polar p).Adj u v ↔ u ≠ v ∧ u.orthogonal v := Iff.rfl

theorem card_pt : Nat.card (Pt p) = p ^ 2 + p + 1 := by
  have h := card_of_finrank (ZMod p) (Fin 3 → ZMod p) (Module.finrank_fin_fun (ZMod p))
  rw [Nat.card_zmod] at h
  rw [show Nat.card (Pt p) = _ from h]
  simp [Finset.sum_range_succ]
  ring

/-- A point orthogonal to two distinct points is their cross product. -/
theorem eq_cross {u v w : Pt p} (huv : u ≠ v) (hu : w.orthogonal u) (hv : w.orthogonal v) :
    w = cross u v := by
  induction u using Projectivization.ind with | h u hu0 =>
  induction v using Projectivization.ind with | h v hv0 =>
  induction w using Projectivization.ind with | h w hw0 =>
  rw [orthogonal_mk hw0 hu0] at hu
  rw [orthogonal_mk hw0 hv0] at hv
  rw [cross_mk_of_ne hu0 hv0 huv, mk_eq_mk_iff_crossProduct_eq_zero,
    cross_cross_eq_smul_sub_smul', hv, dotProduct_comm u w, hu, zero_smul, zero_smul, sub_zero]

theorem polar_uniq {u v w w' : Pt p} (huv : u ≠ v) (h1 : (polar p).Adj u w)
    (h2 : (polar p).Adj v w) (h3 : (polar p).Adj u w') (h4 : (polar p).Adj v w') : w = w' :=
  (eq_cross huv (orthogonal_comm.mp (polar_adj.mp h1).2) (orthogonal_comm.mp (polar_adj.mp h2).2)).trans
    (eq_cross huv (orthogonal_comm.mp (polar_adj.mp h3).2)
      (orthogonal_comm.mp (polar_adj.mp h4).2)).symm

theorem polar_cn {u v : Pt p} (huv : u ≠ v) (hn : ¬ (polar p).Adj u v) :
    ∃ w, (polar p).Adj u w ∧ (polar p).Adj w v := by
  have hno : ¬ u.orthogonal v := fun h => hn (polar_adj.mpr ⟨huv, h⟩)
  refine ⟨cross u v, polar_adj.mpr ⟨fun h => hno ?_, orthogonal_cross_left huv⟩,
    polar_adj.mpr ⟨fun h => hno ?_, cross_orthogonal_right huv⟩⟩
  · have := cross_orthogonal_right huv
    rwa [← h] at this
  · have := orthogonal_cross_left huv
    rwa [h] at this

theorem polar_deg (v : Pt p) : {w | (polar p).Adj v w}.ncard ≤ p + 1 := by
  obtain ⟨f, hf_def⟩ : ∃ f, f = dotProductEquiv (ZMod p) (Fin 3) v.rep := ⟨_, rfl⟩
  have hf : f ≠ 0 := by
    rw [hf_def, ne_eq, LinearEquiv.map_eq_zero_iff]
    exact v.rep_nonzero
  have h2 : Module.finrank (ZMod p) (LinearMap.ker f) = 2 := by
    have := Module.Dual.finrank_ker_add_one_of_ne_zero hf
    rw [Module.finrank_fin_fun] at this
    omega
  have hc := card_of_finrank_two (ZMod p) (LinearMap.ker f) h2
  rw [Nat.card_zmod] at hc
  have hinj : Function.Injective (LinearMap.ker f).subtype := (LinearMap.ker f).injective_subtype
  calc {w | (polar p).Adj v w}.ncard
      ≤ (Projectivization.map (LinearMap.ker f).subtype hinj '' Set.univ).ncard := by
        refine Set.ncard_le_ncard ?_ (Set.toFinite _)
        intro w hw
        replace hw := (polar_adj.mp hw).2
        induction w using Projectivization.ind with | h w hw0 => ?_
        have hv : (Projectivization.mk (ZMod p) v.rep v.rep_nonzero).orthogonal
            (Projectivization.mk (ZMod p) w hw0) := by
          rwa [Projectivization.mk_rep]
        rw [orthogonal_mk] at hv
        have hk : w ∈ LinearMap.ker f := by
          rw [LinearMap.mem_ker, hf_def]
          simpa using hv
        refine ⟨Projectivization.mk (ZMod p) ⟨w, hk⟩ (fun h => hw0 (congrArg Subtype.val h)),
          Set.mem_univ _, ?_⟩
        rw [Projectivization.map_mk]
        rfl
    _ ≤ (Set.univ : Set (Projectivization (ZMod p) (LinearMap.ker f))).ncard := Set.ncard_image_le
    _ = p + 1 := by rw [Set.ncard_univ, hc]

theorem rows_card {q : ℕ} (c : ZMod q) :
    {z : Pt p × (ZMod q × ZMod q) | z.2.2 = c}.ncard = (p ^ 2 + p + 1) * q := by
  have : {z : Pt p × (ZMod q × ZMod q) | z.2.2 = c} = Set.univ ×ˢ (Set.univ ×ˢ {c}) := by
    ext z
    simp
  rw [this, Set.ncard_prod, Set.ncard_prod, Set.ncard_univ, Set.ncard_univ, Set.ncard_singleton,
    card_pt, Nat.card_zmod, mul_one]

/-- An equivalence relation on a finite set of at most `q` points is the kernel of a map
into `ZMod q`. -/
theorem exists_ker {α : Type} [Nonempty α] {q : ℕ} [NeZero q] (S : Set α) (hS : S.ncard ≤ q)
    (r : α → α → Prop) (hr : ∀ a ∈ S, r a a) (hsy : ∀ a ∈ S, ∀ b ∈ S, r a b → r b a)
    (htr : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, r a b → r b c → r a c) (hfin : S.Finite) :
    ∃ f : α → ZMod q, ∀ a ∈ S, ∀ b ∈ S, (f a = f b ↔ r a b) := by
  obtain ⟨g, -, hg⟩ := hfin.exists_injOn_of_encard_le (t := (Set.univ : Set (ZMod q))) (by
    rw [Set.encard_univ, ENat.card_eq_coe_natCard, Nat.card_zmod, ← hfin.cast_ncard_eq]
    exact_mod_cast hS)
  let rep : α → α := fun a => Classical.epsilon (fun c => c ∈ S ∧ r a c)
  have hrep : ∀ a ∈ S, rep a ∈ S ∧ r a (rep a) := fun a ha =>
    Classical.epsilon_spec (p := fun c => c ∈ S ∧ r a c) ⟨a, ha, hr a ha⟩
  have hrep2 : ∀ a ∈ S, ∀ b ∈ S, r a b → rep a = rep b := by
    intro a ha b hb hab
    have : (fun c => c ∈ S ∧ r a c) = (fun c => c ∈ S ∧ r b c) := by
      funext c
      apply propext
      exact ⟨fun h => ⟨h.1, htr b hb a ha c h.1 (hsy a ha b hb hab) h.2⟩,
        fun h => ⟨h.1, htr a ha b hb c h.1 hab h.2⟩⟩
    exact congrArg (fun P => Classical.epsilon P) this
  refine ⟨fun a => g (rep a), fun a ha b hb => ⟨fun h => ?_, fun h => congrArg g (hrep2 a ha b hb h)⟩⟩
  have e := hg (hrep a ha).1 (hrep b hb).1 h
  have h1 := (hrep a ha).2
  rw [e] at h1
  exact htr a ha _ (hrep b hb).1 b hb h1 (hsy b hb _ (hrep b hb).1 (hrep b hb).2)

/-- Slopes at each base vertex: two neighbours get the same slope exactly when they are equal or
adjacent. -/
theorem exists_slope {β : Type} [Finite β] (Gb : SimpleGraph β) {q d : ℕ} [NeZero q] (hdq : d ≤ q)
    (huniq : ∀ u v w w', u ≠ v → Gb.Adj u w → Gb.Adj v w → Gb.Adj u w' → Gb.Adj v w' → w = w')
    (hdeg : ∀ v, {w | Gb.Adj v w}.ncard ≤ d) :
    ∃ s : β → β → ZMod q, ∀ o a b, Gb.Adj o a → Gb.Adj o b →
      (s o a = s o b ↔ a = b ∨ Gb.Adj a b) := by
  have key : ∀ o, ∃ f : β → ZMod q, ∀ a ∈ {x | Gb.Adj o x}, ∀ b ∈ {x | Gb.Adj o x},
      (f a = f b ↔ a = b ∨ Gb.Adj a b) := by
    intro o
    have : Nonempty β := ⟨o⟩
    refine exists_ker _ ((hdeg o).trans hdq) _ (fun a _ => Or.inl rfl) ?_ ?_ (Set.toFinite _)
    · rintro a - b - (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    · rintro a ha b hb c hc (rfl | hab) (rfl | hbc)
      · exact Or.inl rfl
      · exact Or.inr hbc
      · exact Or.inr hab
      · exact Or.inl (huniq b o a c (Gb.ne_of_adj hb).symm hab.symm ha hbc hc)
  choose s hs using key
  exact ⟨s, fun o a b ha hb => hs o a ha b hb⟩

section Blowup

variable {β : Type} [LinearOrder β] {q : ℕ}

/-- The orientation sign of a base edge. -/
def sg (u v : β) : ZMod q := if u < v then 1 else -1

theorem sg_sq (u v : β) : (sg u v : ZMod q) ^ 2 = 1 := by
  unfold sg
  split_ifs <;> ring

theorem sg_swap {u v : β} (h : u ≠ v) : (sg v u : ZMod q) = - sg u v := by
  unfold sg
  rcases lt_or_gt_of_ne h with h | h
  · rw [if_neg (not_lt_of_gt h), if_pos h]
  · rw [if_pos h, if_neg (not_lt_of_gt h), neg_neg]

/-- Cross edges between adjacent copies. -/
def Cr (Gb : SimpleGraph β) (s : β → β → ZMod q) (a b : β × (ZMod q × ZMod q)) : Prop :=
  Gb.Adj a.1 b.1 ∧ a.2.1 + s a.1 b.1 * a.2.2 - (b.2.1 + s b.1 a.1 * b.2.2) = sg a.1 b.1

theorem Cr.symm {Gb : SimpleGraph β} {s : β → β → ZMod q} {a b : β × (ZMod q × ZMod q)}
    (h : Cr Gb s a b) : Cr Gb s b a := by
  refine ⟨h.1.symm, ?_⟩
  rw [sg_swap (Gb.ne_of_adj h.1)]
  linear_combination -h.2

/-- The blown-up graph before the maximal extension. -/
def G0 (Gb : SimpleGraph β) (s : β → β → ZMod q) (H : β → SimpleGraph (ZMod q × ZMod q)) :
    SimpleGraph (β × (ZMod q × ZMod q)) where
  Adj a b := (a.1 = b.1 ∧ (H a.1).Adj a.2 b.2) ∨ Cr Gb s a b
  symm.symm a b h := by
    rcases h with ⟨e, h⟩ | h
    · refine Or.inl ⟨e.symm, ?_⟩
      rw [← e]
      exact h.symm
    · exact Or.inr h.symm
  loopless.irrefl a h := by
    rcases h with ⟨-, h⟩ | h
    · exact (H a.1).irrefl h
    · exact Gb.irrefl h.1

variable {Gb : SimpleGraph β} {s : β → β → ZMod q} {H : β → SimpleGraph (ZMod q × ZMod q)}

theorem tri2 (hi : ∀ w x y, (H w).Adj x y → ∀ v, Gb.Adj w v → x.1 + s w v * x.2 ≠ y.1 + s w v * y.2)
    {a b c : β × (ZMod q × ZMod q)} (e : a.1 = b.1) (hab : (H a.1).Adj a.2 b.2)
    (h1 : Cr Gb s a c) (h2 : Cr Gb s b c) : False := by
  obtain ⟨u, x⟩ := a
  obtain ⟨v, y⟩ := b
  obtain ⟨w, z⟩ := c
  obtain ⟨hw, e1⟩ := h1
  obtain ⟨-, e2⟩ := h2
  dsimp only at e hab hw e1 e2
  subst e
  exact hi u x y hab w hw (by linear_combination e1 - e2)

theorem tri3 (h3 : (3 : ZMod q) ≠ 0)
    (hs : ∀ w a b, Gb.Adj w a → Gb.Adj w b → Gb.Adj a b → s w a = s w b)
    {a b c : β × (ZMod q × ZMod q)} (h1 : Cr Gb s a b) (h2 : Cr Gb s a c) (h4 : Cr Gb s b c) :
    False := by
  obtain ⟨u, x⟩ := a
  obtain ⟨v, y⟩ := b
  obtain ⟨w, z⟩ := c
  obtain ⟨huv, e1⟩ := h1
  obtain ⟨huw, e2⟩ := h2
  obtain ⟨hvw, e3⟩ := h4
  dsimp only at huv huw hvw e1 e2 e3
  rw [hs u v w huv huw hvw, hs v u w huv.symm hvw huw] at e1
  rw [hs w u v huw.symm hvw.symm huv] at e2
  have E : sg u v + sg v w - sg u w = (0 : ZMod q) := by linear_combination e2 - e1 - e3
  have q1 := sg_sq (q := q) u v
  have q2 := sg_sq (q := q) v w
  have q3 := sg_sq (q := q) u w
  apply h3
  linear_combination (2 * sg u v * sg v w - 1) * (q3 - q1 - q2 + (sg u v + sg v w + sg u w) * E)
    - 4 * sg u v ^ 2 * q2 - 4 * q1

theorem G0_cf (h3 : (3 : ZMod q) ≠ 0) (hH : ∀ w, (H w).CliqueFree 3)
    (hi : ∀ w x y, (H w).Adj x y → ∀ v, Gb.Adj w v → x.1 + s w v * x.2 ≠ y.1 + s w v * y.2)
    (hs : ∀ w a b, Gb.Adj w a → Gb.Adj w b → Gb.Adj a b → s w a = s w b) :
    (G0 Gb s H).CliqueFree 3 := by
  refine cf3_of fun a b c hab hac hbc => ?_
  rcases hab with ⟨e1, h1⟩ | h1 <;> rcases hac with ⟨e2, h2⟩ | h2 <;>
    rcases hbc with ⟨e3, h4⟩ | h4
  · obtain ⟨u, x⟩ := a
    obtain ⟨v, y⟩ := b
    obtain ⟨w, z⟩ := c
    dsimp only at e1 e2 e3 h1 h2 h4
    subst e1 e2
    exact cf3_use (hH u) h1 h2 h4
  · exact Gb.ne_of_adj h4.1 (e1.symm.trans e2)
  · exact Gb.ne_of_adj h2.1 (e1.trans e3)
  · exact tri2 hi e1 h1 h2 h4
  · exact Gb.ne_of_adj h1.1 (e2.trans e3.symm)
  · exact tri2 hi e2 h2 h1 h4.symm
  · exact tri2 hi e3 h4 h1.symm h2.symm
  · exact tri3 h3 hs h1 h2 h4

theorem solve2 [Fact q.Prime] {c1 c2 : ZMod q} (h : c1 ≠ c2) (α γ : ZMod q) :
    ∃ t : ZMod q × ZMod q, t.1 + c1 * t.2 = α ∧ t.1 + c2 * t.2 = γ := by
  have h' : c1 - c2 ≠ 0 := sub_ne_zero.mpr h
  refine ⟨(α - c1 * ((α - γ) / (c1 - c2)), (α - γ) / (c1 - c2)), by ring, ?_⟩
  dsimp only
  field_simp
  ring

theorem G0_cn [Fact q.Prime]
    (hii : ∀ w x v, Gb.Adj w v → ∀ b, b ≠ x.1 + s w v * x.2 →
      ∃ y, (H w).Adj x y ∧ y.1 + s w v * y.2 = b)
    (hne : ∀ w a b, Gb.Adj w a → Gb.Adj w b → a ≠ b → ¬ Gb.Adj a b → s w a ≠ s w b)
    (hcn : ∀ u v, u ≠ v → ¬ Gb.Adj u v → ∃ w, Gb.Adj u w ∧ Gb.Adj w v)
    {a b : β × (ZMod q × ZMod q)} (hab : a.1 ≠ b.1) (hn : ¬ (G0 Gb s H).Adj a b) :
    ∃ c, (G0 Gb s H).Adj a c ∧ (G0 Gb s H).Adj c b := by
  obtain ⟨u, x⟩ := a
  obtain ⟨v, y⟩ := b
  dsimp only at hab
  by_cases huv : Gb.Adj u v
  · obtain ⟨x', hx', ex'⟩ := hii u x v huv (y.1 + s v u * y.2 + sg u v)
      (fun h => hn (Or.inr ⟨huv, by dsimp only; linear_combination -h⟩))
    exact ⟨(u, x'), Or.inl ⟨rfl, hx'⟩, Or.inr ⟨huv, by dsimp only; linear_combination ex'⟩⟩
  · obtain ⟨w, huw, hwv⟩ := hcn u v hab huv
    obtain ⟨t, ht1, ht2⟩ := solve2 (hne w u v huw.symm hwv hab huv)
      (x.1 + s u w * x.2 - sg u w) (y.1 + s v w * y.2 + sg w v)
    exact ⟨(w, t), Or.inr ⟨huw, by dsimp only; linear_combination -ht1⟩,
      Or.inr ⟨hwv, by dsimp only; linear_combination ht2⟩⟩

end Blowup

/-- The blow-up of a finite base graph with unique common neighbours, common neighbours of
nonadjacent pairs and degrees at most `d`, by local graphs from part A. -/
theorem blowup {q : ℕ} [Fact q.Prime] (hq : 4 ≤ q) {β : Type} [Finite β] (Gb : SimpleGraph β)
    (d : ℕ) (ε : ℝ) (hd : 2 * d ≤ q)
    (huniq : ∀ u v w w', u ≠ v → Gb.Adj u w → Gb.Adj v w → Gb.Adj u w' → Gb.Adj v w' → w = w')
    (hcn : ∀ u v, u ≠ v → ¬ Gb.Adj u v → ∃ w, Gb.Adj u w ∧ Gb.Adj w v)
    (hdeg : ∀ v, {w | Gb.Adj v w}.ncard ≤ d)
    (hA : ∀ C : Finset (ZMod q), 2 * C.card ≤ q →
      ∃ H : SimpleGraph (ZMod q × ZMod q),
        H.CliqueFree 3 ∧
        (∀ x y, H.Adj x y → ∀ c ∈ C, x.1 + c * x.2 ≠ y.1 + c * y.2) ∧
        (∀ x, ∀ c ∈ C, ∀ b : ZMod q, b ≠ x.1 + c * x.2 →
          ∃ y, H.Adj x y ∧ y.1 + c * y.2 = b) ∧
        (∀ s : Set (ZMod q × ZMod q), (∀ x ∈ s, ∀ y ∈ s, ¬ H.Adj x y) →
          (s.ncard : ℝ) ≤ ε * (q : ℝ) ^ 2)) :
    ∃ G : SimpleGraph (β × (ZMod q × ZMod q)), G.CliqueFree 3 ∧
      (∀ x y, x ≠ y → ¬ G.Adj x y → ∃ z, G.Adj x z ∧ G.Adj z y) ∧
      (∀ x (R : Set (ZMod q)), ({z | G.Adj x z ∧ z.2.2 ∈ R}.ncard : ℝ) ≤
        (R.ncard : ℝ) * (d : ℝ) + ε * (q : ℝ) ^ 2) := by
  classical
  have : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  obtain ⟨s, hs⟩ := exists_slope Gb (q := q) (by omega : d ≤ q) huniq hdeg
  let C : β → Finset (ZMod q) := fun w => (Set.toFinite (s w '' {a | Gb.Adj w a})).toFinset
  have hC : ∀ w v, Gb.Adj w v → s w v ∈ C w := fun w v h =>
    (Set.Finite.mem_toFinset _).mpr (Set.mem_image_of_mem _ h)
  have hC2 : ∀ w, 2 * (C w).card ≤ q := by
    intro w
    have : (C w).card ≤ d := by
      rw [← Set.ncard_eq_toFinset_card]
      exact le_trans Set.ncard_image_le (hdeg w)
    omega
  choose H hH1 hH2 hH3 hH4 using fun w => hA (C w) (hC2 w)
  obtain ⟨n, ⟨eqv⟩⟩ := Finite.exists_equiv_fin β
  let _ : LinearOrder β := LinearOrder.lift' eqv eqv.injective
  have h3 : (3 : ZMod q) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : ZMod q) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  have hseq : ∀ w a b, Gb.Adj w a → Gb.Adj w b → Gb.Adj a b → s w a = s w b :=
    fun w a b ha hb hab => (hs w a b ha hb).mpr (Or.inr hab)
  have hsne : ∀ w a b, Gb.Adj w a → Gb.Adj w b → a ≠ b → ¬ Gb.Adj a b → s w a ≠ s w b :=
    fun w a b ha hb hne hn h => ((hs w a b ha hb).mp h).elim hne hn
  have hi : ∀ w x y, (H w).Adj x y → ∀ v, Gb.Adj w v → x.1 + s w v * x.2 ≠ y.1 + s w v * y.2 :=
    fun w x y h v hv => hH2 w x y h _ (hC w v hv)
  have hii : ∀ w x v, Gb.Adj w v → ∀ b, b ≠ x.1 + s w v * x.2 →
      ∃ y, (H w).Adj x y ∧ y.1 + s w v * y.2 = b :=
    fun w x v hv b hb => hH3 w x _ (hC w v hv) b hb
  have hcf0 : (G0 Gb s H).CliqueFree 3 := G0_cf h3 hH1 hi hseq
  obtain ⟨G, hle, hmax⟩ := Finite.exists_le_maximal
    (p := fun G : SimpleGraph (β × (ZMod q × ZMod q)) => G.CliqueFree 3) hcf0
  have hcross : ∀ a b, G.Adj a b → a.1 ≠ b.1 → Cr Gb s a b := by
    intro a b hab hne
    by_contra hc
    have hn : ¬ (G0 Gb s H).Adj a b := by
      rintro (⟨e, -⟩ | h)
      · exact hne e
      · exact hc h
    obtain ⟨c, hac, hcb⟩ := G0_cn hii hsne hcn hne hn
    exact cf3_use hmax.1 hab (hle hac) (hle hcb).symm
  refine ⟨G, hmax.1, fun x y hxy hn => max_cn hmax hxy hn, ?_⟩
  rintro ⟨v, x⟩ R
  have hIind : ∀ t ∈ {t | G.Adj (v, x) (v, t)}, ∀ t' ∈ {t | G.Adj (v, x) (v, t)},
      ¬ (H v).Adj t t' := by
    intro t ht t' ht' h
    exact cf3_use hmax.1 ht ht' (hle (Or.inl ⟨rfl, h⟩))
  have hIc := hH4 v _ hIind
  have hsub : {z | G.Adj (v, x) z ∧ z.2.2 ∈ R} ⊆
      (fun t => (v, t)) '' {t | G.Adj (v, x) (v, t)} ∪
      (fun r : β × ZMod q => (r.1, (x.1 + s v r.1 * x.2 - sg v r.1 - s r.1 v * r.2, r.2))) ''
        ({w | Gb.Adj v w} ×ˢ R) := by
    rintro ⟨w, t⟩ ⟨hz, hR⟩
    by_cases hw : w = v
    · rw [hw] at hz
      exact Or.inl ⟨t, hz, by rw [hw]⟩
    · obtain ⟨hvw, e⟩ := hcross _ _ hz (Ne.symm hw)
      refine Or.inr ⟨(w, t.2), ⟨hvw, hR⟩, Prod.ext rfl (Prod.ext ?_ rfl)⟩
      dsimp only at e ⊢
      linear_combination e
  have h1 : ((fun t => (v, t)) '' {t | G.Adj (v, x) (v, t)}).ncard ≤
      {t | G.Adj (v, x) (v, t)}.ncard := Set.ncard_image_le
  have h2 : ((fun r : β × ZMod q => (r.1, (x.1 + s v r.1 * x.2 - sg v r.1 - s r.1 v * r.2, r.2))) ''
        ({w | Gb.Adj v w} ×ˢ R)).ncard ≤ d * R.ncard := by
    refine le_trans Set.ncard_image_le ?_
    rw [Set.ncard_prod]
    exact Nat.mul_le_mul_right _ (hdeg v)
  have h0 := (Set.ncard_le_ncard hsub).trans (Set.ncard_union_le _ _)
  have : ({z | G.Adj (v, x) z ∧ z.2.2 ∈ R}.ncard : ℝ) ≤
      {t | G.Adj (v, x) (v, t)}.ncard + d * R.ncard := by
    exact_mod_cast h0.trans (Nat.add_le_add h1 h2)
  linarith

end B

theorem partB_of_partA (hA : PartA) : PartB := by
  intro ε hε
  obtain ⟨Q, hQ⟩ := hA ε hε
  refine ⟨Q, fun p q hp hq hQq hpq => ?_⟩
  have := Fact.mk hp
  have := Fact.mk hq
  have h2p := hp.two_le
  obtain ⟨G, hcf, hcn, hrow⟩ := B.blowup (by omega) (B.polar p) (p + 1) ε hpq
    (fun _ _ _ _ => B.polar_uniq) (fun _ _ => B.polar_cn) B.polar_deg (hQ q hq hQq)
  refine ⟨B.Pt p × (ZMod q × ZMod q), G, fun z => z.2.2, inferInstance, ?_, B.rows_card, hcf, hcn,
    fun x R => ?_⟩
  · rw [Nat.card_prod, Nat.card_prod, B.card_pt, Nat.card_zmod]
    ring
  · have := hrow x R
    push_cast at this
    exact this

/-
Part C of the Erdős 133 H2 proof (Korsky, Section 4): from short prime intervals and the Part B
graph to `H2`. Vertices are duplicated deterministically along whole rows of the Part B graph, the
primes `p` and `q` are chosen with `q (p + 1) ≤ √n ≤ λ q (p + 1)`, the graph is moved to `Fin n`,
and the real-number bookkeeping gives `f n ≤ (1 + ε) √n`. Helpers live in `Korsky133.C`.
Builder: Claude Opus 5.5 (max effort), for the Lane B lead, November 27, 2026.
-/

namespace C

open SimpleGraph

/-- Pulling a triangle-free graph back along any map gives a triangle-free graph: three pairwise
adjacent vertices have pairwise adjacent images. -/
theorem cliqueFree_comap {V W : Type} (G : SimpleGraph W) (π : V → W) (h : G.CliqueFree 3) :
    (G.comap π).CliqueFree 3 := by
  classical
  intro t ht
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := is3Clique_iff.mp ht
  exact h {π a, π b, π c} (is3Clique_triple_iff.mpr ⟨hab, hac, hbc⟩)

/-- The diameter-two criterion: on at least three vertices, a triangle-free graph in which any two
distinct nonadjacent vertices have a common neighbour has diameter exactly two. -/
theorem diam_two {W : Type} [Fintype W] (H : SimpleGraph W) (h3 : 2 < Fintype.card W)
    (htf : H.CliqueFree 3)
    (hcn : ∀ u v, u ≠ v → ¬ H.Adj u v → ∃ w, H.Adj u w ∧ H.Adj w v) : H.diam = 2 := by
  classical
  have cn : ∀ u v, u ≠ v → ¬ H.Adj u v → (H.commonNeighbors u v).Nonempty := by
    intro u v huv hn
    obtain ⟨w, hu, hv⟩ := hcn u v huv hn
    refine ⟨w, ?_⟩
    rw [mem_commonNeighbors]
    exact ⟨hu, hv.symm⟩
  have he : H.ediam = 2 := by
    apply le_antisymm
    · apply ediam_le_of_edist_le
      intro u v
      by_contra! h
      obtain ⟨huv, hn, he⟩ := two_lt_edist_iff.mp h
      exact (cn u v huv hn).ne_empty he
    · obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp h3
      obtain ⟨x, y, hxy, hn⟩ : ∃ x y, x ≠ y ∧ ¬ H.Adj x y := by
        by_contra! hall
        exact htf {a, b, c}
          (is3Clique_triple_iff.mpr ⟨hall a b hab, hall a c hac, hall b c hbc⟩)
      rw [← edist_eq_two_iff.mpr ⟨hxy, hn, cn x y hxy hn⟩]
      exact edist_le_ediam
  simp [SimpleGraph.diam, he]

/-- Transfer to `Fin n`: a triangle-free graph on a finite type with `n ≥ 3` vertices, in which any
two distinct nonadjacent vertices have a common neighbour and every neighbourhood has at most
`X` vertices, gives `Erdos133.f n ≤ X`. -/
theorem f_le {W : Type} [Finite W] (H : SimpleGraph W) (n : ℕ) (X : ℝ)
    (hW : Nat.card W = n) (h3 : 3 ≤ n) (htf : H.CliqueFree 3)
    (hcn : ∀ u v, u ≠ v → ¬ H.Adj u v → ∃ w, H.Adj u w ∧ H.Adj w v)
    (hdeg : ∀ v, ((H.neighborSet v).ncard : ℝ) ≤ X) : (Erdos133.f n : ℝ) ≤ X := by
  classical
  have := Fintype.ofFinite W
  have hc : Fintype.card W = n := by rw [← Nat.card_eq_fintype_card]; exact hW
  let e : Fin n ≃ W := (Fintype.equivFinOfCardEq hc).symm
  let G : SimpleGraph (Fin n) := H.comap e
  have hX : (0 : ℝ) ≤ X := le_trans (Nat.cast_nonneg _) (hdeg (e ⟨0, by omega⟩))
  have hnb : ∀ v, (G.neighborSet v).ncard = (H.neighborSet (e v)).ncard := fun v =>
    Set.ncard_preimage_of_injective_subset_range e.injective
      (fun x _ => ⟨e.symm x, e.apply_symm_apply x⟩)
  have key : Erdos133.f n ≤ ⌊X⌋₊ := by
    unfold Erdos133.f
    apply Nat.sInf_le
    refine ⟨G, cliqueFree_comap H e htf, ?_, fun v => ?_⟩
    · apply diam_two G (by rw [Fintype.card_fin]; omega) (cliqueFree_comap H e htf)
      intro u v huv hn
      obtain ⟨w, h1, h2⟩ := hcn (e u) (e v) (e.injective.ne huv) hn
      refine ⟨e.symm w, ?_, ?_⟩
      · show H.Adj (e u) (e (e.symm w))
        rw [e.apply_symm_apply]
        exact h1
      · show H.Adj (e (e.symm w)) (e v)
        rw [e.apply_symm_apply]
        exact h2
    · rw [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card,
        Nat.card_coe_set_eq, hnb]
      exact Nat.le_floor (hdeg (e v))
  calc (Erdos133.f n : ℝ) ≤ (⌊X⌋₊ : ℝ) := by exact_mod_cast key
    _ ≤ X := Nat.floor_le hX

/-- Each vertex of `V` has one preimage under the map that identifies every twin in `S` with its
original, and each vertex of `S` has two. -/
theorem ncard_preimage_le {V : Type} [Finite V] (S Y : Set V) :
    ((Sum.elim id Subtype.val : V ⊕ S → V) ⁻¹' Y).ncard ≤ Y.ncard + (S ∩ Y).ncard := by
  have hsub : (Sum.elim id Subtype.val : V ⊕ S → V) ⁻¹' Y ⊆
      Sum.inl '' Y ∪ Sum.inr '' ((Subtype.val : S → V) ⁻¹' Y) := by
    rintro (x | x) hx
    · exact Or.inl ⟨x, hx, rfl⟩
    · exact Or.inr ⟨x, hx, rfl⟩
  calc _ ≤ _ := Set.ncard_le_ncard hsub
    _ ≤ _ := Set.ncard_union_le _ _
    _ = Y.ncard + (S ∩ Y).ncard := by
      rw [Set.ncard_image_of_injective _ Sum.inl_injective,
        Set.ncard_image_of_injective _ Sum.inr_injective,
        ← Set.ncard_image_of_injective _ Subtype.val_injective, Subtype.image_preimage_coe]

/-- Deterministic duplication along whole rows (Korsky, Section 4, with the rows of Part B in
place of a random set): add a twin to each of `a` vertices lying in `r` rows. -/
theorem dup {V : Type} [Finite V] (G : SimpleGraph V) {p q : ℕ} (row : V → ZMod q) (η : ℝ)
    (hq : q.Prime)
    (hcard : Nat.card V = (p ^ 2 + p + 1) * q ^ 2)
    (hrow : ∀ c : ZMod q, {z | row z = c}.ncard = (p ^ 2 + p + 1) * q)
    (htf : G.CliqueFree 3)
    (hcn : ∀ x y : V, x ≠ y → ¬ G.Adj x y → ∃ z, G.Adj x z ∧ G.Adj z y)
    (hdeg : ∀ (x : V) (R : Set (ZMod q)),
      ({z | G.Adj x z ∧ row z ∈ R}.ncard : ℝ) ≤ (R.ncard : ℝ) * ((p : ℝ) + 1) + η * (q : ℝ) ^ 2)
    (a r : ℕ) (hr : r ≤ q) (ha : a ≤ r * ((p ^ 2 + p + 1) * q)) :
    (Erdos133.f ((p ^ 2 + p + 1) * q ^ 2 + a) : ℝ) ≤
      ((q : ℝ) + r) * ((p : ℝ) + 1) + 2 * η * (q : ℝ) ^ 2 := by
  classical
  have h4 : 4 ≤ (p ^ 2 + p + 1) * q ^ 2 := by
    have := hq.two_le
    nlinarith
  obtain ⟨R, -, hR⟩ := Set.exists_subset_card_eq (s := (Set.univ : Set (ZMod q))) (n := r)
    (by rw [Set.ncard_univ, Nat.card_zmod]; exact hr)
  have hU : {z | row z ∈ R}.ncard = r * ((p ^ 2 + p + 1) * q) := by
    have : Fintype V := Fintype.ofFinite V
    have : NeZero q := ⟨hq.ne_zero⟩
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred,
      Finset.card_eq_sum_card_fiberwise (f := row) (t := R.toFinset)
        (fun x hx => by simpa using hx),
      Finset.sum_const_nat (m := (p ^ 2 + p + 1) * q), ← Set.ncard_eq_toFinset_card', hR]
    intro c hc
    rw [← hrow c, Set.ncard_eq_toFinset_card', Set.toFinset_ofPred, Finset.filter_filter]
    refine congrArg Finset.card (Finset.filter_congr fun z _ => ?_)
    exact ⟨fun h => h.2, fun h => ⟨h ▸ Set.mem_toFinset.mp hc, h⟩⟩
  obtain ⟨S, hSU, hS⟩ := Set.exists_subset_card_eq (s := {z | row z ∈ R}) (n := a)
    (by rw [hU]; exact ha)
  have hnbr : ∀ x : V, ∃ z, G.Adj x z := by
    intro x
    have : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; omega)
    obtain ⟨y, hy⟩ := exists_ne x
    by_cases hxy : G.Adj x y
    · exact ⟨y, hxy⟩
    · obtain ⟨z, hz, -⟩ := hcn x y hy.symm hxy
      exact ⟨z, hz⟩
  let π : V ⊕ S → V := Sum.elim id Subtype.val
  refine f_le (G.comap π) _ _ ?_ (by omega) (cliqueFree_comap G π htf) ?_ ?_
  · rw [Nat.card_sum, hcard, Nat.card_coe_set_eq, hS]
  · intro u v huv hn
    by_cases hπ : π u = π v
    · obtain ⟨z, hz⟩ := hnbr (π u)
      refine ⟨Sum.inl z, hz, ?_⟩
      show G.Adj z (π v)
      rw [← hπ]
      exact hz.symm
    · obtain ⟨z, h1, h2⟩ := hcn (π u) (π v) hπ hn
      exact ⟨Sum.inl z, h1, h2⟩
  · intro u
    have h1 := hdeg (π u) Set.univ
    have h2 := hdeg (π u) R
    rw [hR] at h2
    rw [Set.ncard_univ, Nat.card_zmod] at h1
    have e1 : {z | G.Adj (π u) z ∧ row z ∈ (Set.univ : Set (ZMod q))} =
        G.neighborSet (π u) := by
      ext z
      simp
    rw [e1] at h1
    have h3 : (S ∩ G.neighborSet (π u)).ncard ≤ {z | G.Adj (π u) z ∧ row z ∈ R}.ncard :=
      Set.ncard_le_ncard fun z hz => ⟨hz.2, hSU hz.1⟩
    have h4 : ((G.comap π).neighborSet u).ncard ≤
        (G.neighborSet (π u)).ncard + (S ∩ G.neighborSet (π u)).ncard :=
      ncard_preimage_le S (G.neighborSet (π u))
    have h5 : (((G.comap π).neighborSet u).ncard : ℝ) ≤
        (G.neighborSet (π u)).ncard + (S ∩ G.neighborSet (π u)).ncard := by exact_mod_cast h4
    have h6 : ((S ∩ G.neighborSet (π u)).ncard : ℝ) ≤
        {z | G.Adj (π u) z ∧ row z ∈ R}.ncard := by exact_mod_cast h3
    linarith

/-- The real-number bookkeeping of Section 4, with `T = q (p + 1)` between `s / λ` and `s`. -/
theorem final_ineq {e δ η lam p q r s : ℝ} (he0 : 0 < e) (he1 : e ≤ 1) (hη : η = e / 32)
    (hlam0 : 0 ≤ lam) (hlam : lam ≤ 1 + e / 8) (hδ : δ ≤ 1) (hp0 : 0 < p) (hq0 : 0 < q)
    (hp : 16 ≤ e * p) (hq : 16 ≤ e * q) (hs : 0 ≤ s)
    (hT1 : q * (p + 1) ≤ s) (hT2 : s ≤ lam * (q * (p + 1)))
    (hqp : q ≤ 2 * (1 + δ) * (p + 1))
    (hr : r * ((p ^ 2 + p + 1) * q) ≤ s ^ 2 - (p ^ 2 + p + 1) * q ^ 2 + (p ^ 2 + p + 1) * q) :
    (q + r) * (p + 1) + 2 * η * q ^ 2 ≤ (1 + e) * s := by
  subst hη
  have hM : 0 < p ^ 2 + p + 1 := by positivity
  have hMq : 0 < (p ^ 2 + p + 1) * q := by positivity
  have hZ : 0 ≤ s * q * (p ^ 2 + p + 1) := by positivity
  have a1 : (q + r) * ((p ^ 2 + p + 1) * q) * (p + 1) ≤
      (s ^ 2 + (p ^ 2 + p + 1) * q) * (p + 1) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    linarith
  have a2 : s ^ 2 * (p + 1) ≤ lam * (s * q * (p + 1) ^ 2) := by
    have := mul_le_mul_of_nonneg_left hT2 (by positivity : 0 ≤ s * (p + 1))
    linarith
  have a3 : lam * (s * q * p) ≤ lam * (s * q * (p ^ 2 + p + 1)) * (e / 16) := by
    have h1 := mul_le_mul_of_nonneg_right hp hp0.le
    have h2 : 0 ≤ e * (p + 1) := by positivity
    have h16 : 16 * p ≤ e * (p ^ 2 + p + 1) := by linarith
    have := mul_le_mul_of_nonneg_left h16 (by positivity : 0 ≤ lam * (s * q))
    linarith
  have a4 : (p ^ 2 + p + 1) * q * (p + 1) ≤ (p ^ 2 + p + 1) * s := by
    have := mul_le_mul_of_nonneg_left hT1 hM.le
    linarith
  have a5 : 16 * ((p ^ 2 + p + 1) * s) ≤ e * q * ((p ^ 2 + p + 1) * s) :=
    mul_le_mul_of_nonneg_right hq (by positivity)
  have a6 : 2 * (e / 32) * q ^ 2 * ((p ^ 2 + p + 1) * q) ≤
      e / 4 * (s * q * (p ^ 2 + p + 1)) := by
    have h1 := mul_le_mul_of_nonneg_left hqp hq0.le
    have h2 : 0 ≤ (1 - δ) * (q * (p + 1)) := mul_nonneg (by linarith) (by positivity)
    have hq2 : q ^ 2 ≤ 4 * s := by nlinarith
    have := mul_le_mul_of_nonneg_left hq2 (by positivity : 0 ≤ e / 16 * ((p ^ 2 + p + 1) * q))
    linarith
  have a7 : lam * (s * q * (p ^ 2 + p + 1)) ≤ (1 + e / 8) * (s * q * (p ^ 2 + p + 1)) :=
    mul_le_mul_of_nonneg_right hlam hZ
  have a8 := mul_le_mul_of_nonneg_right a7 he0.le
  have a9 : e * (e * (s * q * (p ^ 2 + p + 1))) ≤ 1 * (e * (s * q * (p ^ 2 + p + 1))) :=
    mul_le_mul_of_nonneg_right he1 (by positivity)
  have a10 : 0 ≤ e * (s * q * (p ^ 2 + p + 1)) := by positivity
  have key : ((q + r) * (p + 1) + 2 * (e / 32) * q ^ 2) * ((p ^ 2 + p + 1) * q) ≤
      ((1 + e) * s) * ((p ^ 2 + p + 1) * q) := by
    linarith
  exact le_of_mul_le_mul_right key hMq

/-- With `m = ⌊√(s / (2 λ))⌋₊`: `m² (2 λ) ≤ s < (m + 1)² (2 λ)`. -/
theorem floor_bounds {lam s : ℝ} (hlam : 0 < lam) (hs : 0 ≤ s) :
    ((⌊Real.sqrt (1 / (2 * lam) * s)⌋₊ : ℕ) : ℝ) ^ 2 * (2 * lam) ≤ s ∧
      s < (((⌊Real.sqrt (1 / (2 * lam) * s)⌋₊ : ℕ) : ℝ) + 1) ^ 2 * (2 * lam) := by
  have hw0 : 0 ≤ Real.sqrt (1 / (2 * lam) * s) := Real.sqrt_nonneg _
  have hww : Real.sqrt (1 / (2 * lam) * s) ^ 2 = 1 / (2 * lam) * s :=
    Real.sq_sqrt (by positivity)
  have h1 := pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le hw0) 2
  have h2 := pow_lt_pow_left₀ (Nat.lt_floor_add_one (Real.sqrt (1 / (2 * lam) * s))) hw0
    (two_ne_zero)
  rw [hww] at h1 h2
  have h3 : 1 / (2 * lam) * s * (2 * lam) = s := by field_simp
  constructor
  · have := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 2 * lam)
    linarith
  · have := mul_lt_mul_of_pos_right h2 (by positivity : (0 : ℝ) < 2 * lam)
    linarith

/-- From the choice of `m` and of the primes `p ∈ (m, (1 + δ) m]` and
`q ∈ (2 (p + 1), 2 (1 + δ) (p + 1)]` to `q (p + 1) ≤ s ≤ λ q (p + 1)`. -/
theorem T_bounds {δ lam s m p q : ℝ} (hδ0 : 0 < δ) (hlam : lam = (1 + δ) * (1 + 2 * δ) ^ 2)
    (hm0 : 0 ≤ m) (hm2 : m ^ 2 * (2 * lam) ≤ s) (hm2' : s < (m + 1) ^ 2 * (2 * lam))
    (hδm : 1 ≤ δ * m) (hmp : m + 1 ≤ p) (hpm : p ≤ (1 + δ) * m) (hpq : 2 * (p + 1) < q)
    (hqp : q ≤ (1 + δ) * (2 * (p + 1))) :
    q * (p + 1) ≤ s ∧ s ≤ lam * (q * (p + 1)) := by
  have hlam0 : 0 ≤ lam := by rw [hlam]; positivity
  have hp1 : p + 1 ≤ (1 + 2 * δ) * m := by linarith
  constructor
  · have h1 := mul_le_mul_of_nonneg_right hqp (by linarith : (0 : ℝ) ≤ p + 1)
    have h2 : (p + 1) ^ 2 ≤ ((1 + 2 * δ) * m) ^ 2 := pow_le_pow_left₀ (by linarith) hp1 2
    have h3 : 2 * (1 + δ) * ((1 + 2 * δ) * m) ^ 2 = m ^ 2 * (2 * lam) := by rw [hlam]; ring
    have h4 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 * (1 + δ))
    linarith
  · have h1 : (m + 1) ^ 2 ≤ (p + 1) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have h2 : 2 * (p + 1) * (p + 1) ≤ q * (p + 1) :=
      mul_le_mul_of_nonneg_right hpq.le (by linarith)
    have h3 := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 2 * lam)
    have h4 := mul_le_mul_of_nonneg_left h2 hlam0
    linarith

/-- With `q (p + 1) ≤ s ≤ λ q (p + 1)` and `λ ≤ 9 / 8`, the order `N = (p² + p + 1) q²` of the
Part B graph satisfies `N ≤ s² < 2 N`. -/
theorem N_bounds {lam p q s : ℝ} (hp0 : 0 < p) (hq0 : 0 < q) (hs0 : 0 ≤ s) (hlam1 : 1 ≤ lam)
    (hlam : lam ≤ 9 / 8) (hT1 : q * (p + 1) ≤ s) (hT2 : s ≤ lam * (q * (p + 1))) :
    (p ^ 2 + p + 1) * q ^ 2 ≤ s ^ 2 ∧ s ^ 2 < 2 * ((p ^ 2 + p + 1) * q ^ 2) := by
  have h1 : (q * (p + 1)) ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ (by positivity) hT1 2
  have h2 : s ^ 2 ≤ (lam * (q * (p + 1))) ^ 2 := pow_le_pow_left₀ hs0 hT2 2
  have h3 : lam ^ 2 ≤ 81 / 64 := by nlinarith
  have h4 : (p + 1) ^ 2 ≤ 3 / 2 * (p ^ 2 + p + 1) := by nlinarith [sq_nonneg (p - 1)]
  have h5 := mul_le_mul_of_nonneg_right h3 (sq_nonneg (q * (p + 1)))
  have h6 := mul_le_mul_of_nonneg_left h4 (sq_nonneg q)
  have h7 : 0 < (p ^ 2 + p + 1) * q ^ 2 := by positivity
  have h8 : 0 ≤ p * q ^ 2 := by positivity
  exact ⟨by linarith, by linarith⟩

/-- Write `n = N + a` with `N = M q²` and choose the number `r = a / (M q) + 1 ≤ q` of rows. -/
theorem split_n {M q n : ℕ} (hMq : 0 < M * q) (hNn : M * q ^ 2 ≤ n)
    (hn2 : n < 2 * (M * q ^ 2)) :
    ∃ a r : ℕ, M * q ^ 2 + a = n ∧ r ≤ q ∧ a ≤ r * (M * q) ∧ r * (M * q) ≤ a + M * q := by
  refine ⟨n - M * q ^ 2, (n - M * q ^ 2) / (M * q) + 1, by omega, ?_, ?_, ?_⟩
  · have h1 : M * q ^ 2 = q * (M * q) := by ring
    have h2 : (n - M * q ^ 2) / (M * q) < q := by
      rw [Nat.div_lt_iff_lt_mul hMq]
      omega
    omega
  · exact (Nat.lt_mul_div_succ _ hMq).le.trans_eq (mul_comm _ _)
  · calc ((n - M * q ^ 2) / (M * q) + 1) * (M * q)
        = (n - M * q ^ 2) / (M * q) * (M * q) + M * q := by ring
      _ ≤ (n - M * q ^ 2) + M * q := Nat.add_le_add_right (Nat.div_mul_le_self _ _) _

end C

theorem h2_of_parts (hP : ShortPrimes) (hB : PartB) :
    OMA.R_Erdos133_erdos_133_variants_asymptotic_R1.H2 := by
  intro ε hε
  obtain ⟨e, he0, he1, hee⟩ : ∃ e : ℝ, 0 < e ∧ e ≤ 1 ∧ e ≤ ε :=
    ⟨min ε 1, lt_min hε one_pos, min_le_right _ _, min_le_left _ _⟩
  obtain ⟨Q, hQ⟩ := hB (e / 32) (by positivity)
  obtain ⟨n₀, hn₀⟩ := hP (e / 48) (by positivity)
  set δ : ℝ := e / 48 with hδ
  have hδ0 : 0 < δ := by positivity
  set lam : ℝ := (1 + δ) * (1 + 2 * δ) ^ 2 with hlam_def
  have hlam1 : 1 ≤ lam :=
    one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ (by linarith))
  have hlam : lam ≤ 1 + e / 8 := by
    have h1 : δ * δ ≤ δ / 48 := by nlinarith
    have h2 : δ * δ * δ ≤ δ / 48 := by nlinarith
    have h3 : lam = 1 + 5 * δ + 8 * (δ * δ) + 4 * (δ * δ * δ) := by rw [hlam_def]; ring
    linarith
  have hκ0 : 0 < 1 / (2 * lam) := by positivity
  set K : ℕ := n₀ + Q + ⌈48 / e⌉₊ with hK
  have hm : Tendsto (fun n : ℕ => ⌊Real.sqrt (1 / (2 * lam) * Real.sqrt (n : ℝ))⌋₊)
      atTop atTop :=
    tendsto_nat_floor_atTop.comp (Real.tendsto_sqrt_atTop.comp
      ((Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hκ0))
  filter_upwards [hm.eventually_ge_atTop K] with n hn
  obtain ⟨hm2, hm2'⟩ :=
    C.floor_bounds (lt_of_lt_of_le one_pos hlam1) (Real.sqrt_nonneg (n : ℝ))
  set s : ℝ := Real.sqrt (n : ℝ) with hs
  set m : ℕ := ⌊Real.sqrt (1 / (2 * lam) * s)⌋₊ with hm_def
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg _)
  have hem : 48 ≤ e * m := by
    have h1 : 48 / e ≤ (⌈48 / e⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈48 / e⌉₊ : ℕ) : ℝ) ≤ m := by exact_mod_cast (show ⌈48 / e⌉₊ ≤ m by omega)
    have h3 : 48 / e ≤ m := h1.trans h2
    rw [div_le_iff₀ he0] at h3
    linarith
  obtain ⟨p, hp, hmp, hpm⟩ := hn₀ m (by omega)
  obtain ⟨q, hq, hpq, hqp⟩ := hn₀ (2 * (p + 1)) (by omega)
  push_cast at hqp
  obtain ⟨V, G, row, hfin, hcard, hrow, htf, hcn, hdeg⟩ := hQ p q hp hq (by omega) hpq.le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hmp' : (m : ℝ) + 1 ≤ p := by exact_mod_cast hmp
  have hpq' : 2 * ((p : ℝ) + 1) < q := by exact_mod_cast hpq
  have hδm : 1 ≤ δ * m := by rw [hδ]; linarith
  obtain ⟨hT1, hT2⟩ :=
    C.T_bounds hδ0 hlam_def (Nat.cast_nonneg _) hm2 hm2' hδm hmp' hpm hpq' hqp
  obtain ⟨hN1, hN2⟩ := C.N_bounds hp0 hq0 hs0 hlam1 (by linarith) hT1 hT2
  rw [hss] at hN1 hN2
  have hMq : 0 < (p ^ 2 + p + 1) * q := Nat.mul_pos (by positivity) hq.pos
  have hNn : (p ^ 2 + p + 1) * q ^ 2 ≤ n := by exact_mod_cast hN1
  have hn2 : n < 2 * ((p ^ 2 + p + 1) * q ^ 2) := by exact_mod_cast hN2
  obtain ⟨a, r, han, hrq, har, hr2⟩ := C.split_n hMq hNn hn2
  have hr3 : (r : ℝ) * (((p : ℝ) ^ 2 + p + 1) * q) ≤
      s ^ 2 - ((p : ℝ) ^ 2 + p + 1) * q ^ 2 + ((p : ℝ) ^ 2 + p + 1) * q := by
    have h1 : ((r * ((p ^ 2 + p + 1) * q) : ℕ) : ℝ) ≤ ((a + (p ^ 2 + p + 1) * q : ℕ) : ℝ) := by
      exact_mod_cast hr2
    have h2 : (((p ^ 2 + p + 1) * q ^ 2 + a : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast han
    push_cast at h1 h2
    rw [hss]
    linarith
  have hf := @C.dup V hfin G p q row (e / 32) hq hcard hrow htf hcn hdeg a r hrq har
  rw [han] at hf
  have hep : e * m ≤ e * p := mul_le_mul_of_nonneg_left (by linarith) he0.le
  have heq : e * p ≤ e * q := mul_le_mul_of_nonneg_left (by linarith) he0.le
  have hfin2 := C.final_ineq (e := e) (δ := δ) (η := e / 32) (lam := lam) (r := (r : ℝ))
    he0 he1 rfl (by linarith) hlam (by linarith) hp0 hq0 (by linarith) (by linarith) hs0
    hT1 hT2 (by linarith) hr3
  calc (Erdos133.f n : ℝ) ≤ _ := hf
    _ ≤ (1 + e) * s := hfin2
    _ ≤ (1 + ε) * s := by gcongr

end Korsky133

/-
Primes in short intervals. This block is copied from the merged Left to Solve proof of
Erdos133.erdos_133.variants.furedi_seress, which took it from the merged proof of step H1 of
reduction Erdos30.erdos_30.variants.singer.R1. Modified for this file: the source URL in the
credit below is replaced by the project name; nothing else in the block is changed.

Step H1 of reduction Erdos30.erdos_30.variants.singer.R1: primes in short intervals,
  for every δ > 0 and every large n there is a prime p with n < p ≤ (1 + δ) n.

It is derived (theorem OMA.PNT.h1, at the end of this file) from the asymptotic θ(x) ~ x for
Chebyshev's function θ: if (n, (1 + δ) n] contained no prime, then θ((1 + δ) n) = θ(n), which
contradicts θ((1 + δ) n) - θ(n) ~ δ n.

The proof of θ(x) ~ x (and of the weak prime number theorem it rests on, via the Wiener-Ikehara
tauberian theorem) is ported from the PrimeNumberTheoremAnd project, commit 55270df807,
by Alex Kontorovich, Terence Tao and the project's contributors, used under the Apache License 2.0.
Files used, in this order (each in its own section below):
  PrimeNumberTheoremAnd/Mathlib/Algebra/Notation/Support.lean
  PrimeNumberTheoremAnd/Mathlib/Analysis/Asymptotics/Asymptotics.lean
  PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean
  PrimeNumberTheoremAnd/Sobolev.lean
  PrimeNumberTheoremAnd/Fourier.lean
  PrimeNumberTheoremAnd/SmoothExistence.lean
  PrimeNumberTheoremAnd/Wiener.lean (up to and including theorem WeakPNT)
  PrimeNumberTheoremAnd/Consequences.lean (only add_isLittleO'', WeakPNT', WeakPNT'',
    isLittleO_sqrt_mul_log and chebyshev_asymptotic)
Modifications: imports merged into the single import above; blueprint annotations and all
attributes (blueprint, ext, continuity, fun_prop, gcongr, norm_cast) and option settings removed,
with the call sites that relied on them adjusted (an explicit CS.ext lemma, explicit continuity
facts handed to fun_prop, an explicit monotonicity step in place of gcongr); the proofs of
second_fourier and limiting_cor_aux were rewritten so that they compile without the
backward.isDefEq.respectTransparency option; four unproved and unused lemmas of Wiener.lean
(prelim_decay_2, prelim_decay_3, decay_alt and the definition AbsolutelyContinuous) were deleted.
The proof of H1 from chebyshev_asymptotic (OMA.PNT.exists_prime_of_theta_lt, OMA.PNT.h1) is new.
-/

-- Ported from PrimeNumberTheoremAnd: Mathlib/Algebra/Notation/Support.lean, Mathlib/Analysis/Asymptotics/Asymptotics.lean, Mathlib/Analysis/SpecialFunctions/Log/Basic.lean
section PNTX_Base

namespace Function

variable {α : Type*} [Zero α]

theorem support_id : support (id : α → α) = {0}ᶜ := by
  ext; simp

theorem support_id' {α : Type*} [Zero α] : support (fun x : α ↦ x) = {0}ᶜ :=
  support_id

end Function


open Filter Topology

namespace Asymptotics

variable {α : Type*} {β : Type*} {E : Type*} {F : Type*} {G : Type*} {E' : Type*}
  {F' : Type*} {G' : Type*} {E'' : Type*} {F'' : Type*} {G'' : Type*} {R : Type*}
  {R' : Type*} {𝕜 : Type*} {𝕜' : Type*}

variable [Norm E] [Norm F] [Norm G]

variable [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F'] [SeminormedAddCommGroup G']
  [NormedAddCommGroup E''] [NormedAddCommGroup F''] [NormedAddCommGroup G''] [SeminormedRing R]
  [SeminormedRing R']


theorem isLittleO_const_id_cocompact [ProperSpace F'']
    (c : E'') : (fun _x : F'' => c) =o[cocompact F''] id :=
  isLittleO_const_left.2 <| Or.inr tendsto_norm_cocompact_atTop

-- to replace existing `isLittleO_const_id_atTop`
theorem isLittleO_const_id_atTop2 [LinearOrder F''] [NoMaxOrder F''] [ClosedIciTopology F'']
    [ProperSpace F''] (c : E'') : (fun _x : F'' => c) =o[atTop] id :=
 (isLittleO_const_id_cocompact c).mono atTop_le_cocompact

-- to replace existing `isLittleO_const_id_atBot`
theorem isLittleO_const_id_atBot2 [LinearOrder F''] [NoMinOrder F''] [ClosedIicTopology F'']
    [ProperSpace F''] (c : E'') : (fun _x : F'' => c) =o[atBot] id :=
  (isLittleO_const_id_cocompact c).mono atBot_le_cocompact

theorem _root_.Filter.Eventually.natCast {f : ℝ → Prop} (hf : ∀ᶠ x in atTop, f x) :
    ∀ᶠ n : ℕ in atTop, f n :=
  tendsto_natCast_atTop_atTop.eventually hf

theorem IsBigO.natCast {f g : ℝ → E} (h : f =O[atTop] g) :
    (fun n : ℕ => f n) =O[atTop] fun n : ℕ => g n :=
  h.comp_tendsto tendsto_natCast_atTop_atTop

end Asymptotics


open Filter Real

/-- log^b x / x^a goes to zero at infinity if a is positive. -/
theorem Real.tendsto_pow_log_div_pow_atTop (a : ℝ) (b : ℝ) (ha : 0 < a) :
    Filter.Tendsto (fun x ↦ log x ^ b / x^a) Filter.atTop (nhds 0) := by
  apply Asymptotics.isLittleO_iff_tendsto' _|>.mp <| isLittleO_log_rpow_rpow_atTop _ ha
  filter_upwards [eventually_gt_atTop 0] with x hx
  intro h
  rw [rpow_eq_zero hx.le ha.ne.symm] at h
  exfalso
  linarith

end PNTX_Base

-- Ported from PrimeNumberTheoremAnd: Sobolev.lean
section PNTX_Sobolev

open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

structure CS (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  h1 : ContDiff ℝ n toFun
  h2 : HasCompactSupport toFun

theorem CS.ext {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : CS n E}
    (h : f.toFun = g.toFun) : f = g := by
  cases f; cases g; cases h; rfl

structure trunc extends (CS 2 ℝ) where
  h3 : (Set.Icc (-1) (1)).indicator 1 ≤ toFun
  h4 : toFun ≤ Set.indicator (Set.Ioo (-2) (2)) 1

structure W1 (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  smooth : ContDiff ℝ n toFun
  integrable : ∀ ⦃k⦄, k ≤ n → Integrable (iteratedDeriv k toFun)

abbrev W21 := W1 2 ℂ

section lemmas

noncomputable def funscale {E : Type*} (g : ℝ → E) (R x : ℝ) : E := g (R⁻¹ • x)

lemma contDiff_ofReal : ContDiff ℝ ∞ ofReal := by
  have key x : HasDerivAt ofReal 1 x := hasDerivAt_id x |>.ofReal_comp
  have key' : deriv ofReal = fun _ => 1 := by ext x ; exact (key x).deriv
  refine contDiff_infty_iff_deriv.mpr ⟨fun x => (key x).differentiableAt, ?_⟩
  simpa [key'] using contDiff_const

omit [NormedSpace ℝ E] in
lemma tendsto_funscale {f : ℝ → E} (hf : ContinuousAt f 0) (x : ℝ) :
    Tendsto (fun R => funscale f R x) atTop (𝓝 (f 0)) :=
  hf.tendsto.comp (by simpa using tendsto_inv_atTop_zero.mul_const x)

end lemmas

namespace CS

variable {f : CS n E} {R x v : ℝ}

instance : CoeFun (CS n E) (fun _ => ℝ → E) where coe := CS.toFun

instance : Coe (CS n ℝ) (CS n ℂ) where coe f := ⟨fun x => f x,
  contDiff_ofReal.of_le (mod_cast le_top) |>.comp f.h1, f.h2.comp_left (g := ofReal) rfl⟩

def neg (f : CS n E) : CS n E where
  toFun := -f
  h1 := f.h1.neg
  h2 := by simpa [HasCompactSupport, tsupport] using f.h2

instance : Neg (CS n E) where neg := neg

@[simp] lemma neg_apply {x : ℝ} : (-f) x = - (f x) := rfl

def smul (R : ℝ) (f : CS n E) : CS n E := ⟨R • f, f.h1.const_smul R, f.h2.smul_left⟩

instance : HSMul ℝ (CS n E) (CS n E) where hSMul := smul

@[simp] lemma smul_apply : (R • f) x = R • f x := rfl

lemma continuous (f : CS n E) : Continuous f := f.h1.continuous

noncomputable def deriv (f : CS (n + 1) E) : CS n E where
  toFun := _root_.deriv f
  h1 := (contDiff_succ_iff_deriv.mp f.h1).2.2
  h2 := f.h2.deriv

lemma hasDerivAt (f : CS (n + 1) E) (x : ℝ) : HasDerivAt f (f.deriv x) x :=
  (f.h1.differentiable (by simp)).differentiableAt.hasDerivAt

lemma deriv_apply {f : CS (n + 1) E} {x : ℝ} : f.deriv x = _root_.deriv f x := rfl

lemma deriv_smul {f : CS (n + 1) E} : (R • f).deriv = R • f.deriv := by
  refine CS.ext (funext fun x => ?_) ; exact (f.hasDerivAt x |>.const_smul R).deriv

noncomputable def scale (g : CS n E) (R : ℝ) : CS n E := by
  by_cases h : R = 0
  · exact ⟨0, contDiff_const, by simp [HasCompactSupport, tsupport]⟩
  · refine ⟨fun x => funscale g R x, ?_, ?_⟩
    · exact g.h1.comp (contDiff_const_smul R⁻¹)
    · exact g.h2.comp_smul (inv_ne_zero h)

lemma deriv_scale {f : CS (n + 1) E} : (f.scale R).deriv = R⁻¹ • f.deriv.scale R := by
  refine CS.ext (funext fun v => ?_) ; by_cases hR : R = 0
  · simp [hR, scale, deriv]
  · simp only [scale, hR, ↓reduceDIte, smul_apply]
    exact ((f.hasDerivAt (R⁻¹ • v)).scomp v
      (by simpa using! (hasDerivAt_id v).const_smul R⁻¹)).deriv

lemma deriv_scale' {f : CS (n + 1) E} :
    (f.scale R).deriv v = R⁻¹ • f.deriv (R⁻¹ • v) := by
  rw [deriv_scale, smul_apply]
  by_cases hR : R = 0 <;> simp [hR, scale, funscale]

lemma hasDerivAt_scale (f : CS (n + 1) E) (R x : ℝ) :
    HasDerivAt (f.scale R) (R⁻¹ • _root_.deriv f (R⁻¹ • x)) x := by
  convert hasDerivAt (f.scale R) x ; rw [deriv_scale'] ; rfl

lemma tendsto_scale (f : CS n E) (x : ℝ) : Tendsto (fun R => f.scale R x) atTop (𝓝 (f 0)) := by
  apply (tendsto_funscale f.continuous.continuousAt x).congr'
  filter_upwards [eventually_ne_atTop 0] with R hR ; simp [scale, hR]

lemma bounded : ∃ C, ∀ v, ‖f v‖ ≤ C := by
  obtain ⟨x, hx⟩ :=
    (continuous_norm.comp f.continuous).exists_forall_ge_of_hasCompactSupport f.h2.norm
  exact ⟨_, hx⟩

end CS

namespace trunc

instance : CoeFun trunc (fun _ => ℝ → ℝ) where coe f := f.toFun

instance : Coe trunc (CS 2 ℝ) where coe := trunc.toCS

lemma nonneg (g : trunc) (x : ℝ) : 0 ≤ g x := (Set.indicator_nonneg (by simp) x).trans (g.h3 x)

lemma le_one (g : trunc) (x : ℝ) : g x ≤ 1 :=
  (g.h4 x).trans <| Set.indicator_le_self' (by simp) x

lemma zero (g : trunc) : g =ᶠ[𝓝 0] 1 := by
  have : Set.Icc (-1) 1 ∈ 𝓝 (0 : ℝ) := by apply Icc_mem_nhds <;> linarith
  exact eventually_of_mem this (fun x hx => le_antisymm (g.le_one x) (by simpa [hx] using g.h3 x))

@[simp] lemma zero_at {g : trunc} : g 0 = 1 := g.zero.eq_of_nhds

end trunc

namespace W1

instance : CoeFun (W1 n E) (fun _ => ℝ → E) where coe := W1.toFun

lemma continuous (f : W1 n E) : Continuous f := f.smooth.continuous

lemma differentiable (f : W1 (n + 1) E) : Differentiable ℝ f :=
  f.smooth.differentiable (by simp)

lemma iteratedDeriv_sub {f g : ℝ → E} (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    iteratedDeriv n (f - g) = iteratedDeriv n f - iteratedDeriv n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    have hf' : ContDiff ℝ n (deriv f) := hf.iterate_deriv' n 1
    have hg' : ContDiff ℝ n (deriv g) := hg.iterate_deriv' n 1
    have hfg : deriv (f - g) = deriv f - deriv g := by
      ext x ; apply deriv_sub
      · exact (hf.differentiable (by simp)).differentiableAt
      · exact (hg.differentiable (by simp)).differentiableAt
    simp_rw [iteratedDeriv_succ', ← ih hf' hg', hfg]

noncomputable def deriv (f : W1 (n + 1) E) : W1 n E where
  toFun := _root_.deriv f
  smooth := contDiff_succ_iff_deriv.mp f.smooth |>.2.2
  integrable k hk := by
    simpa [iteratedDeriv_succ'] using f.integrable (Nat.succ_le_succ hk)

lemma hasDerivAt (f : W1 (n + 1) E) (x : ℝ) : HasDerivAt f (f.deriv x) x :=
  f.differentiable.differentiableAt.hasDerivAt

def sub (f g : W1 n E) : W1 n E where
  toFun := f - g
  smooth := f.smooth.sub g.smooth
  integrable k hk := by
    have hf : ContDiff ℝ k f := f.smooth.of_le (by simp [hk])
    have hg : ContDiff ℝ k g := g.smooth.of_le (by simp [hk])
    simpa [iteratedDeriv_sub hf hg] using (f.integrable hk).sub (g.integrable hk)

instance : Sub (W1 n E) where sub := sub

lemma integrable_iteratedDeriv_Schwarz {f : 𝓢(ℝ, ℂ)} : Integrable (iteratedDeriv n f) := by
  induction n generalizing f with
  | zero => exact f.integrable
  | succ n ih => simpa [iteratedDeriv_succ'] using! ih (f := SchwartzMap.derivCLM ℝ ℂ f)

noncomputable def of_Schwartz (f : 𝓢(ℝ, ℂ)) : W1 n ℂ where
  toFun := f
  smooth := f.smooth n
  integrable _ _ := integrable_iteratedDeriv_Schwarz

end W1

namespace W21

variable {f : W21}

noncomputable def norm (f : ℝ → ℂ) : ℝ :=
    (∫ v, ‖f v‖) + (4 * π ^ 2)⁻¹ * (∫ v, ‖deriv (deriv f) v‖)

lemma norm_nonneg {f : ℝ → ℂ} : 0 ≤ norm f :=
  add_nonneg (integral_nonneg (fun t => by simp))
    (mul_nonneg (by positivity) (integral_nonneg (fun t => by simp)))

noncomputable instance : Norm W21 where norm := norm ∘ W1.toFun

noncomputable instance : Coe 𝓢(ℝ, ℂ) W21 where coe := W1.of_Schwartz

def ofCS2 (f : CS 2 ℂ) : W21 := by
  refine ⟨f, f.h1, fun k hk => ?_⟩ ; match k with
  | 0 => exact f.h1.continuous.integrable_of_hasCompactSupport f.h2
  | 1 => simpa using (f.h1.continuous_deriv one_le_two).integrable_of_hasCompactSupport f.h2.deriv
  | 2 => simpa [iteratedDeriv_succ] using
    (f.h1.iterate_deriv' 0 2).continuous.integrable_of_hasCompactSupport f.h2.deriv.deriv

instance : Coe (CS 2 ℂ) W21 where coe := ofCS2

instance : HMul (CS 2 ℂ) W21 (CS 2 ℂ) where
  hMul g f := ⟨g * f, g.h1.mul f.smooth, g.h2.mul_right⟩

instance : HMul (CS 2 ℝ) W21 (CS 2 ℂ) where hMul g f := (g : CS 2 ℂ) * f

lemma hf (f : W21) : Integrable f := f.integrable zero_le_two

lemma hf' (f : W21) : Integrable (deriv f) := by
  simpa [iteratedDeriv_succ] using f.integrable one_le_two

lemma hf'' (f : W21) : Integrable (deriv (deriv f))  := by
  simpa [iteratedDeriv_succ] using f.integrable le_rfl

end W21

theorem W21_approximation (f : W21) (g : trunc) :
    Tendsto (fun R => ‖f - (g.scale R * f : W21)‖) atTop (𝓝 0) := by

  -- Definitions
  let f' := f.deriv
  let f'' := f'.deriv
  let g' := (g : CS 2 ℝ).deriv
  let g'' := g'.deriv
  let h R v := 1 - g.scale R v
  let h' R := - (g.scale R).deriv
  let h'' R := - (g.scale R).deriv.deriv

  -- Properties of h
  have ch {R} : Continuous (fun v => (h R v : ℂ)) :=
    continuous_ofReal.comp <| continuous_const.sub (CS.continuous _)
  have ch' {R} : Continuous (fun v => (h' R v : ℂ)) := continuous_ofReal.comp (CS.continuous _)
  have ch'' {R} : Continuous (fun v => (h'' R v : ℂ)) := continuous_ofReal.comp (CS.continuous _)
  have dh R v : HasDerivAt (h R) (h' R v) v := by
    convert! CS.hasDerivAt_scale (g : CS 2 ℝ) R v |>.const_sub 1 using 1
    simp [h', CS.deriv_scale', show g.deriv.toFun = deriv g.toFun from rfl]
  have dh' R v : HasDerivAt (h' R) (h'' R v) v := ((g.scale R).deriv.hasDerivAt v).neg
  have hh1 R v : |h R v| ≤ 1 := by
    by_cases hR : R = 0 <;>
      simp only [CS.scale, funscale, smul_eq_mul, hR, ↓reduceDIte, Pi.zero_apply, sub_zero,
        abs_one, le_refl, h]
    rw [abs_le] ; constructor <;>
    linarith [g.le_one (R⁻¹ * v), g.nonneg (R⁻¹ * v)]
  have vR v : Tendsto (fun R : ℝ => v * R⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul v

  -- Proof
  convert_to Tendsto (fun R => W21.norm (fun v => h R v * f v)) atTop (𝓝 0)
  · ext R ; change W21.norm _ = _ ; congr ; ext v ; simp [h, sub_mul] ; rfl
  rw [show (0 : ℝ) = 0 + ((4 * π ^ 2)⁻¹ : ℝ) * 0 by simp]
  refine Tendsto.add ?_ (Tendsto.const_mul _ ?_)

  · let F R v := ‖h R v * f v‖
    have eh v : ∀ᶠ R in atTop, h R v = 0 := by
      filter_upwards [(vR v).eventually g.zero, eventually_ne_atTop 0] with R hR hR'
      simp [h, hR, CS.scale, hR', funscale, mul_comm R⁻¹]
    have e1 : ∀ᶠ (n : ℝ) in atTop, AEStronglyMeasurable (F n) volume := by
      apply Eventually.of_forall ; intro R
      exact (ch.mul f.continuous).norm.aestronglyMeasurable
    have e2 : ∀ᶠ (n : ℝ) in atTop, ∀ᵐ (a : ℝ), ‖F n a‖ ≤ ‖f a‖ := by
      apply Eventually.of_forall ; intro R
      apply Eventually.of_forall ; intro v
      simpa [F] using mul_le_mul (hh1 R v) le_rfl (by simp) zero_le_one
    have e4 : ∀ᵐ (a : ℝ), Tendsto (fun n ↦ F n a) atTop (𝓝 0) := by
      apply Eventually.of_forall ; intro v
      apply tendsto_nhds_of_eventually_eq ; filter_upwards [eh v] with R hR ; simp [F, hR]
    simpa [F] using tendsto_integral_filter_of_dominated_convergence _ e1 e2 f.hf.norm e4

  · let F R v := ‖h'' R v * f v + 2 * h' R v * f' v + h R v * f'' v‖
    convert_to Tendsto (fun R ↦ ∫ (v : ℝ), F R v) atTop (𝓝 0)
    · have this R v :
        deriv (deriv (fun v => h R v * f v)) v =
          h'' R v * f v + 2 * h' R v * f' v + h R v * f'' v := by
        have df v : HasDerivAt f (f' v) v := f.hasDerivAt v
        have df' v : HasDerivAt f' (f'' v) v := f'.hasDerivAt v
        have l3 v : HasDerivAt (fun v => h R v * f v) (h' R v * f v + h R v * f' v) v :=
          (dh R v).ofReal_comp.mul (df v)
        have l5 : HasDerivAt (fun v => h' R v * f v) (h'' R v * f v + h' R v * f' v) v :=
          (dh' R v).ofReal_comp.mul (df v)
        have l7 : HasDerivAt (fun v => h R v * f' v) (h' R v * f' v + h R v * f'' v) v :=
          (dh R v).ofReal_comp.mul (df' v)
        have d1 : deriv (fun v => h R v * f v) = fun v => h' R v * f v + h R v * f' v :=
          funext (fun v => (l3 v).deriv)
        rw [d1] ; convert! (l5.add l7).deriv using 1 ; ring
      simp_rw [this, F]

    obtain ⟨c1, mg'⟩ := g'.bounded
    obtain ⟨c2, mg''⟩ := g''.bounded
    let bound v := c2 * ‖f v‖ + 2 * c1 * ‖f' v‖ + ‖f'' v‖
    have e1 : ∀ᶠ (n : ℝ) in atTop, AEStronglyMeasurable (F n) volume := by
      apply Eventually.of_forall ; intro R ; apply (Continuous.norm ?_).aestronglyMeasurable
      exact ((ch''.mul f.continuous).add ((continuous_const.mul ch').mul f.deriv.continuous)).add
        (ch.mul f.deriv.deriv.continuous)
    have e2 : ∀ᶠ R in atTop, ∀ᵐ (a : ℝ), ‖F R a‖ ≤ bound a := by
      have hc1 : ∀ᶠ R in atTop, ∀ v, |h' R v| ≤ c1 := by
        filter_upwards [eventually_ge_atTop 1] with R hR v
        have hR' : R ≠ 0 := by linarith
        have : 0 ≤ R := by linarith
        simp only [CS.deriv_scale, CS.neg_apply, CS.smul_apply, smul_eq_mul, abs_neg, abs_mul,
          abs_inv, abs_eq_self.mpr this, ge_iff_le, h']
        simp only [CS.scale, hR', ↓reduceDIte, funscale, smul_eq_mul]
        convert_to _ ≤ c1 * 1
        · simp
        · rw [mul_comm]
          apply mul_le_mul (mg' _)
            (inv_le_of_inv_le₀ (by linarith) (by simpa using hR)) (by positivity)
          exact (abs_nonneg _).trans (mg' 0)
      have hc2 : ∀ᶠ R in atTop, ∀ v, |h'' R v| ≤ c2 := by
        filter_upwards [eventually_ge_atTop 1] with R hR v
        have e1 : 0 ≤ R := by linarith
        have e2 : R⁻¹ ≤ 1 := inv_le_of_inv_le₀ (by linarith) (by simpa using hR)
        have e3 : R ≠ 0 := by linarith
        simp only [CS.deriv_scale, CS.deriv_smul, CS.neg_apply, CS.smul_apply, smul_eq_mul, abs_neg,
          abs_mul, abs_inv, abs_eq_self.mpr e1, ge_iff_le, h'']
        convert_to _ ≤ 1 * (1 * c2)
        · simp
        apply mul_le_mul e2 ?_ (by positivity) zero_le_one
        apply mul_le_mul e2 ?_ (by positivity) zero_le_one
        simp only [CS.scale, e3, ↓reduceDIte, funscale, smul_eq_mul] ; apply mg''
      filter_upwards [hc1, hc2] with R hc1 hc2
      apply Eventually.of_forall ; intro v ; specialize hc1 v ; specialize hc2 v
      simp only [F, bound, norm_norm]
      refine (norm_add_le _ _).trans ?_ ; apply add_le_add
      · refine (norm_add_le _ _).trans ?_ ; apply add_le_add <;> simp only [Complex.norm_mul,
        Complex.norm_ofNat, norm_real, norm_eq_abs] <;> gcongr
      · simpa using mul_le_mul (hh1 R v) le_rfl (by simp) zero_le_one
    have e3 : Integrable bound volume :=
      (((f.hf.norm).const_mul _).add ((f.hf'.norm).const_mul _)).add f.hf''.norm
    have e4 : ∀ᵐ (a : ℝ), Tendsto (fun n ↦ F n a) atTop (𝓝 0) := by
      apply Eventually.of_forall ; intro v
      have evg' : g' =ᶠ[𝓝 0] 0 := by convert! ← g.zero.deriv ; exact deriv_const' _
      have evg'' : g'' =ᶠ[𝓝 0] 0 := by convert! ← evg'.deriv ; exact deriv_const' _
      refine tendsto_norm_zero.comp <| (ZeroAtFilter.add ?_ ?_).add ?_
      · have eh'' v : ∀ᶠ R in atTop, h'' R v = 0 := by
          filter_upwards [(vR v).eventually evg'', eventually_ne_atTop 0] with R hR hR'
          simp only [CS.deriv_scale, CS.deriv_smul, CS.neg_apply, CS.smul_apply, smul_eq_mul,
            neg_eq_zero, mul_eq_zero, inv_eq_zero, hR', false_or, h'']
          simp only [CS.scale, hR', ↓reduceDIte, funscale, smul_eq_mul, mul_comm R⁻¹]
          exact hR
        apply tendsto_nhds_of_eventually_eq
        filter_upwards [eh'' v] with R hR ; simp [hR]
      · have eh' v : ∀ᶠ R in atTop, h' R v = 0 := by
          filter_upwards [(vR v).eventually evg'] with R hR
          simp [g'] at hR
          simp [h', CS.deriv_scale', mul_comm R⁻¹, hR]
        apply tendsto_nhds_of_eventually_eq
        filter_upwards [eh' v] with R hR ; simp [hR]
      · simpa [h] using! ((g.tendsto_scale v).const_sub 1).ofReal.mul tendsto_const_nhds
    simpa [F] using tendsto_integral_filter_of_dominated_convergence bound e1 e2 e3 e4

end PNTX_Sobolev

-- Ported from PrimeNumberTheoremAnd: Fourier.lean
section PNTX_Fourier

open FourierTransform Real Complex MeasureTheory Filter Topology BoundedContinuousFunction
  SchwartzMap VectorFourier BigOperators

local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩

section lemmas

@[simp]
theorem nnnorm_eq_of_mem_circle (z : Circle) : ‖z.val‖₊ = 1 :=
  NNReal.coe_eq_one.mp (by simp [Circle.norm_coe])

@[simp]
theorem nnnorm_circle_smul (z : Circle) (s : ℂ) : ‖z • s‖₊ = ‖s‖₊ := by
  simp [show z • s = z.val * s from rfl]

noncomputable def e (u : ℝ) : ℝ →ᵇ ℂ where
  toFun v := 𝐞 (-v * u)
  map_bounded' :=
    ⟨2, fun x y => (dist_le_norm_add_norm _ _).trans (by simp [Circle.norm_coe, one_add_one_eq_two])⟩

@[simp] lemma e_apply (u : ℝ) (v : ℝ) : e u v = 𝐞 (-v * u) := rfl

theorem hasDerivAt_e {u x : ℝ} : HasDerivAt (e u) (-2 * π * u * I * e u x) x := by
  have l2 : HasDerivAt (fun v => -v * u) (-u) x := by
    simpa only [neg_mul_comm] using hasDerivAt_mul_const (-u)
  convert! (hasDerivAt_fourierChar (-x * u)).scomp x l2 using 1
  change _ = ((-u : ℝ) : ℂ) * _ -- `scomp` introduces ℝ-smul on ℂ, which we undo
  simp ; ring

lemma fourierIntegral_deriv_aux2 (e : ℝ →ᵇ ℂ) {f : ℝ → ℂ} (hf : Integrable f) :
    Integrable (⇑e * f) :=
  hf.bdd_mul e.continuous.aestronglyMeasurable (ae_of_all _ e.norm_coe_le_norm)

@[simp] lemma F_neg {f : ℝ → ℂ} {u : ℝ} : 𝓕 (fun x => -f x) u = - 𝓕 f u := by
  simp [fourier_eq, integral_neg]

@[simp] lemma F_add {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x + g x) x = 𝓕 f x + 𝓕 g x := by
  have : Continuous fun p : ℝ × ℝ ↦ ((innerₗ ℝ) p.1) p.2 := continuous_inner
  have := fourierIntegral_add continuous_fourierChar this hf hg
  exact congr_fun this x

@[simp] lemma F_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x - g x) x = 𝓕 f x - 𝓕 g x := by
  simpa [sub_eq_add_neg, Pi.neg_def] using F_add hf hg.neg x

@[simp] lemma F_mul {f : ℝ → ℂ} {c : ℂ} {u : ℝ} :
    𝓕 (fun x => c * f x) u = c * 𝓕 f u := by
  exact congr_fun (VectorFourier.fourierIntegral_const_smul 𝐞 _ _ f c) u

end lemmas

theorem fourierIntegral_self_add_deriv_deriv (f : W21) (u : ℝ) :
    (1 + u ^ 2) * 𝓕 (f : ℝ → ℂ) u =
      𝓕 (fun u : ℝ => (f u - (1 / (4 * π ^ 2)) * deriv^[2] f u : ℂ)) u := by
  have l1 : Integrable (fun x => (((π : ℂ) ^ 2)⁻¹ * 4⁻¹) * deriv (deriv f) x) := by
    apply Integrable.const_mul ; simpa [iteratedDeriv_succ] using f.integrable le_rfl
  have l4 : Differentiable ℝ f := f.differentiable
  have l5 : Differentiable ℝ (deriv f) := f.deriv.differentiable
  simp [f.hf, l1, add_mul, Real.fourier_deriv f.hf' l5 f.hf'', Real.fourier_deriv f.hf l4 f.hf']
  field_simp [pi_ne_zero] ; ring_nf ; simp

@[simp] lemma deriv_ofReal : deriv ofReal = fun _ => 1 := by
  ext x ; exact ((hasDerivAt_id x).ofReal_comp).deriv

/-- If, eventually in `T`, the integrand `f T` is bounded on `uIoc lo hi` by `B T`
and `B T * |hi - lo| → 0`, then the interval integral `∫ x in lo..hi, f T x → 0`. -/
lemma tendsto_intervalIntegral_zero_of_uniform_norm_bound
    {f : ℝ → ℝ → ℂ} {lo hi : ℝ} {B : ℝ → ℝ}
    (hB : Filter.Tendsto (fun T : ℝ => B T * |hi - lo|) Filter.atTop (nhds 0))
    (hf : ∀ᶠ T in Filter.atTop, ∀ x ∈ Set.uIoc lo hi, ‖f T x‖ ≤ B T) :
    Filter.Tendsto (fun T : ℝ => ∫ x in lo..hi, f T x) Filter.atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) ?_ hB
  filter_upwards [hf] with T hT
  exact intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => hT x hx)

/-- The decay `K * (log (T + 2) / (T + 2)) → 0` as `T → ∞`, for any constant `K`. -/
lemma tendsto_const_mul_log_add_two_div_add_two_atTop (K : ℝ) :
    Filter.Tendsto (fun T : ℝ => K * (Real.log (T + 2) / (T + 2)))
      Filter.atTop (nhds 0) := by
  have h0 : Filter.Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (nhds 0) := by
    simpa using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num : (1 : ℝ) ≠ 0))
  have hshift : Filter.Tendsto (fun T : ℝ => Real.log (T + 2) / (T + 2))
      Filter.atTop (nhds 0) := by
    have := h0.comp (tendsto_atTop_add_const_right Filter.atTop 2 tendsto_id)
    simpa [Function.comp_def] using this
  simpa using hshift.const_mul K

/-- Fourier-transform decay from an integrable derivative: for integrable,
differentiable `g` with integrable derivative, `‖𝓕 g w‖ ≤ (∫ ‖deriv g x‖) / (2π·|w|)`. -/
lemma norm_fourier_le_integral_deriv_div
    (g : ℝ → ℂ) (hg : Integrable g) (hdiff : Differentiable ℝ g)
    (hg' : Integrable (deriv g)) {w : ℝ} (hw : w ≠ 0) :
    ‖𝓕 g w‖ ≤ (∫ x, ‖deriv g x‖ ∂volume) / ((2 * Real.pi) * |w|) := by
  have hmul :
      𝓕 (deriv g) w = (2 * Real.pi * Complex.I * (w : ℂ)) * 𝓕 g w := by
    have h := congrFun (Real.fourier_deriv hg hdiff hg') w
    simpa [smul_eq_mul, mul_assoc] using h
  have h_fourier :
      ‖𝓕 (deriv g) w‖ ≤ ∫ x, ‖deriv g x‖ ∂volume := by
    exact VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 volume (innerₗ ℝ)
      (deriv g) w
  have hleft :
      ((2 * Real.pi) * |w|) * ‖𝓕 g w‖ =
        ‖(2 * Real.pi * Complex.I * (w : ℂ)) * 𝓕 g w‖ := by
    have htwopi : ‖(2 * ↑Real.pi : ℂ)‖ = 2 * Real.pi := by
      rw [norm_mul, Complex.norm_two, Complex.norm_of_nonneg Real.pi_pos.le]
    have hwc : ‖(w : ℂ)‖ = |w| := by rw [norm_real, Real.norm_eq_abs]
    rw [norm_mul, norm_mul, norm_mul, htwopi, norm_I, hwc]
    ring
  have hmain : ((2 * Real.pi) * |w|) * ‖𝓕 g w‖ ≤ ∫ x, ‖deriv g x‖ ∂volume := by
    rw [hleft, ← hmul]
    exact h_fourier
  have hpos : 0 < (2 * Real.pi) * |w| := by
    positivity
  exact (le_div_iff₀ hpos).mpr (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmain)

/-- The oscillatory-integral form of the decay bound: for `0 < T`,
`‖∫ g y · exp(T·i·y)‖ ≤ (∫ ‖deriv g x‖) / T`. -/
lemma norm_oscillatory_integral_le_integral_deriv_div
    (g : ℝ → ℂ) (hg : Integrable g) (hdiff : Differentiable ℝ g)
    (hg' : Integrable (deriv g)) {T : ℝ} (hT : 0 < T) :
    ‖∫ y, g y * exp ((T : ℂ) * Complex.I * (y : ℂ)) ∂volume‖ ≤
      (∫ x, ‖deriv g x‖ ∂volume) / T := by
  have hw : -T / (2 * Real.pi) ≠ 0 := by
    exact div_ne_zero (neg_ne_zero.mpr hT.ne') (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  have hfourier := norm_fourier_le_integral_deriv_div g hg hdiff hg' hw
  have heq :
      (∫ y, g y * exp ((T : ℂ) * Complex.I * (y : ℂ)) ∂volume) =
        𝓕 g (-T / (2 * Real.pi)) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards with y
    rw [smul_eq_mul]
    rw [mul_comm (g y)]
    congr 1
    congr 1
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [heq]
  refine hfourier.trans_eq ?_
  congr 1
  have hden : (2 * Real.pi) * |-T / (2 * Real.pi)| = T := by
    have htwopi_pos : 0 < 2 * Real.pi := by positivity
    have hneg : -T / (2 * Real.pi) < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos hT) htwopi_pos
    rw [abs_of_neg hneg]
    field_simp [Real.pi_ne_zero]
  rw [hden]

/-- The `|T|` variant of the oscillatory-integral decay bound: for `T ≠ 0`,
`‖∫ g y · exp(T·i·y)‖ ≤ (∫ ‖deriv g x‖) / |T|`. -/
lemma norm_oscillatory_integral_le_integral_deriv_div_abs
    (g : ℝ → ℂ) (hg : Integrable g) (hdiff : Differentiable ℝ g)
    (hg' : Integrable (deriv g)) {T : ℝ} (hT : T ≠ 0) :
    ‖∫ y, g y * exp ((T : ℂ) * Complex.I * (y : ℂ)) ∂volume‖ ≤
      (∫ x, ‖deriv g x‖ ∂volume) / |T| := by
  have hw : -T / (2 * Real.pi) ≠ 0 := by
    exact div_ne_zero (neg_ne_zero.mpr hT) (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  have hfourier := norm_fourier_le_integral_deriv_div g hg hdiff hg' hw
  have heq :
      (∫ y, g y * exp ((T : ℂ) * Complex.I * (y : ℂ)) ∂volume) =
        𝓕 g (-T / (2 * Real.pi)) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards with y
    rw [smul_eq_mul]
    rw [mul_comm (g y)]
    congr 1
    congr 1
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [heq]
  refine hfourier.trans_eq ?_
  congr 1
  have hden : (2 * Real.pi) * |-T / (2 * Real.pi)| = |T| := by
    have htwopi_pos : 0 < 2 * Real.pi := by positivity
    rw [abs_div, abs_neg, abs_of_pos htwopi_pos]
    field_simp [Real.pi_ne_zero]
  rw [hden]

end PNTX_Fourier

-- Ported from PrimeNumberTheoremAnd: SmoothExistence.lean
section PNTX_Smooth

open MeasureTheory Set Real
open scoped ContDiff

lemma smooth_urysohn_support_Ioo {a b c d : ℝ} (h1 : a < b) (h3 : c < d) :
    ∃ Ψ : ℝ → ℝ, (ContDiff ℝ ∞ Ψ) ∧ (HasCompactSupport Ψ) ∧
    Set.indicator (Set.Icc b c) 1 ≤ Ψ ∧ Ψ ≤ Set.indicator (Set.Ioo a d) 1 ∧
    (Function.support Ψ = Set.Ioo a d) := by
  have := exists_contMDiff_zero_iff_one_iff_of_isClosed (n := ⊤)
    (modelWithCornersSelf ℝ ℝ) (s := Set.Iic a ∪ Set.Ici d) (t := Set.Icc b c)
    (IsClosed.union isClosed_Iic isClosed_Ici) isClosed_Icc
    (by
      simp_rw [Set.disjoint_union_left, Set.disjoint_iff, Set.subset_def,
        Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, Set.mem_empty_iff_false,
        and_imp, imp_false, not_le, Set.mem_Ici]
      constructor <;> intros <;> linarith)
  obtain ⟨Ψ, hΨSmooth, hΨrange, hΨ0, hΨ1⟩ := this
  simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici, Set.mem_Icc] at *
  use Ψ
  simp only [range_subset_iff, mem_Icc] at hΨrange
  refine ⟨ContMDiff.contDiff hΨSmooth, ?_, ?_, ?_, ?_⟩
  · apply HasCompactSupport.of_support_subset_isCompact (K := Set.Icc a d) isCompact_Icc
    simp only [Function.support_subset_iff, ne_eq, mem_Icc, ← hΨ0, not_or]
    bound
  · apply Set.indicator_le'
    · intro x hx
      rw [hΨ1 x |>.mp, Pi.one_apply]
      simpa using hx
    · exact fun x _ ↦ (hΨrange x).1
  · intro x
    apply Set.le_indicator_apply
    · exact fun _ ↦ (hΨrange x).2
    · intro hx
      rw [← hΨ0 x |>.mp]
      simpa [-not_and, mem_Ioo, not_and_or, not_lt] using hx
  · ext x
    simp only [Function.mem_support, ne_eq, mem_Ioo, ← hΨ0, not_or, not_le]



lemma SmoothExistence :
    ∃ (ν : ℝ → ℝ), (ContDiff ℝ ∞ ν) ∧ (∀ x, 0 ≤ ν x) ∧
    ν.support ⊆ Icc (1 / 2) 2 ∧ ∫ x in Ici 0, ν x / x = 1 := by
  suffices h : ∃ (ν : ℝ → ℝ), (ContDiff ℝ ∞ ν) ∧ (∀ x, 0 ≤ ν x) ∧
      ν.support ⊆ Set.Icc (1 / 2) 2 ∧ 0 < ∫ x in Set.Ici 0, ν x / x by
    obtain ⟨ν, hν, hνnonneg, hνsupp, hνpos⟩ := h
    let c := (∫ x in Ici 0, ν x / x)
    use fun y ↦ ν y / c
    refine ⟨hν.div_const c, fun y ↦ div_nonneg (hνnonneg y) (le_of_lt hνpos), ?_, ?_⟩
    · rw [Function.support_div, Function.support_const (ne_of_lt hνpos).symm, inter_univ]
      convert hνsupp
    · simp only [div_right_comm _ c _, integral_div c, div_self <| ne_of_gt hνpos, c]
  have := smooth_urysohn_support_Ioo (a := 1 / 2) (b := 1) (c := 3 / 2) (d := 2)
    (by linarith) (by linarith)
  obtain ⟨ν, hνContDiff, _, hν0, hν1, hνSupport⟩ := this
  use ν, hνContDiff
  unfold indicator at hν0 hν1
  simp only [mem_Icc, Pi.one_apply, Pi.le_def, mem_Ioo] at hν0 hν1
  simp only [hνSupport, subset_def, mem_Ioo, mem_Icc, and_imp]
  split_ands
  · exact fun x ↦ le_trans (by simp [apply_ite]) (hν0 x)
  · exact fun y hy hy' ↦ ⟨by linarith, by linarith⟩
  · rw [integral_pos_iff_support_of_nonneg]
    · simp only [Function.support_div, measurableSet_Ici, Measure.restrict_apply',
        hνSupport, Function.support_id']
      have : (Ioo (1 / 2 : ℝ) 2 ∩ {0}ᶜ ∩ Ici 0) = Ioo (1 / 2) 2 := by
        ext x
        simp only [one_div, mem_inter_iff, mem_Ioo, mem_compl_iff, mem_singleton_iff, mem_Ici]
        bound
      simp only [this, volume_Ioo, ENNReal.ofReal_pos, sub_pos, gt_iff_lt]
      linarith
    · simp_rw [Pi.le_def, Pi.zero_apply]
      intro y
      by_cases h : y ∈ Function.support ν
      · apply div_nonneg <| le_trans (by simp [apply_ite]) (hν0 y)
        rw [hνSupport, mem_Ioo] at h
        linarith [h.left]
      · simp only [Function.mem_support, ne_eq, not_not] at h
        simp [h]
    · have : (fun x ↦ ν x / x).support ⊆ Icc (1 / 2) 2 := by
        rw [Function.support_div, hνSupport]
        exact (inter_subset_left).trans Ioo_subset_Icc_self
      apply (integrableOn_iff_integrable_of_support_subset this).mp
      apply ContinuousOn.integrableOn_compact isCompact_Icc
      apply hνContDiff.continuous.continuousOn.div continuousOn_id ?_
      simp only [mem_Icc, ne_eq, and_imp, id_eq]
      intros; linarith

end PNTX_Smooth

-- Ported from PrimeNumberTheoremAnd: Wiener.lean (up to and including theorem WeakPNT)
section PNTX_Wiener

-- note: the opening of ArithmeticFunction introduces a notation σ that seems
-- impossible to hide, and hence parameters that are traditionally called σ will
-- have to be called σ' instead in this file.

open Real BigOperators ArithmeticFunction MeasureTheory Filter Set FourierTransform LSeries
  Asymptotics SchwartzMap
open Complex hiding log
open scoped Topology
open scoped ContDiff
open scoped ComplexConjugate

variable {n : ℕ} {A a b c d u x y t σ' : ℝ} {ψ Ψ : ℝ → ℂ} {F G : ℂ → ℂ} {f : ℕ → ℂ} {𝕜 : Type}
  [RCLike 𝕜]



noncomputable
def nterm (f : ℕ → ℂ) (σ' : ℝ) (n : ℕ) : ℝ := if n = 0 then 0 else ‖f n‖ / n ^ σ'

lemma nterm_eq_norm_term {f : ℕ → ℂ} : nterm f σ' n = ‖term f σ' n‖ := by
  by_cases h : n = 0 <;> simp [nterm, term, h]

theorem norm_term_eq_nterm_re (s : ℂ) :
    ‖term f s n‖ = nterm f (s.re) n := by
  simp only [nterm, term, apply_ite (‖·‖), norm_zero, norm_div]
  apply ite_congr rfl (fun _ ↦ rfl)
  intro h
  congr
  refine norm_natCast_cpow_of_pos (by omega) s

lemma hf_coe1 (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hσ : 1 < σ') :
    ∑' i, (‖term f σ' i‖₊ : ENNReal) ≠ ⊤ := by
  simp_rw [ENNReal.tsum_coe_ne_top_iff_summable_coe, ← norm_toNNReal]
  norm_cast
  apply Summable.toNNReal
  convert hf σ' hσ with i
  simp [nterm_eq_norm_term]

instance instMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype _
instance instBorelSpace : BorelSpace Circle :=
  inferInstanceAs <| BorelSpace <| Subtype (· ∈ Metric.sphere (0 : ℂ) 1)


lemma first_fourier_aux1 (hψ : AEMeasurable ψ) {x : ℝ} (n : ℕ) : AEMeasurable fun (u : ℝ) ↦
    (‖fourierChar (-(u * ((1 : ℝ) / ((2 : ℝ) * π) * (n / x).log))) • ψ u‖ₑ : ENNReal) := by
  fun_prop

lemma first_fourier_aux2a :
    (2 : ℂ) * π * -(y * (1 / (2 * π) * Real.log ((n) / x))) = -(y * ((n) / x).log) := by
  calc
    _ = -(y * (((2 : ℂ) * π) / (2 * π) * Real.log ((n) / x))) := by ring
    _ = _ := by rw [div_self (by norm_num), one_mul]

lemma first_fourier_aux2 (hx : 0 < x) (n : ℕ) :
    term f σ' n * 𝐞 (-(y * (1 / (2 * π) * Real.log (n / x)))) • ψ y =
    term f (σ' + y * I) n • (ψ y * x ^ (y * I)) := by
  by_cases hn : n = 0
  · simp [term, hn]
  simp only [term, hn, ↓reduceIte]
  calc
    _ = (f n * (cexp ((2 * π * -(y * (1 / (2 * π) * Real.log (n / x)))) * I) /
        ↑((n : ℝ) ^ σ'))) • ψ y := by
      rw [Circle.smul_def, fourierChar_apply, ofReal_cpow (by norm_num)]
      simp only [one_div, mul_inv_rev, mul_neg, ofReal_neg, ofReal_mul, ofReal_ofNat, ofReal_inv,
        neg_mul, smul_eq_mul, ofReal_natCast]
      ring
    _ = (f n * (x ^ (y * I) / n ^ (σ' + y * I))) • ψ y := by
      congr 2
      have l1 : 0 < (n : ℝ) := by simpa using Nat.pos_iff_ne_zero.mpr hn
      have l2 : (x : ℂ) ≠ 0 := by simp [hx.ne.symm]
      have l3 : (n : ℂ) ≠ 0 := by simp [hn]
      rw [Real.rpow_def_of_pos l1, Complex.cpow_def_of_ne_zero l2, Complex.cpow_def_of_ne_zero l3]
      push_cast
      simp_rw [← Complex.exp_sub]
      congr 1
      rw [first_fourier_aux2a, Real.log_div l1.ne.symm hx.ne.symm]
      push_cast
      rw [Complex.ofReal_log hx.le]
      ring
    _ = _ := by simp ; group

lemma first_fourier (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hsupp : Integrable ψ) (hx : 0 < x) (hσ : 1 < σ') :
    ∑' n : ℕ, term f σ' n * (𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x))) =
    ∫ t : ℝ, LSeries f (σ' + t * I) * ψ t * x ^ (t * I) := by

  calc
    _ = ∑' n, term f σ' n * ∫ (v : ℝ), 𝐞 (-(v * ((1 : ℝ) /
        ((2 : ℝ) * π) * Real.log (n / x)))) • ψ v := by
      simp only [Real.fourier_eq]
      simp only [one_div, mul_inv_rev, RCLike.inner_apply', conj_trivial]
    _ = ∑' n, ∫ (v : ℝ), term f σ' n * 𝐞 (-(v * ((1 : ℝ) /
        ((2 : ℝ) * π) * Real.log (n / x)))) • ψ v := by
      simp [integral_const_mul]
    _ = ∫ (v : ℝ), ∑' n, term f σ' n * 𝐞 (-(v * ((1 : ℝ) /
        ((2 : ℝ) * π) * Real.log (n / x)))) • ψ v := by
      refine (integral_tsum ?_ ?_).symm
      · refine fun _ ↦ AEMeasurable.aestronglyMeasurable ?_
        have := hsupp.aemeasurable
        fun_prop
      · simp only [enorm_mul]
        simp_rw [lintegral_const_mul'' _ (first_fourier_aux1 hsupp.aemeasurable _)]
        calc
          _ = (∑' (i : ℕ), ‖term f σ' i‖ₑ) * ∫⁻ (a : ℝ), ‖ψ a‖ₑ ∂volume := by
            simp [ENNReal.tsum_mul_right, enorm_eq_nnnorm]
          _ ≠ ⊤ := ENNReal.mul_ne_top (hf_coe1 hf hσ)
            (ne_top_of_lt hsupp.2)
    _ = _ := by
      congr 1; ext y
      simp_rw [mul_assoc (LSeries _ _), ← smul_eq_mul (a := (LSeries _ _)), LSeries]
      rw [← Summable.tsum_smul_const]
      · simp_rw [first_fourier_aux2 hx]
      · apply Summable.of_norm
        convert hf σ' hσ with n
        rw [norm_term_eq_nterm_re]
        simp



lemma continuous_multiplicative_ofAdd : Continuous (⇑Multiplicative.ofAdd : ℝ → ℝ) := ⟨fun _ ↦ id⟩


lemma second_fourier_integrable_aux1a (hσ : 1 < σ') :
    IntegrableOn (fun (x : ℝ) ↦ cexp (-((x : ℂ) * ((σ' : ℂ) - 1)))) (Ici (-Real.log x)) := by
  norm_cast
  suffices IntegrableOn (fun (x : ℝ) ↦ (rexp (-(x * (σ' - 1))))) (Ici (-x.log)) _ from this.ofReal
  simp_rw [fun (a x : ℝ) ↦ (by ring : -(x * a) = -a * x)]
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  apply exp_neg_integrableOn_Ioi
  linarith

lemma second_fourier_integrable_aux1 (hcont : Measurable ψ) (hsupp : Integrable ψ) (hσ : 1 < σ') :
    let ν : Measure (ℝ × ℝ) := (volume.restrict (Ici (-Real.log x))).prod volume
    Integrable (Function.uncurry fun (u : ℝ) (a : ℝ) ↦ ((rexp (-u * (σ' - 1))) : ℂ) •
    (𝐞 (Multiplicative.ofAdd (-(a * (u / (2 * π))))) : ℂ) • ψ a) ν := by
  intro ν
  constructor
  · apply Measurable.aestronglyMeasurable
    -- `Multiplicative.ofAdd x` is definitionally `x`; unfold it by `change` since `fun_prop`
    -- does not see through it.
    change Measurable (Function.uncurry fun (u : ℝ) (a : ℝ) ↦ ((rexp (-u * (σ' - 1))) : ℂ) •
      (𝐞 (-(a * (u / (2 * π)))) : ℂ) • ψ a)
    simp only [neg_mul, ofReal_exp, ofReal_neg, ofReal_mul, ofReal_sub, ofReal_one, smul_eq_mul]
    fun_prop
  · let f1 : ℝ → ENNReal := fun a1 ↦ ‖cexp (-(↑a1 * (↑σ' - 1)))‖ₑ
    let f2 : ℝ → ENNReal := fun a2 ↦ ‖ψ a2‖ₑ
    suffices ∫⁻ (a : ℝ × ℝ), f1 a.1 * f2 a.2 ∂ν < ⊤ by
      simpa [hasFiniteIntegral_iff_enorm, enorm_eq_nnnorm, Function.uncurry]
    refine (lintegral_prod_mul ?_ ?_).trans_lt ?_ <;> try fun_prop
    exact ENNReal.mul_lt_top (second_fourier_integrable_aux1a hσ).2 hsupp.2

lemma second_fourier_integrable_aux2 (hσ : 1 < σ') :
    IntegrableOn (fun (u : ℝ) ↦ cexp ((1 - ↑σ' - ↑t * I) * ↑u)) (Ioi (-Real.log x)) := by
  refine (integrable_norm_iff (Measurable.aestronglyMeasurable <| by fun_prop)).mp ?_
  suffices IntegrableOn (fun a ↦ rexp (-(σ' - 1) * a)) (Ioi (-x.log)) _ by simpa [Complex.norm_exp]
  apply exp_neg_integrableOn_Ioi
  linarith

lemma second_fourier_aux (hx : 0 < x) :
    -(cexp (-((1 - ↑σ' - ↑t * I) * ↑(Real.log x))) / (1 - ↑σ' - ↑t * I)) =
    ↑(x ^ (σ' - 1)) * (↑σ' + ↑t * I - 1)⁻¹ * ↑x ^ (↑t * I) := by
  calc
    _ = cexp (↑(Real.log x) * ((↑σ' - 1) + ↑t * I)) * (↑σ' + ↑t * I - 1)⁻¹ := by
      rw [← div_neg]; ring_nf
    _ = (x ^ ((↑σ' - 1) + ↑t * I)) * (↑σ' + ↑t * I - 1)⁻¹ := by
      rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr (ne_of_gt hx)), Complex.ofReal_log hx.le]
    _ = (x ^ ((σ' : ℂ) - 1)) * (x ^ (↑t * I)) * (↑σ' + ↑t * I - 1)⁻¹ := by
      rw [Complex.cpow_add _ _ (ofReal_ne_zero.mpr (ne_of_gt hx))]
    _ = _ := by rw [ofReal_cpow hx.le]; push_cast; ring

lemma second_fourier (hcont : Measurable ψ) (hsupp : Integrable ψ)
    {x σ' : ℝ} (hx : 0 < x) (hσ : 1 < σ') :
    ∫ u in Ici (-log x), Real.exp (-u * (σ' - 1)) * 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)) =
    (x^(σ' - 1) : ℝ) * ∫ t, (1 / (σ' + t * I - 1)) * ψ t * x^(t * I) ∂ volume := by

  conv in ↑(rexp _) * _ => { rw [Real.fourier_real_eq, ← smul_eq_mul, ← integral_smul] }
  rw [MeasureTheory.integral_integral_swap]
  swap
  · exact second_fourier_integrable_aux1 hcont hsupp hσ
  rw [← integral_const_mul]
  congr 1; ext t
  simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
  rw [fun (a b d : ℂ) ↦ show a * (b * (ψ t) * d) = (a * b * d) * ψ t by ring]
  simp_rw [← mul_assoc]
  rw [integral_mul_const]
  congr 1
  push_cast
  simp_rw [← Complex.exp_add]
  have (u : ℝ) :
      -↑u * (↑σ' - 1) + 2 * ↑π * -(↑t * (↑u / (2 * ↑π))) * I = (1 - σ' - t * I) * u := calc
    _ = -↑u * (↑σ' - 1) + (2 * ↑π) / (2 * ↑π) * -(↑t * ↑u) * I := by ring
    _ = -↑u * (↑σ' - 1) + 1 * -(↑t * ↑u) * I := by rw [div_self (by norm_num)]
    _ = _ := by ring
  simp_rw [this]
  let c : ℂ := (1 - ↑σ' - ↑t * I)
  have : c ≠ 0 := by simp [Complex.ext_iff, c, sub_ne_zero.mpr hσ.ne]
  let f' (u : ℝ) := cexp (c * u)
  let f := fun (u : ℝ) ↦ (f' u) / c
  have hderiv : ∀ u ∈ Ici (-Real.log x), HasDerivAt f (f' u) u := by
    intro u _
    rw [show f' u = cexp (c * u) * (c * 1) / c by simp only [f']; field_simp]
    exact (hasDerivAt_id' u).ofReal_comp.const_mul c |>.cexp.div_const c
  have hf : Tendsto f atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    suffices Tendsto (fun (x : ℝ) ↦ ‖cexp (c * ↑x)‖ / ‖c‖) atTop (𝓝 (0 / ‖c‖)) by
      simpa [f, f'] using this
    apply Filter.Tendsto.div_const
    suffices Tendsto (· * (1 - σ')) atTop atBot by simpa [Complex.norm_exp, mul_comm (1 - σ'), c]
    exact Tendsto.atTop_mul_const_of_neg (by linarith) fun ⦃s⦄ h ↦ h
  rw [integral_Ici_eq_integral_Ioi,
    integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (second_fourier_integrable_aux2 hσ) hf]
  simpa [f, f'] using second_fourier_aux hx



lemma one_add_sq_pos (u : ℝ) : 0 < 1 + u ^ 2 := zero_lt_one.trans_le (by simpa using sq_nonneg u)

theorem prelim_decay (ψ : ℝ → ℂ) (u : ℝ) : ‖𝓕 (ψ : ℝ → ℂ) u‖ ≤ ∫ t, ‖ψ t‖ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm ..

lemma decay_bounds_key (f : W21) (u : ℝ) : ‖𝓕 (f : ℝ → ℂ) u‖ ≤ ‖f‖ * (1 + u ^ 2)⁻¹ := by
  have l1 : 0 < 1 + u ^ 2 := one_add_sq_pos _
  have l2 : 1 + u ^ 2 = ‖(1 : ℂ) + u ^ 2‖ := by
    norm_cast ; simp only [Real.norm_eq_abs, abs_eq_self.2 l1.le]
  have l3 : ‖1 / ((4 : ℂ) * ↑π ^ 2)‖ ≤ (4 * π ^ 2)⁻¹ := by simp
  have key := fourierIntegral_self_add_deriv_deriv f u
  simp only [Function.iterate_succ _ 1, Function.iterate_one, Function.comp_apply] at key
  rw [F_sub f.hf (f.hf''.const_mul (1 / (4 * ↑π ^ 2)))] at key
  rw [← div_eq_mul_inv, le_div_iff₀ l1, mul_comm, l2, ← norm_mul, key, sub_eq_add_neg]
  apply norm_add_le _ _ |>.trans
  change _ ≤ W21.norm _
  rw [norm_neg, F_mul, norm_mul, W21.norm]
  gcongr <;> apply VectorFourier.norm_fourierIntegral_le_integral_norm

lemma decay_bounds_aux {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume)
    (h : ∀ t, ‖f t‖ ≤ A * (1 + t ^ 2)⁻¹) :
    ∫ t, ‖f t‖ ≤ π * A := by
  have l1 : Integrable (fun x ↦ A * (1 + x ^ 2)⁻¹) := integrable_inv_one_add_sq.const_mul A
  simp_rw [← integral_univ_inv_one_add_sq, mul_comm, ← integral_const_mul]
  exact integral_mono (l1.mono' hf (Eventually.of_forall h)).norm l1 h

theorem decay_bounds_W21 (f : W21) (hA : ∀ t, ‖f t‖ ≤ A / (1 + t ^ 2))
    (hA' : ∀ t, ‖deriv (deriv f) t‖ ≤ A / (1 + t ^ 2)) (u) :
    ‖𝓕 (f : ℝ → ℂ) u‖ ≤ (π + 1 / (4 * π)) * A / (1 + u ^ 2) := by
  have l0 : 1 * (4 * π)⁻¹ * A = (4 * π ^ 2)⁻¹ * (π * A) := by field_simp
  have l1 : ∫ (v : ℝ), ‖f v‖ ≤ π * A := by
    apply decay_bounds_aux f.continuous.aestronglyMeasurable
    simp_rw [← div_eq_mul_inv] ; exact hA
  have l2 : ∫ (v : ℝ), ‖deriv (deriv f) v‖ ≤ π * A := by
    apply decay_bounds_aux f.deriv.deriv.continuous.aestronglyMeasurable
    simp_rw [← div_eq_mul_inv] ; exact hA'
  apply decay_bounds_key f u |>.trans
  change W21.norm _ * _ ≤ _
  simp_rw [W21.norm, div_eq_mul_inv, add_mul, l0] ; gcongr

lemma decay_bounds (ψ : CS 2 ℂ) (hA : ∀ t, ‖ψ t‖ ≤ A / (1 + t ^ 2))
    (hA' : ∀ t, ‖deriv^[2] ψ t‖ ≤ A / (1 + t ^ 2)) :
    ‖𝓕 (ψ : ℝ → ℂ) u‖ ≤ (π + 1 / (4 * π)) * A / (1 + u ^ 2) := by
  exact decay_bounds_W21 ψ hA hA' u

lemma decay_bounds_cor_aux (ψ : CS 2 ℂ) : ∃ C : ℝ, ∀ u, ‖ψ u‖ ≤ C / (1 + u ^ 2) := by
  have l1 : HasCompactSupport (fun u : ℝ => ((1 + u ^ 2) : ℝ) * ψ u) := by exact ψ.h2.mul_left
  have := ψ.h1.continuous
  obtain ⟨C, hC⟩ := l1.exists_bound_of_continuous (by fun_prop)
  refine ⟨C, fun u => ?_⟩
  specialize hC u
  simp only [norm_mul, Complex.norm_real, norm_of_nonneg (one_add_sq_pos u).le] at hC
  rwa [le_div_iff₀' (one_add_sq_pos _)]

lemma decay_bounds_cor (ψ : W21) :
    ∃ C : ℝ, ∀ u, ‖𝓕 (ψ : ℝ → ℂ) u‖ ≤ C / (1 + u ^ 2) := by
  simpa only [div_eq_mul_inv] using ⟨_, decay_bounds_key ψ⟩

lemma continuous_FourierIntegral (ψ : W21) : Continuous (𝓕 (ψ : ℝ → ℂ)) :=
  VectorFourier.fourierIntegral_continuous continuous_fourierChar
    (by simp only [innerₗ_apply_apply, RCLike.inner_apply', conj_trivial, continuous_mul])
    ψ.hf

lemma W21.integrable_fourier (ψ : W21) (hc : c ≠ 0) :
    Integrable fun u ↦ 𝓕 (ψ : ℝ → ℂ) (u / c) := by
  have l1 (C) : Integrable (fun u ↦ C / (1 + (u / c) ^ 2)) volume := by
    simpa using! (integrable_inv_one_add_sq.comp_div hc).const_mul C
  have l2 : AEStronglyMeasurable (fun u ↦ 𝓕 (ψ : ℝ → ℂ) (u / c)) volume := by
    apply Continuous.aestronglyMeasurable ; have := continuous_FourierIntegral ψ ; fun_prop
  obtain ⟨C, h⟩ := decay_bounds_cor ψ
  apply @Integrable.mono' ℝ ℂ _ volume _ _ (fun u => C / (1 + (u / c) ^ 2)) (l1 C) l2 ?_
  apply Eventually.of_forall (fun x => h _)





lemma continuous_LSeries_aux (hf : Summable (nterm f σ')) :
    Continuous fun x : ℝ => LSeries f (σ' + x * I) := by

  have l1 i : Continuous fun x : ℝ ↦ term f (σ' + x * I) i := by
    by_cases h : i = 0
    · simpa [h] using continuous_const
    · simpa [h] using! continuous_const.div (continuous_const.cpow (by fun_prop) (by simp [h]))
        (fun x => by simp [h])
  have l2 n (x : ℝ) : ‖term f (σ' + x * I) n‖ = nterm f σ' n := by
    by_cases h : n = 0
    · simp [h, nterm]
    · simp [h, nterm, cpow_add _ _ (Nat.cast_ne_zero.mpr h),
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero h)]
  exact continuous_tsum l1 hf (fun n x => le_of_eq (l2 n x))

-- Here compact support is used but perhaps it is not necessary
lemma limiting_fourier_aux (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (ψ : CS 2 ℂ) (hx : 1 ≤ x) (σ' : ℝ)
    (hσ' : 1 < σ') :
    ∑' n, term f σ' n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
    A * (x ^ (1 - σ') : ℝ) * ∫ u in Ici (- log x), rexp (-u * (σ' - 1)) * 𝓕 (ψ : ℝ → ℂ)
      (u / (2 * π)) = ∫ t : ℝ, G (σ' + t * I) * ψ t * x ^ (t * I) := by
  have hint : Integrable ψ := ψ.h1.continuous.integrable_of_hasCompactSupport ψ.h2
  have l3 : 0 < x := zero_lt_one.trans_le hx
  have l1 (σ') (hσ' : 1 < σ') := first_fourier hf hint l3 hσ'
  have l2 (σ') (hσ' : 1 < σ') := second_fourier ψ.h1.continuous.measurable hint l3 hσ'
  have l8 : Continuous fun t : ℝ ↦ (x : ℂ) ^ (t * I) :=
    continuous_const.cpow (continuous_ofReal.mul continuous_const) (by simp [l3])
  have l6 : Continuous fun t : ℝ ↦ LSeries f (↑σ' + ↑t * I) * ψ t * ↑x ^ (↑t * I) := by
    apply ((continuous_LSeries_aux (hf _ hσ')).mul ψ.h1.continuous).mul l8
  have l4 : Integrable fun t : ℝ ↦ LSeries f (↑σ' + ↑t * I) * ψ t * ↑x ^ (↑t * I) := by
    exact l6.integrable_of_hasCompactSupport ψ.h2.mul_left.mul_right
  have e2 (u : ℝ) : σ' + u * I - 1 ≠ 0 := by
    intro h ; have := congr_arg Complex.re h ; simp at this ; linarith
  have l7 : Continuous fun a ↦ A * ↑(x ^ (1 - σ')) * (↑(x ^ (σ' - 1)) *
      (1 / (σ' + a * I - 1) * ψ a * x ^ (a * I))) := by
    simp only [one_div, ← mul_assoc]
    refine ((continuous_const.mul <| Continuous.inv₀ ?_ e2).mul ψ.h1.continuous).mul l8
    fun_prop
  have l5 : Integrable fun a ↦ A * ↑(x ^ (1 - σ')) * (↑(x ^ (σ' - 1)) *
      (1 / (σ' + a * I - 1) * ψ a * x ^ (a * I))) := by
    apply l7.integrable_of_hasCompactSupport
    exact ψ.h2.mul_left.mul_right.mul_left.mul_left

  simp_rw [l1 σ' hσ', l2 σ' hσ', ← integral_const_mul, ← integral_sub l4 l5]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro u
  have e1 : 1 < ((σ' : ℂ) + (u : ℂ) * I).re := by simp [hσ']
  simp_rw [hG' e1, sub_mul, ← mul_assoc]
  simp only [one_div, sub_right_inj, mul_eq_mul_right_iff, cpow_eq_zero_iff, ofReal_eq_zero, ne_eq,
    mul_eq_zero, I_ne_zero, or_false]
  left ; left
  field_simp [e2]
  norm_cast
  simp [mul_assoc, ← rpow_add l3]

section nabla

variable {α E : Type*} [OfNat α 1] [Add α] [Sub α] {u : α → ℂ}

def cumsum [AddCommMonoid E] (u : ℕ → E) (n : ℕ) : E := ∑ i ∈ Finset.range n, u i

def nabla [Sub E] (u : α → E) (n : α) : E := u (n + 1) - u n

/- `nnabla` is the backward difference `u n - u (n+1)`; kept alongside `nabla`
   for summation-by-parts identities that prefer that orientation. -/
def nnabla [Sub E] (u : α → E) (n : α) : E := u n - u (n + 1)

def shift (u : α → E) (n : α) : E := u (n + 1)

@[simp] lemma cumsum_zero [AddCommMonoid E] {u : ℕ → E} : cumsum u 0 = 0 := by simp [cumsum]

lemma cumsum_succ [AddCommMonoid E] {u : ℕ → E} (n : ℕ) :
    cumsum u (n + 1) = cumsum u n + u n := by
  simp [cumsum, Finset.sum_range_succ]

@[simp] lemma nabla_cumsum [AddCommGroup E] {u : ℕ → E} : nabla (cumsum u) = u := by
  ext n ; simp [nabla, cumsum, Finset.range_add_one]

lemma neg_cumsum [AddCommGroup E] {u : ℕ → E} : -(cumsum u) = cumsum (-u) :=
  funext (fun n => by simp [cumsum])

lemma cumsum_nonneg {u : ℕ → ℝ} (hu : 0 ≤ u) : 0 ≤ cumsum u :=
  fun _ => Finset.sum_nonneg (fun i _ => hu i)

omit [Sub α] in
lemma neg_nabla [Ring E] {u : α → E} : -(nabla u) = nnabla u := by ext n ; simp [nabla, nnabla]

omit [Sub α] in
@[simp] lemma nabla_mul [Ring E] {u : α → E} {c : E} : nabla (fun n => c * u n) = c • nabla u := by
  ext n ; simp [nabla, mul_sub]

omit [Sub α] in
@[simp] lemma nnabla_mul [Ring E] {u : α → E} {c : E} :
    nnabla (fun n => c * u n) = c • nnabla u := by
  ext n ; simp [nnabla, mul_sub]

lemma nnabla_cast (u : ℝ → E) [Sub E] : nnabla u ∘ ((↑) : ℕ → ℝ) = nnabla (u ∘ (↑)) := by
  ext n ; simp [nnabla]

end nabla

lemma Finset.sum_shift_front {E : Type*} [Ring E] {u : ℕ → E} {n : ℕ} :
    cumsum u (n + 1) = u 0 + cumsum (shift u) n := by
  simp_rw [add_comm n, cumsum, sum_range_add, sum_range_one, add_comm 1] ; rfl

lemma Finset.sum_shift_front' {E : Type*} [Ring E] {u : ℕ → E} :
    shift (cumsum u) = (fun _ => u 0) + cumsum (shift u) := by
  ext n ; apply Finset.sum_shift_front

lemma Finset.sum_shift_back {E : Type*} [Ring E] {u : ℕ → E} {n : ℕ} :
    cumsum u (n + 1) = cumsum u n + u n := by
  simp [cumsum, Finset.range_add_one, add_comm]

lemma Finset.sum_shift_back' {E : Type*} [Ring E] {u : ℕ → E} :
    shift (cumsum u) = cumsum u + u := by
  ext n ; apply Finset.sum_shift_back

lemma summation_by_parts {E : Type*} [Ring E] {a A b : ℕ → E} (ha : a = nabla A) {n : ℕ} :
    cumsum (a * b) (n + 1) = A (n + 1) * b n - A 0 * b 0 -
    cumsum (shift A * fun i => (b (i + 1) - b i)) n := by
  have l1 : ∑ x ∈ Finset.range (n + 1), A (x + 1) * b x = ∑ x ∈ Finset.range n,
      A (x + 1) * b x + A (n + 1) * b n :=
    Finset.sum_shift_back
  have l2 : ∑ x ∈ Finset.range (n + 1), A x * b x = A 0 * b 0 + ∑ x ∈ Finset.range n,
      A (x + 1) * b (x + 1) :=
    Finset.sum_shift_front
  simp only [cumsum, ha, Pi.mul_apply, nabla, sub_mul, Finset.sum_sub_distrib, l1, l2, shift,
    mul_sub]
  abel

lemma summation_by_parts' {E : Type*} [Ring E] {a b : ℕ → E} {n : ℕ} :
    cumsum (a * b) (n + 1) = cumsum a (n + 1) * b n - cumsum (shift (cumsum a) * nabla b) n := by
  simpa using! summation_by_parts (a := a) (b := b) (A := cumsum a) (by simp)

lemma summation_by_parts'' {E : Type*} [Ring E] {a b : ℕ → E} :
    shift (cumsum (a * b)) = shift (cumsum a) * b - cumsum (shift (cumsum a) * nabla b) := by
  ext n ; apply summation_by_parts'

lemma summable_iff_bounded {u : ℕ → ℝ} (hu : 0 ≤ u) :
    Summable u ↔ BoundedAtFilter atTop (cumsum u) := by
  have l1 : (cumsum u =O[atTop] 1) ↔ _ := isBigO_one_nat_atTop_iff
  have l2 n : ‖cumsum u n‖ = cumsum u n := by simpa using cumsum_nonneg hu n
  simp only [BoundedAtFilter, l1, l2]
  constructor <;> intro ⟨C, h1⟩
  · exact ⟨C, fun n => sum_le_hasSum _ (fun i _ => hu i) h1⟩
  · exact summable_of_sum_range_le hu h1

lemma Filter.EventuallyEq.summable {u v : ℕ → ℝ} (h : u =ᶠ[atTop] v) (hu : Summable v) :
    Summable u :=
  summable_of_isBigO_nat hu h.isBigO

lemma summable_congr_ae {u v : ℕ → ℝ} (huv : u =ᶠ[atTop] v) : Summable u ↔ Summable v := by
  constructor <;> intro h <;> simp [huv.summable, huv.symm.summable, h]

lemma BoundedAtFilter.add_const {u : ℕ → ℝ} {c : ℝ} :
    BoundedAtFilter atTop (fun n => u n + c) ↔ BoundedAtFilter atTop u := by
  have : u = fun n => (u n + c) + (-c) := by ext n ; ring
  simp only [BoundedAtFilter]
  constructor <;> intro h
  on_goal 1 => rw [this]
  all_goals { exact h.add (const_boundedAtFilter _ _) }

lemma BoundedAtFilter.comp_add {u : ℕ → ℝ} {N : ℕ} :
    BoundedAtFilter atTop (fun n => u (n + N)) ↔ BoundedAtFilter atTop u := by
  simp only [BoundedAtFilter, isBigO_iff, norm_eq_abs, Pi.one_apply,
    eventually_atTop]
  constructor <;> intro ⟨C, n₀, h⟩ <;> use C
  · refine ⟨n₀ + N, fun n hn => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (m := N) (n := n) (by grind)
    exact h _ <| Nat.add_le_add_iff_right.mp hn
  · exact ⟨n₀, fun n hn => h _ (by grind)⟩

lemma summable_iff_bounded' {u : ℕ → ℝ} (hu : ∀ᶠ n in atTop, 0 ≤ u n) :
    Summable u ↔ BoundedAtFilter atTop (cumsum u) := by
  obtain ⟨N, hu⟩ := eventually_atTop.mp hu
  have e2 : cumsum (fun i ↦ u (i + N)) = fun n => cumsum u (n + N) - cumsum u N := by
    ext n ; simp_rw [cumsum, add_comm _ N, Finset.sum_range_add] ; ring
  rw [← summable_nat_add_iff N, summable_iff_bounded (fun n => hu _ <| Nat.le_add_left N n), e2]
  simp_rw [sub_eq_add_neg, BoundedAtFilter.add_const, BoundedAtFilter.comp_add]

lemma bounded_of_shift {u : ℕ → ℝ} (h : BoundedAtFilter atTop (shift u)) :
    BoundedAtFilter atTop u := by
  simp only [BoundedAtFilter, isBigO_iff, eventually_atTop] at h ⊢
  obtain ⟨C, N, hC⟩ := h
  refine ⟨C, N + 1, fun n hn => ?_⟩
  simp only [shift] at hC
  have r1 : n - 1 ≥ N := Nat.le_sub_one_of_lt hn
  have r2 : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  simpa [r2] using hC (n - 1) r1

lemma dirichlet_test' {a b : ℕ → ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hAb : BoundedAtFilter atTop (shift (cumsum a) * b)) (hbb : ∀ᶠ n in atTop, b (n + 1) ≤ b n)
    (h : Summable (shift (cumsum a) * nnabla b)) : Summable (a * b) := by
  have l1 : ∀ᶠ n in atTop, 0 ≤ (shift (cumsum a) * nnabla b) n := by
    filter_upwards [hbb] with n hb
    exact mul_nonneg (by simpa [shift] using! Finset.sum_nonneg' ha) (sub_nonneg.mpr hb)
  rw [summable_iff_bounded (mul_nonneg ha hb)]
  rw [summable_iff_bounded' l1] at h
  apply bounded_of_shift
  simpa only [summation_by_parts'', sub_eq_add_neg, neg_cumsum, ← mul_neg, neg_nabla]
    using hAb.add h

lemma exists_antitone_of_eventually {u : ℕ → ℝ} (hu : ∀ᶠ n in atTop, u (n + 1) ≤ u n) :
    ∃ v : ℕ → ℝ, range v ⊆ range u ∧ Antitone v ∧ v =ᶠ[atTop] u := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hu
  let v (n : ℕ) := u (if n < N then N else n)
  refine ⟨v, ?_, ?_, ?_⟩
  · exact fun x ⟨n, hn⟩ => ⟨if n < N then N else n, hn⟩
  · refine antitone_nat_of_succ_le (fun n => ?_)
    by_cases h : n < N
    · by_cases h' : n + 1 < N <;> simp [v, h, h']
      have : n + 1 = N := by linarith
      simp [this]
    · have : ¬(n + 1 < N) := by linarith
      simp only [this, ↓reduceIte, h, ge_iff_le, v] ; apply hN ; linarith
  · have : ∀ᶠ n in atTop, ¬(n < N) := by simpa using ⟨N, fun b hb => by linarith⟩
    filter_upwards [this] with n hn ; simp [v, hn]

lemma summable_inv_mul_log_sq : Summable (fun n : ℕ => (n * (Real.log n) ^ 2)⁻¹) := by
  let u (n : ℕ) := (n * (Real.log n) ^ 2)⁻¹
  have l7 : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log n :=
    tendsto_atTop.mp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop) 1
  have l8 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  have l9 : ∀ᶠ n in atTop, u (n + 1) ≤ u n := by
    filter_upwards [l7, l8] with n l2 l8; dsimp [u]; gcongr <;> simp
  obtain ⟨v, l1, l2, l3⟩ := exists_antitone_of_eventually l9
  rw [summable_congr_ae l3.symm]
  have l4 (n : ℕ) : 0 ≤ v n := by obtain ⟨k, hk⟩ := l1 ⟨n, rfl⟩ ; rw [← hk] ; positivity
  apply (summable_condensed_iff_of_nonneg l4 (fun _ _ _ a ↦ l2 a)).mp
  suffices this : ∀ᶠ k : ℕ in atTop, 2 ^ k * v (2 ^ k) = ((k : ℝ) ^ 2)⁻¹ * ((Real.log 2) ^ 2)⁻¹ by
    exact (summable_congr_ae this).mpr <| (Real.summable_nat_pow_inv.mpr one_lt_two).mul_right _
  have l5 : ∀ᶠ k in atTop, v (2 ^ k) = u (2 ^ k) :=
    l3.comp_tendsto <| tendsto_pow_atTop_atTop_of_one_lt Nat.le.refl
  filter_upwards [l5, l8] with k l5 l8
  simp only [l5, mul_inv_rev, Nat.cast_pow, Nat.cast_ofNat, log_pow, u]
  field_simp

lemma tendsto_mul_add_atTop {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Tendsto (fun x => a * x + b) atTop atTop :=
  tendsto_atTop_add_const_right _ b (tendsto_id.const_mul_atTop ha)

lemma isLittleO_const_of_tendsto_atTop {α : Type*} [Preorder α] (a : ℝ) {f : α → ℝ}
    (hf : Tendsto f atTop atTop) : (fun _ => a) =o[atTop] f := by
  simp [tendsto_norm_atTop_atTop.comp hf]

lemma isBigO_pow_pow_of_le {m n : ℕ} (h : m ≤ n) :
    (fun x : ℝ => x ^ m) =O[atTop] (fun x : ℝ => x ^ n) := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop 1] with x l1
  simpa [abs_eq_self.mpr (zero_le_one.trans l1)] using pow_le_pow_right₀ l1 h

lemma isLittleO_mul_add_sq (a b : ℝ) : (fun x => a * x + b) =o[atTop] (fun x => x ^ 2) := by
  apply IsLittleO.add
  · apply IsLittleO.const_mul_left ; simpa using isLittleO_pow_pow_atTop_of_lt (𝕜 := ℝ) one_lt_two
  · apply isLittleO_const_of_tendsto_atTop _ <| tendsto_pow_atTop (by linarith)

lemma log_mul_add_isBigO_log {a : ℝ} (ha : 0 < a) (b : ℝ) :
    (fun x => Real.log (a * x + b)) =O[atTop] Real.log := by
  apply IsBigO.of_bound (2 : ℕ)
  have l2 : ∀ᶠ x : ℝ in atTop, 0 ≤ log x := tendsto_atTop.mp tendsto_log_atTop 0
  have l3 : ∀ᶠ x : ℝ in atTop, 0 ≤ log (a * x + b) :=
    tendsto_atTop.mp (tendsto_log_atTop.comp (tendsto_mul_add_atTop ha b)) 0
  have l5 : ∀ᶠ x : ℝ in atTop, 1 ≤ a * x + b := tendsto_atTop.mp (tendsto_mul_add_atTop ha b) 1
  have l1 : ∀ᶠ x : ℝ in atTop, a * x + b ≤ x ^ 2 := by
    filter_upwards [(isLittleO_mul_add_sq a b).eventuallyLE, l5] with x r2 l5
    simpa [abs_eq_self.mpr (zero_le_one.trans l5)] using r2
  filter_upwards [l1, l2, l3, l5] with x l1 l2 l3 l5
  simpa [abs_eq_self.mpr l2, abs_eq_self.mpr l3, Real.log_pow] using
    Real.log_le_log (by linarith) l1

lemma isBigO_log_mul_add {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Real.log =O[atTop] (fun x => Real.log (a * x + b)) := by
  convert! (log_mul_add_isBigO_log (b := -b / a) (inv_pos.mpr ha)).comp_tendsto
    (tendsto_mul_add_atTop (b := b) ha) using 1
  ext x
  simp only [Function.comp_apply]
  congr
  field_simp
  simp

lemma log_isbigo_log_div {d : ℝ} (hb : 0 < d) :
    (fun n ↦ Real.log n) =O[atTop] (fun n ↦ Real.log (n / d)) := by
  convert isBigO_log_mul_add (inv_pos.mpr hb) 0 using 1; simp only [add_zero]; field_simp

lemma Asymptotics.IsBigO.add_isLittleO_right {f g : ℝ → ℝ} (h : g =o[atTop] f) :
    f =O[atTop] (f + g) := by
  rw [isLittleO_iff] at h ; specialize h (c := 2⁻¹) (by norm_num)
  rw [isBigO_iff'']
  refine ⟨2⁻¹, by norm_num, ?_⟩
  filter_upwards [h] with x h
  simp only [norm_eq_abs, Pi.add_apply] at h ⊢
  calc _ = |f x| - 2⁻¹ * |f x| := by ring
       _ ≤ |f x| - |g x| := by linarith
       _ ≤ |(|f x| - |g x|)| := le_abs_self _
       _ ≤ _ := by rw [← sub_neg_eq_add, ← abs_neg (g x)] ; exact abs_abs_sub_abs_le (f x) (-g x)

lemma Asymptotics.IsBigO.sq {α : Type*} [Preorder α] {f g : α → ℝ} (h : f =O[atTop] g) :
    (fun n ↦ f n ^ 2) =O[atTop] (fun n => g n ^ 2) := by
  simpa [pow_two] using h.mul h

lemma log_sq_isbigo_mul {a b : ℝ} (hb : 0 < b) :
    (fun x ↦ Real.log x ^ 2) =O[atTop] (fun x ↦ a + Real.log (x / b) ^ 2) := by
  apply (log_isbigo_log_div hb).sq.trans ; simp_rw [add_comm a]
  refine IsBigO.add_isLittleO_right <| isLittleO_const_of_tendsto_atTop _ ?_
  exact (tendsto_pow_atTop two_ne_zero).comp <|
    tendsto_log_atTop.comp <| tendsto_id.atTop_div_const hb

theorem log_add_div_isBigO_log (a : ℝ) {b : ℝ} (hb : 0 < b) :
    (fun x ↦ Real.log ((x + a) / b)) =O[atTop] fun x ↦ Real.log x := by
  convert log_mul_add_isBigO_log (inv_pos.mpr hb) (a / b) using 3 ; ring

lemma log_add_one_sub_log_le {x : ℝ} (hx : 0 < x) : nabla Real.log x ≤ x⁻¹ := by
  have l1 : ContinuousOn Real.log (Icc x (x + 1)) := by
    apply continuousOn_log.mono ; intro t ⟨h1, _⟩ ; simp ; linarith
  have l2 t (ht : t ∈ Ioo x (x + 1)) : HasDerivAt Real.log t⁻¹ t :=
    Real.hasDerivAt_log (by linarith [ht.1])
  obtain ⟨t, ⟨ht1, _⟩, htx⟩ := exists_hasDerivAt_eq_slope Real.log (·⁻¹) (by linarith) l1 l2
  simp only [add_sub_cancel_left, div_one] at htx
  rw [nabla, ← htx, inv_le_inv₀ (by linarith) hx]
  exact ht1.le

lemma nabla_log_main : nabla Real.log =O[atTop] fun x ↦ 1 / x := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_gt_atTop 0] with x l1
  have l2 : log x ≤ log (x + 1) := log_le_log l1 (by linarith)
  simpa [nabla, abs_eq_self.mpr l1.le, abs_eq_self.mpr (sub_nonneg.mpr l2)] using
    log_add_one_sub_log_le l1

lemma nabla_log {b : ℝ} (hb : 0 < b) :
    nabla (fun x => Real.log (x / b)) =O[atTop] (fun x => 1 / x) := by
  refine EventuallyEq.trans_isBigO ?_ nabla_log_main
  filter_upwards [eventually_gt_atTop 0] with x l2
  rw [nabla, log_div (by linarith) (by linarith), log_div l2.ne.symm (by linarith), nabla] ; ring

lemma nnabla_mul_log_sq (a : ℝ) {b : ℝ} (hb : 0 < b) :
    nabla (fun x => x * (a + Real.log (x / b) ^ 2)) =O[atTop] (fun x => Real.log x ^ 2) := by

  have l1 : nabla (fun n => n * (a + Real.log (n / b) ^ 2)) = fun n =>
      a + Real.log ((n + 1) / b) ^ 2 +
        (n * (Real.log ((n + 1) / b) ^ 2 - Real.log (n / b) ^ 2)) := by
    ext n ; simp [nabla] ; ring
  have l2 := (isLittleO_const_of_tendsto_atTop a
    ((tendsto_pow_atTop two_ne_zero).comp tendsto_log_atTop)).isBigO
  have l3 := (log_add_div_isBigO_log 1 hb).sq
  have l4 : (fun x => Real.log ((x + 1) / b) + Real.log (x / b)) =O[atTop] Real.log := by
    simpa using (log_add_div_isBigO_log _ hb).add (log_add_div_isBigO_log 0 hb)
  have e2 : (fun x : ℝ => x * (Real.log x * (1 / x))) =ᶠ[atTop] Real.log := by
    filter_upwards [eventually_ge_atTop 1] with x hx using by field_simp
  have l5 : (fun n ↦ n * (Real.log n * (1 / n))) =O[atTop] (fun n ↦ (Real.log n) ^ 2) :=
    e2.trans_isBigO
      (by simpa using! (isLittleO_mul_add_sq 1 0).isBigO.comp_tendsto Real.tendsto_log_atTop)

  simp_rw [l1, _root_.sq_sub_sq]
  exact ((l2.add l3).add (isBigO_refl (·) atTop |>.mul (l4.mul (nabla_log hb)) |>.trans l5))

lemma nnabla_bound_aux1 (a : ℝ) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun x => x * (a + Real.log (x / b) ^ 2)) atTop atTop :=
  tendsto_id.atTop_mul_atTop₀ <| tendsto_atTop_add_const_left _ _ <|
    (tendsto_pow_atTop two_ne_zero).comp <| tendsto_log_atTop.comp <| tendsto_id.atTop_div_const hb

lemma nnabla_bound_aux2 (a : ℝ) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ x in atTop, 0 < x * (a + Real.log (x / b) ^ 2) :=
  (nnabla_bound_aux1 a hb).eventually (eventually_gt_atTop 0)

lemma Real.log_eventually_gt_atTop (a : ℝ) :
    ∀ᶠ x in atTop, a < Real.log x :=
  Real.tendsto_log_atTop.eventually (eventually_gt_atTop a)

/-- Should this be a gcongr lemma? -/
theorem norm_lt_norm_of_nonneg (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) :
    ‖x‖ ≤ ‖y‖ := by
  simp_rw [Real.norm_eq_abs]
  apply abs_le_abs hxy
  linarith

lemma nnabla_bound_aux {x : ℝ} (hx : 0 < x) :
    nnabla (fun n ↦ 1 / (n * ((2 * π) ^ 2 + Real.log (n / x) ^ 2))) =O[atTop]
    (fun n ↦ 1 / (Real.log n ^ 2 * n ^ 2)) := by

  let d n : ℝ := n * ((2 * π) ^ 2 + Real.log (n / x) ^ 2)
  change (fun x_1 ↦ nnabla (fun n ↦ 1 / d n) x_1) =O[atTop] _

  have l2 : ∀ᶠ n in atTop, 0 < d n := (nnabla_bound_aux2 ((2 * π) ^ 2) hx)
  have l3 : ∀ᶠ n in atTop, 0 < d (n + 1) :=
    (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id).eventually l2
  have l1 : ∀ᶠ n : ℝ in atTop,
      nnabla (fun n ↦ 1 / d n) n = (d (n + 1) - d n) * (d n)⁻¹ * (d (n + 1))⁻¹ := by
    filter_upwards [l2, l3] with n l2 l3
    rw [nnabla, one_div, one_div, inv_sub_inv l2.ne.symm l3.ne.symm, div_eq_mul_inv, mul_inv,
      mul_assoc]

  have l4 : (fun n => (d n)⁻¹) =O[atTop] (fun n => (n * (Real.log n) ^ 2)⁻¹) := by
    apply IsBigO.inv_rev
    · refine (isBigO_refl _ _).mul <| (log_sq_isbigo_mul hx)
    · filter_upwards [Real.log_eventually_gt_atTop 0, eventually_gt_atTop 0] with x hx hx'
      rw [← not_imp_not]
      intro _
      positivity
  have l5 : (fun n => (d (n + 1))⁻¹) =O[atTop] (fun n => (n * (Real.log n) ^ 2)⁻¹) := by
    refine IsBigO.trans ?_ l4
    rw [isBigO_iff]; use 1
    have e3 : ∀ᶠ n in atTop, d n ≤ d (n + 1) := by
      filter_upwards [eventually_ge_atTop x] with n hn
      have e2 : 1 ≤ n / x := (one_le_div hx).mpr hn
      have : 0 ≤ n := hx.le.trans hn
      simp only [d]
      gcongr <;> simp [Real.log_nonneg, *]
    filter_upwards [l2, l3, e3] with n e1 e2 e3
    simp_rw [one_mul]
    exact norm_lt_norm_of_nonneg _ _ (inv_nonneg.mpr e2.le) (inv_anti₀ e1 e3)

  have l6 : (fun n => d (n + 1) - d n) =O[atTop] (fun n => (Real.log n) ^ 2) := by
    simpa [d, nabla] using! (nnabla_mul_log_sq ((2 * π) ^ 2) hx)

  apply EventuallyEq.trans_isBigO l1

  apply ((l6.mul l4).mul l5).trans_eventuallyEq
  filter_upwards [eventually_ge_atTop 2, Real.log_eventually_gt_atTop 0] with n hn hn'
  field_simp

lemma nnabla_bound (C : ℝ) {x : ℝ} (hx : 0 < x) :
    nnabla (fun n => C / (1 + (Real.log (n / x) / (2 * π)) ^ 2) / n) =O[atTop]
    (fun n => (n ^ 2 * (Real.log n) ^ 2)⁻¹) := by
  field_simp
  simp only [div_eq_mul_inv, mul_inv, nnabla_mul, one_mul]
  apply IsBigO.const_mul_left
  simpa [div_eq_mul_inv, mul_pow, mul_comm] using nnabla_bound_aux hx

def chebyWith (C : ℝ) (f : ℕ → ℂ) : Prop := ∀ n, cumsum (‖f ·‖) n ≤ C * n

def cheby (f : ℕ → ℂ) : Prop := ∃ C, chebyWith C f

lemma cheby.bigO (h : cheby f) : cumsum (‖f ·‖) =O[atTop] ((↑) : ℕ → ℝ) := by
  have l1 : 0 ≤ cumsum (‖f ·‖) := cumsum_nonneg (fun _ => norm_nonneg _)
  obtain ⟨C, hC⟩ := h
  apply isBigO_of_le' (c := C) atTop
  intro n
  rw [Real.norm_eq_abs, abs_eq_self.mpr (l1 n)]
  simpa using hC n

lemma limiting_fourier_lim1_aux (hcheby : cheby f) (hx : 0 < x) (C : ℝ) (hC : 0 ≤ C) :
    Summable fun n ↦ ‖f n‖ / ↑n * (C / (1 + (1 / (2 * π) * Real.log (↑n / x)) ^ 2)) := by

  let a (n : ℕ) := (C / (1 + (Real.log (↑n / x) / (2 * π)) ^ 2) / ↑n)
  replace hcheby := hcheby.bigO

  have l1 : shift (cumsum (‖f ·‖)) =O[atTop] (fun n : ℕ => (↑(n + 1) : ℝ)) :=
    hcheby.comp_tendsto <| tendsto_add_atTop_nat 1
  have l2 : shift (cumsum (‖f ·‖)) =O[atTop] (fun n => (n : ℝ)) :=
    l1.trans
      (by simpa using (isBigO_refl _ _).add <| isBigO_iff.mpr ⟨1, by simpa using ⟨1, by tauto⟩⟩)
  have l5 : BoundedAtFilter atTop (fun n : ℕ => C / (1 + (Real.log (↑n / x) / (2 * π)) ^ 2)) := by
    simp only [BoundedAtFilter]
    field_simp
    apply isBigO_of_le' (c := C) ; intro n
    have : 0 ≤ 2 ^ 2 * π ^ 2 + Real.log (n / x) ^ 2 := by positivity
    simp only [norm_div, norm_mul, norm_eq_abs, abs_eq_self.mpr hC, norm_pow,
      abs_eq_self.mpr pi_nonneg, abs_eq_self.mpr this, Pi.one_apply, one_mem,
      CStarRing.norm_of_mem_unitary, mul_one, ge_iff_le, Nat.abs_ofNat]
    apply div_le_of_le_mul₀ this hC
    rw [mul_add, ← mul_assoc]
    apply le_add_of_le_of_nonneg le_rfl
    positivity
  have l3 : a =O[atTop] (fun n => 1 / (n : ℝ)) := by
    simpa [a] using! IsBigO.mul l5 (isBigO_refl (fun n : ℕ => 1 / (n : ℝ)) _)
  have l4 : nnabla a =O[atTop] (fun n : ℕ => (n ^ 2 * (Real.log n) ^ 2)⁻¹) := by
    convert (nnabla_bound C hx).natCast ; simp [nnabla, a]

  simp_rw [div_mul_eq_mul_div, mul_div_assoc, one_mul]
  apply dirichlet_test'
  · intro n ; exact norm_nonneg _
  · intro n ; positivity
  · apply (l2.mul l3).trans_eventuallyEq
    apply eventually_of_mem (Ici_mem_atTop 1)
    intro x (hx : 1 ≤ x)
    have : x ≠ 0 := Nat.one_le_iff_ne_zero.mp hx
    simp [this]
  · have : ∀ᶠ n : ℕ in atTop, x ≤ n := by simpa using eventually_ge_atTop ⌈x⌉₊
    filter_upwards [this] with n hn
    have e1 : 0 < (n : ℝ) := by linarith
    have e2 : 1 ≤ n / x := (one_le_div hx).mpr hn
    have e3 := Nat.le_succ n
    gcongr
    refine div_nonneg (Real.log_nonneg e2) (by norm_num [pi_nonneg])
  · apply summable_of_isBigO_nat summable_inv_mul_log_sq
    apply (l2.mul l4).trans_eventuallyEq
    apply eventually_of_mem (Ici_mem_atTop 2)
    intro x (hx : 2 ≤ x)
    have : (x : ℝ) ≠ 0 := by simp ; linarith
    have : Real.log x ≠ 0 := by
      have ll : 2 ≤ (x : ℝ) := by simp [hx]
      simp
      grind
    field_simp

theorem limiting_fourier_lim1 (hcheby : cheby f) (ψ : W21) (hx : 0 < x) :
    Tendsto (fun σ' : ℝ ↦
        ∑' n, term f σ' n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (n / x))) (𝓝[>] 1)
      (𝓝 (∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (n / x)))) := by

  obtain ⟨C, hC⟩ := decay_bounds_cor ψ
  have : 0 ≤ C := by simpa using (norm_nonneg _).trans (hC 0)
  refine tendsto_tsum_of_dominated_convergence
    (limiting_fourier_lim1_aux hcheby hx C this) (fun n => ?_) ?_
  · apply Tendsto.mul_const
    by_cases h : n = 0 <;> simp only [term, h, ↓reduceIte, CharP.cast_eq_zero, div_zero,
      tendsto_const_nhds_iff]
    refine tendsto_const_nhds.div ?_ (by simp [h])
    simpa using ((continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds).const_cpow
  · rw [eventually_nhdsWithin_iff]
    apply Eventually.of_forall
    intro σ' (hσ' : 1 < σ') n
    rw [norm_mul, ← nterm_eq_norm_term]
    refine mul_le_mul ?_ (hC _) (norm_nonneg _) (div_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
    by_cases h : n = 0 <;> simp only [nterm, h, ↓reduceIte, CharP.cast_eq_zero, div_zero, le_refl]
    have : 1 ≤ (n : ℝ) := by simpa using! Nat.pos_iff_ne_zero.mpr h
    refine div_le_div₀ (norm_nonneg _) le_rfl (by simpa [Nat.pos_iff_ne_zero]) ?_
    simpa using Real.rpow_le_rpow_of_exponent_le this hσ'.le

theorem limiting_fourier_lim2_aux (x : ℝ) (C : ℝ) :
    Integrable (fun t ↦ max |x| 1 * (C / (1 + (t / (2 * π)) ^ 2)))
      (Measure.restrict volume (Ici (-Real.log x))) := by
  simp_rw [div_eq_mul_inv C]
  exact (((integrable_inv_one_add_sq.comp_div
    (by simp [pi_ne_zero])).const_mul _).const_mul _).restrict

theorem limiting_fourier_lim2 (A : ℝ) (ψ : W21) (hx : 1 ≤ x) :
    Tendsto (fun σ' ↦ A * ↑(x ^ (1 - σ')) *
        ∫ u in Ici (-Real.log x), rexp (-u * (σ' - 1)) * 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)))
      (𝓝[>] 1) (𝓝 (A * ∫ u in Ici (-Real.log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)))) := by

  obtain ⟨C, hC⟩ := decay_bounds_cor ψ
  apply Tendsto.mul
  · suffices h : Tendsto (fun σ' : ℝ ↦ ofReal (x ^ (1 - σ'))) (𝓝[>] 1) (𝓝 1) by
      simpa using h.const_mul ↑A
    suffices h : Tendsto (fun σ' : ℝ ↦ x ^ (1 - σ')) (𝓝[>] 1) (𝓝 1) from
      (continuous_ofReal.tendsto 1).comp h
    have : Tendsto (fun σ' : ℝ ↦ σ') (𝓝 1) (𝓝 1) := fun _ a ↦ a
    have : Tendsto (fun σ' : ℝ ↦ 1 - σ') (𝓝[>] 1) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds (by simpa using this.const_sub 1)
    simpa using tendsto_const_nhds.rpow this (Or.inl (zero_lt_one.trans_le hx).ne.symm)
  · refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_
      (limiting_fourier_lim2_aux x C) ?_
    · apply Eventually.of_forall ; intro σ'
      apply Continuous.aestronglyMeasurable
      have := continuous_FourierIntegral ψ
      continuity
    · apply eventually_of_mem (U := Ioo 1 2)
      · apply Ioo_mem_nhdsGT_of_mem ; simp
      · intro σ' ⟨h1, h2⟩
        rw [ae_restrict_iff' measurableSet_Ici]
        apply Eventually.of_forall
        intro t (ht : - Real.log x ≤ t)
        rw [norm_mul]
        have hdom_nonneg : 0 ≤ max |x| 1 := by
          exact (abs_nonneg x).trans (le_max_left _ _)
        refine mul_le_mul ?_ (hC _) (norm_nonneg _) hdom_nonneg
        simp only [neg_mul, ofReal_exp, ofReal_neg, ofReal_mul, ofReal_sub, ofReal_one, norm_exp,
          neg_re, mul_re, ofReal_re, sub_re, one_re, ofReal_im, sub_im, one_im, sub_self, mul_zero,
          sub_zero]
        have : -Real.log x * (σ' - 1) ≤ t * (σ' - 1) := mul_le_mul_of_nonneg_right ht (by linarith)
        have : -(t * (σ' - 1)) ≤ Real.log x * (σ' - 1) := by simpa using neg_le_neg this
        have := Real.exp_monotone this
        apply this.trans
        have l1 : σ' - 1 ≤ 1 := by linarith
        have : 0 ≤ Real.log x := Real.log_nonneg hx
        have := mul_le_mul_of_nonneg_left l1 this
        refine (Real.exp_monotone this).trans ?_
        have hxabs : |x| = x := abs_of_nonneg (zero_le_one.trans hx)
        calc
          Real.exp (Real.log x * 1) = |x| := by
            simpa [mul_one, hxabs] using (Real.exp_log (zero_lt_one.trans_le hx))
          _ ≤ max |x| 1 := le_max_left _ _
    · apply Eventually.of_forall
      intro x
      suffices h : Tendsto (fun n ↦ ((rexp (-x * (n - 1))) : ℂ)) (𝓝[>] 1) (𝓝 1) by
        simpa using h.mul_const _
      apply Tendsto.mono_left ?_ nhdsWithin_le_nhds
      suffices h : Continuous (fun n ↦ ((rexp (-x * (n - 1))) : ℂ)) by simpa using h.tendsto 1
      continuity

theorem limiting_fourier_lim3 (hG : ContinuousOn G {s | 1 ≤ s.re}) (ψ : CS 2 ℂ) (hx : 1 ≤ x) :
    Tendsto (fun σ' : ℝ ↦ ∫ t : ℝ, G (σ' + t * I) * ψ t * x ^ (t * I)) (𝓝[>] 1)
      (𝓝 (∫ t : ℝ, G (1 + t * I) * ψ t * x ^ (t * I))) := by

  by_cases hh : tsupport ψ = ∅
  · simp [tsupport_eq_empty_iff.mp hh]
  obtain ⟨a₀, ha₀⟩ := Set.nonempty_iff_ne_empty.mpr hh

  let S : Set ℂ := reProdIm (Icc 1 2) (tsupport ψ)
  have l1 : IsCompact S := by
    refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨?_, ?_⟩
    · exact isClosed_Icc.reProdIm (isClosed_tsupport ψ)
    · exact (Metric.isBounded_Icc 1 2).reProdIm ψ.h2.isBounded
  have l2 : S ⊆ {s : ℂ | 1 ≤ s.re} := fun z hz => (mem_reProdIm.mp hz).1.1
  have l3 : ContinuousOn (‖G ·‖) S := (hG.mono l2).norm
  have l4 : S.Nonempty := ⟨1 + a₀ * I, by simp [S, mem_reProdIm, ha₀]⟩
  obtain ⟨z, -, hmax⟩ := l1.exists_isMaxOn l4 l3
  let MG := ‖G z‖
  let bound (a : ℝ) : ℝ := MG * ‖ψ a‖

  apply tendsto_integral_filter_of_dominated_convergence (bound := bound)
  · apply eventually_of_mem (U := Icc 1 2) (Icc_mem_nhdsGT_of_mem (by simp)) ; intro u hu
    apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · exact (hG.comp_continuous (by fun_prop) (by simp [hu.1])).mul ψ.h1.continuous
    · apply Continuous.const_cpow (by fun_prop) ; simp ; linarith
  · apply eventually_of_mem (U := Icc 1 2) (Icc_mem_nhdsGT_of_mem (by simp))
    intro u hu
    apply Eventually.of_forall ; intro v
    by_cases h : v ∈ tsupport ψ
    · have r1 : u + v * I ∈ S := by simp [S, mem_reProdIm, hu.1, hu.2, h]
      have r2 := isMaxOn_iff.mp hmax _ r1
      have r4 : (x : ℂ) ≠ 0 := by simp ; linarith
      have r5 : arg x = 0 := by simp [arg_eq_zero_iff] ; linarith
      have r3 : ‖(x : ℂ) ^ (v * I)‖ = 1 := by simp [norm_cpow_of_ne_zero r4, r5]
      simp_rw [norm_mul, r3, mul_one]
      exact mul_le_mul_of_nonneg_right r2 (norm_nonneg _)
    · have : v ∉ Function.support ψ := fun a ↦ h (subset_tsupport ψ a)
      simp at this ; simp [this, bound]

  · suffices h : Continuous bound by exact h.integrable_of_hasCompactSupport ψ.h2.norm.mul_left
    have := ψ.h1.continuous ; fun_prop
  · apply Eventually.of_forall ; intro t
    apply Tendsto.mul_const
    apply Tendsto.mul_const
    refine (hG (1 + t * I) (by simp)).tendsto.comp <| tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact ((continuous_ofReal.tendsto _).add tendsto_const_nhds).mono_left nhdsWithin_le_nhds
    · exact eventually_nhdsWithin_of_forall (fun x (hx : 1 < x) => by simp [hx.le])

lemma limiting_fourier (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (ψ : CS 2 ℂ) (hx : 1 ≤ x) :
    ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)) =
      ∫ (t : ℝ), (G (1 + t * I)) * (ψ t) * x ^ (t * I) := by

  have l1 := limiting_fourier_lim1 hcheby ψ (by linarith)
  have l2 := limiting_fourier_lim2 A ψ hx
  have l3 := limiting_fourier_lim3 hG ψ hx
  apply tendsto_nhds_unique_of_eventuallyEq (l1.sub l2) l3
  simpa [eventuallyEq_nhdsWithin_iff] using! Eventually.of_forall (limiting_fourier_aux hG' hf ψ hx)




lemma limiting_cor_aux {f : ℝ → ℂ} : Tendsto (fun x : ℝ ↦ ∫ t, f t * x ^ (t * I)) atTop (𝓝 0) := by

  have l1 : ∀ᶠ x : ℝ in atTop, ∀ t : ℝ, x ^ (t * I) = exp (log x * t * I) := by
    filter_upwards [eventually_ne_atTop 0, eventually_ge_atTop 0] with x hx hx' t
    rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx), ofReal_log hx'] ; ring_nf

  have l2 : ∀ᶠ x : ℝ in atTop, ∫ t, f t * x ^ (t * I) = ∫ t, f t * exp (log x * t * I) := by
    filter_upwards [l1] with x hx
    refine integral_congr_ae (Eventually.of_forall (fun x => by simp [hx]))

  simp_rw [tendsto_congr' l2]
  convert_to Tendsto (fun x => 𝓕 f (-Real.log x / (2 * π))) atTop (𝓝 0)
  · ext x
    rw [Real.fourier_real_eq_integral_exp_smul]
    congr 1; ext t
    rw [smul_eq_mul, mul_comm (f t)]
    congr 2
    push_cast
    field_simp
  refine (Real.zero_at_infty_fourier f).comp <| Tendsto.mono_right ?_ _root_.atBot_le_cocompact
  exact (tendsto_neg_atBot_iff.mpr tendsto_log_atTop).atBot_mul_const (inv_pos.mpr two_pi_pos)

lemma limiting_cor (ψ : CS 2 ℂ) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun x : ℝ ↦ ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))) atTop (𝓝 0) := by

  apply limiting_cor_aux.congr'
  filter_upwards [eventually_ge_atTop 1] with x hx using
    limiting_fourier hcheby hG hG' hf ψ hx |>.symm





lemma smooth_urysohn (a b c d : ℝ) (h1 : a < b) (h3 : c < d) : ∃ Ψ : ℝ → ℝ,
    (ContDiff ℝ ∞ Ψ) ∧ (HasCompactSupport Ψ) ∧
      Set.indicator (Set.Icc b c) 1 ≤ Ψ ∧ Ψ ≤ Set.indicator (Set.Ioo a d) 1 := by

  obtain ⟨ψ, l1, l2, l3, l4, -⟩ := smooth_urysohn_support_Ioo h1 h3
  refine ⟨ψ, l1, l2, l3, l4⟩



noncomputable def exists_trunc : trunc := by
  choose ψ h1 h2 h3 h4 using smooth_urysohn (-2) (-1) (1) (2) (by linarith) (by linarith)
  exact ⟨⟨ψ, h1.of_le (by norm_cast), h2⟩, h3, h4⟩

lemma one_div_sub_one (n : ℕ) : 1 / (↑(n - 1) : ℝ) ≤ 2 / n := by
  match n with
  | 0 => simp
  | 1 => simp
  | n + 2 => { norm_cast ; rw [div_le_div_iff₀] <;> simp [mul_add] <;> linarith }

lemma quadratic_pos (a b c x : ℝ) (ha : 0 < a) (hΔ : discrim a b c < 0) :
    0 < a * x ^ 2 + b * x + c := by
  have l1 : a * x ^ 2 + b * x + c = a * (x + b / (2 * a)) ^ 2 - discrim a b c / (4 * a) := by
    simp only [discrim]; field_simp; ring
  have l2 : 0 < - discrim a b c := by linarith
  rw [l1, sub_eq_add_neg, ← neg_div] ; positivity

noncomputable def pp (a x : ℝ) : ℝ := a ^ 2 * (x + 1) ^ 2 + (1 - a) * (1 + a)

noncomputable def pp' (a x : ℝ) : ℝ := a ^ 2 * (2 * (x + 1))

lemma pp_pos {a : ℝ} (ha : a ∈ Ioo (-1) 1) (x : ℝ) : 0 < pp a x := by
  simp only [pp]
  have : 0 < 1 - a := by linarith [ha.2]
  have : 0 < 1 + a := by linarith [ha.1]
  positivity

lemma pp_deriv (a x : ℝ) : HasDerivAt (pp a) (pp' a x) x := by
  unfold pp pp'
  simpa using hasDerivAt_id x |>.add_const 1 |>.pow 2 |>.const_mul _

lemma pp_deriv_eq (a : ℝ) : deriv (pp a) = pp' a := by
  ext x ; exact pp_deriv a x |>.deriv

lemma pp'_deriv (a x : ℝ) : HasDerivAt (pp' a) (a ^ 2 * 2) x := by
  simpa using! hasDerivAt_id x |>.add_const 1 |>.const_mul 2 |>.const_mul (a ^ 2)

lemma pp'_deriv_eq (a : ℝ) : deriv (pp' a) = fun _ => a ^ 2 * 2 := by
  ext x ; exact pp'_deriv a x |>.deriv

noncomputable def hh (a t : ℝ) : ℝ := (t * (1 + (a * log t) ^ 2))⁻¹

noncomputable def hh' (a t : ℝ) : ℝ := - pp a (log t) * hh a t ^ 2

lemma hh_nonneg (a : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ hh a t := by dsimp only [hh] ; positivity

lemma hh_le (a t : ℝ) (ht : 0 ≤ t) : |hh a t| ≤ t⁻¹ := by
  by_cases h0 : t = 0
  · simp [hh, h0]
  replace ht : 0 < t := lt_of_le_of_ne ht (by tauto)
  unfold hh
  rw [abs_inv, inv_le_inv₀ (by positivity) ht, abs_mul, abs_eq_self.mpr ht.le]
  convert_to! t * 1 ≤ _
  · simp
  apply mul_le_mul le_rfl ?_ zero_le_one ht.le
  rw [abs_eq_self.mpr (by positivity)]
  simp only [le_add_iff_nonneg_right]
  positivity

lemma hh_deriv (a : ℝ) {t : ℝ} (ht : t ≠ 0) : HasDerivAt (hh a) (hh' a t) t := by
  have e1 : t * (1 + (a * log t) ^ 2) ≠ 0 := mul_ne_zero ht (_root_.ne_of_lt (by positivity)).symm
  have l5 : HasDerivAt (fun t : ℝ => log t) t⁻¹ t := Real.hasDerivAt_log ht
  have l4 : HasDerivAt (fun t : ℝ => a * log t) (a * t⁻¹) t := l5.const_mul _
  have l3 : HasDerivAt (fun t : ℝ => (a * log t) ^ 2) (2 * a ^ 2 * t⁻¹ * log t) t := by
    convert! l4.pow 2 using 1 ; ring
  have l2 : HasDerivAt (fun t : ℝ => 1 + (a * log t) ^ 2) (2 * a ^ 2 * t⁻¹ * log t) t :=
    l3.const_add _
  have l1 : HasDerivAt (fun t : ℝ => t * (1 + (a * log t) ^ 2))
      (1 + 2 * a ^ 2 * log t + a ^ 2 * log t ^ 2) t := by
    convert! (hasDerivAt_id' t).mul l2 using 1; field_simp; ring
  convert! l1.inv e1 using 1; simp only [hh', pp, hh]; field_simp; ring

lemma hh_continuous (a : ℝ) : ContinuousOn (hh a) (Ioi 0) :=
  fun t (ht : 0 < t) => (hh_deriv a ht.ne.symm).continuousAt.continuousWithinAt

lemma hh'_nonpos {a x : ℝ} (ha : a ∈ Ioo (-1) 1) : hh' a x ≤ 0 := by
  have := pp_pos ha (log x)
  simp only [hh', neg_mul, Left.neg_nonpos_iff, ge_iff_le]
  positivity

lemma hh_antitone {a : ℝ} (ha : a ∈ Ioo (-1) 1) : AntitoneOn (hh a) (Ioi 0) := by
  have l1 x (hx : x ∈ interior (Ioi 0)) :
      HasDerivWithinAt (hh a) (hh' a x) (interior (Ioi 0)) x := by
    have : x ≠ 0 := by contrapose! hx ; simp [hx]
    exact (hh_deriv a this).hasDerivWithinAt
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi _) (hh_continuous _) l1
    (fun x _ => hh'_nonpos ha)

noncomputable def gg (x i : ℝ) : ℝ := 1 / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹

lemma gg_of_hh {x : ℝ} (hx : x ≠ 0) (i : ℝ) : gg x i = x⁻¹ * hh (1 / (2 * π)) (i / x) := by
  simp only [gg, hh]
  field_simp

lemma gg_l1 {x : ℝ} (hx : 0 < x) (n : ℕ) : |gg x n| ≤ 1 / n := by
  simp only [gg_of_hh hx.ne.symm, one_div, mul_inv_rev, abs_mul]
  apply mul_le_mul le_rfl (hh_le _ _ (by positivity)) (by positivity) (by positivity) |>.trans
    (le_of_eq ?_)
  simp [abs_inv, abs_eq_self.mpr hx.le] ; field_simp

lemma gg_le_one (i : ℕ) : gg x i ≤ 1 := by
  by_cases hi : i = 0 <;> simp only [gg, hi, CharP.cast_eq_zero, div_zero, one_div, mul_inv_rev,
    zero_div, Real.log_zero, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    add_zero, inv_one, mul_one, zero_le_one]
  have l1 : 1 ≤ (i : ℝ) := by simp ; omega
  have l2 : 1 ≤ 1 + (π⁻¹ * 2⁻¹ * Real.log (↑i / x)) ^ 2 := by
    simp only [le_add_iff_nonneg_right] ; positivity
  rw [← mul_inv] ; apply inv_le_one_of_one_le₀ ; simpa using mul_le_mul l1 l2 zero_le_one (by simp)

lemma one_div_two_pi_mem_Ioo : 1 / (2 * π) ∈ Ioo (-1) 1 := by
  constructor
  · trans 0
    · linarith
    · positivity
  · rw [div_lt_iff₀ (by positivity)]
    convert_to! 1 * 1 < 2 * π
    · simp
    · simp
    apply mul_lt_mul one_lt_two ?_ zero_lt_one zero_le_two
    trans 2
    · exact one_le_two
    · exact two_le_pi

lemma sum_telescopic (a : ℕ → ℝ) (n : ℕ) : ∑ i ∈ Finset.range n, (a (i + 1) - a i) = a n - a 0 := by
  apply Finset.sum_range_sub

lemma cancel_aux {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) :
    ∑ i ∈ Finset.range n, f i * g i ≤ g (n - 1) * (C * n) + (C * (↑(n - 1 - 1) + 1) * g 0
      - C * (↑(n - 1 - 1) + 1) * g (n - 1) -
    ((n - 1 - 1) • (C * g 0) - ∑ x ∈ Finset.range (n - 1 - 1), C * g (x + 1))) := by

  have l1 (n : ℕ) :
      (g n - g (n + 1)) * ∑ i ∈ Finset.range (n + 1), f i ≤ (g n - g (n + 1)) * (C * (n + 1)) := by
    apply mul_le_mul le_rfl (by simpa using! hf' (n + 1)) (Finset.sum_nonneg' hf) ?_
    simp only [sub_nonneg] ; apply hg' ; simp
  have l2 (x : ℕ) : C * (↑(x + 1) + 1) - C * (↑x + 1) = C := by simp ; ring
  have l3 (n : ℕ) : 0 ≤ cumsum f n := Finset.sum_nonneg' hf

  convert_to ∑ i ∈ Finset.range n, (g i) • (f i) ≤ _
  · simp [mul_comm]
  rw [Finset.sum_range_by_parts, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  simp_rw [← neg_smul, neg_sub, smul_eq_mul]
  apply _root_.add_le_add
  · exact mul_le_mul le_rfl (hf' n) (l3 n) (hg _)
  · apply Finset.sum_le_sum (fun n _ => l1 n) |>.trans
    convert_to! ∑ i ∈ Finset.range (n - 1), (C * (↑i + 1)) • (g i - g (i + 1)) ≤ _
    · congr ; ext i ; simp ; ring
    rw [Finset.sum_range_by_parts]
    simp_rw [Finset.sum_range_sub', l2, smul_sub, smul_eq_mul, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_range]
    apply le_of_eq ; ring_nf

lemma sum_range_succ (a : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, a (i + 1) = (∑ i ∈ Finset.range (n + 1), a i) - a 0 := by
  have := Finset.sum_range_sub a n
  rw [Finset.sum_sub_distrib, sub_eq_iff_eq_add] at this
  rw [Finset.sum_range_succ, this] ; ring

lemma cancel_aux' {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) :
    ∑ i ∈ Finset.range n, f i * g i ≤
        C * n * g (n - 1)
      + C * cumsum g (n - 1 - 1 + 1)
      - C * (↑(n - 1 - 1) + 1) * g (n - 1)
      := by
  have := cancel_aux hf hg hf' hg' n
  simp only [nsmul_eq_mul, ← Finset.mul_sum, sum_range_succ] at this
  convert this using 1 ; unfold cumsum ; ring

lemma cancel_main {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) (hn : 2 ≤ n) :
    cumsum (f * g) n ≤ C * cumsum g n := by
  convert! cancel_aux' hf hg hf' hg' n using 1
  match n with
  | n + 2 => simp only [cumsum_succ] ; push_cast ; ring

lemma cancel_main' {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hf0 : f 0 = 0) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) :
    cumsum (f * g) n ≤ C * cumsum g n := by
  match n with
  | 0 => simp [cumsum]
  | 1 => specialize hg 0 ; specialize hf' 1 ; simp only [cumsum, Finset.range_one,
    Finset.sum_singleton, hf0, Nat.cast_one, mul_one, Pi.zero_apply, Pi.mul_apply, zero_mul,
    ge_iff_le] at hf' hg ⊢ ; positivity
  | n + 2 => convert! cancel_aux' hf hg hf' hg' (n + 2) using 1 ; simp [cumsum_succ] ; ring

theorem sum_le_integral {x₀ : ℝ} {f : ℝ → ℝ} {n : ℕ} (hf : AntitoneOn f (Ioc x₀ (x₀ + n)))
    (hfi : IntegrableOn f (Icc x₀ (x₀ + n))) :
    (∑ i ∈ Finset.range n, f (x₀ + ↑(i + 1))) ≤ ∫ x in x₀..x₀ + n, f x := by

  cases n with simp only [Nat.cast_add, Nat.cast_one, CharP.cast_eq_zero, add_zero,
      lt_self_iff_false, not_false_eq_true,
    Ioc_eq_empty, Finset.range_zero, Nat.cast_add, Nat.cast_one, Finset.sum_empty,
    intervalIntegral.integral_same, le_refl] at hf ⊢
  | succ n =>
  have : Finset.range (n + 1) = {0} ∪ Finset.Ico 1 (n + 1) := by
    ext i ; by_cases hi : i = 0 <;> simp [hi] ; omega
  simp only [this, Finset.singleton_union, Finset.mem_Ico, nonpos_iff_eq_zero, one_ne_zero,
    lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, and_true, not_false_eq_true,
    Finset.sum_insert, CharP.cast_eq_zero, zero_add, ge_iff_le]

  have l4 : IntervalIntegrable f volume x₀ (x₀ + 1) := by
    apply IntegrableOn.intervalIntegrable
    simp only [le_add_iff_nonneg_right, zero_le_one, uIcc_of_le]
    apply hfi.mono_set
    apply Icc_subset_Icc le_rfl
    simp
  have l5 x (hx : x ∈ Ioc x₀ (x₀ + 1)) : (fun x ↦ f (x₀ + 1)) x ≤ f x := by
    rcases hx with ⟨hx1, hx2⟩
    refine hf ⟨hx1, by linarith⟩ ⟨by linarith, by linarith⟩ hx2
  have l6 : ∫ x in x₀..x₀ + 1, f (x₀ + 1) = f (x₀ + 1) := by simp

  have l1 : f (x₀ + 1) ≤ ∫ x in x₀..x₀ + 1, f x := by
    rw [← l6] ; apply intervalIntegral.integral_mono_ae_restrict (by linarith) (by simp) l4
    apply eventually_of_mem _ l5
    have : (Ioc x₀ (x₀ + 1))ᶜ ∩ Icc x₀ (x₀ + 1) = {x₀} := by simp [← sdiff_eq_compl_inter]
    rw [mem_ae_iff, Measure.restrict_apply measurableSet_Ioc.compl, this]
    simp

  have l2 : AntitoneOn (fun x ↦ f (x₀ + x)) (Icc 1 ↑(n + 1)) := by
    intro u ⟨hu1, _⟩ v ⟨_, hv2⟩ huv ; push_cast at hv2
    refine hf ⟨?_, ?_⟩ ⟨?_, ?_⟩ ?_ <;> linarith

  have l3 := @AntitoneOn.sum_le_integral_Ico 1 (n + 1) (fun x => f (x₀ + x)) (by simp)
    (by simpa using l2)

  simp only [Nat.cast_add, Nat.cast_one, intervalIntegral.integral_comp_add_left] at l3
  convert! _root_.add_le_add l1 l3

  have := @intervalIntegral.integral_comp_mul_add ℝ _ _ 1 (n + 1) 1 f one_ne_zero x₀
  rw [intervalIntegral.integral_add_adjacent_intervals]
  · exact l4
  · apply IntegrableOn.intervalIntegrable
    simp only [add_le_add_iff_left, le_add_iff_nonneg_left, Nat.cast_nonneg, uIcc_of_le]
    apply hfi.mono_set
    apply Icc_subset_Icc
    · linarith
    · simp

lemma hh_integrable_aux (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (IntegrableOn (fun t ↦ a * hh b (t / c)) (Ici 0)) ∧
    (∫ (t : ℝ) in Ioi 0, a * hh b (t / c) = a * c / b * π) := by

  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  simp only [hh]

  let g (x : ℝ) := (a * c / b) * Real.arctan (b * log (x / c))
  let g₀ (x : ℝ) := if x = 0 then ((a * c / b) * (- (π / 2))) else g x
  let g' (x : ℝ) := a * (x / c * (1 + (b * Real.log (x / c)) ^ 2))⁻¹

  have l3 (x) (hx : 0 < x) : HasDerivAt Real.log x⁻¹ x := by apply Real.hasDerivAt_log (by linarith)
  have l4 (x) : HasDerivAt (fun t => t / c) (1 / c) x := (hasDerivAt_id x).div_const c
  have l2 (x) (hx : 0 < x) : HasDerivAt (fun t => log (t / c)) x⁻¹ x := by
    have := @HasDerivAt.comp _ _ _ _ _ _ (fun t => t / c) _ _ _  (l3 (x / c) (by positivity)) (l4 x)
    convert! this using 1 ; field_simp
  have l5 (x) (hx : 0 < x) := (l2 x hx).const_mul b
  have l1 (x) (hx : 0 < x) := (l5 x hx).arctan
  have l6 (x) (hx : 0 < x) : HasDerivAt g (g' x) x := by
    convert! (l1 x hx).const_mul (a * c / b) using 1
    simp only [g']
    field_simp
  have key (x) (hx : 0 < x) : HasDerivAt g₀ (g' x) x := by
    apply (l6 x hx).congr_of_eventuallyEq
    apply eventually_of_mem <| Ioi_mem_nhds hx
    intro y (hy : 0 < y)
    simp [g₀, hy.ne.symm]

  have k1 : Tendsto g₀ atTop (𝓝 ((a * c / b) * (π / 2))) := by
    have : g =ᶠ[atTop] g₀ := by
      apply eventually_of_mem (Ioi_mem_atTop 0)
      intro y (hy : 0 < y)
      simp [g₀, hy.ne.symm]
    apply Tendsto.congr' this
    apply Tendsto.const_mul
    apply (tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
    apply Tendsto.const_mul_atTop hb
    apply tendsto_log_atTop.comp
    apply Tendsto.atTop_div_const hc
    apply tendsto_id

  have k2 : Tendsto g₀ (𝓝[>] 0) (𝓝 (g₀ 0)) := by
    have : g =ᶠ[𝓝[>] 0] g₀ := by
      apply eventually_of_mem self_mem_nhdsWithin
      intro x (hx : 0 < x) ; simp [g₀, hx.ne.symm]
    simp only [g₀]
    apply Tendsto.congr' this
    apply Tendsto.const_mul
    apply (tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp
    apply Tendsto.const_mul_atBot hb
    apply tendsto_log_nhdsGT_zero.comp
    rw [Metric.tendsto_nhdsWithin_nhdsWithin]
    intro ε hε
    refine ⟨c * ε, by positivity, fun x hx1 hx2 => ⟨?_, ?_⟩⟩
    · simp only [mem_Ioi] at hx1 ⊢ ; positivity
    · simp only [dist_zero_right, norm_eq_abs, norm_div, abs_eq_self.mpr hc.le] at hx2 ⊢
      rwa [div_lt_iff₀ hc, mul_comm]

  have k3 : ContinuousWithinAt g₀ (Ici 0) 0 := by
    rw [Metric.continuousWithinAt_iff]
    rw [Metric.tendsto_nhdsWithin_nhds] at k2
    peel k2 with ε hε δ hδ x h
    intro (hx : 0 ≤ x)
    have := le_iff_lt_or_eq.mp hx
    cases this with
    | inl hx => exact h hx
    | inr hx => simp [g₀, hx.symm, hε]

  have k4 : ∀ x ∈ Ioi 0, 0 ≤ g' x := by
    intro x (hx : 0 < x) ; simp only [mul_inv_rev, inv_div, g'] ; positivity

  constructor
  · convert_to IntegrableOn g' _
    exact integrableOn_Ioi_deriv_of_nonneg k3 key k4 k1
  · have := integral_Ioi_of_hasDerivAt_of_nonneg k3 key k4 k1
    simp only [mul_inv_rev, inv_div, mul_neg, ↓reduceIte, sub_neg_eq_add, g', g₀] at this ⊢
    convert this using 1 ; field_simp ; ring

lemma hh_integrable (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    IntegrableOn (fun t ↦ a * hh b (t / c)) (Ici 0) :=
  hh_integrable_aux ha hb hc |>.1

lemma hh_integral (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ∫ (t : ℝ) in Ioi 0, a * hh b (t / c) = a * c / b * π :=
  hh_integrable_aux ha hb hc |>.2

lemma hh_integral' : ∫ t in Ioi 0, hh (1 / (2 * π)) t = 2 * π ^ 2 := by
  have := hh_integral (a := 1) (b := 1 / (2 * π)) (c := 1)
    (by positivity) (by positivity) (by positivity)
  convert this using 1 <;> simp ; ring

lemma bound_sum_log {C : ℝ} (hf0 : f 0 = 0) (hf : chebyWith C f) {x : ℝ} (hx : 1 ≤ x) :
    ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ ≤
      C * (1 + ∫ t in Ioi 0, hh (1 / (2 * π)) t) := by

  let ggg (i : ℕ) : ℝ := if i = 0 then 1 else gg x i

  have l0 : x ≠ 0 := by linarith
  have l1 i : 0 ≤ ggg i := by by_cases hi : i = 0 <;> simp only [gg, one_div, mul_inv_rev, hi,
    ↓reduceIte, zero_le_one, ggg] ; positivity
  have l2 : Antitone ggg := by
    intro i j hij ; by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp only [hj, ↓reduceIte, hi,
      le_refl, ggg]
    · exact gg_le_one _
    · omega
    · simp only [gg_of_hh l0]
      gcongr
      apply hh_antitone one_div_two_pi_mem_Ioo
      · simp only [mem_Ioi] ; positivity
      · simp only [mem_Ioi] ; positivity
      · gcongr
  have l3 : 0 ≤ C := by simpa [cumsum, hf0] using hf 1

  have l4 : 0 ≤ ∫ (t : ℝ) in Ioi 0, hh (π⁻¹ * 2⁻¹) t :=
    setIntegral_nonneg measurableSet_Ioi (fun x hx => hh_nonneg _ (LT.lt.le hx))

  have l5 {n : ℕ} : AntitoneOn (fun t ↦ x⁻¹ * hh (1 / (2 * π)) (t / x)) (Ioc 0 n) := by
    intro u ⟨hu1, _⟩ v ⟨hv1, _⟩ huv
    simp only
    apply mul_le_mul le_rfl ?_ (hh_nonneg _ (by positivity)) (by positivity)
    apply hh_antitone one_div_two_pi_mem_Ioo (by simp only [mem_Ioi] ; positivity)
      (by simp only [mem_Ioi] ; positivity)
    apply (div_le_div_iff_of_pos_right (by positivity)).mpr huv

  have l6 {n : ℕ} : IntegrableOn (fun t ↦ x⁻¹ * hh (π⁻¹ * 2⁻¹) (t / x)) (Icc 0 n) volume := by
    apply IntegrableOn.mono_set
      (hh_integrable (by positivity) (by positivity) (by positivity)) Icc_subset_Ici_self

  apply Real.tsum_le_of_sum_range_le (fun n => by positivity) ; intro n
  convert_to! ∑ i ∈ Finset.range n, ‖f i‖ * ggg i ≤ _
  · congr ; ext i
    by_cases hi : i = 0
    · simp [hi, hf0]
    · simp only [gg, hi, ↓reduceIte, ggg]
      field_simp

  apply cancel_main' (fun _ => norm_nonneg _) (by simp [hf0]) l1 hf l2 n |>.trans
  gcongr ; simp only [cumsum, gg_of_hh l0, one_div, mul_inv_rev, ggg]

  by_cases hn : n = 0
  · simp only [hn, Finset.range_zero, Finset.sum_empty] ; positivity
  replace hn : 0 < n := by omega
  have : Finset.range n = {0} ∪ Finset.Ico 1 n := by
    ext i ; simp ; by_cases hi : i = 0 <;> simp [hi, hn] ; omega
  simp only [this, Finset.singleton_union, Finset.mem_Ico, nonpos_iff_eq_zero, one_ne_zero,
    false_and, not_false_eq_true, Finset.sum_insert, ↓reduceIte, add_le_add_iff_left, ge_iff_le]
  convert_to! ∑ x_1 ∈ Finset.Ico 1 n, x⁻¹ * hh (π⁻¹ * 2⁻¹) (↑x_1 / x) ≤ _
  · apply Finset.sum_congr rfl (fun i hi => ?_)
    simp at hi
    have : i ≠ 0 := by omega
    simp [this]
  simp_rw [Finset.sum_Ico_eq_sum_range, add_comm 1]
  have := @sum_le_integral 0 (fun t => x⁻¹ * hh (π⁻¹ * 2⁻¹) (t / x)) (n - 1)
    (by simpa using l5) (by simpa using l6)
  simp only [zero_add] at this
  apply this.trans
  rw [@intervalIntegral.integral_comp_div ℝ _ _ 0 ↑(n - 1) x (fun t => x⁻¹ * hh (π⁻¹ * 2⁻¹) (t)) l0]
  simp only [zero_div, intervalIntegral.integral_const_mul, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ l0, one_mul]
  have : (0 : ℝ) ≤ ↑(n - 1) / x := by positivity
  rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
  simp only [this, ↓reduceIte, uIoc_of_le, smul_eq_mul, one_mul, ge_iff_le]
  apply integral_mono_measure
  · apply Measure.restrict_mono Ioc_subset_Ioi_self le_rfl
  · apply eventually_of_mem (self_mem_ae_restrict measurableSet_Ioi)
    intro x (hx : 0 < x)
    apply hh_nonneg _ hx.le
  · have := (@hh_integrable 1 (1 / (2 * π)) 1 (by positivity) (by positivity) (by positivity))
    simpa using! this.mono_set Ioi_subset_Ici_self

lemma bound_sum_log0 {C : ℝ} (hf : chebyWith C f) {x : ℝ} (hx : 1 ≤ x) :
    ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ ≤
      C * (1 + ∫ t in Ioi 0, hh (1 / (2 * π)) t) := by

  let f0 i := if i = 0 then 0 else f i
  have l1 : chebyWith C f0 := by
    intro n ; refine Finset.sum_le_sum (fun i _ => ?_) |>.trans (hf n)
    by_cases hi : i = 0 <;> simp [hi, f0]
  have l2 i : ‖f i‖ / i = ‖f0 i‖ / i := by by_cases hi : i = 0 <;> simp [hi, f0]
  simp_rw [l2] ; apply bound_sum_log rfl l1 hx

lemma bound_sum_log' {C : ℝ} (hf : chebyWith C f) {x : ℝ} (hx : 1 ≤ x) :
    ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ ≤ C * (1 + 2 * π ^ 2) := by
  simpa only [hh_integral'] using bound_sum_log0 hf hx

variable (f x) in
lemma summable_fourier_aux (ψ : W21) (i : ℕ) :
    ‖f i / i * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (i / x))‖ ≤
      W21.norm ψ * (‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹) := by
  convert! mul_le_mul_of_nonneg_left (decay_bounds_key ψ (1 / (2 * π) * log (i / x)))
    (norm_nonneg (f i / i)) using 1
  · simp
  · change _ = _ * (W21.norm ψ * _)
    simp only [W21.norm, mul_inv_rev, one_div, Complex.norm_div, RCLike.norm_natCast]
    ring

lemma summable_fourier (x : ℝ) (hx : 0 < x) (ψ : W21) (hcheby : cheby f) :
    Summable fun i ↦ ‖f i / ↑i * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (↑i / x))‖ := by
  have l5 : Summable fun i ↦ ‖f i‖ / ↑i * ((1 + (1 / (2 * ↑π) * ↑(Real.log (↑i / x))) ^ 2)⁻¹) := by
    simpa using limiting_fourier_lim1_aux hcheby hx 1 (zero_le_one' ℝ)
  have l6 := summable_fourier_aux x f ψ
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) l6
    (by simpa using l5.const_smul (W21.norm ψ))

lemma bound_I1 (x : ℝ) (hx : 0 < x) (ψ : W21) (hcheby : cheby f) :
    ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x))‖ ≤
    W21.norm ψ • ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ := by

  have l5 : Summable fun i ↦ ‖f i‖ / ↑i * ((1 + (1 / (2 * ↑π) * ↑(Real.log (↑i / x))) ^ 2)⁻¹) := by
    simpa using limiting_fourier_lim1_aux hcheby hx 1 (zero_le_one' ℝ)
  have l6 := summable_fourier_aux x f ψ
  have l1 : Summable fun i ↦ ‖f i / ↑i * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (↑i / x))‖ := by
    exact summable_fourier x hx ψ hcheby
  apply (norm_tsum_le_tsum_norm l1).trans
  simpa only [← Summable.tsum_const_smul _ l5] using!
    Summable.tsum_mono l1 (by simpa using l5.const_smul (W21.norm ψ)) l6

lemma bound_I1' {C : ℝ} (x : ℝ) (hx : 1 ≤ x) (ψ : W21) (hcheby : chebyWith C f) :
    ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x))‖ ≤
      W21.norm ψ * C * (1 + 2 * π ^ 2) := by

  apply bound_I1 x (by linarith) ψ ⟨_, hcheby⟩ |>.trans
  rw [smul_eq_mul, mul_assoc]
  apply mul_le_mul le_rfl (bound_sum_log' hcheby hx) ?_ W21.norm_nonneg
  apply tsum_nonneg (fun i => by positivity)

lemma bound_I2 (x : ℝ) (ψ : W21) :
    ‖∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))‖ ≤ W21.norm ψ * (2 * π ^ 2) := by

  have key a : ‖𝓕 (ψ : ℝ → ℂ) (a / (2 * π))‖ ≤ W21.norm ψ * (1 + (a / (2 * π)) ^ 2)⁻¹ :=
    decay_bounds_key ψ _
  have twopi : 0 ≤ 2 * π := by simp [pi_nonneg]
  have l3 : Integrable (fun a ↦ (1 + (a / (2 * π)) ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.comp_div (by norm_num [pi_ne_zero])
  have l2 : IntegrableOn (fun i ↦ W21.norm ψ * (1 + (i / (2 * π)) ^ 2)⁻¹) (Ici (-Real.log x)) := by
    exact (l3.const_mul _).integrableOn
  have l1 : IntegrableOn (fun i ↦ ‖𝓕 (ψ : ℝ → ℂ) (i / (2 * π))‖) (Ici (-Real.log x)) := by
    refine ((l3.const_mul (W21.norm ψ)).mono' ?_ ?_).integrableOn
    · apply Continuous.aestronglyMeasurable ; have := continuous_FourierIntegral ψ ; fun_prop
    · simp only [norm_norm, key] ; simp
  have l5 : 0 ≤ᵐ[volume] fun a ↦ (1 + (a / (2 * π)) ^ 2)⁻¹ := by
    apply Eventually.of_forall ; intro x ; positivity
  refine (norm_integral_le_integral_norm _).trans <| (setIntegral_mono l1 l2 key).trans ?_
  rw [integral_const_mul] ; gcongr
  · apply W21.norm_nonneg
  refine (setIntegral_le_integral l3 l5).trans ?_
  rw [Measure.integral_comp_div (fun x => (1 + x ^ 2)⁻¹) (2 * π)]
  simp [abs_eq_self.mpr twopi] ; ring_nf ; rfl

lemma bound_main {C : ℝ} (A : ℂ) (x : ℝ) (hx : 1 ≤ x) (ψ : W21)
    (hcheby : chebyWith C f) :
    ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))‖ ≤
      W21.norm ψ * (C * (1 + 2 * π ^ 2) + ‖A‖ * (2 * π ^ 2)) := by

  have l1 := bound_I1' x hx ψ hcheby
  have l2 := mul_le_mul (le_refl ‖A‖) (bound_I2 x ψ) (by positivity) (by positivity)
  apply norm_sub_le _ _ |>.trans ; rw [norm_mul]
  convert _root_.add_le_add l1 l2 using 1 ; ring


lemma limiting_cor_W21 (ψ : W21) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun x : ℝ ↦ ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))) atTop (𝓝 0) := by

  -- Shorter notation for clarity
  let S1 x (ψ : ℝ → ℂ) := ∑' (n : ℕ), f n / ↑n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (↑n / x))
  let S2 x (ψ : ℝ → ℂ) := ↑A * ∫ (u : ℝ) in Ici (-Real.log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))
  let S x ψ := S1 x ψ - S2 x ψ ; change Tendsto (fun x ↦ S x ψ) atTop (𝓝 0)

  -- Build the truncation
  obtain g := exists_trunc
  let Ψ R := g.scale R * ψ
  have key R : Tendsto (fun x ↦ S x (Ψ R)) atTop (𝓝 0) := limiting_cor (Ψ R) hf hcheby hG hG'

  -- Choose the truncation radius
  obtain ⟨C, hcheby⟩ := hcheby
  have hC : 0 ≤ C := by
    have : ‖f 0‖ ≤ C := by simpa [cumsum] using hcheby 1
    have : 0 ≤ ‖f 0‖ := by positivity
    linarith
  have key2 : Tendsto (fun R ↦ W21.norm (ψ - Ψ R)) atTop (𝓝 0) := W21_approximation ψ g
  simp_rw [Metric.tendsto_nhds] at key key2 ⊢ ; intro ε hε
  let M := C * (1 + 2 * π ^ 2) + ‖(A : ℂ)‖ * (2 * π ^ 2)
  obtain ⟨R, hRψ⟩ := (key2 ((ε / 2) / (1 + M)) (by positivity)).exists
  simp only [dist_zero_right, Real.norm_eq_abs, abs_eq_self.mpr W21.norm_nonneg] at hRψ key

  -- Apply the compact support case
  filter_upwards [eventually_ge_atTop 1, key R (ε / 2) (by positivity)] with x hx key

  -- Control the tail term
  have key3 : ‖S x (ψ - Ψ R)‖ < ε / 2 := by
    have : ‖S x _‖ ≤ _ * M := @bound_main f C A x hx (ψ - Ψ R) hcheby
    apply this.trans_lt
    apply (mul_le_mul (d := 1 + M) le_rfl (by simp) (by positivity) W21.norm_nonneg).trans_lt
    have : 0 < 1 + M := by positivity
    convert! (mul_lt_mul_iff_left₀ this).mpr hRψ using 1 ; field_simp

  -- Conclude the proof
  have S1_sub_1 x : 𝓕 (⇑ψ - ⇑(Ψ R)) x = 𝓕 (ψ : ℝ → ℂ) x - 𝓕 ⇑(Ψ R) x := by
    have l1 : AEStronglyMeasurable (fun x_1 : ℝ ↦ cexp (-(2 * ↑π * (↑x_1 * ↑x) * I))) volume := by
      refine (Continuous.mul ?_ continuous_const).neg.cexp.aestronglyMeasurable
      apply continuous_const.mul <| contDiff_ofReal.continuous.mul continuous_const
    simp only [Real.fourier_eq', neg_mul, RCLike.inner_apply', conj_trivial, ofReal_neg,
      ofReal_mul, ofReal_ofNat, Pi.sub_apply, smul_eq_mul, mul_sub]
    apply integral_sub
    · apply ψ.hf.bdd_mul (c := 1) l1 ; simp [Complex.norm_exp]
    · apply (Ψ R : W21) |>.hf |>.bdd_mul (c := 1) l1
      simp [Complex.norm_exp]

  have S1_sub : S1 x (ψ - Ψ R) = S1 x ψ - S1 x (Ψ R) := by
    simp only [one_div, mul_inv_rev, S1_sub_1, mul_sub, S1] ; apply Summable.tsum_sub
    · have := summable_fourier x (by positivity) ψ ⟨_, hcheby⟩
      rw [summable_norm_iff] at this
      simpa using this
    · have := summable_fourier x (by positivity) (Ψ R) ⟨_, hcheby⟩
      rw [summable_norm_iff] at this
      simpa using! this

  have S2_sub : S2 x (ψ - Ψ R) = S2 x ψ - S2 x (Ψ R) := by
    simp only [S1_sub_1, S2] ; rw [integral_sub]
    · ring
    · exact ψ.integrable_fourier (by positivity) |>.restrict
    · exact (Ψ R : W21).integrable_fourier (by positivity) |>.restrict

  have S_sub : S x (ψ - Ψ R) = S x ψ - S x (Ψ R) := by simp [S, S1_sub, S2_sub] ; ring
  simpa [S_sub, Ψ] using norm_add_le _ _ |>.trans_lt (_root_.add_lt_add key3 key)

lemma limiting_cor_schwartz (ψ : 𝓢(ℝ, ℂ)) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun x : ℝ ↦ ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))) atTop (𝓝 0) :=
  limiting_cor_W21 ψ hf hcheby hG hG'





-- just the surjectivity is stated here, as this is all that is needed for the current
-- application, but perhaps one should state and prove bijectivity instead

lemma fourier_surjection_on_schwartz (f : 𝓢(ℝ, ℂ)) : ∃ g : 𝓢(ℝ, ℂ), 𝓕 g = f := by
  refine ⟨𝓕⁻ f, ?_⟩
  exact FourierTransform.fourier_fourierInv_eq f




noncomputable def toSchwartz (f : ℝ → ℂ) (h1 : ContDiff ℝ ∞ f)
    (h2 : HasCompactSupport f) : 𝓢(ℝ, ℂ) where
  toFun := f
  smooth' := h1
  decay' k n := by
    have l1 : Continuous (fun x => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) := by
      have : ContDiff ℝ ∞ (iteratedFDeriv ℝ n f) := h1.iteratedFDeriv_right (mod_cast le_top)
      exact Continuous.mul (by continuity) this.continuous.norm
    have l2 : HasCompactSupport (fun x ↦ ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) :=
      (h2.iteratedFDeriv _).norm.mul_left
    simpa using l1.bounded_above_of_compact_support l2

@[simp] lemma toSchwartz_apply (f : ℝ → ℂ) {h1 h2 x} : SchwartzMap.mk f h1 h2 x = f x := rfl

lemma comp_exp_support0 {Ψ : ℝ → ℂ} (hplus : closure (Function.support Ψ) ⊆ Ioi 0) :
    ∀ᶠ x in 𝓝 0, Ψ x = 0 :=
  notMem_tsupport_iff_eventuallyEq.mp (fun h => lt_irrefl 0 <| mem_Ioi.mp (hplus h))

lemma comp_exp_support1 {Ψ : ℝ → ℂ} (hplus : closure (Function.support Ψ) ⊆ Ioi 0) :
    ∀ᶠ x in atBot, Ψ (exp x) = 0 :=
  Real.tendsto_exp_atBot <| comp_exp_support0 hplus

lemma comp_exp_support2 {Ψ : ℝ → ℂ} (hsupp : HasCompactSupport Ψ) :
    ∀ᶠ (x : ℝ) in atTop, (Ψ ∘ rexp) x = 0 := by
  simp only [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact,
    cocompact_eq_atBot_atTop] at hsupp
  exact Real.tendsto_exp_atTop hsupp.2

theorem comp_exp_support {Ψ : ℝ → ℂ} (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Ioi 0) : HasCompactSupport (Ψ ∘ rexp) := by
  simp only [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact,
    cocompact_eq_atBot_atTop]
  exact ⟨comp_exp_support1 hplus, comp_exp_support2 hsupp⟩

lemma wiener_ikehara_smooth_aux (l0 : Continuous Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Ioi 0) (x : ℝ) (hx : 0 < x) :
    ∫ (u : ℝ) in Ioi (-Real.log x), ↑(rexp u) * Ψ (rexp u) = ∫ (y : ℝ) in Ioi (1 / x), Ψ y := by

  have l1 : ContinuousOn rexp (Ici (-Real.log x)) := by fun_prop
  have l2 : Tendsto rexp atTop atTop := Real.tendsto_exp_atTop
  have l3 t (_ : t ∈ Ioi (-log x)) : HasDerivWithinAt rexp (rexp t) (Ioi t) t :=
    (Real.hasDerivAt_exp t).hasDerivWithinAt
  have l4 : ContinuousOn Ψ (rexp '' Ioi (-Real.log x)) := by fun_prop
  have l5 : IntegrableOn Ψ (rexp '' Ici (-Real.log x)) volume :=
    (l0.integrable_of_hasCompactSupport hsupp).integrableOn
  have l6 : IntegrableOn (fun x ↦ rexp x • (Ψ ∘ rexp) x) (Ici (-Real.log x)) volume := by
    refine (Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_).integrableOn
    change HasCompactSupport (rexp • (Ψ ∘ rexp))
    exact (comp_exp_support hsupp hplus).smul_left
  have := MeasureTheory.integral_deriv_smul_comp_Ioi l1 l2 l3 l4 l5 l6
  simpa [Real.exp_neg, Real.exp_log hx] using this

theorem wiener_ikehara_smooth_sub (h1 : Integrable Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Ioi 0) :
    Tendsto (fun x ↦ (↑A * ∫ (y : ℝ) in Ioi x⁻¹, Ψ y) - ↑A * ∫ (y : ℝ) in Ioi 0, Ψ y)
      atTop (𝓝 0) := by

  obtain ⟨ε, hε, hh⟩ := Metric.eventually_nhds_iff.mp <| comp_exp_support0 hplus
  apply tendsto_nhds_of_eventually_eq ; filter_upwards [eventually_gt_atTop ε⁻¹] with x hxε

  have l1 : Integrable (indicator (Ioi x⁻¹) (fun x : ℝ => Ψ x)) := h1.indicator measurableSet_Ioi
  have l2 : Integrable (indicator (Ioi 0) (fun x : ℝ => Ψ x)) := h1.indicator measurableSet_Ioi

  simp_rw [← MeasureTheory.integral_indicator measurableSet_Ioi, ← mul_sub, ← integral_sub l1 l2]
  simp only [mul_eq_zero, ofReal_eq_zero]
  right
  apply MeasureTheory.integral_eq_zero_of_ae
  apply Eventually.of_forall
  intro t
  simp only [Pi.zero_apply]

  have hε' : 0 < ε⁻¹ := by positivity
  have hx : 0 < x := by linarith
  have hx' : 0 < x⁻¹ := by positivity
  have hεx : x⁻¹ < ε := (inv_lt_comm₀ hε hx).mp hxε

  have l3 : Ioi 0 = Ioc 0 x⁻¹ ∪ Ioi x⁻¹ := by
    ext t ; simp only [mem_Ioi, mem_union, mem_Ioc] ; constructor <;> intro h
    · simp [h, le_or_gt]
    · cases h with
      | inl h => exact h.1
      | inr h => exact hx'.trans h
  have l4 : Disjoint (Ioc 0 x⁻¹) (Ioi x⁻¹) := by simp
  have l5 := Set.indicator_union_of_disjoint l4 Ψ
  rw [l3, l5]
  simp only
  rw [add_comm, sub_add_cancel_left]
  by_cases ht : t ∈ Ioc 0 x⁻¹
  · simp only [ht, indicator_of_mem, neg_eq_zero]
    apply hh ; simp only [mem_Ioc, dist_zero_right, norm_eq_abs] at ht ⊢
    apply hεx.trans_le'
    rw [abs_le] ; constructor <;> linarith
  simp [ht]



lemma wiener_ikehara_smooth (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hsmooth : ContDiff ℝ ∞ Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * Ψ (n / x)) / x - A * ∫ y in Set.Ioi 0, Ψ y)
      atTop (𝓝 0) := by

  let h (x : ℝ) : ℂ := rexp (2 * π * x) * Ψ (exp (2 * π * x))
  have h1 : ContDiff ℝ ∞ h := by
    have : ContDiff ℝ ∞ (fun x : ℝ => (rexp (2 * π * x))) := (contDiff_const.mul contDiff_id).exp
    exact (contDiff_ofReal.comp this).mul (hsmooth.comp this)
  have h2 : HasCompactSupport h := by
    have : 2 * π ≠ 0 := by simp [pi_ne_zero]
    simpa using! (comp_exp_support hsupp hplus).comp_smul this |>.mul_left
  obtain ⟨g, hg⟩ := fourier_surjection_on_schwartz (toSchwartz h h1 h2)

  have l1 {y} (hy : 0 < y) : y * Ψ y = 𝓕 g (1 / (2 * π) * Real.log y) := by
    simp only [one_div, mul_inv_rev, hg, toSchwartz, ofReal_exp, ofReal_mul, ofReal_ofNat,
      toSchwartz_apply, ofReal_inv, h]
    field_simp
    norm_cast
    rw [Real.exp_log hy]

  have key := limiting_cor_schwartz g hf hcheby hG hG'

  have l2 : ∀ᶠ x in atTop, ∑' (n : ℕ), f n / ↑n * 𝓕 g (1 / (2 * π) * Real.log (↑n / x)) =
      ∑' (n : ℕ), f n * Ψ (↑n / x) / x := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    congr ; ext n
    by_cases hn : n = 0
    · simp [hn, (comp_exp_support0 hplus).self_of_nhds]
    rw [← l1 (by positivity)]
    have : (n : ℂ) ≠ 0 := by simpa using hn
    have : (x : ℂ) ≠ 0 := by simpa using hx.ne.symm
    simp only [ofReal_div, ofReal_natCast]
    field_simp

  have l3 : ∀ᶠ x in atTop, ↑A * ∫ (u : ℝ) in Ici (-Real.log x), 𝓕 g (u / (2 * π)) =
      ↑A * ∫ (y : ℝ) in Ioi x⁻¹, Ψ y := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    congr 1
    simp only [hg, toSchwartz, ofReal_exp, ofReal_mul, ofReal_ofNat, toSchwartz_apply,
      ofReal_div, h]
    norm_cast ; field_simp; norm_cast
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
    exact wiener_ikehara_smooth_aux hsmooth.continuous hsupp hplus x hx

  have l4 : Tendsto (fun x => (↑A * ∫ (y : ℝ) in Ioi x⁻¹, Ψ y) - ↑A * ∫ (y : ℝ) in Ioi 0, Ψ y)
      atTop (𝓝 0) := by
    exact wiener_ikehara_smooth_sub (hsmooth.continuous.integrable_of_hasCompactSupport hsupp) hplus

  simpa [tsum_div_const] using (key.congr' <| EventuallyEq.sub l2 l3) |>.add l4



lemma wiener_ikehara_smooth' (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hsmooth : ContDiff ℝ ∞ Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * Ψ (n / x)) / x) atTop (nhds (A * ∫ y in Set.Ioi 0, Ψ y)) :=
  tendsto_sub_nhds_zero_iff.mp <| wiener_ikehara_smooth hf hcheby hG hG' hsmooth hsupp hplus

local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩

theorem set_integral_ofReal {f : ℝ → ℝ} {s : Set ℝ} : ∫ x in s, (f x : ℂ) = ∫ x in s, f x :=
  integral_ofReal

lemma wiener_ikehara_smooth_real {f : ℕ → ℝ} {Ψ : ℝ → ℝ}
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hsmooth : ContDiff ℝ ∞ Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * Ψ (n / x)) / x) atTop (nhds (A * ∫ y in Set.Ioi 0, Ψ y)) := by

  let Ψ' := ofReal ∘ Ψ
  have l1 : ContDiff ℝ ∞ Ψ' := contDiff_ofReal.comp hsmooth
  have l2 : HasCompactSupport Ψ' := hsupp.comp_left rfl
  have l3 : closure (Function.support Ψ') ⊆ Ioi 0 := by rwa [Function.support_comp_eq] ; simp
  have key := (continuous_re.tendsto _).comp
    (@wiener_ikehara_smooth' A Ψ G f hf hcheby hG hG' l1 l2 l3)
  simp at key ; norm_cast at key

lemma interval_approx_inf (ha : 0 < a) (hab : a < b) :
    ∀ᶠ ε in 𝓝[>] 0, ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      closure (Function.support ψ) ⊆ Set.Ioi 0 ∧
        ψ ≤ indicator (Ico a b) 1 ∧ b - a - ε ≤ ∫ y in Ioi 0, ψ y := by

  have l1 : Iio ((b - a) / 3) ∈ 𝓝[>] 0 := nhdsWithin_le_nhds <| Iio_mem_nhds <| by
    rw [← sub_pos] at hab
    positivity
  filter_upwards [self_mem_nhdsWithin, l1] with ε (hε : 0 < ε) (hε' : ε < (b - a) / 3)
  have l2 : a < a + ε / 2 := by simp [hε]
  have l3 : b - ε / 2 < b := by simp [hε]
  obtain ⟨ψ, h1, h2, h3, h4, h5⟩ := smooth_urysohn_support_Ioo l2 l3
  refine ⟨ψ, h1, h2, ?_, ?_, ?_⟩
  · simp [h5, hab.ne, Icc_subset_Ioi_iff hab.le, ha]
  · exact h4.trans <| indicator_le_indicator_of_subset Ioo_subset_Ico_self (by simp)
  · have l4 : 0 ≤ b - a - ε := by linarith
    have l5 : Icc (a + ε / 2) (b - ε / 2) ⊆ Ioi 0 := by
      intro t ht
      simp only [mem_Icc, mem_Ioi] at ht ⊢
      exact ha.trans <| l2.trans_le <| ht.1
    have l6 : Icc (a + ε / 2) (b - ε / 2) ∩ Ioi 0 = Icc (a + ε / 2) (b - ε / 2) :=
      inter_eq_left.mpr l5
    have l7 : ∫ y in Ioi 0, indicator (Icc (a + ε / 2) (b - ε / 2)) 1 y = b - a - ε := by
      simp only [measurableSet_Icc, integral_indicator_one, measureReal_restrict_apply, l6,
        volume_real_Icc]
      convert max_eq_left l4 using 1 ; ring_nf
    have l8 : IntegrableOn ψ (Ioi 0) volume :=
      (h1.continuous.integrable_of_hasCompactSupport h2).integrableOn
    rw [← l7] ; apply setIntegral_mono ?_ l8 h3
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Icc]
    apply IntegrableOn.mono ?_ subset_rfl Measure.restrict_le_self
    apply integrableOn_const <;>
    simp

lemma interval_approx_sup (ha : 0 < a) (hab : a < b) :
    ∀ᶠ ε in 𝓝[>] 0, ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      closure (Function.support ψ) ⊆ Set.Ioi 0 ∧
        indicator (Ico a b) 1 ≤ ψ ∧ ∫ y in Ioi 0, ψ y ≤ b - a + ε := by

  have l1 : Iio (a / 2) ∈ 𝓝[>] 0 := nhdsWithin_le_nhds <| Iio_mem_nhds (by linarith)
  filter_upwards [self_mem_nhdsWithin, l1] with ε (hε : 0 < ε) (hε' : ε < a / 2)
  have l2 : a - ε / 2 < a := by linarith
  have l3 : b < b + ε / 2 := by linarith
  obtain ⟨ψ, h1, h2, h3, h4, h5⟩ := smooth_urysohn_support_Ioo l2 l3
  refine ⟨ψ, h1, h2, ?_, ?_, ?_⟩
  · have l4 : a - ε / 2 < b + ε / 2 := by linarith
    have l5 : ε / 2 < a := by linarith
    simp [h5, l4.ne, Icc_subset_Ioi_iff l4.le, l5]
  · apply le_trans ?_ h3
    apply indicator_le_indicator_of_subset Ico_subset_Icc_self (by simp)
  · have l4 : 0 ≤ b - a + ε := by linarith
    have l5 : Ioo (a - ε / 2) (b + ε / 2) ⊆ Ioi 0 := by intro t ht ; simp at ht ⊢ ; linarith
    have l6 : Ioo (a - ε / 2) (b + ε / 2) ∩ Ioi 0 = Ioo (a - ε / 2) (b + ε / 2) := inter_eq_left.mpr l5
    have l7 : ∫ y in Ioi 0, indicator (Ioo (a - ε / 2) (b + ε / 2)) 1 y = b - a + ε := by
      simp only [measurableSet_Ioo, integral_indicator_one, measureReal_restrict_apply, l6,
        volume_real_Ioo]
      convert max_eq_left l4 using 1 ; ring_nf
    have l8 : IntegrableOn ψ (Ioi 0) volume := (h1.continuous.integrable_of_hasCompactSupport h2).integrableOn
    rw [← l7]
    refine setIntegral_mono l8 ?_ h4
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Ioo]
    apply IntegrableOn.mono ?_ subset_rfl Measure.restrict_le_self
    apply integrableOn_const <;>
    simp

lemma WI_summable {f : ℕ → ℝ} {g : ℝ → ℝ} (hg : HasCompactSupport g) (hx : 0 < x) :
    Summable (fun n => f n * g (n / x)) := by
  obtain ⟨M, hM⟩ := hg.bddAbove.mono subset_closure
  apply summable_of_hasFiniteSupport
  unfold Function.HasFiniteSupport
  simp only [Function.support_mul] ; apply Finite.inter_of_right ; rw [finite_iff_bddAbove]
  exact ⟨Nat.ceil (M * x), fun i hi => by simpa using Nat.ceil_mono ((div_le_iff₀ hx).mp (hM hi))⟩

lemma WI_sum_le {f : ℕ → ℝ} {g₁ g₂ : ℝ → ℝ} (hf : 0 ≤ f) (hg : g₁ ≤ g₂) (hx : 0 < x)
    (hg₁ : HasCompactSupport g₁) (hg₂ : HasCompactSupport g₂) :
    (∑' n, f n * g₁ (n / x)) / x ≤ (∑' n, f n * g₂ (n / x)) / x := by
  apply div_le_div_of_nonneg_right ?_ hx.le
  exact Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left (hg _) (hf _))
    (WI_summable hg₁ hx) (WI_summable hg₂ hx)

lemma WI_sum_Iab_le {f : ℕ → ℝ} (hpos : 0 ≤ f) {C : ℝ} (hcheby : chebyWith C f) (hb : 0 < b) (hxb : 2 / b < x) :
    (∑' n, f n * indicator (Ico a b) 1 (n / x)) / x ≤ C * 2 * b := by
  have hb' : 0 < 2 / b := by positivity
  have hx : 0 < x := by linarith
  have hxb' : 2 < x * b := (div_lt_iff₀ hb).mp hxb
  have l1 (i : ℕ) (hi : i ∉ Finset.range ⌈b * x⌉₊) : f i * indicator (Ico a b) 1 (i / x) = 0 := by
    simp_all [le_div_iff₀ hx]
  have l2 (i : ℕ) (_ : i ∈ Finset.range ⌈b * x⌉₊) : f i * indicator (Ico a b) 1 (i / x) ≤ |f i| := by
    rw [abs_eq_self.mpr (hpos _)]
    convert_to _ ≤ f i * 1
    · ring
    apply mul_le_mul_of_nonneg_left ?_ (hpos _)
    by_cases hi : (i / x) ∈ (Ico a b) <;> simp [hi]
  rw [tsum_eq_sum l1, div_le_iff₀ hx, mul_assoc, mul_assoc]
  apply Finset.sum_le_sum l2 |>.trans
  have := hcheby ⌈b * x⌉₊ ; simp only [norm_real, norm_eq_abs] at this ; apply this.trans
  have : 0 ≤ C := by have := hcheby 1 ; simp only [cumsum, Finset.range_one, norm_real,
    Finset.sum_singleton, Nat.cast_one, mul_one] at this ; exact (abs_nonneg _).trans this
  refine mul_le_mul_of_nonneg_left ?_ this
  apply (Nat.ceil_lt_add_one (by positivity)).le.trans
  linarith

lemma WI_sum_Iab_le' {f : ℕ → ℝ} (hpos : 0 ≤ f) {C : ℝ} (hcheby : chebyWith C f) (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, (∑' n, f n * indicator (Ico a b) 1 (n / x)) / x ≤ C * 2 * b := by
  filter_upwards [eventually_gt_atTop (2 / b)] with x hx using WI_sum_Iab_le hpos hcheby hb hx

lemma le_of_eventually_nhdsWithin {a b : ℝ} (h : ∀ᶠ c in 𝓝[>] b, a ≤ c) : a ≤ b := by
  apply le_of_forall_gt ; intro d hd
  have key : ∀ᶠ c in 𝓝[>] b, c < d := by
    apply eventually_of_mem (U := Iio d) ?_ (fun x hx => hx)
    rw [mem_nhdsWithin]
    refine ⟨Iio d, isOpen_Iio, hd, inter_subset_left⟩
  obtain ⟨x, h1, h2⟩ := (h.and key).exists
  linarith

lemma ge_of_eventually_nhdsWithin {a b : ℝ} (h : ∀ᶠ c in 𝓝[<] b, c ≤ a) : b ≤ a := by
  apply le_of_forall_lt ; intro d hd
  have key : ∀ᶠ c in 𝓝[<] b, c > d := by
    apply eventually_of_mem (U := Ioi d) ?_ (fun x hx => hx)
    rw [mem_nhdsWithin]
    refine ⟨Ioi d, isOpen_Ioi, hd, inter_subset_left⟩
  obtain ⟨x, h1, h2⟩ := (h.and key).exists
  linarith

lemma WI_tendsto_aux (a b : ℝ) {A : ℝ} (hA : 0 < A) :
    Tendsto (fun c => c / A - (b - a)) (𝓝[>] (A * (b - a))) (𝓝[>] 0) := by
  rw [Metric.tendsto_nhdsWithin_nhdsWithin]
  intro ε hε
  refine ⟨A * ε, by positivity, ?_⟩
  intro x hx1 hx2
  constructor
  · simpa [lt_div_iff₀' hA]
  · simp only [Real.dist_eq, dist_zero_right, Real.norm_eq_abs] at hx2 ⊢
    have : |x / A - (b - a)| = |x - A * (b - a)| / A := by
      rw [← abs_eq_self.mpr hA.le, ← abs_div, abs_eq_self.mpr hA.le] ; congr ; field_simp
    rwa [this, div_lt_iff₀' hA]

lemma WI_tendsto_aux' (a b : ℝ) {A : ℝ} (hA : 0 < A) :
    Tendsto (fun c => (b - a) - c / A) (𝓝[<] (A * (b - a))) (𝓝[>] 0) := by
  rw [Metric.tendsto_nhdsWithin_nhdsWithin]
  intro ε hε
  refine ⟨A * ε, by positivity, ?_⟩
  intro x hx1 hx2
  constructor
  · simpa [div_lt_iff₀' hA]
  · simp only [Real.dist_eq, dist_zero_right, norm_eq_abs] at hx2 ⊢
    have : |(b - a) - x / A| = |A * (b - a) - x| / A := by
      rw [← abs_eq_self.mpr hA.le, ← abs_div, abs_eq_self.mpr hA.le] ; congr ; field_simp
    rwa [this, div_lt_iff₀' hA, ← neg_sub, abs_neg]

theorem residue_nonneg {f : ℕ → ℝ} (hpos : 0 ≤ f)
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm (fun n ↦ ↑(f n)) σ')) (hcheby : cheby fun n ↦ ↑(f n))
    (hG : ContinuousOn G {s | 1 ≤ s.re}) (hG' : EqOn G (fun s ↦ LSeries (fun n ↦ ↑(f n)) s - ↑A / (s - 1)) {s | 1 < s.re}) : 0 ≤ A := by
  let S (g : ℝ → ℝ) (x : ℝ) := (∑' n, f n * g (n / x)) / x
  have hSnonneg {g : ℝ → ℝ} (hg : 0 ≤ g) : ∀ᶠ x : ℝ in atTop, 0 ≤ S g x := by
    filter_upwards [eventually_ge_atTop 0] with x hx
    exact div_nonneg (tsum_nonneg (fun i => mul_nonneg (hpos _) (hg _))) hx
  obtain ⟨ε, ψ, h1, h2, h3, h4, -⟩ := (interval_approx_sup zero_lt_one one_lt_two).exists
  have key := @wiener_ikehara_smooth_real A G f ψ hf hcheby hG hG' h1 h2 h3
  have l2 : 0 ≤ ψ := by apply le_trans _ h4 ; apply indicator_nonneg ; simp
  have l1 : ∀ᶠ x in atTop, 0 ≤ S ψ x := hSnonneg l2
  have l3 : 0 ≤ A * ∫ (y : ℝ) in Ioi 0, ψ y := ge_of_tendsto key l1
  have l4 : 0 < ∫ (y : ℝ) in Ioi 0, ψ y := by
    have r1 : 0 ≤ᵐ[Measure.restrict volume (Ioi 0)] ψ := Eventually.of_forall l2
    have r2 : IntegrableOn (fun y ↦ ψ y) (Ioi 0) volume :=
      (h1.continuous.integrable_of_hasCompactSupport h2).integrableOn
    have r3 : Ico 1 2 ⊆ Function.support ψ := by intro x hx ; have := h4 x ; simp [hx] at this ⊢ ; linarith
    have r4 : Ico 1 2 ⊆ Function.support ψ ∩ Ioi 0 := by
      simp only [subset_inter_iff, r3, true_and] ; apply Ico_subset_Icc_self.trans ; rw [Icc_subset_Ioi_iff] <;> linarith
    have r5 : 1 ≤ volume ((Function.support fun y ↦ ψ y) ∩ Ioi 0) := by convert! volume.mono r4 ; norm_num
    simpa [setIntegral_pos_iff_support_of_nonneg_ae r1 r2] using! zero_lt_one.trans_le r5
  have := div_nonneg l3 l4.le ; field_simp at this ; exact this



lemma WienerIkeharaInterval {f : ℕ → ℝ} (hpos : 0 ≤ f) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) (ha : 0 < a) (hb : a ≤ b) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * (indicator (Ico a b) 1 (n / x))) / x) atTop (nhds (A * (b - a))) := by

  -- Take care of the trivial case `a = b`
  by_cases hab : a = b
  · simp [hab]
  replace hb : a < b := lt_of_le_of_ne hb hab ; clear hab

  -- Notation to make the proof more readable
  let S (g : ℝ → ℝ) (x : ℝ) :=  (∑' n, f n * g (n / x)) / x
  have hSnonneg {g : ℝ → ℝ} (hg : 0 ≤ g) : ∀ᶠ x : ℝ in atTop, 0 ≤ S g x := by
    filter_upwards [eventually_ge_atTop 0] with x hx
    refine div_nonneg ?_ hx
    refine tsum_nonneg (fun i => mul_nonneg (hpos _) (hg _))
  have hA : 0 ≤ A := residue_nonneg hpos hf hcheby hG hG'

  -- A few facts about the indicator function of `Icc a b`
  let Iab : ℝ → ℝ := indicator (Ico a b) 1
  change Tendsto (S Iab) atTop (𝓝 (A * (b - a)))
  have hIab : HasCompactSupport Iab := by simpa [Iab, HasCompactSupport, tsupport, hb.ne] using isCompact_Icc
  have Iab_nonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ S Iab x := hSnonneg (indicator_nonneg (by simp))
  have Iab2 : IsBoundedUnder (· ≤ ·) atTop (S Iab) := by
    obtain ⟨C, hC⟩ := hcheby ; exact ⟨C * 2 * b, WI_sum_Iab_le' hpos hC (by linarith)⟩
  have Iab3 : IsBoundedUnder (· ≥ ·) atTop (S Iab) := ⟨0, Iab_nonneg⟩
  have Iab0 : IsCoboundedUnder (· ≥ ·) atTop (S Iab) := Iab2.isCoboundedUnder_ge
  have Iab1 : IsCoboundedUnder (· ≤ ·) atTop (S Iab) := Iab3.isCoboundedUnder_le

  -- Bound from above by a smooth function
  have sup_le : limsup (S Iab) atTop ≤ A * (b - a) := by
    have l_sup : ∀ᶠ ε in 𝓝[>] 0, limsup (S Iab) atTop ≤ A * (b - a + ε) := by
      filter_upwards [interval_approx_sup ha hb] with ε ⟨ψ, h1, h2, h3, h4, h6⟩
      have l1 : Tendsto (S ψ) atTop _ := wiener_ikehara_smooth_real hf hcheby hG hG' h1 h2 h3
      have l6 : S Iab ≤ᶠ[atTop] S ψ := by
        filter_upwards [eventually_gt_atTop 0] with x hx using WI_sum_le hpos h4 hx hIab h2
      have l5 : IsBoundedUnder (· ≤ ·) atTop (S ψ) := l1.isBoundedUnder_le
      have l3 : limsup (S Iab) atTop ≤ limsup (S ψ) atTop := limsup_le_limsup l6 Iab1 l5
      apply l3.trans ; rw [l1.limsup_eq] ; gcongr
    obtain rfl | h := eq_or_ne A 0
    · simpa using l_sup
    apply le_of_eventually_nhdsWithin
    have key : 0 < A := lt_of_le_of_ne hA h.symm
    filter_upwards [WI_tendsto_aux a b key l_sup] with x hx
    simpa [mul_div_cancel₀ _ h] using hx

  -- Bound from below by a smooth function
  have le_inf : A * (b - a) ≤ liminf (S Iab) atTop := by
    have l_inf : ∀ᶠ ε in 𝓝[>] 0, A * (b - a - ε) ≤ liminf (S Iab) atTop := by
      filter_upwards [interval_approx_inf ha hb] with ε ⟨ψ, h1, h2, h3, h5, h6⟩
      have l1 : Tendsto (S ψ) atTop _ := wiener_ikehara_smooth_real hf hcheby hG hG' h1 h2 h3
      have l2 : S ψ ≤ᶠ[atTop] S Iab := by
        filter_upwards [eventually_gt_atTop 0] with x hx using WI_sum_le hpos h5 hx h2 hIab
      have l4 : IsBoundedUnder (· ≥ ·) atTop (S ψ) := l1.isBoundedUnder_ge
      have l3 : liminf (S ψ) atTop ≤ liminf (S Iab) atTop := liminf_le_liminf l2 l4 Iab0
      apply le_trans ?_ l3 ; rw [l1.liminf_eq] ; gcongr
    obtain rfl | h := eq_or_ne A 0
    · simpa using l_inf
    apply ge_of_eventually_nhdsWithin
    have key : 0 < A := lt_of_le_of_ne hA h.symm
    filter_upwards [WI_tendsto_aux' a b key l_inf] with x hx
    simpa [mul_div_cancel₀ _ h] using hx

  -- Combine the two bounds
  have : liminf (S Iab) atTop ≤ limsup (S Iab) atTop := liminf_le_limsup Iab2 Iab3
  refine tendsto_of_liminf_eq_limsup ?_ ?_ Iab2 Iab3 <;> linarith



lemma le_floor_mul_iff (hb : 0 ≤ b) (hx : 0 < x) : n ≤ ⌊b * x⌋₊ ↔ n / x ≤ b := by
  rw [div_le_iff₀ hx, Nat.le_floor_iff] ; positivity

lemma lt_ceil_mul_iff (hx : 0 < x) : n < ⌈b * x⌉₊ ↔ n / x < b := by
  rw [div_lt_iff₀ hx, Nat.lt_ceil]

lemma ceil_mul_le_iff (hx : 0 < x) : ⌈a * x⌉₊ ≤ n ↔ a ≤ n / x := by
  rw [le_div_iff₀ hx, Nat.ceil_le]

lemma mem_Icc_iff_div (hb : 0 ≤ b) (hx : 0 < x) : n ∈ Finset.Icc ⌈a * x⌉₊ ⌊b * x⌋₊ ↔ n / x ∈ Icc a b := by
  rw [Finset.mem_Icc, mem_Icc, ceil_mul_le_iff hx, le_floor_mul_iff hb hx]

lemma mem_Ico_iff_div (hx : 0 < x) : n ∈ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊ ↔ n / x ∈ Ico a b := by
  rw [Finset.mem_Ico, mem_Ico, ceil_mul_le_iff hx, lt_ceil_mul_iff hx]

lemma tsum_indicator {f : ℕ → ℝ} (hx : 0 < x) :
    ∑' n, f n * (indicator (Ico a b) 1 (n / x)) = ∑ n ∈ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊, f n := by
  have l1 : ∀ n ∉ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊, f n * indicator (Ico a b) 1 (↑n / x) = 0 := by
    simp [mem_Ico_iff_div hx] ; tauto
  rw [tsum_eq_sum l1] ; apply Finset.sum_congr rfl ; simp only [mem_Ico_iff_div hx] ; intro n hn ; simp [hn]

lemma WienerIkeharaInterval_discrete {f : ℕ → ℝ} (hpos : 0 ≤ f) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) (ha : 0 < a) (hb : a ≤ b) :
    Tendsto (fun x : ℝ ↦ (∑ n ∈ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊, f n) / x) atTop (nhds (A * (b - a))) := by
  apply (WienerIkeharaInterval hpos hf hcheby hG hG' ha hb).congr'
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [tsum_indicator hx]

lemma WienerIkeharaInterval_discrete' {f : ℕ → ℝ} (hpos : 0 ≤ f) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) (ha : 0 < a) (hb : a ≤ b) :
    Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.Ico ⌈a * N⌉₊ ⌈b * N⌉₊, f n) / N) atTop (nhds (A * (b - a))) :=
  WienerIkeharaInterval_discrete hpos hf hcheby hG hG' ha hb |>.comp tendsto_natCast_atTop_atTop

-- TODO with `Ico`



/-- A version of the *Wiener-Ikehara Tauberian Theorem*: If `f` is a nonnegative arithmetic
function whose L-series has a simple pole at `s = 1` with residue `A` and otherwise extends
continuously to the closed half-plane `re s ≥ 1`, then `∑ n < N, f n` is asymptotic to `A*N`. -/

lemma tendsto_mul_ceil_div :
    Tendsto (fun (p : ℝ × ℕ) => ⌈p.1 * p.2⌉₊ / (p.2 : ℝ)) (𝓝[>] 0 ×ˢ atTop) (𝓝 0) := by
  rw [Metric.tendsto_nhds] ; intro δ hδ
  have l1 : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioo 0 (δ / 2) := inter_mem_nhdsWithin _ (Iio_mem_nhds (by positivity))
  have l2 : ∀ᶠ N : ℕ in atTop, 1 ≤ δ / 2 * N := by
    apply Tendsto.eventually_ge_atTop
    exact tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  filter_upwards [l1.prod_mk l2] with (ε, N) ⟨⟨hε, h1⟩, h2⟩ ; dsimp only at *
  have l3 : 0 < (N : ℝ) := by
    simp only [Nat.cast_pos, Nat.pos_iff_ne_zero] ; rintro rfl ; simp [zero_lt_one.not_ge] at h2
  have l5 : 0 ≤ ε * ↑N := by positivity
  have l6 : ε * N ≤ δ / 2 * N := mul_le_mul h1.le le_rfl (by positivity) (by positivity)
  simp only [dist_zero_right, norm_div, RCLike.norm_natCast, div_lt_iff₀ l3, gt_iff_lt]
  convert (Nat.ceil_lt_add_one l5).trans_le (add_le_add l6 h2) using 1 ; ring

noncomputable def S (f : ℕ → 𝕜) (ε : ℝ) (N : ℕ) : 𝕜 := (∑ n ∈ Finset.Ico ⌈ε * N⌉₊ N, f n) / N

lemma S_sub_S {f : ℕ → 𝕜} {ε : ℝ} {N : ℕ} (hε : ε ≤ 1) : S f 0 N - S f ε N = cumsum f ⌈ε * N⌉₊ / N := by
  have hceilN : ⌈ε * N⌉₊ ≤ N := by
    simp only [Nat.ceil_le]
    exact mul_le_of_le_one_left N.cast_nonneg hε
  have r1 : Finset.range N = Finset.range ⌈ε * N⌉₊ ∪ Finset.Ico ⌈ε * N⌉₊ N := by
    ext n
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    omega
  have r2 : Disjoint (Finset.range ⌈ε * N⌉₊) (Finset.Ico ⌈ε * N⌉₊ N) := by
    rw [Finset.range_eq_Ico] ; apply Finset.Ico_disjoint_Ico_consecutive
  simp [S, r1, Finset.sum_union r2, cumsum, add_div]

lemma tendsto_S_S_zero {f : ℕ → ℝ} (hpos : 0 ≤ f) (hcheby : cheby f) :
    TendstoUniformlyOnFilter (S f) (S f 0) (𝓝[>] 0) atTop := by
  rw [Metric.tendstoUniformlyOnFilter_iff] ; intro δ hδ
  obtain ⟨C, hC⟩ := hcheby
  have l1 : ∀ᶠ (p : ℝ × ℕ) in 𝓝[>] 0 ×ˢ atTop, C * ⌈p.1 * p.2⌉₊ / p.2 < δ := by
    have r1 := tendsto_mul_ceil_div.const_mul C
    simp only [mul_div_assoc', mul_zero] at r1 ; exact r1 (Iio_mem_nhds hδ)
  have : Ioc 0 1 ∈ 𝓝[>] (0 : ℝ) := inter_mem_nhdsWithin _ (Iic_mem_nhds zero_lt_one)
  filter_upwards [l1, Eventually.prod_inl this _] with (ε, N) h1 h2
  have l2 : ‖cumsum f ⌈ε * ↑N⌉₊ / ↑N‖ ≤ C * ⌈ε * N⌉₊ / N := by
    have r1 := hC ⌈ε * N⌉₊
    have r2 : 0 ≤ cumsum f ⌈ε * N⌉₊ := by apply cumsum_nonneg hpos
    simp only [norm_real, norm_of_nonneg (hpos _), norm_div,
      norm_of_nonneg r2, Real.norm_natCast] at r1 ⊢
    apply div_le_div_of_nonneg_right r1 (by positivity)
  simpa [← S_sub_S h2.2] using! l2.trans_lt h1

theorem WienerIkeharaTheorem' {f : ℕ → ℝ} (hpos : 0 ≤ f)
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun N => cumsum f N / N) atTop (𝓝 A) := by

  convert_to Tendsto (S f 0) atTop (𝓝 A) ; · ext N ; simp [S, cumsum]
  apply (tendsto_S_S_zero hpos hcheby).tendsto_of_eventually_tendsto
  · have L0 : Ioc 0 1 ∈ 𝓝[>] (0 : ℝ) := inter_mem_nhdsWithin _ (Iic_mem_nhds zero_lt_one)
    apply eventually_of_mem L0
    · intro ε hε
      simpa using! WienerIkeharaInterval_discrete' hpos hf hcheby hG hG' hε.1 hε.2
  · have : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    simpa using (this.const_sub 1).const_mul A

theorem vonMangoldt_cheby : cheby Λ := by
  use Real.log 4 + 4
  intro N
  by_cases! h : N = 0
  · simp [h, cumsum]
  simp only [cumsum, norm_real, norm_eq_abs]
  rw [Nat.range_eq_Icc_zero_sub_one _ h, (by simp : N - 1 = ⌊(N : ℝ) - 1⌋₊)]
  simp_rw [abs_of_nonneg vonMangoldt_nonneg]
  rw [← Chebyshev.psi_eq_sum_Icc]
  grw [Chebyshev.psi_le_const_mul_self <| sub_nonneg_of_le <| Nat.one_le_cast_iff_ne_zero.mpr h]
  gcongr
  linarith



-- Proof extracted from the `EulerProducts` project so we can adapt it to the
-- version of the Wiener-Ikehara theorem proved above (with the `cheby`
-- hypothesis)

theorem WeakPNT : Tendsto (fun N ↦ cumsum Λ N / N) atTop (𝓝 1) := by
  let F := vonMangoldt.LFunctionResidueClassAux (q := 1) 1
  have hnv := riemannZeta_ne_zero_of_one_le_re
  have l1 (n : ℕ) : 0 ≤ Λ n := vonMangoldt_nonneg
  have l2 s (hs : 1 < s.re) : F s = LSeries Λ s - 1 / (s - 1) := by
    have := vonMangoldt.eqOn_LFunctionResidueClassAux (q := 1) isUnit_one hs
    simp only [F, this, vonMangoldt.residueClass, Nat.totient_one, Nat.cast_one, inv_one, one_div, sub_left_inj]
    apply LSeries_congr
    intro n _
    simp only [ofReal_inj, indicator_apply_eq_self, mem_setOf_eq]
    exact fun hn ↦ absurd (Subsingleton.eq_one _) hn
  have l3 : ContinuousOn F {s | 1 ≤ s.re} := vonMangoldt.continuousOn_LFunctionResidueClassAux 1
  have l4 : cheby Λ := vonMangoldt_cheby
  have l5 (σ' : ℝ) (hσ' : 1 < σ') : Summable (nterm Λ σ') := by
    simpa only [← nterm_eq_norm_term] using (@ArithmeticFunction.LSeriesSummable_vonMangoldt σ' hσ').norm
  apply WienerIkeharaTheorem' l1 l5 l4 l3 l2

end PNTX_Wiener

-- Ported from PrimeNumberTheoremAnd: Consequences.lean (selected lemmas up to chebyshev_asymptotic), followed by the new proof of H1
section PNTX_Conseq

section PNTConseq
open ArithmeticFunction hiding log
open Nat hiding log
open Finset
open BigOperators Filter Real Classical Asymptotics MeasureTheory intervalIntegral
open scoped ArithmeticFunction.Moebius ArithmeticFunction.Omega Chebyshev

/-- If u ~ v and u-w = o(v) then w ~ v. -/
theorem Asymptotics.IsEquivalent.add_isLittleO'' {α : Type*} {β : Type*} [NormedAddCommGroup β]
    {u : α → β} {v : α → β} {w : α → β} {l : Filter α}
    (huv : Asymptotics.IsEquivalent l u v) (hwu : (u - w) =o[l] v) :
    Asymptotics.IsEquivalent l w v := by
  rw [← sub_sub_self u w]
  exact sub_isLittleO huv hwu

theorem WeakPNT' : Tendsto (fun N ↦ (∑ n ∈ Iic N, Λ n) / N) atTop (nhds 1) := by
  have : (fun N ↦ (∑ n ∈ Iic N, Λ n) / N) =
      (fun N ↦ (∑ n ∈ range N, Λ n)/N + Λ N / N) := by
    ext N
    have : N ∈ Iic N := mem_Iic.mpr (le_refl _)
    rw [← Finset.sum_erase_add _ _ this, ← Nat.Iio_eq_range, Iic_erase]
    exact add_div _ _ _

  rw [this, ← add_zero 1]
  apply Tendsto.add WeakPNT
  convert squeeze_zero (f := fun N ↦ Λ N / N) (g := fun N ↦ log N / N) (t₀ := atTop) ?_ ?_ ?_
  · intro N
    exact div_nonneg vonMangoldt_nonneg (cast_nonneg N)
  · intro N
    exact div_le_div_of_nonneg_right vonMangoldt_le_log (cast_nonneg N)
  have := Real.tendsto_pow_log_div_pow_atTop 1 1 Real.zero_lt_one
  simp only [rpow_one] at this
  exact Tendsto.comp this tendsto_natCast_atTop_atTop

/-- An alternate form of the Weak PNT. -/
theorem WeakPNT'' : ψ ~[atTop] (fun x ↦ x) := by
    rw [(by rfl : ψ = (fun x ↦ ψ x))]
    simp_rw [Chebyshev.psi_eq_sum_Icc]
    apply IsEquivalent.trans (v := fun x ↦ (⌊x⌋₊:ℝ))
    · rw [isEquivalent_iff_tendsto_one]
      · convert! Tendsto.comp WeakPNT' tendsto_nat_floor_atTop
        infer_instance
      rw [eventually_iff]
      simp only [ne_eq, cast_eq_zero, floor_eq_zero, not_lt, mem_atTop_sets,
        Set.mem_setOf_eq]
      use 1
      simp only [imp_self, implies_true]
    apply IsLittleO.isEquivalent
    rw [← isLittleO_neg_left]
    apply IsLittleO.of_bound
    intro ε hε
    simp only [Pi.sub_apply, neg_sub, norm_eq_abs, eventually_atTop]
    use ε⁻¹
    intro b hb
    have hb' : 0 ≤ b := le_of_lt (lt_of_lt_of_le (inv_pos_of_pos hε) hb)
    rw [abs_of_nonneg, abs_of_nonneg hb']
    · apply LE.le.trans _ ((inv_le_iff_one_le_mul₀' hε).mp hb)
      linarith [Nat.lt_floor_add_one b]
    rw [sub_nonneg]
    exact floor_le hb'

/-- `√x · log x = o(x)` as `x → ∞`. -/
lemma isLittleO_sqrt_mul_log : (fun x : ℝ ↦ x.sqrt * x.log) =o[atTop] _root_.id := by
  have : (fun x : ℝ ↦ x.sqrt * x.log) =o[atTop] fun x ↦ x := by
    refine (isLittleO_mul_iff_isLittleO_div ?_).mpr ?_
    · filter_upwards [eventually_gt_atTop 0] with x hx; exact (sqrt_ne_zero hx.le).mpr hx.ne'
    · convert! isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2) using 2 with x
      rw [div_sqrt, sqrt_eq_rpow]
  exact this

theorem chebyshev_asymptotic : θ ~[atTop] id := by
  refine WeakPNT''.add_isLittleO'' (IsBigO.trans_isLittleO (g := fun x ↦ 2 * x.sqrt * x.log) ?_ ?_)
  · rw [isBigO_iff']; refine ⟨1, one_pos, ?_⟩
    simp only [one_mul, eventually_atTop]
    exact ⟨2, fun x hx ↦ by
      rw [Pi.sub_apply, norm_eq_abs, norm_eq_abs, abs_of_nonneg (by bound : 0 ≤ 2 * √x * log x)]
      exact (abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi x))).symm ▸
        Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by linarith : 1 ≤ x)⟩
  · simpa only [mul_assoc] using! isLittleO_sqrt_mul_log.const_mul_left 2

end PNTConseq

section OMAH1

theorem OMA.PNT.exists_prime_of_theta_lt (n : ℕ) (y : ℝ)
    (h : Chebyshev.theta (n : ℝ) < Chebyshev.theta y) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ (p : ℝ) ≤ y := by
  by_contra hne
  push Not at hne
  apply absurd h
  apply not_lt.mpr
  unfold Chebyshev.theta
  rw [Nat.floor_natCast]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
    refine ⟨⟨hp.1.1, ?_⟩, hp.2⟩
    have hpy : (p : ℝ) ≤ y := (Nat.le_floor_iff' (Nat.pos_iff_ne_zero.mp hp.1.1)).1 hp.1.2
    by_contra hpn
    push Not at hpn
    have := hne p hp.2 hpn
    linarith
  · intro p _ _
    exact Real.log_natCast_nonneg p

theorem OMA.PNT.h1 : ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∃ p : ℕ, p.Prime ∧ n < p ∧ (p : ℝ) ≤ (1 + δ) * (n : ℝ) := by
  intro δ hδ
  have hlo := chebyshev_asymptotic.isLittleO
  have hεpos : 0 < δ / (2 * (2 + δ)) := by positivity
  have hε2 : δ / (2 * (2 + δ)) * (2 + δ) = δ / 2 := by
    field_simp
  have hb := hlo.bound hεpos
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.1 hb
  refine ⟨⌈X⌉₊ + 1, fun n hn => ?_⟩
  apply OMA.PNT.exists_prime_of_theta_lt
  have hn' : ((⌈X⌉₊ : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hceil := Nat.le_ceil X
  have hnX : X ≤ (n : ℝ) := by linarith
  have hn1 : (1 : ℝ) ≤ n := by
    have : 1 ≤ n := by omega
    exact_mod_cast this
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hnn : (n : ℝ) ≤ (1 + δ) * n := by nlinarith
  have hn2 : (0 : ℝ) ≤ (1 + δ) * n := by linarith
  have h1 := hX n hnX
  have h2 := hX ((1 + δ) * n) (le_trans hnX hnn)
  simp only [Pi.sub_apply, id_eq, Real.norm_eq_abs] at h1 h2
  rw [abs_of_nonneg hn0] at h1
  rw [abs_of_nonneg hn2] at h2
  have h1' := (abs_le.1 h1).2
  have h2' := (abs_le.1 h2).1
  have key : δ / (2 * (2 + δ)) * ((1 + δ) * n) + δ / (2 * (2 + δ)) * n = δ / 2 * n := by
    have : δ / (2 * (2 + δ)) * ((1 + δ) * n) + δ / (2 * (2 + δ)) * n
        = (δ / (2 * (2 + δ)) * (2 + δ)) * n := by ring
    rw [this, hε2]
  have hpos : 0 < δ / 2 * n := by positivity
  linarith

end OMAH1

end PNTX_Conseq

theorem OMA.solution : OMA.R_Erdos133_erdos_133_variants_asymptotic_R1.H2 :=
  Korsky133.h2_of_parts OMA.PNT.h1 (Korsky133.partB_of_partA Korsky133.partA_holds)
