import OMAStatements.S_oeis_a179269

/-!
# Proof of OEIS A179269

We prove that for every `n : ℕ`,
`{ps : List ℕ | valid 0 0 ps ∧ ps.sum = n}.ncard = {es : List ℕ | tetra es.length + degree es = n}.ncard`.

Proof outline:
We construct an explicit bijection between the two sets via second differences:
- `toEs prev gap (p :: ps) = (p - prev - gap - 1) :: toEs p (p - prev) ps`
- `fromEs prev gap (e :: es) = (prev + gap + e + 1) :: fromEs (prev + gap + e + 1) (gap + e + 1) es`
By structural induction on lists:
1. `valid prev gap (fromEs prev gap es)` always holds.
2. `toEs prev gap (fromEs prev gap es) = es`, and for `valid prev gap ps`,
   `fromEs prev gap (toEs prev gap ps) = ps`.
3. `(fromEs prev gap es).sum = es.length * prev + triangular es.length * gap + tetra es.length + degree es`.
Setting `prev = 0, gap = 0` shows `fromEs 0 0` is a bijection from
`{es | tetra es.length + degree es = n}` onto `{ps | valid 0 0 ps ∧ ps.sum = n}`, hence their
`Set.ncard` values are equal.
-/

namespace OMA.A179269Proof

open OMA.S_oeis_a179269

private def toEs (prev gap : ℕ) : List ℕ → List ℕ
  | [] => []
  | p :: ps => (p - prev - gap - 1) :: toEs p (p - prev) ps

private def fromEs (prev gap : ℕ) : List ℕ → List ℕ
  | [] => []
  | e :: es => (prev + gap + e + 1) :: fromEs (prev + gap + e + 1) (gap + e + 1) es

private lemma valid_fromEs (es : List ℕ) :
    ∀ prev gap : ℕ, valid prev gap (fromEs prev gap es) := by
  induction es with
  | nil => intro prev gap; trivial
  | cons e es ih =>
    intro prev gap
    simp only [fromEs, valid]
    refine ⟨by omega, ?_⟩
    have hsub : prev + gap + e + 1 - prev = gap + e + 1 := by omega
    rw [hsub]
    exact ih (prev + gap + e + 1) (gap + e + 1)

private lemma toEs_fromEs (es : List ℕ) :
    ∀ prev gap : ℕ, toEs prev gap (fromEs prev gap es) = es := by
  induction es with
  | nil => intro prev gap; rfl
  | cons e es ih =>
    intro prev gap
    simp only [fromEs, toEs]
    have h1 : prev + gap + e + 1 - prev - gap - 1 = e := by omega
    have h2 : prev + gap + e + 1 - prev = gap + e + 1 := by omega
    rw [h1, h2, ih]

private lemma fromEs_toEs (ps : List ℕ) :
    ∀ prev gap : ℕ, valid prev gap ps → fromEs prev gap (toEs prev gap ps) = ps := by
  induction ps with
  | nil => intro prev gap _; rfl
  | cons p ps ih =>
    intro prev gap hval
    simp only [valid] at hval
    obtain ⟨hlt, hrest⟩ := hval
    simp only [toEs, fromEs]
    have h1 : prev + gap + (p - prev - gap - 1) + 1 = p := by omega
    have h2 : gap + (p - prev - gap - 1) + 1 = p - prev := by omega
    rw [h1, h2, ih p (p - prev) hrest]

private lemma sum_fromEs (es : List ℕ) :
    ∀ prev gap : ℕ,
      (fromEs prev gap es).sum =
        es.length * prev + triangular es.length * gap + tetra es.length + degree es := by
  induction es with
  | nil =>
    intro prev gap
    simp [fromEs, triangular, tetra, degree]
  | cons e es ih =>
    intro prev gap
    simp only [fromEs, List.sum_cons, List.length_cons, degree, triangular, tetra]
    rw [ih (prev + gap + e + 1) (gap + e + 1)]
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
    omega

theorem result : type_of% @OMA.S_oeis_a179269.main := by
  intro n
  symm
  refine Set.ncard_congr (fun es _ => fromEs 0 0 es) ?_ ?_ ?_
  · intro es hes
    simp only [Set.mem_ofPred_eq] at hes ⊢
    refine ⟨valid_fromEs es 0 0, ?_⟩
    rw [sum_fromEs es 0 0]
    omega
  · intro e1 e2 _ _ h
    have h1 := congrArg (toEs 0 0) h
    rw [toEs_fromEs, toEs_fromEs] at h1
    exact h1
  · intro ps hps
    simp only [Set.mem_ofPred_eq] at hps
    refine ⟨toEs 0 0 ps, ?_, fromEs_toEs ps 0 0 hps.1⟩
    simp only [Set.mem_ofPred_eq]
    have hsum := sum_fromEs (toEs 0 0 ps) 0 0
    rw [fromEs_toEs ps 0 0 hps.1, hps.2] at hsum
    omega

end OMA.A179269Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a179269.main := OMA.A179269Proof.result
