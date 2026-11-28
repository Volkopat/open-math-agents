import OMAStatements.S_oeis_a215229
import Mathlib

/-!
Proof: count the words letter by letter. A prefix whose letters are exactly `0, ..., d - 1`
extends by one of its own `d` letters or by a fresh letter, and all `N - d` fresh letters give
the same count, because swapping two letters preserves the square-free test. This turns the
count into a polynomial in the alphabet size `N`, whose coefficients the kernel computes by
walking the 203 equality patterns of length 6.
-/

namespace OMA.P_oeis_a215229

section engine

variable (q : List ℕ → Bool)

/-- Completions of `u` by `r` letters below `N` that pass the test `q`. -/
def H (N : ℕ) (u : List ℕ) (r : ℕ) : ℕ :=
  ∑ v : Fin r → Fin N, if q (u ++ List.ofFn fun i => (v i : ℕ)) then 1 else 0

lemma H_zero (N : ℕ) (u : List ℕ) : H q N u 0 = if q u then 1 else 0 := by
  simp [H]

lemma H_succ (N : ℕ) (u : List ℕ) (r : ℕ) :
    H q N u (r + 1) = ∑ x : Fin N, H q N (u ++ [(x : ℕ)]) r := by
  unfold H
  rw [← (Fin.consEquiv fun _ => Fin N).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun v _ => ?_
  simp [Fin.consEquiv, List.ofFn_succ]

lemma swap_fin_val {N : ℕ} (x y : Fin N) (i : Fin N) :
    ((Equiv.swap x y i : Fin N) : ℕ) = Equiv.swap (x : ℕ) (y : ℕ) (i : ℕ) := by
  simp only [Equiv.swap_apply_def, Fin.ext_iff]
  split_ifs <;> rfl

lemma H_swap (hq : ∀ f : ℕ → ℕ, f.Injective → ∀ l, q (l.map f) = q l) (N : ℕ) (u : List ℕ)
    (r : ℕ) (x y : ℕ) (hx : x < N) (hy : y < N) :
    H q N (u.map (Equiv.swap x y)) r = H q N u r := by
  unfold H
  let σ : Equiv.Perm (Fin N) := Equiv.swap ⟨x, hx⟩ ⟨y, hy⟩
  rw [← (Equiv.arrowCongr (Equiv.refl (Fin r)) σ).sum_comp]
  refine Finset.sum_congr rfl fun v _ => ?_
  congr 1
  rw [← hq (Equiv.swap x y) (Equiv.injective _) (u ++ _)]
  simp only [List.map_append, List.map_ofFn]
  rw [show (List.ofFn fun i => ((Equiv.arrowCongr (Equiv.refl (Fin r)) σ v i : Fin N) : ℕ)) =
    List.ofFn (Equiv.swap x y ∘ fun i => (v i : ℕ)) from ?_]
  congr 1
  funext i
  simp only [Function.comp_apply, Equiv.arrowCongr_apply, Equiv.refl_symm, Equiv.coe_refl,
    Function.comp_id, σ, swap_fin_val, Equiv.swap_apply_self]

lemma H_fresh (hq : ∀ f : ℕ → ℕ, f.Injective → ∀ l, q (l.map f) = q l) (N : ℕ) (u : List ℕ)
    (r d x : ℕ) (hu : ∀ c ∈ u, c < d) (hdx : d ≤ x) (hx : x < N) :
    H q N (u ++ [x]) r = H q N (u ++ [d]) r := by
  have e : (u ++ [d]).map (Equiv.swap d x) = u ++ [x] := by
    rw [List.map_append, List.map_singleton, Equiv.swap_apply_left]
    congr 1
    conv_rhs => rw [← List.map_id u]
    apply List.map_congr_left
    intro c hc
    have := hu c hc
    exact Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
  rw [← e, H_swap q hq N _ r d x (by omega) hx]

lemma H_split (hq : ∀ f : ℕ → ℕ, f.Injective → ∀ l, q (l.map f) = q l) (N : ℕ) (u : List ℕ)
    (r d : ℕ) (hu : ∀ c ∈ u, c < d) (hd : d ≤ N) :
    H q N u (r + 1) = ∑ x ∈ Finset.range d, H q N (u ++ [x]) r + (N - d) * H q N (u ++ [d]) r := by
  rw [H_succ, Fin.sum_univ_eq_sum_range (fun x => H q N (u ++ [x]) r) N,
    ← Finset.sum_range_add_sum_Ico _ hd]
  congr 1
  rw [Finset.sum_congr rfl (g := fun _ => H q N (u ++ [d]) r) fun x hx => by
    rw [Finset.mem_Ico] at hx
    exact H_fresh q hq N u r d x hu hx.1 hx.2]
  rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]

end engine

/-! Polynomials as coefficient lists, lowest degree first. -/

def padd : List ℤ → List ℤ → List ℤ
  | [], p => p
  | a :: p, [] => a :: p
  | a :: p, b :: p' => (a + b) :: padd p p'

def ev : List ℤ → ℤ → ℤ
  | [], _ => 0
  | a :: p, x => a + x * ev p x

lemma ev_padd : ∀ (p p' : List ℤ) (x : ℤ), ev (padd p p') x = ev p x + ev p' x
  | [], p, x => by simp [padd, ev]
  | a :: p, [], x => by simp [padd, ev]
  | a :: p, b :: p', x => by
    simp only [padd, ev, ev_padd p p' x]
    ring

lemma ev_map_mul (c : ℤ) : ∀ (p : List ℤ) (x : ℤ), ev (p.map (c * ·)) x = c * ev p x
  | [], x => by simp [ev]
  | a :: p, x => by
    simp only [List.map_cons, ev, ev_map_mul c p x]
    ring

def mulXs (d : ℤ) (p : List ℤ) : List ℤ := padd (0 :: p) (p.map (-d * ·))

lemma ev_mulXs (d : ℤ) (p : List ℤ) (x : ℤ) : ev (mulXs d p) x = (x - d) * ev p x := by
  rw [mulXs, ev_padd, ev_map_mul, ev]
  ring

def psum (l : List (List ℤ)) : List ℤ := l.foldr padd []

lemma ev_psum (x : ℤ) : ∀ l : List (List ℤ), ev (psum l) x = (l.map (ev · x)).sum
  | [] => by simp [psum, ev]
  | p :: l => by
    simp only [psum, List.foldr_cons, List.map_cons, List.sum_cons] at *
    rw [ev_padd, ← ev_psum x l, psum]

lemma list_range_sum (g : ℕ → ℤ) : ∀ d : ℕ, ((List.range d).map g).sum = ∑ x ∈ Finset.range d, g x
  | 0 => by simp
  | d + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, list_range_sum g d,
      Finset.sum_range_succ]
    simp

section engine2

variable (q : List ℕ → Bool)

/-- The count as a polynomial in the alphabet size. -/
def Pc (u : List ℕ) (d : ℕ) : ℕ → List ℤ
  | 0 => if q u then [1] else []
  | r + 1 => padd (psum ((List.range d).map fun x => Pc (u ++ [x]) d r))
      (mulXs d (Pc (u ++ [d]) (d + 1) r))

theorem H_eq_ev (hq : ∀ f : ℕ → ℕ, f.Injective → ∀ l, q (l.map f) = q l) (N : ℕ) :
    ∀ (r : ℕ) (u : List ℕ) (d : ℕ), (∀ c ∈ u, c < d) → d ≤ N →
      (H q N u r : ℤ) = ev (Pc q u d r) N
  | 0, u, d, _, _ => by
    rw [H_zero, Pc]
    split_ifs <;> simp [ev]
  | r + 1, u, d, hu, hd => by
    rw [H_split q hq N u r d hu hd, Pc, ev_padd, ev_psum, ev_mulXs, List.map_map,
      list_range_sum, Nat.cast_add, Nat.cast_sum, Nat.cast_mul, Nat.cast_sub hd]
    congr 1
    · refine Finset.sum_congr rfl fun x hx => ?_
      rw [Finset.mem_range] at hx
      refine H_eq_ev hq N r (u ++ [x]) d ?_ hd
      intro c hc
      rw [List.mem_append, List.mem_singleton] at hc
      rcases hc with hc | rfl
      · exact hu c hc
      · exact hx
    · rcases hd.lt_or_eq with hd' | rfl
      · rw [H_eq_ev hq N r (u ++ [d]) (d + 1) ?_ hd']
        intro c hc
        rw [List.mem_append, List.mem_singleton] at hc
        rcases hc with hc | rfl
        · have := hu c hc
          omega
        · omega
      · simp

theorem card_eq_H (L N : ℕ) :
    Nat.card {w : List ℕ // w.length = L ∧ (∀ c ∈ w, c < N) ∧ q w = true} = H q N [] L := by
  have hb : Function.Bijective (fun v : {v : Fin L → Fin N // q (List.ofFn fun i => (v i : ℕ)) = true} =>
      (⟨List.ofFn fun i => (v.1 i : ℕ), by simp, by simp, v.2⟩ :
        {w : List ℕ // w.length = L ∧ (∀ c ∈ w, c < N) ∧ q w = true})) := by
    constructor
    · rintro ⟨v₁, h₁⟩ ⟨v₂, h₂⟩ h
      simp only [Subtype.mk.injEq] at h
      have := List.ofFn_injective h
      apply Subtype.ext
      funext i
      exact Fin.ext (congrFun this i)
    · rintro ⟨w, hl, hc, hw⟩
      refine ⟨⟨fun i => ⟨w[(i : ℕ)]'(by omega), hc _ (List.getElem_mem _)⟩, ?_⟩, ?_⟩
      · convert hw
        apply List.ext_getElem (by simp [hl])
        intro i h1 h2
        simp
      · apply Subtype.ext
        apply List.ext_getElem (by simp [hl])
        intro i h1 h2
        simp
  rw [← Nat.card_eq_of_bijective _ hb, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.card_filter, H]
  simp

end engine2

end OMA.P_oeis_a215229

namespace OMA.P_oeis_a215229

open PowerSeries OMA.S_oeis_a215229

lemma bne_map (f : ℕ → ℕ) (hf : f.Injective) (a b : Option ℕ) :
    (a.map f != b.map f) = (a != b) := by
  rw [Bool.eq_iff_iff, bne_iff_ne, bne_iff_ne, ne_eq, ne_eq, (Option.map_injective hf).eq_iff]

lemma sqf_map (f : ℕ → ℕ) (hf : f.Injective) (l : List ℕ) :
    squarefree (l.map f) = squarefree l := by
  simp only [squarefree, List.getElem?_map, bne_map f hf]

set_option maxRecDepth 100000 in
theorem Pc_val : Pc squarefree [] 0 6 = [0, 18, -31, 9, 9, -6, 1] := by decide +kernel

theorem poly (k : ℕ) : total k = (k:ℤ)^6 - 6*(k:ℤ)^4 + 5*(k:ℤ)^3 + 5*(k:ℤ)^2 - 5*k := by
  unfold total
  rw [card_eq_H, H_eq_ev squarefree sqf_map (k + 1) 6 [] 0 (by simp) (by omega), Pc_val]
  simp only [ev]
  push_cast
  ring

open PowerSeries in
theorem gf_core (f : ℕ → ℤ) (hp : ∀ k : ℕ, f k = (k:ℤ)^6 - 6*(k:ℤ)^4 + 5*(k:ℤ)^3 + 5*(k:ℤ)^2 - 5*k) :
    (1-X)^7 * mk f = (6*X^2*(3+47*X+77*X^2-7*X^3) : PowerSeries ℤ) := by
  have e : (1 - X) ^ 7 * mk f = mk f - C 7 * (X ^ 1 * mk f) + C 21 * (X ^ 2 * mk f) -
      C 35 * (X ^ 3 * mk f) + C 35 * (X ^ 4 * mk f) - C 21 * (X ^ 5 * mk f) +
      C 7 * (X ^ 6 * mk f) - X ^ 7 * mk f := by
    simp only [map_ofNat]
    ring
  have e2 : (6*X^2*(3+47*X+77*X^2-7*X^3) : PowerSeries ℤ) =
      C 18 * X ^ 2 + C 282 * X ^ 3 + C 462 * X ^ 4 - C 42 * X ^ 5 := by
    simp only [map_ofNat]
    ring
  rw [e, e2]
  ext N
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', coeff_mk, coeff_X_pow]
  rcases lt_or_ge N 7 with h | h
  · interval_cases N <;> simp [hp] <;> norm_num
  · obtain ⟨M, rfl⟩ : ∃ M, N = M + 7 := ⟨N - 7, by omega⟩
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega),
      if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega),
      show M + 7 - 1 = M + 6 by omega, show M + 7 - 2 = M + 5 by omega,
      show M + 7 - 3 = M + 4 by omega, show M + 7 - 4 = M + 3 by omega,
      show M + 7 - 5 = M + 2 by omega, show M + 7 - 6 = M + 1 by omega,
      show M + 7 - 7 = M by omega]
    simp only [hp]
    push_cast
    ring

end OMA.P_oeis_a215229

open OMA.S_oeis_a215229 OMA.P_oeis_a215229 in
theorem OMA.solution : type_of% @OMA.S_oeis_a215229.main := by
  refine ⟨poly, fun k => ?_, gf_core total poly⟩
  simp only [poly]
  push_cast
  ring
