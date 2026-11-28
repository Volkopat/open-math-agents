import FormalConjectures.Kourovka.«19_25»

-- Problem: Conjecture 19.25
-- Upstream: formal-conjectures FormalConjectures/Kourovka/19_25.lean:51 (declaration Kourovka.«19.25».kourovka_19_25)
-- Credit: @ronak14p (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/- Counterexample: G = PSU(3,3) (as a permutation group on 28 points, simple via conjugacy-class
   certificates), H = C6 × S4 × (C7 ⋊ C6); both of order 6048 with totient sum 23984.
   All finite computations are checked by the kernel (decide +kernel). -/


namespace OMA1925

/-! ## Base-128 codes of functions on `{0, …, n-1}` -/

def get (c p : ℕ) : ℕ := c / 128 ^ p % 128

def encN (f : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, k => f k + 128 * encN f n (k + 1)

theorem get_lt (c p : ℕ) : get c p < 128 := Nat.mod_lt _ (by norm_num)

theorem get_zero_add (x y : ℕ) (hx : x < 128) : get (x + 128 * y) 0 = x := by
  unfold get
  rw [pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]

theorem get_succ_add (x y p : ℕ) (hx : x < 128) : get (x + 128 * y) (p + 1) = get y p := by
  unfold get
  rw [pow_succ', ← Nat.div_div_eq_div_mul]
  congr 2
  rw [Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt hx, zero_add]

theorem get_encN (f : ℕ → ℕ) : ∀ (n k : ℕ), (∀ i, k ≤ i → i < k + n → f i < 128) →
    ∀ p, p < n → get (encN f n k) p = f (k + p)
  | 0, _, _, _, hp => absurd hp (Nat.not_lt_zero _)
  | n + 1, k, hf, 0, _ => by
      rw [encN, get_zero_add _ _ (hf k le_rfl (by omega)), Nat.add_zero]
  | n + 1, k, hf, p + 1, hp => by
      rw [encN, get_succ_add _ _ _ (hf k le_rfl (by omega)),
        get_encN f n (k + 1) (fun i h1 h2 => hf i (by omega) (by omega)) p (by omega)]
      congr 1
      omega

theorem encN_congr (f g : ℕ → ℕ) : ∀ (n k : ℕ), (∀ i, k ≤ i → i < k + n → f i = g i) →
    encN f n k = encN g n k
  | 0, _, _ => rfl
  | n + 1, k, h => by
      rw [encN, encN, h k le_rfl (by omega),
        encN_congr f g n (k + 1) (fun i h1 h2 => h i (by omega) (by omega))]

def allBelow : ℕ → (ℕ → Bool) → Bool
  | 0, _ => true
  | k + 1, f => f k && allBelow k f

theorem allBelow_spec : ∀ (k : ℕ) (f : ℕ → Bool), allBelow k f = true → ∀ i, i < k → f i = true
  | 0, _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | k + 1, f, h, i, hi => by
      rw [allBelow, Bool.and_eq_true] at h
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
      · exact allBelow_spec k f h.2 i hi
      · subst hi; exact h.1

def sumBelow : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | k + 1, f => sumBelow k f + f k

theorem sumBelow_eq : ∀ (k : ℕ) (f : ℕ → ℕ), sumBelow k f = ∑ i ∈ Finset.range k, f i
  | 0, _ => rfl
  | k + 1, f => by rw [sumBelow, Finset.sum_range_succ, sumBelow_eq k f]

def comp (n c d : ℕ) : ℕ := encN (fun p => get c (get d p)) n 0

def idc (n : ℕ) : ℕ := encN (fun p => p) n 0

theorem get_comp (n c d p : ℕ) (hp : p < n) : get (comp n c d) p = get c (get d p) := by
  unfold comp
  rw [get_encN _ n 0 (fun i _ _ => get_lt _ _) p hp, zero_add]

theorem get_idc (n p : ℕ) (hn : n ≤ 128) (hp : p < n) : get (idc n) p = p := by
  unfold idc
  rw [get_encN _ n 0 (fun i _ h => by omega) p hp, zero_add]

/-! ## Codes of permutations -/

section perm
variable {n : ℕ}

def code (σ : Equiv.Perm (Fin n)) : ℕ :=
  encN (fun p => if h : p < n then ((σ ⟨p, h⟩ : Fin n) : ℕ) else 0) n 0

theorem get_code (hn : n ≤ 128) (σ : Equiv.Perm (Fin n)) (p : Fin n) :
    get (code σ) p = σ p := by
  unfold code
  rw [get_encN _ n 0 (fun i _ _ => by split <;> omega) p p.isLt, zero_add, dif_pos p.isLt]

theorem code_inj (hn : n ≤ 128) {σ τ : Equiv.Perm (Fin n)} (h : code σ = code τ) : σ = τ :=
  Equiv.ext fun p => Fin.ext (by rw [← get_code hn σ p, h, get_code hn τ p])

theorem code_mul (hn : n ≤ 128) (σ τ : Equiv.Perm (Fin n)) :
    code (σ * τ) = comp n (code σ) (code τ) := by
  show encN _ n 0 = encN _ n 0
  apply encN_congr
  intro i _ hi
  rw [zero_add] at hi
  rw [dif_pos hi, get_code hn τ ⟨i, hi⟩, get_code hn σ]
  rfl

theorem code_one (hn : n ≤ 128) : code (1 : Equiv.Perm (Fin n)) = idc n := by
  show encN _ n 0 = encN _ n 0
  apply encN_congr
  intro i _ hi
  rw [zero_add] at hi
  rw [dif_pos hi]
  rfl

theorem eq_one_iff (hn : n ≤ 128) (σ : Equiv.Perm (Fin n)) : σ = 1 ↔ code σ = idc n := by
  constructor
  · rintro rfl; exact code_one hn
  · intro h; exact code_inj hn (h.trans (code_one hn).symm)

def canon (n c : ℕ) : Bool := c == encN (get c) n 0 && allBelow n (fun p => decide (get c p < n))

def okPair (n c d : ℕ) : Bool :=
  canon n c && canon n d && comp n c d == idc n && comp n d c == idc n

theorem canon_spec {c : ℕ} (h : canon n c = true) :
    c = encN (get c) n 0 ∧ ∀ p, p < n → get c p < n := by
  unfold canon at h
  rw [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1, fun p hp => of_decide_eq_true (allBelow_spec n _ h.2 p hp)⟩

theorem okPair_spec {c d : ℕ} (h : okPair n c d = true) :
    canon n c = true ∧ canon n d = true ∧ comp n c d = idc n ∧ comp n d c = idc n := by
  unfold okPair at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem npos_of_fin (p : Fin n) : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) p.isLt

def ofC (n c d : ℕ) (hn : n ≤ 128) (h : okPair n c d = true) : Equiv.Perm (Fin n) where
  toFun p := ⟨get c p % n, Nat.mod_lt _ (npos_of_fin p)⟩
  invFun p := ⟨get d p % n, Nat.mod_lt _ (npos_of_fin p)⟩
  left_inv p := by
    obtain ⟨hc, _, _, hdc⟩ := okPair_spec h
    apply Fin.ext
    simp only
    rw [Nat.mod_eq_of_lt ((canon_spec hc).2 p p.isLt), ← get_comp n d c p p.isLt, hdc,
      get_idc n p hn p.isLt, Nat.mod_eq_of_lt p.isLt]
  right_inv p := by
    obtain ⟨_, hd, hcd, _⟩ := okPair_spec h
    apply Fin.ext
    simp only
    rw [Nat.mod_eq_of_lt ((canon_spec hd).2 p p.isLt), ← get_comp n c d p p.isLt, hcd,
      get_idc n p hn p.isLt, Nat.mod_eq_of_lt p.isLt]

theorem code_ofC (c d : ℕ) (hn : n ≤ 128) (h : okPair n c d = true) : code (ofC n c d hn h) = c := by
  obtain ⟨hc, _, _, _⟩ := okPair_spec h
  obtain ⟨h1, h2⟩ := canon_spec hc
  conv_rhs => rw [h1]
  show encN _ n 0 = encN _ n 0
  apply encN_congr
  intro i _ hi
  rw [zero_add] at hi
  rw [dif_pos hi]
  exact Nat.mod_eq_of_lt (h2 i hi)

theorem code_ofC_inv (c d : ℕ) (hn : n ≤ 128) (h : okPair n c d = true) :
    code (ofC n c d hn h)⁻¹ = d := by
  obtain ⟨_, hd, _, _⟩ := okPair_spec h
  obtain ⟨h1, h2⟩ := canon_spec hd
  conv_rhs => rw [h1]
  show encN _ n 0 = encN _ n 0
  apply encN_congr
  intro i _ hi
  rw [zero_add] at hi
  rw [dif_pos hi]
  exact Nat.mod_eq_of_lt (h2 i hi)

/-! ## Orders -/

def ordAux (n c : ℕ) : ℕ → ℕ → ℕ → ℕ
  | _, _, 0 => 0
  | x, k, f + 1 => if x == idc n then k else ordAux n c (comp n c x) (k + 1) f

theorem ordAux_spec (hn : n ≤ 128) (σ : Equiv.Perm (Fin n)) :
    ∀ (f k : ℕ), 0 < k → (∀ m, 0 < m → m < k → σ ^ m ≠ 1) →
      ordAux n (code σ) (code (σ ^ k)) k f ≠ 0 →
      orderOf σ = ordAux n (code σ) (code (σ ^ k)) k f ∧ ordAux n (code σ) (code (σ ^ k)) k f ≤ k + f
  | 0, k, _, _, h => absurd rfl h
  | f + 1, k, hk, hm, h => by
      by_cases hx : code (σ ^ k) = idc n
      · have e : ordAux n (code σ) (code (σ ^ k)) k (f + 1) = k := by
          rw [ordAux, if_pos (beq_iff_eq.mpr hx)]
        rw [e]
        refine ⟨?_, by omega⟩
        rw [orderOf_eq_iff hk]
        exact ⟨(eq_one_iff hn _).mpr hx, fun m h1 h2 => hm m h2 h1⟩
      · have e : ordAux n (code σ) (code (σ ^ k)) k (f + 1) =
            ordAux n (code σ) (code (σ ^ (k + 1))) (k + 1) f := by
          rw [ordAux, if_neg (by simpa using hx), pow_succ', code_mul hn]
        rw [e] at h ⊢
        have hk1 : σ ^ k ≠ 1 := fun h' => hx ((eq_one_iff hn _).mp h')
        have := ordAux_spec hn σ f (k + 1) (by omega)
          (fun m h1 h2 => by
            rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h2 | h2
            · exact hm m h1 h2
            · subst h2; exact hk1) h
        exact ⟨this.1, by omega⟩

def ordc (n c : ℕ) : ℕ := ordAux n c c 1 90

theorem ordc_spec (hn : n ≤ 128) (σ : Equiv.Perm (Fin n)) (h : ordc n (code σ) ≠ 0) :
    orderOf σ = ordc n (code σ) ∧ ordc n (code σ) ≤ 91 := by
  have := ordAux_spec hn σ 90 1 (by norm_num) (fun m h1 h2 => by omega) (by simpa [ordc] using h)
  simpa [ordc] using this

end perm

def totT : List ℕ := [0, 1, 1, 2, 2, 4, 2, 6, 4, 6, 4, 10, 4, 12, 6, 8, 8, 16, 6, 18, 8, 12, 10, 22, 8, 20, 12, 18, 12, 28, 8, 30, 16, 20, 16, 24, 12, 36, 18, 24, 16, 40, 12, 42, 20, 24, 22, 46, 16, 42, 20, 32, 24, 52, 18, 40, 24, 36, 28, 58, 16, 60, 30, 36, 32, 48, 20, 66, 32, 44, 24, 70, 24, 72, 36, 40, 36, 60, 24, 78, 32, 54, 40, 82, 24, 64, 42, 56, 40, 88, 24, 72]

theorem totT_all : allBelow 92 (fun r => totT.getD r 0 == Nat.totient r) = true := by decide +kernel

theorem totT_spec (r : ℕ) (hr : r ≤ 91) : totT.getD r 0 = Nat.totient r :=
  beq_iff_eq.mp (allBelow_spec 92 _ totT_all r (by omega))

end OMA1925

/- Stabiliser chains with three levels -/

namespace OMA1925

structure Chain where
  n : ℕ
  gens : List (ℕ × ℕ)
  s0 : ℕ
  s1 : ℕ
  s2 : ℕ
  b0 : ℕ
  b1 : ℕ
  b2 : ℕ
  T0 : List (ℕ × ℕ)
  T1 : List (ℕ × ℕ)
  T2 : List (ℕ × ℕ)
  I0 : List ℕ
  I1 : List ℕ
  I2 : List ℕ
  W0 : List (List ℕ)
  W1 : List (List ℕ)
  W2 : List (List ℕ)

namespace Chain

variable (C : Chain)

def T : ℕ → List (ℕ × ℕ)
  | 0 => C.T0
  | 1 => C.T1
  | _ => C.T2

def W : ℕ → List (List ℕ)
  | 0 => C.W0
  | 1 => C.W1
  | _ => C.W2

def sz : ℕ → ℕ
  | 0 => C.s0
  | 1 => C.s1
  | _ => C.s2

def uc (l i : ℕ) : ℕ := ((C.T l).getD i (0, 0)).1
def uic (l i : ℕ) : ℕ := ((C.T l).getD i (0, 0)).2
def gc (i : ℕ) : ℕ := (C.gens.getD i (0, 0)).1
def gic (i : ℕ) : ℕ := (C.gens.getD i (0, 0)).2
def wd (l i : ℕ) : List ℕ := (C.W l).getD i []
def ng : ℕ := C.gens.length

def wordc (w : List ℕ) : ℕ := w.foldr (fun i acc => comp C.n (C.gc i) acc) (idc C.n)

def ec3 (i j k : ℕ) : ℕ := comp C.n (C.uc 0 i) (comp C.n (C.uc 1 j) (C.uc 2 k))

def vc (v : ℕ) : ℕ := if v < C.s1 then C.uc 1 v else C.uc 2 (v - C.s1)

def c2ok' (k x : ℕ) : Bool := decide (k < C.s2) && C.uc 2 k == x
def c2ok (x : ℕ) : Bool := C.c2ok' (C.I2.getD (get x C.b2) 0) x

def c1ok'' (j k x : ℕ) : Bool := decide (j < C.s1) && decide (k < C.s2) && x == comp C.n (C.uc 1 j) (C.uc 2 k)
def c1ok' (j x : ℕ) : Bool := C.c1ok'' j (C.I2.getD (get (comp C.n (C.uic 1 j) x) C.b2) 0) x
def c1ok (x : ℕ) : Bool := C.c1ok' (C.I1.getD (get x C.b1) 0) x

def c0d (i j k x : ℕ) : Bool :=
  decide (i < C.s0) && decide (j < C.s1) && decide (k < C.s2) && x == C.ec3 i j k
def c0c (i j r1 x : ℕ) : Bool := C.c0d i j (C.I2.getD (get (comp C.n (C.uic 1 j) r1) C.b2) 0) x
def c0b (i r1 x : ℕ) : Bool := C.c0c i (C.I1.getD (get r1 C.b1) 0) r1 x
def c0a (i x : ℕ) : Bool := C.c0b i (comp C.n (C.uic 0 i) x) x
def c0ok (x : ℕ) : Bool := C.c0a (C.I0.getD (get x C.b0) 0) x

def checkBasic : Bool :=
  decide (C.n ≤ 128) && decide (C.b0 < C.n) && decide (C.b1 < C.n) && decide (C.b2 < C.n) &&
  decide (0 < C.s0) && decide (0 < C.s1) && decide (0 < C.s2)

def checkGens : Bool := allBelow C.ng (fun i => okPair C.n (C.gc i) (C.gic i))

def checkLevel (l : ℕ) : Bool :=
  allBelow (C.sz l) (fun i => okPair C.n (C.uc l i) (C.uic l i) &&
    C.uc l i == C.wordc (C.wd l i) && (C.wd l i).all (fun j => decide (j < C.ng)))

def checkFix : Bool :=
  allBelow C.s1 (fun i => get (C.uc 1 i) C.b0 == C.b0) &&
  allBelow C.s2 (fun i => get (C.uc 2 i) C.b0 == C.b0 && get (C.uc 2 i) C.b1 == C.b1)

def checkDist : Bool :=
  allBelow C.s0 (fun i => C.I0.getD (get (C.uc 0 i) C.b0) 0 == i) &&
  allBelow C.s1 (fun i => C.I1.getD (get (C.uc 1 i) C.b1) 0 == i) &&
  allBelow C.s2 (fun i => C.I2.getD (get (C.uc 2 i) C.b2) 0 == i)

def checkC2 : Bool := allBelow C.s2 (fun v => allBelow C.s2 (fun w => C.c2ok (comp C.n (C.uc 2 v) (C.uc 2 w))))

def checkC1 : Bool := allBelow (C.s1 + C.s2) (fun v => allBelow C.s1 (fun u => C.c1ok (comp C.n (C.vc v) (C.uc 1 u))))

def checkC0 : Bool := allBelow C.ng (fun g => allBelow C.s0 (fun u =>
  C.c0ok (comp C.n (C.gc g) (C.uc 0 u)) && C.c0ok (comp C.n (C.gic g) (C.uc 0 u))))

def checkId : Bool := C.uc 0 0 == idc C.n && C.uc 1 0 == idc C.n && C.uc 2 0 == idc C.n

def valid : Bool :=
  C.checkId && C.checkBasic && C.checkGens && C.checkLevel 0 && C.checkLevel 1 && C.checkLevel 2 &&
  C.checkFix && C.checkDist && C.checkC2 && C.checkC1 && C.checkC0

/- Permutations -/

def genP (i : ℕ) : Equiv.Perm (Fin C.n) :=
  if h : C.n ≤ 128 ∧ okPair C.n (C.gc i) (C.gic i) = true then ofC C.n _ _ h.1 h.2 else 1

def U (l i : ℕ) : Equiv.Perm (Fin C.n) :=
  if h : C.n ≤ 128 ∧ okPair C.n (C.uc l i) (C.uic l i) = true then ofC C.n _ _ h.1 h.2 else 1

def grp : Subgroup (Equiv.Perm (Fin C.n)) :=
  Subgroup.closure (Set.range (fun i : Fin C.ng => C.genP i))

def wordP (w : List ℕ) : Equiv.Perm (Fin C.n) := w.foldr (fun i acc => C.genP i * acc) 1

def e3 (i j k : ℕ) : Equiv.Perm (Fin C.n) := C.U 0 i * (C.U 1 j * C.U 2 k)

noncomputable instance : Fintype C.grp := Fintype.ofFinite _

variable {C}

section valid
variable (hv : C.valid = true)
include hv

theorem hBasic : C.checkBasic = true := by
  unfold valid at hv; simp only [Bool.and_eq_true] at hv; tauto
theorem hn : C.n ≤ 128 := by
  have := hBasic hv; unfold checkBasic at this; simp only [Bool.and_eq_true, decide_eq_true_eq] at this; tauto
theorem hb0 : C.b0 < C.n := by
  have := hBasic hv; unfold checkBasic at this; simp only [Bool.and_eq_true, decide_eq_true_eq] at this; tauto
theorem hb1 : C.b1 < C.n := by
  have := hBasic hv; unfold checkBasic at this; simp only [Bool.and_eq_true, decide_eq_true_eq] at this; tauto
theorem hb2 : C.b2 < C.n := by
  have := hBasic hv; unfold checkBasic at this; simp only [Bool.and_eq_true, decide_eq_true_eq] at this; tauto
theorem hId : C.checkId = true := by
  unfold valid at hv; simp only [Bool.and_eq_true] at hv; tauto
theorem hs0 : 0 < C.s0 := by
  have := hBasic hv; unfold checkBasic at this; simp only [Bool.and_eq_true, decide_eq_true_eq] at this; tauto
theorem hs1 : 0 < C.s1 := by
  have := hBasic hv; unfold checkBasic at this; simp only [Bool.and_eq_true, decide_eq_true_eq] at this; tauto
theorem hs2 : 0 < C.s2 := by
  have := hBasic hv; unfold checkBasic at this; simp only [Bool.and_eq_true, decide_eq_true_eq] at this; tauto
theorem hGens : C.checkGens = true := by
  unfold valid at hv; simp only [Bool.and_eq_true] at hv; tauto
theorem hLevel (l : ℕ) (hl : l < 3) : C.checkLevel l = true := by
  unfold valid at hv; simp only [Bool.and_eq_true] at hv
  interval_cases l <;> tauto
theorem hFix : C.checkFix = true := by
  unfold valid at hv; simp only [Bool.and_eq_true] at hv; tauto
theorem hDist : C.checkDist = true := by
  unfold valid at hv; simp only [Bool.and_eq_true] at hv; tauto
theorem hC2 : C.checkC2 = true := by
  unfold valid at hv; simp only [Bool.and_eq_true] at hv; tauto
theorem hC1 : C.checkC1 = true := by
  unfold valid at hv; simp only [Bool.and_eq_true] at hv; tauto
theorem hC0 : C.checkC0 = true := by
  unfold valid at hv; simp only [Bool.and_eq_true] at hv; tauto

theorem okU {l i : ℕ} (hl : l < 3) (hi : i < C.sz l) : okPair C.n (C.uc l i) (C.uic l i) = true := by
  have := allBelow_spec _ _ (hLevel hv l hl) i hi
  simp only [Bool.and_eq_true] at this
  exact this.1.1

theorem code_U {l i : ℕ} (hl : l < 3) (hi : i < C.sz l) : code (C.U l i) = C.uc l i := by
  unfold U; rw [dif_pos ⟨hn hv, okU hv hl hi⟩, code_ofC]

theorem code_U_inv {l i : ℕ} (hl : l < 3) (hi : i < C.sz l) : code (C.U l i)⁻¹ = C.uic l i := by
  unfold U; rw [dif_pos ⟨hn hv, okU hv hl hi⟩, code_ofC_inv]

theorem okG {i : ℕ} (hi : i < C.ng) : okPair C.n (C.gc i) (C.gic i) = true :=
  allBelow_spec _ _ (hGens hv) i hi

theorem code_genP {i : ℕ} (hi : i < C.ng) : code (C.genP i) = C.gc i := by
  unfold genP; rw [dif_pos ⟨hn hv, okG hv hi⟩, code_ofC]

theorem code_genP_inv {i : ℕ} (hi : i < C.ng) : code (C.genP i)⁻¹ = C.gic i := by
  unfold genP; rw [dif_pos ⟨hn hv, okG hv hi⟩, code_ofC_inv]

theorem U_apply {l i : ℕ} (hl : l < 3) (hi : i < C.sz l) (p : Fin C.n) :
    ((C.U l i p : Fin C.n) : ℕ) = get (C.uc l i) p := by
  rw [← get_code (hn hv) (C.U l i) p, code_U hv hl hi]

theorem code_e3 {i j k : ℕ} (hi : i < C.s0) (hj : j < C.s1) (hk : k < C.s2) :
    code (C.e3 i j k) = C.ec3 i j k := by
  unfold e3 ec3
  rw [code_mul (hn hv), code_mul (hn hv), code_U hv (l := 0) (by norm_num) hi,
    code_U hv (l := 1) (by norm_num) hj, code_U hv (l := 2) (by norm_num) hk]

theorem code_eq {σ τ : Equiv.Perm (Fin C.n)} (h : code σ = code τ) : σ = τ := code_inj (hn hv) h

end valid

theorem wordP_mem (w : List ℕ) (hw : ∀ j ∈ w, j < C.ng) : C.wordP w ∈ C.grp := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons a w ih =>
    show C.genP a * C.wordP w ∈ C.grp
    refine Subgroup.mul_mem _ (Subgroup.subset_closure ⟨⟨a, hw a (by simp)⟩, rfl⟩) ?_
    exact ih (fun j hj => hw j (by simp [hj]))

theorem code_wordP (hv : C.valid = true) (w : List ℕ) (hw : ∀ j ∈ w, j < C.ng) :
    code (C.wordP w) = C.wordc w := by
  induction w with
  | nil => exact code_one (hn hv)
  | cons a w ih =>
    show code (C.genP a * C.wordP w) = comp C.n (C.gc a) (C.wordc w)
    rw [code_mul (hn hv), code_genP hv (hw a (by simp)), ih (fun j hj => hw j (by simp [hj]))]

theorem U_mem (hv : C.valid = true) {l i : ℕ} (hl : l < 3) (hi : i < C.sz l) : C.U l i ∈ C.grp := by
  have h := allBelow_spec _ _ (hLevel hv l hl) i hi
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  have : C.U l i = C.wordP (C.wd l i) :=
    code_eq hv (by rw [code_U hv hl hi, code_wordP hv _ h.2, h.1.2])
  rw [this]; exact wordP_mem _ h.2

theorem e3_mem (hv : C.valid = true) {i j k : ℕ} (hi : i < C.s0) (hj : j < C.s1) (hk : k < C.s2) :
    C.e3 i j k ∈ C.grp :=
  Subgroup.mul_mem _ (U_mem hv (l := 0) (by norm_num) hi)
    (Subgroup.mul_mem _ (U_mem hv (l := 1) (by norm_num) hj) (U_mem hv (l := 2) (by norm_num) hk))

/- closure lemmas -/

theorem lemA (hv : C.valid = true) {v w : ℕ} (hv' : v < C.s2) (hw : w < C.s2) :
    ∃ k, k < C.s2 ∧ C.U 2 v * C.U 2 w = C.U 2 k := by
  have h := allBelow_spec _ _ (allBelow_spec _ _ (hC2 hv) v hv') w hw
  unfold c2ok c2ok' at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  refine ⟨_, h.1, code_eq hv ?_⟩
  rw [code_mul (hn hv), code_U hv (l := 2) (by norm_num) hv', code_U hv (l := 2) (by norm_num) hw,
    code_U hv (l := 2) (by norm_num) h.1, h.2]

def V (C : Chain) (v : ℕ) : Equiv.Perm (Fin C.n) := if v < C.s1 then C.U 1 v else C.U 2 (v - C.s1)

theorem lemB (hv : C.valid = true) {v u : ℕ} (hv' : v < C.s1 + C.s2) (hu : u < C.s1) :
    ∃ j k, j < C.s1 ∧ k < C.s2 ∧ C.V v * C.U 1 u = C.U 1 j * C.U 2 k := by
  have h := allBelow_spec _ _ (allBelow_spec _ _ (hC1 hv) v hv') u hu
  unfold c1ok c1ok' c1ok'' at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨_, _, h1, h2, code_eq hv ?_⟩
  rw [code_mul (hn hv), code_mul (hn hv), code_U hv (l := 1) (by norm_num) hu,
    code_U hv (l := 1) (by norm_num) h1, code_U hv (l := 2) (by norm_num) h2, ← h3]
  congr 1
  unfold V vc
  split_ifs with hs
  · exact code_U hv (l := 1) (by norm_num) hs
  · exact code_U hv (l := 2) (by norm_num) (show v - C.s1 < C.s2 by omega)

theorem lemC (hv : C.valid = true) {x : ℕ} (h : C.c0ok x = true) :
    ∃ i j k, i < C.s0 ∧ j < C.s1 ∧ k < C.s2 ∧ x = code (C.e3 i j k) := by
  unfold c0ok c0a c0b c0c c0d at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨_, _, _, h1, h2, h3, by rw [code_e3 hv h1 h2 h3]; exact h4⟩

def InS1 (C : Chain) (x : Equiv.Perm (Fin C.n)) : Prop := ∃ j k, j < C.s1 ∧ k < C.s2 ∧ x = C.U 1 j * C.U 2 k
def InS0 (C : Chain) (x : Equiv.Perm (Fin C.n)) : Prop :=
  ∃ i j k, i < C.s0 ∧ j < C.s1 ∧ k < C.s2 ∧ x = C.e3 i j k

theorem S1_mul (hv : C.valid = true) {x y : Equiv.Perm (Fin C.n)} (hx : C.InS1 x) (hy : C.InS1 y) :
    C.InS1 (x * y) := by
  obtain ⟨j, k, hj, hk, rfl⟩ := hx
  obtain ⟨j', k', hj', hk', rfl⟩ := hy
  obtain ⟨j2, k2, hj2, hk2, e1⟩ := lemB hv (v := C.s1 + k) (by omega) hj'
  have e1' : C.U 2 k * C.U 1 j' = C.U 1 j2 * C.U 2 k2 := by
    rw [← e1]; unfold V; rw [if_neg (by omega), Nat.add_sub_cancel_left]
  obtain ⟨j3, k3, hj3, hk3, e2⟩ := lemB hv (v := j) (by omega) hj2
  have e2' : C.U 1 j * C.U 1 j2 = C.U 1 j3 * C.U 2 k3 := by
    rw [← e2]; unfold V; rw [if_pos hj]
  obtain ⟨k4, hk4, e3⟩ := lemA hv hk3 hk2
  obtain ⟨k5, hk5, e4⟩ := lemA hv hk4 hk'
  refine ⟨j3, k5, hj3, hk5, ?_⟩
  calc C.U 1 j * C.U 2 k * (C.U 1 j' * C.U 2 k') = C.U 1 j * (C.U 2 k * C.U 1 j') * C.U 2 k' := by
        simp only [mul_assoc]
    _ = C.U 1 j * C.U 1 j2 * C.U 2 k2 * C.U 2 k' := by rw [e1']; simp only [mul_assoc]
    _ = C.U 1 j3 * (C.U 2 k3 * C.U 2 k2) * C.U 2 k' := by rw [e2']; simp only [mul_assoc]
    _ = C.U 1 j3 * C.U 2 k5 := by rw [e3, mul_assoc, e4]

theorem S0_left (hv : C.valid = true) (g : Equiv.Perm (Fin C.n))
    (hg : ∀ u, u < C.s0 → C.c0ok (comp C.n (code g) (C.uc 0 u)) = true)
    {x : Equiv.Perm (Fin C.n)} (hx : C.InS0 x) : C.InS0 (g * x) := by
  obtain ⟨i, j, k, hi, hj, hk, rfl⟩ := hx
  obtain ⟨i', j', k', hi', hj', hk', h⟩ := lemC hv (hg i hi)
  have e : g * C.U 0 i = C.e3 i' j' k' :=
    code_eq hv (by rw [code_mul (hn hv), code_U hv (l := 0) (by norm_num) hi, h])
  obtain ⟨j2, k2, hj2, hk2, e2⟩ := S1_mul hv (x := C.U 1 j' * C.U 2 k') (y := C.U 1 j * C.U 2 k)
    ⟨j', k', hj', hk', rfl⟩ ⟨j, k, hj, hk, rfl⟩
  refine ⟨i', j2, k2, hi', hj2, hk2, ?_⟩
  unfold e3 at e ⊢
  rw [← mul_assoc, e, mul_assoc, e2]

theorem U_zero (hv : C.valid = true) {l : ℕ} (hl : l < 3) : C.U l 0 = 1 := by
  have h := hId hv
  unfold checkId at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  have hl0 : 0 < C.sz l := by
    interval_cases l
    · exact hs0 hv
    · exact hs1 hv
    · exact hs2 hv
  apply code_eq hv
  rw [code_U hv hl hl0, code_one (hn hv)]
  interval_cases l
  · exact h.1.1
  · exact h.1.2
  · exact h.2

theorem closure_sub (hv : C.valid = true) {x : Equiv.Perm (Fin C.n)} (hx : x ∈ C.grp) : C.InS0 x := by
  have hid : C.InS0 1 := ⟨0, 0, 0, hs0 hv, hs1 hv, hs2 hv, by
    unfold e3; rw [U_zero hv (by norm_num), U_zero hv (by norm_num), U_zero hv (by norm_num)]; simp⟩
  induction hx using Subgroup.closure_induction_left with
  | one => exact hid
  | mul_left g hg y _ ih =>
    obtain ⟨⟨i, hi⟩, rfl⟩ := hg
    refine S0_left hv _ (fun u hu => ?_) ih
    have := allBelow_spec _ _ (allBelow_spec _ _ (hC0 hv) i hi) u hu
    rw [code_genP hv hi]
    simp only [Bool.and_eq_true] at this; exact this.1
  | inv_mul_cancel g hg y _ ih =>
    obtain ⟨⟨i, hi⟩, rfl⟩ := hg
    refine S0_left hv _ (fun u hu => ?_) ih
    have := allBelow_spec _ _ (allBelow_spec _ _ (hC0 hv) i hi) u hu
    rw [code_genP_inv hv hi]
    simp only [Bool.and_eq_true] at this; exact this.2

theorem e3_apply_b0 (hv : C.valid = true) {i j k : ℕ} (hi : i < C.s0) (hj : j < C.s1) (hk : k < C.s2) :
    ((C.e3 i j k ⟨C.b0, hb0 hv⟩ : Fin C.n) : ℕ) = get (C.uc 0 i) C.b0 := by
  have hf := hFix hv
  unfold checkFix at hf
  rw [Bool.and_eq_true] at hf
  have h1 := allBelow_spec _ _ hf.1 j hj
  have h2 := allBelow_spec _ _ hf.2 k hk
  simp only [Bool.and_eq_true, beq_iff_eq] at h1 h2
  have q2 : C.U 2 k ⟨C.b0, hb0 hv⟩ = ⟨C.b0, hb0 hv⟩ :=
    Fin.ext (by rw [U_apply hv (l := 2) (by norm_num) hk]; exact h2.1)
  have q1 : C.U 1 j ⟨C.b0, hb0 hv⟩ = ⟨C.b0, hb0 hv⟩ :=
    Fin.ext (by rw [U_apply hv (l := 1) (by norm_num) hj]; exact h1)
  unfold e3
  simp only [Equiv.Perm.mul_apply, q2, q1]
  rw [U_apply hv (l := 0) (by norm_num) hi]

theorem e3_inj (hv : C.valid = true) {i j k i' j' k' : ℕ} (hi : i < C.s0) (hj : j < C.s1) (hk : k < C.s2)
    (hi' : i' < C.s0) (hj' : j' < C.s1) (hk' : k' < C.s2) (h : C.e3 i j k = C.e3 i' j' k') :
    i = i' ∧ j = j' ∧ k = k' := by
  have hd := hDist hv
  unfold checkDist at hd
  simp only [Bool.and_eq_true] at hd
  have d0 := fun i hi => beq_iff_eq.mp (allBelow_spec _ _ hd.1.1 i hi)
  have d1 := fun i hi => beq_iff_eq.mp (allBelow_spec _ _ hd.1.2 i hi)
  have d2 := fun i hi => beq_iff_eq.mp (allBelow_spec _ _ hd.2 i hi)
  have ei : i = i' := by
    have := congrArg (fun σ => ((σ ⟨C.b0, hb0 hv⟩ : Fin C.n) : ℕ)) h
    try dsimp only at this
    rw [e3_apply_b0 hv hi hj hk, e3_apply_b0 hv hi' hj' hk'] at this
    rw [← d0 i hi, ← d0 i' hi', this]
  subst ei
  have h' : C.U 1 j * C.U 2 k = C.U 1 j' * C.U 2 k' := mul_left_cancel h
  have hf := hFix hv
  unfold checkFix at hf
  rw [Bool.and_eq_true] at hf
  have fix2 : ∀ k, k < C.s2 → C.U 2 k ⟨C.b1, hb1 hv⟩ = ⟨C.b1, hb1 hv⟩ := fun k hk => by
    have h2 := allBelow_spec _ _ hf.2 k hk
    simp only [Bool.and_eq_true, beq_iff_eq] at h2
    exact Fin.ext (by rw [U_apply hv (l := 2) (by norm_num) hk]; exact h2.2)
  have ej : j = j' := by
    have := congrArg (fun σ => ((σ ⟨C.b1, hb1 hv⟩ : Fin C.n) : ℕ)) h'
    simp only [Equiv.Perm.mul_apply, fix2 k hk, fix2 k' hk'] at this
    rw [U_apply hv (l := 1) (by norm_num) hj, U_apply hv (l := 1) (by norm_num) hj'] at this
    rw [← d1 j hj, ← d1 j' hj', this]
  subst ej
  have h'' : C.U 2 k = C.U 2 k' := mul_left_cancel h'
  refine ⟨rfl, rfl, ?_⟩
  have := congrArg (fun σ => ((σ ⟨C.b2, hb2 hv⟩ : Fin C.n) : ℕ)) h''
  try dsimp only at this
  rw [U_apply hv (l := 2) (by norm_num) hk, U_apply hv (l := 2) (by norm_num) hk'] at this
  rw [← d2 k hk, ← d2 k' hk', this]

/-- the enumeration map -/
def enum (hv : C.valid = true) (x : Fin C.s0 × Fin C.s1 × Fin C.s2) : C.grp :=
  ⟨C.e3 x.1 x.2.1 x.2.2, e3_mem hv x.1.isLt x.2.1.isLt x.2.2.isLt⟩

theorem enum_bij (hv : C.valid = true) : Function.Bijective (enum hv) := by
  constructor
  · rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ h
    have h' : C.e3 i j k = C.e3 i' j' k' := congrArg Subtype.val h
    obtain ⟨e1, e2, e3⟩ := e3_inj hv i.isLt j.isLt k.isLt i'.isLt j'.isLt k'.isLt h'
    rw [Fin.ext e1, Fin.ext e2, Fin.ext e3]
  · rintro ⟨x, hx⟩
    obtain ⟨i, j, k, hi, hj, hk, rfl⟩ := closure_sub hv hx
    exact ⟨(⟨i, hi⟩, ⟨j, hj⟩, ⟨k, hk⟩), rfl⟩

theorem card_grp (hv : C.valid = true) : Fintype.card C.grp = C.s0 * (C.s1 * C.s2) := by
  rw [← Fintype.card_of_bijective (enum_bij hv)]
  simp

theorem sum_grp (hv : C.valid = true) (F : Equiv.Perm (Fin C.n) → ℕ) :
    ∑ g : C.grp, F g = sumBelow C.s0 (fun i => sumBelow C.s1 (fun j => sumBelow C.s2 (fun k =>
      if h : i < C.s0 ∧ j < C.s1 ∧ k < C.s2 then F (C.e3 i j k) else 0))) := by
  rw [← (enum_bij hv).sum_comp (fun g : C.grp => F g), Fintype.sum_prod_type]
  simp only [sumBelow_eq, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
  rw [dif_pos ⟨i.isLt, j.isLt, k.isLt⟩]
  rfl

end Chain
end OMA1925

namespace OMA1925
open Chain
def PSU : Chain where
  n := 28
  gens := [(0x36405861a582880e248971410d0c2660a8e323c9140200103, 0x363438a2058484161489a0c20b8c323c9142660a8e0004182), (0x32507923054713345c69036586110608080122058a0a10386, 0x1e4cd972438b1a2860610325488d0a1038602001821628488)]
  s0 := 28
  s1 := 27
  s2 := 8
  b0 := 0
  b1 := 1
  b2 := 4
  T0 := [(0x3668c982e58a9426488901e3868c16284880e182840608080, 0x3668c982e58a9426488901e3868c16284880e182840608080), (0x365c98f345890e325488d305080c0e182841628488040c001, 0x365c98f345890e325488d305080c0e182841628488040c001), (0x363438a2058484161489a0c20b8c323c9142660a8e0004182, 0x36405861a582880e248971410d0c2660a8e323c9140200103), (0x36405861a582880e248971410d0c2660a8e323c9140200103, 0x363438a2058484161489a0c20b8c323c9142660a8e0004182), (0x3230482205408a062c6941000c111e6cb9334487160c1c284, 0x141cd8d1210b101018617161489a2450c8f040c0802660a8e), (0x3240188185458012046980428a1134487161e6cb930e18205, 0xc2cd900a20b0d082861a0e248972a389980608001323c914), (0x32507923054713345c69036586110608080122058a0a10386, 0x1e4cd972438b1a2860610325488d0a1038602001821628488), (0x3260d1b2854b961e3868c244c811122058a06080800814307, 0x3064d9a2a50b171c3c60d2648890122058a00041030e18284), (0x1e4cd972438b1a2860610325488d0a1038602001821628488, 0x32507923054713345c69036586110608080122058a0a10386), (0x1e48a192638c1536586112e6880d02001820a10386142c409, 0x2638c151e48a192e6880d3658611040c0010a10386122058a), (0x2638c151e48a192e6880d3658611040c0010a10386122058a, 0x1e48a192638c1536586112e6880d02001820a10386142c409), (0x1e402802238186021c612080898d285cb153664c1a122050b, 0xe10305142440b1a40b9a365861100041822450c8f2a38998), (0xe207951a68817144c0163604294301090b0c0c88e046448c, 0x1e5810b2840c0c24242953210b80104c09a361c68a0c0c711), (0x218c96224c812085040e1e2419a2e08c05002c615146c38d, 0x430c8916602122c50b951e400050c0c71102684131a28d87), (0x141cd8d1210b101018617161489a2450c8f040c0802660a8e, 0x3230482205408a062c6941000c111e6cb9334487160c1c284), (0x16205090c142072034d17365861102001032a389982450c8f, 0x1e4408420383820a0c613001890d3664c1a285cb15102458a), (0x186923460c9b28288820e3ca88063029316047170858490, 0x285ca96080869310608801c14c8a0e4808c1e68483164031b), (0x1200d8e18508180468315321c5932428b831014696083c091, 0x32487941210816182c01504602971a28d871c44303104c09a), (0x165c08e18149832a08d0600604112024216146c687323ca12, 0xc4418e34209812a0060b0460297361c50d0840b092848c8f), (0x145c903221008f0464609280039a1034b05362c3102a38c13, 0xe30901342418f0064b8428085110c6c80b1a14416304ca8e), (0x1630a802e14118024cd081c0c311146c68720242161e64914, 0x14441142e10c802404607063c49a362c3101034b051c54998), (0x142440b0e1030536586111a40b9a040c0802450c8f304c715, 0x26302831a48006041c80e0804791306cd192e54a16142c488), (0x424c8c0228a900020898062c6942e4c79b08143863448716, 0x100cc901600a8c140889412046981c58d120a103071e6cb93), (0x660396222cd051c10a080c4800d200451504646091e6c997, 0x45431a00604110238b8b064c6052c24210323ca12361c50d), (0xe10305142440b1a40b9a365861100041822450c8f2a38998, 0x1e402802238186021c612080898d285cb153664c1a122050b), (0x161881b10146961410d0c121cb912a3899802001032848799, 0x30440081a5058312086190228a90364c7971c68b120814386), (0x460b851a2839b083c88126184940030a8b320c4101c5891a, 0x280039a320848c1e04884240cb8a10586852a38c130c6c80b), (0x600101102c5092030a18325488d0e182051c58d122e4c79b, 0x1479006187110410693021c6122c54a1716284093664c1a)]
  T1 := [(0x3668c982e58a9426488901e3868c16284880e182840608080, 0x3668c982e58a9426488901e3868c16284880e182840608080), (0x266438b28384041214a920c28798226cb0c2e4069a020c100, 0x1410d0c0e2489736405861a582883038995323c9140404180), (0x161881b0a20b0d225c487343020a2660a8e2464a0f0404180, 0x303c30a2454485161c9990820a0e36308962068b8d020c100), (0x1c609952c342882404607342418f2018d8b2208a0a325c200, 0x123c19a045cc05324c38b186cb1110107142028a811a18900), (0x1c58d12284410a1030317086ca83026048d262cc87203c280, 0x1c6428a20686970e60b03046c4120c50493084408f1854580), (0x266cb8f3230109164429a0e58c0302545101c20a041a48300, 0x3440b8d32385053608908301c1962624a061e048841854580), (0x840b09260c6050420d921a648951604b8e1e6030a3450380, 0x220c70612646022e4069a0e207951610c120214a1b2c4c500), (0x1a3c70c36500850e645931448b8304683152010b093044400, 0x2e289031a1441620381073464d98223c2012624a06182ca80), (0x2430381285cb1532201901e18c0a2610682164429a1c6c480, 0x41098d2c54a17166c3101e0c49a0e30092323828a2220c00), (0x3464c1b223c0840a484951650683044038e2e186082658500, 0x306cd190e0880e0648b8a2c206851e048841218994182ca80), (0x325830124408931e2419a28107083014b82146c38d2a30580, 0xc40d8b126818f285ca962634202021c90c0a6450e2220c00), (0x260441a22187032464a0f20582093634507045c2982a2c600, 0x16609040c38191364cb8f20545010424619105828d281cd00), (0x2854b17142048b223c201041c80e3660d1918141930c48680, 0x162440a3064d1b080898d2430087285ca961c0c3110a3c800), (0xa103071a44a991004d132c3c10b18608142e0c512126c700, 0x444a0a0e3ca882010b091c04b8b18141933064d9a0c34900), (0x1068981146c687126410c16602120c38883285ca960a40780, 0x2c6890e0c1028732304820228a901e5c99b282c18d1044c00), (0x301cb0326243141c5c08b2a44c8d246c402341060a1e14800, 0x141c69b24647942e2c701064c6052010b0934541063020880), (0xa301930238b8b3634507283c91908248162a18d023020880, 0x26146032a2038f30340891c5891a28445022018d8b3210b80), (0x165c70112588041450111105438f0a4c6033268c1b0c34900, 0x818385345871214048151864109364cb8f1a0c5941044c00), (0x1840a180e18205246c402022c7173234a911e2419a1458980, 0x24105981808499024c41a0e3451b1c0c3112e58a150a40780), (0x1234c011030b86163c11614382990854d8324409910e68a00, 0x12086192a405010a1c2062438d16263cd97065068b1044c00), (0xe142062e6c98f1204698225010a2c38d12200c4191630a80, 0x2c242102e2c08e2a20787282888206309853660d190c34900), (0x362c310240438c045c2981038214340c48f2a6488d144cb00, 0x362c310240438c045c2981038214340c48f2a6488d144cb00), (0xa04a1b3454302162848822409921a3078e0658c070864b80, 0x305c1050218b191a3078e122058a26488900854d830e50d00), (0xc40d8b126818f285ca962634202021c90c0a6450e2220c00, 0x325830124408931e2419a28107083014b82146c38d2a30580), (0x200838e282c6831858d91303c5062454289024c41a2e10c80, 0x221008f06485170c2c81b1c60a932c3440532304822868380), (0x2e3c99b1404a9006447062410c0b1808c890a20696281cd00, 0x300448d3610a83323c914344428b185c406044038e2628b00), (0x1018b8c323ca122028a810660b07341488b1a4c1041c24d80, 0x22cb8e32348950c504932c0c398104811b18685041e14800)]
  T2 := [(0x3668c982e58a9426488901e3868c16284880e182840608080, 0x3668c982e58a9426488901e3868c16284880e182840608080), (0x183478e20449923064d9a2854b9614205890c103850608080, 0x22409131a3070f2a50b173260d1b122c40a0a1c2060608080), (0x22409131a3070f2a50b173260d1b122c40a0a1c2060608080, 0x183478e20449923064d9a2854b9614205890c103850608080), (0x2c5ca15346cc191c3c60d244c811102450b08143070608080, 0x2c5ca15346cc191c3c60d244c811102450b08143070608080), (0x2058484363438a0c20b8c161489a28487992660a8e040c080, 0x2e30406226828b0e2869b1210b101e50c922a4c718040c080), (0x1a6c5072c402090a2cd111018617323c9141c54c13040c080, 0x3444585185c3080824816141cd8d2464a0f3038995040c080), (0x3444585185c3080824816141cd8d2464a0f3038995040c080, 0x1a6c5072c402090a2cd111018617323c9141c54c13040c080), (0x2e30406226828b0e2869b1210b101e50c922a4c718040c080, 0x2058484363438a0c20b8c161489a28487992660a8e040c080)]
  I0 := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
  I1 := [0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]
  I2 := [0, 0, 0, 0, 0, 1, 2, 3, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 5, 0, 6, 0, 0, 7, 0, 0, 0]
  W0 := [[], [0, 0], [0, 0, 0], [0], [1, 0, 0, 0], [1, 0], [1], [1, 0, 0], [1, 1], [1, 1, 0, 0], [0, 0, 1], [1, 1, 0], [1, 0, 1, 0, 1, 0], [0, 1, 0, 1, 0], [0, 1, 1], [0, 1], [0, 1, 0, 1, 1, 0], [1, 1, 0, 1, 0, 1, 0], [0, 1, 0], [0, 1, 1, 0], [0, 1, 0, 0, 0], [0, 1, 1, 0, 0], [1, 0, 1, 1], [1, 0, 1, 0], [0, 0, 0, 1], [0, 1, 0, 0], [1, 0, 1, 1, 0], [1, 0, 1]]
  W1 := [[], [1, 0, 1, 0, 0, 1, 0, 1, 0], [0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1], [0, 1, 1, 0, 1, 0, 1, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1], [1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1], [0, 1, 0, 1, 1, 0, 1, 0, 1], [0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1], [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0], [1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1], [0, 1, 0, 1, 0, 1, 0, 0], [1, 0, 1, 1, 0, 1, 1, 0], [0, 0, 1, 0, 1, 0, 0, 0, 1], [0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1], [1, 1, 0, 0, 0, 1, 0, 1, 0, 0], [1, 1, 0, 1, 1, 0, 1, 0], [0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0], [1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0], [0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0], [0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0], [1, 0, 0, 0, 1, 0, 1, 1, 0, 0], [0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1], [0, 1, 1, 0, 0, 0, 1, 1, 0, 1, 1, 0], [0, 0, 0, 1, 0, 1, 0, 1, 0, 1], [1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0], [1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1], [1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1]]
  W2 := [[], [1, 0, 0, 1, 0, 1, 0, 0, 1, 0], [1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0], [1, 0, 0, 1, 1, 0, 0, 1], [0, 1, 0, 0, 1], [0, 1, 1, 0, 0, 1, 1], [1, 0, 0, 1, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0]]

def C6c : Chain where
  n := 6
  gens := [(1350615297, 138248470533)]
  s0 := 6
  s1 := 1
  s2 := 1
  b0 := 0
  b1 := 0
  b2 := 0
  T0 := [(172878758016, 172878758016), (1350615297, 138248470533), (34370290050, 103618183812), (68987994627, 68987994627), (103618183812, 34370290050), (138248470533, 1350615297)]
  T1 := [(172878758016, 172878758016)]
  T2 := [(172878758016, 172878758016)]
  I0 := [0, 1, 2, 3, 4, 5]
  I1 := [0, 0, 0, 0, 0, 0]
  I2 := [0, 0, 0, 0, 0, 0]
  W0 := [[], [0], [0, 0], [0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0, 0]]
  W1 := [[]]
  W2 := [[]]

def S4c : Chain where
  n := 4
  gens := [(49409, 4210691), (6324225, 6324225)]
  s0 := 4
  s1 := 3
  s2 := 2
  b0 := 0
  b1 := 1
  b2 := 2
  T0 := [(6324352, 6324352), (49409, 4210691), (2097538, 2097538), (4210691, 49409)]
  T1 := [(6324352, 6324352), (2146560, 4211072), (4211072, 2146560)]
  T2 := [(6324352, 6324352), (4243584, 4243584)]
  I0 := [0, 1, 2, 3]
  I1 := [0, 0, 1, 2]
  I2 := [0, 0, 0, 1]
  W0 := [[], [0], [0, 0], [0, 0, 0]]
  W1 := [[], [1, 0], [1, 0, 1, 0]]
  W2 := [[], [0, 0, 1, 0, 0]]

def Fc : Chain where
  n := 7
  gens := [(207509045505, 22128481026054), (17627892253056, 8935144735360)]
  s0 := 7
  s1 := 6
  s2 := 1
  b0 := 0
  b1 := 1
  b2 := 0
  T0 := [(26561157824640, 26561157824640), (207509045505, 22128481026054), (4399667675522, 17695804228357), (137717908227, 4502467936774), (4570394705924, 0xc2800410301), (9003056824453, 21990777913475), (0xc0040214106, 69805818245)]
  T1 := [(26561157824640, 26561157824640), (22093592854784, 0xc3020a04200), (17627892253056, 8935144735360), (0xc3020a04200, 22093592854784), (8935144735360, 17627892253056), (4467579765504, 4467579765504)]
  T2 := [(26561157824640, 26561157824640)]
  I0 := [0, 1, 2, 3, 4, 5, 6]
  I1 := [0, 0, 1, 2, 3, 4, 5]
  I2 := [0, 0, 0, 0, 0, 0, 0]
  W0 := [[], [0], [0, 0], [1, 0], [0, 1, 0], [0, 0, 1, 0], [1, 0, 0]]
  W1 := [[], [1, 1], [1], [1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1]]
  W2 := [[]]

def TBL : ℕ := 0x868c3d87494cb443a10ded59e95f37294c31fe1747699751e2bb43b5b0315d2caf9d743dcd76ae1191b6d38754e01e019870b47d3ab3e16928860848f89b3d1d16d07e5a176229674acf03fd434fab79d15b8905e54cda9939ad6349ccc1eedbd15e8952bd654c1d819315788842c28ba511dd95ecd2225fe282db1c72a3bf7b686d70152af43ee807cb2e251c1740cbd20030d92954d898c553041a6701f2e087d9113b7fe2c8394e2d5016b885142280f98582b5ce99b99a4aac80c443ce4f30902fb94cd416d88ae86acd86f681eae148a064d86a3d5074fc3b29a7b27ad0495aa0892c47e8a8d7143698a8e77916cd89d64f111dc065e2ce1ce9da11a8ba3a324f01579238b5c9eae4edca5ad2554f8d47cf213cc2ec506a6be79ca8ee0b6daf6c4e1609a59492c82661bf901a980d4b91f91ab21a72d23ca66668e1957b74ca3826ee40158e1ed42ed08d38f332e60b4b85769a1fde2a62805eda4165af28bb091e4778524b2957c1716a392c54656a7d349a8a08d359f140bd8caea820d4d918c929644d0dad296995baf2df1ac13a71118cb42c2ca5b25bf3264d92dfb9bfa81eb5eab6f55d91509b0157a0d0e58234ddb7d4b91a0abdb3730d710d415198d03d6222a21210087c18554e1ad649b267c2ed6951d4d9152c081aa29b91a61b51f4c8b6382c341a5a3ea7720a50216a59715639995464682dd4fe4a43bc145a595a85dab5885263188a686aad34fe5d320107a2827a736d91f0c190ed879724223a0107807ecb3434677621b435a471fe4789cbba8644a02c6a3c22daa87d345ca6b4855cadab94b825db2532e8680acc1b1c1b19a52c30e25952a82b34d3565cdd850a59ba06a881b6d7372310161b2abc549b13116112d75642d710a81631951411e68f8a100119faaa005a48422d8d9eb454a774d35c974d4cd216c98528479e430a3cac1ad2cfc70df6a6e175b0ad69d12548e8f5866e5619dadc8464a4e5386c6a47ec72212a1421f76b8aa953a9f6a92a5416186677867ec30307ff6d84a53b6a13d84238f8067a8d81fb5ea3b31d520aa4b6ee64196faca84aaf72855db08286f54370597834e8d269fe8332c9e2a062d52abd51f4fcfb50d79c3151012030f0f3655d2211ac0c58846c8b464f7b4ad35296b62ee1c22aac893857b9f35d0f5994d46fc9e8a285d05050a06d0666047a0e91ad7e788ce22b5de4da672806963f5901596facc5b8c525b09ad8b7f8a0320a098199b4daa40faaa832a3d44c26a274bd05d7a0b507b7c9aa72b0315518e601761c8ed0578db946e2dbda5578da8b6d4dca307ead72e826c8a4696c2ae25779bc69c427208b2d459467e6e91f54d814ae9880c343ce0f30a6a615d5a809b5aa16fa9d1bf5381ae9edb4dfc5e2abf990e448af051b852b7f077ed534583a6574d00d580a2b18bb58694145881aaa3a3cf276f21b72172f564689e2868ec5a151212fd1c1b0aa0d01aeddaa8482d2b74502e3fc9ab2ab0f6a4135baf69f6b8f5dd08d53b19c90d8c1f4013602fb2a051717829c22a92e5bb9791c8f2a8c5dc74d8a48534fa1c9951e2a3b54b7ed296ced2eeadc870a6b4899c9b97476048e5242d7df9738457bb3d12a47382a25b19648a987a6c251db8eac9314035953178732329ec6c926c0892735a5364574c5841f9a53418d33aa48a838680bb4b12a035ba4de14170d1306bc880a2cbb26a52e9d2b967bb90586d48c2720356c501cbb0e01ad88e6cf6a8ad2c1e542a669532c123b2965a4b298215e4e93464a48b2815df4e20dfa8dba028b6953163e4b6f6a191529745d98120c34950523af044acc6be659b9d921f6ba639ffd43caa1c0c6532a24a1a45a7aba4793ba3f633584a98120bb9b60d5d80bedb24634a6293ba81c7989a8d82e10e6b4c4b2c543e29feb5097ab3738c5e006b86e8da0923a212096a3b95963d2a171c0bae9ab2cbeb6c94097a503b52eddd9724308548c29e5181749de8bf160286064daca4a449aafab496710a7a9a866e1d3a3e1bd6eadd3b246a2aea5a0d0c54044681c2d9ebb0d455aeec80726f36637a60a2bb260b17a7a6a691d9c0a8f6789d1d9f04257a9f3cb0e7d8cfd81c35f4dae2a58b3e8b0d1eb2d38ea4dd40afb58c8a470a734bcf270586a742564162c1524eb604bc1b2b4715228c494d75ac2273743d70cc944952964d077c89435879bc06250cb744056b3aa963034f4b8d66fe207ad8131ada9a72b658ee28470f23c213e1af5ceaa876fa2ca09c89851b523e76672acaf6c836debd062ecf89d624e040d9b145a6900a1ad2a4780eb09daeb59385685dbb8130285550448232979ded18a0c5c269452409f4d4cf5672b2a2b914008bce5a67a379205f081c2d85ce202ea20e94247770e4f85a5c0c810da58acadd4521819374d5c40ca00e1803bc9b808db617c0c6d053f164d7911636088c799d0be16e98d272c0285be8b2b328040ca9caa60b0bdf4d0764176d5fb594eeae97b7ac229acf50966e9b4b60efe2929b48d73906826303270e097778ea0f5c7c71163c43bdd83d152eb743397654866ac6351a7a0f5bc2660c05803bd2096342de2d88c9fab68dd57f62d791d1a29bec20617bb44e255e152e5a14b64dc263622c21c46c109486056e9733576ca430b5caeb4895cafadebb8245b25715f080adc991e5be6edf38c5548b35aeed5ea5a07fda3760fa9ae7ed740d38ca281f65f080fe861399ea2dc8492cf50975490a8af753eea41ea447d14b4b74c51842a2e9dfacb3f2c1e4e2e254544e6a55714b22399c6bb2e5cb6a21fc20fa0805bd71f65ae6a9e089d27423e381d12876061ca2039a988a209525669f68336e142a061d868bd51b4fcdaec973cfc145e50ea85d9b2bbd206988a086a9d6f022b6508d8a5e750dbe958209e2833b41edb3bab55dcc212c27bdc33b593d8d1ba3a5eacf1c54500cdc793ec46b1a0f07ed7a6b3d39f6c8d8400804069a7b0e7500fe7a48a18311fe4afa058f843e9cd9e944d270d9548f98e46e9c81ac3bd7b52e8f50ccc79fd47d7151cc33b5068e9891d994e0b3d42cc1b034946a6cba592e99f69c557266c9af28ee1c16790c1581151ecb560715c4515134bf940b78caba2a251fa18c9c9641d9f1546734610953c684a401ff01018e9a8876527271e90cf9055e84b5bac6cab0e57a9a344855547951fa066eb7c101fcc7b5aa4be135f0c810db0837da016edf5b80d1cb85e46df5679573ab19be1c3e9f3c8db27a23a1760a1ecd01f7420e0197128f6e014500ecbf92354810282a3b5419a271a4a9c3a7eb5e5c54900c8c790ec473225907e8745bc33d5cddd5491345b2afcd292a88a859f5ad739c16f90c555b9d5b4f47df15c35557d1ab769f0881c66badd4966881087046922ae4357216e51d05462bf91921904eb9f6e21298d72d6a6d2e96ba12a3c3638bc4e6e4ede9330ad4e6658b8d8147b96bd69b216182229c3b4d2764fc021b4204e69ac0dae0c394dc8e6fe57452bd210e948a60533c55ab2ec3bb295c4bd6950968814a55885222f3a050a8a5ad734a0edd61b8aadd4985204098191b727a6952aa9f06cb460c6aa169f8b5d00f6cd706458ff540cbb0dfd1523289940bf8cafa4b751fb987c69645d8a52017f64c70b3446322471b13a8f5ddaa7ed35a50f83868970da52f0855b8ee8f67842dbcd0c446441b4d5d05a682555032a54530a1563e18f39a582b8357416fb3707685c11c6292384d1c054583571fa2904dc91f116521eaed049a666ec0bd57b14742835028a91c79b8f115445313731624d42fd69c581e75ea9b37e52cfa4b7ae64f96fdc387c4b8200f38086c1872581ea337a5606b1f2972f4b9760a8d872ad1399e830d861a86c0c03582aa7a7a90162cceeb8f4b5cd67a6822ee99ea08bdb25eaff111e4cafba1682505da2cda106a039ebe9f5c52afa7b4afd1c2d478715ccd285d1ec30e81afb4b7455952f0d4a9764c2805ce014b2da048d74cdc34684c58e04d2ca2a9811d1683ba556e1b70294b50b9474286c519a66989ab62255014f06a2cf0452b72488e8c09a6dc65fce1af1e212876ea8258a7218519523f7101b37f52a1b409bd7906454207ad0e57c3f444e1900a7a98c45636a6f9953f8d0b69f0bc015c189a043d5946cf32dbd1a7165972a3207009194e3b3603b29c8890836464dcc32d34bb0adbfa4cfbcf2b05a0b5995a02b1dcd54b79529a328dd495e881251055ada273344070cca441eac8e1077e8d56577164f89a120c813d2cd2bb7145278351786a215a6040681c1d85d65cee9096915572a5447c09f4f4cf469912b3f91f408da853b63b8172c4f4478425b2b4b1ee4ea0c4cb7a43c46597688a7b4253d5ff505fa74477d0e0122c08787424339317ba930388ba59f6a1f87011787e1b938e1ce98406af30a3d633ce6110eaf9e14d4400e300e788128b4be573a292bb1fd7391e826f06a3045077796b0d5cc931160c87b5aa5516a8a5d9347dd4d1eaabd55b5a101bcd0a0c038038da7beba631c0f736ba4e422b655cdaad07452ad5a5764c2883e63612253606cb3146b04969536eda2a54dd88ee8c691bc8c162a050eb58d2dbe924989ef425229aeab6dfd013e02ff1d5f121f88f1a4c9ae5b99792c60f54549061186447bcc63b26d149514bdb8bb566f5f34cdcfc1496859a1a48965243b9351f120fd469ad017d92fd405fb073d5023a2d863e2c0dea5f9ab9452cdc86025a4c614132b0506bd81b6aa8464882e70ab297b094b4f2ad424c00ce5ae5498eec355abbaaf1f578f68b7d4e55a0a31d00802fc72131eade2ac4be6400ceb489e286e069dae9a9ce9c387831a5b7bd348758250ca753ffa01a720eb80bfb56f65739a29aa373a393aa3c961b885e340c238e9f1496a62457469bbce95bb0bc2781b34c570bb0d133d3e460f55e28094bba128a162516c10aa3d425427934786a6c3a2cbd3d560e4446ac6413d9fd29f698d61db4451d55ca3d83ef4952ba289ef27b3cada5555e354308c0a1caca2b3f5a1ef4a04c01a6bb7102cccde3a7a2d48eb2984c25158f85afbb16128092c7d56ab25404fafaab4382d101aa4b13861988a5d5d689572963a4e6d92f1a55105b70b3382ff4d5f8af087fb43a3b65a0f199c01a606120dd7a5607af6d425aa3c5434ba3a169ecb1a4567eea8dfd439367c3116a564064e291901604ac872b0d951b0c4bd073ec2c4a1a1c14980c020e3e8300836d3640e0687c524588b38872cd4559e1778d5947916395723451152804cea92d063ad719a92de1669a176c852d5e11b7a9d4b70dc2a678a3fc9151eb3cc52a5c467d9f4b54912044e2802cfc1962040f8ac9c30a2d4e64676fa8a4718aaa17c71e1b51759023aee3c967c43464f528707b425bd5f7505bb08271edbafe31a0355af4825b8a3e9394d23e17d2ed80140e3acf4b706b4593628d42d9481841db200758071c3d629b41888306221aef3aae958b8a0c7c70364e6eaa0c89ab7840d181f64288a486028e05f19644acb6a15eea28a191d54f55413a8b65679794c27901e2d7f6ce94d86b5e9d0c0b6d9703d651dea1649223ead4e5b0d255a1063b09cfdbac65c9d870ccf03d454c263d00a3aa7b45e5d2b26dc0fa263c333ad93d16ce923f59b5bcf81c083a0c7dab62b7ab5cad6b2ad038db3df4113ac29586151fc18abe9649d2ca6b6c14095a594b745ddd9f0d4c8549c52ce54a2a360ad2a63cc4c0d6d7bca5107315d5092a5dd4975a547400eb463ae600c36cbd25b6d2b9430804ce504dce43a17c89273bbcf62c5918e82ec1d83d56a88bd9b0a633b7d28e34037d4d1aa81f0be74cfe67e7ea12e289d43c1528031c8c9a730595a45b3a81463e0c0dca2612d911268a9495544ad1a6f47e492226016e80b6e0e3b0395550e89b5207494178ae2217a307ace755a28d548ef1cd2c26d5a48dafb32e728093c049e980adda6a54ed88f687751af2c38ca840abab69a41b47180e0e1ff15cc8e1dd52ecb967dc031a068db7a3dc9ca8a696b1651720a4f4299097d431233b19ab33adcdc5ada8565997740a0c4dd3de476797ac1577dbe3d7f4e554742b28e64546894697177b6ea24b22b9c80a0d8862b48a2dbbb1c1a1b6bc87e4e1774575a4d63e022c4f0507c727e4f79a068d131db7fd4b7e1b84ea5a39b82beaf62316025d2ef894420f30c8725bc9dcb7f23c29793c05ee5cfe0eab0025c5e2da2d7578bb1aa5b5fa1c8ac05b882ac56e654968fa0b430605ed81a31f1e9076cb4b6a4b6986ac4b1442f5bd06689d10e545e3ab9b9539488f4474d65092e35354f5d6fe28e972190a15978b328edd08d28d0059d129831c031864e5129ea955a84f83d268a4ede6b2e8b7329a412e5bb6914295ed71f354e8295e350b7a374e80df02b3153977466a3c1d6b91198c05ee9ab71331014c7a4fec165d71b1649c6519ad316eae894abb59d273b07ccc86c54a449ae6e380a3607b60e212d9f0acafbd2e9ea0e2a199663cc34de5d2a0109a0fb7a706d90f2a6907727745aad9d528e95e54aaa28b95436d9342778423c295e717370399b51af6ab055247aac039f0308c5490e456e8ba35836f52de7574d591b611288ad621dd4f454250c05dc8e262229cbb296bea02eea3d62da287d44b84e46d763ad4f2cb19ae33faaac48b7f7b27db9435725a97d5649602ab192573304281c1650a0914f55694b41e7ea05aacced1b241b01a28c30e655d9a82ab4d3d65c9daba5466745ca953963dd401e3010989d4832240e1a09a19490c8276225501ad8084bb90a210300cd8840b28b30dd12e864877764c2207d8d5db29ba3cc42126d0e48510986ee82d6c9eea066d42cbd50f4fc7b6ce7234a8ed565be8af74613a296f467a966882285032b6e6c80fb6552e54c5931cb518a7b1ec8aa0d9b43ea594b64f7aed53421ad582c5b47628eb2bfab13ac819416b9430745d30cf563e588cda1f73835b416bb16a7922a5bfb264b8addb5dea81e35eaf6f57d065604a20e9ba569788fe22a5de41ad00890ea84a1c79d8df058f23137f0d40d42dd5006ba811ed280fb81f7b2845a275a4a8c7d3ba812292066eca7fbad25909848a0554263084f14eba6bd664e618f2db0d50ccd7a2c51298e8429485b6d282bb48d965cfd720acb3d114c6369b82a5561a8d735034a422e5c9d0e9f6060c3cc3d89c97bc8510673241a7301f8e082d3bb3931e2c8994e5d0415bebb2aa280d0c26ae5afa1b651495c0dae8ba121469539882caaf1d1cda869a556cdcc87296296f8c03eebd4f6beaaf53b877d27230c92c99e54a6c8f6ee38aa3657ba16d409a8d98b036502e83f211fc8a26472aeae5ad2f2ab96d99aa48fec15d8c96cb57d589ed64db264c3616b07d688d50d489f9e0985613ce892552dab53912868a665665421ff6286a583abb4ac801416395ca7a01a8f230d4ca261797365c9f63c4d5ab60d9d41219390e9ca1b103b5b518c750cfc62fe0e19df348cf8a769dcf7762d3935ba0676dc8681f8d73041b0534b15bfecaa1ca9a2016765a10b3342efa38f3111cf404a2a13be65c163a0d0d464d0ba16132d1f6c0fdd467f44c28bce6a2d401f7010589d28a47a524119e2a8ae5269bb3de94087491874792e522d2ecbc3a29ae97194f3747448130c033b1bc2e749d59143c974fdcf11bc657a1762e1ed301f864ea40168d51af1167502898588794059cb206c9311152c8f2a0305b4f340c1a3f854b039f936a89a79572ecb4c5f1c2fb03567479b705e5bd0ef2a5adb1cf9540d85f0a42650d6195048036d01662722d05392c046e35a8455789a8b4d391a23d51bc0adc55b17d537729e9b68cb8f8d82431b0c8bedc15a2c8e30a33499f662d51d06dac7afb6c2a3a1213243ef152abcce452b56cd4ae9b238ba2891cdd4309ca9252b77077ac7d3583be1ff100d780bcb1286c69dac6790d1622c29001ed76a01bc96f63c9eef218622401263b1a2e7d00bcc2ca5140d93944f578a27d279b607903c254dcba255e791b792d051e072d96b0b733ab4bea706907ac67241e2dc39657a106c047f1a9c9160bc94e7429f2b7f5474981cb788dd80935f51b37354383589c5954a513815a22a8b5eb310394602d58edcf9395c54a4a2d229664c8bca4a48322ddd40820dda5d9a24b6236a80a3dad5a97622db9b1c2a1486ac890ec2835886e66566b4eaad16c68412dbd29a47b47280e163e3d54cce1cb5a4ce141b2b0103db8220adc5e5e72e88eb0e5a2ce1a23fb16ea2a7dacd14a9fa090d34c6c7eaa9a4c567481d2c1cb4059602cd9ef3d711c037a06bdb7aba2988a468cbb6356639ba0179a35873f83b3e223378e8dd0e5c00db2308e6ead3295274ea5c94429a87159d08e622b3134a02c527b503ef64ac160a2d81a2cba2dca0396be936e26acf5bae034cdb10a3a76c66e0d3a36172cf2df34c72014b57f516cb445334e19958baa9cc6acdc06550e125137103d57295a52ca5ac6c8d3486d3a1a7b1cae76d589637d53e2865bd014b0322ca2e51d5a3e668c0db1fb6b205b7a75653a89c53503831b4085a3c37331a141d2b4ea78a5bc6a2261068309ced4df5592b640c88f069162b3db4115608ad53ed4bcedc0daa86c1dc2ba292e94923e5790e395307ab0cc4804d6a9210682c4fba57bbb4d94582b3c8c36ad32db6e4305d955af6c803274560fba317aa5820b13abd0a2a563a22eecd94be4024e965756fea6acb492a52de9f00e425c147548fc6090e72367a0b5139e4544bd04024e3bed190790d9b4585822b2ed287e3c5333145ea4e7820253d5c2956597489beb81e3d5f35059b081785dc5d0e00e58039c8b50d4a628a8c6d250216209d00936fa3c4c1e2c8999d6b0e3a77064f818f74c812d20aaaa094525819171012070f5af30c294425242e307fef73aa7d3b3e9289a711f1267ea59a16c82afa14703a9965c18d926654d438f15220d4e07c3916bd7dc323009ac5fb38ef62d299497d01ce8d05cdc90603c093d2a3a91734628a69118dd6d52e8a9557a443bc3507cf161c2a5bc7c6140a6cf6a67f2c7c1098e8fa1547943b5d00b5b14d474d3977922b34e3dc4cfa8f8d83dd49cbc4d758d91cd812448596cdcc8b0b3496fbc03e6bd4366f2af50b3043262d55458363a067ebc45058ace0fa5e052f0994b44deb81c12b29e0559a798a5f35dc9cdc84b4084ac3d40d6935d441aa0596156d4772f62051f542ddaa280a7b0d7322ba354f148d5645453cfc30426b5515578237150860a65a50da6c61207f0833a48f14307e00f98081c109a1a9aa33da5676581bbe69c165a0d3d924d0ce96684d1f7c42265a31130f6063c4383977ca032851365026d9f1142a82c582a133abdae83b46dc59c54a52eab9b16ac387a1043270cf462a59f39d2b419f811589b23c4a222318f24da726d355ea631645c162ba99a0d3b8081d0a753642d64fb265c2ede8fbd688f4e80871bea749a429910c61e5e52f9422af736565189b1957acccb1834ddd8e54b9da0afd866ec30b07fb6c35a7746a135842186bc6ac23c33b18c149c343918c12d83614722764be3ad5247d60afc3b3ab9535bd56b97d9c0435a6292984d4c069d834f11248fafcaa2e9f976454f6cb703e5c28d40c7ad3dd5775590f586a8bfa621ed4f59422ac05ac946d1aaf5938973061c4db2be688f087744ea350b366d6c4deca0328441e974a3cfc5eca17648a2ec79f7421e019f0e95768b4064dc37340cfac275767b9f836a81b2c0794b24b5e1188805cda41e0ec6a9ea870f708834be140b98438a47ad1fb588b89647d143b500d0f6340c9d263b546e9549898f556e5cc93082496ffc03debd5b6634ad39b3b0aae4757236e53d054e36411923904dba9cd273f2bc6cf95536349aeae890a363710ba86df112ab0997ba52c46d13e88e88581e34fbf2d4ba3dc61c56478ecf2b45d0d2614590329a0f4e3d34c60a1dc10ba73e888f63f8e1e47abfa76f2384420193874cda45218091408aff658cfb9f9aa3e06a058667ec21e0f3d4c3b591fd140220964d3869f35466b442e91846a2ec01ef010b91e48b6ea972b4d3f60a9d3612a53586cb0ca7106be555100b9704fcb5cc524f09a793868abba0a1e27ac8a03d6e7e8fb9895792ec61debddb14abea0b4c8a32951e2da5b026a370b0d4563e38f3ba1f7b835f4169a62270a552be2ec3fb297c4bc6b0694d994795835e55b128af94fe1ab79a9b4adf3c72ca42efdb2a910e10513982cb1abf531b4c9b4a32545a9201f8db078da6a4e6a527770ac161e589dd0b69743a96fb86da94b6cadc15e122bd90bc6b4e751a8a13dd2a790a58d96fab79d4e4c8d0042ec64dceeb5746bada2543d1652908ca3bb496c9991258cb09a17b23785a235b3dea2a55bb5d4a95a097d4a6524954bbf0e19dae522ed9249d00a6d7915972f23ca9797c05c6541a12e90020c99bdccb69379888ddaafa2f431ad2ee69a0a5c3485052faa2a48be6cdc18a6d8753681ea80a340517075d2b1241ee8d3fb4d5672b22a3d0800b49058f80a2dd81b751f175c6cb905c6d4b156b778e561e2d0f0dc3c9602b7fdc03d83e35a31ec351a22591a2641665ae50e496028c5e06b706d161a8fe52eebd701c03da06ed5f03be78a8ae836d639f6ca960f594ca05ba53871705eca9605333b452955b79520a037641cb01716f894144629354646f1e157f32c36520b289ca592364f69ae86c8e5d28051c8e1eaef04b381e2382604d08aa5d1e93d70d0fb54f86c5e142b70a5bb4b96685268f156895484f8b88bcd73023d454243f8d0d6f0543b4b0bbc528c8d997f40a6cb93bde57679fb4727959a052d8063a4e9a7fb343c2940389a755f5e3ab9292b6097c91fe39b584d0af42a43bb145a195aa5d9197a280836b4f6fafdb26e577a2933a81a798a2af42d94e6b4a4745e9fddd6b7119ec05c69aa31cd3014b79705275aa241569da191c1bb76cd0e031c15068d6708e3672fa3a9b8fa922ad535fc5f4e5cf9292d6095c91ee39b98548a51fa1dcb1f5155b38376a036641cf014975d7493f54cd6d11db42ec60cd1901d7a588a64ac82ad718beb4a00c0186d0c1048acde6a2efb491311cda812691f1bd55d3910502a392223c515ecaadc51bd5176b1573adcfb01561c9ed05f93a245e15a85d5785a8b2d6fca8a2b0a70a1d273912b101086088f5536340d8e61c49087bb49e92d92952d08ea1e9bbe132f05514745536bd7e0b1882a447d6eaebd4045ad56b43bad11d995f05d81508c5c4601758022c2e4e14f92f2b9795b2613ba016112a01ccb1db444f2580d461d613bb049e79bb796d0526074996baa81ca853ea1360d8d447855ca32f089b8512dea87d2a981c38d831d538e51cf3582b10865463ec8659e31916a6515a1d9d048b0295d2eec4ea76212b1c6a41ec1dcd0149b6da48f83d2445408c0d9a263ad905179c91f158a339779c0d9a01cda94b40510c44545470115c1db4055a4ba534ee8fdd29acc892a2a5edb51412ba54bb18ea0b86a237ad7e61ee458821b838ef0c3224c552ca46acbb767ec467325aeee89d57bc02eb448ae6aac7f852d1a83a353a4a0186159dcddda1d28a4c6bc45cbcf164ec6c31cc5d662886c2b69c39c8a247e6501a2df64eeb6064c5de60b133b6d2edb4033d89e2a80f0be94cf8638caaf076d2f68b1d3935a0bb2d768029c2ece1ae343e14babb47922bdd55bab166491e6147a84aaa998604a65cfd17d591f6b749625d1d8349430aabbd8a8f46b584a1a453a37fe96e2e6b4c447ea28e9d6b69bec87d201b720e180b9b56d657299188a377aa9a3b6e548b8a01dc1eb3444310b2d462d90cc4bb2004380b9c9915de53219085cac8536a1320d8f550456f5b4b7c9b830adda0f1b2d71414b8cbca4493cf336f2fa9be71b04a522210d66c44585d4925a08c9690d6fd28a2723c6a1e374e42979d0d3488f456910b2bd603ed0f68010ebeb3559ab11db297bbe17297f51464553ed04e097482554a483c7c4540ac0daaa47acf311b50949159ed4386f4eaab1c7a61ac359d014bb63948bf6dc458a6b86226593a25e502c50294daebab27dc38f83415754d3d03512b10875b5ccdac5e8a6b155b779e56121f0b0dc2cb6aa952349a76094d59e3446347154341483be80a6cb18a029d8ffd3b618ac0869cd8b510db50da0e4416afab807740dba5df77f94467711eaee8ada61402e742c4e6a9c8f25424a87c14659a019e2f39cddfa1e38a4dedcc1da59164fc9151ad2967748f40b50aaaf0f5b8568b3d4e75a0b72e3a802bc5b155d0ed119b42ccb75d5af9cd6d91564a832d126a14baaee856e92b7e9bd4d6978011ec47ee6eeafaed28bc21d56e86279f67f1a1c9d1784ae6959b85aae34bb79629a4b0201bf20e380a7b56c60ee1aa62b523a9e76de5368e2e8a67bc4a829f0f1342f8681ea114204ae8aa4d8d3bd7010ea74f87c254b1ce9540590f3aa3a505819db48032d90cbba432d1b44a6475d50d630545a745b550d97230c489796c05de5cea0ea70023c391ab41d48d8865a417c38a2f273aa62252eeb16f72771b03062ca1b4e5d3950503a7a0d48fb15e0c2575a4a5afa327c08096c324a807f2d7ea608774030f55a8c1b111cb48ebda2925acc5c46505b2c657ad06c64015ec0f160e9a023b3bb31a7b5eeb44ff45454b909d7ccb55fb7796561a0d730dc0c2cd3cf69c0dfa01fd79cb110526e047ac72695825b4a93ab3350b352cf983b69119da48bd240516cc0d8a3062cc892cd091f05ad7aa536a751a5de8053ea0fa254a91b047cf33c6b118ba974669120a5b5e0281608a3a43d075946aeaba7c4a876d4389873e74cfc1aaf02c0e0bbd7446c67f19fd126371b25c518e774b317432cc526b5318f64cc17c400cb2a78e6ecdaf3d275e95e953a7a5342be8b59e36076d16ba450ea2c3a45062803c1220e44749da2cfb26b9a225b4ffc31fece0193f789b9669622dfd26c90056daef3573954bd940ba8195b2bde88f251758dc53e6956130e4fd6cbd0b23067fb219b3006aa1aa91ad4c24226d2c9d46a8c056c023683034b54f5ab7b22db329565fa941d0c4455b10513b78941dd224b1528eb23f404f5b3c3411db22a5457d23d5a400964ed732229692470a3bd5935d57ff1003b724b0c4329351b5b409ed793e0ffe234f0e52cb93c40eb4bbeb717a736bcf3705aea74454a7edb360f4543d3575bed70aad0f6451cb4d296474a0f604fd2a7652e12ec18e8db747bba3465bec288a88623f531f0aec6da64264b8d1909604fc1b034701252c4948793a6144e83feaa60650259f9327d6808ec9cbedd8b610ee84d73d643e7ed10e8d1b9967b39060f52b156155a400ff00ed903484f42c4b1a1c94984c02363e93009f759d414b650c146a8f24558f16565b68b4cd866a11b8d931a554d5e40ffa191d167901c4d793aaf295f4e8ff74269b22d899eb0a04a88050f05265387687b45a92c5418194057b4960ee62927b1fb73936827b06a90e0d74b9527b6ab675559a01fe9813117501887496bbbd762cf95e389c31d8215cea879abb3852cd2dd6ba450cb6742f5a9822b085d3fbb12a51375564cd6796823361a2a074bb8babe8f59e16074d11e24e2ea2c1b413619ee8b2b09756bfaa4add50ef4b55156452c86db2d409ba505b52d5dd8b2974854cc52da5d31077ca5925b93dde236bfb92c0aa7ee4501a17cc915d39199651e47f149ea3016c89297ecd2104658d28a94478c054c14552b719d1aea5a17ebe341290c896877297c45561ca78f25c0aa302736e394df944fce22899b60c63dd3f6c207d00a9b38044a06b946ead0ab2dd68db81134185a6a675eb2328c9e8ad44a79c6a49cac09b8c87c11e2cf3b232cae6e7613c1b428bbab03bd3cfc945dd7b2b4f5b2f3b461694b991b75333a412d1aa0a9f455ae2333902a90288d14a63b694478f4b658f1e565365c8cb096426237c69988e367c2152071f46288de18502233e12cdcb32657d3c152991694a052700ab4a9c1858c5854d7391f5028f5328c9caedd8f4e84eaee7368445aacf5886a094c3e17a299dead0067d3e208500898054b18a29cf99e6b5277cb13a22dac11987e7c03a600f72e8f07688b7ab5c9c4f50acbb811e402731eb2e724db49e1b71e923a3b885482d8210bbe6510b77b6c5971a9d12497303e427a007ba1547545518ba82434a6aa046e90a959e3a075b860a177eac9bb2636890a0157515b0db24b90b2dfd8c79a9facacaec2518ab18d1b6959a8651cb3ea295cba53081564ed8f34a3f360237116f776c42ca20ee12bcaa74a5145e8bce0e2c8b5d490ea5d870a9b8e8fb2c9e964ec099aa7b502adbe9b232c8045c45faa61b0bd74fe3655e2b4a5c1839261555a38f0d2c414ed9c03ae00f3206d10be8b7a322985976b6b18454228152c88b34655021281a89a4d19f8060e81175c52eb0974a1eacb35130ab2cb283a8efd5d1a8b614401e959e957775fcc426a3976a2a4efc3c868a071b440a8b3e83692558ae6d7345489ca6a13dd946f760d59ad83fa9b498eb4d4a66b04957af4ecf881858dd150ef25167a055358d5a58ca5dca1240f4e1e498e50c6fd230b2813ba2f3616223d7da2c7a103a03aebe835c5cafa0b29d51807475c86d9602ae06519e02acb2a1b021d089962cbd6797124372c0998c86c38353492c679a2c9c7266c5b152b14d8686dc553c1537d1038d9e7e20855330e2c456baa52ca8d72efd6c144d3a3c54b6eadd68a1b53f32221a768664ad48fa0d58e9ca377bed2a5cc9d1164c80c5aa491ceab6273333c5a4317e2f492da0bb8652013b8725d1125508e971b521fa545400f345e6e606c68dc50e74e1eb1bba19f69fa28eff62cbc843951210d8ce3636642e013b29cf6b0340275be970e888047ca9e2a61721cb4b2767e164541d09e86e1a0e2eb5fa245483174103b4e751d99409fd7936455a07a50e51c825c140dd92f49c83a7f6245b5568d5c4645bd152d9f4e4cf4845b23945668aaff64288549d7193ec3175047e38e50fcb8a05bacbeb07d8ab385aa676da8659c824a297c9cb6dd87652ce84c75f043e7acda08b09996f30a2e94b62a5a71ee3d6ad0ed54fd5c1f75458b458c8e0967d0ebe86c0efaec6572141ead984e2cba581ac01df007d89ae81e12440ea17ceedbc5c6b830f0ce4b7215515a865988994057c843d47f589d48603d9e660b1955e0f59d581ce9779591148a6894d4421b68e4a7a1a6d3650b6c58b4eb6d103c22710515b78a41dca3d216236b23e402bea62d1b6087ee84fc618fb5b64c9ba653323a3d0b26a66355e6557fb2f15aababb225a50b565dacc958863830f408fad8672ada4b5dac9faaffa047d991d411facf3d35025d8f0a9f8a5bb2c96964ac09db3865a23ab192e1ecf01f952fe1965a36ab66ea103b80fb4c0b86e188d1542669ffd555aa393ead81c32d009fc5243d72a2d239490d54822a49595566a6349638f9a22cd8ef4d11e50f4d2501973f71d461a9ae9ab499ad6e9e9a822011555f54d1e9f0a882b640ec3bb438a50011a8bf4a26e07669946909077f1bdce54ac4a009c570d45a74c49084d54d06903f2b3b748ea8ab2cdae2a35b00ba4cce8eaf2baf64dca224e0f5aa8e4973e74262a8468f4db16c827fab401db0ca00ac9703cacf0c934ca04005ed3561c548cef43d26be6a15c7484f5584a958140178b27784324e0a8f74f44fca6b454f10013b7134aaad304908918eaf71d4e2052ddb14998d5894374b514ea87aa206e1c7ed82749a2d8c7d421d2565945d7b002002b53d08ed888b46be66110b4d5e5b9c28fdd4011912c74d0e903324556d45a4532c0162a31a879a894530452505950271d5631ced943499bdafaa2fda22788016d74c6d1d1ad5d8b7164d3a005363fb131d4b5663a6b5ad2c895639d20057691b0bbb4b56e3a676d7ccc1569bca1b662b208017d74deca95ad5f86406b66b29db2d1dacc469982d309402d8ff6753a65b39a2a0d68cd5ae380532420b7475767b29d72d1bb423657f28eb9402b8cf8700be13a94952ed90594d34549ad1faa77c06c40361c1b120d860e3286e5038c81b9514448a218510e288854bdad32c6c048771004d805aca206bd03967dd032c88252cf14512c0329231b10c860b53e731987b599ba83396cf2aa5462f4408dbe134c2394d0a009ed65526fe8a488a38b5ae5a8dbb431c1d5a804b2e86aff278d262d2762aac96064095936e85c78f85d1eb2365f2e74f12ca7c2dba5e90258cc0dbb9ea285601b55ab8b65b08830c45b424657c2c85140238cfd7a19651c98c88c26cd9bf200436b2891fb8311e8ffda34d8ec9600864cd559fce4ef5a37ed7b5a8678c12600969b72177a89a344dcaa1fe9233a6a68a44d3e7b1985ad36b6cae4bb1d82883d3a66e50b871f0da979b238b09bb5124d430c39f24c6917e30011d5a46c5598443950d6009e3ad556b6e56e53b3db2968c218f87d60aa16c71422e3d0a8a92a1faaee5ae2983e2d20431983b598ba9ca003b4ee50ec641c35307ddd6d8ca74911438b90019aceb475a60c9ea10290947a6945c5d001ba7d8475ae5756a10492e4745d2003f69a10a684326d5169dd6f8ca644405212962d5137ed00765cf95644e5675425acb32a6f9af9e8a3e299c9e7c0a00cc572d441d66e1137dd006e3ab95a0ee3f358943dcfd47e4a00fc967d4dff4c450d59514648a318518e28c8548dda96d7a04510106f3837a01bcc0de914ca8a550532829551b01a1dcc01f6011bb58d91046de772cf215aeb09b09bb76cfaac3b08bf194eca37d843614eb69d14c27ba52e9d0992f59580643b557b54b3f1371d0036a06a15928f95477d640c1d876959ca229ad78dd60aa005c11bed89daea58ca366135c0c7610f8d70a51b6d619a3218744631159ddb584f8781a0026114147ccf2e55816a3be72e86e111a4362001f53190bab4ae2421de9adcb372d3273ce29593aa007c40938e1907b34ef8c9b9a5cc213368005d80f54dcf628709c353ba6b09709bf6f11aac2308b32104ca34d29c6c21721496e2fa344b5d4f210ed4a7d788c4dc10009a99846b6ac50226e1b01fa6a73bbed5938a006c8193c0bd07b54efbc11a6d60992f792966a365c0cf61098494a15b6b0930a7176cdab10346472102ca35d4872a1ceaeb1b14684cf24bd1103f0003d4816966a203149c4582dc3e4d0003abaf4baced70220374d69540e43e410005aacd442daa1c29207b5f584cfa4ddd20b30000d8c73ac0d69f0a003cba3bd42507bf4d8ac97128f8dc0038c9856c5e566a870490357324bce355936a002c81a39719022f456cc309513890add903677a43800308aeb2e356cfda1dca625636010d8486c20360e1b0698bdaf404a205608b0dab86d6436ac1b58144206c10360a28852209801ec00172cf3027c01d5c08940a430c8282f50250808f5053c0089c0eb408f30bc282e5025a808b50c4a82d542f08071404f302e48051008da0b1282f5426e80ac405c30139c0aa2004a0ca28141422a80a44027980a5c1710074a027a864d41788110401f5013a00e8e0b93002d029d809ee05410a9205854178a0cd40465023d8148402380ca205654192a08a402a3823c4172c006a05fa8605010481285014c029c811f407560d2a822d032e80a8502ac023dc07940b830c8a82fd02c2805450143829200a86077a0452859d014e8197505c1008a00e8c08ea03d2865900a08184502ab813c4148c007a01aa860900f8811050cb281c542cc80b8402a9808dc1730076a02a40279c08f40a730be280d502c48055509ba82094322808f4011b013c80e90055a0c8201550158a1825047c00a5809b405420c9a0151019aa181504f4008980af405520a9281f142f8804f40143023c80eb004ea05388291c007404e608aa81e9031280b85053b82e440aac001a05228611019281675052082e1c005405460b3282d5034a80b950aca02a1014ea12d505c0813d800140b97008a039501caa0115003b801e400ec0078004a83b9401280ee4000480020000e000606c2800141b08000400018000800020000
def reps : List ℕ := [0, 1, 2, 3, 4, 6, 8, 9, 10, 11, 25, 217, 242, 272]
def repOrd : List ℕ := [1, 4, 4, 2, 8, 8, 6, 12, 12, 3, 3, 4, 7, 7]
def prods : List (List (List ℕ)) := [[[], []], [[648], [39, 164, 3843]], [[2, 649], [58, 1142, 4437]], [[3, 2974, 5812], [219, 1947]], [[30, 2783], [13, 2161]], [[63, 5706], [35, 2801]], [[117, 3390], [36, 2876]], [[9, 1733, 4552], [609, 1752]], [[97, 1079], [16, 5640]], [[18, 3354, 4521], [18, 669, 3603, 3946]], [[96, 1129], [1296]], [[218, 433], [387, 770]], [[313, 5537], [242, 1231]], [[333, 3566], [277, 2291]]]
end OMA1925

namespace OMA1925

theorem sumBelow_congr : ∀ (k : ℕ) (f g : ℕ → ℕ), (∀ i, i < k → f i = g i) → sumBelow k f = sumBelow k g
  | 0, _, _, _ => rfl
  | k + 1, f, g, h => by
      rw [sumBelow, sumBelow, sumBelow_congr k f g (fun i hi => h i (by omega)), h k (by omega)]

theorem orderOf_conj' {G : Type*} [Group G] (c x : G) : orderOf (c⁻¹ * x * c) = orderOf x := by
  have := orderOf_injective (MulAut.conj c⁻¹).toMonoidHom (MulAut.conj c⁻¹).injective x
  simpa using this

namespace Chain
variable {C : Chain}

def checkOrd (C : Chain) : Bool := allBelow C.s0 (fun i => allBelow C.s1 (fun j => allBelow C.s2 (fun k =>
  ordc C.n (C.ec3 i j k) != 0)))

theorem sum_grp_ord (hv : C.valid = true) (ho : C.checkOrd = true) (F : ℕ → ℕ) :
    ∑ g : C.grp, F (orderOf g) = sumBelow C.s0 (fun i => sumBelow C.s1 (fun j => sumBelow C.s2 (fun k =>
      F (ordc C.n (C.ec3 i j k))))) := by
  have : ∑ g : C.grp, F (orderOf g) = ∑ g : C.grp, (fun σ => F (orderOf σ)) (g : Equiv.Perm (Fin C.n)) := by
    simp only [Subgroup.orderOf_coe]
  refine this.trans ((sum_grp hv (fun σ => F (orderOf σ))).trans ?_)
  refine sumBelow_congr _ _ _ (fun i hi => sumBelow_congr _ _ _ (fun j hj => sumBelow_congr _ _ _ (fun k hk => ?_)))
  rw [dif_pos ⟨hi, hj, hk⟩]
  have h0 := allBelow_spec _ _ (allBelow_spec _ _ (allBelow_spec _ _ ho i hi) j hj) k hk
  simp only [bne_iff_ne, ne_eq] at h0
  rw [← code_e3 hv hi hj hk] at h0 ⊢
  rw [(ordc_spec (hn hv) _ h0).1]

end Chain

open Chain

/- The simple group `PSU(3,3)` on 28 points -/

def tb (t : ℕ) : ℕ := TBL / 131072 ^ t % 131072

def ecT (t : ℕ) : ℕ := PSU.ec3 (t / 216) (t / 8 % 27) (t % 8)

def eT (t : ℕ) : Equiv.Perm (Fin PSU.n) := PSU.e3 (t / 216) (t / 8 % 27) (t % 8)

def ck2 (d x : ℕ) : Bool :=
  decide (d / 16 < 6048) && decide (d % 16 < 14) &&
    comp PSU.n (ecT (d / 16)) x == comp PSU.n (ecT (reps.getD (d % 16) 0)) (ecT (d / 16))

def checkConj : Bool := allBelow 28 (fun i => allBelow 27 (fun j => allBelow 8 (fun k =>
  ck2 (tb (i * 216 + j * 8 + k)) (PSU.ec3 i j k))))

def checkReps : Bool := allBelow 14 (fun r => decide (reps.getD r 0 < 6048) &&
  ordc PSU.n (ecT (reps.getD r 0)) == repOrd.getD r 0 && repOrd.getD r 0 != 0)

def checkProds : Bool := allBelow 14 (fun r => decide (r = 0) || allBelow 2 (fun g =>
  ((prods.getD r []).getD g []).all (fun s => decide (s < 6048) && tb s % 16 == r) &&
  ((prods.getD r []).getD g []).foldr (fun s acc => comp PSU.n (ecT s) acc) (idc PSU.n) == PSU.gc g))

def psiG : ℕ := sumBelow 28 (fun i => sumBelow 27 (fun j => sumBelow 8 (fun k =>
  Nat.totient (repOrd.getD (tb (i * 216 + j * 8 + k) % 16) 0))))

theorem vG : PSU.valid = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem hConj : checkConj = true := by decide +kernel

theorem hReps : checkReps = true := by decide +kernel

theorem hProds : checkProds = true := by decide +kernel

theorem hPsiG : psiG = 23984 := by decide +kernel

theorem psu_ng : PSU.ng = 2 := rfl
theorem psu_s0 : PSU.s0 = 28 := rfl
theorem psu_s1 : PSU.s1 = 27 := rfl
theorem psu_s2 : PSU.s2 = 8 := rfl
theorem psu_n : PSU.n = 28 := rfl

theorem idx_lt {t : ℕ} (ht : t < 6048) : t / 216 < PSU.s0 ∧ t / 8 % 27 < PSU.s1 ∧ t % 8 < PSU.s2 := by
  rw [psu_s0, psu_s1, psu_s2]; omega

theorem code_eT {t : ℕ} (ht : t < 6048) : code (eT t) = ecT t := by
  obtain ⟨h1, h2, h3⟩ := idx_lt ht
  exact code_e3 vG h1 h2 h3

theorem eT_mem {t : ℕ} (ht : t < 6048) : eT t ∈ PSU.grp := by
  obtain ⟨h1, h2, h3⟩ := idx_lt ht
  exact e3_mem vG h1 h2 h3

theorem eT_zero : eT 0 = 1 := by
  rw [show eT 0 = PSU.U 0 0 * (PSU.U 1 0 * PSU.U 2 0) from rfl, U_zero vG (l := 0) (by norm_num),
    U_zero vG (l := 1) (by norm_num), U_zero vG (l := 2) (by norm_num), mul_one, mul_one]

/-- conjugacy certificate: `c * e = r * c` -/
theorem conj_cert {t : ℕ} (ht : t < 6048) :
    tb t / 16 < 6048 ∧ tb t % 16 < 14 ∧ reps.getD (tb t % 16) 0 < 6048 ∧
      eT (tb t / 16) * eT t = eT (reps.getD (tb t % 16) 0) * eT (tb t / 16) := by
  obtain ⟨h1, h2, h3⟩ := idx_lt ht
  simp only [psu_s0, psu_s1, psu_s2] at h1 h2 h3
  have h := allBelow_spec _ _ (allBelow_spec _ _ (allBelow_spec _ _ hConj _ h1) _ h2) _ h3
  have et : t / 216 * 216 + t / 8 % 27 * 8 + t % 8 = t := by omega
  rw [et] at h
  unfold ck2 at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨hc, hr⟩, he⟩ := h
  have hrr := allBelow_spec _ _ hReps _ hr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hrr
  refine ⟨hc, hr, hrr.1.1, code_eq vG ?_⟩
  rw [code_mul (hn vG), code_mul (hn vG), code_eT hc, code_eT hrr.1.1]
  have : code (eT t) = PSU.ec3 (t / 216) (t / 8 % 27) (t % 8) := code_eT ht
  rw [this]
  exact he

theorem orderOf_eT {t : ℕ} (ht : t < 6048) : orderOf (eT t) = repOrd.getD (tb t % 16) 0 := by
  obtain ⟨hc, hr, hrr, he⟩ := conj_cert ht
  have e1 : eT t = (eT (tb t / 16))⁻¹ * eT (reps.getD (tb t % 16) 0) * eT (tb t / 16) := by
    rw [mul_assoc, ← he]; group
  rw [e1, orderOf_conj']
  have h := allBelow_spec _ _ hReps _ hr
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨_, h2⟩, h3⟩ := h
  have hne : ordc PSU.n (code (eT (reps.getD (tb t % 16) 0))) ≠ 0 := by
    rw [code_eT hrr, h2]; exact h3
  have := (ordc_spec (n := PSU.n) (hn vG) _ hne).1
  rw [this, code_eT hrr, h2]

theorem card_G : Fintype.card PSU.grp = 6048 := by
  rw [card_grp vG]; rfl

theorem psi_G : ∑ g : PSU.grp, Nat.totient (orderOf g) = 23984 := by
  have : ∑ g : PSU.grp, Nat.totient (orderOf g) =
      ∑ g : PSU.grp, (fun σ => Nat.totient (orderOf σ)) (g : Equiv.Perm (Fin PSU.n)) := by
    simp only [Subgroup.orderOf_coe]
  refine this.trans ((sum_grp vG (fun σ => Nat.totient (orderOf σ))).trans ?_)
  rw [← hPsiG]
  unfold psiG
  refine sumBelow_congr _ _ _ (fun i hi => sumBelow_congr _ _ _ (fun j hj => sumBelow_congr _ _ _ (fun k hk => ?_)))
  rw [dif_pos ⟨hi, hj, hk⟩]
  rw [psu_s0] at hi; rw [psu_s1] at hj; rw [psu_s2] at hk
  have ht : i * 216 + j * 8 + k < 6048 := by omega
  have hq : PSU.e3 i j k = eT (i * 216 + j * 8 + k) := by
    unfold eT; congr 1 <;> omega
  rw [hq, orderOf_eT ht]

/-- elements of `PSU.grp` -/
def eG {t : ℕ} (ht : t < 6048) : PSU.grp := ⟨eT t, eT_mem ht⟩

theorem simple_G : IsSimpleGroup PSU.grp := by
  have g0mem : PSU.genP 0 ∈ PSU.grp := Subgroup.subset_closure ⟨⟨0, by rw [psu_ng]; norm_num⟩, rfl⟩
  have g1mem : PSU.genP 1 ∈ PSU.grp := Subgroup.subset_closure ⟨⟨1, by rw [psu_ng]; norm_num⟩, rfl⟩
  haveI : Nontrivial PSU.grp := by
    refine ⟨⟨⟨PSU.genP 0, g0mem⟩, 1, fun h => ?_⟩⟩
    have h' : PSU.genP 0 = 1 := congrArg Subtype.val h
    have := congrArg code h'
    rw [code_genP vG (by rw [psu_ng]; norm_num), code_one (hn vG)] at this
    revert this; decide +kernel
  refine ⟨fun H hH => ?_⟩
  rcases Subgroup.bot_or_exists_ne_one H with hb | ⟨x, hxH, hx1⟩
  · exact Or.inl hb
  right
  -- write x as an enumerated element
  obtain ⟨xv, xmem⟩ := x
  obtain ⟨i, j, k, hi, hj, hk, rfl⟩ := closure_sub vG xmem
  rw [psu_s0] at hi; rw [psu_s1] at hj; rw [psu_s2] at hk
  set t := i * 216 + j * 8 + k with htdef
  have ht : t < 6048 := by omega
  have hq : PSU.e3 i j k = eT t := by unfold eT; congr 1 <;> omega
  -- membership of conjugates
  have conj_in : ∀ (c y : PSU.grp), y ∈ H → c⁻¹ * y * c ∈ H := fun c y hy => by
    have := hH.conj_mem y hy c⁻¹
    simpa using this
  obtain ⟨hc, hr, hrr, he⟩ := conj_cert ht
  set kk := tb t % 16 with hkk
  have hR : eG hrr ∈ H := by
    have e1 : eT (reps.getD kk 0) = eT (tb t / 16) * eT t * (eT (tb t / 16))⁻¹ := by
      rw [he]; group
    have : eG hrr = (eG hc)⁻¹⁻¹ * ⟨PSU.e3 i j k, xmem⟩ * (eG hc)⁻¹ := by
      apply Subtype.ext
      simp only [eG, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
      rw [hq, ← e1]
    rw [this]; exact conj_in _ _ hxH
  -- every element of the class `kk` lies in `H`
  have cls_in : ∀ s (hs : s < 6048), tb s % 16 = kk → eG hs ∈ H := by
    intro s hs hsk
    obtain ⟨hc', hr', hrr', he'⟩ := conj_cert hs
    have : eG hs = (eG hc')⁻¹ * eG hrr * eG hc' := by
      apply Subtype.ext
      simp only [eG, Subgroup.coe_mul, Subgroup.coe_inv]
      have hk' : reps.getD (tb s % 16) 0 = reps.getD kk 0 := by rw [hsk]
      rw [← hk']
      rw [mul_assoc, ← he']; group
    rw [this]; exact conj_in _ _ hR
  -- `kk ≠ 0`
  have hk0 : kk ≠ 0 := by
    intro h0
    apply hx1
    apply Subtype.ext
    have r0 : reps.getD kk 0 = 0 := by rw [h0]; rfl
    have e1 : eT t = (eT (tb t / 16))⁻¹ * eT (reps.getD kk 0) * eT (tb t / 16) := by
      rw [mul_assoc, ← he]; group
    show PSU.e3 i j k = 1
    rw [hq, e1, r0, eT_zero]; group
  -- generators lie in `H`
  have gen_in : ∀ g (hg : g < 2), (⟨PSU.genP g, Subgroup.subset_closure ⟨⟨g, by rw [psu_ng]; omega⟩, rfl⟩⟩ : PSU.grp) ∈ H := by
    intro g hg
    have hp := allBelow_spec _ _ hProds kk hr
    simp only [Bool.or_eq_true, decide_eq_true_eq, hk0, false_or] at hp
    have hp2 := allBelow_spec _ _ hp g hg
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hp2
    obtain ⟨hall, hprod⟩ := hp2
    generalize (prods.getD kk []).getD g [] = L at hall hprod
    -- product of the list
    have key : ∀ L : List ℕ, (∀ s ∈ L, s < 6048 ∧ tb s % 16 = kk) →
        ∃ y : PSU.grp, y ∈ H ∧ code y.1 = L.foldr (fun s acc => comp PSU.n (ecT s) acc) (idc PSU.n) := by
      intro L
      induction L with
      | nil => intro _; exact ⟨1, H.one_mem, code_one (hn vG)⟩
      | cons a L ih =>
        intro hL
        obtain ⟨y, hy, hyc⟩ := ih (fun s hs => hL s (by simp [hs]))
        have ha := hL a (by simp)
        refine ⟨eG ha.1 * y, H.mul_mem (cls_in a ha.1 ha.2) hy, ?_⟩
        simp only [Subgroup.coe_mul, eG, List.foldr_cons]
        rw [code_mul (hn vG), code_eT ha.1, hyc]
    obtain ⟨y, hy, hyc⟩ := key L hall
    have : y = ⟨PSU.genP g, Subgroup.subset_closure ⟨⟨g, by rw [psu_ng]; omega⟩, rfl⟩⟩ := by
      apply Subtype.ext
      apply code_eq vG
      show code y.1 = code (PSU.genP g)
      rw [hyc, hprod, code_genP vG (by rw [psu_ng]; omega)]
    rw [← this]; exact hy
  -- conclude
  rw [eq_top_iff]
  rintro ⟨z, hz⟩ -
  have hle : PSU.grp ≤ H.map PSU.grp.subtype := by
    unfold grp
    rw [Subgroup.closure_le]
    rintro _ ⟨⟨g, hg⟩, rfl⟩
    rw [psu_ng] at hg
    exact ⟨_, gen_in g hg, rfl⟩
  obtain ⟨w, hw, hwz⟩ := hle hz
  have : w = ⟨z, hz⟩ := Subtype.ext hwz
  rw [← this]; exact hw

/- The non-simple group `C₆ × S₄ × (C₇ ⋊ C₆)` -/

theorem vC6 : C6c.valid = true := by decide +kernel
theorem vS4 : S4c.valid = true := by decide +kernel
theorem vF : Fc.valid = true := by decide +kernel
theorem oC6 : C6c.checkOrd = true := by decide +kernel
theorem oS4 : S4c.checkOrd = true := by decide +kernel
theorem oF : Fc.checkOrd = true := by decide +kernel

abbrev HH : Type := C6c.grp × S4c.grp × Fc.grp

theorem card_H : Fintype.card HH = 6048 := by
  simp only [Fintype.card_prod, card_grp vC6, card_grp vS4, card_grp vF]
  rfl

def psiH : ℕ :=
  sumBelow C6c.s0 (fun i => sumBelow C6c.s1 (fun j => sumBelow C6c.s2 (fun k =>
  sumBelow S4c.s0 (fun i' => sumBelow S4c.s1 (fun j' => sumBelow S4c.s2 (fun k' =>
  sumBelow Fc.s0 (fun i'' => sumBelow Fc.s1 (fun j'' => sumBelow Fc.s2 (fun k'' =>
    Nat.totient ((ordc C6c.n (C6c.ec3 i j k)).lcm ((ordc S4c.n (S4c.ec3 i' j' k')).lcm
      (ordc Fc.n (Fc.ec3 i'' j'' k'')))))))))))))

theorem hPsiH : psiH = 23984 := by decide +kernel

theorem psi_H : ∑ h : HH, Nat.totient (orderOf h) = 23984 := by
  rw [← hPsiH]
  simp only [Fintype.sum_prod_type, Prod.orderOf]
  rw [sum_grp_ord vC6 oC6 (fun a => ∑ b : S4c.grp, ∑ c : Fc.grp,
    Nat.totient (a.lcm ((orderOf b).lcm (orderOf c))))]
  unfold psiH
  refine sumBelow_congr _ _ _ (fun i _ => sumBelow_congr _ _ _ (fun j _ => sumBelow_congr _ _ _ (fun k _ => ?_)))
  rw [sum_grp_ord vS4 oS4 (fun b => ∑ c : Fc.grp,
    Nat.totient ((ordc C6c.n (C6c.ec3 i j k)).lcm (b.lcm (orderOf c))))]
  refine sumBelow_congr _ _ _ (fun i' _ => sumBelow_congr _ _ _ (fun j' _ => sumBelow_congr _ _ _ (fun k' _ => ?_)))
  rw [sum_grp_ord vF oF (fun c =>
    Nat.totient ((ordc C6c.n (C6c.ec3 i j k)).lcm ((ordc S4c.n (S4c.ec3 i' j' k')).lcm c)))]

theorem not_simple_H : ¬ IsSimpleGroup HH := by
  intro hs
  have m0 : C6c.genP 0 ∈ C6c.grp := Subgroup.subset_closure ⟨⟨0, by decide⟩, rfl⟩
  have m1 : S4c.genP 0 ∈ S4c.grp := Subgroup.subset_closure ⟨⟨0, by decide⟩, rfl⟩
  have n0 : (⟨C6c.genP 0, m0⟩ : C6c.grp) ≠ 1 := fun h => by
    have := congrArg code (congrArg Subtype.val h)
    rw [Subgroup.coe_one, code_genP vC6 (by decide), code_one (hn vC6)] at this
    revert this; decide +kernel
  have n1 : (⟨S4c.genP 0, m1⟩ : S4c.grp) ≠ 1 := fun h => by
    have := congrArg code (congrArg Subtype.val h)
    rw [Subgroup.coe_one, code_genP vS4 (by decide), code_one (hn vS4)] at this
    revert this; decide +kernel
  let f : HH →* S4c.grp × Fc.grp := MonoidHom.snd _ _
  rcases (MonoidHom.normal_ker f).eq_bot_or_eq_top with h | h
  · have : ((⟨C6c.genP 0, m0⟩, 1) : HH) ∈ f.ker := by
      rw [MonoidHom.mem_ker]; rfl
    rw [h, Subgroup.mem_bot] at this
    exact n0 (congrArg Prod.fst this)
  · have : ((1, ⟨S4c.genP 0, m1⟩, 1) : HH) ∈ f.ker := by rw [h]; exact Subgroup.mem_top _
    rw [MonoidHom.mem_ker] at this
    exact n1 (congrArg Prod.fst this)

end OMA1925

theorem OMA.solution : type_of% @Kourovka.«19.25».kourovka_19_25 := by
  intro h
  have := @h OMA1925.PSU.grp OMA1925.HH _ _ _ _ (OMA1925.card_G.trans OMA1925.card_H.symm)
    (OMA1925.psi_G.trans OMA1925.psi_H.symm) OMA1925.simple_G
  exact OMA1925.not_simple_H this
