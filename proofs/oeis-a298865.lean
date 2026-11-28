import OMAStatements.S_oeis_a298865
import Mathlib

private def FactorPair (n : ℕ) (uv : ℕ × ℕ) : Prop :=
  0 < uv.1 ∧ uv.1 < uv.2 ∧ uv.1 * uv.2 = n

private def SquarePair (n : ℕ) (xy : ℕ × ℕ) : Prop :=
  xy.2 < xy.1 ∧ xy.1 ^ 2 = n + xy.2 ^ 2

private theorem pair_eq {n : ℕ} (hn : n.Prime) {uv : ℕ × ℕ}
    (h : FactorPair n uv) : uv = (1, n) := by
  rcases uv with ⟨u, v⟩
  rcases h with ⟨hu, huv, hp⟩
  change 0 < u at hu
  change u < v at huv
  change u * v = n at hp
  have ud : u ∣ n := ⟨v, hp.symm⟩
  have ule : u ≤ n := Nat.le_of_dvd hn.pos ud
  have une : u ≠ n := by
    intro he
    have : u * 1 < u * v := Nat.mul_lt_mul_of_pos_left (by omega) hu
    omega
  have h1 : u = 1 := (Nat.prime_def_lt.mp hn).2 u (lt_of_le_of_ne ule une) ud
  subst u
  simp at hp
  simp [hp]

private theorem prime_not_square {n : ℕ} (hn : n.Prime) : ¬ IsSquare n := by
  rintro ⟨u, hu⟩
  have hp := hn.two_le
  have uu : 1 < u := by
    by_contra! h
    interval_cases u <;> simp_all
  have ud : u ∣ n := ⟨u, hu⟩
  have : u * 1 < u * u := Nat.mul_lt_mul_of_pos_left uu (by omega)
  have hlt : u < n := by simpa [← hu] using this
  have := (Nat.prime_def_lt.mp hn).2 u hlt ud
  omega

private theorem unique_factor_iff {n : ℕ} (hs : ¬ IsSquare n) :
    (∃! uv, FactorPair n uv) ↔ n.Prime := by
  have hn : 2 ≤ n := by
    by_contra! h
    interval_cases n
    · exact hs ⟨0, rfl⟩
    · exact hs ⟨1, rfl⟩
  have hbase : FactorPair n (1, n) := ⟨by omega, by omega, by simp⟩
  constructor
  · rintro ⟨w, hw, hu⟩
    by_contra hp
    obtain ⟨u, ud, hu1, hun⟩ := Nat.exists_dvd_of_not_prime hn hp
    obtain ⟨v, hv⟩ := ud
    have unc : u ≠ 0 := by intro e; subst u; simp at hv; omega
    have vnc : v ≠ 0 := by intro e; subst v; simp at hv; omega
    have vn1 : v ≠ 1 := by intro e; subst v; simp at hv; omega
    have huv : u ≠ v := by intro e; subst v; exact hs ⟨u, hv⟩
    have hw1 := hu (1,n) hbase
    by_cases hh : u < v
    · have hpair : FactorPair n (u,v) := ⟨by omega, hh, hv.symm⟩
      have h := congrArg Prod.fst ((hu (u,v) hpair).trans hw1.symm)
      exact hu1 h
    · have hpair : FactorPair n (v,u) := ⟨by omega, by omega, by simpa [mul_comm] using hv.symm⟩
      have h := congrArg Prod.fst ((hu (v,u) hpair).trans hw1.symm)
      exact vn1 h
  · intro hp
    exact ⟨(1,n), hbase, fun _ h => pair_eq hp h⟩

private theorem square_pair_iff {n x y : ℕ} :
    SquarePair n (x,y) ↔ y < x ∧ (x-y) * (x+y) = n := by
  change (y < x ∧ x^2 = n+y^2) ↔ _
  constructor <;> rintro ⟨h, he⟩ <;> refine ⟨h, ?_⟩
  · rw [Nat.sub_mul]
    have hh : x*(x+y) = n+y*(x+y) := by nlinarith
    omega
  · rw [Nat.sub_mul, Nat.sub_eq_iff_eq_add (Nat.mul_le_mul_right _ h.le)] at he
    nlinarith

private theorem unique_of_correspondence {n m : ℕ}
    (f : ℕ × ℕ → ℕ × ℕ) (g : ℕ × ℕ → ℕ × ℕ)
    (hf : ∀ uv, FactorPair m uv → SquarePair n (f uv))
    (hg : ∀ xy, SquarePair n xy → FactorPair m (g xy))
    (hfg : ∀ xy, SquarePair n xy → f (g xy) = xy)
    (hgf : ∀ uv, FactorPair m uv → g (f uv) = uv) :
    (∃! xy, SquarePair n xy) ↔ ∃! uv, FactorPair m uv := by
  constructor
  · rintro ⟨xy, hxy, hu⟩
    refine ⟨g xy, hg xy hxy, fun uv huv => ?_⟩
    rw [← hgf uv huv, hu (f uv) (hf uv huv)]
  · rintro ⟨uv, huv, hu⟩
    refine ⟨f uv, hf uv huv, fun xy hxy => ?_⟩
    rw [← hfg xy hxy, hu (g xy) (hg xy hxy)]

private theorem odd_pairs {n : ℕ} (hn : n % 2 = 1) (hs : ¬ IsSquare n) :
    (∃! xy, SquarePair n xy) ↔ ∃! uv, FactorPair n uv := by
  let f : ℕ × ℕ → ℕ × ℕ := fun uv => ((uv.2+uv.1)/2,(uv.2-uv.1)/2)
  let g : ℕ × ℕ → ℕ × ℕ := fun xy => (xy.1-xy.2,xy.1+xy.2)
  have split (u v : ℕ) (h : FactorPair n (u,v)) :
      (v+u)/2-(v-u)/2 = u ∧ (v+u)/2+(v-u)/2 = v := by
    rcases h with ⟨hu, huv, he⟩
    change u < v at huv
    change u*v = n at he
    have hm : u%2 * (v%2) % 2 = 1 := by rw [← Nat.mul_mod, he, hn]
    have hp : u % 2 = 1 ∧ v % 2 = 1 := by
      by_cases hu : u % 2 = 0 <;> by_cases hv : v % 2 = 0 <;> simp_all
    omega
  apply unique_of_correspondence f g
  · rintro ⟨u,v⟩ h
    have ⟨h1,h2⟩ := split u v h
    rcases h with ⟨hu,huv,he⟩
    apply square_pair_iff.mpr
    change (v-u)/2 < (v+u)/2 ∧ _ * _ = n
    constructor
    · change 0 < u at hu
      omega
    · rwa [h1,h2]
  · rintro ⟨x,y⟩ h
    have ⟨hlt,he⟩ := square_pair_iff.mp h
    have hy : 0 < y := by
      by_contra! hzero
      have ey : y = 0 := by omega
      exact hs ⟨x, by simpa [ey] using he.symm⟩
    exact ⟨by change 0 < x-y; omega, by change x-y < x+y; omega, he⟩
  · rintro ⟨x,y⟩ h
    have ⟨hlt,he⟩ := square_pair_iff.mp h
    apply Prod.ext <;> dsimp [f,g] <;> omega
  · rintro ⟨u,v⟩ h
    have ⟨h1,h2⟩ := split u v h
    exact Prod.ext h1 h2

private theorem four_pairs {m : ℕ} (hs : ¬ IsSquare (4*m)) :
    (∃! xy, SquarePair (4*m) xy) ↔ ∃! uv, FactorPair m uv := by
  let f : ℕ × ℕ → ℕ × ℕ := fun uv => (uv.2+uv.1,uv.2-uv.1)
  let g : ℕ × ℕ → ℕ × ℕ := fun xy => ((xy.1-xy.2)/2,(xy.1+xy.2)/2)
  have reduced (x y : ℕ) (h : SquarePair (4*m) (x,y)) :
      0 < y ∧ y < x ∧ (x-y)%2 = 0 ∧ (x+y)%2 = 0 ∧
      (x-y)/2 * ((x+y)/2) = m := by
    obtain ⟨hlt, he⟩ := square_pair_iff.mp h
    have hy : 0 < y := by
      by_contra! hy
      have : y = 0 := by omega
      subst y
      exact hs ⟨x, by simpa using he.symm⟩
    have hm : (x-y)%2 * ((x+y)%2) % 2 = 0 := by rw [← Nat.mul_mod, he]; omega
    have hpar : (x-y)%2 = 0 ∧ (x+y)%2 = 0 := by
      by_contra! hp
      have hh : (x-y)%2 = 1 ∧ (x+y)%2 = 1 := by omega
      simp [hh.1,hh.2] at hm
    refine ⟨hy,hlt,hpar.1,hpar.2,?_⟩
    have e1 : x-y = 2*((x-y)/2) := by omega
    have e2 : x+y = 2*((x+y)/2) := by omega
    have hh := he
    nth_rewrite 1 [e1, e2] at hh
    nlinarith only [hh]
  have doubled (u v : ℕ) (h : u < v) :
      (v+u)-(v-u) = 2*u ∧ (v+u)+(v-u) = 2*v := by omega
  apply unique_of_correspondence f g
  · rintro ⟨u,v⟩ ⟨hu, huv, he⟩
    change 0 < u at hu
    change u < v at huv
    change u*v = m at he
    have ⟨h1,h2⟩ := doubled u v huv
    apply square_pair_iff.mpr
    change (v-u) < (v+u) ∧ ((v+u)-(v-u))*((v+u)+(v-u)) = 4*m
    refine ⟨by omega, ?_⟩
    rw [h1,h2]
    nlinarith only [he]
  · rintro ⟨x,y⟩ h
    obtain ⟨hy,hlt,e1,e2,he⟩ := reduced x y h
    exact ⟨by change 0 < (x-y)/2; omega, by change (x-y)/2 < (x+y)/2; omega, he⟩
  · rintro ⟨x,y⟩ h
    obtain ⟨hy,hlt,e1,e2,he⟩ := reduced x y h
    apply Prod.ext <;> dsimp [f,g] <;> omega
  · rintro ⟨u,v⟩ h
    have ⟨h1,h2⟩ := doubled u v h.2.1
    apply Prod.ext <;> dsimp [f,g] <;> omega

private theorem n_of_pair {n : ℕ} (h : ∃ xy, SquarePair n xy) :
    n%2 = 1 ∨ n%4 = 0 := by
  obtain ⟨⟨x,y⟩,h⟩ := h
  obtain ⟨hlt,he⟩ := square_pair_iff.mp h
  by_cases hn : n%2 = 1
  · exact Or.inl hn
  right
  have hm : (x-y)%2 * ((x+y)%2) % 2 = 0 := by rw [← Nat.mul_mod, he]; omega
  have hpar : (x-y)%2 = 0 ∧ (x+y)%2 = 0 := by
    by_contra! hp
    have hh : (x-y)%2 = 1 ∧ (x+y)%2 = 1 := by omega
    simp [hh.1,hh.2] at hm
  have e1 : x-y = 2*((x-y)/2) := by omega
  have e2 : x+y = 2*((x+y)/2) := by omega
  nth_rewrite 1 [e1,e2] at he
  have hh : n = 4*(((x-y)/2)*((x+y)/2)) := by nlinarith only [he]
  omega

private theorem square_four_iff {m : ℕ} : IsSquare (4*m) ↔ IsSquare m := by
  constructor
  · rintro ⟨x,hx⟩
    have hm : x%2 * (x%2) % 2 = 0 := by rw [← Nat.mul_mod, ← hx]; omega
    have hx0 : x%2 = 0 := by
      by_contra! hh
      have : x%2 = 1 := by omega
      simp [this] at hm
    refine ⟨x/2, ?_⟩
    have he : x = 2*(x/2) := by omega
    have hmul : x*x = (2*(x/2))*(2*(x/2)) := congrArg (fun t : ℕ => t*t) he
    nlinarith only [hx, hmul]
  · rintro ⟨x,hx⟩
    refine ⟨2*x, ?_⟩
    nlinarith only [hx]

theorem OMA.solution : type_of% @OMA.S_oeis_a298865.main := by
  intro n
  change (n ≠ 2 ∧ (n.Prime ∨ ∃ p, p.Prime ∧ n = 4*p)) ↔
    ¬IsSquare n ∧ ∃! xy, SquarePair n xy
  constructor
  · rintro ⟨hne, hp | ⟨m,hm,rfl⟩⟩
    · have hs := prime_not_square hp
      have ho : n % 2 = 1 := (Nat.odd_iff.mp (hp.odd_of_ne_two hne))
      exact ⟨hs,(odd_pairs ho hs).mpr ((unique_factor_iff hs).mpr hp)⟩
    · have hms := prime_not_square hm
      have hns : ¬IsSquare (4*m) := fun h => hms (square_four_iff.mp h)
      exact ⟨hns,(four_pairs hns).mpr ((unique_factor_iff hms).mpr hm)⟩
  · rintro ⟨hs, ⟨xy,hxy,huniq⟩⟩
    rcases n_of_pair ⟨xy,hxy⟩ with ho | he
    · refine ⟨by omega, Or.inl ?_⟩
      exact (unique_factor_iff hs).mp ((odd_pairs ho hs).mp ⟨xy,hxy,huniq⟩)
    · have h4 : n = 4*(n/4) := by omega
      obtain ⟨m,rfl⟩ : ∃ m, n = 4*m := ⟨n/4,h4⟩
      have hms : ¬IsSquare m := fun h => hs (square_four_iff.mpr h)
      refine ⟨by omega, Or.inr ⟨m, ?_, rfl⟩⟩
      exact (unique_factor_iff hms).mp ((four_pairs hs).mp ⟨xy,hxy,huniq⟩)