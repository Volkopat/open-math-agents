import FormalConjectures.ErdosProblems.«124»

lemma Z (p q) (hq : 7 ≤ q) : 3^(p+1) + 3501 ≤ 4^q ∨ 4^q + 2334 ≤ 3^(p+1) := by
  have h := (by decide +kernel : ∀ i < 64, ∀ j < 64, let u := 3*(3^(64*i+j) % 82713067520); let k := (u+3500)/16384; 16384*k+2334 ≤ u ∨ k^116 % 15145215 + k % 3 ≠ 2) (p%4096/64) (by omega) (p%4096%64) (by omega)
  simp only [Nat.div_add_mod] at h
  have := ((by decide +kernel : 3^4096 ≡ 1 [MOD 82713067520]).pow (p/4096)).mul_left (3^(p%4096))
  rw [Nat.ModEq, one_pow, mul_one, ← pow_mul, ← pow_add, Nat.mod_add_div] at this
  have e2 := pow_mul_pow_sub 4 hq
  have h3 : 4^(q-7) % 3 = 1 := by simp [Nat.pow_mod]
  have h4 : (4^(q-7) % 15145215)^116 % 15145215 = 1 := by rw [← Nat.pow_mod, pow_right_comm, Nat.pow_mod]; norm_num
  have := lt_trichotomy (3^p/82713067520) (4^(q-7)/15145215)
  by_cases e : 4^(q-7) % 15145215 = (3*(3^(p%4096) % 82713067520)+3500)/16384
  · rw [e] at h4; omega
  · omega

def B (d e x : ℕ) := ∃ s, (∀ i ∈ s, i ≤ e) ∧ (∀ i ∈ s, 1 ≤ i) ∧ ∑ i ∈ s, d^i = x

lemma W {d e x} : B d e x → B d (e+1) x
  | ⟨s,h⟩ => ⟨s, by grind⟩

lemma N {d e x} : B d e x → B d (e+1) (d^(e+1) + x)
  | ⟨s,h⟩ => ⟨insert (e+1) s, by grind [Finset.sum_insert]⟩

def A (d b : ℕ) : ℕ → ℕ
  | 0 => b
  | e+1 => A d b e ||| A d b e <<< d^(e+1)

lemma S {d b e n} (h : (A d b e).testBit n) : ∃ t u, b.testBit t ∧ B d e u ∧ t+u = n := by
  induction e generalizing n
  · exact ⟨n, 0, h, ⟨∅, by simp⟩, rfl⟩
  next e ih =>
    simp [A] at h
    rcases h with h | ⟨g, h⟩ <;> obtain ⟨t,u,a,c,f⟩ := ih h
    exacts [⟨t,u,a,W c,f⟩, ⟨t,_,a,N c,by omega⟩]

def C (U) (P : ℕ → Prop) := ∀ n, 582 ≤ n → n ≤ U → P n

lemma E (w) {U P Q} (H : C U P) (g : w+581 ≤ U) (k : ∀ n, P n → Q n ∧ Q (n+w)) : C (U+w) Q := fun n h h' =>
  if o : n ≤ U then (k n (H n h o)).1 else (by omega : n-w+w = n) ▸ (k _ (H (n-w) (by omega) (by omega))).2

lemma X (t) : ∃ a b c U, (t ≤ U ∧ 6 ≤ b ∧ 0 < 3^a ∧ 0 < 4^b ∧ 0 < 7^c ∧ 3*3^(a+1)+2*4^(b+1)+7^(c+1) ≤ 6*U+3516) ∧ C U fun n => ∃ x y z, B 3 a x ∧ B 4 b y ∧ B 7 c z ∧ x+y+z = n :=
  Nat.rec ⟨7,6,3,8556,by decide,fun n h h' => by
    have := congrArg (·.testBit n) (by decide +kernel : let I := (2^7975-1) <<< 582; A 7 (A 4 (A 3 1 7) 6) 3 &&& I = I)
    simp [h, show n-582 < 7975 by omega] at this
    exact let ⟨s,z,hs,hz,e⟩ := S this; let ⟨r,y,hr,hy,f⟩ := S hs; let ⟨t,x,ht,hx,g⟩ := S hr
      ⟨x,y,z,hx,hy,hz,by grind [Nat.testBit_one_eq_true_iff_self_eq_zero]⟩⟩ (fun t ⟨a,b,c,U,h0,H⟩ => by
    have := Z a (b+1) (by omega)
    by_cases h1 : 3^(a+1) ≤ min (4^(b+1)) (7^(c+1))
    · refine ⟨a+1,b,c,_,?_,E (3^(a+1)) H ?_ fun n ⟨x,y,z,hx,hy,hz,e⟩ => ⟨⟨x,y,z,W hx,hy,hz,e⟩,_,y,z,N hx,hy,hz,?_⟩⟩ <;> omega
    by_cases h2 : 4^(b+1) ≤ 7^(c+1)
    · refine ⟨a,b+1,c,_,?_,E (4^(b+1)) H ?_ fun n ⟨x,y,z,hx,hy,hz,e⟩ => ⟨⟨x,y,z,hx,W hy,hz,e⟩,x,_,z,hx,N hy,hz,?_⟩⟩ <;> omega
    refine ⟨a,b,c+1,_,?_,E (7^(c+1)) H ?_ fun n ⟨x,y,z,hx,hy,hz,e⟩ => ⟨⟨x,y,z,hx,hy,W hz,e⟩,x,y,_,hx,hy,N hz,?_⟩⟩ <;> omega) t

theorem OMA.solution : type_of% @Erdos124.erdos124.ne_zero_three_four_seven :=
  Filter.eventually_atTop.2 ⟨582, fun n hn =>
    let ⟨_,_,_,_,⟨h,_⟩,H⟩ := X n
    let ⟨_,_,_,⟨r,_,hr⟩,⟨s,_,hs⟩,⟨u,_,hu⟩,e⟩ := H n hn h
    ⟨_, ⟨_, ⟨r,hr⟩, _, ⟨s,hs⟩, rfl⟩, _, ⟨u,hu⟩, e⟩⟩
