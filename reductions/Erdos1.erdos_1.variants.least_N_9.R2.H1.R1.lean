import OMAReductions.R_Erdos1_erdos_1_variants_least_N_9_R2

/-! Split a nine-element candidate into its six largest values and its residual triple.
The cube interval-growth bound leaves four possible maxima. Single-value and pair
relations remove vertices and edges from the residual graph. Three forced vertices
either fail the pair tests or sum to a relation on their own. For larger candidate
sets, check only triangles satisfying the moment, rank-span and modular support
bounds. The maximum bounds three gaps in the ordered distinct subset sums, from ranks
158 to 306, 207 to 355, and 224 to 367.
A surviving triangle has four signed sums to inspect up to sign. -/

namespace OMA.R_Erdos1_erdos_1_variants_least_N_9_R2_H1_R1
open Finset
open scoped Pointwise

-- The interval-growth certificate and rank table are due to physbuzz.
-- https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/9920 (7f72b5343be39f7cdacfeda6548dc2fe0a8b0666).
-- The second-largest bound and its short-span certificates are due to justusklocke-cloud.
-- https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/19448 (66e9446714b2385af8e25cf455e0a0f5f7ea5a27).

namespace CubeWindow
open Finset Erdos1
open scoped Classical

lemma advance (f : ℤ → ℕ) (g h : ℕ → ℕ) (d : ℕ) (M a : ℤ)
    (inc : Monotone f) (bound : ∀ z, f z ≤ d) (grow : ∀ z, g (f z) ≤ f (z+M))
    (ha : 0≤a) (ham : a≤M)
    (table : ∀ i j : Fin (d+1), h (i.val+j.val) ≤ max (g i.val) j.val + max (g j.val) i.val) (z : ℤ) :
    h (f z + f (z-a)) ≤ f (z+M) + f (z+M-a) := by
  have u := table ⟨f z, by have := bound z; omega⟩ ⟨f (z-a), by have := bound (z-a); omega⟩
  refine u.trans (Nat.add_le_add (max_le (grow _) (inc (by omega))) (max_le ?_ (inc (by omega))))
  simpa only [sub_add_eq_add_sub] using grow (z-a)

lemma iterate (C : Finset ℕ → ℤ → ℕ) (M : ℕ)
    (monoC : ∀ A, Monotone (C A)) (sizeC : ∀ A z, C A z ≤ 2^A.card)
    (stepC : ∀ A a, a∉A → ∀ z, C (insert a A) z = C A z + C A (z-a))
    (n : ℕ) (g h : ℕ → ℕ)
    (prev : ∀ A : Finset ℕ, A.card=n → (∀ a∈A, a≤M) → ∀ z, g (C A z) ≤ C A (z+M))
    (tab : ∀ i j : Fin (2^n+1), h (i.val+j.val) ≤ max (g i.val) j.val + max (g j.val) i.val) :
    ∀ A : Finset ℕ, A.card=n+1 → (∀ a∈A, a≤M) → ∀ z, h (C A z) ≤ C A (z+M) := by
  intro A hc cap z
  obtain ⟨a,ha⟩ := card_pos.mp (show 0<A.card by omega)
  let B := A.erase a
  have eq : insert a B = A := insert_erase ha
  have ne : a∉B := notMem_erase _ _
  have bc : B.card=n := by simp [B,card_erase_of_mem ha,hc]
  have sub : B⊆A := erase_subset _ _
  have v := advance (C B) g h (2^n) M a (monoC B) (fun t => bc ▸ sizeC B t)
    (prev B bc (fun x hx => cap x (sub hx))) (by positivity) (by exact_mod_cast cap a ha) tab z
  simpa only [← stepC B a ne,eq] using v


lemma verifyRows (g h : ℕ→ℕ) (d : ℕ)
    (check : (List.range (d+1)).all (fun i => (List.range (d+1)).all (fun j =>
      decide (h (i+j) ≤ max (g i) j + max (g j) i))) = true) :
    ∀ i j : Fin (d+1), h (i.val+j.val) ≤ max (g i.val) j.val + max (g j.val) i.val := by
  intro i j
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp check i.val (List.mem_range.mpr i.isLt)) j.val (List.mem_range.mpr j.isLt))
lemma verifyBlocks (p : ℕ→Bool) (u m : ℕ)
    (lo : (List.range u).all p=true) (hi : (List.range' u m).all p=true) :
    (List.range (u+m)).all p=true := by
  rw [List.range_add,←List.range'_eq_map_range,List.all_append,lo,hi]; rfl
lemma table0 : ∀ i j : Fin (1+1), (fun j : ℕ => (0x200800 >>> (10*j)) % 1024) (i.val+j.val) ≤ max (id i.val) j.val + max (id j.val) i.val := by
  apply verifyRows id (fun j : ℕ => (0x200800 >>> (10*j)) % 1024) 1
  let test := (fun i : ℕ => (List.range (1+1)).all (fun j => decide ((fun j : ℕ => (0x200800 >>> (10*j)) % 1024) (i+j) ≤ max (id i) j + max (id j) i)))
  change (List.range 2).all test=true
  have block0 : (List.range 0).all test=true := rfl
  have block2 := verifyBlocks test 0 2 block0 (by decide +kernel)
  exact block2

lemma table1 : ∀ i j : Fin (2+1), (fun j : ℕ => (0x40100400c00 >>> (10*j)) % 1024) (i.val+j.val) ≤ max ((fun j : ℕ => (0x200800 >>> (10*j)) % 1024) i.val) j.val + max ((fun j : ℕ => (0x200800 >>> (10*j)) % 1024) j.val) i.val := by
  apply verifyRows (fun j : ℕ => (0x200800 >>> (10*j)) % 1024) (fun j : ℕ => (0x40100400c00 >>> (10*j)) % 1024) 2
  let test := (fun i : ℕ => (List.range (2+1)).all (fun j => decide ((fun j : ℕ => (0x40100400c00 >>> (10*j)) % 1024) (i+j) ≤ max ((fun j : ℕ => (0x200800 >>> (10*j)) % 1024) i) j + max ((fun j : ℕ => (0x200800 >>> (10*j)) % 1024) j) i)))
  change (List.range 3).all test=true
  have block0 : (List.range 0).all test=true := rfl
  have block3 := verifyBlocks test 0 3 block0 (by decide +kernel)
  exact block3

lemma table2 : ∀ i j : Fin (4+1), (fun j : ℕ => (0x8020080200701c0601000 >>> (10*j)) % 1024) (i.val+j.val) ≤ max ((fun j : ℕ => (0x40100400c00 >>> (10*j)) % 1024) i.val) j.val + max ((fun j : ℕ => (0x40100400c00 >>> (10*j)) % 1024) j.val) i.val := by
  apply verifyRows (fun j : ℕ => (0x40100400c00 >>> (10*j)) % 1024) (fun j : ℕ => (0x8020080200701c0601000 >>> (10*j)) % 1024) 4
  let test := (fun i : ℕ => (List.range (4+1)).all (fun j => decide ((fun j : ℕ => (0x8020080200701c0601000 >>> (10*j)) % 1024) (i+j) ≤ max ((fun j : ℕ => (0x40100400c00 >>> (10*j)) % 1024) i) j + max ((fun j : ℕ => (0x40100400c00 >>> (10*j)) % 1024) j) i)))
  change (List.range 5).all test=true
  have block0 : (List.range 0).all test=true := rfl
  have block4 := verifyBlocks test 0 4 block0 (by decide +kernel)
  have block5 := verifyBlocks test 4 1 block4 (by decide +kernel)
  exact block5

lemma table3 : ∀ i j : Fin (8+1), (fun j : ℕ => (0x10040100401003c0f03c0e0380d02c0b0280801400 >>> (10*j)) % 1024) (i.val+j.val) ≤ max ((fun j : ℕ => (0x8020080200701c0601000 >>> (10*j)) % 1024) i.val) j.val + max ((fun j : ℕ => (0x8020080200701c0601000 >>> (10*j)) % 1024) j.val) i.val := by
  apply verifyRows (fun j : ℕ => (0x8020080200701c0601000 >>> (10*j)) % 1024) (fun j : ℕ => (0x10040100401003c0f03c0e0380d02c0b0280801400 >>> (10*j)) % 1024) 8
  let test := (fun i : ℕ => (List.range (8+1)).all (fun j => decide ((fun j : ℕ => (0x10040100401003c0f03c0e0380d02c0b0280801400 >>> (10*j)) % 1024) (i+j) ≤ max ((fun j : ℕ => (0x8020080200701c0601000 >>> (10*j)) % 1024) i) j + max ((fun j : ℕ => (0x8020080200701c0601000 >>> (10*j)) % 1024) j) i)))
  change (List.range 9).all test=true
  have block0 : (List.range 0).all test=true := rfl
  have block4 := verifyBlocks test 0 4 block0 (by decide +kernel)
  have block8 := verifyBlocks test 4 4 block4 (by decide +kernel)
  have block9 := verifyBlocks test 8 1 block8 (by decide +kernel)
  exact block9

lemma table4 : ∀ i j : Fin (16+1), (fun j : ℕ => (0x2008020080200801f07c1f07c1e0781e0741d0701a0681a06419060160581504c100400f0340a01800 >>> (10*j)) % 1024) (i.val+j.val) ≤ max ((fun j : ℕ => (0x10040100401003c0f03c0e0380d02c0b0280801400 >>> (10*j)) % 1024) i.val) j.val + max ((fun j : ℕ => (0x10040100401003c0f03c0e0380d02c0b0280801400 >>> (10*j)) % 1024) j.val) i.val := by
  apply verifyRows (fun j : ℕ => (0x10040100401003c0f03c0e0380d02c0b0280801400 >>> (10*j)) % 1024) (fun j : ℕ => (0x2008020080200801f07c1f07c1e0781e0741d0701a0681a06419060160581504c100400f0340a01800 >>> (10*j)) % 1024) 16
  let test := (fun i : ℕ => (List.range (16+1)).all (fun j => decide ((fun j : ℕ => (0x2008020080200801f07c1f07c1e0781e0741d0701a0681a06419060160581504c100400f0340a01800 >>> (10*j)) % 1024) (i+j) ≤ max ((fun j : ℕ => (0x10040100401003c0f03c0e0380d02c0b0280801400 >>> (10*j)) % 1024) i) j + max ((fun j : ℕ => (0x10040100401003c0f03c0e0380d02c0b0280801400 >>> (10*j)) % 1024) j) i)))
  change (List.range 17).all test=true
  have block0 : (List.range 0).all test=true := rfl
  have block4 := verifyBlocks test 0 4 block0 (by decide +kernel)
  have block8 := verifyBlocks test 4 4 block4 (by decide +kernel)
  have block12 := verifyBlocks test 8 4 block8 (by decide +kernel)
  have block16 := verifyBlocks test 12 4 block12 (by decide +kernel)
  have block17 := verifyBlocks test 16 1 block16 (by decide +kernel)
  exact block17

lemma table5 : ∀ i j : Fin (32+1), (fun j : ℕ => (0x401004010040100400fc3f0fc3f0fc3e0f83e0f83d0f43d0f03c0ec390e4390e4380e0380dc370d8340d0340cc330c8300c02f0b42a0a82a0a4290a0260982508c200801f0741a05816054130400c01c00 >>> (10*j)) % 1024) (i.val+j.val) ≤ max ((fun j : ℕ => (0x2008020080200801f07c1f07c1e0781e0741d0701a0681a06419060160581504c100400f0340a01800 >>> (10*j)) % 1024) i.val) j.val + max ((fun j : ℕ => (0x2008020080200801f07c1f07c1e0781e0741d0701a0681a06419060160581504c100400f0340a01800 >>> (10*j)) % 1024) j.val) i.val := by
  apply verifyRows (fun j : ℕ => (0x2008020080200801f07c1f07c1e0781e0741d0701a0681a06419060160581504c100400f0340a01800 >>> (10*j)) % 1024) (fun j : ℕ => (0x401004010040100400fc3f0fc3f0fc3e0f83e0f83d0f43d0f03c0ec390e4390e4380e0380dc370d8340d0340cc330c8300c02f0b42a0a82a0a4290a0260982508c200801f0741a05816054130400c01c00 >>> (10*j)) % 1024) 32
  let test := (fun i : ℕ => (List.range (32+1)).all (fun j => decide ((fun j : ℕ => (0x401004010040100400fc3f0fc3f0fc3e0f83e0f83d0f43d0f03c0ec390e4390e4380e0380dc370d8340d0340cc330c8300c02f0b42a0a82a0a4290a0260982508c200801f0741a05816054130400c01c00 >>> (10*j)) % 1024) (i+j) ≤ max ((fun j : ℕ => (0x2008020080200801f07c1f07c1e0781e0741d0701a0681a06419060160581504c100400f0340a01800 >>> (10*j)) % 1024) i) j + max ((fun j : ℕ => (0x2008020080200801f07c1f07c1e0781e0741d0701a0681a06419060160581504c100400f0340a01800 >>> (10*j)) % 1024) j) i)))
  change (List.range 33).all test=true
  have block0 : (List.range 0).all test=true := rfl
  have block4 := verifyBlocks test 0 4 block0 (by decide +kernel)
  have block8 := verifyBlocks test 4 4 block4 (by decide +kernel)
  have block12 := verifyBlocks test 8 4 block8 (by decide +kernel)
  have block16 := verifyBlocks test 12 4 block12 (by decide +kernel)
  have block20 := verifyBlocks test 16 4 block16 (by decide +kernel)
  have block24 := verifyBlocks test 20 4 block20 (by decide +kernel)
  have block28 := verifyBlocks test 24 4 block24 (by decide +kernel)
  have block32 := verifyBlocks test 28 4 block28 (by decide +kernel)
  have block33 := verifyBlocks test 32 1 block32 (by decide +kernel)
  exact block33

lemma table6 : ∀ i j : Fin (64+1), (fun j : ℕ => (0x802008020080200802007f1fc7f1fc7f1fc7e1f87e1f87e1f47d1f47d1f07c1f07b1ec7a1e0781e0781e0771dc771dc761d8761d4751d0721c8721c8711c4711c0701bc6d1b46d1b06c1ac691a4681986318c6318c6218862184611805e1785e1745d1705a1685915c541505414c53148501404f1344a1284911c44100401003f0fc3e0f03c0ec390d8360d4330c02c0b02b0a4260881d0741c0681704c0e02000 >>> (10*j)) % 1024) (i.val+j.val) ≤ max ((fun j : ℕ => (0x401004010040100400fc3f0fc3f0fc3e0f83e0f83d0f43d0f03c0ec390e4390e4380e0380dc370d8340d0340cc330c8300c02f0b42a0a82a0a4290a0260982508c200801f0741a05816054130400c01c00 >>> (10*j)) % 1024) i.val) j.val + max ((fun j : ℕ => (0x401004010040100400fc3f0fc3f0fc3e0f83e0f83d0f43d0f03c0ec390e4390e4380e0380dc370d8340d0340cc330c8300c02f0b42a0a82a0a4290a0260982508c200801f0741a05816054130400c01c00 >>> (10*j)) % 1024) j.val) i.val := by
  apply verifyRows (fun j : ℕ => (0x401004010040100400fc3f0fc3f0fc3e0f83e0f83d0f43d0f03c0ec390e4390e4380e0380dc370d8340d0340cc330c8300c02f0b42a0a82a0a4290a0260982508c200801f0741a05816054130400c01c00 >>> (10*j)) % 1024) (fun j : ℕ => (0x802008020080200802007f1fc7f1fc7f1fc7e1f87e1f87e1f47d1f47d1f07c1f07b1ec7a1e0781e0781e0771dc771dc761d8761d4751d0721c8721c8711c4711c0701bc6d1b46d1b06c1ac691a4681986318c6318c6218862184611805e1785e1745d1705a1685915c541505414c53148501404f1344a1284911c44100401003f0fc3e0f03c0ec390d8360d4330c02c0b02b0a4260881d0741c0681704c0e02000 >>> (10*j)) % 1024) 64
  let test := (fun i : ℕ => (List.range (64+1)).all (fun j => decide ((fun j : ℕ => (0x802008020080200802007f1fc7f1fc7f1fc7e1f87e1f87e1f47d1f47d1f07c1f07b1ec7a1e0781e0781e0771dc771dc761d8761d4751d0721c8721c8711c4711c0701bc6d1b46d1b06c1ac691a4681986318c6318c6218862184611805e1785e1745d1705a1685915c541505414c53148501404f1344a1284911c44100401003f0fc3e0f03c0ec390d8360d4330c02c0b02b0a4260881d0741c0681704c0e02000 >>> (10*j)) % 1024) (i+j) ≤ max ((fun j : ℕ => (0x401004010040100400fc3f0fc3f0fc3e0f83e0f83d0f43d0f03c0ec390e4390e4380e0380dc370d8340d0340cc330c8300c02f0b42a0a82a0a4290a0260982508c200801f0741a05816054130400c01c00 >>> (10*j)) % 1024) i) j + max ((fun j : ℕ => (0x401004010040100400fc3f0fc3f0fc3e0f83e0f83d0f43d0f03c0ec390e4390e4380e0380dc370d8340d0340cc330c8300c02f0b42a0a82a0a4290a0260982508c200801f0741a05816054130400c01c00 >>> (10*j)) % 1024) j) i)))
  change (List.range 65).all test=true
  have block0 : (List.range 0).all test=true := rfl
  have block4 := verifyBlocks test 0 4 block0 (by decide +kernel)
  have block8 := verifyBlocks test 4 4 block4 (by decide +kernel)
  have block12 := verifyBlocks test 8 4 block8 (by decide +kernel)
  have block16 := verifyBlocks test 12 4 block12 (by decide +kernel)
  have block20 := verifyBlocks test 16 4 block16 (by decide +kernel)
  have block24 := verifyBlocks test 20 4 block20 (by decide +kernel)
  have block28 := verifyBlocks test 24 4 block24 (by decide +kernel)
  have block32 := verifyBlocks test 28 4 block28 (by decide +kernel)
  have block36 := verifyBlocks test 32 4 block32 (by decide +kernel)
  have block40 := verifyBlocks test 36 4 block36 (by decide +kernel)
  have block44 := verifyBlocks test 40 4 block40 (by decide +kernel)
  have block48 := verifyBlocks test 44 4 block44 (by decide +kernel)
  have block52 := verifyBlocks test 48 4 block48 (by decide +kernel)
  have block56 := verifyBlocks test 52 4 block52 (by decide +kernel)
  have block60 := verifyBlocks test 56 4 block56 (by decide +kernel)
  have block64 := verifyBlocks test 60 4 block60 (by decide +kernel)
  have block65 := verifyBlocks test 64 1 block64 (by decide +kernel)
  exact block65

lemma table7 : ∀ i j : Fin (128+1), (fun j : ℕ => (0x100401004010040100401003fcff3fcff3fcff3fcfe3f8fe3f8fe3f8fd3f4fd3f4fd3f0fc3f0fc3ecfb3ecfa3e8f93dcf73dcf73dcf73d8f63d8f63d8f53d4f53d4f43d0f43ccf33c8f03c0f03c0f03bcef3bcef3b8ee3b8ed3b4ec3a8ea3a8ea3a4e93a4e83a0e7394e5394e4390e3384e1380de36cdb36cdb36cda368da368d9364d9360d835cd5354d5354d4350d434cd3348d0340d033ccf338cc330cb324c6318c6318c5314c5310c430cc1304c1300c02fcbd2f4bc2e8b72dcb72d8b62d4b32ccb22c0ad2b4ac2a8a728ca328ca3288a2288a1284a02789e2789d2749c2689a26497250942509324c922409023c8d2288a2248721080200801fc7f1f87c1f07b1e4761d8751cc701b06c1ac69198621745d1745c1705b164591605614c53148501344912448118430fc3a0e8390dc340c02b094250902207c1b0581002400 >>> (10*j)) % 1024) (i.val+j.val) ≤ max ((fun j : ℕ => (0x802008020080200802007f1fc7f1fc7f1fc7e1f87e1f87e1f47d1f47d1f07c1f07b1ec7a1e0781e0781e0771dc771dc761d8761d4751d0721c8721c8711c4711c0701bc6d1b46d1b06c1ac691a4681986318c6318c6218862184611805e1785e1745d1705a1685915c541505414c53148501404f1344a1284911c44100401003f0fc3e0f03c0ec390d8360d4330c02c0b02b0a4260881d0741c0681704c0e02000 >>> (10*j)) % 1024) i.val) j.val + max ((fun j : ℕ => (0x802008020080200802007f1fc7f1fc7f1fc7e1f87e1f87e1f47d1f47d1f07c1f07b1ec7a1e0781e0781e0771dc771dc761d8761d4751d0721c8721c8711c4711c0701bc6d1b46d1b06c1ac691a4681986318c6318c6218862184611805e1785e1745d1705a1685915c541505414c53148501404f1344a1284911c44100401003f0fc3e0f03c0ec390d8360d4330c02c0b02b0a4260881d0741c0681704c0e02000 >>> (10*j)) % 1024) j.val) i.val := by
  apply verifyRows (fun j : ℕ => (0x802008020080200802007f1fc7f1fc7f1fc7e1f87e1f87e1f47d1f47d1f07c1f07b1ec7a1e0781e0781e0771dc771dc761d8761d4751d0721c8721c8711c4711c0701bc6d1b46d1b06c1ac691a4681986318c6318c6218862184611805e1785e1745d1705a1685915c541505414c53148501404f1344a1284911c44100401003f0fc3e0f03c0ec390d8360d4330c02c0b02b0a4260881d0741c0681704c0e02000 >>> (10*j)) % 1024) (fun j : ℕ => (0x100401004010040100401003fcff3fcff3fcff3fcfe3f8fe3f8fe3f8fd3f4fd3f4fd3f0fc3f0fc3ecfb3ecfa3e8f93dcf73dcf73dcf73d8f63d8f63d8f53d4f53d4f43d0f43ccf33c8f03c0f03c0f03bcef3bcef3b8ee3b8ed3b4ec3a8ea3a8ea3a4e93a4e83a0e7394e5394e4390e3384e1380de36cdb36cdb36cda368da368d9364d9360d835cd5354d5354d4350d434cd3348d0340d033ccf338cc330cb324c6318c6318c5314c5310c430cc1304c1300c02fcbd2f4bc2e8b72dcb72d8b62d4b32ccb22c0ad2b4ac2a8a728ca328ca3288a2288a1284a02789e2789d2749c2689a26497250942509324c922409023c8d2288a2248721080200801fc7f1f87c1f07b1e4761d8751cc701b06c1ac69198621745d1745c1705b164591605614c53148501344912448118430fc3a0e8390dc340c02b094250902207c1b0581002400 >>> (10*j)) % 1024) 128
  let test := (fun i : ℕ => (List.range (128+1)).all (fun j => decide ((fun j : ℕ => (0x100401004010040100401003fcff3fcff3fcff3fcfe3f8fe3f8fe3f8fd3f4fd3f4fd3f0fc3f0fc3ecfb3ecfa3e8f93dcf73dcf73dcf73d8f63d8f63d8f53d4f53d4f43d0f43ccf33c8f03c0f03c0f03bcef3bcef3b8ee3b8ed3b4ec3a8ea3a8ea3a4e93a4e83a0e7394e5394e4390e3384e1380de36cdb36cdb36cda368da368d9364d9360d835cd5354d5354d4350d434cd3348d0340d033ccf338cc330cb324c6318c6318c5314c5310c430cc1304c1300c02fcbd2f4bc2e8b72dcb72d8b62d4b32ccb22c0ad2b4ac2a8a728ca328ca3288a2288a1284a02789e2789d2749c2689a26497250942509324c922409023c8d2288a2248721080200801fc7f1f87c1f07b1e4761d8751cc701b06c1ac69198621745d1745c1705b164591605614c53148501344912448118430fc3a0e8390dc340c02b094250902207c1b0581002400 >>> (10*j)) % 1024) (i+j) ≤ max ((fun j : ℕ => (0x802008020080200802007f1fc7f1fc7f1fc7e1f87e1f87e1f47d1f47d1f07c1f07b1ec7a1e0781e0781e0771dc771dc761d8761d4751d0721c8721c8711c4711c0701bc6d1b46d1b06c1ac691a4681986318c6318c6218862184611805e1785e1745d1705a1685915c541505414c53148501404f1344a1284911c44100401003f0fc3e0f03c0ec390d8360d4330c02c0b02b0a4260881d0741c0681704c0e02000 >>> (10*j)) % 1024) i) j + max ((fun j : ℕ => (0x802008020080200802007f1fc7f1fc7f1fc7e1f87e1f87e1f47d1f47d1f07c1f07b1ec7a1e0781e0781e0771dc771dc761d8761d4751d0721c8721c8711c4711c0701bc6d1b46d1b06c1ac691a4681986318c6318c6218862184611805e1785e1745d1705a1685915c541505414c53148501404f1344a1284911c44100401003f0fc3e0f03c0ec390d8360d4330c02c0b02b0a4260881d0741c0681704c0e02000 >>> (10*j)) % 1024) j) i)))
  change (List.range 129).all test=true
  have block0 : (List.range 0).all test=true := rfl
  have block4 := verifyBlocks test 0 4 block0 (by decide +kernel)
  have block8 := verifyBlocks test 4 4 block4 (by decide +kernel)
  have block12 := verifyBlocks test 8 4 block8 (by decide +kernel)
  have block16 := verifyBlocks test 12 4 block12 (by decide +kernel)
  have block20 := verifyBlocks test 16 4 block16 (by decide +kernel)
  have block24 := verifyBlocks test 20 4 block20 (by decide +kernel)
  have block28 := verifyBlocks test 24 4 block24 (by decide +kernel)
  have block32 := verifyBlocks test 28 4 block28 (by decide +kernel)
  have block36 := verifyBlocks test 32 4 block32 (by decide +kernel)
  have block40 := verifyBlocks test 36 4 block36 (by decide +kernel)
  have block44 := verifyBlocks test 40 4 block40 (by decide +kernel)
  have block48 := verifyBlocks test 44 4 block44 (by decide +kernel)
  have block52 := verifyBlocks test 48 4 block48 (by decide +kernel)
  have block56 := verifyBlocks test 52 4 block52 (by decide +kernel)
  have block60 := verifyBlocks test 56 4 block56 (by decide +kernel)
  have block64 := verifyBlocks test 60 4 block60 (by decide +kernel)
  have block68 := verifyBlocks test 64 4 block64 (by decide +kernel)
  have block72 := verifyBlocks test 68 4 block68 (by decide +kernel)
  have block76 := verifyBlocks test 72 4 block72 (by decide +kernel)
  have block80 := verifyBlocks test 76 4 block76 (by decide +kernel)
  have block84 := verifyBlocks test 80 4 block80 (by decide +kernel)
  have block88 := verifyBlocks test 84 4 block84 (by decide +kernel)
  have block92 := verifyBlocks test 88 4 block88 (by decide +kernel)
  have block96 := verifyBlocks test 92 4 block92 (by decide +kernel)
  have block100 := verifyBlocks test 96 4 block96 (by decide +kernel)
  have block104 := verifyBlocks test 100 4 block100 (by decide +kernel)
  have block108 := verifyBlocks test 104 4 block104 (by decide +kernel)
  have block112 := verifyBlocks test 108 4 block108 (by decide +kernel)
  have block116 := verifyBlocks test 112 4 block112 (by decide +kernel)
  have block120 := verifyBlocks test 116 4 block116 (by decide +kernel)
  have block124 := verifyBlocks test 120 4 block120 (by decide +kernel)
  have block128 := verifyBlocks test 124 4 block124 (by decide +kernel)
  have block129 := verifyBlocks test 128 1 block128 (by decide +kernel)
  exact block129

lemma table8 (K : ℕ) (hK : K = 158 ∨ K = 207 ∨ K = 224) : ∀ i j : Fin (256+1), (fun j : ℕ => if j=K then K+(if K=224 then 143 else 148) else 0) (i.val+j.val) ≤ max ((fun j : ℕ => (0x100401004010040100401003fcff3fcff3fcff3fcfe3f8fe3f8fe3f8fd3f4fd3f4fd3f0fc3f0fc3ecfb3ecfa3e8f93dcf73dcf73dcf73d8f63d8f63d8f53d4f53d4f43d0f43ccf33c8f03c0f03c0f03bcef3bcef3b8ee3b8ed3b4ec3a8ea3a8ea3a4e93a4e83a0e7394e5394e4390e3384e1380de36cdb36cdb36cda368da368d9364d9360d835cd5354d5354d4350d434cd3348d0340d033ccf338cc330cb324c6318c6318c5314c5310c430cc1304c1300c02fcbd2f4bc2e8b72dcb72d8b62d4b32ccb22c0ad2b4ac2a8a728ca328ca3288a2288a1284a02789e2789d2749c2689a26497250942509324c922409023c8d2288a2248721080200801fc7f1f87c1f07b1e4761d8751cc701b06c1ac69198621745d1745c1705b164591605614c53148501344912448118430fc3a0e8390dc340c02b094250902207c1b0581002400 >>> (10*j)) % 1024) i.val) j.val + max ((fun j : ℕ => (0x100401004010040100401003fcff3fcff3fcff3fcfe3f8fe3f8fe3f8fd3f4fd3f4fd3f0fc3f0fc3ecfb3ecfa3e8f93dcf73dcf73dcf73d8f63d8f63d8f53d4f53d4f43d0f43ccf33c8f03c0f03c0f03bcef3bcef3b8ee3b8ed3b4ec3a8ea3a8ea3a4e93a4e83a0e7394e5394e4390e3384e1380de36cdb36cdb36cda368da368d9364d9360d835cd5354d5354d4350d434cd3348d0340d033ccf338cc330cb324c6318c6318c5314c5310c430cc1304c1300c02fcbd2f4bc2e8b72dcb72d8b62d4b32ccb22c0ad2b4ac2a8a728ca328ca3288a2288a1284a02789e2789d2749c2689a26497250942509324c922409023c8d2288a2248721080200801fc7f1f87c1f07b1e4761d8751cc701b06c1ac69198621745d1745c1705b164591605614c53148501344912448118430fc3a0e8390dc340c02b094250902207c1b0581002400 >>> (10*j)) % 1024) j.val) i.val := by
  rcases hK with rfl | rfl | rfl
  · intro i j
    change (if i.val+j.val=158 then 306 else 0)≤_
    split
    · rename_i eq
      have chk : ∀ t ∈ List.range 159, 306 ≤ max ((fun j : ℕ => (0x100401004010040100401003fcff3fcff3fcff3fcfe3f8fe3f8fe3f8fd3f4fd3f4fd3f0fc3f0fc3ecfb3ecfa3e8f93dcf73dcf73dcf73d8f63d8f63d8f53d4f53d4f43d0f43ccf33c8f03c0f03c0f03bcef3bcef3b8ee3b8ed3b4ec3a8ea3a8ea3a4e93a4e83a0e7394e5394e4390e3384e1380de36cdb36cdb36cda368da368d9364d9360d835cd5354d5354d4350d434cd3348d0340d033ccf338cc330cb324c6318c6318c5314c5310c430cc1304c1300c02fcbd2f4bc2e8b72dcb72d8b62d4b32ccb22c0ad2b4ac2a8a728ca328ca3288a2288a1284a02789e2789d2749c2689a26497250942509324c922409023c8d2288a2248721080200801fc7f1f87c1f07b1e4761d8751cc701b06c1ac69198621745d1745c1705b164591605614c53148501344912448118430fc3a0e8390dc340c02b094250902207c1b0581002400 >>> (10*j)) % 1024) t) (158-t) + max ((fun j : ℕ => (0x100401004010040100401003fcff3fcff3fcff3fcfe3f8fe3f8fe3f8fd3f4fd3f4fd3f0fc3f0fc3ecfb3ecfa3e8f93dcf73dcf73dcf73d8f63d8f63d8f53d4f53d4f43d0f43ccf33c8f03c0f03c0f03bcef3bcef3b8ee3b8ed3b4ec3a8ea3a8ea3a4e93a4e83a0e7394e5394e4390e3384e1380de36cdb36cdb36cda368da368d9364d9360d835cd5354d5354d4350d434cd3348d0340d033ccf338cc330cb324c6318c6318c5314c5310c430cc1304c1300c02fcbd2f4bc2e8b72dcb72d8b62d4b32ccb22c0ad2b4ac2a8a728ca328ca3288a2288a1284a02789e2789d2749c2689a26497250942509324c922409023c8d2288a2248721080200801fc7f1f87c1f07b1e4761d8751cc701b06c1ac69198621745d1745c1705b164591605614c53148501344912448118430fc3a0e8390dc340c02b094250902207c1b0581002400 >>> (10*j)) % 1024) (158-t)) t := by decide +kernel
      have v := chk i.val (List.mem_range.mpr (by omega))
      rwa [show 158-i.val=j.val by omega] at v
    · omega
  · intro i j
    change (if i.val+j.val=207 then 355 else 0)≤_
    split
    · rename_i eq
      have chk : ∀ t ∈ List.range 208, 355 ≤ max ((fun j : ℕ => (0x100401004010040100401003fcff3fcff3fcff3fcfe3f8fe3f8fe3f8fd3f4fd3f4fd3f0fc3f0fc3ecfb3ecfa3e8f93dcf73dcf73dcf73d8f63d8f63d8f53d4f53d4f43d0f43ccf33c8f03c0f03c0f03bcef3bcef3b8ee3b8ed3b4ec3a8ea3a8ea3a4e93a4e83a0e7394e5394e4390e3384e1380de36cdb36cdb36cda368da368d9364d9360d835cd5354d5354d4350d434cd3348d0340d033ccf338cc330cb324c6318c6318c5314c5310c430cc1304c1300c02fcbd2f4bc2e8b72dcb72d8b62d4b32ccb22c0ad2b4ac2a8a728ca328ca3288a2288a1284a02789e2789d2749c2689a26497250942509324c922409023c8d2288a2248721080200801fc7f1f87c1f07b1e4761d8751cc701b06c1ac69198621745d1745c1705b164591605614c53148501344912448118430fc3a0e8390dc340c02b094250902207c1b0581002400 >>> (10*j)) % 1024) t) (207-t) + max ((fun j : ℕ => (0x100401004010040100401003fcff3fcff3fcff3fcfe3f8fe3f8fe3f8fd3f4fd3f4fd3f0fc3f0fc3ecfb3ecfa3e8f93dcf73dcf73dcf73d8f63d8f63d8f53d4f53d4f43d0f43ccf33c8f03c0f03c0f03bcef3bcef3b8ee3b8ed3b4ec3a8ea3a8ea3a4e93a4e83a0e7394e5394e4390e3384e1380de36cdb36cdb36cda368da368d9364d9360d835cd5354d5354d4350d434cd3348d0340d033ccf338cc330cb324c6318c6318c5314c5310c430cc1304c1300c02fcbd2f4bc2e8b72dcb72d8b62d4b32ccb22c0ad2b4ac2a8a728ca328ca3288a2288a1284a02789e2789d2749c2689a26497250942509324c922409023c8d2288a2248721080200801fc7f1f87c1f07b1e4761d8751cc701b06c1ac69198621745d1745c1705b164591605614c53148501344912448118430fc3a0e8390dc340c02b094250902207c1b0581002400 >>> (10*j)) % 1024) (207-t)) t := by decide +kernel
      have v := chk i.val (List.mem_range.mpr (by omega))
      rwa [show 207-i.val=j.val by omega] at v
    · omega
  · intro i j
    change (if i.val+j.val=224 then 367 else 0)≤_
    split
    · rename_i eq
      have chk : ∀ t ∈ List.range 225, 367 ≤ max ((fun j : ℕ => (0x100401004010040100401003fcff3fcff3fcff3fcfe3f8fe3f8fe3f8fd3f4fd3f4fd3f0fc3f0fc3ecfb3ecfa3e8f93dcf73dcf73dcf73d8f63d8f63d8f53d4f53d4f43d0f43ccf33c8f03c0f03c0f03bcef3bcef3b8ee3b8ed3b4ec3a8ea3a8ea3a4e93a4e83a0e7394e5394e4390e3384e1380de36cdb36cdb36cda368da368d9364d9360d835cd5354d5354d4350d434cd3348d0340d033ccf338cc330cb324c6318c6318c5314c5310c430cc1304c1300c02fcbd2f4bc2e8b72dcb72d8b62d4b32ccb22c0ad2b4ac2a8a728ca328ca3288a2288a1284a02789e2789d2749c2689a26497250942509324c922409023c8d2288a2248721080200801fc7f1f87c1f07b1e4761d8751cc701b06c1ac69198621745d1745c1705b164591605614c53148501344912448118430fc3a0e8390dc340c02b094250902207c1b0581002400 >>> (10*j)) % 1024) t) (224-t) + max ((fun j : ℕ => (0x100401004010040100401003fcff3fcff3fcff3fcfe3f8fe3f8fe3f8fd3f4fd3f4fd3f0fc3f0fc3ecfb3ecfa3e8f93dcf73dcf73dcf73d8f63d8f63d8f53d4f53d4f43d0f43ccf33c8f03c0f03c0f03bcef3bcef3b8ee3b8ed3b4ec3a8ea3a8ea3a4e93a4e83a0e7394e5394e4390e3384e1380de36cdb36cdb36cda368da368d9364d9360d835cd5354d5354d4350d434cd3348d0340d033ccf338cc330cb324c6318c6318c5314c5310c430cc1304c1300c02fcbd2f4bc2e8b72dcb72d8b62d4b32ccb22c0ad2b4ac2a8a728ca328ca3288a2288a1284a02789e2789d2749c2689a26497250942509324c922409023c8d2288a2248721080200801fc7f1f87c1f07b1e4761d8751cc701b06c1ac69198621745d1745c1705b164591605614c53148501344912448118430fc3a0e8390dc340c02b094250902207c1b0581002400 >>> (10*j)) % 1024) (224-t)) t := by decide +kernel
      have v := chk i.val (List.mem_range.mpr (by omega))
      rwa [show 224-i.val=j.val by omega] at v
    · omega

lemma count_growth (r K gap : ℕ) (positive : 0<K) (topBound : K≤2^r) (M : ℕ) (A : Finset ℕ) (hc : A.card=r) (hA : IsSumDistinctSet A M)
    (growth : ∀ (C : Finset ℕ → ℤ → ℕ), (∀ B, Monotone (C B)) → (∀ B z, C B z ≤ 2^B.card) →
      (∀ B a, a∉B → ∀ z, C (insert a B) z = C B z + C B (z-a)) →
      ∀ B : Finset ℕ, B.card=r → (∀ a∈B, a≤M) → ∀ z, C B z=K → K+gap≤C B (z+M)) : gap ≤ M ∧ gap ≤ (A.powerset.image (fun S ↦ S.sum id % M)).card ∧
    ∃ t ∈ A.powerset.image (fun S ↦ S.sum id),
      ((A.powerset.image (fun S ↦ S.sum id)).filter (· ≤ t)).card = K ∧
      K + gap ≤ ((A.powerset.image (fun S ↦ S.sum id)).filter (· ≤ t+M)).card := by
  classical
  let val (X : Finset ℕ) : ℤ := (X.sum id : ℕ)
  let P (B : Finset ℕ) (z : ℤ) := B.powerset.filter (fun X => val X ≤ z)
  let C (B : Finset ℕ) (z : ℤ) := (P B z).card
  have sub (B : Finset ℕ) {z w : ℤ} (hw : z≤w) : P B z ⊆ P B w :=
    fun _ h => mem_filter.mpr ⟨(mem_filter.mp h).1,(mem_filter.mp h).2.trans hw⟩
  have monoC (B) : Monotone (C B) := fun _ _ h => card_le_card (sub B h)
  have sizeC (B z) : C B z ≤ 2^B.card := (card_filter_le _ _).trans_eq (card_powerset _)
  have sums (B z) : C B z = ∑ X∈B.powerset, (if val X ≤ z then 1 else 0 : ℕ) := by
    simp [C,P,Finset.sum_boole]
  have stepC (B : Finset ℕ) (a : ℕ) (ha : a∉B) (z : ℤ) :
      C (insert a B) z = C B z + C B (z-a) := by
    rw [sums,sum_powerset_insert ha,sums,sums]
    apply congrArg (_ + ·)
    apply sum_congr rfl
    intro X hX
    have nmem : a∉X := fun q => ha (mem_powerset.mp hX q)
    have vs : val (insert a X) = (a : ℤ) + val X := by simp [val,sum_insert nmem]
    simp only [vs,show ((a:ℤ) + val X ≤ z) ↔ val X ≤ z - a by omega]
  have diff (z : ℤ) (n : ℕ) : C A (z+n) ≤ C A z + n := by
    let D := P A (z+n) \ P A z
    have inj : Set.InjOn val (D : Set (Finset ℕ)) := by
      intro X hx Y hy equal
      have hX := (mem_filter.mp (mem_sdiff.mp hx).1).1
      have hY := (mem_filter.mp (mem_sdiff.mp hy).1).1
      have raw : X.sum id = Y.sum id := Int.ofNat_inj.mp equal
      have e := @hA.2 ⟨X,hX⟩ ⟨Y,hY⟩ raw
      exact congrArg Subtype.val e
    have img : D.image val ⊆ Ioc z (z+n) := by
      intro u hu
      obtain ⟨X,hX,rfl⟩ := mem_image.mp hu
      obtain ⟨hfull,hn⟩ := mem_sdiff.mp hX
      obtain ⟨ha,hi⟩ := mem_filter.mp hfull
      exact mem_Ioc.mpr ⟨lt_of_not_ge (fun h => hn (mem_filter.mpr ⟨ha,h⟩)),hi⟩
    have d := card_le_card img
    rw [card_image_of_injOn inj,Int.card_Ioc] at d
    have eq := card_sdiff_add_card_eq_card (sub A (show z≤z+(n:ℤ) by omega))
    change D.card + C A z = C A (z+n) at eq
    omega
  have left : C A (-1)=0 := by
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro X h
    have neg := (mem_filter.mp h).2
    have pos : 0≤val X := Int.natCast_nonneg _
    omega
  have top : K ≤ C A (A.sum id : ℕ) := by
    have all : P A (A.sum id : ℕ) = A.powerset := by
      apply filter_true_of_mem
      intro X hx
      change ((X.sum id : ℕ) : ℤ) ≤ ((A.sum id : ℕ) : ℤ)
      exact_mod_cast (sum_le_sum_of_subset (mem_powerset.mp hx) : X.sum id ≤ A.sum id)
    change K ≤ (P A _).card
    rw [all,card_powerset,hc]
    exact topBound
  let good (t : ℕ) := K ≤ C A (t:ℤ)
  have ex : ∃ t, good t := ⟨A.sum id,top⟩
  let t := Nat.find ex
  have cur : K≤C A (t:ℤ) := Nat.find_spec ex
  have before : C A ((t:ℤ)-1) < K := by
    by_cases zero : t=0
    · simpa [zero,left] using positive
    · have h : ¬good (t-1) := Nat.find_min ex (show t-1<t by omega)
      change ¬K ≤ C A ((t-1 : ℕ):ℤ) at h
      rw [Nat.cast_sub (by omega : 1≤t),Nat.cast_one] at h
      exact Nat.lt_of_not_ge h
  have upper := diff ((t:ℤ)-1) 1
  simp only [Nat.cast_one,sub_add_cancel] at upper
  have hit : C A (t:ℤ)=K := by omega
  have large := growth C monoC sizeC stepC A hc (fun a ha => (mem_Icc.mp (hA.1 ha)).2) t hit
  have short := diff (t:ℤ) M
  refine ⟨by omega, ?_⟩
  constructor
  · let W := P A ((t:ℤ)+M) \ P A (t:ℤ)
    have window {S} (hs : S ∈ W) :
        (t:ℤ) < (S.sum id : ℕ) ∧ ((S.sum id : ℕ) : ℤ) ≤ t+M := by
      obtain ⟨hi,lo⟩ := mem_sdiff.mp hs
      obtain ⟨hS,hhi⟩ := mem_filter.mp hi
      exact ⟨lt_of_not_ge (fun h ↦ lo (mem_filter.mpr ⟨hS,h⟩)),hhi⟩
    have hw (S) (hs : S ∈ W) : S ∈ A.powerset :=
      (mem_filter.mp (mem_sdiff.mp hs).1).1
    have hmod : Set.InjOn (fun S : Finset ℕ ↦ S.sum id % M) (W : Set (Finset ℕ)) := by
      intro X hx Y hy hh
      have hX := window hx
      have hY := window hy
      have heq : X.sum id = Y.sum id := Nat.ModEq.eq_of_abs_lt hh (abs_lt.mpr (by omega))
      exact congrArg Subtype.val (@hA.2 ⟨X,hw _ hx⟩ ⟨Y,hw _ hy⟩ heq)
    have hsize := card_le_card (image_subset_image (f := fun S : Finset ℕ ↦ S.sum id % M) hw)
    rw [card_image_of_injOn hmod] at hsize
    have hcard := card_sdiff_add_card_eq_card (sub A (show (t:ℤ) ≤ t+M by omega))
    change W.card + C A t = C A ((t:ℤ)+M) at hcard
    omega
  · let V := A.powerset.image (fun S ↦ S.sum id)
    have hmem : t ∈ V := by
      by_contra hh
      have incl : P A (t:ℤ) ⊆ P A ((t:ℤ)-1) := by
        intro S hS
        obtain ⟨hs,hb⟩ := mem_filter.mp hS
        have hn : S.sum id ≠ t := fun he ↦ hh (mem_image.mpr ⟨S,hs,he⟩)
        change ((S.sum id : ℕ) : ℤ) ≤ t at hb
        exact mem_filter.mpr ⟨hs,show ((S.sum id : ℕ) : ℤ) ≤ (t:ℤ)-1 by omega⟩
      have hc := card_le_card incl
      change C A t ≤ C A ((t:ℤ)-1) at hc
      omega
    have counts (u : ℕ) : (V.filter (· ≤ u)).card = C A (u:ℤ) := by
      have he : V.filter (· ≤ u) = (P A (u:ℤ)).image (fun S ↦ S.sum id) := by
        ext n
        simp only [V,P,val,mem_filter,mem_image,Nat.cast_le]
        constructor
        · rintro ⟨⟨S,hs,rfl⟩,hb⟩
          exact ⟨S,⟨hs,hb⟩,rfl⟩
        · rintro ⟨S,⟨hs,hb⟩,rfl⟩
          exact ⟨⟨S,hs,rfl⟩,hb⟩
      have hinj : Set.InjOn (fun S : Finset ℕ ↦ S.sum id) (P A (u:ℤ)) := by
        intro X hx Y hy hh
        exact congrArg Subtype.val (@hA.2 ⟨X,(mem_filter.mp hx).1⟩ ⟨Y,(mem_filter.mp hy).1⟩ hh)
      rw [he,card_image_of_injOn hinj]
    exact ⟨t,hmem,(counts t).trans hit,by rwa [counts,Nat.cast_add]⟩
lemma all_growth (C : Finset ℕ → ℤ → ℕ) (M : ℕ)
    (monoC : ∀ A, Monotone (C A)) (sizeC : ∀ A z, C A z ≤ 2^A.card)
    (stepC : ∀ A a, a∉A → ∀ z, C (insert a A) z = C A z + C A (z-a))
    (K : ℕ) (hK : K = 158 ∨ K = 207 ∨ K = 224) :
    (∀ B : Finset ℕ, B.card=1 → (∀ a∈B, a≤M) → ∀ z, C B z=1 → 1+1≤C B (z+M)) ∧
    (∀ B : Finset ℕ, B.card=2 → (∀ a∈B, a≤M) → ∀ z, C B z=1 → 1+2≤C B (z+M)) ∧
    (∀ B : Finset ℕ, B.card=3 → (∀ a∈B, a≤M) → ∀ z, C B z=2 → 2+4≤C B (z+M)) ∧
    (∀ B : Finset ℕ, B.card=4 → (∀ a∈B, a≤M) → ∀ z, C B z=3 → 3+7≤C B (z+M)) ∧
    (∀ B : Finset ℕ, B.card=5 → (∀ a∈B, a≤M) → ∀ z, C B z=8 → 8+13≤C B (z+M)) ∧
    (∀ B : Finset ℕ, B.card=6 → (∀ a∈B, a≤M) → ∀ z, C B z=14 → 14+23≤C B (z+M)) ∧
    (∀ B : Finset ℕ, B.card=7 → (∀ a∈B, a≤M) → ∀ z, C B z=36 → 36+43≤C B (z+M)) ∧
    (∀ B : Finset ℕ, B.card=8 → (∀ a∈B, a≤M) → ∀ z, C B z=65 → 65+78≤C B (z+M)) ∧
    (∀ B : Finset ℕ, B.card=9 → (∀ a∈B, a≤M) → ∀ z, C B z=K → K+(if K=224 then 143 else 148)≤C B (z+M)) := by
  have base : ∀ A : Finset ℕ, A.card=0 → (∀ a∈A, a≤M) → ∀ z, id (C A z) ≤ C A (z+M) :=
    fun A _ _ z => monoC A (show z ≤ z + (M:ℤ) by omega)
  have h1 := iterate C M monoC sizeC stepC 0 id (fun j : ℕ => (0x200800 >>> (10*j)) % 1024) base table0
  have h2 := iterate C M monoC sizeC stepC 1 (fun j : ℕ => (0x200800 >>> (10*j)) % 1024) (fun j : ℕ => (0x40100400c00 >>> (10*j)) % 1024) h1 table1
  have h3 := iterate C M monoC sizeC stepC 2 (fun j : ℕ => (0x40100400c00 >>> (10*j)) % 1024) (fun j : ℕ => (0x8020080200701c0601000 >>> (10*j)) % 1024) h2 table2
  have h4 := iterate C M monoC sizeC stepC 3 (fun j : ℕ => (0x8020080200701c0601000 >>> (10*j)) % 1024) (fun j : ℕ => (0x10040100401003c0f03c0e0380d02c0b0280801400 >>> (10*j)) % 1024) h3 table3
  have h5 := iterate C M monoC sizeC stepC 4 (fun j : ℕ => (0x10040100401003c0f03c0e0380d02c0b0280801400 >>> (10*j)) % 1024) (fun j : ℕ => (0x2008020080200801f07c1f07c1e0781e0741d0701a0681a06419060160581504c100400f0340a01800 >>> (10*j)) % 1024) h4 table4
  have h6 := iterate C M monoC sizeC stepC 5 (fun j : ℕ => (0x2008020080200801f07c1f07c1e0781e0741d0701a0681a06419060160581504c100400f0340a01800 >>> (10*j)) % 1024) (fun j : ℕ => (0x401004010040100400fc3f0fc3f0fc3e0f83e0f83d0f43d0f03c0ec390e4390e4380e0380dc370d8340d0340cc330c8300c02f0b42a0a82a0a4290a0260982508c200801f0741a05816054130400c01c00 >>> (10*j)) % 1024) h5 table5
  have h7 := iterate C M monoC sizeC stepC 6 (fun j : ℕ => (0x401004010040100400fc3f0fc3f0fc3e0f83e0f83d0f43d0f03c0ec390e4390e4380e0380dc370d8340d0340cc330c8300c02f0b42a0a82a0a4290a0260982508c200801f0741a05816054130400c01c00 >>> (10*j)) % 1024) (fun j : ℕ => (0x802008020080200802007f1fc7f1fc7f1fc7e1f87e1f87e1f47d1f47d1f07c1f07b1ec7a1e0781e0781e0771dc771dc761d8761d4751d0721c8721c8711c4711c0701bc6d1b46d1b06c1ac691a4681986318c6318c6218862184611805e1785e1745d1705a1685915c541505414c53148501404f1344a1284911c44100401003f0fc3e0f03c0ec390d8360d4330c02c0b02b0a4260881d0741c0681704c0e02000 >>> (10*j)) % 1024) h6 table6
  have h8 := iterate C M monoC sizeC stepC 7 (fun j : ℕ => (0x802008020080200802007f1fc7f1fc7f1fc7e1f87e1f87e1f47d1f47d1f07c1f07b1ec7a1e0781e0781e0771dc771dc761d8761d4751d0721c8721c8711c4711c0701bc6d1b46d1b06c1ac691a4681986318c6318c6218862184611805e1785e1745d1705a1685915c541505414c53148501404f1344a1284911c44100401003f0fc3e0f03c0ec390d8360d4330c02c0b02b0a4260881d0741c0681704c0e02000 >>> (10*j)) % 1024) (fun j : ℕ => (0x100401004010040100401003fcff3fcff3fcff3fcfe3f8fe3f8fe3f8fd3f4fd3f4fd3f0fc3f0fc3ecfb3ecfa3e8f93dcf73dcf73dcf73d8f63d8f63d8f53d4f53d4f43d0f43ccf33c8f03c0f03c0f03bcef3bcef3b8ee3b8ed3b4ec3a8ea3a8ea3a4e93a4e83a0e7394e5394e4390e3384e1380de36cdb36cdb36cda368da368d9364d9360d835cd5354d5354d4350d434cd3348d0340d033ccf338cc330cb324c6318c6318c5314c5310c430cc1304c1300c02fcbd2f4bc2e8b72dcb72d8b62d4b32ccb22c0ad2b4ac2a8a728ca328ca3288a2288a1284a02789e2789d2749c2689a26497250942509324c922409023c8d2288a2248721080200801fc7f1f87c1f07b1e4761d8751cc701b06c1ac69198621745d1745c1705b164591605614c53148501344912448118430fc3a0e8390dc340c02b094250902207c1b0581002400 >>> (10*j)) % 1024) h7 table7
  have h9 := iterate C M monoC sizeC stepC 8 (fun j : ℕ => (0x100401004010040100401003fcff3fcff3fcff3fcfe3f8fe3f8fe3f8fd3f4fd3f4fd3f0fc3f0fc3ecfb3ecfa3e8f93dcf73dcf73dcf73d8f63d8f63d8f53d4f53d4f43d0f43ccf33c8f03c0f03c0f03bcef3bcef3b8ee3b8ed3b4ec3a8ea3a8ea3a4e93a4e83a0e7394e5394e4390e3384e1380de36cdb36cdb36cda368da368d9364d9360d835cd5354d5354d4350d434cd3348d0340d033ccf338cc330cb324c6318c6318c5314c5310c430cc1304c1300c02fcbd2f4bc2e8b72dcb72d8b62d4b32ccb22c0ad2b4ac2a8a728ca328ca3288a2288a1284a02789e2789d2749c2689a26497250942509324c922409023c8d2288a2248721080200801fc7f1f87c1f07b1e4761d8751cc701b06c1ac69198621745d1745c1705b164591605614c53148501344912448118430fc3a0e8390dc340c02b094250902207c1b0581002400 >>> (10*j)) % 1024) (fun j : ℕ => if j=K then K+(if K=224 then 143 else 148) else 0) h8 (table8 K hK)
  refine ⟨?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ⟩
  · intro B hc hb z hit
    have res := h1 B hc hb z
    rw [hit] at res
    exact res
  · intro B hc hb z hit
    have res := h2 B hc hb z
    rw [hit] at res
    exact res
  · intro B hc hb z hit
    have res := h3 B hc hb z
    rw [hit] at res
    exact res
  · intro B hc hb z hit
    have res := h4 B hc hb z
    rw [hit] at res
    exact res
  · intro B hc hb z hit
    have res := h5 B hc hb z
    rw [hit] at res
    exact res
  · intro B hc hb z hit
    have res := h6 B hc hb z
    rw [hit] at res
    exact res
  · intro B hc hb z hit
    have res := h7 B hc hb z
    rw [hit] at res
    exact res
  · intro B hc hb z hit
    have res := h8 B hc hb z
    rw [hit] at res
    exact res
  · intro B hc hb z hit
    have res := h9 B hc hb z
    rw [hit] at res
    simpa using res
lemma lower (A : Finset ℕ) (M : ℕ) (r : ℕ) (small : r≤9) (hc : A.card=r) (distinct : IsSumDistinctSet A M) :
    ([0,1,2,4,7,13,23,43,78,148] : List ℕ)[r]! ≤ M := by
  interval_cases r
  · exact Nat.zero_le M
  · exact (count_growth 1 1 1 (by decide) (by decide) M A hc distinct (fun C mono sz step => (all_growth C M mono sz step 158 (Or.inl rfl)).1)).1
  · exact (count_growth 2 1 2 (by decide) (by decide) M A hc distinct (fun C mono sz step => (all_growth C M mono sz step 158 (Or.inl rfl)).2.1)).1
  · exact (count_growth 3 2 4 (by decide) (by decide) M A hc distinct (fun C mono sz step => (all_growth C M mono sz step 158 (Or.inl rfl)).2.2.1)).1
  · exact (count_growth 4 3 7 (by decide) (by decide) M A hc distinct (fun C mono sz step => (all_growth C M mono sz step 158 (Or.inl rfl)).2.2.2.1)).1
  · exact (count_growth 5 8 13 (by decide) (by decide) M A hc distinct (fun C mono sz step => (all_growth C M mono sz step 158 (Or.inl rfl)).2.2.2.2.1)).1
  · exact (count_growth 6 14 23 (by decide) (by decide) M A hc distinct (fun C mono sz step => (all_growth C M mono sz step 158 (Or.inl rfl)).2.2.2.2.2.1)).1
  · exact (count_growth 7 36 43 (by decide) (by decide) M A hc distinct (fun C mono sz step => (all_growth C M mono sz step 158 (Or.inl rfl)).2.2.2.2.2.2.1)).1
  · exact (count_growth 8 65 78 (by decide) (by decide) M A hc distinct (fun C mono sz step => (all_growth C M mono sz step 158 (Or.inl rfl)).2.2.2.2.2.2.2.1)).1
  · exact (count_growth 9 158 148 (by decide) (by decide) M A hc distinct (fun C mono sz step => (all_growth C M mono sz step 158 (Or.inl rfl)).2.2.2.2.2.2.2.2)).1

end CubeWindow


set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
/-- The two small span certificates use a bitmask search after translation
to minimum 1. A common shift encodes the cardinality of each subset in its
sum. The kernel computes only the searches for these short intervals. -/
private theorem span_certificate (k B : ℕ)
    (hkB : (k = 6 ∧ B = 12) ∨ (k = 7 ∧ B = 21))
    (A : Finset ℕ) (lo : ℕ) (hlo : lo ∈ A) (hA : A ⊆ Icc lo (lo + B))
    (hc : A.card = k) :
    ¬ (∀ S ⊆ A, ∀ T ⊆ A, S.card = T.card → S.sum id = T.sum id → S = T) := by
  let mask (l : List ℕ) : ℕ := l.foldr (fun a bits => bits ||| (bits <<< a)) 1
  let hasSubsetSum (A : Finset ℕ) (n : ℕ) : Prop := ∃ S ⊆ A, S.sum id = n
  let distinctSums (A : Finset ℕ) : Prop :=
    ∀ S ⊆ A, ∀ T ⊆ A, S.sum id = T.sum id → S = T
  let pseudoDistinct (A : Finset ℕ) : Prop :=
    ∀ S ⊆ A, ∀ T ⊆ A, S.card = T.card → S.sum id = T.sum id → S = T
  let addWeight (offset : ℕ) : ℕ ↪ ℕ :=
    ⟨fun x => x + offset, fun _ _ h => Nat.add_right_cancel h⟩

  -- Branch on choosing the largest remaining index. An overlapping shifted
  -- mask discards the branch that chooses it.
  let search (weight : ℕ → ℕ) (k b bits : ℕ) : Bool :=
    Nat.rec (motive := fun _ => ℕ → ℕ → Bool)
      (fun k _ => k == 0)
      (fun b recur k bits =>
        match k with
        | 0 => true
        | k + 1 =>
          let shifted := bits <<< weight (b + 1)
          ((bits &&& shifted == 0) && recur k (bits ||| shifted)) || recur (k + 1) bits)
      b k bits
  have mask_nil : mask [] = 1 := rfl
  have mask_cons (a : ℕ) (l : List ℕ) :
      mask (a :: l) = mask l ||| (mask l <<< a) := rfl
  have search_zero_k (weight : ℕ → ℕ) (b bits : ℕ) :
      search weight 0 b bits = true := by cases b <;> rfl
  have search_succ (weight : ℕ → ℕ) (k b bits : ℕ) :
      search weight (k + 1) (b + 1) bits =
        let shifted := bits <<< weight (b + 1)
        ((bits &&& shifted == 0) && search weight k b (bits ||| shifted)) ||
          search weight (k + 1) b bits := rfl

  have distinct_mono {A B : Finset ℕ} (hAB : A ⊆ B) (hB : distinctSums B) :
      distinctSums A := by
    intro S hS T hT h
    exact hB S (hS.trans hAB) T (hT.trans hAB) h

  have has_subset_sum_insert {a n : ℕ} {A : Finset ℕ} (ha : a ∉ A) :
      hasSubsetSum (insert a A) n ↔ hasSubsetSum A n ∨
        a ≤ n ∧ hasSubsetSum A (n - a) := by
    constructor
    · rintro ⟨S, hS, hsum⟩
      by_cases hm : a ∈ S
      · right
        have Tsub : S.erase a ⊆ A := by
          intro b hb
          rcases Finset.mem_erase.mp hb with ⟨hba, hbin⟩
          exact (Finset.mem_insert.mp (hS hbin)).resolve_left hba
        have hdecomp : (S.erase a).sum id + a = n := by
          simpa only [Finset.sum_erase_add _ _ hm, id_eq] using hsum
        exact ⟨by omega, S.erase a, Tsub, by omega⟩
      · left
        refine ⟨S, ?_, hsum⟩
        intro b hb
        exact (Finset.mem_insert.mp (hS hb)).resolve_left (by rintro rfl; exact hm hb)
    · rintro (⟨S, hS, hsum⟩ | ⟨hn, S, hS, hsum⟩)
      · exact ⟨S, hS.trans (subset_insert _ _), hsum⟩
      · have hna : a ∉ S := fun h ↦ ha (hS h)
        refine ⟨insert a S, Finset.insert_subset_insert _ hS, ?_⟩
        rw [Finset.sum_insert hna, id_eq, hsum]
        omega

  have mask_testBit_iff (l : List ℕ) (hl : l.Nodup) (n : ℕ) :
      (mask l).testBit n = true ↔ hasSubsetSum l.toFinset n := by
    induction l generalizing n with
    | nil =>
        simp only [mask_nil, List.toFinset_nil, hasSubsetSum, Finset.subset_empty,
          exists_eq_left, Finset.sum_empty]
        cases n <;> simp [Nat.testBit_succ]
    | cons a l ih =>
        obtain ⟨ha, hnd⟩ := List.nodup_cons.mp hl
        have hnot : a ∉ l.toFinset := by simpa using ha
        simp only [mask_cons, Nat.testBit_or, Nat.testBit_shiftLeft, Bool.or_eq_true,
          Bool.and_eq_true, decide_eq_true_eq, ih hnd, List.toFinset_cons]
        exact (has_subset_sum_insert hnot).symm

  have shift_and_zero_of_distinct {a : ℕ} {l : List ℕ} (hl : l.Nodup) (ha : a ∉ l.toFinset)
      (h : distinctSums (insert a l.toFinset)) :
      mask l &&& (mask l <<< a) = 0 := by
    apply Nat.eq_of_testBit_eq
    intro n
    simp only [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.zero_testBit]
    by_cases hb : ((mask l).testBit n && (decide (a ≤ n) && (mask l).testBit (n - a))) = true
    · have hb' : (mask l).testBit n = true ∧ a ≤ n ∧ (mask l).testBit (n - a) = true := by
        simpa only [Bool.and_eq_true, decide_eq_true_eq] using hb
      obtain ⟨h0, han, h2⟩ := hb'
      obtain ⟨S, hS, hsumS⟩ := (mask_testBit_iff l hl n).mp h0
      obtain ⟨T, hT, hsumT⟩ := (mask_testBit_iff l hl (n - a)).mp h2
      have hna : a ∉ T := fun h' ↦ ha (hT h')
      have hsum : (insert a T).sum id = n := by
        rw [Finset.sum_insert hna, id_eq, hsumT]
        omega
      have he := h S (hS.trans (subset_insert _ _)) (insert a T)
        (Finset.insert_subset_insert _ hT) (hsumS.trans hsum.symm)
      exact False.elim (ha (hS (he ▸ Finset.mem_insert_self a T)))
    · exact Bool.eq_false_iff.mpr hb

  have search_complete (weight : ℕ ↪ ℕ) {R : Finset ℕ} {l : List ℕ} {b : ℕ}
      (hR : ∀ x ∈ R, 0 < x ∧ x ≤ b) (hl : l.Nodup)
      (hD : Disjoint (R.map weight) l.toFinset)
      (h : distinctSums (R.map weight ∪ l.toFinset)) :
      search weight R.card b (mask l) = true := by
    induction b generalizing R l with
    | zero =>
      have hE : R = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun a ha => by
        obtain ⟨h₀, h₁⟩ := hR a ha
        omega
      simp [hE, search_zero_k]
    | succ b ih =>
      cases hcard : R.card with
      | zero => simp [search_zero_k]
      | succ k =>
        by_cases hb : b + 1 ∈ R
        · have hbL : weight (b + 1) ∉ l.toFinset := fun hx =>
            (Finset.disjoint_left.mp hD) (Finset.mem_map_of_mem _ hb) hx
          have hnd : (weight (b + 1) :: l).Nodup :=
            List.nodup_cons.mpr ⟨by simpa using hbL, hl⟩
          have htail : ∀ x ∈ R.erase (b + 1), 0 < x ∧ x ≤ b := by
            intro x hx
            obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hx
            obtain ⟨h₀, h₁⟩ := hR x hmem
            exact ⟨h₀, by omega⟩
          have hdis : Disjoint ((R.erase (b + 1)).map weight)
              (weight (b + 1) :: l).toFinset := by
            rw [List.toFinset_cons, Finset.map_erase, Finset.disjoint_right]
            intro x hx
            obtain rfl | hm := Finset.mem_insert.mp hx
            · exact Finset.notMem_erase _ _
            · exact fun hr => (Finset.disjoint_left.mp hD) (Finset.mem_of_mem_erase hr) hm
          have hunion : (R.erase (b + 1)).map weight ∪ (weight (b + 1) :: l).toFinset =
              R.map weight ∪ l.toFinset := by
            rw [List.toFinset_cons, Finset.map_erase, Finset.union_insert,
              ← Finset.insert_union, Finset.insert_erase (Finset.mem_map_of_mem _ hb)]
          have hrec := ih htail hnd hdis (hunion.symm ▸ h)
          have herase : (R.erase (b + 1)).card = k := by
            rw [Finset.card_erase_of_mem hb, hcard]
            omega
          rw [herase, mask_cons] at hrec
          have hprefix : insert (weight (b + 1)) l.toFinset ⊆ R.map weight ∪ l.toFinset := by
            refine Finset.insert_subset_iff.mpr ⟨Finset.mem_union_left _
              (Finset.mem_map_of_mem _ hb), Finset.subset_union_right⟩
          have htest := shift_and_zero_of_distinct hl hbL (distinct_mono hprefix h)
          simp [search_succ, htest, hrec]
        · have htail : ∀ x ∈ R, 0 < x ∧ x ≤ b := by
            intro x hx
            obtain ⟨h₀, h₁⟩ := hR x hx
            have hne : x ≠ b + 1 := fun he => hb (he ▸ hx)
            exact ⟨h₀, by omega⟩
          have hrec := ih htail hl hD h
          rw [hcard] at hrec
          simp [search_succ, hrec]

  have sum_map_add (A : Finset ℕ) (offset : ℕ) :
      (A.map (addWeight offset)).sum id = A.sum id + A.card * offset := by
    rw [Finset.sum_map]
    change (∑ x ∈ A, (x + offset)) = A.sum id + A.card * offset
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, id_eq, Nat.cast_id]

  have sum_lt_of_card_lt {r s m n c : ℕ} (hr : r < c) (hmn : m < n) :
      r + m * c < s + n * c := by
    calc
      r + m * c < c + m * c := Nat.add_lt_add_right hr _
      _ = (m + 1) * c := by ring
      _ ≤ n * c := Nat.mul_le_mul_right _ hmn
      _ ≤ s + n * c := Nat.le_add_left _ _

  -- Adding a large common offset encodes cardinality together with each sum.
  have shifted_distinct {A : Finset ℕ} {offset : ℕ}
      (hsmall : ∀ S ⊆ A, S.sum id < offset) (hA : pseudoDistinct A) :
      distinctSums (A.map (addWeight offset)) := by
    intro S hS T hT he
    obtain ⟨S', hS', rfl⟩ := Finset.subset_map_iff.mp hS
    obtain ⟨T', hT', rfl⟩ := Finset.subset_map_iff.mp hT
    rw [sum_map_add, sum_map_add] at he
    have hc : S'.card = T'.card := by
      by_contra hn
      rcases lt_or_gt_of_ne hn with hlt | hgt
      · exact (ne_of_lt (sum_lt_of_card_lt (hsmall S' hS') hlt)) he
      · exact (ne_of_lt (sum_lt_of_card_lt (hsmall T' hT') hgt)) he.symm
    rw [hc] at he
    have hsum : S'.sum id = T'.sum id := Nat.add_right_cancel he
    rw [hA S' hS' T' hT' hc hsum]

  have sum_lt_encoding_bound {A : Finset ℕ} {k B : ℕ}
      (hA : A ⊆ Icc 1 B) (hc : A.card = k) {S : Finset ℕ} (hS : S ⊆ A) :
      S.sum id < k * B + 1 := by
    refine Nat.lt_succ_of_le ?_
    calc
      S.sum id ≤ S.card * B :=
        Finset.sum_le_card_nsmul _ _ _ fun x hx => (Finset.mem_Icc.mp (hA (hS hx))).2
      _ ≤ k * B := Nat.mul_le_mul_right _ (hc ▸ Finset.card_le_card hS)

  -- For span bounds the smallest point is translated to 1 and forced into the prefix.
  have no_normalized_of_search_false (k B : ℕ)
      (hf : search (addWeight ((k + 1) * B + 1)) k B
        (mask [addWeight ((k + 1) * B + 1) 1]) = false)
      (A : Finset ℕ) (hA : A ⊆ Icc 1 B) (hc : A.card = k + 1) (h1 : 1 ∈ A) :
      ¬ pseudoDistinct A := by
    intro h
    let w := addWeight ((k + 1) * B + 1)
    let R := A.erase 1
    have hr : R.card = k := by
      rw [Finset.card_erase_of_mem h1, hc]
      omega
    have hb : ∀ x ∈ R, 0 < x ∧ x ≤ B := by
      intro x hx
      exact Finset.mem_Icc.mp (hA (Finset.mem_of_mem_erase hx))
    have hd : Disjoint (R.map w) [w 1].toFinset := by
      simp [R, Finset.map_erase]
    have he : R.map w ∪ [w 1].toFinset = A.map w := by
      rw [List.toFinset_cons, List.toFinset_nil, Finset.union_insert, Finset.union_empty]
      change insert (w 1) ((A.erase 1).map w) = A.map w
      rw [Finset.map_erase, Finset.insert_erase (Finset.mem_map_of_mem _ h1)]
    have h' := search_complete w hb (by simp : [w 1].Nodup) hd
      (he.symm ▸ shifted_distinct (fun S hS => sum_lt_encoding_bound hA hc hS) h)
    rw [hr] at h'
    exact Bool.false_ne_true (hf.symm.trans h')

  have pseudo_map_add_iff (A : Finset ℕ) (b : ℕ) :
      pseudoDistinct (A.map (addWeight b)) ↔ pseudoDistinct A := by
    constructor
    · intro h S hS T hT hc he
      apply Finset.map_injective (addWeight b)
      apply h _ (Finset.map_subset_map.mpr hS) _ (Finset.map_subset_map.mpr hT)
      · simpa using hc
      · rw [sum_map_add, sum_map_add, he, hc]
    · intro h S hS T hT hc he
      obtain ⟨S', hS', rfl⟩ := Finset.subset_map_iff.mp hS
      obtain ⟨T', hT', rfl⟩ := Finset.subset_map_iff.mp hT
      have hc' : S'.card = T'.card := by simpa using hc
      rw [sum_map_add, sum_map_add, hc'] at he
      have hsum : S'.sum id = T'.sum id := Nat.add_right_cancel he
      rw [h S' hS' T' hT' hc' hsum]

  -- Translate an arbitrary interval so that its first point becomes 1.
  have obstruction_on_interval {k B : ℕ}
      (h : ∀ A : Finset ℕ, A ⊆ Icc 1 (B + 1) → A.card = k → 1 ∈ A → ¬ pseudoDistinct A)
      (A : Finset ℕ) (lo : ℕ) (hlo : lo ∈ A) (hA : A ⊆ Icc lo (lo + B))
      (hc : A.card = k) : ¬ pseudoDistinct A := by
    let f : ℕ → ℕ := fun x => x - lo + 1
    let C := A.image f
    have hi : Set.InjOn f (↑A : Set ℕ) := by
      intro x hx y hy he
      have hxl := (Finset.mem_Icc.mp (hA hx)).1
      have hyl := (Finset.mem_Icc.mp (hA hy)).1
      dsimp [f] at he
      omega
    have hC : C ⊆ Icc 1 (B + 1) := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨hxl, hxu⟩ := Finset.mem_Icc.mp (hA hx)
      apply Finset.mem_Icc.mpr
      dsimp [f]
      omega
    have hC1 : 1 ∈ C := Finset.mem_image.mpr ⟨lo, hlo, by simp [f]⟩
    have heq : C.map (addWeight lo) = A.map (addWeight 1) := by
      rw [Finset.map_eq_image, Finset.map_eq_image, Finset.image_image]
      refine Finset.image_congr fun x hx => ?_
      obtain ⟨hxl, _⟩ := Finset.mem_Icc.mp (hA hx)
      change x - lo + 1 + lo = x + 1
      omega
    have hCcard : C.card = k := (Finset.card_image_of_injOn hi).trans hc
    intro hP
    apply h C hC hCcard hC1
    rw [← pseudo_map_add_iff C lo, heq, pseudo_map_add_iff]
    exact hP

  rcases hkB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact obstruction_on_interval (no_normalized_of_search_false 5 13 (by decide +kernel))
      A lo hlo hA hc
  · exact obstruction_on_interval (no_normalized_of_search_false 6 22 (by decide +kernel))
      A lo hlo hA hc

/-- A span obstruction for short equal-cardinality-sum sets bounds each tail
of the increasing enumeration of a sum-distinct set. -/
private theorem tail_gap {k : ℕ} {A : Finset ℕ} {N : ℕ}
    (hA : ∀ S ⊆ A, ∀ T ⊆ A, S.sum id = T.sum id → S = T) (f : Fin k → ℕ) (hf : StrictMono f)
    (hfA : ∀ j, f j ∈ A) (hfu : ∀ j, f j ≤ N) (i : Fin k) (width : ℕ)
    (hspan : (k - i.val = 6 ∧ width = 12) ∨ (k - i.val = 7 ∧ width = 21)) :
    f i + width + 1 ≤ N := by
  by_contra! h
  let B := (Ici i).image f
  have hfi : f i ∈ B := Finset.mem_image.mpr ⟨i, Finset.mem_Ici.mpr le_rfl, rfl⟩
  have hB : B ⊆ Icc (f i) (f i + width) := by
    intro j hj
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hj
    have hbound := hfu t
    exact Finset.mem_Icc.mpr ⟨hf.monotone (Finset.mem_Ici.mp ht), by omega⟩
  have hc : B.card = k - i.val := by
    change ((Ici i).image f).card = _
    rw [Finset.card_image_of_injOn hf.injective.injOn, Fin.card_Ici]
  apply span_certificate _ _ hspan B (f i) hfi hB hc
  intro S hS T hT hc he
  have hBA : B ⊆ A := by
    intro j hj
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hj
    exact hfA t
  exact hA S (hS.trans hBA) T (hT.trans hBA) he

/-- Within the exact 160-bound search, the second-largest number is at least
96. This eliminates an entire initial choice interval before any masks. -/
private theorem second_largest_ge_96 {A : Finset ℕ}
    (hA : ∀ S ⊆ A, ∀ T ⊆ A, S.sum id = T.sum id → S = T) (hbound : ∀ x ∈ A, x ≤ 160) (hc : A.card = 9)
    (hmoment : 87381 ≤ ∑ x ∈ A, x ^ 2) :
    96 ≤ (A.orderIsoOfFin hc (7 : Fin 9)).val := by
  let e := A.orderIsoOfFin hc
  let f : Fin 9 → ℕ := fun i => (e i).val
  have hf : StrictMono f := fun _ _ h => e.strictMono h
  have hmem : ∀ i, f i ∈ A := fun i => (e i).property
  change 96 ≤ f 7
  by_contra! h
  let g : Fin 8 → ℕ := fun i => f i.castSucc
  have hg : StrictMono g := fun i j hij =>
    hf (show i.castSucc < j.castSucc from hij)
  have hgA : ∀ i, g i ∈ A := fun i => hmem i.castSucc
  have hgU : ∀ i, g i ≤ 95 := by
    intro i
    have hib : i.castSucc ≤ (7 : Fin 9) := Nat.le_of_lt_succ i.isLt
    exact (hf.monotone hib).trans (by omega)
  have h22 : g 1 + 21 + 1 ≤ 95 :=
    tail_gap hA g hg hgA hgU 1 21 (Or.inr ⟨by decide, rfl⟩)
  have h13 : g 2 + 12 + 1 ≤ 95 :=
    tail_gap hA g hg hgA hgU 2 12 (Or.inl ⟨by decide, rfl⟩)
  change f 1 + 21 + 1 ≤ 95 at h22
  change f 2 + 12 + 1 ≤ 95 at h13
  have h01 := hf (by decide : (0 : Fin 9) < 1)
  have h34 := hf (by decide : (3 : Fin 9) < 4)
  have h45 := hf (by decide : (4 : Fin 9) < 5)
  have h56 := hf (by decide : (5 : Fin 9) < 6)
  have h67 := hf (by decide : (6 : Fin 9) < 7)
  have h8 : f 8 ≤ 160 := hbound _ (hmem 8)
  let cap : Fin 9 → ℕ := ![72, 73, 82, 91, 92, 93, 94, 95, 160]
  have hcap (i : Fin 9) : f i ≤ cap i := by
    fin_cases i <;> simp [cap] <;> omega
  have hsmall : (∑ i : Fin 9, cap i ^ 2) < 87381 := by decide +kernel
  have htotal : (∑ x ∈ A, x ^ 2) < 87381 := calc
    (∑ x ∈ A, x ^ 2) = ∑ x : A, x.val ^ 2 :=
      (sum_coe_sort A (fun x : ℕ => x ^ 2)).symm
    _ = ∑ i : Fin 9, f i ^ 2 := (Fintype.sum_equiv e.toEquiv _ _ (fun _ => rfl)).symm
    _ ≤ ∑ i : Fin 9, cap i ^ 2 :=
      Finset.sum_le_sum fun i _ => Nat.pow_le_pow_left (hcap i) 2
    _ < _ := hsmall
  exact (not_lt_of_ge hmoment) htotal

private theorem extract_min {A : Finset ℕ} {k : ℕ} (h : A.card = k+1) :
    ∃ x B, insert x B = A ∧ B.card = k ∧ x ∉ B ∧ ∀ b ∈ B, x < b := by
  have hn : A.Nonempty := card_pos.mp (by omega)
  let x := A.min' hn
  have hx : x ∈ A := A.min'_mem hn
  refine ⟨x, A.erase x, insert_erase hx, ?_, notMem_erase _ _, ?_⟩
  · rw [card_erase_of_mem hx, h]; omega
  · intro b hb
    exact lt_of_le_of_ne (A.min'_le _ (mem_erase.mp hb).2) (mem_erase.mp hb).1.symm

private theorem no_difference {A B R U V : Finset ℕ}
    (hiq : ∀ S ⊆ A, ∀ T ⊆ A, S.sum id = T.sum id → S = T)
    (hBA : B ⊆ A) (hRA : R ⊆ A) (hdis : Disjoint R B)
    (hU : U ⊆ R) (hV : V ⊆ R) (hne : U ≠ V) :
    let P := B.powerset.image (fun S ↦ ((S.sum id : ℕ) : ℤ))
    ((U.sum id : ℕ) : ℤ) - (V.sum id : ℕ) ∉ P - P := by
  dsimp only
  intro hd
  obtain ⟨a, ha, b, hb, hh⟩ := mem_sub.mp hd
  obtain ⟨S, hS, rfl⟩ := mem_image.mp ha
  obtain ⟨T, hT, rfl⟩ := mem_image.mp hb
  have hSB := mem_powerset.mp hS
  have hTB := mem_powerset.mp hT
  have hu : Disjoint U T := hdis.mono hU hTB
  have hv : Disjoint V S := hdis.mono hV hSB
  have he : U ∪ T = V ∪ S := by
    apply hiq _ (union_subset (hU.trans hRA) (hTB.trans hBA)) _
      (union_subset (hV.trans hRA) (hSB.trans hBA))
    change ((S.sum id : ℕ) : ℤ) - (T.sum id : ℕ) = ((U.sum id : ℕ) : ℤ) - (V.sum id : ℕ) at hh
    rw [sum_union hu, sum_union hv]
    change U.sum id + T.sum id = V.sum id + S.sum id
    omega
  apply hne
  ext x
  by_cases hx : x ∈ R
  · have ht : x ∉ T := fun h ↦ disjoint_left.mp hdis hx (hTB h)
    have hs : x ∉ S := fun h ↦ disjoint_left.mp hdis hx (hSB h)
    simpa [ht, hs] using Finset.ext_iff.mp he x
  · exact iff_of_false (fun h ↦ hx (hU h)) (fun h ↦ hx (hV h))

private theorem ranks_fit {A : Finset ℕ}
    (hiq : ∀ S ⊆ A, ∀ T ⊆ A, S.sum id = T.sum id → S = T)
    (W : Finset ℕ) (hw : W ⊆ A) (k : ℕ) :
    let V := (W.powersetCard k).image (fun s ↦ s.sum id)
    ∀ hv : V.Nonempty, W.card.choose k ≤ V.max' hv + 1 - V.min' hv := by
  let V := (W.powersetCard k).image (fun s ↦ s.sum id)
  change ∀ hv : V.Nonempty, W.card.choose k ≤ V.max' hv + 1 - V.min' hv
  intro hv
  have hinj : Set.InjOn (fun s : Finset ℕ ↦ s.sum id) (W.powersetCard k) :=
    fun a ha b hb ↦ hiq a ((mem_powersetCard.mp ha).1.trans hw) b ((mem_powersetCard.mp hb).1.trans hw)
  have hle := card_le_card (show V ⊆ Icc (V.min' hv) (V.max' hv) from fun y hy ↦
    mem_Icc.mpr ⟨V.min'_le y hy, V.le_max' y hy⟩)
  dsimp only [V] at hle
  rwa [card_image_of_injOn hinj, card_powersetCard, Nat.card_Icc] at hle

private theorem forced_triangle (C : Finset ℕ) (D : Finset ℤ) (hD : 0 ∈ D)
    (hC : C.card = 3) (hpositive : ∀ x ∈ C, 1 ≤ x)
    (hclosure : ∀ a ∈ C, ∀ b ∈ C, a < b → b-a ∈ C) :
    ∃ J ∈ C.powerset, ((J.sum id : ℕ) : ℤ) - ((C \ J).sum id : ℕ) ∈ D := by
  let e := C.orderEmbOfFin hC
  let x := e 0
  let y := e 1
  let z := e 2
  have hx : x ∈ C := C.orderEmbOfFin_mem hC 0
  have hy : y ∈ C := C.orderEmbOfFin_mem hC 1
  have hz : z ∈ C := C.orderEmbOfFin_mem hC 2
  have hxy : x < y := e.strictMono (by decide : (0 : Fin 3) < 1)
  have hyz : y < z := e.strictMono (by decide : (1 : Fin 3) < 2)
  have heq : ({x,y,z} : Finset ℕ) = C := by
    apply eq_of_subset_of_card_le (insert_subset hx (insert_subset hy (singleton_subset_iff.mpr hz)))
    simp [hC,hxy.ne,hyz.ne,(hxy.trans hyz).ne]
  have diff (a b : ℕ) (ha : a ∈ C) (hb : b ∈ C) (hlt : a < b) :
      b-a = x ∨ b-a = y ∨ b-a = z := by
    have hd := hclosure a ha b hb hlt
    simpa [← heq] using hd
  have ha := diff x y hx hy hxy
  have hb := diff x z hx hz (hxy.trans hyz)
  have hc' := diff y z hy hz hyz
  have hpos := hpositive x hx
  have hsum : x+y=z := by omega
  refine ⟨{z},mem_powerset.mpr (singleton_subset_iff.mpr hz),?_⟩
  rw [← heq]
  have hrem : ({x,y,z} : Finset ℕ) \ {z} = {x,y} := by
    ext t
    simp only [mem_sdiff,mem_insert,mem_singleton]
    constructor
    · rintro ⟨hx | hy | hz, hn⟩
      · exact Or.inl hx
      · exact Or.inr hy
      · exact (hn hz).elim
    · rintro (hx | hy)
      · exact ⟨Or.inl hx, hx ▸ (hxy.trans hyz).ne⟩
      · exact ⟨Or.inr (Or.inl hy), hy ▸ hyz.ne⟩
  rw [hrem]
  simpa [hxy.ne, ← hsum, Nat.cast_add] using hD

/-- Residual graph triangles at maximum 148. -/
def H1 : Prop :=
  ∀ B : Finset ℕ, B ⊆ Icc 1 148 → 148 ∈ B → (hc : B.card = 6) →
    (∀ U ∈ B.powerset, ∀ hu : U.Nonempty,
      ([0,1,2,4,7,13,23,43,78,148] : List ℕ)[U.card+3]! ≤ U.max' hu) →
    2 ≤ (B.filter (96 ≤ ·)).card →
    (∀ S ∈ B.powerset, ∀ T ∈ B.powerset, S.sum id = T.sum id → S = T) →
    let P := B.powerset.image (fun S ↦ ((S.sum id : ℕ) : ℤ))
    let D := P - P
    let C := (Icc 1 (B.min' (card_pos.mp (by omega)) - 1)).filter fun (x : ℕ) ↦ (x : ℤ) ∉ D
    3 < C.card → ∀ R ∈ C.powersetCard 3,
    87381 ≤ (∑ x ∈ B, x^2) + ∑ x ∈ R, x^2 →
    (∀ W ∈ (B ∪ R).powerset, ∀ k ∈ range (W.card + 1),
      let V := (W.powersetCard k).image (fun s ↦ s.sum id)
      ∀ hv : V.Nonempty, W.card.choose k ≤ V.max' hv + 1 - V.min' hv) →
    148 ≤ ((B ∪ R).powerset.image (fun S ↦ S.sum id % 148)).card →
    (let V := (B ∪ R).powerset.image (fun S ↦ S.sum id)
     ∀ k ∈ ({158,207,224} : Finset ℕ), ∃ t ∈ V, (V.filter (· ≤ t)).card = k ∧
       k+(if k=224 then 143 else 148) ≤ (V.filter (· ≤ t+148)).card) →
    (∀ x ∈ R, ∀ y ∈ R, x < y → (y : ℤ) - x ∉ D ∧ (y : ℤ) + x ∉ D) →
    ∃ J ∈ R.powerset, ((J.sum id : ℕ) : ℤ) - ((R \ J).sum id : ℕ) ∈ D

/-- Residual graph triangles at maximum 149. -/
def H2 : Prop :=
  ∀ B : Finset ℕ, B ⊆ Icc 1 149 → 149 ∈ B → (hc : B.card = 6) →
    (∀ U ∈ B.powerset, ∀ hu : U.Nonempty,
      ([0,1,2,4,7,13,23,43,78,148] : List ℕ)[U.card+3]! ≤ U.max' hu) →
    2 ≤ (B.filter (96 ≤ ·)).card →
    (∀ S ∈ B.powerset, ∀ T ∈ B.powerset, S.sum id = T.sum id → S = T) →
    let P := B.powerset.image (fun S ↦ ((S.sum id : ℕ) : ℤ))
    let D := P - P
    let C := (Icc 1 (B.min' (card_pos.mp (by omega)) - 1)).filter fun (x : ℕ) ↦ (x : ℤ) ∉ D
    3 < C.card → ∀ R ∈ C.powersetCard 3,
    87381 ≤ (∑ x ∈ B, x^2) + ∑ x ∈ R, x^2 →
    (∀ W ∈ (B ∪ R).powerset, ∀ k ∈ range (W.card + 1),
      let V := (W.powersetCard k).image (fun s ↦ s.sum id)
      ∀ hv : V.Nonempty, W.card.choose k ≤ V.max' hv + 1 - V.min' hv) →
    148 ≤ ((B ∪ R).powerset.image (fun S ↦ S.sum id % 149)).card →
    (let V := (B ∪ R).powerset.image (fun S ↦ S.sum id)
     ∀ k ∈ ({158,207,224} : Finset ℕ), ∃ t ∈ V, (V.filter (· ≤ t)).card = k ∧
       k+(if k=224 then 143 else 148) ≤ (V.filter (· ≤ t+149)).card) →
    (∀ x ∈ R, ∀ y ∈ R, x < y → (y : ℤ) - x ∉ D ∧ (y : ℤ) + x ∉ D) →
    ∃ J ∈ R.powerset, ((J.sum id : ℕ) : ℤ) - ((R \ J).sum id : ℕ) ∈ D

/-- Residual graph triangles at maximum 150. -/
def H3 : Prop :=
  ∀ B : Finset ℕ, B ⊆ Icc 1 150 → 150 ∈ B → (hc : B.card = 6) →
    (∀ U ∈ B.powerset, ∀ hu : U.Nonempty,
      ([0,1,2,4,7,13,23,43,78,148] : List ℕ)[U.card+3]! ≤ U.max' hu) →
    2 ≤ (B.filter (96 ≤ ·)).card →
    (∀ S ∈ B.powerset, ∀ T ∈ B.powerset, S.sum id = T.sum id → S = T) →
    let P := B.powerset.image (fun S ↦ ((S.sum id : ℕ) : ℤ))
    let D := P - P
    let C := (Icc 1 (B.min' (card_pos.mp (by omega)) - 1)).filter fun (x : ℕ) ↦ (x : ℤ) ∉ D
    3 < C.card → ∀ R ∈ C.powersetCard 3,
    87381 ≤ (∑ x ∈ B, x^2) + ∑ x ∈ R, x^2 →
    (∀ W ∈ (B ∪ R).powerset, ∀ k ∈ range (W.card + 1),
      let V := (W.powersetCard k).image (fun s ↦ s.sum id)
      ∀ hv : V.Nonempty, W.card.choose k ≤ V.max' hv + 1 - V.min' hv) →
    148 ≤ ((B ∪ R).powerset.image (fun S ↦ S.sum id % 150)).card →
    (let V := (B ∪ R).powerset.image (fun S ↦ S.sum id)
     ∀ k ∈ ({158,207,224} : Finset ℕ), ∃ t ∈ V, (V.filter (· ≤ t)).card = k ∧
       k+(if k=224 then 143 else 148) ≤ (V.filter (· ≤ t+150)).card) →
    (∀ x ∈ R, ∀ y ∈ R, x < y → (y : ℤ) - x ∉ D ∧ (y : ℤ) + x ∉ D) →
    ∃ J ∈ R.powerset, ((J.sum id : ℕ) : ℤ) - ((R \ J).sum id : ℕ) ∈ D

/-- Residual graph triangles at maximum 151. -/
def H4 : Prop :=
  ∀ B : Finset ℕ, B ⊆ Icc 1 151 → 151 ∈ B → (hc : B.card = 6) →
    (∀ U ∈ B.powerset, ∀ hu : U.Nonempty,
      ([0,1,2,4,7,13,23,43,78,148] : List ℕ)[U.card+3]! ≤ U.max' hu) →
    2 ≤ (B.filter (96 ≤ ·)).card →
    (∀ S ∈ B.powerset, ∀ T ∈ B.powerset, S.sum id = T.sum id → S = T) →
    let P := B.powerset.image (fun S ↦ ((S.sum id : ℕ) : ℤ))
    let D := P - P
    let C := (Icc 1 (B.min' (card_pos.mp (by omega)) - 1)).filter fun (x : ℕ) ↦ (x : ℤ) ∉ D
    3 < C.card → ∀ R ∈ C.powersetCard 3,
    87381 ≤ (∑ x ∈ B, x^2) + ∑ x ∈ R, x^2 →
    (∀ W ∈ (B ∪ R).powerset, ∀ k ∈ range (W.card + 1),
      let V := (W.powersetCard k).image (fun s ↦ s.sum id)
      ∀ hv : V.Nonempty, W.card.choose k ≤ V.max' hv + 1 - V.min' hv) →
    148 ≤ ((B ∪ R).powerset.image (fun S ↦ S.sum id % 151)).card →
    (let V := (B ∪ R).powerset.image (fun S ↦ S.sum id)
     ∀ k ∈ ({158,207,224} : Finset ℕ), ∃ t ∈ V, (V.filter (· ≤ t)).card = k ∧
       k+(if k=224 then 143 else 148) ≤ (V.filter (· ≤ t+151)).card) →
    (∀ x ∈ R, ∀ y ∈ R, x < y → (y : ℤ) - x ∉ D ∧ (y : ℤ) + x ∉ D) →
    ∃ J ∈ R.powerset, ((J.sum id : ℕ) : ℤ) - ((R \ J).sum id : ℕ) ∈ D

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos1_erdos_1_variants_least_N_9_R2.H1 := by
  intro case148 case149 case150 case151 A hbound _ hc hsq _
  by_contra! hnoc
  have hiq : ∀ S ⊆ A, ∀ T ⊆ A, S.sum id = T.sum id → S = T := by
    intro S hs T ht he
    by_contra hne
    exact hnoc S hs T ht hne he
  obtain ⟨x,A₁,h₁,hc₁,hx₁,hlt₁⟩ := extract_min (k := 8) hc
  obtain ⟨y,A₂,h₂,hc₂,hy₂,hlt₂⟩ := extract_min (k := 7) hc₁
  obtain ⟨z,B,h₃,hcB,hzB,hlt₃⟩ := extract_min (k := 6) hc₂
  have hy₁ : y ∈ A₁ := h₂ ▸ mem_insert_self _ _
  have hz₂ : z ∈ A₂ := h₃ ▸ mem_insert_self _ _
  have hxy := hlt₁ _ hy₁
  have hyz := hlt₂ _ hz₂
  let R : Finset ℕ := {x,y,z}
  have hRAeq : B ∪ R = A := by
    rw [← h₁, ← h₂, ← h₃]
    ext b
    simp [R]
  have hBA : B ⊆ A := hRAeq ▸ subset_union_left
  have hRA : R ⊆ A := hRAeq ▸ subset_union_right
  have hrc : R.card = 3 := by simp [R, hxy.ne, hyz.ne, (hxy.trans hyz).ne]
  have hsmall (r) (hr : r ∈ R) (b) (hb : b ∈ B) : r < b := by
    have h := hlt₃ b hb
    simp only [R, mem_insert, mem_singleton] at hr
    omega
  have hdis : Disjoint R B := disjoint_left.mpr fun r hr hb ↦ (hsmall _ hr _ hb).false
  have hBb := hBA.trans hbound
  have hprior (U : Finset ℕ) (hUB : U ∈ B.powerset) (hu : U.Nonempty) :
      ([0,1,2,4,7,13,23,43,78,148] : List ℕ)[U.card+3]! ≤ U.max' hu := by
    have hs := mem_powerset.mp hUB
    have hUR : Disjoint U R := hdis.symm.mono_left hs
    have hcard : (U ∪ R).card = U.card + 3 := by rw [card_union_of_disjoint hUR,hrc]
    have hKA : U ∪ R ⊆ A := union_subset (hs.trans hBA) hRA
    have hdist : Erdos1.IsSumDistinctSet (U ∪ R) (U.max' hu) := by
      constructor
      · intro a h
        refine mem_Icc.mpr ⟨(mem_Icc.mp (hbound (hKA h))).1, ?_⟩
        rcases mem_union.mp h with hU | hR
        · exact U.le_max' _ hU
        · exact (hsmall _ hR _ (hs (U.max'_mem hu))).le
      · intro S T he
        apply Subtype.ext
        exact hiq _ ((mem_powerset.mp S.property).trans hKA) _
          ((mem_powerset.mp T.property).trans hKA) he
    have hcU := card_le_card hs
    exact CubeWindow.lower _ _ _ (by omega) hcard hdist
  have htwo : 2 ≤ (B.filter (96 ≤ ·)).card := by
    by_cases h : ∃ r ∈ R, 96 ≤ r
    · obtain ⟨r,hr,hl⟩ := h
      have hf : B.filter (96 ≤ ·) = B := filter_true_of_mem fun b hb ↦ hl.trans (hsmall r hr b hb).le
      rw [hf,hcB]; decide
    · let e := A.orderIsoOfFin hc
      have h7 : 96 ≤ (e 7).val :=
        second_largest_ge_96 hiq (fun a ha ↦ (mem_Icc.mp (hbound ha)).2.trans (by decide)) hc hsq
      have h78 : (e 7).val < (e 8).val := e.strictMono (by decide : (7 : Fin 9) < 8)
      have hBof (a : ℕ) (ha : a ∈ A) (hl : 96 ≤ a) : a ∈ B := by
        rw [← hRAeq] at ha
        rcases mem_union.mp ha with hb | hr
        · exact hb
        · exact (h ⟨a,hr,hl⟩).elim
      exact one_lt_card.mpr ⟨_, mem_filter.mpr ⟨hBof _ (e 7).property h7,h7⟩,
        _, mem_filter.mpr ⟨hBof _ (e 8).property (h7.trans h78.le), h7.trans h78.le⟩, h78.ne⟩
  have hBi : ∀ S ∈ B.powerset, ∀ T ∈ B.powerset, S.sum id = T.sum id → S = T :=
    fun S hS T hT ↦ hiq S ((mem_powerset.mp hS).trans hBA) T ((mem_powerset.mp hT).trans hBA)
  let P := B.powerset.image (fun S ↦ ((S.sum id : ℕ) : ℤ))
  let D := P - P
  have hn : B.Nonempty := card_pos.mp (by omega)
  let C := (Icc 1 (B.min' hn - 1)).filter fun (t : ℕ) ↦ (t : ℤ) ∉ D
  have allok {U V : Finset ℕ} (u : U ⊆ R) (v : V ⊆ R) (n : U ≠ V) :
      ((U.sum id : ℕ) : ℤ) - (V.sum id : ℕ) ∉ D := no_difference hiq hBA hRA hdis u v n
  have hRC : R ⊆ C := by
    intro r hr
    have hmin := hsmall _ hr _ (B.min'_mem hn)
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp (hbound (hRA hr))).1, by omega⟩, ?_⟩
    simpa using allok (singleton_subset_iff.mpr hr) (empty_subset R) (by simp)
  have hq : 87381 ≤ (∑ t ∈ B, t^2) + ∑ t ∈ R, t^2 := by
    rw [← sum_union hdis.symm, hRAeq]; exact hsq
  have hrank (W) (hw : W ∈ (B ∪ R).powerset) (k : ℕ) (_ : k ∈ range (W.card+1)) :=
    ranks_fit hiq W (hRAeq ▸ mem_powerset.mp hw) k
  have edges (u) (hu : u ∈ R) (v) (hv : v ∈ R) (hlt : u < v) :
      (v : ℤ) - u ∉ D ∧ (v : ℤ) + u ∉ D := by
    constructor
    · simpa using allok (singleton_subset_iff.mpr hv) (singleton_subset_iff.mpr hu)
        (by simpa using hlt.ne.symm)
    · have hsub : ({v,u} : Finset ℕ) ⊆ R := insert_subset hv (singleton_subset_iff.mpr hu)
      simpa [hlt.ne.symm] using allok hsub (empty_subset R) (by simp)
  have result : ∃ J ∈ R.powerset, ((J.sum id : ℕ) : ℤ) - ((R \ J).sum id : ℕ) ∈ D := by
    rcases eq_or_lt_of_le (card_le_card hRC) with he | he
    · have heq : R = C := eq_of_subset_of_card_le hRC he.ge
      have h0 : (0 : ℤ) ∈ P := mem_image.mpr ⟨∅, by simp, by simp⟩
      have hD : (0 : ℤ) ∈ D := mem_sub.mpr ⟨0,h0,0,h0,by simp⟩
      apply forced_triangle R D hD hrc (fun a ha ↦ (mem_Icc.mp (hbound (hRA ha))).1)
      intro a ha b hb hlt
      rw [heq]
      have hhi := (mem_Icc.mp (mem_filter.mp (hRC hb)).1).2
      apply mem_filter.mpr
      refine ⟨mem_Icc.mpr ⟨by omega,by omega⟩, ?_⟩
      rw [Nat.cast_sub hlt.le]
      exact (edges a ha b hb hlt).1
    · let M := B.max' hn
      have hm : M ∈ B := B.max'_mem hn
      have hboundM : B ⊆ Icc 1 M := fun b hb ↦ mem_Icc.mpr
        ⟨(mem_Icc.mp (hBb hb)).1,B.le_max' _ hb⟩
      have hlo : 148 ≤ M := by
        have h := hprior B (mem_powerset.mpr Subset.rfl) hn
        simpa [hcB] using h
      have hhi : M ≤ 151 := (mem_Icc.mp (hBb hm)).2
      have hd : Erdos1.IsSumDistinctSet A M := by
        constructor
        · intro a ha
          refine mem_Icc.mpr ⟨(mem_Icc.mp (hbound ha)).1,?_⟩
          rw [← hRAeq] at ha
          rcases mem_union.mp ha with h | h
          · exact B.le_max' _ h
          · exact (hsmall _ h _ hm).le
        · intro S T heq
          exact Subtype.ext (hiq _ (mem_powerset.mp S.property) _ (mem_powerset.mp T.property) heq)
      have hgrowth (k : ℕ) (hk : k = 158 ∨ k = 207 ∨ k = 224) :=
        CubeWindow.count_growth 9 k (if k=224 then 143 else 148) (by omega) (by norm_num; omega) M A hc hd
          (fun g mono sz step ↦ (CubeWindow.all_growth g M mono sz step k hk).2.2.2.2.2.2.2.2)
      have hres : 148 ≤ ((B ∪ R).powerset.image (fun S ↦ S.sum id % M)).card := by
        rw [hRAeq]; exact (hgrowth 158 (Or.inl rfl)).2.1
      let V := (B ∪ R).powerset.image (fun S ↦ S.sum id)
      have hwin (k : ℕ) (hk : k ∈ ({158,207,224} : Finset ℕ)) :
          ∃ t ∈ V, (V.filter (· ≤ t)).card = k ∧ k+(if k=224 then 143 else 148) ≤ (V.filter (· ≤ t+M)).card := by
        simpa only [V,hRAeq] using (hgrowth k (by simpa using hk)).2.2
      have hbig : 3 < C.card := by omega
      have htr : R ∈ C.powersetCard 3 := mem_powersetCard.mpr ⟨hRC,hrc⟩
      clear_value M
      interval_cases M
      · exact case148 B hboundM hm hcB hprior htwo hBi hbig R htr hq hrank hres hwin edges
      · exact case149 B hboundM hm hcB hprior htwo hBi hbig R htr hq hrank hres hwin edges
      · exact case150 B hboundM hm hcB hprior htwo hBi hbig R htr hq hrank hres hwin edges
      · exact case151 B hboundM hm hcB hprior htwo hBi hbig R htr hq hrank hres hwin edges
  obtain ⟨J,hJ,hbad⟩ := result
  have hne : J ≠ R \ J := by
    intro hh
    have hdisj : Disjoint J (R \ J) := disjoint_sdiff
    rw [← hh] at hdisj
    have hzero : J = ∅ := disjoint_self.mp hdisj
    simp [hzero] at hh
    simp [← hh] at hrc
  exact allok (mem_powerset.mp hJ) sdiff_subset hne hbad

end OMA.R_Erdos1_erdos_1_variants_least_N_9_R2_H1_R1
