import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1697

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def pf (x : Fin 9 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

lemma getD_snoc_lt (l : List Bool) (x : Bool) (i : ℕ) (hi : i < l.length) :
    (l ++ [x]).getD i false = l.getD i false := by
  simp [List.getD, List.getElem?_append_left hi]

lemma getD_snoc_eq (l : List Bool) (x : Bool) (i : ℕ) (hi : i = l.length) :
    (l ++ [x]).getD i false = x := by
  subst hi
  simp [List.getD]

lemma stepW_length (w : List Bool) (g : Gate) : (stepW w g).length = w.length + 1 := by
  simp [stepW]

lemma fold_getD_lt (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [List.foldl_cons, ih (stepW w g) i (by rw [stepW_length]; omega)]
    exact getD_snoc_lt w _ i hi

lemma ofFn_getD_lt_gen {n : ℕ} (y : Fin n → Bool) (i : ℕ) (h : i < n) :
    (List.ofFn y).getD i false = y ⟨i, h⟩ := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h]

lemma ofFn_getD_lt (y : Fin 9 → Bool) (i : ℕ) (h : i < 9) :
    (List.ofFn y).getD i false = y ⟨i, h⟩ :=
  ofFn_getD_lt_gen y i h

lemma ofFn_getD_ge (y : Fin 9 → Bool) (i : ℕ) (h : 9 ≤ i) :
    (List.ofFn y).getD i false = false :=
  List.getD_eq_default _ _ (by rw [List.length_ofFn]; exact h)

def valIn (y : Fin 9 → Bool) (i : ℕ) : Bool := (List.ofFn y).getD i false

lemma valIn_lt (y : Fin 9 → Bool) (i : ℕ) (h : i < 9) : valIn y i = y ⟨i, h⟩ :=
  ofFn_getD_lt y i h

lemma valIn_ge (y : Fin 9 → Bool) (i : ℕ) (h : 9 ≤ i) : valIn y i = false :=
  ofFn_getD_ge y i h

def w9 (C : Circuit) (y : Fin 9 → Bool) : Bool := (C.wires (List.ofFn y)).getD 9 false

lemma w9_first (C : Circuit) (g0 : Gate) (rest : List Gate) (hg : C.gates = g0 :: rest)
    (y : Fin 9 → Bool) : w9 C y = g0.op.eval (g0.inputs.map (valIn y)) := by
  have h1 : (rest.foldl stepW (stepW (List.ofFn y) g0)).getD 9 false
      = (stepW (List.ofFn y) g0).getD 9 false :=
    fold_getD_lt rest (stepW (List.ofFn y) g0) 9 (by rw [stepW_length, List.length_ofFn]; omega)
  have h2 : (stepW (List.ofFn y) g0).getD 9 false = g0.op.eval (g0.inputs.map (valIn y)) :=
    getD_snoc_eq (List.ofFn y) (g0.op.eval (g0.inputs.map (valIn y))) 9
      (by rw [List.length_ofFn])
  have h3 : w9 C y = (rest.foldl stepW (stepW (List.ofFn y) g0)).getD 9 false := by
    show (C.wires (List.ofFn y)).getD 9 false = _
    rw [wires_eq, hg, List.foldl_cons]
  exact h3.trans (h1.trans h2)

lemma wires_input (C : Circuit) (y : Fin 9 → Bool) (i : ℕ) (h : i < 9) :
    (C.wires (List.ofFn y)).getD i false = y ⟨i, h⟩ := by
  rw [wires_eq, fold_getD_lt C.gates (List.ofFn y) i (by rw [List.length_ofFn]; exact h)]
  exact ofFn_getD_lt y i h

lemma gateShape (op : GateOp) (ins : List ℕ) (w : (Fin 9 → Bool) → Bool)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) (hlen : ins.length ≤ 2)
    (hw : ∀ y, w y = op.eval (ins.map (valIn y)))
    (hnc : ∃ x y : Fin 9 → Bool, w x ≠ w y)
    (hne : ∀ i : Fin 9, ∃ x : Fin 9 → Bool, x i ≠ w x) :
    (∃ a : Fin 9, ∀ y, w y = !(y a)) ∨
    (∃ a b : Fin 9, a ≠ b ∧ ∀ y, w y = (y a && y b)) ∨
    (∃ a b : Fin 9, a ≠ b ∧ ∀ y, w y = (y a || y b)) := by
  have hconst : ∀ c : Bool, (∀ y, w y = c) → False := by
    intro c h
    obtain ⟨x, y, hxy⟩ := hnc
    exact hxy ((h x).trans (h y).symm)
  have hproj : ∀ (i : ℕ), i < 9 → (∀ y, w y = valIn y i) → False := by
    intro i hi h
    obtain ⟨x, hx⟩ := hne ⟨i, hi⟩
    exact hx ((valIn_lt x i hi).symm.trans (h x).symm)
  have hone : ∀ (i : ℕ), (∀ y, w y = valIn y i) → False := by
    intro i h
    by_cases hi : i < 9
    · exact hproj i hi h
    · exact hconst false (fun y => (h y).trans (valIn_ge y i (by omega)))
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · exact (hconst true (fun y => (hw y).trans (by simp [GateOp.eval]))).elim
    · exact (hone a (fun y => (hw y).trans (by simp [GateOp.eval]))).elim
    · have h : ∀ y, w y = (valIn y a && valIn y b) :=
        fun y => (hw y).trans (by simp [GateOp.eval])
      by_cases ha : a < 9
      · by_cases hb : b < 9
        · by_cases hab : a = b
          · exact (hproj a ha (fun y => by rw [h y, ← hab, Bool.and_self])).elim
          · right; left
            refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_, ?_⟩
            · intro hh
              exact hab (congrArg Fin.val hh)
            · intro y
              rw [h y, valIn_lt y a ha, valIn_lt y b hb]
        · exact (hconst false (fun y => by
            rw [h y, valIn_ge y b (by omega), Bool.and_false])).elim
      · exact (hconst false (fun y => by
          rw [h y, valIn_ge y a (by omega), Bool.false_and])).elim
    · exact absurd hlen (by simp only [List.length_cons]; omega)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · exact (hconst false (fun y => (hw y).trans (by simp [GateOp.eval]))).elim
    · exact (hone a (fun y => (hw y).trans (by simp [GateOp.eval]))).elim
    · have h : ∀ y, w y = (valIn y a || valIn y b) :=
        fun y => (hw y).trans (by simp [GateOp.eval])
      by_cases ha : a < 9
      · by_cases hb : b < 9
        · by_cases hab : a = b
          · exact (hproj a ha (fun y => by rw [h y, ← hab, Bool.or_self])).elim
          · right; right
            refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_, ?_⟩
            · intro hh
              exact hab (congrArg Fin.val hh)
            · intro y
              rw [h y, valIn_lt y a ha, valIn_lt y b hb]
        · exact (hproj a ha (fun y => by
            rw [h y, valIn_ge y b (by omega), Bool.or_false])).elim
      · exact (hone b (fun y => by
          rw [h y, valIn_ge y a (by omega), Bool.false_or])).elim
    · exact absurd hlen (by simp only [List.length_cons]; omega)
  · rcases ins with _ | ⟨a, rest⟩
    · exact (hconst true (fun y => (hw y).trans (by simp [GateOp.eval]))).elim
    · have h : ∀ y, w y = !(valIn y a) :=
        fun y => (hw y).trans (by simp [GateOp.eval])
      by_cases ha : a < 9
      · left
        exact ⟨⟨a, ha⟩, fun y => by rw [h y, valIn_lt y a ha]⟩
      · exact (hconst true (fun y => by simp [h y, valIn_ge y a (by omega)])).elim

def rhoF (σ : Fin 9 → Fin 9) (i : ℕ) : ℕ := if h : i < 9 then (σ ⟨i, h⟩).val else i

lemma rhoF_lt (σ : Fin 9 → Fin 9) (i : ℕ) (h : i < 9) : rhoF σ i = (σ ⟨i, h⟩).val := by
  unfold rhoF
  rw [dif_pos h]

lemma rhoF_ge (σ : Fin 9 → Fin 9) (i : ℕ) (h : 9 ≤ i) : rhoF σ i = i := by
  unfold rhoF
  rw [dif_neg (by omega)]

lemma rhoF_bound (σ : Fin 9 → Fin 9) (i n : ℕ) (hn : 9 ≤ n) (h : i < n) : rhoF σ i < n := by
  by_cases hi : i < 9
  · rw [rhoF_lt σ i hi]
    have := (σ ⟨i, hi⟩).isLt
    omega
  · rw [rhoF_ge σ i (by omega)]
    exact h

def rgF (σ : Fin 9 → Fin 9) (g : Gate) : Gate := ⟨g.op, g.inputs.map (rhoF σ)⟩

def relabC (σ : Fin 9 → Fin 9) (C : Circuit) : Circuit :=
  ⟨C.gates.map (rgF σ), rhoF σ C.output⟩

lemma rgF_val (σ : Fin 9 → Fin 9) (g : Gate) (w w' : List Bool)
    (h : ∀ i, w'.getD (rhoF σ i) false = w.getD i false) :
    (rgF σ g).op.eval ((rgF σ g).inputs.map fun i => w'.getD i false)
      = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  show g.op.eval ((g.inputs.map (rhoF σ)).map fun i => w'.getD i false)
      = g.op.eval (g.inputs.map fun i => w.getD i false)
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact h i

lemma relab_fold (σ : Fin 9 → Fin 9) (gs : List Gate) : ∀ (w w' : List Bool),
    w'.length = w.length → 9 ≤ w.length →
    (∀ i, w'.getD (rhoF σ i) false = w.getD i false) →
    ∀ i, ((gs.map (rgF σ)).foldl stepW w').getD (rhoF σ i) false
      = (gs.foldl stepW w).getD i false := by
  induction gs with
  | nil =>
    intro w w' _ _ h i
    exact h i
  | cons g gs ih =>
    intro w w' hl h9 h
    simp only [List.map_cons, List.foldl_cons]
    refine ih (stepW w g) (stepW w' (rgF σ g)) ?_ ?_ ?_
    · rw [stepW_length, stepW_length, hl]
    · rw [stepW_length]
      omega
    · intro i
      have hv := rgF_val σ g w w' h
      unfold stepW
      rw [hv]
      rcases lt_trichotomy i w.length with hi | hi | hi
      · rw [getD_snoc_lt w' _ (rhoF σ i) (by rw [hl]; exact rhoF_bound σ i w.length h9 hi),
          getD_snoc_lt w _ i hi]
        exact h i
      · rw [rhoF_ge σ i (by omega), getD_snoc_eq w' _ i (by omega), getD_snoc_eq w _ i hi]
      · rw [rhoF_ge σ i (by omega),
          List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton]; omega),
          List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton]; omega)]

lemma relab_base (σ : Fin 9 → Fin 9) (y : Fin 9 → Bool) (i : ℕ) :
    (List.ofFn y).getD (rhoF σ i) false = (List.ofFn (y ∘ σ)).getD i false := by
  by_cases hi : i < 9
  · have e1 := ofFn_getD_lt y (σ ⟨i, hi⟩).val (σ ⟨i, hi⟩).isLt
    have e2 := ofFn_getD_lt (y ∘ σ) i hi
    rw [rhoF_lt σ i hi]
    exact e1.trans e2.symm
  · rw [rhoF_ge σ i (by omega), ofFn_getD_ge y i (by omega), ofFn_getD_ge (y ∘ σ) i (by omega)]

lemma relab_wires (σ : Fin 9 → Fin 9) (C : Circuit) (y : Fin 9 → Bool) (i : ℕ) :
    ((relabC σ C).wires (List.ofFn y)).getD (rhoF σ i) false
      = (C.wires (List.ofFn (y ∘ σ))).getD i false :=
  relab_fold σ C.gates (List.ofFn (y ∘ σ)) (List.ofFn y) (by simp) (by simp)
    (relab_base σ y) i

lemma relab_w9 (σ : Fin 9 → Fin 9) (C : Circuit) (y : Fin 9 → Bool) :
    w9 (relabC σ C) y = w9 C (y ∘ σ) := by
  have h := relab_wires σ C y 9
  rw [rhoF_ge σ 9 (le_refl 9)] at h
  exact h

lemma relab_fan (σ : Fin 9 → Fin 9) (C : Circuit) (h : FanInTwo C) :
    FanInTwo (relabC σ C) := by
  intro g hg
  have hg' : g ∈ C.gates.map (rgF σ) := hg
  rw [List.mem_map] at hg'
  obtain ⟨g0, hg0, rfl⟩ := hg'
  have h0 := h g0 hg0
  refine ⟨h0.1, ?_⟩
  show (g0.inputs.map (rhoF σ)).length ≤ 2
  rw [List.length_map]
  exact h0.2

lemma relab_size (σ : Fin 9 → Fin 9) (C : Circuit) : (relabC σ C).size = C.size := by
  simp [relabC, Circuit.size]

def tabF (l : List ℕ) (i : Fin 9) : Fin 9 := ⟨l.getD i.val 0 % 9, Nat.mod_lt _ (by norm_num)⟩

def autos : List (Fin 9 → Fin 9) := [tabF [0, 1, 2, 3, 4, 5, 6, 7, 8], tabF [0, 5, 8, 3, 4, 1, 7, 6, 2], tabF [1, 0, 5, 8, 6, 2, 4, 7, 3], tabF [1, 2, 3, 8, 6, 0, 7, 4, 5], tabF [2, 1, 0, 5, 7, 3, 6, 4, 8], tabF [2, 3, 8, 5, 7, 1, 4, 6, 0], tabF [3, 2, 1, 0, 4, 8, 7, 6, 5], tabF [3, 8, 5, 0, 4, 2, 6, 7, 1], tabF [5, 0, 1, 2, 7, 8, 4, 6, 3], tabF [5, 8, 3, 2, 7, 0, 6, 4, 1], tabF [8, 3, 2, 1, 6, 5, 4, 7, 0], tabF [8, 5, 0, 1, 6, 3, 7, 4, 2]]

abbrev pairOK (c d : Fin 9) : Prop := (c = 0 ∧ d = 1) ∨ (c = 0 ∧ d = 2) ∨ (c = 0 ∧ d = 3) ∨ (c = 0 ∧ d = 4) ∨ (c = 0 ∧ d = 6) ∨ (c = 4 ∧ d = 6)

lemma invb_0 : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 : Bool,
    ((a0 && a1) || (a1 && a2) || (a2 && a3) || (a3 && a4) || (a4 && a0) || (a0 && a5) || (a1 && a6) || (a2 && a7) || (a3 && a8) || (a5 && a7) || (a6 && a8) || (a8 && a5)) = ((a0 && a1) || (a1 && a2) || (a2 && a3) || (a3 && a4) || (a4 && a0) || (a0 && a5) || (a1 && a6) || (a2 && a7) || (a3 && a8) || (a5 && a7) || (a6 && a8) || (a8 && a5)) := by
  decide +kernel

lemma inv_0 (y : Fin 9 → Bool) : pf (y ∘ tabF [0, 1, 2, 3, 4, 5, 6, 7, 8]) = pf y := by
  have t0 : tabF [0, 1, 2, 3, 4, 5, 6, 7, 8] 0 = 0 := by decide +kernel
  have t1 : tabF [0, 1, 2, 3, 4, 5, 6, 7, 8] 1 = 1 := by decide +kernel
  have t2 : tabF [0, 1, 2, 3, 4, 5, 6, 7, 8] 2 = 2 := by decide +kernel
  have t3 : tabF [0, 1, 2, 3, 4, 5, 6, 7, 8] 3 = 3 := by decide +kernel
  have t4 : tabF [0, 1, 2, 3, 4, 5, 6, 7, 8] 4 = 4 := by decide +kernel
  have t5 : tabF [0, 1, 2, 3, 4, 5, 6, 7, 8] 5 = 5 := by decide +kernel
  have t6 : tabF [0, 1, 2, 3, 4, 5, 6, 7, 8] 6 = 6 := by decide +kernel
  have t7 : tabF [0, 1, 2, 3, 4, 5, 6, 7, 8] 7 = 7 := by decide +kernel
  have t8 : tabF [0, 1, 2, 3, 4, 5, 6, 7, 8] 8 = 8 := by decide +kernel
  have g : pf (y ∘ tabF [0, 1, 2, 3, 4, 5, 6, 7, 8]) = (((y 0) && (y 1)) || ((y 1) && (y 2)) || ((y 2) && (y 3)) || ((y 3) && (y 4)) || ((y 4) && (y 0)) || ((y 0) && (y 5)) || ((y 1) && (y 6)) || ((y 2) && (y 7)) || ((y 3) && (y 8)) || ((y 5) && (y 7)) || ((y 6) && (y 8)) || ((y 8) && (y 5))) := by
    simp only [pf, Function.comp_apply, t0, t1, t2, t3, t4, t5, t6, t7, t8]
  exact g.trans (invb_0 (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8))

lemma invb_1 : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 : Bool,
    ((a0 && a5) || (a5 && a8) || (a8 && a3) || (a3 && a4) || (a4 && a0) || (a0 && a1) || (a5 && a7) || (a8 && a6) || (a3 && a2) || (a1 && a6) || (a7 && a2) || (a2 && a1)) = ((a0 && a1) || (a1 && a2) || (a2 && a3) || (a3 && a4) || (a4 && a0) || (a0 && a5) || (a1 && a6) || (a2 && a7) || (a3 && a8) || (a5 && a7) || (a6 && a8) || (a8 && a5)) := by
  decide +kernel

lemma inv_1 (y : Fin 9 → Bool) : pf (y ∘ tabF [0, 5, 8, 3, 4, 1, 7, 6, 2]) = pf y := by
  have t0 : tabF [0, 5, 8, 3, 4, 1, 7, 6, 2] 0 = 0 := by decide +kernel
  have t1 : tabF [0, 5, 8, 3, 4, 1, 7, 6, 2] 1 = 5 := by decide +kernel
  have t2 : tabF [0, 5, 8, 3, 4, 1, 7, 6, 2] 2 = 8 := by decide +kernel
  have t3 : tabF [0, 5, 8, 3, 4, 1, 7, 6, 2] 3 = 3 := by decide +kernel
  have t4 : tabF [0, 5, 8, 3, 4, 1, 7, 6, 2] 4 = 4 := by decide +kernel
  have t5 : tabF [0, 5, 8, 3, 4, 1, 7, 6, 2] 5 = 1 := by decide +kernel
  have t6 : tabF [0, 5, 8, 3, 4, 1, 7, 6, 2] 6 = 7 := by decide +kernel
  have t7 : tabF [0, 5, 8, 3, 4, 1, 7, 6, 2] 7 = 6 := by decide +kernel
  have t8 : tabF [0, 5, 8, 3, 4, 1, 7, 6, 2] 8 = 2 := by decide +kernel
  have g : pf (y ∘ tabF [0, 5, 8, 3, 4, 1, 7, 6, 2]) = (((y 0) && (y 5)) || ((y 5) && (y 8)) || ((y 8) && (y 3)) || ((y 3) && (y 4)) || ((y 4) && (y 0)) || ((y 0) && (y 1)) || ((y 5) && (y 7)) || ((y 8) && (y 6)) || ((y 3) && (y 2)) || ((y 1) && (y 6)) || ((y 7) && (y 2)) || ((y 2) && (y 1))) := by
    simp only [pf, Function.comp_apply, t0, t1, t2, t3, t4, t5, t6, t7, t8]
  exact g.trans (invb_1 (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8))

lemma invb_2 : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 : Bool,
    ((a1 && a0) || (a0 && a5) || (a5 && a8) || (a8 && a6) || (a6 && a1) || (a1 && a2) || (a0 && a4) || (a5 && a7) || (a8 && a3) || (a2 && a7) || (a4 && a3) || (a3 && a2)) = ((a0 && a1) || (a1 && a2) || (a2 && a3) || (a3 && a4) || (a4 && a0) || (a0 && a5) || (a1 && a6) || (a2 && a7) || (a3 && a8) || (a5 && a7) || (a6 && a8) || (a8 && a5)) := by
  decide +kernel

lemma inv_2 (y : Fin 9 → Bool) : pf (y ∘ tabF [1, 0, 5, 8, 6, 2, 4, 7, 3]) = pf y := by
  have t0 : tabF [1, 0, 5, 8, 6, 2, 4, 7, 3] 0 = 1 := by decide +kernel
  have t1 : tabF [1, 0, 5, 8, 6, 2, 4, 7, 3] 1 = 0 := by decide +kernel
  have t2 : tabF [1, 0, 5, 8, 6, 2, 4, 7, 3] 2 = 5 := by decide +kernel
  have t3 : tabF [1, 0, 5, 8, 6, 2, 4, 7, 3] 3 = 8 := by decide +kernel
  have t4 : tabF [1, 0, 5, 8, 6, 2, 4, 7, 3] 4 = 6 := by decide +kernel
  have t5 : tabF [1, 0, 5, 8, 6, 2, 4, 7, 3] 5 = 2 := by decide +kernel
  have t6 : tabF [1, 0, 5, 8, 6, 2, 4, 7, 3] 6 = 4 := by decide +kernel
  have t7 : tabF [1, 0, 5, 8, 6, 2, 4, 7, 3] 7 = 7 := by decide +kernel
  have t8 : tabF [1, 0, 5, 8, 6, 2, 4, 7, 3] 8 = 3 := by decide +kernel
  have g : pf (y ∘ tabF [1, 0, 5, 8, 6, 2, 4, 7, 3]) = (((y 1) && (y 0)) || ((y 0) && (y 5)) || ((y 5) && (y 8)) || ((y 8) && (y 6)) || ((y 6) && (y 1)) || ((y 1) && (y 2)) || ((y 0) && (y 4)) || ((y 5) && (y 7)) || ((y 8) && (y 3)) || ((y 2) && (y 7)) || ((y 4) && (y 3)) || ((y 3) && (y 2))) := by
    simp only [pf, Function.comp_apply, t0, t1, t2, t3, t4, t5, t6, t7, t8]
  exact g.trans (invb_2 (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8))

lemma invb_3 : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 : Bool,
    ((a1 && a2) || (a2 && a3) || (a3 && a8) || (a8 && a6) || (a6 && a1) || (a1 && a0) || (a2 && a7) || (a3 && a4) || (a8 && a5) || (a0 && a4) || (a7 && a5) || (a5 && a0)) = ((a0 && a1) || (a1 && a2) || (a2 && a3) || (a3 && a4) || (a4 && a0) || (a0 && a5) || (a1 && a6) || (a2 && a7) || (a3 && a8) || (a5 && a7) || (a6 && a8) || (a8 && a5)) := by
  decide +kernel

lemma inv_3 (y : Fin 9 → Bool) : pf (y ∘ tabF [1, 2, 3, 8, 6, 0, 7, 4, 5]) = pf y := by
  have t0 : tabF [1, 2, 3, 8, 6, 0, 7, 4, 5] 0 = 1 := by decide +kernel
  have t1 : tabF [1, 2, 3, 8, 6, 0, 7, 4, 5] 1 = 2 := by decide +kernel
  have t2 : tabF [1, 2, 3, 8, 6, 0, 7, 4, 5] 2 = 3 := by decide +kernel
  have t3 : tabF [1, 2, 3, 8, 6, 0, 7, 4, 5] 3 = 8 := by decide +kernel
  have t4 : tabF [1, 2, 3, 8, 6, 0, 7, 4, 5] 4 = 6 := by decide +kernel
  have t5 : tabF [1, 2, 3, 8, 6, 0, 7, 4, 5] 5 = 0 := by decide +kernel
  have t6 : tabF [1, 2, 3, 8, 6, 0, 7, 4, 5] 6 = 7 := by decide +kernel
  have t7 : tabF [1, 2, 3, 8, 6, 0, 7, 4, 5] 7 = 4 := by decide +kernel
  have t8 : tabF [1, 2, 3, 8, 6, 0, 7, 4, 5] 8 = 5 := by decide +kernel
  have g : pf (y ∘ tabF [1, 2, 3, 8, 6, 0, 7, 4, 5]) = (((y 1) && (y 2)) || ((y 2) && (y 3)) || ((y 3) && (y 8)) || ((y 8) && (y 6)) || ((y 6) && (y 1)) || ((y 1) && (y 0)) || ((y 2) && (y 7)) || ((y 3) && (y 4)) || ((y 8) && (y 5)) || ((y 0) && (y 4)) || ((y 7) && (y 5)) || ((y 5) && (y 0))) := by
    simp only [pf, Function.comp_apply, t0, t1, t2, t3, t4, t5, t6, t7, t8]
  exact g.trans (invb_3 (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8))

lemma invb_4 : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 : Bool,
    ((a2 && a1) || (a1 && a0) || (a0 && a5) || (a5 && a7) || (a7 && a2) || (a2 && a3) || (a1 && a6) || (a0 && a4) || (a5 && a8) || (a3 && a4) || (a6 && a8) || (a8 && a3)) = ((a0 && a1) || (a1 && a2) || (a2 && a3) || (a3 && a4) || (a4 && a0) || (a0 && a5) || (a1 && a6) || (a2 && a7) || (a3 && a8) || (a5 && a7) || (a6 && a8) || (a8 && a5)) := by
  decide +kernel

lemma inv_4 (y : Fin 9 → Bool) : pf (y ∘ tabF [2, 1, 0, 5, 7, 3, 6, 4, 8]) = pf y := by
  have t0 : tabF [2, 1, 0, 5, 7, 3, 6, 4, 8] 0 = 2 := by decide +kernel
  have t1 : tabF [2, 1, 0, 5, 7, 3, 6, 4, 8] 1 = 1 := by decide +kernel
  have t2 : tabF [2, 1, 0, 5, 7, 3, 6, 4, 8] 2 = 0 := by decide +kernel
  have t3 : tabF [2, 1, 0, 5, 7, 3, 6, 4, 8] 3 = 5 := by decide +kernel
  have t4 : tabF [2, 1, 0, 5, 7, 3, 6, 4, 8] 4 = 7 := by decide +kernel
  have t5 : tabF [2, 1, 0, 5, 7, 3, 6, 4, 8] 5 = 3 := by decide +kernel
  have t6 : tabF [2, 1, 0, 5, 7, 3, 6, 4, 8] 6 = 6 := by decide +kernel
  have t7 : tabF [2, 1, 0, 5, 7, 3, 6, 4, 8] 7 = 4 := by decide +kernel
  have t8 : tabF [2, 1, 0, 5, 7, 3, 6, 4, 8] 8 = 8 := by decide +kernel
  have g : pf (y ∘ tabF [2, 1, 0, 5, 7, 3, 6, 4, 8]) = (((y 2) && (y 1)) || ((y 1) && (y 0)) || ((y 0) && (y 5)) || ((y 5) && (y 7)) || ((y 7) && (y 2)) || ((y 2) && (y 3)) || ((y 1) && (y 6)) || ((y 0) && (y 4)) || ((y 5) && (y 8)) || ((y 3) && (y 4)) || ((y 6) && (y 8)) || ((y 8) && (y 3))) := by
    simp only [pf, Function.comp_apply, t0, t1, t2, t3, t4, t5, t6, t7, t8]
  exact g.trans (invb_4 (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8))

lemma invb_5 : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 : Bool,
    ((a2 && a3) || (a3 && a8) || (a8 && a5) || (a5 && a7) || (a7 && a2) || (a2 && a1) || (a3 && a4) || (a8 && a6) || (a5 && a0) || (a1 && a6) || (a4 && a0) || (a0 && a1)) = ((a0 && a1) || (a1 && a2) || (a2 && a3) || (a3 && a4) || (a4 && a0) || (a0 && a5) || (a1 && a6) || (a2 && a7) || (a3 && a8) || (a5 && a7) || (a6 && a8) || (a8 && a5)) := by
  decide +kernel

lemma inv_5 (y : Fin 9 → Bool) : pf (y ∘ tabF [2, 3, 8, 5, 7, 1, 4, 6, 0]) = pf y := by
  have t0 : tabF [2, 3, 8, 5, 7, 1, 4, 6, 0] 0 = 2 := by decide +kernel
  have t1 : tabF [2, 3, 8, 5, 7, 1, 4, 6, 0] 1 = 3 := by decide +kernel
  have t2 : tabF [2, 3, 8, 5, 7, 1, 4, 6, 0] 2 = 8 := by decide +kernel
  have t3 : tabF [2, 3, 8, 5, 7, 1, 4, 6, 0] 3 = 5 := by decide +kernel
  have t4 : tabF [2, 3, 8, 5, 7, 1, 4, 6, 0] 4 = 7 := by decide +kernel
  have t5 : tabF [2, 3, 8, 5, 7, 1, 4, 6, 0] 5 = 1 := by decide +kernel
  have t6 : tabF [2, 3, 8, 5, 7, 1, 4, 6, 0] 6 = 4 := by decide +kernel
  have t7 : tabF [2, 3, 8, 5, 7, 1, 4, 6, 0] 7 = 6 := by decide +kernel
  have t8 : tabF [2, 3, 8, 5, 7, 1, 4, 6, 0] 8 = 0 := by decide +kernel
  have g : pf (y ∘ tabF [2, 3, 8, 5, 7, 1, 4, 6, 0]) = (((y 2) && (y 3)) || ((y 3) && (y 8)) || ((y 8) && (y 5)) || ((y 5) && (y 7)) || ((y 7) && (y 2)) || ((y 2) && (y 1)) || ((y 3) && (y 4)) || ((y 8) && (y 6)) || ((y 5) && (y 0)) || ((y 1) && (y 6)) || ((y 4) && (y 0)) || ((y 0) && (y 1))) := by
    simp only [pf, Function.comp_apply, t0, t1, t2, t3, t4, t5, t6, t7, t8]
  exact g.trans (invb_5 (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8))

lemma invb_6 : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 : Bool,
    ((a3 && a2) || (a2 && a1) || (a1 && a0) || (a0 && a4) || (a4 && a3) || (a3 && a8) || (a2 && a7) || (a1 && a6) || (a0 && a5) || (a8 && a6) || (a7 && a5) || (a5 && a8)) = ((a0 && a1) || (a1 && a2) || (a2 && a3) || (a3 && a4) || (a4 && a0) || (a0 && a5) || (a1 && a6) || (a2 && a7) || (a3 && a8) || (a5 && a7) || (a6 && a8) || (a8 && a5)) := by
  decide +kernel

lemma inv_6 (y : Fin 9 → Bool) : pf (y ∘ tabF [3, 2, 1, 0, 4, 8, 7, 6, 5]) = pf y := by
  have t0 : tabF [3, 2, 1, 0, 4, 8, 7, 6, 5] 0 = 3 := by decide +kernel
  have t1 : tabF [3, 2, 1, 0, 4, 8, 7, 6, 5] 1 = 2 := by decide +kernel
  have t2 : tabF [3, 2, 1, 0, 4, 8, 7, 6, 5] 2 = 1 := by decide +kernel
  have t3 : tabF [3, 2, 1, 0, 4, 8, 7, 6, 5] 3 = 0 := by decide +kernel
  have t4 : tabF [3, 2, 1, 0, 4, 8, 7, 6, 5] 4 = 4 := by decide +kernel
  have t5 : tabF [3, 2, 1, 0, 4, 8, 7, 6, 5] 5 = 8 := by decide +kernel
  have t6 : tabF [3, 2, 1, 0, 4, 8, 7, 6, 5] 6 = 7 := by decide +kernel
  have t7 : tabF [3, 2, 1, 0, 4, 8, 7, 6, 5] 7 = 6 := by decide +kernel
  have t8 : tabF [3, 2, 1, 0, 4, 8, 7, 6, 5] 8 = 5 := by decide +kernel
  have g : pf (y ∘ tabF [3, 2, 1, 0, 4, 8, 7, 6, 5]) = (((y 3) && (y 2)) || ((y 2) && (y 1)) || ((y 1) && (y 0)) || ((y 0) && (y 4)) || ((y 4) && (y 3)) || ((y 3) && (y 8)) || ((y 2) && (y 7)) || ((y 1) && (y 6)) || ((y 0) && (y 5)) || ((y 8) && (y 6)) || ((y 7) && (y 5)) || ((y 5) && (y 8))) := by
    simp only [pf, Function.comp_apply, t0, t1, t2, t3, t4, t5, t6, t7, t8]
  exact g.trans (invb_6 (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8))

lemma invb_7 : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 : Bool,
    ((a3 && a8) || (a8 && a5) || (a5 && a0) || (a0 && a4) || (a4 && a3) || (a3 && a2) || (a8 && a6) || (a5 && a7) || (a0 && a1) || (a2 && a7) || (a6 && a1) || (a1 && a2)) = ((a0 && a1) || (a1 && a2) || (a2 && a3) || (a3 && a4) || (a4 && a0) || (a0 && a5) || (a1 && a6) || (a2 && a7) || (a3 && a8) || (a5 && a7) || (a6 && a8) || (a8 && a5)) := by
  decide +kernel

lemma inv_7 (y : Fin 9 → Bool) : pf (y ∘ tabF [3, 8, 5, 0, 4, 2, 6, 7, 1]) = pf y := by
  have t0 : tabF [3, 8, 5, 0, 4, 2, 6, 7, 1] 0 = 3 := by decide +kernel
  have t1 : tabF [3, 8, 5, 0, 4, 2, 6, 7, 1] 1 = 8 := by decide +kernel
  have t2 : tabF [3, 8, 5, 0, 4, 2, 6, 7, 1] 2 = 5 := by decide +kernel
  have t3 : tabF [3, 8, 5, 0, 4, 2, 6, 7, 1] 3 = 0 := by decide +kernel
  have t4 : tabF [3, 8, 5, 0, 4, 2, 6, 7, 1] 4 = 4 := by decide +kernel
  have t5 : tabF [3, 8, 5, 0, 4, 2, 6, 7, 1] 5 = 2 := by decide +kernel
  have t6 : tabF [3, 8, 5, 0, 4, 2, 6, 7, 1] 6 = 6 := by decide +kernel
  have t7 : tabF [3, 8, 5, 0, 4, 2, 6, 7, 1] 7 = 7 := by decide +kernel
  have t8 : tabF [3, 8, 5, 0, 4, 2, 6, 7, 1] 8 = 1 := by decide +kernel
  have g : pf (y ∘ tabF [3, 8, 5, 0, 4, 2, 6, 7, 1]) = (((y 3) && (y 8)) || ((y 8) && (y 5)) || ((y 5) && (y 0)) || ((y 0) && (y 4)) || ((y 4) && (y 3)) || ((y 3) && (y 2)) || ((y 8) && (y 6)) || ((y 5) && (y 7)) || ((y 0) && (y 1)) || ((y 2) && (y 7)) || ((y 6) && (y 1)) || ((y 1) && (y 2))) := by
    simp only [pf, Function.comp_apply, t0, t1, t2, t3, t4, t5, t6, t7, t8]
  exact g.trans (invb_7 (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8))

lemma invb_8 : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 : Bool,
    ((a5 && a0) || (a0 && a1) || (a1 && a2) || (a2 && a7) || (a7 && a5) || (a5 && a8) || (a0 && a4) || (a1 && a6) || (a2 && a3) || (a8 && a6) || (a4 && a3) || (a3 && a8)) = ((a0 && a1) || (a1 && a2) || (a2 && a3) || (a3 && a4) || (a4 && a0) || (a0 && a5) || (a1 && a6) || (a2 && a7) || (a3 && a8) || (a5 && a7) || (a6 && a8) || (a8 && a5)) := by
  decide +kernel

lemma inv_8 (y : Fin 9 → Bool) : pf (y ∘ tabF [5, 0, 1, 2, 7, 8, 4, 6, 3]) = pf y := by
  have t0 : tabF [5, 0, 1, 2, 7, 8, 4, 6, 3] 0 = 5 := by decide +kernel
  have t1 : tabF [5, 0, 1, 2, 7, 8, 4, 6, 3] 1 = 0 := by decide +kernel
  have t2 : tabF [5, 0, 1, 2, 7, 8, 4, 6, 3] 2 = 1 := by decide +kernel
  have t3 : tabF [5, 0, 1, 2, 7, 8, 4, 6, 3] 3 = 2 := by decide +kernel
  have t4 : tabF [5, 0, 1, 2, 7, 8, 4, 6, 3] 4 = 7 := by decide +kernel
  have t5 : tabF [5, 0, 1, 2, 7, 8, 4, 6, 3] 5 = 8 := by decide +kernel
  have t6 : tabF [5, 0, 1, 2, 7, 8, 4, 6, 3] 6 = 4 := by decide +kernel
  have t7 : tabF [5, 0, 1, 2, 7, 8, 4, 6, 3] 7 = 6 := by decide +kernel
  have t8 : tabF [5, 0, 1, 2, 7, 8, 4, 6, 3] 8 = 3 := by decide +kernel
  have g : pf (y ∘ tabF [5, 0, 1, 2, 7, 8, 4, 6, 3]) = (((y 5) && (y 0)) || ((y 0) && (y 1)) || ((y 1) && (y 2)) || ((y 2) && (y 7)) || ((y 7) && (y 5)) || ((y 5) && (y 8)) || ((y 0) && (y 4)) || ((y 1) && (y 6)) || ((y 2) && (y 3)) || ((y 8) && (y 6)) || ((y 4) && (y 3)) || ((y 3) && (y 8))) := by
    simp only [pf, Function.comp_apply, t0, t1, t2, t3, t4, t5, t6, t7, t8]
  exact g.trans (invb_8 (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8))

lemma invb_9 : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 : Bool,
    ((a5 && a8) || (a8 && a3) || (a3 && a2) || (a2 && a7) || (a7 && a5) || (a5 && a0) || (a8 && a6) || (a3 && a4) || (a2 && a1) || (a0 && a4) || (a6 && a1) || (a1 && a0)) = ((a0 && a1) || (a1 && a2) || (a2 && a3) || (a3 && a4) || (a4 && a0) || (a0 && a5) || (a1 && a6) || (a2 && a7) || (a3 && a8) || (a5 && a7) || (a6 && a8) || (a8 && a5)) := by
  decide +kernel

lemma inv_9 (y : Fin 9 → Bool) : pf (y ∘ tabF [5, 8, 3, 2, 7, 0, 6, 4, 1]) = pf y := by
  have t0 : tabF [5, 8, 3, 2, 7, 0, 6, 4, 1] 0 = 5 := by decide +kernel
  have t1 : tabF [5, 8, 3, 2, 7, 0, 6, 4, 1] 1 = 8 := by decide +kernel
  have t2 : tabF [5, 8, 3, 2, 7, 0, 6, 4, 1] 2 = 3 := by decide +kernel
  have t3 : tabF [5, 8, 3, 2, 7, 0, 6, 4, 1] 3 = 2 := by decide +kernel
  have t4 : tabF [5, 8, 3, 2, 7, 0, 6, 4, 1] 4 = 7 := by decide +kernel
  have t5 : tabF [5, 8, 3, 2, 7, 0, 6, 4, 1] 5 = 0 := by decide +kernel
  have t6 : tabF [5, 8, 3, 2, 7, 0, 6, 4, 1] 6 = 6 := by decide +kernel
  have t7 : tabF [5, 8, 3, 2, 7, 0, 6, 4, 1] 7 = 4 := by decide +kernel
  have t8 : tabF [5, 8, 3, 2, 7, 0, 6, 4, 1] 8 = 1 := by decide +kernel
  have g : pf (y ∘ tabF [5, 8, 3, 2, 7, 0, 6, 4, 1]) = (((y 5) && (y 8)) || ((y 8) && (y 3)) || ((y 3) && (y 2)) || ((y 2) && (y 7)) || ((y 7) && (y 5)) || ((y 5) && (y 0)) || ((y 8) && (y 6)) || ((y 3) && (y 4)) || ((y 2) && (y 1)) || ((y 0) && (y 4)) || ((y 6) && (y 1)) || ((y 1) && (y 0))) := by
    simp only [pf, Function.comp_apply, t0, t1, t2, t3, t4, t5, t6, t7, t8]
  exact g.trans (invb_9 (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8))

lemma invb_10 : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 : Bool,
    ((a8 && a3) || (a3 && a2) || (a2 && a1) || (a1 && a6) || (a6 && a8) || (a8 && a5) || (a3 && a4) || (a2 && a7) || (a1 && a0) || (a5 && a7) || (a4 && a0) || (a0 && a5)) = ((a0 && a1) || (a1 && a2) || (a2 && a3) || (a3 && a4) || (a4 && a0) || (a0 && a5) || (a1 && a6) || (a2 && a7) || (a3 && a8) || (a5 && a7) || (a6 && a8) || (a8 && a5)) := by
  decide +kernel

lemma inv_10 (y : Fin 9 → Bool) : pf (y ∘ tabF [8, 3, 2, 1, 6, 5, 4, 7, 0]) = pf y := by
  have t0 : tabF [8, 3, 2, 1, 6, 5, 4, 7, 0] 0 = 8 := by decide +kernel
  have t1 : tabF [8, 3, 2, 1, 6, 5, 4, 7, 0] 1 = 3 := by decide +kernel
  have t2 : tabF [8, 3, 2, 1, 6, 5, 4, 7, 0] 2 = 2 := by decide +kernel
  have t3 : tabF [8, 3, 2, 1, 6, 5, 4, 7, 0] 3 = 1 := by decide +kernel
  have t4 : tabF [8, 3, 2, 1, 6, 5, 4, 7, 0] 4 = 6 := by decide +kernel
  have t5 : tabF [8, 3, 2, 1, 6, 5, 4, 7, 0] 5 = 5 := by decide +kernel
  have t6 : tabF [8, 3, 2, 1, 6, 5, 4, 7, 0] 6 = 4 := by decide +kernel
  have t7 : tabF [8, 3, 2, 1, 6, 5, 4, 7, 0] 7 = 7 := by decide +kernel
  have t8 : tabF [8, 3, 2, 1, 6, 5, 4, 7, 0] 8 = 0 := by decide +kernel
  have g : pf (y ∘ tabF [8, 3, 2, 1, 6, 5, 4, 7, 0]) = (((y 8) && (y 3)) || ((y 3) && (y 2)) || ((y 2) && (y 1)) || ((y 1) && (y 6)) || ((y 6) && (y 8)) || ((y 8) && (y 5)) || ((y 3) && (y 4)) || ((y 2) && (y 7)) || ((y 1) && (y 0)) || ((y 5) && (y 7)) || ((y 4) && (y 0)) || ((y 0) && (y 5))) := by
    simp only [pf, Function.comp_apply, t0, t1, t2, t3, t4, t5, t6, t7, t8]
  exact g.trans (invb_10 (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8))

lemma invb_11 : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 : Bool,
    ((a8 && a5) || (a5 && a0) || (a0 && a1) || (a1 && a6) || (a6 && a8) || (a8 && a3) || (a5 && a7) || (a0 && a4) || (a1 && a2) || (a3 && a4) || (a7 && a2) || (a2 && a3)) = ((a0 && a1) || (a1 && a2) || (a2 && a3) || (a3 && a4) || (a4 && a0) || (a0 && a5) || (a1 && a6) || (a2 && a7) || (a3 && a8) || (a5 && a7) || (a6 && a8) || (a8 && a5)) := by
  decide +kernel

lemma inv_11 (y : Fin 9 → Bool) : pf (y ∘ tabF [8, 5, 0, 1, 6, 3, 7, 4, 2]) = pf y := by
  have t0 : tabF [8, 5, 0, 1, 6, 3, 7, 4, 2] 0 = 8 := by decide +kernel
  have t1 : tabF [8, 5, 0, 1, 6, 3, 7, 4, 2] 1 = 5 := by decide +kernel
  have t2 : tabF [8, 5, 0, 1, 6, 3, 7, 4, 2] 2 = 0 := by decide +kernel
  have t3 : tabF [8, 5, 0, 1, 6, 3, 7, 4, 2] 3 = 1 := by decide +kernel
  have t4 : tabF [8, 5, 0, 1, 6, 3, 7, 4, 2] 4 = 6 := by decide +kernel
  have t5 : tabF [8, 5, 0, 1, 6, 3, 7, 4, 2] 5 = 3 := by decide +kernel
  have t6 : tabF [8, 5, 0, 1, 6, 3, 7, 4, 2] 6 = 7 := by decide +kernel
  have t7 : tabF [8, 5, 0, 1, 6, 3, 7, 4, 2] 7 = 4 := by decide +kernel
  have t8 : tabF [8, 5, 0, 1, 6, 3, 7, 4, 2] 8 = 2 := by decide +kernel
  have g : pf (y ∘ tabF [8, 5, 0, 1, 6, 3, 7, 4, 2]) = (((y 8) && (y 5)) || ((y 5) && (y 0)) || ((y 0) && (y 1)) || ((y 1) && (y 6)) || ((y 6) && (y 8)) || ((y 8) && (y 3)) || ((y 5) && (y 7)) || ((y 0) && (y 4)) || ((y 1) && (y 2)) || ((y 3) && (y 4)) || ((y 7) && (y 2)) || ((y 2) && (y 3))) := by
    simp only [pf, Function.comp_apply, t0, t1, t2, t3, t4, t5, t6, t7, t8]
  exact g.trans (invb_11 (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8))

lemma pf_inv (σ : Fin 9 → Fin 9) (hσ : σ ∈ autos) (y : Fin 9 → Bool) : pf (y ∘ σ) = pf y := by
  unfold autos at hσ
  simp only [List.mem_cons] at hσ
  rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
  · exact inv_0 y
  · exact inv_1 y
  · exact inv_2 y
  · exact inv_3 y
  · exact inv_4 y
  · exact inv_5 y
  · exact inv_6 y
  · exact inv_7 y
  · exact inv_8 y
  · exact inv_9 y
  · exact inv_10 y
  · exact inv_11 y
  · cases h

set_option maxRecDepth 100000 in
lemma orbit1 : ∀ a : Fin 9, ∃ σ ∈ autos, σ a = 0 ∨ σ a = 4 := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma orbit2 : ∀ a b : Fin 9, a ≠ b →
    ∃ σ ∈ autos, pairOK (σ a) (σ b) ∨ pairOK (σ b) (σ a) := by
  decide +kernel

lemma pf_single : ∀ k : Fin 9, pf (fun i => decide (i = k)) = false := by
  decide +kernel

lemma no_empty (C : Circuit) (hg : C.gates = []) (hf : circuitFun 9 C = pf) : False := by
  have hev : ∀ y : Fin 9 → Bool, (List.ofFn y).getD C.output false = pf y := by
    intro y
    have h := congrFun hf y
    have h2 : circuitFun 9 C y = (List.ofFn y).getD C.output false := by
      show (C.wires (List.ofFn y)).getD C.output false = _
      rw [wires_eq, hg, List.foldl_nil]
    exact h2.symm.trans h
  by_cases ho : C.output < 9
  · have h := hev (fun i : Fin 9 => decide (i = (⟨C.output, ho⟩ : Fin 9)))
    have h1 := ofFn_getD_lt (fun i : Fin 9 => decide (i = (⟨C.output, ho⟩ : Fin 9))) C.output ho
    have h2 := pf_single ⟨C.output, ho⟩
    have h3 : decide ((⟨C.output, ho⟩ : Fin 9) = ⟨C.output, ho⟩) = false :=
      h1.symm.trans (h.trans h2)
    simp at h3
  · have h := hev (fun _ => true)
    rw [ofFn_getD_ge _ _ (by omega)] at h
    exact absurd h (by decide)

lemma relab_fun (σ : Fin 9 → Fin 9) (hσ : σ ∈ autos) (C : Circuit)
    (hf : circuitFun 9 C = pf) : circuitFun 9 (relabC σ C) = pf := by
  funext y
  have e1 : circuitFun 9 (relabC σ C) y = (C.wires (List.ofFn (y ∘ σ))).getD C.output false :=
    relab_wires σ C y C.output
  have e2 : (C.wires (List.ofFn (y ∘ σ))).getD C.output false = pf (y ∘ σ) :=
    congrFun hf (y ∘ σ)
  exact e1.trans (e2.trans (pf_inv σ hσ y))

lemma minimal_ge
    (H : ∀ C : Circuit, IsMinimalCircuit 9 C → (∃ x y : Fin 9 → Bool, circuitFun 9 C x ≠ circuitFun 9 C y) → (∀ j : ℕ, j < C.gates.length → ∃ x y : Fin 9 → Bool, (C.wires (List.ofFn x)).getD (9 + j) false ≠ (C.wires (List.ofFn y)).getD (9 + j) false) ∧ (∀ i j : ℕ, i < 9 + j → j < C.gates.length → ∃ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD i false ≠ (C.wires (List.ofFn x)).getD (9 + j) false))
    (HN : ∀ c : Fin 9, (c = 0 ∨ c = 4) → ∀ C : Circuit, FanInTwo C → (∀ y : Fin 9 → Bool, w9 C y = !(y c)) → circuitFun 9 C = pf → 16 ≤ C.size)
    (HA : ∀ c d : Fin 9, pairOK c d → ∀ C : Circuit, FanInTwo C → (∀ y : Fin 9 → Bool, w9 C y = (y c && y d)) → circuitFun 9 C = pf → 16 ≤ C.size)
    (HO : ∀ c d : Fin 9, pairOK c d → ∀ C : Circuit, FanInTwo C → (∀ y : Fin 9 → Bool, w9 C y = (y c || y d)) → circuitFun 9 C = pf → 16 ≤ C.size)
    (C : Circuit) (hmin : IsMinimalCircuit 9 C) (hf : circuitFun 9 C = pf) : 16 ≤ C.size := by
  have hnc : ∃ x y : Fin 9 → Bool, circuitFun 9 C x ≠ circuitFun 9 C y :=
    ⟨fun _ => false, fun _ => true, by rw [hf]; decide⟩
  obtain ⟨ha, hb⟩ := H C hmin hnc
  have hcases : (∃ g0 rest, C.gates = g0 :: rest) ∨ C.gates = [] := by
    cases hc : C.gates with
    | nil => exact Or.inr rfl
    | cons g r => exact Or.inl ⟨g, r, rfl⟩
  rcases hcases with ⟨g0, rest, hg⟩ | hg
  · have hlen : 0 < C.gates.length := by
      rw [hg]
      simp
    have hfan := hmin.1 g0 (by rw [hg]; simp)
    have hnc9 : ∃ x y : Fin 9 → Bool, w9 C x ≠ w9 C y := ha 0 hlen
    have hne9 : ∀ i : Fin 9, ∃ x : Fin 9 → Bool, x i ≠ w9 C x := by
      intro i
      obtain ⟨x, hx⟩ := hb i.val 0 (by have := i.isLt; omega) hlen
      refine ⟨x, ?_⟩
      rw [wires_input C x i.val i.isLt] at hx
      exact hx
    rcases gateShape g0.op g0.inputs (w9 C) hfan.1 hfan.2 (w9_first C g0 rest hg) hnc9 hne9
      with ⟨a, hA⟩ | ⟨a, b, hab, hA⟩ | ⟨a, b, hab, hA⟩
    · obtain ⟨σ, hσ, hσa⟩ := orbit1 a
      have h := HN (σ a) hσa (relabC σ C) (relab_fan σ C hmin.1)
        (fun y => by rw [relab_w9]; exact hA (y ∘ σ)) (relab_fun σ hσ C hf)
      rw [relab_size] at h
      exact h
    · obtain ⟨σ, hσ, hp | hp⟩ := orbit2 a b hab
      · have h := HA (σ a) (σ b) hp (relabC σ C) (relab_fan σ C hmin.1)
          (fun y => by rw [relab_w9]; exact hA (y ∘ σ)) (relab_fun σ hσ C hf)
        rw [relab_size] at h
        exact h
      · have h := HA (σ b) (σ a) hp (relabC σ C) (relab_fan σ C hmin.1)
          (fun y => by rw [relab_w9]; exact (hA (y ∘ σ)).trans (Bool.and_comm _ _))
          (relab_fun σ hσ C hf)
        rw [relab_size] at h
        exact h
    · obtain ⟨σ, hσ, hp | hp⟩ := orbit2 a b hab
      · have h := HO (σ a) (σ b) hp (relabC σ C) (relab_fan σ C hmin.1)
          (fun y => by rw [relab_w9]; exact hA (y ∘ σ)) (relab_fun σ hσ C hf)
        rw [relab_size] at h
        exact h
      · have h := HO (σ b) (σ a) hp (relabC σ C) (relab_fan σ C hmin.1)
          (fun y => by rw [relab_w9]; exact (hA (y ∘ σ)).trans (Bool.or_comm _ _))
          (relab_fun σ hσ C hf)
        rw [relab_size] at h
        exact h
  · exact (no_empty C hg hf).elim

lemma all_ge
    (H : ∀ C : Circuit, IsMinimalCircuit 9 C → (∃ x y : Fin 9 → Bool, circuitFun 9 C x ≠ circuitFun 9 C y) → (∀ j : ℕ, j < C.gates.length → ∃ x y : Fin 9 → Bool, (C.wires (List.ofFn x)).getD (9 + j) false ≠ (C.wires (List.ofFn y)).getD (9 + j) false) ∧ (∀ i j : ℕ, i < 9 + j → j < C.gates.length → ∃ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD i false ≠ (C.wires (List.ofFn x)).getD (9 + j) false))
    (HN : ∀ c : Fin 9, (c = 0 ∨ c = 4) → ∀ C : Circuit, FanInTwo C → (∀ y : Fin 9 → Bool, w9 C y = !(y c)) → circuitFun 9 C = pf → 16 ≤ C.size)
    (HA : ∀ c d : Fin 9, pairOK c d → ∀ C : Circuit, FanInTwo C → (∀ y : Fin 9 → Bool, w9 C y = (y c && y d)) → circuitFun 9 C = pf → 16 ≤ C.size)
    (HO : ∀ c d : Fin 9, pairOK c d → ∀ C : Circuit, FanInTwo C → (∀ y : Fin 9 → Bool, w9 C y = (y c || y d)) → circuitFun 9 C = pf → 16 ≤ C.size) :
    ∀ s : ℕ, ∀ C : Circuit, FanInTwo C → C.size = s → circuitFun 9 C = pf → 16 ≤ s := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro C hfan hs hf
    by_cases hmin : ∀ D : Circuit, FanInTwo D → circuitFun 9 D = circuitFun 9 C →
        C.size ≤ D.size
    · have hm : IsMinimalCircuit 9 C := And.intro hfan hmin
      have h := minimal_ge H HN HA HO C hm hf
      omega
    · push_neg at hmin
      obtain ⟨D, hD, hDf, hlt⟩ := hmin
      have h := ih D.size (by omega) D hD rfl (hDf.trans hf)
      omega

theorem core
    (H : ∀ C : Circuit, IsMinimalCircuit 9 C → (∃ x y : Fin 9 → Bool, circuitFun 9 C x ≠ circuitFun 9 C y) → (∀ j : ℕ, j < C.gates.length → ∃ x y : Fin 9 → Bool, (C.wires (List.ofFn x)).getD (9 + j) false ≠ (C.wires (List.ofFn y)).getD (9 + j) false) ∧ (∀ i j : ℕ, i < 9 + j → j < C.gates.length → ∃ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD i false ≠ (C.wires (List.ofFn x)).getD (9 + j) false))
    (HN : ∀ c : Fin 9, (c = 0 ∨ c = 4) → ∀ C : Circuit, FanInTwo C → (∀ y : Fin 9 → Bool, w9 C y = !(y c)) → circuitFun 9 C = pf → 16 ≤ C.size)
    (HA : ∀ c d : Fin 9, pairOK c d → ∀ C : Circuit, FanInTwo C → (∀ y : Fin 9 → Bool, w9 C y = (y c && y d)) → circuitFun 9 C = pf → 16 ≤ C.size)
    (HO : ∀ c d : Fin 9, pairOK c d → ∀ C : Circuit, FanInTwo C → (∀ y : Fin 9 → Bool, w9 C y = (y c || y d)) → circuitFun 9 C = pf → 16 ≤ C.size) :
    ¬ HasCircuitSize 9 pf 15 := by
  rintro ⟨C, hfan, hsz, hev⟩
  have h := all_ge H HN HA HO C.size C hfan rfl (by funext x; exact hev x)
  omega

theorem main_aux : (∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit n C → (∃ x y : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x ≠ PEqualNP.MetaComplexity.circuitFun n C y) → (∀ j : ℕ, j < C.gates.length → ∃ x y : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j) false ≠ (C.wires (List.ofFn y)).getD (n + j) false) ∧ (∀ i j : ℕ, i < n + j → j < C.gates.length → ∃ x : Fin n → Bool, (C.wires (List.ofFn x)).getD i false ≠ (C.wires (List.ofFn x)).getD (n + j) false) ∧ (C.gates ≠ [] → C.output + 1 = n + C.gates.length) ∧ (∀ j : ℕ, j + 1 < C.gates.length → ∃ p ∈ C.gates.zipIdx, n + j < n + p.2 ∧ (PEqualNP.CircuitLowerBounds.GateOp.casesOn (motive := fun _ => List ℕ) p.1.op p.1.inputs p.1.inputs (p.1.inputs.take 1) (fun _ => p.1.inputs) p.1.inputs).contains (n + j) = true)) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 0)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 4)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 1)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 2)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 3)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 4)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 && y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 1)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 2)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 3)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 4)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 || y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 15 := by
  intro H h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  refine core (fun C hC hnc => ⟨(H 9 C hC hnc).1, (H 9 C hC hnc).2.1⟩) ?_ ?_ ?_
  · rintro c (rfl | rfl)
    · exact h1
    · exact h2
  · rintro c d (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact h3
    · exact h4
    · exact h5
    · exact h6
    · exact h7
    · exact h8
  · rintro c d (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact h9
    · exact h10
    · exact h11
    · exact h12
    · exact h13
    · exact h14

end PEqualNP.Outside.L_meta_1697

theorem PEqualNP.Outside.L_meta_1697 : (∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit n C → (∃ x y : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x ≠ PEqualNP.MetaComplexity.circuitFun n C y) → (∀ j : ℕ, j < C.gates.length → ∃ x y : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j) false ≠ (C.wires (List.ofFn y)).getD (n + j) false) ∧ (∀ i j : ℕ, i < n + j → j < C.gates.length → ∃ x : Fin n → Bool, (C.wires (List.ofFn x)).getD i false ≠ (C.wires (List.ofFn x)).getD (n + j) false) ∧ (C.gates ≠ [] → C.output + 1 = n + C.gates.length) ∧ (∀ j : ℕ, j + 1 < C.gates.length → ∃ p ∈ C.gates.zipIdx, n + j < n + p.2 ∧ (PEqualNP.CircuitLowerBounds.GateOp.casesOn (motive := fun _ => List ℕ) p.1.op p.1.inputs p.1.inputs (p.1.inputs.take 1) (fun _ => p.1.inputs) p.1.inputs).contains (n + j) = true)) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 0)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 4)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 1)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 2)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 3)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 4)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 && y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 1)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 2)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 3)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 4)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 || y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 15 :=
  PEqualNP.Outside.L_meta_1697.main_aux
