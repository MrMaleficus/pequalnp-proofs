import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2103

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = W C.gates x := rfl

theorem W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl

theorem W_append (a b : List Gate) (w : List Bool) : W (a ++ b) w = W b (W a w) := by
  simp [W, List.foldl_append]

theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem getD_app_lt (l l2 : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l2).getD i false = l.getD i false := by
  simp [List.getD, List.getElem?_append_left h]

theorem getD_app_len (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD]

theorem getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false :=
  List.getD_eq_default _ _ h

theorem W_length (gs : List Gate) :
    ∀ w : List Bool, (W gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [W]
  | cons g gs ih =>
    intro w
    rw [W_cons, ih, step_len, List.length_cons]
    omega

theorem W_prefix (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (W gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [W_cons, ih (step w g) i (by rw [step_len]; omega)]
    exact getD_app_lt w _ i hi

def ren (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

theorem sim (f : ℕ → ℕ) (gs : List Gate) : ∀ (w w2 : List Bool),
    (∀ (j : ℕ) (hj : j < gs.length), ∀ i ∈ (gs[j]).inputs, i < w.length + j) →
    (∀ i, i < w.length → w2.getD (f i) false = w.getD i false) →
    (∀ i, i < w.length → f i < w2.length) →
    (∀ j, f (w.length + j) = w2.length + j) →
    ∀ i, i < w.length + gs.length →
      (W (gs.map (ren f)) w2).getD (f i) false = (W gs w).getD i false := by
  induction gs with
  | nil =>
    intro w w2 _ hinv _ _ i hi
    exact hinv i (by simpa using hi)
  | cons g gs ih =>
    intro w w2 hread hinv hlt hf i hi
    obtain ⟨v, hv0⟩ : ∃ v, g.op.eval (g.inputs.map fun i => w.getD i false) = v := ⟨_, rfl⟩
    have hmap : (ren f g).inputs.map (fun i => w2.getD i false)
        = g.inputs.map fun i => w.getD i false := by
      show (g.inputs.map f).map (fun i => w2.getD i false) = _
      rw [List.map_map]
      apply List.map_congr_left
      intro a ha
      have h0 := hread 0 (by simp) a (by simpa using ha)
      exact hinv a (by simpa using h0)
    have hs : step w g = w ++ [v] := by rw [← hv0]; rfl
    have hs2 : step w2 (ren f g) = w2 ++ [v] := by
      show w2 ++ [g.op.eval ((ren f g).inputs.map fun i => w2.getD i false)] = _
      rw [hmap, hv0]
    rw [List.map_cons, W_cons, W_cons, hs, hs2]
    have hf0 : f w.length = w2.length := by
      have := hf 0
      simpa using this
    refine ih (w ++ [v]) (w2 ++ [v]) ?_ ?_ ?_ ?_ i ?_
    · intro j hj a ha
      have h1 := hread (j + 1) (by simp; omega) a (by simpa using ha)
      simp only [List.length_append, List.length_singleton]
      omega
    · intro a ha
      simp only [List.length_append, List.length_singleton] at ha
      by_cases h : a < w.length
      · rw [getD_app_lt _ _ _ (hlt a h), getD_app_lt _ _ _ h]
        exact hinv a h
      · have ha2 : a = w.length := by omega
        rw [ha2, hf0, getD_app_len, getD_app_len]
    · intro a ha
      simp only [List.length_append, List.length_singleton] at ha ⊢
      by_cases h : a < w.length
      · have := hlt a h
        omega
      · have ha2 : a = w.length := by omega
        rw [ha2, hf0]
        omega
    · intro j
      simp only [List.length_append, List.length_singleton]
      have := hf (j + 1)
      rw [show w.length + 1 + j = w.length + (j + 1) by omega, this]
      omega
    · simp only [List.length_append, List.length_singleton, List.length_cons] at hi ⊢
      omega

def f4 (n1 n2 : ℕ) (σ : Fin n1 → Fin n2) (i : ℕ) : ℕ :=
  if h : i < n1 then (σ ⟨i, h⟩ : ℕ) else n2 + (i - n1)

def f5 (n2 s : ℕ) (i : ℕ) : ℕ := if i < n2 then i else i + s

theorem f4_lt (n1 n2 : ℕ) (σ : Fin n1 → Fin n2) (i : ℕ) (h : i < n1) :
    f4 n1 n2 σ i = (σ ⟨i, h⟩ : ℕ) := by
  unfold f4
  rw [dif_pos h]

theorem f4_ge (n1 n2 : ℕ) (σ : Fin n1 → Fin n2) (j : ℕ) :
    f4 n1 n2 σ (n1 + j) = n2 + j := by
  unfold f4
  rw [dif_neg (by omega)]
  omega

theorem f4_bound (n1 n2 : ℕ) (σ : Fin n1 → Fin n2) (s i : ℕ) (h : i < n1 + s) :
    f4 n1 n2 σ i < n2 + s := by
  by_cases h1 : i < n1
  · rw [f4_lt n1 n2 σ i h1]
    have := (σ ⟨i, h1⟩).isLt
    omega
  · have hi : i = n1 + (i - n1) := by omega
    rw [hi, f4_ge]
    omega

theorem f5_lt (n2 s i : ℕ) (h : i < n2) : f5 n2 s i = i := by
  unfold f5
  rw [if_pos h]

theorem f5_ge (n2 s j : ℕ) : f5 n2 s (n2 + j) = n2 + s + j := by
  unfold f5
  rw [if_neg (by omega)]
  omega

theorem readsBack_get (n : ℕ) (C : Circuit) (h : NestedCover.ReadsBack n C) :
    ∀ (j : ℕ) (hj : j < C.gates.length), ∀ i ∈ (C.gates[j]).inputs, i < n + j := by
  intro j hj i hi
  apply h j hj i
  have e : NestedCover.gateAt C j = C.gates[j] := by
    unfold NestedCover.gateAt
    exact List.getD_eq_getElem _ _ hj
  rw [e]
  exact hi

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    (List.ofFn x).getD i false = x ⟨i, h⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using h)]
  simp

theorem part4 (n1 n2 : ℕ) (σ : Fin n1 → Fin n2) (C4 : Circuit)
    (hr4 : NestedCover.ReadsBack n1 C4) (x : Fin n2 → Bool) :
    ∀ i, i < n1 + C4.gates.length →
      (W (C4.gates.map (ren (f4 n1 n2 σ))) (List.ofFn x)).getD (f4 n1 n2 σ i) false
        = (W C4.gates (List.ofFn fun i => x (σ i))).getD i false := by
  intro i hi
  refine sim (f4 n1 n2 σ) C4.gates (List.ofFn fun i => x (σ i)) (List.ofFn x) ?_ ?_ ?_ ?_ i ?_
  · intro j hj a ha
    have := readsBack_get n1 C4 hr4 j hj a ha
    rw [List.length_ofFn]
    exact this
  · intro a ha
    have h : a < n1 := by simpa using ha
    have e1 : (List.ofFn fun i => x (σ i)).getD a false = x (σ ⟨a, h⟩) :=
      ofFn_getD (fun i => x (σ i)) a h
    have e2 : (List.ofFn x).getD (f4 n1 n2 σ a) false = x (σ ⟨a, h⟩) := by
      rw [f4_lt n1 n2 σ a h]
      exact ofFn_getD x _ (σ ⟨a, h⟩).isLt
    rw [e1, e2]
  · intro a ha
    have h : a < n1 := by simpa using ha
    rw [f4_lt n1 n2 σ a h, List.length_ofFn]
    exact (σ ⟨a, h⟩).isLt
  · intro j
    rw [List.length_ofFn, List.length_ofFn]
    exact f4_ge n1 n2 σ j
  · rw [List.length_ofFn]
    exact hi

theorem part5 (n2 : ℕ) (C5 : Circuit) (hr5 : NestedCover.ReadsBack n2 C5)
    (x : Fin n2 → Bool) (pre : List Gate) (s : ℕ) (hs : pre.length = s) :
    ∀ i, i < n2 + C5.gates.length →
      (W (C5.gates.map (ren (f5 n2 s))) (W pre (List.ofFn x))).getD (f5 n2 s i) false
        = (W C5.gates (List.ofFn x)).getD i false := by
  intro i hi
  refine sim (f5 n2 s) C5.gates (List.ofFn x) (W pre (List.ofFn x)) ?_ ?_ ?_ ?_ i ?_
  · intro j hj a ha
    have := readsBack_get n2 C5 hr5 j hj a ha
    rw [List.length_ofFn]
    exact this
  · intro a ha
    have h : a < n2 := by simpa using ha
    rw [f5_lt n2 s a h]
    exact W_prefix pre (List.ofFn x) a ha
  · intro a ha
    have h : a < n2 := by simpa using ha
    rw [f5_lt n2 s a h, W_length, List.length_ofFn]
    omega
  · intro j
    rw [W_length, List.length_ofFn, hs]
    exact f5_ge n2 s j
  · rw [List.length_ofFn]
    exact hi

theorem glue_sem (A B : List Gate) (X : List Bool) (a b : ℕ) (v4 v5 : Bool)
    (ha : (W B (W A X)).getD a false = v4) (hb : (W B (W A X)).getD b false = v5) :
    (W (A ++ B ++ [⟨GateOp.or, [a, b]⟩]) X).getD (X.length + A.length + B.length) false
      = (v4 || v5) := by
  rw [W_append, W_append]
  have hL : (W B (W A X)).length = X.length + A.length + B.length := by
    rw [W_length, W_length]
  rw [← hL, ← ha, ← hb]
  show (W B (W A X) ++ [GateOp.or.eval
    ([a, b].map fun i => (W B (W A X)).getD i false)]).getD (W B (W A X)).length false = _
  rw [getD_app_len]
  simp [GateOp.eval]

def D (n1 n2 : ℕ) (σ : Fin n1 → Fin n2) (C4 C5 : Circuit) : Circuit :=
  ⟨C4.gates.map (ren (f4 n1 n2 σ)) ++ C5.gates.map (ren (f5 n2 C4.gates.length)) ++
    [⟨GateOp.or,
      [if C4.output < n1 + C4.gates.length then f4 n1 n2 σ C4.output
        else n2 + C4.gates.length + C5.gates.length + 1,
       if C5.output < n2 + C5.gates.length then f5 n2 C4.gates.length C5.output
        else n2 + C4.gates.length + C5.gates.length + 1]⟩],
   n2 + C4.gates.length + C5.gates.length⟩

theorem ren_mono (f : ℕ → ℕ) (gs : List Gate)
    (h : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ gs.map (ren f),
      g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  rw [List.mem_map] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  have h0 := h g0 hg0
  refine ⟨h0.1, ?_⟩
  show (g0.inputs.map f).length ≤ 2
  rw [List.length_map]
  exact h0.2

theorem D_mono (n1 n2 : ℕ) (σ : Fin n1 → Fin n2) (C4 C5 : Circuit)
    (hm4 : Monotone2 C4) (hm5 : Monotone2 C5) : Monotone2 (D n1 n2 σ C4 C5) := by
  intro g hg
  simp only [D, List.mem_append, List.mem_singleton] at hg
  rcases hg with (h | h) | h
  · exact ren_mono _ _ hm4 g h
  · exact ren_mono _ _ hm5 g h
  · subst h
    exact ⟨by simp, by simp⟩

theorem D_eval (n1 n2 : ℕ) (σ : Fin n1 → Fin n2) (C4 C5 : Circuit)
    (hr4 : NestedCover.ReadsBack n1 C4) (hr5 : NestedCover.ReadsBack n2 C5)
    (x : Fin n2 → Bool) :
    (D n1 n2 σ C4 C5).eval (List.ofFn x)
      = (C4.eval (List.ofFn fun i => x (σ i)) || C5.eval (List.ofFn x)) := by
  have hL1 : (W (C4.gates.map (ren (f4 n1 n2 σ))) (List.ofFn x)).length
      = n2 + C4.gates.length := by
    rw [W_length, List.length_map, List.length_ofFn]
  have hL2 : (W (C5.gates.map (ren (f5 n2 C4.gates.length)))
      (W (C4.gates.map (ren (f4 n1 n2 σ))) (List.ofFn x))).length
      = n2 + C4.gates.length + C5.gates.length := by
    rw [W_length, hL1, List.length_map]
  have ha : (W (C5.gates.map (ren (f5 n2 C4.gates.length)))
      (W (C4.gates.map (ren (f4 n1 n2 σ))) (List.ofFn x))).getD
        (if C4.output < n1 + C4.gates.length then f4 n1 n2 σ C4.output
          else n2 + C4.gates.length + C5.gates.length + 1) false
      = C4.eval (List.ofFn fun i => x (σ i)) := by
    by_cases h : C4.output < n1 + C4.gates.length
    · rw [if_pos h, W_prefix _ _ _ (by rw [hL1]; exact f4_bound n1 n2 σ _ _ h)]
      exact part4 n1 n2 σ C4 hr4 x _ h
    · rw [if_neg h, getD_ge _ _ (by rw [hL2]; omega)]
      symm
      show (C4.wires (List.ofFn fun i => x (σ i))).getD C4.output false = false
      exact getD_ge _ _ (by rw [wires_eq, W_length, List.length_ofFn]; omega)
  have hb : (W (C5.gates.map (ren (f5 n2 C4.gates.length)))
      (W (C4.gates.map (ren (f4 n1 n2 σ))) (List.ofFn x))).getD
        (if C5.output < n2 + C5.gates.length then f5 n2 C4.gates.length C5.output
          else n2 + C4.gates.length + C5.gates.length + 1) false
      = C5.eval (List.ofFn x) := by
    by_cases h : C5.output < n2 + C5.gates.length
    · rw [if_pos h]
      exact part5 n2 C5 hr5 x _ _ (List.length_map _) _ h
    · rw [if_neg h, getD_ge _ _ (by rw [hL2]; omega)]
      symm
      show (C5.wires (List.ofFn x)).getD C5.output false = false
      exact getD_ge _ _ (by rw [wires_eq, W_length, List.length_ofFn]; omega)
  have hg := glue_sem (C4.gates.map (ren (f4 n1 n2 σ)))
    (C5.gates.map (ren (f5 n2 C4.gates.length))) (List.ofFn x) _ _ _ _ ha hb
  simp only [List.length_map, List.length_ofFn] at hg
  exact hg

theorem main_aux : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2) (x4 x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x4 → PEqualNP.MetaComplexity.Monotone2 x5 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x2 x5 → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ x10.size ≤ x4.size + x5.size + (1 : ℕ) ∧ ∀ (x11 : Fin x2 → Bool), PEqualNP.MetaComplexity.circuitFun x2 x10 x11 = ((PEqualNP.MetaComplexity.circuitFun x1 x4 fun (x12 : Fin x1) => x11 (x3 x12)) || PEqualNP.MetaComplexity.circuitFun x2 x5 x11) := by
  intro n1 n2 σ C4 C5 hm4 hr4 hm5 hr5
  refine ⟨D n1 n2 σ C4 C5, D_mono n1 n2 σ C4 C5 hm4 hm5, ?_, ?_⟩
  · simp only [Circuit.size, D, List.length_append, List.length_map, List.length_singleton]
    omega
  · intro x
    exact D_eval n1 n2 σ C4 C5 hr4 hr5 x

end PEqualNP.Outside.L_meta_2103

theorem PEqualNP.Outside.L_meta_2103 : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2) (x4 x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x4 → PEqualNP.MetaComplexity.Monotone2 x5 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x2 x5 → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ x10.size ≤ x4.size + x5.size + (1 : ℕ) ∧ ∀ (x11 : Fin x2 → Bool), PEqualNP.MetaComplexity.circuitFun x2 x10 x11 = ((PEqualNP.MetaComplexity.circuitFun x1 x4 fun (x12 : Fin x1) => x11 (x3 x12)) || PEqualNP.MetaComplexity.circuitFun x2 x5 x11) :=
  PEqualNP.Outside.L_meta_2103.main_aux
