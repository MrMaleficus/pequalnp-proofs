import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2430

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

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
    (∀ i, w2.getD (f i) false = w.getD i false) →
    (∀ i, i < w.length → f i < w2.length) →
    (∀ j, f (w.length + j) = w2.length + j) →
    ∀ i, (W (gs.map (ren f)) w2).getD (f i) false = (W gs w).getD i false := by
  induction gs with
  | nil =>
    intro w w2 hinv _ _ i
    exact hinv i
  | cons g gs ih =>
    intro w w2 hinv hlt hf i
    obtain ⟨v, hv0⟩ : ∃ v, g.op.eval (g.inputs.map fun i => w.getD i false) = v := ⟨_, rfl⟩
    have hmap : (ren f g).inputs.map (fun i => w2.getD i false)
        = g.inputs.map fun i => w.getD i false := by
      show (g.inputs.map f).map (fun i => w2.getD i false) = _
      rw [List.map_map]
      apply List.map_congr_left
      intro a _
      exact hinv a
    have hs : step w g = w ++ [v] := by rw [← hv0]; rfl
    have hs2 : step w2 (ren f g) = w2 ++ [v] := by
      show w2 ++ [g.op.eval ((ren f g).inputs.map fun i => w2.getD i false)] = _
      rw [hmap, hv0]
    rw [List.map_cons, W_cons, W_cons, hs, hs2]
    have hf0 : f w.length = w2.length := by
      have := hf 0
      simpa using this
    refine ih (w ++ [v]) (w2 ++ [v]) ?_ ?_ ?_ i
    · intro a
      by_cases h : a < w.length
      · rw [getD_app_lt _ _ _ (hlt a h), getD_app_lt _ _ _ h]
        exact hinv a
      · by_cases ha2 : a = w.length
        · rw [ha2, hf0, getD_app_len, getD_app_len]
        · have hfa := hf (a - w.length)
          have e : w.length + (a - w.length) = a := by omega
          rw [e] at hfa
          rw [hfa, getD_ge (w2 ++ [v]) (w2.length + (a - w.length))
              (by rw [List.length_append, List.length_singleton]; omega),
            getD_ge (w ++ [v]) a (by rw [List.length_append, List.length_singleton]; omega)]
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

def f4 (n1 n2 : ℕ) (σ : Fin n1 → Fin n2) (i : ℕ) : ℕ :=
  if h : i < n1 then (σ ⟨i, h⟩ : ℕ) else n2 + (i - n1)

theorem f4_lt (n1 n2 : ℕ) (σ : Fin n1 → Fin n2) (i : ℕ) (h : i < n1) :
    f4 n1 n2 σ i = (σ ⟨i, h⟩ : ℕ) := by
  unfold f4
  rw [dif_pos h]

theorem f4_ge (n1 n2 : ℕ) (σ : Fin n1 → Fin n2) (j : ℕ) :
    f4 n1 n2 σ (n1 + j) = n2 + j := by
  unfold f4
  rw [dif_neg (by omega)]
  omega

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    (List.ofFn x).getD i false = x ⟨i, h⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using h)]
  simp

theorem partB (n2 m : ℕ) (σ : Fin n2 → Fin m) (WA : List Bool) (hWA : WA.length = m)
    (gs : List Gate) :
    ∀ i, (W (gs.map (ren (f4 n2 m σ))) WA).getD (f4 n2 m σ i) false
      = (W gs (List.ofFn fun j : Fin n2 => WA.getD (σ j) false)).getD i false := by
  intro i
  refine sim (f4 n2 m σ) gs (List.ofFn fun j : Fin n2 => WA.getD (σ j) false) WA ?_ ?_ ?_ i
  · intro a
    by_cases h : a < n2
    · rw [f4_lt n2 m σ a h]
      exact (ofFn_getD (fun j : Fin n2 => WA.getD (σ j) false) a h).symm
    · have hfa := f4_ge n2 m σ (a - n2)
      have e : n2 + (a - n2) = a := by omega
      rw [e] at hfa
      rw [hfa, getD_ge WA (m + (a - n2)) (by omega),
        getD_ge (List.ofFn fun j : Fin n2 => WA.getD (σ j) false) a
          (by rw [List.length_ofFn]; omega)]
  · intro a ha
    have h : a < n2 := by simpa using ha
    rw [f4_lt n2 m σ a h, hWA]
    exact (σ ⟨a, h⟩).isLt
  · intro j
    rw [List.length_ofFn, hWA]
    exact f4_ge n2 m σ j

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

def D (n1 n2 : ℕ) (A B : Circuit) (σ : Fin n2 → Fin (n1 + A.size)) : Circuit :=
  ⟨A.gates ++ B.gates.map (ren (f4 n2 (n1 + A.size) σ)) ++
    [⟨GateOp.or, [A.output, f4 n2 (n1 + A.size) σ B.output]⟩],
   n1 + A.gates.length + B.gates.length⟩

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

theorem D_mono (n1 n2 : ℕ) (A B : Circuit) (σ : Fin n2 → Fin (n1 + A.size))
    (hmA : Monotone2 A) (hmB : Monotone2 B) : Monotone2 (D n1 n2 A B σ) := by
  intro g hg
  simp only [D, List.mem_append, List.mem_singleton] at hg
  rcases hg with (h | h) | h
  · exact hmA g h
  · exact ren_mono _ _ hmB g h
  · subst h
    exact ⟨by simp, by simp⟩

theorem D_size (n1 n2 : ℕ) (A B : Circuit) (σ : Fin n2 → Fin (n1 + A.size)) :
    (D n1 n2 A B σ).size = A.size + B.size + 1 := by
  show (A.gates ++ B.gates.map (ren (f4 n2 (n1 + A.size) σ)) ++
    [(⟨GateOp.or, [A.output, f4 n2 (n1 + A.size) σ B.output]⟩ : Gate)]).length
      = A.gates.length + B.gates.length + 1
  rw [List.length_append, List.length_append, List.length_map, List.length_singleton]

theorem D_eval (n1 n2 : ℕ) (A B : Circuit) (σ : Fin n2 → Fin (n1 + A.size))
    (hout : A.output < n1 + A.size) (x : Fin n1 → Bool) :
    (D n1 n2 A B σ).eval (List.ofFn x)
      = (A.eval (List.ofFn x) || B.eval (List.ofFn fun j : Fin n2 =>
          (A.wires (List.ofFn x)).getD (σ j) false)) := by
  have hWA : (W A.gates (List.ofFn x)).length = n1 + A.size := by
    show (W A.gates (List.ofFn x)).length = n1 + A.gates.length
    rw [W_length, List.length_ofFn]
  have ha : (W (B.gates.map (ren (f4 n2 (n1 + A.size) σ))) (W A.gates (List.ofFn x))).getD
      A.output false = A.eval (List.ofFn x) :=
    W_prefix (B.gates.map (ren (f4 n2 (n1 + A.size) σ))) (W A.gates (List.ofFn x)) A.output
      (by rw [hWA]; exact hout)
  have hb : (W (B.gates.map (ren (f4 n2 (n1 + A.size) σ))) (W A.gates (List.ofFn x))).getD
      (f4 n2 (n1 + A.size) σ B.output) false
      = B.eval (List.ofFn fun j : Fin n2 => (A.wires (List.ofFn x)).getD (σ j) false) :=
    partB n2 (n1 + A.size) σ (W A.gates (List.ofFn x)) hWA B.gates B.output
  have hg := glue_sem A.gates (B.gates.map (ren (f4 n2 (n1 + A.size) σ))) (List.ofFn x)
    _ _ _ _ ha hb
  simp only [List.length_map, List.length_ofFn] at hg
  exact hg

theorem main_aux : ∀ (x1 x2 : ℕ) (x3 x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Fin x2 → Fin (x1 + x3.size)), x3.output < x1 + x3.size → PEqualNP.MetaComplexity.Monotone2 x3 → PEqualNP.MetaComplexity.Monotone2 x4 → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x9 ∧ x9.size ≤ x3.size + x4.size + (1 : ℕ) ∧ ∀ (x10 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x9 x10 = (PEqualNP.MetaComplexity.circuitFun x1 x3 x10 || PEqualNP.MetaComplexity.circuitFun x2 x4 fun (x11 : Fin x2) => (x3.wires (List.ofFn x10)).getD (↑(x5 x11)) Bool.false) := by
  intro n1 n2 A B σ hout hmA hmB
  refine ⟨D n1 n2 A B σ, D_mono n1 n2 A B σ hmA hmB, ?_, ?_⟩
  · exact Nat.le_of_eq (D_size n1 n2 A B σ)
  · intro x
    exact D_eval n1 n2 A B σ hout x

end PEqualNP.Outside.L_meta_2430

theorem PEqualNP.Outside.L_meta_2430 : ∀ (x1 x2 : ℕ) (x3 x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Fin x2 → Fin (x1 + x3.size)), x3.output < x1 + x3.size → PEqualNP.MetaComplexity.Monotone2 x3 → PEqualNP.MetaComplexity.Monotone2 x4 → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x9 ∧ x9.size ≤ x3.size + x4.size + (1 : ℕ) ∧ ∀ (x10 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x9 x10 = (PEqualNP.MetaComplexity.circuitFun x1 x3 x10 || PEqualNP.MetaComplexity.circuitFun x2 x4 fun (x11 : Fin x2) => (x3.wires (List.ofFn x10)).getD (↑(x5 x11)) Bool.false) :=
  PEqualNP.Outside.L_meta_2430.main_aux
