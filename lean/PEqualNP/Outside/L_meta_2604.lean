import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2604

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl

theorem W_single (g : Gate) (w : List Bool) : W [g] w = step w g := rfl

theorem W_append (a b : List Gate) (w : List Bool) : W (a ++ b) w = W b (W a w) := by
  simp [W, List.foldl_append]

theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem getD_app_lt (l l2 : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l2).getD i false = l.getD i false := by
  simp [List.getD, List.getElem?_append_left h]

theorem getD_app_len (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD]

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

theorem or2_step (V : List Bool) (p q k : ℕ) (hk : k = V.length) :
    (step V ⟨GateOp.or, [p, q]⟩).getD k false = (V.getD p false || V.getD q false) := by
  subst hk
  show (V ++ [GateOp.or.eval ([p, q].map fun i => V.getD i false)]).getD V.length false = _
  rw [getD_app_len]
  simp [GateOp.eval]

theorem split_at (gs : List Gate) : ∀ (j : ℕ) (g g2 : Gate), gs[j]? = some g →
    ∃ pre post, pre.length = j ∧ gs = pre ++ g :: post ∧ gs.set j g2 = pre ++ g2 :: post := by
  induction gs with
  | nil => intro j g g2 h; simp at h
  | cons a gs ih =>
    intro j g g2 h
    cases j with
    | zero =>
      have ha : a = g := by simpa using h
      subst ha
      exact ⟨[], gs, rfl, rfl, rfl⟩
    | succ j =>
      have h2 : gs[j]? = some g := by simpa using h
      obtain ⟨pre, post, hl, e1, e2⟩ := ih j g g2 h2
      refine ⟨a :: pre, post, by rw [List.length_cons, hl], ?_, ?_⟩
      · exact congrArg (List.cons a) e1
      · exact congrArg (List.cons a) e2

theorem core (P : List Bool) (post : List Gate) (u t o k : ℕ) (ht : t < P.length)
    (hk : k = P.length + 1 + post.length)
    (himp : (W post (step P ⟨GateOp.or, [u, t]⟩)).getD t false = true →
      (W post (step P ⟨GateOp.or, [u, t]⟩)).getD o false = true) :
    (step (W post (step P ⟨GateOp.or, [u]⟩)) ⟨GateOp.or, [o, t]⟩).getD k false
      = (W post (step P ⟨GateOp.or, [u, t]⟩)).getD o false := by
  have hLn : k = (W post (step P ⟨GateOp.or, [u]⟩)).length := by
    rw [W_length, step_len]
    exact hk
  rw [or2_step _ _ _ _ hLn]
  have hn_t : (W post (step P ⟨GateOp.or, [u]⟩)).getD t false = P.getD t false := by
    rw [W_prefix _ _ _ (by rw [step_len]; omega)]
    exact getD_app_lt P _ t ht
  have ho_t : (W post (step P ⟨GateOp.or, [u, t]⟩)).getD t false = P.getD t false := by
    rw [W_prefix _ _ _ (by rw [step_len]; omega)]
    exact getD_app_lt P _ t ht
  have e1 : GateOp.or.eval ([u].map fun i => P.getD i false) = P.getD u false := by
    simp [GateOp.eval]
  have e2 : GateOp.or.eval ([u, t].map fun i => P.getD i false)
      = (P.getD u false || P.getD t false) := by
    simp [GateOp.eval]
  rw [hn_t]
  rw [ho_t] at himp
  cases hpt : P.getD t false
  · have hstep : step P ⟨GateOp.or, [u]⟩ = step P ⟨GateOp.or, [u, t]⟩ := by
      show P ++ [GateOp.or.eval ([u].map fun i => P.getD i false)]
        = P ++ [GateOp.or.eval ([u, t].map fun i => P.getD i false)]
      rw [e1, e2, hpt, Bool.or_false]
    rw [hstep, Bool.or_false]
  · rw [himp hpt, Bool.or_true]

theorem main_aux : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (j u t : ℕ), PEqualNP.MetaComplexity.Monotone2 C → j < C.gates.length → C.gates[j]? = some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [u, t] } → t < n + j → (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true → PEqualNP.MetaComplexity.circuitFun n C x = true) → PEqualNP.MetaComplexity.circuitFun n { gates := C.gates.set j { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [u] } ++ [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [C.output, t] }], output := n + C.gates.length } = PEqualNP.MetaComplexity.circuitFun n C := by
  intro n C j u t _ hj hg ht himp
  obtain ⟨pre, post, hlen, h1, h2⟩ :=
    split_at C.gates j ⟨GateOp.or, [u, t]⟩ ⟨GateOp.or, [u]⟩ hg
  funext x
  have hP : (W pre (List.ofFn x)).length = n + j := by
    rw [W_length, List.length_ofFn, hlen]
  have hWo : W C.gates (List.ofFn x)
      = W post (step (W pre (List.ofFn x)) ⟨GateOp.or, [u, t]⟩) := by
    rw [h1, W_append, W_cons]
  have hWn : W (C.gates.set j ⟨GateOp.or, [u]⟩ ++ [⟨GateOp.or, [C.output, t]⟩]) (List.ofFn x)
      = step (W post (step (W pre (List.ofFn x)) ⟨GateOp.or, [u]⟩))
          ⟨GateOp.or, [C.output, t]⟩ := by
    rw [h2, W_append, W_single, W_append, W_cons]
  have hlenC : C.gates.length = j + 1 + post.length := by
    have h3 := congrArg List.length h1
    rw [List.length_append, List.length_cons] at h3
    omega
  show (W (C.gates.set j ⟨GateOp.or, [u]⟩ ++ [⟨GateOp.or, [C.output, t]⟩])
      (List.ofFn x)).getD (n + C.gates.length) false
    = (W C.gates (List.ofFn x)).getD C.output false
  rw [hWn, hWo]
  refine core (W pre (List.ofFn x)) post u t C.output (n + C.gates.length)
    (by rw [hP]; exact ht) (by rw [hP]; omega) ?_
  rw [← hWo]
  exact himp x

end PEqualNP.Outside.L_meta_2604

theorem PEqualNP.Outside.L_meta_2604 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (j u t : ℕ), PEqualNP.MetaComplexity.Monotone2 C → j < C.gates.length → C.gates[j]? = some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [u, t] } → t < n + j → (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true → PEqualNP.MetaComplexity.circuitFun n C x = true) → PEqualNP.MetaComplexity.circuitFun n { gates := C.gates.set j { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [u] } ++ [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [C.output, t] }], output := n + C.gates.length } = PEqualNP.MetaComplexity.circuitFun n C :=
  PEqualNP.Outside.L_meta_2604.main_aux
