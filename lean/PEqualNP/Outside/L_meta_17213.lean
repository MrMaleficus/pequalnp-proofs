import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17213

-- FRAGMENT fold    DEPENDS: (none)
-- Wire list as a fold over the gate list. C.wires x = W C.gates x (rfl), C.eval x = (W C.gates x).getD C.output false.
-- Exports:
--   def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
--   def W (gs : List Gate) (w : List Bool) := gs.foldl step w
--   wires_W C x : C.wires x = W C.gates x
--   eval_W C x : C.eval x = (W C.gates x).getD C.output false
--   circuitFun_W n C x : circuitFun n C x = (W C.gates (List.ofFn x)).getD C.output false
--   W_nil, W_cons : W (g :: gs) w = W gs (step w g), W_single : W [g] w = step w g
--   W_append : W (a ++ b) w = W b (W a w),  W_snoc : W (gs ++ [g]) w = step (W gs w) g
--   W_split j : W gs w = W (gs.drop j) (W (gs.take j) w)
--   step_len : (step w g).length = w.length + 1,  W_length : (W gs w).length = w.length + gs.length
--   getD_app_lt (i < l.length) : (l ++ l2).getD i false = l.getD i false
--   getD_app_len : (l ++ [v]).getD l.length false = v
--   getD_ge (l.length <= i) : l.getD i false = false
--   step_lt (i < w.length) : (step w g).getD i false = w.getD i false
--   step_last (k = w.length) : (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false)
--   W_prefix (i < w.length) : (W gs w).getD i false = w.getD i false
--   W_ge (w.length + gs.length <= i) : (W gs w).getD i false = false
--   W_snoc_getD : (W (gs ++ [g]) w).getD t false = if t = w.length + gs.length then (eval of g on W gs w) else (W gs w).getD t false
--   W_gate (j < gs.length) : (W gs w).getD (w.length + j) false
--        = gs[j].op.eval (gs[j].inputs.map fun i => if i < w.length + j then (W gs w).getD i false else false)
--   W_gate_pre (gs = pre ++ g :: post) : (W gs w).getD (w.length + pre.length) false = g.op.eval (g.inputs.map fun i => (W pre w).getD i false)
--   ofFn_getD (u < n) : (List.ofFn x).getD u false = x u
--   ofFn_getD_ge (n <= u) : (List.ofFn x).getD u false = false
--   split_gates (j < gs.length) : exists pre post, gs = pre ++ gs[j] :: post and pre.length = j
--   split2 (gs[j]? = some g) : exists pre post, pre.length = j, gs = pre ++ g :: post, and for all g2, gs.set j g2 = pre ++ g2 :: post
--   step_congr : same gate value on P gives same step
--   gateAt_eq (j < C.gates.length) : gateAt C j = C.gates[j],  gateAt_mem : gateAt C j in C.gates
--   gateAt_ge (C.gates.length <= j) : gateAt C j = (OR of nothing)
--   getElem?_gateAt : C.gates[j]? = some g -> gateAt C j = g and j < C.gates.length
--   eval_and_iff : GateOp.and.eval (l.map f) = true iff all i in l, f i = true
--   eval_or_iff : GateOp.or.eval (l.map f) = true iff exists i in l, f i = true
--   eval_and2 / eval_or2 : GateOp.and.eval [a, b] = (a and b) / GateOp.or.eval [a, b] = (a or b);  eval_or1 / eval_and1 : one operand copies it
-- Use: rewrite C.wires/eval/circuitFun into W, split the gate list at the changed gate with split2,
-- then compare W post (step P g1) with W post (step P g2) (W_prefix for wires below, W_gate for gate wires).

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem wires_W (C : Circuit) (x : List Bool) : C.wires x = W C.gates x := rfl

theorem eval_W (C : Circuit) (x : List Bool) : C.eval x = (W C.gates x).getD C.output false := rfl

theorem circuitFun_W (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    circuitFun n C x = (W C.gates (List.ofFn x)).getD C.output false := rfl

theorem W_nil (w : List Bool) : W [] w = w := rfl

theorem W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl

theorem W_single (g : Gate) (w : List Bool) : W [g] w = step w g := rfl

theorem W_append (a b : List Gate) (w : List Bool) : W (a ++ b) w = W b (W a w) := by
  simp [W, List.foldl_append]

theorem W_snoc (gs : List Gate) (g : Gate) (w : List Bool) : W (gs ++ [g]) w = step (W gs w) g := by
  rw [W_append]; rfl

theorem W_split (gs : List Gate) (w : List Bool) (j : ℕ) :
    W gs w = W (gs.drop j) (W (gs.take j) w) := by
  rw [← W_append, List.take_append_drop]

theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem W_length (gs : List Gate) :
    ∀ w : List Bool, (W gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [W]
  | cons g gs ih =>
    intro w
    rw [W_cons, ih, step_len, List.length_cons]
    omega

theorem getD_app_lt (l l2 : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l2).getD i false = l.getD i false := by
  simp [List.getD, List.getElem?_append_left h]

theorem getD_app_len (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD]

theorem getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem step_lt (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) :
    (step w g).getD i false = w.getD i false := getD_app_lt w _ i h

theorem step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk; exact getD_app_len w _

theorem W_prefix (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (W gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [W_cons, ih (step w g) i (by rw [step_len]; omega)]
    exact getD_app_lt w _ i hi

theorem W_ge (gs : List Gate) (w : List Bool) (i : ℕ) (h : w.length + gs.length ≤ i) :
    (W gs w).getD i false = false := getD_ge _ _ (by rw [W_length]; exact h)

theorem W_snoc_getD (gs : List Gate) (g : Gate) (w : List Bool) (t : ℕ) :
    (W (gs ++ [g]) w).getD t false =
      if t = w.length + gs.length then g.op.eval (g.inputs.map fun i => (W gs w).getD i false)
      else (W gs w).getD t false := by
  rw [W_snoc]
  by_cases ht : t = w.length + gs.length
  · rw [if_pos ht, step_last _ _ _ (by rw [W_length]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < w.length + gs.length
    · exact step_lt _ _ _ (by rw [W_length]; exact hlt)
    · rw [getD_ge _ _ (by rw [step_len, W_length]; omega), getD_ge _ _ (by rw [W_length]; omega)]

theorem W_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (W gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (W gs w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [W_cons]
    cases j with
    | zero =>
      have h1 : w.length < (step w g).length := by simp [step]
      rw [Nat.add_zero, W_prefix gs (step w g) w.length h1]
      simp only [List.getElem_cons_zero]
      rw [step_last w g w.length rfl]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, W_prefix gs (step w g) i (by simp [step]; omega)]
        exact (step_lt w g i hi).symm
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (step w g) j hj'
      have hl : (step w g).length = w.length + 1 := step_len w g
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

theorem W_gate_pre (gs pre post : List Gate) (g : Gate) (w : List Bool)
    (h : gs = pre ++ g :: post) :
    (W gs w).getD (w.length + pre.length) false =
      g.op.eval (g.inputs.map fun i => (W pre w).getD i false) := by
  subst h
  rw [W_append, W_cons, W_prefix _ _ _ (by rw [step_len, W_length]; omega)]
  exact step_last _ _ _ (by rw [W_length])

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    (List.ofFn x).getD u false = x ⟨u, hu⟩ := by
  simp [List.getD_eq_getElem?_getD, hu]

theorem ofFn_getD_ge {n : ℕ} (x : Fin n → Bool) (u : ℕ) (hu : n ≤ u) :
    (List.ofFn x).getD u false = false := getD_ge _ _ (by simpa using hu)

theorem split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate), gs = pre ++ gs[j] :: post ∧ pre.length = j := by
  refine ⟨gs.take j, gs.drop (j + 1), ?_, by simp; omega⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

theorem split2 (gs : List Gate) : ∀ (j : ℕ) (g : Gate), gs[j]? = some g →
    ∃ pre post, pre.length = j ∧ gs = pre ++ g :: post ∧ ∀ g2, gs.set j g2 = pre ++ g2 :: post := by
  induction gs with
  | nil => intro j g h; simp at h
  | cons a gs ih =>
    intro j g h
    cases j with
    | zero =>
      have ha : a = g := by simpa using h
      subst ha
      exact ⟨[], gs, rfl, rfl, fun g2 => rfl⟩
    | succ j =>
      have h2 : gs[j]? = some g := by simpa using h
      obtain ⟨pre, post, hl, e1, e2⟩ := ih j g h2
      refine ⟨a :: pre, post, by rw [List.length_cons, hl], ?_, fun g2 => ?_⟩
      · exact congrArg (List.cons a) e1
      · exact congrArg (List.cons a) (e2 g2)

theorem step_congr (P : List Bool) (g1 g2 : Gate)
    (h : g1.op.eval (g1.inputs.map fun i => P.getD i false)
      = g2.op.eval (g2.inputs.map fun i => P.getD i false)) :
    step P g1 = step P g2 := by
  show P ++ [_] = P ++ [_]
  rw [h]

theorem gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

theorem gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

theorem gateAt_ge {C : Circuit} {j : ℕ} (hj : C.gates.length ≤ j) :
    gateAt C j = ⟨GateOp.or, []⟩ := by
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_none hj]

theorem getElem?_gateAt {C : Circuit} {j : ℕ} {g : Gate} (h : C.gates[j]? = some g) :
    gateAt C j = g ∧ j < C.gates.length := by
  have hj : j < C.gates.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; cases h
  refine ⟨?_, hj⟩
  rw [gateAt_eq hj]
  rw [List.getElem?_eq_getElem hj] at h
  exact Option.some.inj h

theorem eval_and_iff (l : List ℕ) (f : ℕ → Bool) :
    GateOp.and.eval (l.map f) = true ↔ ∀ i ∈ l, f i = true := by
  simp [GateOp.eval]

theorem eval_or_iff (l : List ℕ) (f : ℕ → Bool) :
    GateOp.or.eval (l.map f) = true ↔ ∃ i ∈ l, f i = true := by
  simp [GateOp.eval]

theorem eval_and2 (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
  cases a <;> cases b <;> rfl

theorem eval_or2 (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
  cases a <;> cases b <;> rfl

theorem eval_and1 (a : Bool) : GateOp.and.eval [a] = a := by cases a <;> rfl

theorem eval_or1 (a : Bool) : GateOp.or.eval [a] = a := by cases a <;> rfl

-- FRAGMENT mono    DEPENDS: fold
-- Wire values val, gate-by-gate value equations, monotonicity of AND/OR circuits, Monotone2 / IsAO2 facts,
-- minimal true points.
-- Exports:
--   def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false     (val C x u = (W C.gates x).getD u false by rfl)
--   eval_eq_val : C.eval x = val C x C.output ;  circuitFun_val : circuitFun n C x = val C (List.ofFn x) C.output
--   val_input (hx : x.length = n) (hu : u < n) : val C x u = x.getD u false
--   val_ofFn (u : Fin n) : val C (List.ofFn x) u.val = x u ;  val_ofFn_lt (hu : u < n) : val C (List.ofFn x) u = x (u, hu)
--   val_ge (hx : x.length = n) (hu : n + C.gates.length <= u) : val C x u = false
--   val_gate (hx : x.length = n) (hj : j < C.gates.length) :
--       val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => if i < n + j then val C x i else false)
--   val_gate_rb : same, without the if, when every input i of gate j has i < n + j (ReadsBack)
--   val_or  (op = or)  : val C x (n + r) = true iff exists i in inputs, i < n + r and val C x i = true
--   val_and (op = and) : val C x (n + r) = true iff all i in inputs, i < n + r and val C x i = true
--   and_val (IsAO2, op = and) : val C x (n + j) = (val of input 0 && val of input 1)  (inputs.getD 0 0 / getD 1 0)
--   or_val  (IsAO2, op = or)  : val C x (n + j) = (val of input 0 || val of input 1)
--   def OpMono R : AND and OR are monotone for relation R on Bool ;  opMono_eq : OpMono Eq ;  opMono_imp : OpMono (a = true -> b = true)
--   andOrOnly_of_monotone2 : Monotone2 C -> AndOrOnly C ;  andOrOnly_of_isAO2 : IsAO2 n C -> AndOrOnly C
--   mono (AndOrOnly C) (x <= y pointwise) : for all w, val C (ofFn x) w = true -> val C (ofFn y) w = true
--   circuitFun_mono (AndOrOnly C) (x <= y) : circuitFun n C x = true -> circuitFun n C y = true
--   monotone2_len : Monotone2 C -> g in C.gates -> g.inputs.length <= 2 ;  isAO2_len : IsAO2 n C -> g in C.gates -> g.inputs.length = 2
--   isAO2_rb : IsAO2 n C -> j < C.gates.length -> i in (gateAt C j).inputs -> i < n + j
--   def tr y : Finset of true coordinates ;  tr_lt : z < y strictly -> (tr z).card < (tr y).card
--   exists_min F x (F x = true) : exists y <= x, F y = true and every z < y (z <= y, z ne y) has F z = false
-- Use: induction on the wire index w (Nat.strong_induction_on) with val_input / val_ge / val_gate to compare two runs.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

theorem eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

theorem circuitFun_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    circuitFun n C x = val C (List.ofFn x) C.output := rfl

theorem val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := W_prefix _ _ _ (by omega)

theorem val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := W_ge _ _ _ (by omega)

theorem val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact W_gate C.gates x j hj

theorem val_gate_rb {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) (hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => val C x i) := by
  rw [val_gate hx hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [if_pos (hrb i hi)]

theorem val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

theorem val_ofFn_lt {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    val C (List.ofFn x) u = x ⟨u, hu⟩ := val_ofFn C x ⟨u, hu⟩

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

theorem opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

theorem opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

theorem val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

theorem val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2

theorem andOrOnly_of_monotone2 {C : Circuit} (h : Monotone2 C) :
    PEqualNP.EdgeOwnership.AndOrOnly C := by
  intro g hg
  have h1 := (h g hg).1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
  exact h1

theorem andOrOnly_of_isAO2 {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) :
    PEqualNP.EdgeOwnership.AndOrOnly C := h.1

theorem monotone2_len {C : Circuit} (h : Monotone2 C) {g : Gate} (hg : g ∈ C.gates) :
    g.inputs.length ≤ 2 := (h g hg).2

theorem isAO2_len {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) {g : Gate} (hg : g ∈ C.gates) :
    g.inputs.length = 2 := h.2.2 g hg

theorem isAO2_rb {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) {j : ℕ}
    (hj : j < C.gates.length) {i : ℕ} (hi : i ∈ (gateAt C j).inputs) : i < n + j :=
  h.2.1 j hj i hi

theorem mono (n : ℕ) (C : Circuit) (hAO : PEqualNP.EdgeOwnership.AndOrOnly C)
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, x i = true → y i = true) :
    ∀ w : ℕ, val C (List.ofFn x) w = true → val C (List.ofFn y) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · have e1 : val C (List.ofFn x) w = x ⟨w, hw⟩ := val_ofFn C x ⟨w, hw⟩
      have e2 : val C (List.ofFn y) w = y ⟨w, hw⟩ := val_ofFn C y ⟨w, hw⟩
      rw [e2]
      rw [e1] at hv
      exact hxy _ hv
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge (n := n) (by simp) hlen] at hv
        cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        rw [val_gate (n := n) (by simp) hk] at hv ⊢
        have h : ∀ i ∈ (gateAt C k).inputs,
            ((if i < n + k then val C (List.ofFn x) i else false) = true →
              (if i < n + k then val C (List.ofFn y) i else false) = true) := by
          intro i _
          by_cases hi : i < n + k
          · rw [if_pos hi, if_pos hi]
            exact ih i hi
          · rw [if_neg hi, if_neg hi]
            exact id
        exact opMono_imp (gateAt C k).op (hAO _ (gateAt_mem hk)) (gateAt C k).inputs
          (fun i => if i < n + k then val C (List.ofFn x) i else false)
          (fun i => if i < n + k then val C (List.ofFn y) i else false) h hv

theorem circuitFun_mono (n : ℕ) (C : Circuit) (hAO : PEqualNP.EdgeOwnership.AndOrOnly C)
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, x i = true → y i = true)
    (h : circuitFun n C x = true) : circuitFun n C y = true :=
  mono n C hAO x y hxy C.output h

theorem and_val (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) (x : List Bool)
    (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) :
    val C x (n + j) = (val C x ((gateAt C j).inputs.getD 0 0) &&
      val C x ((gateAt C j).inputs.getD 1 0)) := by
  obtain ⟨_, hRB, h2⟩ := hC
  have hlen : (gateAt C j).inputs.length = 2 := h2 _ (gateAt_mem hj)
  have hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j := hRB j hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  rw [val_gate hx hj, hop]
  rw [hab] at hrb ⊢
  have ha : a < n + j := hrb a (by simp)
  have hb : b < n + j := hrb b (by simp)
  simp [GateOp.eval, ha, hb]

theorem or_val (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) (x : List Bool)
    (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) :
    val C x (n + j) = (val C x ((gateAt C j).inputs.getD 0 0) ||
      val C x ((gateAt C j).inputs.getD 1 0)) := by
  obtain ⟨_, hRB, h2⟩ := hC
  have hlen : (gateAt C j).inputs.length = 2 := h2 _ (gateAt_mem hj)
  have hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j := hRB j hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  rw [val_gate hx hj, hop]
  rw [hab] at hrb ⊢
  have ha : a < n + j := hrb a (by simp)
  have hb : b < n + j := hrb b (by simp)
  simp [GateOp.eval, ha, hb]

def tr {n : ℕ} (y : Fin n → Bool) : Finset (Fin n) := Finset.univ.filter (fun i => y i = true)

theorem tr_lt {n : ℕ} (z y : Fin n → Bool) (hzy : ∀ i, z i = true → y i = true) (hne : z ≠ y) :
    (tr z).card < (tr y).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [tr, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hzy i hi
  · intro heq
    apply hne
    funext i
    have h : i ∈ tr z ↔ i ∈ tr y := by rw [heq]
    simp only [tr, Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact Bool.eq_iff_iff.mpr h

theorem exists_min {n : ℕ} (F : (Fin n → Bool) → Bool) (x : Fin n → Bool) (hx : F x = true) :
    ∃ y : Fin n → Bool, (∀ i, y i = true → x i = true) ∧ F y = true ∧
      ∀ z : Fin n → Bool, (∀ i, z i = true → y i = true) → z ≠ y → F z = false := by
  let S : Finset (Fin n → Bool) :=
    Finset.univ.filter (fun y => F y = true ∧ ∀ i, y i = true → x i = true)
  have hS : S.Nonempty := ⟨x, by simp [S, hx]⟩
  obtain ⟨y, hyS, hmin⟩ := Finset.exists_min_image S (fun y => (tr y).card) hS
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hyS
  refine ⟨y, hyS.2, hyS.1, ?_⟩
  intro z hzy hne
  cases hz : F z
  · rfl
  · exfalso
    have hzS : z ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hz, fun i hi => hyS.2 i (hzy i hi)⟩
    have h1 := hmin z hzS
    have h2 := tr_lt z y hzy hne
    omega

-- FRAGMENT table1a    DEPENDS: fold mono
-- Table 1a rows: RepSizeAtMost (fun u v : Fin 4 => M.testBit (4 * u.val + v.val)) s, upper and lower bounds.
-- Profiles: the profile of a wire is the 16-bit Nat whose bit k is its value at input t1_inp k = oneEach (k / 4) (k % 4).
-- Every gate of a Monotone2 circuit has profile a AND b or a OR b of earlier profiles or the constants 0 and 65535,
-- so a circuit of at most s gates gives a chain of s such steps from t1_base reaching the target T; t1_reach
-- (a Bool search, evaluated by decide +kernel) checks that no such chain exists.
-- Exports:
--   def t1_bits (f : Nat -> Bool) (m) : Nat  (bit k is f k for k < m) ;  t1_bits_testBit : testBit (t1_bits f m) i = (decide (i < m) and f i)
--   t1_bits_ext (agree below m) ;  t1_bits_and / t1_bits_or : t1_bits of pointwise and / or = land / lor ;  t1_bits_false : t1_bits (fun _ => false) m = 0
--   def t1_inp k : List Bool := oneEach (k / 4 % 4) (k % 4) ;  t1_inp_len : (t1_inp k).length = 8
--   def t1_prof C w := t1_bits (fun k => val C (t1_inp k) w) 16 ;  def t1_base : the 10 base profiles (0, 65535, 4 rows, 4 columns)
--   def t1_St C j : t1_base with the profiles of gate wires 8 .. 8 + j - 1 pushed in front ;  def t1_Step S p : exists a b in S, p = a land b or p = a lor b
--   t1_St_prof : i < 8 + j -> t1_prof C i in t1_St C j ;  t1_gate_step : one AND / OR gate of fan-in at most 2 is a t1_Step
--   def t1_mem, t1_pany (pairs a b with a before or equal b), t1_one T S (T is one step from S), t1_ext (two-step test with U = S below T, D = S above T)
--   def t1_reach T r S : Bool search (fresh steps only; at 2 steps left the new profile must be comparable with T)
--   def t1_G T r S (T within r steps) ;  t1_Gf (fresh steps) ;  t1_G_Gf, t1_Gf_le ;  t1_reach_sound : t1_Gf T r S -> t1_reach T r S = true
--   t1_chain : a chain of steps gives t1_G ;  t1_proj_and / t1_proj_or : projection by land Q commutes with the steps
--   t1_lower M s T Q L (hT : t1_bits (fun k => M.testBit k) 16 land Q = T) (hL : t1_base.map (fun x => x land Q) = L)
--       (hc : t1_reach T s L = false) : not RepSizeAtMost (fun u v : Fin 4 => M.testBit (4 * u.val + v.val)) s   (Q = 65535: no projection)
--   def t1_okop ;  t1_mono2 (h : C.gates.all (fun g => t1_okop g.op and decide (g.inputs.length <= 2)) = true) : Monotone2 C
-- Use: SP/tools/table1a.py N writes whole files. Kernel cost: lower bound with 3 gates about 10 s, with 4 gates about 50 s;
-- 5 or more gates is out of reach for this search (about 30x more per extra gate).

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def t1_bits (f : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | m + 1 => Nat.bit (f 0) (t1_bits (fun i => f (i + 1)) m)

theorem t1_bits_testBit (m : ℕ) : ∀ (f : ℕ → Bool) (i : ℕ),
    (t1_bits f m).testBit i = (decide (i < m) && f i) := by
  induction m with
  | zero => intro f i; simp [t1_bits]
  | succ m ih =>
    intro f i
    cases i with
    | zero => simp [t1_bits, Nat.testBit_bit_zero]
    | succ i =>
      have e : (t1_bits f (m + 1)).testBit (i + 1) = (t1_bits (fun i => f (i + 1)) m).testBit i :=
        Nat.testBit_bit_succ i _ _
      rw [e, ih]
      simp

theorem t1_bits_ext {f g : ℕ → Bool} {m : ℕ} (h : ∀ k, k < m → f k = g k) :
    t1_bits f m = t1_bits g m := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [t1_bits_testBit, t1_bits_testBit]
  by_cases hi : i < m
  · rw [h i hi]
  · simp [hi]

theorem t1_bits_and (f g : ℕ → Bool) (m : ℕ) :
    t1_bits (fun i => f i && g i) m = t1_bits f m &&& t1_bits g m := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_land, t1_bits_testBit]
  cases (decide (i < m)) <;> cases (f i) <;> cases (g i) <;> rfl

theorem t1_bits_or (f g : ℕ → Bool) (m : ℕ) :
    t1_bits (fun i => f i || g i) m = t1_bits f m ||| t1_bits g m := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_lor, t1_bits_testBit]
  cases (decide (i < m)) <;> cases (f i) <;> cases (g i) <;> rfl

theorem t1_bits_false (m : ℕ) : t1_bits (fun _ => false) m = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp [t1_bits_testBit]

theorem t1_bits_true16 : t1_bits (fun _ => true) 16 = 65535 := by decide

theorem t1_land_comm (a b : ℕ) : a &&& b = b &&& a := by
  apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_land]
  cases a.testBit i <;> cases b.testBit i <;> rfl

theorem t1_lor_comm (a b : ℕ) : a ||| b = b ||| a := by
  apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_lor]
  cases a.testBit i <;> cases b.testBit i <;> rfl

theorem t1_land_absl (a b : ℕ) : a &&& (a &&& b) = a &&& b := by
  apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_land]
  cases a.testBit i <;> cases b.testBit i <;> rfl

theorem t1_land_absr (a b : ℕ) : b &&& (a &&& b) = a &&& b := by
  apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_land]
  cases a.testBit i <;> cases b.testBit i <;> rfl

theorem t1_lor_absl (a b : ℕ) : a ||| (a ||| b) = a ||| b := by
  apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_lor]
  cases a.testBit i <;> cases b.testBit i <;> rfl

theorem t1_lor_absr (a b : ℕ) : b ||| (a ||| b) = a ||| b := by
  apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_lor]
  cases a.testBit i <;> cases b.testBit i <;> rfl

def t1_inp (k : ℕ) : List Bool :=
  PEqualNP.Represents.oneEach (n := 4) (m := 4) ⟨k / 4 % 4, by omega⟩ ⟨k % 4, by omega⟩

theorem t1_inp_len (k : ℕ) : (t1_inp k).length = 8 := by
  simp [t1_inp, PEqualNP.Represents.oneEach]

def t1_prof (C : Circuit) (w : ℕ) : ℕ := t1_bits (fun k => val C (t1_inp k) w) 16

def t1_base : List ℕ := [0, 65535, 15, 240, 3840, 61440, 4369, 8738, 17476, 34952]

theorem t1_base_ok : ∀ u, u < 8 → t1_bits (fun k => (t1_inp k).getD u false) 16 ∈ t1_base := by
  decide +kernel

def t1_St (C : Circuit) : ℕ → List ℕ
  | 0 => t1_base
  | j + 1 => t1_prof C (8 + j) :: t1_St C j

def t1_Step (S : List ℕ) (p : ℕ) : Prop := ∃ a ∈ S, ∃ b ∈ S, p = a &&& b ∨ p = a ||| b

theorem t1_St_base (C : Circuit) {x : ℕ} (hx : x ∈ t1_base) (j : ℕ) : x ∈ t1_St C j := by
  induction j with
  | zero => exact hx
  | succ j ih => exact List.mem_cons_of_mem _ ih

theorem t1_St_prof (C : Circuit) (j : ℕ) : ∀ i, i < 8 + j → t1_prof C i ∈ t1_St C j := by
  induction j with
  | zero =>
    intro i hi
    have e : t1_prof C i = t1_bits (fun k => (t1_inp k).getD i false) 16 := by
      unfold t1_prof
      congr 1
      funext k
      exact val_input (t1_inp_len k) (by omega)
    rw [e]
    exact t1_base_ok i (by omega)
  | succ j ih =>
    intro i hi
    by_cases h : i < 8 + j
    · exact List.mem_cons_of_mem _ (ih i h)
    · have e : i = 8 + j := by omega
      subst e
      simp [t1_St]

theorem t1_gate_step (S : List ℕ) (R : ℕ → ℕ → Bool) (op : GateOp) (l : List ℕ)
    (hop : op = GateOp.and ∨ op = GateOp.or) (hl : l.length ≤ 2)
    (hR : ∀ i ∈ l, t1_bits (fun k => R k i) 16 ∈ S) (h0 : 0 ∈ S) (h1 : 65535 ∈ S) :
    t1_Step S (t1_bits (fun k => op.eval (l.map (R k))) 16) := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · rcases hop with rfl | rfl
    · have e : (fun k => GateOp.and.eval (([] : List ℕ).map (R k))) = fun _ => true := by
        funext k; simp [GateOp.eval]
      rw [e, t1_bits_true16]
      exact ⟨65535, h1, 65535, h1, Or.inl (by decide)⟩
    · have e : (fun k => GateOp.or.eval (([] : List ℕ).map (R k))) = fun _ => false := by
        funext k; simp [GateOp.eval]
      rw [e, t1_bits_false]
      exact ⟨0, h0, 0, h0, Or.inr (by decide)⟩
  · have ha := hR a (by simp)
    rcases hop with rfl | rfl
    · have e : (fun k => GateOp.and.eval ([a].map (R k))) = fun k => R k a && true := by
        funext k; simp [GateOp.eval]
      rw [e, t1_bits_and, t1_bits_true16]
      exact ⟨_, ha, 65535, h1, Or.inl rfl⟩
    · have e : (fun k => GateOp.or.eval ([a].map (R k))) = fun k => R k a || false := by
        funext k; simp [GateOp.eval]
      rw [e, t1_bits_or, t1_bits_false]
      exact ⟨_, ha, 0, h0, Or.inr rfl⟩
  · have ha := hR a (by simp)
    have hb := hR b (by simp)
    rcases hop with rfl | rfl
    · have e : (fun k => GateOp.and.eval ([a, b].map (R k))) = fun k => R k a && R k b := by
        funext k; simp [GateOp.eval]
      rw [e, t1_bits_and]
      exact ⟨_, ha, _, hb, Or.inl rfl⟩
    · have e : (fun k => GateOp.or.eval ([a, b].map (R k))) = fun k => R k a || R k b := by
        funext k; simp [GateOp.eval]
      rw [e, t1_bits_or]
      exact ⟨_, ha, _, hb, Or.inr rfl⟩
  · simp only [List.length_cons] at hl
    omega

def t1_mem (T : ℕ) : List ℕ → Bool
  | [] => false
  | a :: l => (a == T) || t1_mem T l

theorem t1_mem_of (T : ℕ) (l : List ℕ) (h : T ∈ l) : t1_mem T l = true := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    rcases List.mem_cons.mp h with h | h
    · subst h; simp [t1_mem]
    · simp [t1_mem, ih h]

def t1_pany (f : ℕ → ℕ → Bool) : List ℕ → Bool
  | [] => false
  | a :: l => (a :: l).any (f a) || t1_pany f l

theorem t1_pany_of (f : ℕ → ℕ → Bool) (hsym : ∀ a b, f a b = f b a) (l : List ℕ) (a b : ℕ)
    (ha : a ∈ l) (hb : b ∈ l) (h : f a b = true) : t1_pany f l = true := by
  induction l with
  | nil => simp at ha
  | cons x l ih =>
    simp only [t1_pany, Bool.or_eq_true, List.any_eq_true]
    rcases List.mem_cons.mp ha with ha' | ha'
    · subst ha'
      exact Or.inl ⟨b, hb, h⟩
    · rcases List.mem_cons.mp hb with hb' | hb'
      · subst hb'
        exact Or.inl ⟨a, List.mem_cons_of_mem _ ha', by rw [hsym]; exact h⟩
      · exact Or.inr (ih ha' hb')

def t1_one (T : ℕ) (S : List ℕ) : Bool :=
  t1_pany (fun a b => a ||| b == T) (S.filter (fun a => a ||| T == T)) ||
  t1_pany (fun a b => a &&& b == T) (S.filter (fun a => a &&& T == T))

theorem t1_one_of (T : ℕ) (S : List ℕ) (a b : ℕ) (ha : a ∈ S) (hb : b ∈ S)
    (h : a &&& b = T ∨ a ||| b = T) : t1_one T S = true := by
  unfold t1_one
  rw [Bool.or_eq_true]
  rcases h with h | h
  · right
    have hsym : ∀ x y, (fun a b => a &&& b == T) x y = (fun a b => a &&& b == T) y x := by
      intro x y; show (x &&& y == T) = (y &&& x == T); rw [t1_land_comm]
    exact t1_pany_of _ hsym _ a b
      (List.mem_filter.mpr ⟨ha, by rw [← h, t1_land_absl]; exact beq_self_eq_true _⟩)
      (List.mem_filter.mpr ⟨hb, by rw [← h, t1_land_absr]; exact beq_self_eq_true _⟩)
      (by simp [h])
  · left
    have hsym : ∀ x y, (fun a b => a ||| b == T) x y = (fun a b => a ||| b == T) y x := by
      intro x y; show (x ||| y == T) = (y ||| x == T); rw [t1_lor_comm]
    exact t1_pany_of _ hsym _ a b
      (List.mem_filter.mpr ⟨ha, by rw [← h, t1_lor_absl]; exact beq_self_eq_true _⟩)
      (List.mem_filter.mpr ⟨hb, by rw [← h, t1_lor_absr]; exact beq_self_eq_true _⟩)
      (by simp [h])

def t1_ext (T : ℕ) (U D : List ℕ) (p : ℕ) : Bool :=
  ((p ||| T == T) && ((p == T) || U.any (fun q => p ||| q == T))) ||
  ((p &&& T == T) && ((p == T) || D.any (fun q => p &&& q == T)))

def t1_reach (T : ℕ) : ℕ → List ℕ → Bool
  | 0, S => t1_mem T S
  | 1, S => t1_mem T S || t1_one T S
  | 2, S => t1_mem T S || t1_one T S || t1_pany (fun a b =>
      t1_ext T (S.filter (fun x => x ||| T == T)) (S.filter (fun x => x &&& T == T)) (a &&& b) ||
      t1_ext T (S.filter (fun x => x ||| T == T)) (S.filter (fun x => x &&& T == T)) (a ||| b)) S
  | r + 3, S => t1_mem T S || t1_pany (fun a b =>
      (!t1_mem (a &&& b) S && t1_reach T (r + 2) ((a &&& b) :: S)) ||
      (!t1_mem (a ||| b) S && t1_reach T (r + 2) ((a ||| b) :: S))) S

theorem t1_reach_zero (T : ℕ) (S : List ℕ) : t1_reach T 0 S = t1_mem T S := rfl

theorem t1_reach_one (T : ℕ) (S : List ℕ) : t1_reach T 1 S = (t1_mem T S || t1_one T S) := rfl

theorem t1_reach_two (T : ℕ) (S : List ℕ) : t1_reach T 2 S = (t1_mem T S || t1_one T S || t1_pany
    (fun a b => t1_ext T (S.filter (fun x => x ||| T == T)) (S.filter (fun x => x &&& T == T)) (a &&& b) ||
      t1_ext T (S.filter (fun x => x ||| T == T)) (S.filter (fun x => x &&& T == T)) (a ||| b)) S) := rfl

theorem t1_reach_three (T r : ℕ) (S : List ℕ) : t1_reach T (r + 3) S = (t1_mem T S || t1_pany
    (fun a b => (!t1_mem (a &&& b) S && t1_reach T (r + 2) ((a &&& b) :: S)) ||
      (!t1_mem (a ||| b) S && t1_reach T (r + 2) ((a ||| b) :: S))) S) := rfl

def t1_G (T : ℕ) : ℕ → List ℕ → Prop
  | 0, S => T ∈ S
  | r + 1, S => T ∈ S ∨ ∃ a ∈ S, ∃ b ∈ S, ∃ p, (p = a &&& b ∨ p = a ||| b) ∧ t1_G T r (p :: S)

def t1_Gf (T : ℕ) : ℕ → List ℕ → Prop
  | 0, S => T ∈ S
  | r + 1, S => T ∈ S ∨ ∃ a ∈ S, ∃ b ∈ S, ∃ p, (p = a &&& b ∨ p = a ||| b) ∧ p ∉ S ∧
      t1_Gf T r (p :: S)

theorem t1_mem_true (T : ℕ) (l : List ℕ) (h : t1_mem T l = true) : T ∈ l := by
  induction l with
  | nil => simp [t1_mem] at h
  | cons a l ih =>
    simp only [t1_mem, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h
    · subst h; simp
    · exact List.mem_cons_of_mem _ (ih h)

theorem t1_mem_false (T : ℕ) (l : List ℕ) (h : T ∉ l) : t1_mem T l = false := by
  cases hm : t1_mem T l
  · rfl
  · exact absurd (t1_mem_true T l hm) h

theorem t1_G_sub (T r : ℕ) : ∀ S S' : List ℕ, (∀ x ∈ S, x ∈ S') → t1_G T r S → t1_G T r S' := by
  induction r with
  | zero => intro S S' hs h; exact hs _ h
  | succ r ih =>
    intro S S' hs h
    rcases h with h | ⟨a, ha, b, hb, p, hp, hg⟩
    · exact Or.inl (hs _ h)
    · refine Or.inr ⟨a, hs _ ha, b, hs _ hb, p, hp, ih (p :: S) (p :: S') ?_ hg⟩
      intro x hx
      simp only [List.mem_cons] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (hs _ hx)

theorem t1_Gf_succ (T r : ℕ) : ∀ S : List ℕ, t1_Gf T r S → t1_Gf T (r + 1) S := by
  induction r with
  | zero => intro S h; exact Or.inl h
  | succ r ih =>
    intro S h
    rcases h with h | ⟨a, ha, b, hb, p, hp, hn, hg⟩
    · exact Or.inl h
    · exact Or.inr ⟨a, ha, b, hb, p, hp, hn, ih _ hg⟩

theorem t1_Gf_le (T r : ℕ) (S : List ℕ) (h : t1_Gf T r S) : ∀ k, t1_Gf T (r + k) S := by
  intro k
  induction k with
  | zero => exact h
  | succ k ih => exact t1_Gf_succ T (r + k) S ih

theorem t1_G_Gf (T r : ℕ) : ∀ S : List ℕ, t1_G T r S → t1_Gf T r S := by
  induction r with
  | zero => intro S h; exact h
  | succ r ih =>
    intro S h
    rcases h with h | ⟨a, ha, b, hb, p, hp, hg⟩
    · exact Or.inl h
    · by_cases hpS : p ∈ S
      · apply t1_Gf_succ T r S
        apply ih S
        apply t1_G_sub T r (p :: S) S _ hg
        intro x hx
        rcases List.mem_cons.mp hx with hx | hx
        · rw [hx]; exact hpS
        · exact hx
      · exact Or.inr ⟨a, ha, b, hb, p, hp, hpS, ih _ hg⟩

theorem t1_lor_self (a : ℕ) : a ||| a = a := by
  apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_lor]
  cases a.testBit i <;> rfl

theorem t1_land_self (a : ℕ) : a &&& a = a := by
  apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_land]
  cases a.testBit i <;> rfl

theorem t1_ext_of (T p q : ℕ) (S : List ℕ) (h : p ||| q = T ∨ p &&& q = T) (hq : q = p ∨ q ∈ S) :
    t1_ext T (S.filter (fun x => x ||| T == T)) (S.filter (fun x => x &&& T == T)) p = true := by
  unfold t1_ext
  rw [Bool.or_eq_true]
  rcases h with h | h
  · left
    rw [Bool.and_eq_true]
    constructor
    · rw [← h, t1_lor_absl]; exact beq_self_eq_true _
    · rw [Bool.or_eq_true]
      rcases hq with hq | hq
      · left
        rw [hq, t1_lor_self] at h
        rw [h]; exact beq_self_eq_true _
      · right
        rw [List.any_eq_true]
        refine ⟨q, List.mem_filter.mpr ⟨hq, ?_⟩, ?_⟩
        · show (q ||| T == T) = true
          rw [← h, t1_lor_absr]; exact beq_self_eq_true _
        · show (p ||| q == T) = true
          rw [h]; exact beq_self_eq_true _
  · right
    rw [Bool.and_eq_true]
    constructor
    · rw [← h, t1_land_absl]; exact beq_self_eq_true _
    · rw [Bool.or_eq_true]
      rcases hq with hq | hq
      · left
        rw [hq, t1_land_self] at h
        rw [h]; exact beq_self_eq_true _
      · right
        rw [List.any_eq_true]
        refine ⟨q, List.mem_filter.mpr ⟨hq, ?_⟩, ?_⟩
        · show (q &&& T == T) = true
          rw [← h, t1_land_absr]; exact beq_self_eq_true _
        · show (p &&& q == T) = true
          rw [h]; exact beq_self_eq_true _

theorem t1_two_aux (T p : ℕ) (S : List ℕ) (c d : ℕ) (hc : c ∈ p :: S) (hd : d ∈ p :: S)
    (hq : T = c &&& d ∨ T = c ||| d) :
    t1_one T S = true ∨
      t1_ext T (S.filter (fun x => x ||| T == T)) (S.filter (fun x => x &&& T == T)) p = true := by
  by_cases hcS : c ∈ S
  · by_cases hdS : d ∈ S
    · left
      apply t1_one_of T S c d hcS hdS
      rcases hq with hq | hq
      · exact Or.inl hq.symm
      · exact Or.inr hq.symm
    · have e : d = p := by
        rcases List.mem_cons.mp hd with h | h
        · exact h
        · exact absurd h hdS
      right
      apply t1_ext_of T p c S _ (Or.inr hcS)
      rcases hq with hq | hq
      · right; rw [hq, e, t1_land_comm]
      · left; rw [hq, e, t1_lor_comm]
  · have e : c = p := by
      rcases List.mem_cons.mp hc with h | h
      · exact h
      · exact absurd h hcS
    right
    apply t1_ext_of T p d S _ (List.mem_cons.mp hd)
    rcases hq with hq | hq
    · right; rw [hq, e]
    · left; rw [hq, e]

theorem t1_reach_sound (T : ℕ) : ∀ (r : ℕ) (S : List ℕ), t1_Gf T r S → t1_reach T r S = true
  | 0, S, h => t1_mem_of T S h
  | 1, S, h => by
    rw [t1_reach_one, Bool.or_eq_true]
    rcases h with h | ⟨a, ha, b, hb, p, hp, -, hT⟩
    · exact Or.inl (t1_mem_of T S h)
    · have hT' : T ∈ p :: S := hT
      rcases List.mem_cons.mp hT' with hT' | hT'
      · right
        apply t1_one_of T S a b ha hb
        rcases hp with hp | hp
        · exact Or.inl (hp.symm.trans hT'.symm)
        · exact Or.inr (hp.symm.trans hT'.symm)
      · exact Or.inl (t1_mem_of T S hT')
  | 2, S, h => by
    rw [t1_reach_two, Bool.or_eq_true, Bool.or_eq_true]
    rcases h with h | ⟨a, ha, b, hb, p, hp, -, h1⟩
    · exact Or.inl (Or.inl (t1_mem_of T S h))
    · have hab : T = p → t1_one T S = true := by
        intro hTp
        apply t1_one_of T S a b ha hb
        rcases hp with hp | hp
        · exact Or.inl (hp.symm.trans hTp.symm)
        · exact Or.inr (hp.symm.trans hTp.symm)
      rcases h1 with h1 | ⟨c, hc, d, hd, q, hq, -, h0⟩
      · have h1' : T ∈ p :: S := h1
        rcases List.mem_cons.mp h1' with e | e
        · exact Or.inl (Or.inr (hab e))
        · exact Or.inl (Or.inl (t1_mem_of T S e))
      · have h0' : T ∈ q :: p :: S := h0
        rcases List.mem_cons.mp h0' with e | e
        · have hq' : T = c &&& d ∨ T = c ||| d := by
            rcases hq with hq | hq
            · exact Or.inl (e.trans hq)
            · exact Or.inr (e.trans hq)
          rcases t1_two_aux T p S c d hc hd hq' with h2 | h2
          · exact Or.inl (Or.inr h2)
          · right
            have hsym : ∀ x y,
                (fun a b => t1_ext T (S.filter (fun x => x ||| T == T)) (S.filter (fun x => x &&& T == T)) (a &&& b) ||
                  t1_ext T (S.filter (fun x => x ||| T == T)) (S.filter (fun x => x &&& T == T)) (a ||| b)) x y =
                (fun a b => t1_ext T (S.filter (fun x => x ||| T == T)) (S.filter (fun x => x &&& T == T)) (a &&& b) ||
                  t1_ext T (S.filter (fun x => x ||| T == T)) (S.filter (fun x => x &&& T == T)) (a ||| b)) y x := by
              intro x y
              show (t1_ext T (S.filter (fun x => x ||| T == T)) (S.filter (fun x => x &&& T == T)) (x &&& y) ||
                  t1_ext T (S.filter (fun x => x ||| T == T)) (S.filter (fun x => x &&& T == T)) (x ||| y)) =
                (t1_ext T (S.filter (fun x => x ||| T == T)) (S.filter (fun x => x &&& T == T)) (y &&& x) ||
                  t1_ext T (S.filter (fun x => x ||| T == T)) (S.filter (fun x => x &&& T == T)) (y ||| x))
              rw [t1_land_comm x y, t1_lor_comm x y]
            refine t1_pany_of _ hsym S a b ha hb ?_
            rcases hp with hp | hp
            · subst hp; simp [h2]
            · subst hp; simp [h2]
        · rcases List.mem_cons.mp e with e | e
          · exact Or.inl (Or.inr (hab e))
          · exact Or.inl (Or.inl (t1_mem_of T S e))
  | r + 3, S, h => by
    rw [t1_reach_three, Bool.or_eq_true]
    rcases h with h | ⟨a, ha, b, hb, p, hp, hpS, h1⟩
    · exact Or.inl (t1_mem_of T S h)
    · right
      have hr := t1_reach_sound T (r + 2) (p :: S) h1
      have hm := t1_mem_false p S hpS
      have hsym : ∀ x y,
          (fun a b => (!t1_mem (a &&& b) S && t1_reach T (r + 2) ((a &&& b) :: S)) ||
            (!t1_mem (a ||| b) S && t1_reach T (r + 2) ((a ||| b) :: S))) x y =
          (fun a b => (!t1_mem (a &&& b) S && t1_reach T (r + 2) ((a &&& b) :: S)) ||
            (!t1_mem (a ||| b) S && t1_reach T (r + 2) ((a ||| b) :: S))) y x := by
        intro x y
        show ((!t1_mem (x &&& y) S && t1_reach T (r + 2) ((x &&& y) :: S)) ||
            (!t1_mem (x ||| y) S && t1_reach T (r + 2) ((x ||| y) :: S))) =
          ((!t1_mem (y &&& x) S && t1_reach T (r + 2) ((y &&& x) :: S)) ||
            (!t1_mem (y ||| x) S && t1_reach T (r + 2) ((y ||| x) :: S)))
        rw [t1_land_comm x y, t1_lor_comm x y]
      refine t1_pany_of _ hsym S a b ha hb ?_
      rcases hp with hp | hp
      · subst hp; simp [hr, hm]
      · subst hp; simp [hr, hm]

theorem t1_proj_and (a b Q : ℕ) : (a &&& b) &&& Q = (a &&& Q) &&& (b &&& Q) := by
  apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_land]
  cases a.testBit i <;> cases b.testBit i <;> cases Q.testBit i <;> rfl

theorem t1_proj_or (a b Q : ℕ) : (a ||| b) &&& Q = (a &&& Q) ||| (b &&& Q) := by
  apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_land, Nat.testBit_lor]
  cases a.testBit i <;> cases b.testBit i <;> cases Q.testBit i <;> rfl

theorem t1_chain (T : ℕ) (St : ℕ → List ℕ) (P : ℕ → ℕ) (len : ℕ)
    (hst : ∀ j, j < len → St (j + 1) = P j :: St j ∧ t1_Step (St j) (P j))
    (hT : T ∈ St len) : ∀ d j, j + d = len → t1_G T d (St j) := by
  intro d
  induction d with
  | zero =>
    intro j hj
    have e : j = len := by omega
    subst e
    exact hT
  | succ d ih =>
    intro j hj
    obtain ⟨hs, a, ha, b, hb, hp⟩ := hst j (by omega)
    have h := ih (j + 1) (by omega)
    rw [hs] at h
    exact Or.inr ⟨a, ha, b, hb, P j, hp, h⟩

theorem t1_lower (M s T Q : ℕ) (L : List ℕ) (hT : t1_bits (fun k => M.testBit k) 16 &&& Q = T)
    (hL : t1_base.map (fun x => x &&& Q) = L) (hc : t1_reach T s L = false) :
    ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => M.testBit (4 * u.val + v.val)) s := by
  rintro ⟨C, hm, hs, hr⟩
  have hlen : C.gates.length ≤ s := hs
  have h0 : (0 : ℕ) ∈ t1_base := by decide
  have h1 : (65535 : ℕ) ∈ t1_base := by decide
  have hstep : ∀ j, j < C.gates.length → t1_St C (j + 1) = t1_prof C (8 + j) :: t1_St C j ∧
      t1_Step (t1_St C j) (t1_prof C (8 + j)) := by
    intro j hj
    refine ⟨rfl, ?_⟩
    have hg := hm _ (gateAt_mem hj)
    have hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by simpa using hg.1
    have e : t1_prof C (8 + j) = t1_bits (fun k => (gateAt C j).op.eval ((gateAt C j).inputs.map
        (fun i => if i < 8 + j then val C (t1_inp k) i else false))) 16 := by
      unfold t1_prof
      congr 1
      funext k
      exact val_gate (t1_inp_len k) hj
    rw [e]
    apply t1_gate_step _ (fun k i => if i < 8 + j then val C (t1_inp k) i else false) _ _ hop hg.2
    · intro i _
      by_cases hi : i < 8 + j
      · simp only [hi, ↓reduceIte]
        exact t1_St_prof C j i hi
      · simp only [hi, ↓reduceIte]
        rw [t1_bits_false]
        exact t1_St_base C h0 j
    · exact t1_St_base C h0 j
    · exact t1_St_base C h1 j
  have hout : t1_prof C C.output ∈ t1_St C C.gates.length := by
    by_cases ho : C.output < 8 + C.gates.length
    · exact t1_St_prof C _ _ ho
    · have e : (fun k => val C (t1_inp k) C.output) = fun _ => false :=
        funext fun k => val_ge (t1_inp_len k) (by omega)
      have e2 : t1_prof C C.output = 0 := by
        unfold t1_prof; rw [e, t1_bits_false]
      rw [e2]
      exact t1_St_base C h0 _
  have htarget : t1_prof C C.output = t1_bits (fun k => M.testBit k) 16 := by
    unfold t1_prof
    apply t1_bits_ext
    intro k hk
    have h : C.eval (t1_inp k) = M.testBit (4 * (k / 4 % 4) + k % 4) :=
      hr ⟨k / 4 % 4, by omega⟩ ⟨k % 4, by omega⟩
    have e : 4 * (k / 4 % 4) + k % 4 = k := by omega
    rw [e] at h
    exact h
  have hst2 : ∀ j, j < C.gates.length → (t1_St C (j + 1)).map (fun x => x &&& Q) =
      (t1_prof C (8 + j) &&& Q) :: (t1_St C j).map (fun x => x &&& Q) ∧
      t1_Step ((t1_St C j).map (fun x => x &&& Q)) (t1_prof C (8 + j) &&& Q) := by
    intro j hj
    obtain ⟨e, a, ha, b, hb, hp⟩ := hstep j hj
    refine ⟨by simp only [e, List.map_cons], a &&& Q, List.mem_map.mpr ⟨a, ha, rfl⟩,
      b &&& Q, List.mem_map.mpr ⟨b, hb, rfl⟩, ?_⟩
    rcases hp with hp | hp
    · left; rw [hp, t1_proj_and]
    · right; rw [hp, t1_proj_or]
  have hout2 : T ∈ (t1_St C C.gates.length).map (fun x => x &&& Q) :=
    List.mem_map.mpr ⟨t1_prof C C.output, hout, by
      show t1_prof C C.output &&& Q = T
      rw [htarget, hT]⟩
  have hG := t1_chain T (fun j => (t1_St C j).map (fun x => x &&& Q))
    (fun j => t1_prof C (8 + j) &&& Q) C.gates.length hst2 hout2 C.gates.length 0 (by omega)
  have hGf := t1_Gf_le T _ _ (t1_G_Gf T _ _ hG) (s - C.gates.length)
  rw [show C.gates.length + (s - C.gates.length) = s by omega] at hGf
  have h2 := t1_reach_sound T s _ hGf
  have h3 : t1_reach T s (t1_base.map (fun x => x &&& Q)) = true := h2
  rw [hL, hc] at h3
  exact Bool.false_ne_true h3

def t1_okop : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | GateOp.not => false
  | GateOp.mod _ => false
  | GateOp.maj => false

theorem t1_mono2 (C : Circuit)
    (h : C.gates.all (fun g => t1_okop g.op && decide (g.inputs.length ≤ 2)) = true) :
    Monotone2 C := by
  intro g hg
  have h2 := List.all_eq_true.mp h g hg
  rcases g with ⟨op, ins⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
  refine ⟨?_, h2.2⟩
  have h3 := h2.1
  cases op <;> simp [t1_okop] at h3 ⊢

-- FRAGMENT bitmask    DEPENDS: fold
-- Truth tables of explicit circuits as Nat bitmasks: bit m of the mask of a wire is its value on the
-- input numbered m (input wire i reads bit i of m). AND, OR and NOT gates (any fan-in); MOD and MAJ unsupported.
-- Exports:
--   def bm_op K op l : mask of a gate from input masks (AND: foldr land (2^K - 1), OR: foldr lor 0, NOT: xor (2^K - 1) (head))
--   def bm_okop op : Bool (true for and, or, not) ;  def bm_ok C : Bool := C.gates.all (bm_okop of op)
--   def bm_step K m g := m ++ [bm_op K g.op (masks of g.inputs)] ;  def bm_W K gs m := gs.foldl (bm_step K) m
--   bm_step_len, bm_step_lt, bm_step_last : as step_len / step_lt / step_last for masks (default 0)
--   bm_op_bit (k < K) (bm_okop op) (fw i = testBit (fm i) k) : testBit (bm_op K op (l.map fm)) k = op.eval (l.map fw)
--   def bm_Rep k w m : w.length = m.length and every w.getD t false = testBit (m.getD t 0) k
--   bm_rep_step, bm_rep_fold (k < K, all ops ok) : bm_Rep k w m -> bm_Rep k (W gs w) (bm_W K gs m)
--   def bm_num : List Bool -> Nat (low bit first) ;  bm_num_lt : bm_num l < 2 ^ l.length
--   bm_num_bit : testBit (bm_num l) i = l.getD i false ;  bm_num_append : bm_num (a ++ b) = bm_num a + 2 ^ a.length * bm_num b
--   def bm_tab p n : mask over 2^n inputs of input wire p ;  bm_tab_spec p m : bm_tab p m < 2^2^m and for k < 2^m, testBit (bm_tab p m) k = testBit k p
--   def bm_init n := (List.range n).map (bm_tab . n) ;  bm_init_len ;  bm_rep_init (x.length = n) : bm_Rep (bm_num x) x (bm_init n)
--   def bm_out n C := (bm_W (2^n) C.gates (bm_init n)).getD C.output 0      (the output mask, computable by decide)
--   bm_eval (bm_ok C) (x.length = n) : C.eval x = testBit (bm_out n C) (bm_num x)
--   def bm_code (x : Fin n -> Bool) := bm_num (List.ofFn x) ;  bm_code_lt : bm_code x < 2 ^ n
--   def bm_input n m : Fin n -> Bool := fun i => testBit m i
--   bm_input_code : bm_input n (bm_code x) = x ;  bm_code_input (m < 2^n) : bm_code (bm_input n m) = m
--   bm_circuitFun (bm_ok C) : circuitFun n C x = testBit (bm_out n C) (bm_code x)
--   bm_circuitFun_num (bm_ok C) (m < 2^n) : circuitFun n C (bm_input n m) = testBit (bm_out n C) m
--   bm_forall_iff : (forall x, P x) iff forall m, m < 2^n -> P (bm_input n m) ;  bm_exists_iff : same for exists (m < 2^n and P ..)
--   bm_fun_eq (bm_ok C) f (h : forall m, m < 2^n -> testBit (bm_out n C) m = f (bm_input n m)) : forall x, circuitFun n C x = f x
--   bm_eval_two (bm_ok C) x y : C.eval (ofFn x ++ ofFn y) = testBit (bm_out (n1 + n2) C) (bm_code x + 2 ^ n1 * bm_code y)
--   bm_fun_eq2 (bm_ok C) f (h : forall a < 2^n1, forall b < 2^n2, testBit (bm_out (n1+n2) C) (a + 2^n1 * b) = f (bm_input n1 a) (bm_input n2 b))
--       : forall x y, C.eval (ofFn x ++ ofFn y) = f x y
-- Use: theorem t : forall x : Fin 3 -> Bool, circuitFun 3 C x = f x := bm_fun_eq 3 C (by decide) _ (by decide +kernel)
--   (C the explicit circuit, f the Boolean formula in x). Other shapes: rw [bm_circuitFun_num n C (by decide) m hm] or
--   rw [bm_eval n C (by decide) x hx], then decide +kernel on the concrete mask (bm_out n C reduces to a numeral).
--   Rows on two input blocks (eval on ofFn x ++ ofFn y): bm_fun_eq2; decide then runs 2^(n1+n2) checks (tested n = 3: whole test 21 s).

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def bm_op (K : ℕ) (op : GateOp) (l : List ℕ) : ℕ :=
  match op with
  | GateOp.and => l.foldr Nat.land (2 ^ K - 1)
  | GateOp.or => l.foldr Nat.lor 0
  | GateOp.not => Nat.xor (2 ^ K - 1) (l.headD 0)
  | _ => 0

def bm_okop (op : GateOp) : Bool :=
  match op with
  | GateOp.and => true
  | GateOp.or => true
  | GateOp.not => true
  | _ => false

def bm_ok (C : Circuit) : Bool := C.gates.all (fun g => bm_okop g.op)

def bm_step (K : ℕ) (m : List ℕ) (g : Gate) : List ℕ :=
  m ++ [bm_op K g.op (g.inputs.map fun i => m.getD i 0)]

def bm_W (K : ℕ) (gs : List Gate) (m : List ℕ) : List ℕ := gs.foldl (bm_step K) m

theorem bm_step_len (K : ℕ) (m : List ℕ) (g : Gate) :
    (bm_step K m g).length = m.length + 1 := by
  simp [bm_step]

theorem bm_step_lt (K : ℕ) (m : List ℕ) (g : Gate) (i : ℕ) (hi : i < m.length) :
    (bm_step K m g).getD i 0 = m.getD i 0 := by
  simp [bm_step, List.getD, List.getElem?_append_left hi]

theorem bm_step_last (K : ℕ) (m : List ℕ) (g : Gate) (k : ℕ) (hk : k = m.length) :
    (bm_step K m g).getD k 0 = bm_op K g.op (g.inputs.map fun i => m.getD i 0) := by
  subst hk
  simp [bm_step, List.getD]

theorem bm_op_bit (K k : ℕ) (hk : k < K) (op : GateOp) (hop : bm_okop op = true)
    (inputs : List ℕ) (fm : ℕ → ℕ) (fw : ℕ → Bool) (h : ∀ i, fw i = Nat.testBit (fm i) k) :
    Nat.testBit (bm_op K op (inputs.map fm)) k = op.eval (inputs.map fw) := by
  cases op with
  | and =>
    show Nat.testBit (List.foldr Nat.land (2 ^ K - 1) (List.map fm inputs)) k =
      (List.map fw inputs).all id
    induction inputs with
    | nil => simp [Nat.testBit_two_pow_sub_one, hk]
    | cons a l ih =>
      show Nat.testBit (fm a &&& List.foldr Nat.land (2 ^ K - 1) (List.map fm l)) k =
        (fw a && (List.map fw l).all id)
      rw [Nat.testBit_and, ih, h a]
  | or =>
    show Nat.testBit (List.foldr Nat.lor 0 (List.map fm inputs)) k =
      (List.map fw inputs).any id
    induction inputs with
    | nil => simp
    | cons a l ih =>
      show Nat.testBit (fm a ||| List.foldr Nat.lor 0 (List.map fm l)) k =
        (fw a || (List.map fw l).any id)
      rw [Nat.testBit_or, ih, h a]
  | not =>
    cases inputs with
    | nil =>
      show Nat.testBit ((2 ^ K - 1) ^^^ 0) k = !false
      simp [Nat.testBit_two_pow_sub_one, hk]
    | cons a l =>
      show Nat.testBit ((2 ^ K - 1) ^^^ fm a) k = !(fw a)
      rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, h a]
      simp [hk]
  | mod m => simp [bm_okop] at hop
  | maj => simp [bm_okop] at hop

def bm_Rep (k : ℕ) (w : List Bool) (m : List ℕ) : Prop :=
  w.length = m.length ∧ ∀ t, w.getD t false = Nat.testBit (m.getD t 0) k

theorem bm_rep_step (K k : ℕ) (hk : k < K) (g : Gate) (hop : bm_okop g.op = true)
    (w : List Bool) (m : List ℕ) (h : bm_Rep k w m) : bm_Rep k (step w g) (bm_step K m g) := by
  have h1 := h.1
  refine ⟨by rw [step_len, bm_step_len, h1], fun t => ?_⟩
  by_cases hlt : t < w.length
  · rw [step_lt w g t hlt, bm_step_lt K m g t (by omega)]
    exact h.2 t
  · by_cases heq : t = w.length
    · rw [step_last w g t heq, bm_step_last K m g t (heq.trans h1)]
      exact (bm_op_bit K k hk g.op hop g.inputs (fun i => m.getD i 0)
        (fun i => w.getD i false) h.2).symm
    · rw [getD_ge (step w g) t (by rw [step_len]; omega),
        List.getD_eq_default (bm_step K m g) 0 (by rw [bm_step_len]; omega)]
      exact (Nat.zero_testBit k).symm

theorem bm_rep_fold (K k : ℕ) (hk : k < K) (gs : List Gate)
    (hg : ∀ g ∈ gs, bm_okop g.op = true) :
    ∀ (w : List Bool) (m : List ℕ), bm_Rep k w m → bm_Rep k (W gs w) (bm_W K gs m) := by
  induction gs with
  | nil =>
    intro w m h
    exact h
  | cons g gs ih =>
    intro w m h
    show bm_Rep k (W gs (step w g)) (bm_W K gs (bm_step K m g))
    exact ih (fun g' hg' => hg g' (List.mem_cons.mpr (Or.inr hg'))) _ _
      (bm_rep_step K k hk g (hg g (List.mem_cons.mpr (Or.inl rfl))) w m h)

def bm_num : List Bool → ℕ
  | [] => 0
  | b :: l => Nat.bit b (bm_num l)

theorem bm_num_lt : ∀ l : List Bool, bm_num l < 2 ^ l.length
  | [] => by decide
  | b :: l => by
    have ih := bm_num_lt l
    have h2 : bm_num (b :: l) = 2 * bm_num l + b.toNat := Nat.bit_val b (bm_num l)
    have hb : b.toNat ≤ 1 := by cases b <;> decide
    rw [h2, List.length_cons, pow_succ]
    omega

theorem bm_num_bit : ∀ (l : List Bool) (i : ℕ), Nat.testBit (bm_num l) i = l.getD i false
  | [], i => by
    first
    | exact Nat.zero_testBit i
    | simp [bm_num]
  | b :: l, 0 => by
    rw [List.getD_cons_zero]
    exact Nat.testBit_bit_zero b (bm_num l)
  | b :: l, i + 1 => by
    rw [List.getD_cons_succ]
    exact (Nat.testBit_bit_succ i b (bm_num l)).trans (bm_num_bit l i)

theorem bm_num_append : ∀ (a b : List Bool), bm_num (a ++ b) = bm_num a + 2 ^ a.length * bm_num b
  | [], b => by simp [bm_num]
  | c :: a, b => by
    have ih := bm_num_append a b
    show Nat.bit c (bm_num (a ++ b)) = Nat.bit c (bm_num a) + 2 ^ (a.length + 1) * bm_num b
    rw [Nat.bit_val, Nat.bit_val, ih, pow_succ]
    ring

-- Mask over the 2 ^ m numbers k below 2 ^ m of bit p of k.
def bm_tab (p : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 =>
    if m = p then 2 ^ 2 ^ m * (2 ^ 2 ^ m - 1) + 0 else (2 ^ 2 ^ m + 1) * bm_tab p m

theorem bm_bnd (A t : ℕ) (h : t < A) : A * t + t < A * A := by
  have h1 := Nat.mul_le_mul_left A (Nat.succ_le_of_lt h)
  rw [Nat.mul_succ] at h1
  omega

theorem bm_tab_spec (p : ℕ) : ∀ m : ℕ, bm_tab p m < 2 ^ 2 ^ m ∧
    ∀ k : ℕ, k < 2 ^ m → Nat.testBit (bm_tab p m) k = Nat.testBit k p := by
  intro m
  induction m with
  | zero =>
    refine ⟨?_, fun k hk => ?_⟩
    · show (0 : ℕ) < 2 ^ 2 ^ 0
      exact Nat.two_pow_pos _
    · have hk0 : k = 0 := by simpa using hk
      rw [hk0]
      show Nat.testBit 0 0 = Nat.testBit 0 p
      rw [Nat.zero_testBit, Nat.zero_testBit]
  | succ m ih =>
    obtain ⟨hb, hbits⟩ := ih
    have hA : 0 < 2 ^ 2 ^ m := Nat.two_pow_pos _
    have hpm : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := Nat.two_pow_succ m
    have hpow : 2 ^ 2 ^ (m + 1) = 2 ^ 2 ^ m * 2 ^ 2 ^ m := by
      rw [hpm, Nat.pow_add]
    by_cases hmp : m = p
    · have hdef : bm_tab p (m + 1) = 2 ^ 2 ^ m * (2 ^ 2 ^ m - 1) + 0 := by
        rw [bm_tab, if_pos hmp]
      rw [hdef, ← hmp]
      refine ⟨?_, fun k hk => ?_⟩
      · have h1 := bm_bnd (2 ^ 2 ^ m) (2 ^ 2 ^ m - 1) (by omega)
        rw [hpow]
        omega
      · rw [Nat.testBit_two_pow_mul_add (2 ^ 2 ^ m - 1) hA k]
        by_cases hlt : k < 2 ^ m
        · rw [if_pos hlt, Nat.zero_testBit, Nat.testBit_lt_two_pow hlt]
        · rw [if_neg hlt, Nat.testBit_two_pow_sub_one]
          have h1 : Nat.testBit k m = true := by
            have h2 := Nat.testBit_two_pow_add_eq (k - 2 ^ m) m
            rw [show 2 ^ m + (k - 2 ^ m) = k from by omega,
              Nat.testBit_lt_two_pow (show k - 2 ^ m < 2 ^ m from by omega)] at h2
            exact h2
          rw [h1]
          exact decide_eq_true (by omega)
    · have hdef : bm_tab p (m + 1) = 2 ^ 2 ^ m * bm_tab p m + bm_tab p m := by
        rw [bm_tab, if_neg hmp]
        ring
      rw [hdef]
      refine ⟨?_, fun k hk => ?_⟩
      · have h1 := bm_bnd (2 ^ 2 ^ m) (bm_tab p m) hb
        rw [hpow]
        exact h1
      · rw [Nat.testBit_two_pow_mul_add (bm_tab p m) hb k]
        by_cases hlt : k < 2 ^ m
        · rw [if_pos hlt]
          exact hbits k hlt
        · rw [if_neg hlt, hbits (k - 2 ^ m) (by omega)]
          rcases Nat.lt_or_gt_of_ne hmp with hlt2 | hgt
          · have hle : 2 ^ (m + 1) ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hlt2
            rw [Nat.testBit_lt_two_pow (show k - 2 ^ m < 2 ^ p from by omega),
              Nat.testBit_lt_two_pow (show k < 2 ^ p from by omega)]
          · have h2 := Nat.testBit_two_pow_add_gt hgt (k - 2 ^ m)
            rw [show 2 ^ m + (k - 2 ^ m) = k from by omega] at h2
            exact h2.symm

def bm_init (n : ℕ) : List ℕ := (List.range n).map (fun p => bm_tab p n)

theorem bm_init_len (n : ℕ) : (bm_init n).length = n := by simp [bm_init]

theorem bm_rep_init (n : ℕ) (x : List Bool) (hx : x.length = n) :
    bm_Rep (bm_num x) x (bm_init n) := by
  have hk : bm_num x < 2 ^ n := by
    have h := bm_num_lt x
    rw [hx] at h
    exact h
  refine ⟨by rw [bm_init_len, hx], fun t => ?_⟩
  by_cases ht : t < n
  · rw [List.getD_eq_getElem (bm_init n) 0 (by rw [bm_init_len]; exact ht)]
    simp only [bm_init, List.getElem_map, List.getElem_range]
    rw [(bm_tab_spec t n).2 _ hk, bm_num_bit]
  · rw [getD_ge x t (by omega), List.getD_eq_default (bm_init n) 0 (by rw [bm_init_len]; omega)]
    exact (Nat.zero_testBit _).symm

def bm_out (n : ℕ) (C : Circuit) : ℕ := (bm_W (2 ^ n) C.gates (bm_init n)).getD C.output 0

theorem bm_eval (n : ℕ) (C : Circuit) (hC : bm_ok C = true) (x : List Bool) (hx : x.length = n) :
    C.eval x = Nat.testBit (bm_out n C) (bm_num x) := by
  have hk : bm_num x < 2 ^ n := by
    have h := bm_num_lt x
    rw [hx] at h
    exact h
  have hg : ∀ g ∈ C.gates, bm_okop g.op = true := fun g hgm => List.all_eq_true.mp hC g hgm
  have h := bm_rep_fold (2 ^ n) (bm_num x) hk C.gates hg x (bm_init n) (bm_rep_init n x hx)
  rw [eval_W]
  exact h.2 C.output

def bm_code {n : ℕ} (x : Fin n → Bool) : ℕ := bm_num (List.ofFn x)

def bm_input (n m : ℕ) : Fin n → Bool := fun i => Nat.testBit m i.val

theorem bm_code_lt {n : ℕ} (x : Fin n → Bool) : bm_code x < 2 ^ n := by
  have h := bm_num_lt (List.ofFn x)
  rw [List.length_ofFn] at h
  exact h

theorem bm_input_code {n : ℕ} (x : Fin n → Bool) : bm_input n (bm_code x) = x := by
  funext i
  show Nat.testBit (bm_num (List.ofFn x)) i.val = x i
  rw [bm_num_bit, ofFn_getD x i.val i.isLt]

theorem bm_code_input (n m : ℕ) (hm : m < 2 ^ n) : bm_code (bm_input n m) = m := by
  apply Nat.eq_of_testBit_eq
  intro i
  show Nat.testBit (bm_num (List.ofFn (bm_input n m))) i = Nat.testBit m i
  rw [bm_num_bit]
  by_cases hi : i < n
  · rw [ofFn_getD _ i hi]
    rfl
  · rw [ofFn_getD_ge _ i (by omega)]
    have hle : 2 ^ n ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact (Nat.testBit_lt_two_pow (show m < 2 ^ i from by omega)).symm

theorem bm_circuitFun (n : ℕ) (C : Circuit) (hC : bm_ok C = true) (x : Fin n → Bool) :
    circuitFun n C x = Nat.testBit (bm_out n C) (bm_code x) :=
  bm_eval n C hC (List.ofFn x) (List.length_ofFn)

theorem bm_circuitFun_num (n : ℕ) (C : Circuit) (hC : bm_ok C = true) (m : ℕ) (hm : m < 2 ^ n) :
    circuitFun n C (bm_input n m) = Nat.testBit (bm_out n C) m := by
  rw [bm_circuitFun n C hC, bm_code_input n m hm]

theorem bm_forall_iff (n : ℕ) (P : (Fin n → Bool) → Prop) :
    (∀ x, P x) ↔ ∀ m, m < 2 ^ n → P (bm_input n m) := by
  constructor
  · intro h m _
    exact h _
  · intro h x
    have e := h (bm_code x) (bm_code_lt x)
    rw [bm_input_code] at e
    exact e

theorem bm_exists_iff (n : ℕ) (P : (Fin n → Bool) → Prop) :
    (∃ x, P x) ↔ ∃ m, m < 2 ^ n ∧ P (bm_input n m) := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨bm_code x, bm_code_lt x, ?_⟩
    rw [bm_input_code]
    exact hx
  · rintro ⟨m, _, hm⟩
    exact ⟨_, hm⟩

theorem bm_fun_eq (n : ℕ) (C : Circuit) (hC : bm_ok C = true) (f : (Fin n → Bool) → Bool)
    (h : ∀ m, m < 2 ^ n → Nat.testBit (bm_out n C) m = f (bm_input n m)) :
    ∀ x, circuitFun n C x = f x := by
  intro x
  rw [bm_circuitFun n C hC x]
  have e := h (bm_code x) (bm_code_lt x)
  rw [bm_input_code] at e
  exact e

theorem bm_eval_two (n1 n2 : ℕ) (C : Circuit) (hC : bm_ok C = true)
    (x : Fin n1 → Bool) (y : Fin n2 → Bool) :
    C.eval (List.ofFn x ++ List.ofFn y) =
      Nat.testBit (bm_out (n1 + n2) C) (bm_code x + 2 ^ n1 * bm_code y) := by
  show C.eval (List.ofFn x ++ List.ofFn y) =
    Nat.testBit (bm_out (n1 + n2) C) (bm_num (List.ofFn x) + 2 ^ n1 * bm_num (List.ofFn y))
  rw [bm_eval (n1 + n2) C hC (List.ofFn x ++ List.ofFn y) (by simp), bm_num_append, List.length_ofFn]

theorem bm_fun_eq2 (n1 n2 : ℕ) (C : Circuit) (hC : bm_ok C = true)
    (f : (Fin n1 → Bool) → (Fin n2 → Bool) → Bool)
    (h : ∀ a, a < 2 ^ n1 → ∀ b, b < 2 ^ n2 →
      Nat.testBit (bm_out (n1 + n2) C) (a + 2 ^ n1 * b) = f (bm_input n1 a) (bm_input n2 b)) :
    ∀ x y, C.eval (List.ofFn x ++ List.ofFn y) = f x y := by
  intro x y
  rw [bm_eval_two n1 n2 C hC x y]
  have e := h (bm_code x) (bm_code_lt x) (bm_code y) (bm_code_lt y)
  rw [bm_input_code, bm_input_code] at e
  exact e

-- FRAGMENT repvar    DEPENDS: fold mono table1a bitmask
-- Variants of the Table 1a rows (namespace PEqualNP.Represents): repSize, repSize2, RepSize2AtMost (IsAO2),
-- HasLitSize / litSize (AND, OR fan-in at most 2 over the n bits and their negations) and generalSize /
-- HasCircuitSize (AND, OR, NOT fan-in at most 2). Abbreviations: RS = RepSizeAtMost, RS2 = RepSize2AtMost,
-- HL = HasLitSize, HC = PEqualNP.MetaComplexity.HasCircuitSize, full wd = t1_bits (fun _ => true) wd.
-- Exports:
--   (glue, sInf over the naturals in the extended naturals)
--   rv_sInf_le (P k) (P k) : sInf {x | exists j, x = j and P j} <= k ;  rv_le_sInf (all j < k, not P j) : k <= sInf ..
--   rv_sInf_eq P (hm : P monotone) k t (ht : (k : ENat) = t) (h1 : P k) (h2 : 0 < k -> not P (k - 1)) : sInf .. = t
--   rv_repSize_eq A k t ht (h1 : RS A k) (h2 : 0 < k -> not RS A (k - 1)) : repSize A = t ;  rv_repSize2_eq (RS2, repSize2)
--   rv_litSize_eq n f k t ht (HL n f k) (..) : litSize n f = t ;  rv_generalSize_eq n f k t ht (HC n f k) (..) : generalSize n f = t
--   rv_rs_mono, rv_rs2_mono, rv_hl_mono, rv_hc_mono : a <= b -> X a -> X b
--   (profile engine, generic over the inputs inp k (length N) and the profile width wd)
--   def rv_prof wd inp C w := t1_bits (fun k => val C (inp k) w) wd ;  def rv_St wd N inp B C j (B then gate profiles)
--   def rv_G Stp T r S (T within r steps of relation Stp), rv_Gf (fresh steps) ;  rv_G_Gf, rv_G_le, rv_Gf_le, rv_chain
--   rv_Gf_t1 : rv_Gf t1_Step -> t1_Gf (then t1_reach_sound of fragment table1a)
--   rv_run : every gate gives a step Stp (from any S containing B and the earlier profiles) -> rv_G Stp (output profile) s B
--   def rv_Stc F S p := t1_Step S p or p = F (constant gate) ;  rv_split : a chain with constant steps is a chain without,
--       or one of length r - 1 from F :: S ;  rv_close F T s B (hG) (hc1 : t1_reach T s B = false)
--       (hc2 : 0 < s -> t1_reach T (s - 1) (F :: B) = false) : False   (constants cost a gate, F not in B)
--   rv_gate_ao : AND / OR gate (fan-in <= 2; fan-in < 2 needs full in S) is a t1_Step ;  rv_gate_c : AND / OR gate is an rv_Stc full
--   def rv_StepN F S p := t1_Step S p or p = a xor F (a in S) ;  rv_gate_fan : AND / OR / NOT gate is an rv_StepN full (0 in S)
--   def rv_nreach F T r S : Bool search with NOT steps ;  rv_nreach_sound : rv_Gf (rv_StepN F) T r S -> rv_nreach = true
--   (inputs) def rv_inp n m hn hm k := oneEach (k / m mod n) (k mod m) ;  def rv_lit n k := bits of k ++ negated bits ;  def rv_bin n k
--   (lower bounds; T = target bits, F = full, B = base list = 0 and the input profiles; every hypothesis by decide +kernel)
--   rv1_lower n m hn hm A s T F B (hT : t1_bits (fun k => A (k / m mod n) (k mod m)) (n * m) = T) (hF : full (n * m) = F)
--       (hB : inputs in B) (h0 : 0 in B) (hc1 : t1_reach T s B = false) (hc2 : 0 < s -> t1_reach T (s - 1) (F :: B) = false) : not RS A s
--   rv2_lower n m hn hm A s T B hT hB h0 (hc : t1_reach T s B = false) : not RS2 A s
--   rvl_lower n f s T F B (hT : t1_bits (fun k => f (bm_input n k)) (2 ^ n) = T) hF hB h0 hc1 hc2 : not HL n f s   (B: 2n literals)
--   rvg_lower n f s T F B hT hF hB h0 (hc : rv_nreach F T s B = false) : not HC n f s
--   (upper bounds) def rv_okn ;  rv_fan2 (all gates AND / OR / NOT of fan-in <= 2, as a Bool) : FanInTwo C
-- Use: SP/tools/repvariants.py N writes whole files (statement driven). Glue: refine rv_repSize_eq _ 3 _ (by norm_num) ?_ ?_.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem rv_sInf_le (P : ℕ → Prop) (k : ℕ) (h : P k) :
    sInf {x : ℕ∞ | ∃ j : ℕ, x = (j : ℕ∞) ∧ P j} ≤ (k : ℕ∞) :=
  sInf_le ⟨k, rfl, h⟩

theorem rv_le_sInf (P : ℕ → Prop) (k : ℕ) (h : ∀ j, j < k → ¬ P j) :
    (k : ℕ∞) ≤ sInf {x : ℕ∞ | ∃ j : ℕ, x = (j : ℕ∞) ∧ P j} := by
  apply le_sInf
  rintro x ⟨j, rfl, hj⟩
  by_contra hlt
  have hlt' : (j : ℕ∞) < (k : ℕ∞) := not_le.mp hlt
  exact h j (by exact_mod_cast hlt') hj

theorem rv_sInf_eq (P : ℕ → Prop) (hm : ∀ a b, a ≤ b → P a → P b) (k : ℕ) (t : ℕ∞)
    (ht : (k : ℕ∞) = t) (h1 : P k) (h2 : 0 < k → ¬ P (k - 1)) :
    sInf {x : ℕ∞ | ∃ j : ℕ, x = (j : ℕ∞) ∧ P j} = t := by
  rw [← ht]
  apply le_antisymm (rv_sInf_le P k h1)
  apply rv_le_sInf P k
  intro j hj hP
  exact h2 (by omega) (hm j (k - 1) (by omega) hP)

theorem rv_rs_mono {n m : ℕ} (A : Fin n → Fin m → Bool) :
    ∀ a b, a ≤ b → PEqualNP.Represents.RepSizeAtMost A a → PEqualNP.Represents.RepSizeAtMost A b := by
  rintro a b hab ⟨C, h1, h2, h3⟩
  exact ⟨C, h1, le_trans h2 hab, h3⟩

theorem rv_rs2_mono {n m : ℕ} (A : Fin n → Fin m → Bool) :
    ∀ a b, a ≤ b → PEqualNP.Represents.RepSize2AtMost A a → PEqualNP.Represents.RepSize2AtMost A b := by
  rintro a b hab ⟨C, h1, h2, h3⟩
  exact ⟨C, h1, le_trans h2 hab, h3⟩

theorem rv_hl_mono (n : ℕ) (f : (Fin n → Bool) → Bool) :
    ∀ a b, a ≤ b → PEqualNP.Represents.HasLitSize n f a → PEqualNP.Represents.HasLitSize n f b := by
  rintro a b hab ⟨C, h1, h2, h3⟩
  exact ⟨C, h1, le_trans h2 hab, h3⟩

theorem rv_hc_mono (n : ℕ) (f : (Fin n → Bool) → Bool) :
    ∀ a b, a ≤ b → HasCircuitSize n f a → HasCircuitSize n f b := by
  rintro a b hab ⟨C, h1, h2, h3⟩
  exact ⟨C, h1, le_trans h2 hab, h3⟩

theorem rv_repSize_eq {n m : ℕ} (A : Fin n → Fin m → Bool) (k : ℕ) (t : ℕ∞) (ht : (k : ℕ∞) = t)
    (h1 : PEqualNP.Represents.RepSizeAtMost A k)
    (h2 : 0 < k → ¬ PEqualNP.Represents.RepSizeAtMost A (k - 1)) :
    PEqualNP.Represents.repSize A = t := by
  unfold PEqualNP.Represents.repSize
  exact rv_sInf_eq (fun j => PEqualNP.Represents.RepSizeAtMost A j) (rv_rs_mono A) k t ht h1 h2

theorem rv_repSize2_eq {n m : ℕ} (A : Fin n → Fin m → Bool) (k : ℕ) (t : ℕ∞) (ht : (k : ℕ∞) = t)
    (h1 : PEqualNP.Represents.RepSize2AtMost A k)
    (h2 : 0 < k → ¬ PEqualNP.Represents.RepSize2AtMost A (k - 1)) :
    PEqualNP.Represents.repSize2 A = t := by
  unfold PEqualNP.Represents.repSize2
  exact rv_sInf_eq (fun j => PEqualNP.Represents.RepSize2AtMost A j) (rv_rs2_mono A) k t ht h1 h2

theorem rv_litSize_eq (n : ℕ) (f : (Fin n → Bool) → Bool) (k : ℕ) (t : ℕ∞) (ht : (k : ℕ∞) = t)
    (h1 : PEqualNP.Represents.HasLitSize n f k)
    (h2 : 0 < k → ¬ PEqualNP.Represents.HasLitSize n f (k - 1)) :
    PEqualNP.Represents.litSize n f = t := by
  unfold PEqualNP.Represents.litSize
  exact rv_sInf_eq (fun j => PEqualNP.Represents.HasLitSize n f j) (rv_hl_mono n f) k t ht h1 h2

theorem rv_generalSize_eq (n : ℕ) (f : (Fin n → Bool) → Bool) (k : ℕ) (t : ℕ∞) (ht : (k : ℕ∞) = t)
    (h1 : HasCircuitSize n f k) (h2 : 0 < k → ¬ HasCircuitSize n f (k - 1)) :
    PEqualNP.Represents.generalSize n f = t := by
  unfold PEqualNP.Represents.generalSize
  exact rv_sInf_eq (fun j => HasCircuitSize n f j) (rv_hc_mono n f) k t ht h1 h2

def rv_prof (wd : ℕ) (inp : ℕ → List Bool) (C : Circuit) (w : ℕ) : ℕ :=
  t1_bits (fun k => val C (inp k) w) wd

def rv_St (wd N : ℕ) (inp : ℕ → List Bool) (B : List ℕ) (C : Circuit) : ℕ → List ℕ
  | 0 => B
  | j + 1 => rv_prof wd inp C (N + j) :: rv_St wd N inp B C j

theorem rv_St_base (wd N : ℕ) (inp : ℕ → List Bool) (B : List ℕ) (C : Circuit) {x : ℕ} (hx : x ∈ B)
    (j : ℕ) : x ∈ rv_St wd N inp B C j := by
  induction j with
  | zero => exact hx
  | succ j ih => exact List.mem_cons_of_mem _ ih

theorem rv_St_prof (wd N : ℕ) (inp : ℕ → List Bool) (B : List ℕ) (C : Circuit)
    (hlen : ∀ k, (inp k).length = N)
    (hB : ∀ u, u < N → t1_bits (fun k => (inp k).getD u false) wd ∈ B) (j : ℕ) :
    ∀ i, i < N + j → rv_prof wd inp C i ∈ rv_St wd N inp B C j := by
  induction j with
  | zero =>
    intro i hi
    have e : rv_prof wd inp C i = t1_bits (fun k => (inp k).getD i false) wd := by
      unfold rv_prof
      congr 1
      funext k
      exact val_input (hlen k) (by omega)
    rw [e]
    exact hB i (by omega)
  | succ j ih =>
    intro i hi
    by_cases h : i < N + j
    · exact List.mem_cons_of_mem _ (ih i h)
    · have e : i = N + j := by omega
      subst e
      simp [rv_St]

def rv_G (Stp : List ℕ → ℕ → Prop) (T : ℕ) : ℕ → List ℕ → Prop
  | 0, S => T ∈ S
  | r + 1, S => T ∈ S ∨ ∃ p, Stp S p ∧ rv_G Stp T r (p :: S)

def rv_Gf (Stp : List ℕ → ℕ → Prop) (T : ℕ) : ℕ → List ℕ → Prop
  | 0, S => T ∈ S
  | r + 1, S => T ∈ S ∨ ∃ p, Stp S p ∧ p ∉ S ∧ rv_Gf Stp T r (p :: S)

theorem rv_G_sub (Stp : List ℕ → ℕ → Prop) (hmono : ∀ S S' p, (∀ x ∈ S, x ∈ S') → Stp S p → Stp S' p)
    (T r : ℕ) : ∀ S S' : List ℕ, (∀ x ∈ S, x ∈ S') → rv_G Stp T r S → rv_G Stp T r S' := by
  induction r with
  | zero => intro S S' hs h; exact hs _ h
  | succ r ih =>
    intro S S' hs h
    rcases h with h | ⟨p, hp, hg⟩
    · exact Or.inl (hs _ h)
    · refine Or.inr ⟨p, hmono S S' p hs hp, ih (p :: S) (p :: S') ?_ hg⟩
      intro x hx
      simp only [List.mem_cons] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (hs _ hx)

theorem rv_Gf_succ (Stp : List ℕ → ℕ → Prop) (T r : ℕ) :
    ∀ S : List ℕ, rv_Gf Stp T r S → rv_Gf Stp T (r + 1) S := by
  induction r with
  | zero => intro S h; exact Or.inl h
  | succ r ih =>
    intro S h
    rcases h with h | ⟨p, hp, hn, hg⟩
    · exact Or.inl h
    · exact Or.inr ⟨p, hp, hn, ih _ hg⟩

theorem rv_Gf_le (Stp : List ℕ → ℕ → Prop) (T r : ℕ) (S : List ℕ) (h : rv_Gf Stp T r S) :
    ∀ k, rv_Gf Stp T (r + k) S := by
  intro k
  induction k with
  | zero => exact h
  | succ k ih => exact rv_Gf_succ Stp T (r + k) S ih

theorem rv_G_Gf (Stp : List ℕ → ℕ → Prop) (hmono : ∀ S S' p, (∀ x ∈ S, x ∈ S') → Stp S p → Stp S' p)
    (T r : ℕ) : ∀ S : List ℕ, rv_G Stp T r S → rv_Gf Stp T r S := by
  induction r with
  | zero => intro S h; exact h
  | succ r ih =>
    intro S h
    rcases h with h | ⟨p, hp, hg⟩
    · exact Or.inl h
    · by_cases hpS : p ∈ S
      · apply rv_Gf_succ Stp T r S
        apply ih S
        apply rv_G_sub Stp hmono T r (p :: S) S _ hg
        intro x hx
        rcases List.mem_cons.mp hx with hx | hx
        · rw [hx]; exact hpS
        · exact hx
      · exact Or.inr ⟨p, hp, hpS, ih _ hg⟩

theorem rv_chain (Stp : List ℕ → ℕ → Prop) (T : ℕ) (St : ℕ → List ℕ) (P : ℕ → ℕ) (len : ℕ)
    (hst : ∀ j, j < len → St (j + 1) = P j :: St j ∧ Stp (St j) (P j))
    (hT : T ∈ St len) : ∀ d j, j + d = len → rv_G Stp T d (St j) := by
  intro d
  induction d with
  | zero =>
    intro j hj
    have e : j = len := by omega
    rw [e]
    exact hT
  | succ d ih =>
    intro j hj
    obtain ⟨hs, hp⟩ := hst j (by omega)
    have h := ih (j + 1) (by omega)
    rw [hs] at h
    exact Or.inr ⟨P j, hp, h⟩

theorem rv_Gf_t1 (T : ℕ) : ∀ r S, rv_Gf t1_Step T r S → t1_Gf T r S := by
  intro r
  induction r with
  | zero => intro S h; exact h
  | succ r ih =>
    intro S h
    rcases h with h | ⟨p, ⟨a, ha, b, hb, hp⟩, hn, hg⟩
    · exact Or.inl h
    · exact Or.inr ⟨a, ha, b, hb, p, hp, hn, ih _ hg⟩

theorem rv_t1_mono : ∀ S S' : List ℕ, ∀ p, (∀ x ∈ S, x ∈ S') → t1_Step S p → t1_Step S' p := by
  rintro S S' p hs ⟨a, ha, b, hb, hp⟩
  exact ⟨a, hs _ ha, b, hs _ hb, hp⟩

theorem rv_G_succ (Stp : List ℕ → ℕ → Prop) (T : ℕ) :
    ∀ r S, rv_G Stp T r S → rv_G Stp T (r + 1) S := by
  intro r
  induction r with
  | zero => intro S h; exact Or.inl h
  | succ r ih =>
    intro S h
    rcases h with h | ⟨p, hp, hg⟩
    · exact Or.inl h
    · exact Or.inr ⟨p, hp, ih _ hg⟩

theorem rv_G_le (Stp : List ℕ → ℕ → Prop) (T r : ℕ) (S : List ℕ) (h : rv_G Stp T r S) :
    ∀ k, rv_G Stp T (r + k) S := by
  intro k
  induction k with
  | zero => exact h
  | succ k ih => exact rv_G_succ Stp T (r + k) S ih

theorem rv_run (wd N : ℕ) (inp : ℕ → List Bool) (B : List ℕ) (C : Circuit)
    (Stp : List ℕ → ℕ → Prop)
    (hlen : ∀ k, (inp k).length = N)
    (hB : ∀ u, u < N → t1_bits (fun k => (inp k).getD u false) wd ∈ B) (h0 : 0 ∈ B)
    (hgate : ∀ j, j < C.gates.length → ∀ S : List ℕ, (∀ x ∈ B, x ∈ S) →
      (∀ i, i < N + j → rv_prof wd inp C i ∈ S) →
      Stp S (t1_bits (fun k => (gateAt C j).op.eval ((gateAt C j).inputs.map
        (fun i => if i < N + j then val C (inp k) i else false))) wd))
    (s T : ℕ) (hs : C.gates.length ≤ s) (hT : rv_prof wd inp C C.output = T) :
    rv_G Stp T s B := by
  have hstep : ∀ j, j < C.gates.length →
      rv_St wd N inp B C (j + 1) = rv_prof wd inp C (N + j) :: rv_St wd N inp B C j ∧
      Stp (rv_St wd N inp B C j) (rv_prof wd inp C (N + j)) := by
    intro j hj
    refine ⟨rfl, ?_⟩
    have e : rv_prof wd inp C (N + j) = t1_bits (fun k => (gateAt C j).op.eval ((gateAt C j).inputs.map
        (fun i => if i < N + j then val C (inp k) i else false))) wd := by
      unfold rv_prof
      congr 1
      funext k
      exact val_gate (hlen k) hj
    rw [e]
    exact hgate j hj _ (fun x hx => rv_St_base wd N inp B C hx j) (rv_St_prof wd N inp B C hlen hB j)
  have hout : T ∈ rv_St wd N inp B C C.gates.length := by
    rw [← hT]
    by_cases ho : C.output < N + C.gates.length
    · exact rv_St_prof wd N inp B C hlen hB _ _ ho
    · have e : rv_prof wd inp C C.output = 0 := by
        unfold rv_prof
        rw [show (fun k => val C (inp k) C.output) = fun _ => false from
          funext fun k => val_ge (hlen k) (by omega)]
        exact t1_bits_false wd
      rw [e]
      exact rv_St_base wd N inp B C h0 _
  have hG := rv_chain Stp T (rv_St wd N inp B C) (fun j => rv_prof wd inp C (N + j)) C.gates.length
    hstep hout C.gates.length 0 (by omega)
  have hG2 := rv_G_le Stp T _ _ hG (s - C.gates.length)
  rw [show C.gates.length + (s - C.gates.length) = s by omega] at hG2
  exact hG2

theorem rv_gate_ao (wd : ℕ) (S : List ℕ) (R : ℕ → ℕ → Bool) (op : GateOp) (l : List ℕ)
    (hop : op = GateOp.and ∨ op = GateOp.or) (hl : l.length ≤ 2)
    (hR : ∀ i ∈ l, t1_bits (fun k => R k i) wd ∈ S) (h0 : 0 ∈ S)
    (h1 : l.length < 2 → t1_bits (fun _ => true) wd ∈ S) :
    t1_Step S (t1_bits (fun k => op.eval (l.map (R k))) wd) := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · have hF := h1 (by simp)
    rcases hop with rfl | rfl
    · have e : (fun k => GateOp.and.eval (([] : List ℕ).map (R k))) = fun _ => true := by
        funext k; simp [GateOp.eval]
      rw [e]
      exact ⟨_, hF, _, hF, Or.inl (t1_land_self _).symm⟩
    · have e : (fun k => GateOp.or.eval (([] : List ℕ).map (R k))) = fun _ => false := by
        funext k; simp [GateOp.eval]
      rw [e, t1_bits_false]
      exact ⟨0, h0, 0, h0, Or.inr (by decide)⟩
  · have ha := hR a (by simp)
    have hF := h1 (by simp)
    rcases hop with rfl | rfl
    · have e : (fun k => GateOp.and.eval ([a].map (R k))) = fun k => R k a && true := by
        funext k; simp [GateOp.eval]
      rw [e, t1_bits_and]
      exact ⟨_, ha, _, hF, Or.inl rfl⟩
    · have e : (fun k => GateOp.or.eval ([a].map (R k))) = fun k => R k a || false := by
        funext k; simp [GateOp.eval]
      rw [e, t1_bits_or, t1_bits_false]
      exact ⟨_, ha, 0, h0, Or.inr rfl⟩
  · have ha := hR a (by simp)
    have hb := hR b (by simp)
    rcases hop with rfl | rfl
    · have e : (fun k => GateOp.and.eval ([a, b].map (R k))) = fun k => R k a && R k b := by
        funext k; simp [GateOp.eval]
      rw [e, t1_bits_and]
      exact ⟨_, ha, _, hb, Or.inl rfl⟩
    · have e : (fun k => GateOp.or.eval ([a, b].map (R k))) = fun k => R k a || R k b := by
        funext k; simp [GateOp.eval]
      rw [e, t1_bits_or]
      exact ⟨_, ha, _, hb, Or.inr rfl⟩
  · simp only [List.length_cons] at hl
    omega

def rv_StepN (F : ℕ) (S : List ℕ) (p : ℕ) : Prop := t1_Step S p ∨ ∃ a ∈ S, p = a ^^^ F

theorem rv_n_mono (F : ℕ) : ∀ S S' : List ℕ, ∀ p, (∀ x ∈ S, x ∈ S') → rv_StepN F S p → rv_StepN F S' p := by
  rintro S S' p hs (h | ⟨a, ha, hp⟩)
  · exact Or.inl (rv_t1_mono S S' p hs h)
  · exact Or.inr ⟨a, hs _ ha, hp⟩

theorem rv_bits_not (f : ℕ → Bool) (wd : ℕ) :
    t1_bits (fun k => !f k) wd = t1_bits f wd ^^^ t1_bits (fun _ => true) wd := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor, t1_bits_testBit]
  cases (decide (i < wd)) <;> cases (f i) <;> rfl

theorem rv_zero_xor (a : ℕ) : 0 ^^^ a = a := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp [Nat.testBit_xor]

def rv_Stc (F : ℕ) (S : List ℕ) (p : ℕ) : Prop := t1_Step S p ∨ p = F

theorem rv_c_mono (F : ℕ) : ∀ S S' : List ℕ, ∀ p, (∀ x ∈ S, x ∈ S') → rv_Stc F S p → rv_Stc F S' p := by
  rintro S S' p hs (h | h)
  · exact Or.inl (rv_t1_mono S S' p hs h)
  · exact Or.inr h

theorem rv_cfree (F T : ℕ) : ∀ r S, F ∈ S → rv_G (rv_Stc F) T r S → rv_G t1_Step T r S := by
  intro r
  induction r with
  | zero => intro S _ h; exact h
  | succ r ih =>
    intro S hF h
    rcases h with h | ⟨p, hp | hp, hg⟩
    · exact Or.inl h
    · exact Or.inr ⟨p, hp, ih _ (List.mem_cons_of_mem _ hF) hg⟩
    · rw [hp] at hg
      have h1 := ih (F :: S) (by simp) hg
      have h2 := rv_G_sub t1_Step rv_t1_mono T r (F :: S) S (fun x hx => by
        rcases List.mem_cons.mp hx with hx | hx
        · rw [hx]; exact hF
        · exact hx) h1
      exact rv_G_succ t1_Step T r S h2

theorem rv_split (F T : ℕ) : ∀ r S, rv_G (rv_Stc F) T r S →
    rv_G t1_Step T r S ∨ (0 < r ∧ rv_G t1_Step T (r - 1) (F :: S)) := by
  intro r
  induction r with
  | zero => intro S h; exact Or.inl h
  | succ r ih =>
    intro S h
    rcases h with h | ⟨p, hp | hp, hg⟩
    · exact Or.inl (Or.inl h)
    · rcases ih _ hg with h2 | ⟨hpos, h2⟩
      · exact Or.inl (Or.inr ⟨p, hp, h2⟩)
      · right
        refine ⟨by omega, ?_⟩
        rw [show r + 1 - 1 = (r - 1) + 1 by omega]
        refine Or.inr ⟨p, rv_t1_mono S (F :: S) p (fun x hx => List.mem_cons_of_mem _ hx) hp, ?_⟩
        exact rv_G_sub t1_Step rv_t1_mono T (r - 1) _ _ (fun x hx => by
          rcases List.mem_cons.mp hx with h | h
          · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl h))
          · rcases List.mem_cons.mp h with h | h
            · exact List.mem_cons.mpr (Or.inl h)
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)) h2
    · rw [hp] at hg
      right
      refine ⟨by omega, ?_⟩
      rw [show r + 1 - 1 = r by omega]
      exact rv_cfree F T r (F :: S) (by simp) hg

theorem rv_close (F T s : ℕ) (B : List ℕ) (hG : rv_G (rv_Stc F) T s B)
    (hc1 : t1_reach T s B = false) (hc2 : 0 < s → t1_reach T (s - 1) (F :: B) = false) : False := by
  rcases rv_split F T s B hG with h | ⟨hpos, h⟩
  · have h2 := t1_reach_sound T s B (rv_Gf_t1 T s B (rv_G_Gf t1_Step rv_t1_mono T s B h))
    rw [hc1] at h2
    exact Bool.false_ne_true h2
  · have h2 := t1_reach_sound T (s - 1) (F :: B)
      (rv_Gf_t1 T _ _ (rv_G_Gf t1_Step rv_t1_mono T _ _ h))
    rw [hc2 hpos] at h2
    exact Bool.false_ne_true h2

theorem rv_gate_c (wd : ℕ) (S : List ℕ) (R : ℕ → ℕ → Bool) (op : GateOp) (l : List ℕ)
    (hop : op = GateOp.and ∨ op = GateOp.or) (hl : l.length ≤ 2)
    (hR : ∀ i ∈ l, t1_bits (fun k => R k i) wd ∈ S) (h0 : 0 ∈ S) :
    rv_Stc (t1_bits (fun _ => true) wd) S (t1_bits (fun k => op.eval (l.map (R k))) wd) := by
  unfold rv_Stc
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · rcases hop with rfl | rfl
    · have e : (fun k => GateOp.and.eval (([] : List ℕ).map (R k))) = fun _ => true := by
        funext k; simp [GateOp.eval]
      rw [e]
      exact Or.inr rfl
    · have e : (fun k => GateOp.or.eval (([] : List ℕ).map (R k))) = fun _ => false := by
        funext k; simp [GateOp.eval]
      rw [e, t1_bits_false]
      exact Or.inl ⟨0, h0, 0, h0, Or.inr (by decide)⟩
  · have ha := hR a (by simp)
    rcases hop with rfl | rfl
    · have e : (fun k => GateOp.and.eval ([a].map (R k))) = fun k => R k a && R k a := by
        funext k; simp [GateOp.eval]
      rw [e, t1_bits_and]
      exact Or.inl ⟨_, ha, _, ha, Or.inl rfl⟩
    · have e : (fun k => GateOp.or.eval ([a].map (R k))) = fun k => R k a || R k a := by
        funext k; simp [GateOp.eval]
      rw [e, t1_bits_or]
      exact Or.inl ⟨_, ha, _, ha, Or.inr rfl⟩
  · exact Or.inl (rv_gate_ao wd S R op [a, b] hop hl hR h0 (fun h => absurd h (by simp)))
  · simp only [List.length_cons] at hl
    omega

theorem rv_gate_fan (wd : ℕ) (S : List ℕ) (R : ℕ → ℕ → Bool) (op : GateOp) (l : List ℕ)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hl : l.length ≤ 2)
    (hR : ∀ i ∈ l, t1_bits (fun k => R k i) wd ∈ S) (h0 : 0 ∈ S) :
    rv_StepN (t1_bits (fun _ => true) wd) S (t1_bits (fun k => op.eval (l.map (R k))) wd) := by
  unfold rv_StepN
  rcases hop with h | h | h
  · rcases rv_gate_c wd S R op l (Or.inl h) hl hR h0 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr ⟨0, h0, by rw [h2, rv_zero_xor]⟩
  · rcases rv_gate_c wd S R op l (Or.inr h) hl hR h0 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr ⟨0, h0, by rw [h2, rv_zero_xor]⟩
  · subst h
    rcases l with _ | ⟨a, l⟩
    · have e : (fun k => GateOp.not.eval (([] : List ℕ).map (R k))) = fun _ => true := by
        funext k; simp [GateOp.eval]
      rw [e]
      exact Or.inr ⟨0, h0, (rv_zero_xor _).symm⟩
    · have e : (fun k => GateOp.not.eval ((a :: l).map (R k))) = fun k => !R k a := by
        funext k; simp [GateOp.eval]
      rw [e, rv_bits_not]
      exact Or.inr ⟨_, hR a (by simp), rfl⟩


def rv_nreach (F T : ℕ) : ℕ → List ℕ → Bool
  | 0, S => t1_mem T S
  | 1, S => t1_mem T S || t1_one T S || S.any (fun a => a ^^^ F == T)
  | r + 2, S => t1_mem T S || t1_pany (fun a b =>
      (!t1_mem (a &&& b) S && rv_nreach F T (r + 1) ((a &&& b) :: S)) ||
      (!t1_mem (a ||| b) S && rv_nreach F T (r + 1) ((a ||| b) :: S))) S ||
      S.any (fun a => !t1_mem (a ^^^ F) S && rv_nreach F T (r + 1) ((a ^^^ F) :: S))

theorem rv_nreach_one (F T : ℕ) (S : List ℕ) :
    rv_nreach F T 1 S = (t1_mem T S || t1_one T S || S.any (fun a => a ^^^ F == T)) := rfl

theorem rv_nreach_two (F T r : ℕ) (S : List ℕ) : rv_nreach F T (r + 2) S = (t1_mem T S || t1_pany
    (fun a b => (!t1_mem (a &&& b) S && rv_nreach F T (r + 1) ((a &&& b) :: S)) ||
      (!t1_mem (a ||| b) S && rv_nreach F T (r + 1) ((a ||| b) :: S))) S ||
    S.any (fun a => !t1_mem (a ^^^ F) S && rv_nreach F T (r + 1) ((a ^^^ F) :: S))) := rfl

theorem rv_nreach_sound (F T : ℕ) :
    ∀ (r : ℕ) (S : List ℕ), rv_Gf (rv_StepN F) T r S → rv_nreach F T r S = true
  | 0, S, h => t1_mem_of T S h
  | 1, S, h => by
    rw [rv_nreach_one, Bool.or_eq_true, Bool.or_eq_true]
    rcases h with h | ⟨p, hp, -, hT⟩
    · exact Or.inl (Or.inl (t1_mem_of T S h))
    · have hT' : T ∈ p :: S := hT
      rcases List.mem_cons.mp hT' with e | e
      · rcases hp with ⟨a, ha, b, hb, hp⟩ | ⟨a, ha, hp⟩
        · left; right
          apply t1_one_of T S a b ha hb
          rcases hp with hp | hp
          · exact Or.inl (hp.symm.trans e.symm)
          · exact Or.inr (hp.symm.trans e.symm)
        · right
          rw [List.any_eq_true]
          exact ⟨a, ha, by rw [beq_iff_eq, ← hp, e]⟩
      · exact Or.inl (Or.inl (t1_mem_of T S e))
  | r + 2, S, h => by
    rw [rv_nreach_two, Bool.or_eq_true, Bool.or_eq_true]
    rcases h with h | ⟨p, hp, hpS, h1⟩
    · exact Or.inl (Or.inl (t1_mem_of T S h))
    · have hr := rv_nreach_sound F T (r + 1) (p :: S) h1
      have hm := t1_mem_false p S hpS
      rcases hp with ⟨a, ha, b, hb, hp⟩ | ⟨a, ha, hp⟩
      · left; right
        have hsym : ∀ x y,
            (fun a b => (!t1_mem (a &&& b) S && rv_nreach F T (r + 1) ((a &&& b) :: S)) ||
              (!t1_mem (a ||| b) S && rv_nreach F T (r + 1) ((a ||| b) :: S))) x y =
            (fun a b => (!t1_mem (a &&& b) S && rv_nreach F T (r + 1) ((a &&& b) :: S)) ||
              (!t1_mem (a ||| b) S && rv_nreach F T (r + 1) ((a ||| b) :: S))) y x := by
          intro x y
          show ((!t1_mem (x &&& y) S && rv_nreach F T (r + 1) ((x &&& y) :: S)) ||
              (!t1_mem (x ||| y) S && rv_nreach F T (r + 1) ((x ||| y) :: S))) =
            ((!t1_mem (y &&& x) S && rv_nreach F T (r + 1) ((y &&& x) :: S)) ||
              (!t1_mem (y ||| x) S && rv_nreach F T (r + 1) ((y ||| x) :: S)))
          rw [t1_land_comm x y, t1_lor_comm x y]
        refine t1_pany_of _ hsym S a b ha hb ?_
        rcases hp with hp | hp
        · subst hp; simp [hr, hm]
        · subst hp; simp [hr, hm]
      · right
        rw [List.any_eq_true]
        refine ⟨a, ha, ?_⟩
        subst hp
        simp [hr, hm]

def rv_inp (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (k : ℕ) : List Bool :=
  PEqualNP.Represents.oneEach (n := n) (m := m) ⟨k / m % n, Nat.mod_lt _ hn⟩ ⟨k % m, Nat.mod_lt _ hm⟩

theorem rv_inp_len (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (k : ℕ) : (rv_inp n m hn hm k).length = n + m := by
  simp [rv_inp, PEqualNP.Represents.oneEach]

def rv_lit (n k : ℕ) : List Bool :=
  List.ofFn (fun i : Fin n => k.testBit i.val) ++ List.ofFn (fun i : Fin n => !k.testBit i.val)

theorem rv_lit_len (n k : ℕ) : (rv_lit n k).length = n + n := by
  simp [rv_lit]

def rv_bin (n k : ℕ) : List Bool := List.ofFn (fun i : Fin n => k.testBit i.val)

theorem rv_bin_len (n k : ℕ) : (rv_bin n k).length = n := by
  simp [rv_bin]

theorem rv1_lower (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (A : Fin n → Fin m → Bool) (s T F : ℕ) (B : List ℕ)
    (hT : t1_bits (fun k => A ⟨k / m % n, Nat.mod_lt _ hn⟩ ⟨k % m, Nat.mod_lt _ hm⟩) (n * m) = T)
    (hF : t1_bits (fun _ => true) (n * m) = F)
    (hB : ∀ u, u < n + m → t1_bits (fun k => (rv_inp n m hn hm k).getD u false) (n * m) ∈ B)
    (h0 : 0 ∈ B) (hc1 : t1_reach T s B = false) (hc2 : 0 < s → t1_reach T (s - 1) (F :: B) = false) :
    ¬ PEqualNP.Represents.RepSizeAtMost A s := by
  rintro ⟨C, hmo, hs, hr⟩
  subst hF
  have hG := rv_run (n * m) (n + m) (rv_inp n m hn hm) B C (rv_Stc (t1_bits (fun _ => true) (n * m)))
    (rv_inp_len n m hn hm) hB h0
    (fun j hj S hBS hS => by
      have hg := hmo _ (gateAt_mem hj)
      have hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by simpa using hg.1
      refine rv_gate_c _ S (fun k i => if i < n + m + j then val C (rv_inp n m hn hm k) i else false)
        _ _ hop hg.2 ?_ (hBS 0 h0)
      intro i _
      by_cases hi : i < n + m + j
      · simp only [hi, ↓reduceIte]
        exact hS i hi
      · simp only [hi, ↓reduceIte]
        rw [t1_bits_false]
        exact hBS 0 h0)
    s T hs (by
      rw [← hT]
      unfold rv_prof
      congr 1
      funext k
      exact hr ⟨k / m % n, Nat.mod_lt _ hn⟩ ⟨k % m, Nat.mod_lt _ hm⟩)
  exact rv_close _ T s B hG hc1 hc2

theorem rv2_lower (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (A : Fin n → Fin m → Bool) (s T : ℕ) (B : List ℕ)
    (hT : t1_bits (fun k => A ⟨k / m % n, Nat.mod_lt _ hn⟩ ⟨k % m, Nat.mod_lt _ hm⟩) (n * m) = T)
    (hB : ∀ u, u < n + m → t1_bits (fun k => (rv_inp n m hn hm k).getD u false) (n * m) ∈ B)
    (h0 : 0 ∈ B) (hc : t1_reach T s B = false) : ¬ PEqualNP.Represents.RepSize2AtMost A s := by
  rintro ⟨C, hao, hs, hr⟩
  have hG := rv_run (n * m) (n + m) (rv_inp n m hn hm) B C t1_Step (rv_inp_len n m hn hm) hB h0
    (fun j hj S hBS hS => by
      have hgm := gateAt_mem hj
      have hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := andOrOnly_of_isAO2 hao _ hgm
      have hl : (gateAt C j).inputs.length = 2 := isAO2_len hao hgm
      refine rv_gate_ao _ S (fun k i => if i < n + m + j then val C (rv_inp n m hn hm k) i else false)
        _ _ hop (by omega) ?_ (hBS 0 h0) (fun h => absurd hl (by omega))
      intro i _
      by_cases hi : i < n + m + j
      · simp only [hi, ↓reduceIte]
        exact hS i hi
      · simp only [hi, ↓reduceIte]
        rw [t1_bits_false]
        exact hBS 0 h0)
    s T hs (by
      rw [← hT]
      unfold rv_prof
      congr 1
      funext k
      exact hr ⟨k / m % n, Nat.mod_lt _ hn⟩ ⟨k % m, Nat.mod_lt _ hm⟩)
  have h2 := t1_reach_sound T s B (rv_Gf_t1 T s B (rv_G_Gf t1_Step rv_t1_mono T s B hG))
  rw [hc] at h2
  exact Bool.false_ne_true h2

theorem rvl_lower (n : ℕ) (f : (Fin n → Bool) → Bool) (s T F : ℕ) (B : List ℕ)
    (hT : t1_bits (fun k => f (bm_input n k)) (2 ^ n) = T)
    (hF : t1_bits (fun _ => true) (2 ^ n) = F)
    (hB : ∀ u, u < n + n → t1_bits (fun k => (rv_lit n k).getD u false) (2 ^ n) ∈ B)
    (h0 : 0 ∈ B) (hc1 : t1_reach T s B = false) (hc2 : 0 < s → t1_reach T (s - 1) (F :: B) = false) :
    ¬ PEqualNP.Represents.HasLitSize n f s := by
  rintro ⟨C, hmo, hs, hr⟩
  subst hF
  have hG := rv_run (2 ^ n) (n + n) (rv_lit n) B C (rv_Stc (t1_bits (fun _ => true) (2 ^ n)))
    (rv_lit_len n) hB h0
    (fun j hj S hBS hS => by
      have hg := hmo _ (gateAt_mem hj)
      have hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by simpa using hg.1
      refine rv_gate_c _ S (fun k i => if i < n + n + j then val C (rv_lit n k) i else false)
        _ _ hop hg.2 ?_ (hBS 0 h0)
      intro i _
      by_cases hi : i < n + n + j
      · simp only [hi, ↓reduceIte]
        exact hS i hi
      · simp only [hi, ↓reduceIte]
        rw [t1_bits_false]
        exact hBS 0 h0)
    s T hs (by
      rw [← hT]
      unfold rv_prof
      congr 1
      funext k
      exact hr (bm_input n k))
  exact rv_close _ T s B hG hc1 hc2

theorem rvg_lower (n : ℕ) (f : (Fin n → Bool) → Bool) (s T F : ℕ) (B : List ℕ)
    (hT : t1_bits (fun k => f (bm_input n k)) (2 ^ n) = T)
    (hF : t1_bits (fun _ => true) (2 ^ n) = F)
    (hB : ∀ u, u < n → t1_bits (fun k => (rv_bin n k).getD u false) (2 ^ n) ∈ B)
    (h0 : 0 ∈ B) (hc : rv_nreach F T s B = false) : ¬ HasCircuitSize n f s := by
  rintro ⟨C, hfan, hs, hr⟩
  subst hF
  have hG := rv_run (2 ^ n) n (rv_bin n) B C (rv_StepN (t1_bits (fun _ => true) (2 ^ n)))
    (rv_bin_len n) hB h0
    (fun j hj S hBS hS => by
      have hg := hfan _ (gateAt_mem hj)
      have hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or ∨
          (gateAt C j).op = GateOp.not := by simpa using hg.1
      refine rv_gate_fan _ S (fun k i => if i < n + j then val C (rv_bin n k) i else false)
        _ _ hop hg.2 ?_ (hBS 0 h0)
      intro i _
      by_cases hi : i < n + j
      · simp only [hi, ↓reduceIte]
        exact hS i hi
      · simp only [hi, ↓reduceIte]
        rw [t1_bits_false]
        exact hBS 0 h0)
    s T hs (by
      rw [← hT]
      unfold rv_prof
      congr 1
      funext k
      exact hr (bm_input n k))
  have h2 := rv_nreach_sound _ T s B (rv_G_Gf _ (rv_n_mono _) T s B hG)
  rw [hc] at h2
  exact Bool.false_ne_true h2


def rv_okn : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | GateOp.not => true
  | GateOp.mod _ => false
  | GateOp.maj => false

theorem rv_fan2 (C : Circuit)
    (h : C.gates.all (fun g => rv_okn g.op && decide (g.inputs.length ≤ 2)) = true) :
    FanInTwo C := by
  intro g hg
  have h2 := List.all_eq_true.mp h g hg
  rcases g with ⟨op, ins⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
  refine ⟨?_, h2.2⟩
  have h3 := h2.1
  cases op <;> simp [rv_okn] at h3 ⊢

theorem rvr_lower (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (A : Fin n → Fin m → Bool) (s T F : ℕ)
    (B : List ℕ)
    (hT : t1_bits (fun k => A ⟨k / m % n, Nat.mod_lt _ hn⟩ ⟨k % m, Nat.mod_lt _ hm⟩) (n * m) = T)
    (hF : t1_bits (fun _ => true) (n * m) = F)
    (hB : ∀ u, u < n + m → t1_bits (fun k => (rv_inp n m hn hm k).getD u false) (n * m) ∈ B)
    (h0 : 0 ∈ B) (hc : rv_nreach F T s B = false) (C : Circuit)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C) (hs : C.size ≤ s)
    (hr : PEqualNP.Represents.Represents A C) : False := by
  subst hF
  have hG := rv_run (n * m) (n + m) (rv_inp n m hn hm) B C
    (rv_StepN (t1_bits (fun _ => true) (n * m))) (rv_inp_len n m hn hm) hB h0
    (fun j hj S hBS hS => by
      have hg := hfan _ (gateAt_mem hj)
      have hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or ∨
          (gateAt C j).op = GateOp.not := by simpa using hg.1
      refine rv_gate_fan _ S (fun k i => if i < n + m + j then val C (rv_inp n m hn hm k) i else false)
        _ _ hop hg.2 ?_ (hBS 0 h0)
      intro i _
      by_cases hi : i < n + m + j
      · simp only [hi, ↓reduceIte]
        exact hS i hi
      · simp only [hi, ↓reduceIte]
        rw [t1_bits_false]
        exact hBS 0 h0)
    s T hs (by
      rw [← hT]
      unfold rv_prof
      congr 1
      funext k
      exact hr ⟨k / m % n, Nat.mod_lt _ hn⟩ ⟨k % m, Nat.mod_lt _ hm⟩)
  have h2 := rv_nreach_sound _ T s B (rv_G_Gf _ (rv_n_mono _) T s B hG)
  rw [hc] at h2
  exact Bool.false_ne_true h2

theorem main_aux : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents (fun u v : Fin 2 => decide (u = v)) C → 3 ≤ C.size := by
  intro C hF hR
  by_contra hlt
  exact rvr_lower 2 2 (by norm_num) (by norm_num) _ 2 9 15 [0, 3, 12, 5, 10]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)
    C hF (by omega) hR

end PEqualNP.Outside.L_meta_17213

theorem PEqualNP.Outside.L_meta_17213 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents (fun u v : Fin 2 => decide (u = v)) C → 3 ≤ C.size :=
  PEqualNP.Outside.L_meta_17213.main_aux
