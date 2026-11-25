import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9022

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

-- FRAGMENT restrict    DEPENDS: fold mono
-- Dropping a set S of gates that no kept gate reads (S read-closed), with renumbering of the kept wires
-- (rows 2774, 3312). Reading back with an offset (RBo) for gate lists built piece by piece.
-- Abbreviation: hcl = for all k < C.gates.length, k not in S -> for all i in (gateAt C k).inputs, i < n or i - n not in S.
-- Exports:
--   def RBo b gs : for all p < gs.length, every input i of gs.getD p (OR of nothing) has i < b + p
--       (RBo n C.gates is ReadsBack n C by unfolding; RBo n D.gates proves the ReadsBack part of IsAO2 n D)
--   RBo_nil b ;  RBo_cons (all inputs of g below b) (RBo (b + 1) gs) : RBo b (g :: gs)
--   RBo_append (RBo b g1) (RBo (b + g1.length) g2) : RBo b (g1 ++ g2)
--   def keepL S m := (List.range m).filter (not in S) ;  def rk S m := (keepL S m).length (new index of old gate m)
--   def rn n S w := if w < n then w else n + rk S (w - n)  (new wire of old wire w)
--   def mkG n C S j := gate j with inputs mapped by rn n S ;  def Dg n C S m := (keepL S m).map (mkG n C S)
--   keepL_succ_in / keepL_succ_out, Dg_succ_in (m in S) : Dg (m+1) = Dg m ;  Dg_succ_out : Dg (m+1) = Dg m ++ [mkG m]
--   rk_mono (a <= b) : rk S a <= rk S b ;  rk_lt (j < m) (j not in S) : rk S j < rk S m ;  rk_succ_out (m not in S) : rk S (m+1) = rk S m + 1
--   rn_lt (i < n + m) (i < n or i - n not in S) : rn n S i < n + rk S m ;  rn_gate : rn n S (n + o) = n + rk S o
--   Dg_len : (Dg n C S m).length = rk S m ;  keep_gate : j in keepL S C.gates.length -> gateAt C j in C.gates
--   restrict_val (ReadsBack n C) hcl (x.length = n) : for m <= len, (W (Dg n C S m) x).length = n + rk S m and
--       for every w < n + m with (w < n or w - n not in S), (W (Dg n C S m) x).getD (rn n S w) false = val C x w
--   restrict_rb (ReadsBack n C) hcl : m <= len -> RBo n (Dg n C S m)
--   restrict_size (all j in S below len) : (Dg n C S C.gates.length).length + S.card <= C.gates.length
--   restrict_circ (IsAO2 n C) hcl (S below len) (o < len, o not in S, C.output = n + o) :
--       exists D, IsAO2 n D and circuitFun n D = circuitFun n C and D.size + S.card <= C.size
--       (D = the circuit with gates Dg n C S C.gates.length and output n + rk S o)
-- Use: pick the dead set S, prove hcl, then restrict_circ; for other gate shapes use restrict_val / restrict_rb directly
-- (keep_gate transports per-gate properties such as op or fan-in). For S = gates outside the output cone see frag live.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def RBo (b : ℕ) (gs : List Gate) : Prop :=
  ∀ p < gs.length, ∀ i ∈ (gs.getD p ⟨GateOp.or, []⟩).inputs, i < b + p

theorem RBo_nil (b : ℕ) : RBo b [] := by
  intro p hp
  simp at hp

theorem RBo_cons (b : ℕ) (g : Gate) (gs : List Gate) (hg : ∀ i ∈ g.inputs, i < b)
    (h : RBo (b + 1) gs) : RBo b (g :: gs) := by
  intro p hp i hi
  cases p with
  | zero =>
    have hi' : i ∈ g.inputs := hi
    have := hg i hi'
    omega
  | succ q =>
    have hq : q < gs.length := by
      rw [List.length_cons] at hp
      omega
    have hi' : i ∈ (gs.getD q ⟨GateOp.or, []⟩).inputs := hi
    have := h q hq i hi'
    omega

theorem RBo_append (b : ℕ) (g1 g2 : List Gate) (h1 : RBo b g1)
    (h2 : RBo (b + g1.length) g2) : RBo b (g1 ++ g2) := by
  intro p hp i hi
  by_cases hlt : p < g1.length
  · rw [List.getD_append _ _ _ _ hlt] at hi
    exact h1 p hlt i hi
  · have hge : g1.length ≤ p := by omega
    rw [List.getD_append_right _ _ _ _ hge] at hi
    have hp2 : p - g1.length < g2.length := by
      rw [List.length_append] at hp
      omega
    have := h2 (p - g1.length) hp2 i hi
    omega

def keepL (S : Finset ℕ) (m : ℕ) : List ℕ := (List.range m).filter (fun j => !decide (j ∈ S))

def rk (S : Finset ℕ) (m : ℕ) : ℕ := (keepL S m).length

def rn (n : ℕ) (S : Finset ℕ) (w : ℕ) : ℕ := if w < n then w else n + rk S (w - n)

def mkG (n : ℕ) (C : Circuit) (S : Finset ℕ) (j : ℕ) : Gate :=
  ⟨(gateAt C j).op, (gateAt C j).inputs.map (rn n S)⟩

def Dg (n : ℕ) (C : Circuit) (S : Finset ℕ) (m : ℕ) : List Gate := (keepL S m).map (mkG n C S)

theorem keepL_succ_in (S : Finset ℕ) (m : ℕ) (h : m ∈ S) : keepL S (m + 1) = keepL S m := by
  simp [keepL, List.range_succ, List.filter_append, h]

theorem keepL_succ_out (S : Finset ℕ) (m : ℕ) (h : m ∉ S) :
    keepL S (m + 1) = keepL S m ++ [m] := by
  simp [keepL, List.range_succ, List.filter_append, h]

theorem rk_mono (S : Finset ℕ) (a b : ℕ) (h : a ≤ b) : rk S a ≤ rk S b := by
  unfold rk keepL
  exact ((List.range_sublist.mpr h).filter _).length_le

theorem rk_succ_out (S : Finset ℕ) (m : ℕ) (h : m ∉ S) : rk S (m + 1) = rk S m + 1 := by
  unfold rk
  rw [keepL_succ_out S m h, List.length_append, List.length_singleton]

theorem rk_lt (S : Finset ℕ) (j m : ℕ) (hj : j < m) (hS : j ∉ S) : rk S j < rk S m := by
  have h1 := rk_succ_out S j hS
  have h2 := rk_mono S (j + 1) m hj
  omega

theorem rn_lt (n : ℕ) (S : Finset ℕ) (i m : ℕ) (hi : i < n + m) (hS : i < n ∨ i - n ∉ S) :
    rn n S i < n + rk S m := by
  unfold rn
  by_cases h : i < n
  · rw [if_pos h]
    omega
  · rw [if_neg h]
    have hS2 : i - n ∉ S := by
      rcases hS with h1 | h1
      · exact absurd h1 h
      · exact h1
    have := rk_lt S (i - n) m (by omega) hS2
    omega

theorem rn_gate (n : ℕ) (S : Finset ℕ) (o : ℕ) : rn n S (n + o) = n + rk S o := by
  unfold rn
  rw [if_neg (by omega), Nat.add_sub_cancel_left]

theorem Dg_succ_in (n : ℕ) (C : Circuit) (S : Finset ℕ) (m : ℕ) (h : m ∈ S) :
    Dg n C S (m + 1) = Dg n C S m := by
  unfold Dg
  rw [keepL_succ_in S m h]

theorem Dg_succ_out (n : ℕ) (C : Circuit) (S : Finset ℕ) (m : ℕ) (h : m ∉ S) :
    Dg n C S (m + 1) = Dg n C S m ++ [mkG n C S m] := by
  unfold Dg
  rw [keepL_succ_out S m h, List.map_append, List.map_singleton]

theorem Dg_len (n : ℕ) (C : Circuit) (S : Finset ℕ) (m : ℕ) : (Dg n C S m).length = rk S m := by
  unfold Dg rk
  rw [List.length_map]

theorem keep_gate (C : Circuit) (S : Finset ℕ) (j : ℕ) (hj : j ∈ keepL S C.gates.length) :
    gateAt C j ∈ C.gates := by
  have hjl : j < C.gates.length := by
    have := (List.mem_filter.mp hj).1
    exact List.mem_range.mp this
  exact gateAt_mem hjl

theorem restrict_val (n : ℕ) (C : Circuit) (S : Finset ℕ) (hRB : ReadsBack n C)
    (hcl : ∀ k < C.gates.length, k ∉ S → ∀ i ∈ (gateAt C k).inputs, i < n ∨ i - n ∉ S)
    (x : List Bool) (hx : x.length = n) :
    ∀ m, m ≤ C.gates.length →
      (W (Dg n C S m) x).length = n + rk S m ∧
      ∀ w, w < n + m → (w < n ∨ w - n ∉ S) →
        (W (Dg n C S m) x).getD (rn n S w) false = val C x w := by
  have hsn : ∀ (l : List Bool) (b : Bool) (k : ℕ), l.length = k → (l ++ [b]).getD k false = b := by
    intro l b k hk
    subst hk
    exact getD_app_len l b
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨?_, ?_⟩
    · rw [W_length, Dg_len, hx]
    · intro w hw _
      have hw' : w < n := by omega
      have e : rn n S w = w := by unfold rn; rw [if_pos hw']
      rw [e, W_prefix (Dg n C S 0) x w (by omega), val_input hx hw']
  | succ m ih =>
    intro hm
    obtain ⟨hlen, hval⟩ := ih (by omega)
    by_cases hS : m ∈ S
    · have e2 : rk S (m + 1) = rk S m := by unfold rk; rw [keepL_succ_in S m hS]
      rw [Dg_succ_in n C S m hS, e2]
      refine ⟨hlen, ?_⟩
      intro w hw hk
      have hne : w ≠ n + m := by
        intro hwe
        rcases hk with h1 | h1
        · omega
        · apply h1
          have : w - n = m := by omega
          rw [this]
          exact hS
      exact hval w (by omega) hk
    · rw [Dg_succ_out n C S m hS, rk_succ_out S m hS, W_append]
      have hsingle : ∀ v : List Bool, W [mkG n C S m] v =
          v ++ [(gateAt C m).op.eval (((gateAt C m).inputs.map (rn n S)).map
            fun i => v.getD i false)] :=
        fun v => rfl
      rw [hsingle]
      refine ⟨?_, ?_⟩
      · rw [List.length_append, List.length_singleton, hlen]
        omega
      · intro w hw hk
        by_cases hwm : w = n + m
        · subst hwm
          rw [rn_gate, hsn _ _ _ hlen, val_gate_rb hx (by omega) (hRB m (by omega)), List.map_map]
          congr 1
          apply List.map_congr_left
          intro i hi
          exact hval i (hRB m (by omega) i hi) (hcl m (by omega) hS i hi)
        · have hw2 : w < n + m := by omega
          rw [getD_app_lt _ _ _ (by rw [hlen]; exact rn_lt n S w m hw2 hk)]
          exact hval w hw2 hk

theorem restrict_rb (n : ℕ) (C : Circuit) (S : Finset ℕ) (hRB : ReadsBack n C)
    (hcl : ∀ k < C.gates.length, k ∉ S → ∀ i ∈ (gateAt C k).inputs, i < n ∨ i - n ∉ S) :
    ∀ m, m ≤ C.gates.length → RBo n (Dg n C S m) := by
  intro m
  induction m with
  | zero =>
    intro _
    exact RBo_nil n
  | succ m ih =>
    intro hm
    by_cases hS : m ∈ S
    · rw [Dg_succ_in n C S m hS]
      exact ih (by omega)
    · rw [Dg_succ_out n C S m hS]
      apply RBo_append _ _ _ (ih (by omega))
      apply RBo_cons _ _ _ _ (RBo_nil _)
      intro i hi
      have hi' : i ∈ (gateAt C m).inputs.map (rn n S) := hi
      obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hi'
      rw [Dg_len]
      exact rn_lt n S i0 m (hRB m (by omega) i0 hi0) (hcl m (by omega) hS i0 hi0)

theorem restrict_size (n : ℕ) (C : Circuit) (S : Finset ℕ) (hS : ∀ j ∈ S, j < C.gates.length) :
    (Dg n C S C.gates.length).length + S.card ≤ C.gates.length := by
  have h3 : (List.range C.gates.length).length =
      ((List.range C.gates.length).filter (fun j => decide (j ∈ S))).length +
      ((List.range C.gates.length).filter (fun j => !decide (j ∈ S))).length :=
    List.length_eq_length_filter_add _
  have h4 : S.card ≤ ((List.range C.gates.length).filter (fun j => decide (j ∈ S))).length := by
    refine le_trans (Finset.card_le_card ?_)
      (List.toFinset_card_le (l := (List.range C.gates.length).filter (fun j => decide (j ∈ S))))
    intro j hj
    rw [List.mem_toFinset, List.mem_filter]
    exact ⟨List.mem_range.mpr (hS j hj), by simpa using hj⟩
  have h5 : (Dg n C S C.gates.length).length =
      ((List.range C.gates.length).filter (fun j => !decide (j ∈ S))).length := Dg_len n C S _
  rw [List.length_range] at h3
  omega

theorem restrict_circ (n : ℕ) (C : Circuit) (S : Finset ℕ) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hcl : ∀ k < C.gates.length, k ∉ S → ∀ i ∈ (gateAt C k).inputs, i < n ∨ i - n ∉ S)
    (hS : ∀ j ∈ S, j < C.gates.length)
    (o : ℕ) (ho : o < C.gates.length) (hoS : o ∉ S) (hout : C.output = n + o) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ circuitFun n D = circuitFun n C ∧
      D.size + S.card ≤ C.size := by
  obtain ⟨hao, hRB, h2⟩ := hAO
  refine ⟨⟨Dg n C S C.gates.length, n + rk S o⟩, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g hg
    have hg' : g ∈ (keepL S C.gates.length).map (mkG n C S) := hg
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg'
    exact hao (gateAt C j) (keep_gate C S j hj)
  · exact restrict_rb n C S hRB hcl _ le_rfl
  · intro g hg
    have hg' : g ∈ (keepL S C.gates.length).map (mkG n C S) := hg
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg'
    have := h2 _ (keep_gate C S j hj)
    show ((gateAt C j).inputs.map (rn n S)).length = 2
    rw [List.length_map]
    exact this
  · funext x
    have h := (restrict_val n C S hRB hcl (List.ofFn x) (by simp) C.gates.length le_rfl).2 (n + o)
      (by omega) (Or.inr (by rw [Nat.add_sub_cancel_left]; exact hoS))
    rw [rn_gate] at h
    show (W (Dg n C S C.gates.length) (List.ofFn x)).getD (n + rk S o) false =
      val C (List.ofFn x) C.output
    rw [hout]
    exact h
  · exact restrict_size n C S hS

-- FRAGMENT orchain    DEPENDS: fold mono restrict
-- OR chains over a list of existing wires placed at an offset b (the first chain gate is wire b), stars
-- x_c AND (OR of a list) and blocks of several stars, with their values, lengths, ReadsBack (RBo) and gate shapes.
-- Exports (w : List Bool is the wire list before the block, w.length = b):
--   def ocg t L b : OR chain: gates OR(t, L0) at wire b, OR(b, L1) at wire b + 1, ... (L.length gates)
--   def octop t L b : its top wire (t if L = [], else b + L.length - 1) ;  octop_nil, octop_cons (L ne []) ;  octop_lt (t < b) : octop t L b < b + L.length
--   ocg_len : (ocg t L b).length = L.length ;  ocg_gate : g in ocg t L b -> g.op = or and g.inputs.length = 2
--   ocg_val (w.length = b) (t < b) (all of L < b) :
--       (W (ocg t L b) w).getD (octop t L b) false = true iff (w.getD t false = true or exists i in L, w.getD i false = true)
--   ocg_rb (t < b) (all of L < b) : RBo b (ocg t L b)
--   def ostar c L b : the star x_c AND OR(L): [] if L = [], else ocg L0 (tail) b ++ [AND(c, top)] (L.length gates, star wire b + L.length - 1)
--   ostar_len : (ostar c L b).length = L.length ;  ostar_gate : g in ostar c L b -> (op and or or) and 2 inputs
--   ostar_val (L ne []) (w.length = b) (c < b) (all of L < b) :
--       (W (ostar c L b) w).getD (b + L.length - 1) false = true iff (w.getD c false = true and exists i in L, w.getD i false = true)
--   ostar_rb (c < b) (all of L < b) : RBo b (ostar c L b)
--   def ostars Lf cs b : stars of the centres cs (list of wires, block of centre c uses the list Lf c), one after the other
--   def ostarW Lf cs b d : the star wire of the first occurrence of centre d in cs
--   ostars_len : (ostars Lf cs b).length = (cs.map fun c => (Lf c).length).sum ;  ostars_gate : shapes as ostar_gate
--   ostars_val (w.length = b) (all c in cs, c < b) (all c in cs, all i in Lf c, i < b) (d in cs) (Lf d ne []) :
--       ostarW Lf cs b d < b + (ostars Lf cs b).length and ((W (ostars Lf cs b) w).getD (ostarW Lf cs b d) false = true
--       iff (w.getD d false = true and exists i in Lf d, w.getD i false = true))
--   ostars_rb (same bounds) : RBo b (ostars Lf cs b)
--   def ochain L b := chain OR over L at b (L.length - 1 gates, [] for L = [] or one wire) ;  def ochainTop L b : its top wire
--   ochain_len ;  ochain_gate (OR, 2 inputs) ;  ochain_rb (all of L < b) : RBo b (ochain L b)
--   ochain_val (L ne []) (w.length = b) (all of L < b) : ochainTop L b < b + (ochain L b).length and
--       ((W (ochain L b) w).getD (ochainTop L b) false = true iff exists i in L, w.getD i false = true)
--   def ochains Lf Xs b / ochainsW Lf Xs b d : one chain per key X (over the wire list Lf X), one after the other, and the top of key d
--   ochains_len : length = (Xs.map fun X => (Lf X).length - 1).sum ;  ochains_gate ;  ochains_rb (all wires < b)
--   ochains_val (w.length = b) (all wires < b) (d in Xs) (Lf d ne []) : ochainsW < b + length and
--       (value at ochainsW iff exists i in Lf d, w.getD i false = true)
--   oc_ex (all i in L, w1.getD i false = w.getD i false) : (exists i in L, w1 true) iff (exists i in L, w true)
-- Use: as the middle block of frag reorder (block placed after the kept head part, b = n + head part length); the star
-- wire values then come from ostars_val with w = the run of the head part, and frag reorder transports them.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def ocg : ℕ → List ℕ → ℕ → List Gate
  | _, [], _ => []
  | t, i :: L, b => ⟨GateOp.or, [t, i]⟩ :: ocg b L (b + 1)

def octop : ℕ → List ℕ → ℕ → ℕ
  | t, [], _ => t
  | _, _ :: L, b => octop b L (b + 1)

theorem oc_ex (L : List ℕ) (w1 w : List Bool) (h : ∀ i ∈ L, w1.getD i false = w.getD i false) :
    (∃ i ∈ L, w1.getD i false = true) ↔ (∃ i ∈ L, w.getD i false = true) := by
  constructor
  · rintro ⟨i, hi, h1⟩
    exact ⟨i, hi, by rw [← h i hi]; exact h1⟩
  · rintro ⟨i, hi, h1⟩
    exact ⟨i, hi, by rw [h i hi]; exact h1⟩

theorem ocg_len (L : List ℕ) : ∀ (t b : ℕ), (ocg t L b).length = L.length := by
  induction L with
  | nil => intro t b; rfl
  | cons i L ih =>
    intro t b
    show (ocg b L (b + 1)).length + 1 = L.length + 1
    rw [ih]

theorem octop_nil (t b : ℕ) : octop t [] b = t := rfl

theorem octop_cons (L : List ℕ) : ∀ (t b : ℕ), L ≠ [] → octop t L b = b + L.length - 1 := by
  induction L with
  | nil => intro t b h; exact absurd rfl h
  | cons i L ih =>
    intro t b _
    show octop b L (b + 1) = b + (L.length + 1) - 1
    by_cases h : L = []
    · subst h
      rfl
    · rw [ih b (b + 1) h]
      omega

theorem octop_lt (L : List ℕ) (t b : ℕ) (ht : t < b) : octop t L b < b + L.length := by
  by_cases h : L = []
  · subst h
    rw [octop_nil]
    simp
    exact ht
  · rw [octop_cons L t b h]
    have : L.length ≠ 0 := by
      intro h0
      exact h (List.length_eq_zero_iff.mp h0)
    omega

theorem ocg_gate (L : List ℕ) : ∀ (t b : ℕ) (g : Gate), g ∈ ocg t L b →
    g.op = GateOp.or ∧ g.inputs.length = 2 := by
  induction L with
  | nil => intro t b g hg; simp [ocg] at hg
  | cons i L ih =>
    intro t b g hg
    have hg' : g ∈ (⟨GateOp.or, [t, i]⟩ : Gate) :: ocg b L (b + 1) := hg
    rcases List.mem_cons.mp hg' with h1 | h1
    · subst h1
      exact ⟨rfl, rfl⟩
    · exact ih b (b + 1) g h1

theorem ocg_val (L : List ℕ) : ∀ (t b : ℕ) (w : List Bool), w.length = b → t < b → (∀ i ∈ L, i < b) →
    ((W (ocg t L b) w).getD (octop t L b) false = true ↔
      (w.getD t false = true ∨ ∃ i ∈ L, w.getD i false = true)) := by
  induction L with
  | nil =>
    intro t b w _ _ _
    simp [ocg, octop, W_nil]
  | cons i L ih =>
    intro t b w hw ht hL
    have hi : i < b := hL i (List.mem_cons.mpr (Or.inl rfl))
    have hL2 : ∀ a ∈ L, a < b := fun a ha => hL a (List.mem_cons.mpr (Or.inr ha))
    have hs : ∀ a, a < b → (step w ⟨GateOp.or, [t, i]⟩).getD a false = w.getD a false :=
      fun a ha => step_lt w _ a (by omega)
    have hb : (step w ⟨GateOp.or, [t, i]⟩).getD b false = (w.getD t false || w.getD i false) := by
      rw [step_last w _ b hw.symm]
      simp [GateOp.eval]
    show (W (ocg b L (b + 1)) (step w ⟨GateOp.or, [t, i]⟩)).getD (octop b L (b + 1)) false = true ↔ _
    rw [ih b (b + 1) _ (by rw [step_len, hw]) (by omega) (fun a ha => by have := hL2 a ha; omega)]
    rw [hb, oc_ex L _ w (fun a ha => hs a (hL2 a ha))]
    constructor
    · rintro (h | ⟨a, ha, h⟩)
      · simp only [Bool.or_eq_true] at h
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr ⟨i, List.mem_cons.mpr (Or.inl rfl), h⟩
      · exact Or.inr ⟨a, List.mem_cons.mpr (Or.inr ha), h⟩
    · rintro (h | ⟨a, ha, h⟩)
      · exact Or.inl (by rw [h]; rfl)
      · rcases List.mem_cons.mp ha with h2 | ha2
        · subst h2
          exact Or.inl (by rw [h, Bool.or_true])
        · exact Or.inr ⟨a, ha2, h⟩

theorem ocg_rb (L : List ℕ) : ∀ (t b : ℕ), t < b → (∀ i ∈ L, i < b) → RBo b (ocg t L b) := by
  induction L with
  | nil => intro t b _ _; exact RBo_nil b
  | cons i L ih =>
    intro t b ht hL
    have hi : i < b := hL i (List.mem_cons.mpr (Or.inl rfl))
    apply RBo_cons
    · intro a ha
      have ha' : a ∈ [t, i] := ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha'
      rcases ha' with h | h <;> omega
    · exact ih b (b + 1) (by omega)
        (fun a ha => by have := hL a (List.mem_cons.mpr (Or.inr ha)); omega)

def ostar : ℕ → List ℕ → ℕ → List Gate
  | _, [], _ => []
  | c, i :: L, b => ocg i L b ++ [⟨GateOp.and, [c, octop i L b]⟩]

theorem ostar_len (c : ℕ) (L : List ℕ) (b : ℕ) : (ostar c L b).length = L.length := by
  cases L with
  | nil => rfl
  | cons i L =>
    show (ocg i L b ++ [_]).length = L.length + 1
    rw [List.length_append, ocg_len]
    rfl

theorem ostar_gate (c : ℕ) (L : List ℕ) (b : ℕ) (g : Gate) (hg : g ∈ ostar c L b) :
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  cases L with
  | nil => simp [ostar] at hg
  | cons i L =>
    have hg' : g ∈ ocg i L b ++ [⟨GateOp.and, [c, octop i L b]⟩] := hg
    rcases List.mem_append.mp hg' with h1 | h1
    · have := ocg_gate L i b g h1
      exact ⟨Or.inr this.1, this.2⟩
    · rw [List.mem_singleton] at h1
      subst h1
      exact ⟨Or.inl rfl, rfl⟩

theorem ostar_val (c : ℕ) (L : List ℕ) (b : ℕ) (w : List Bool) (hL0 : L ≠ []) (hw : w.length = b)
    (hc : c < b) (hL : ∀ i ∈ L, i < b) :
    ((W (ostar c L b) w).getD (b + L.length - 1) false = true ↔
      (w.getD c false = true ∧ ∃ i ∈ L, w.getD i false = true)) := by
  cases L with
  | nil => exact absurd rfl hL0
  | cons i L =>
    have hi : i < b := hL i (List.mem_cons.mpr (Or.inl rfl))
    have hL2 : ∀ a ∈ L, a < b := fun a ha => hL a (List.mem_cons.mpr (Or.inr ha))
    show (W (ocg i L b ++ [⟨GateOp.and, [c, octop i L b]⟩]) w).getD (b + (L.length + 1) - 1) false = true ↔ _
    have hlen : (W (ocg i L b) w).length = b + L.length := by rw [W_length, ocg_len, hw]
    rw [W_snoc, step_last _ _ _ (by rw [hlen]; omega)]
    have h1 : (W (ocg i L b) w).getD c false = w.getD c false := W_prefix _ w c (by omega)
    have h2 := ocg_val L i b w hw hi hL2
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
      Bool.and_true, Bool.and_eq_true]
    rw [h1, h2]
    constructor
    · rintro ⟨hc1, h | ⟨a, ha, h⟩⟩
      · exact ⟨hc1, i, List.mem_cons.mpr (Or.inl rfl), h⟩
      · exact ⟨hc1, a, List.mem_cons.mpr (Or.inr ha), h⟩
    · rintro ⟨hc1, a, ha, h⟩
      refine ⟨hc1, ?_⟩
      rcases List.mem_cons.mp ha with h3 | h3
      · subst h3
        exact Or.inl h
      · exact Or.inr ⟨a, h3, h⟩

theorem ostar_rb (c : ℕ) (L : List ℕ) (b : ℕ) (hc : c < b) (hL : ∀ i ∈ L, i < b) :
    RBo b (ostar c L b) := by
  cases L with
  | nil => exact RBo_nil b
  | cons i L =>
    have hi : i < b := hL i (List.mem_cons.mpr (Or.inl rfl))
    have hL2 : ∀ a ∈ L, a < b := fun a ha => hL a (List.mem_cons.mpr (Or.inr ha))
    show RBo b (ocg i L b ++ [⟨GateOp.and, [c, octop i L b]⟩])
    apply RBo_append _ _ _ (ocg_rb L i b hi hL2)
    apply RBo_cons _ _ _ _ (RBo_nil _)
    intro a ha
    have ha' : a ∈ [c, octop i L b] := ha
    have htop := octop_lt L i b hi
    rw [ocg_len]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha'
    rcases ha' with h | h <;> omega

def ostars (Lf : ℕ → List ℕ) : List ℕ → ℕ → List Gate
  | [], _ => []
  | c :: cs, b => ostar c (Lf c) b ++ ostars Lf cs (b + (Lf c).length)

def ostarW (Lf : ℕ → List ℕ) : List ℕ → ℕ → ℕ → ℕ
  | [], _, _ => 0
  | c :: cs, b, d => if c = d then b + (Lf c).length - 1 else ostarW Lf cs (b + (Lf c).length) d

theorem ostars_len (Lf : ℕ → List ℕ) (cs : List ℕ) : ∀ b,
    (ostars Lf cs b).length = (cs.map fun c => (Lf c).length).sum := by
  induction cs with
  | nil => intro b; rfl
  | cons c cs ih =>
    intro b
    show (ostar c (Lf c) b ++ ostars Lf cs (b + (Lf c).length)).length = _
    rw [List.length_append, ostar_len, ih, List.map_cons, List.sum_cons]

theorem ostars_gate (Lf : ℕ → List ℕ) (cs : List ℕ) : ∀ b (g : Gate), g ∈ ostars Lf cs b →
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  induction cs with
  | nil => intro b g hg; simp [ostars] at hg
  | cons c cs ih =>
    intro b g hg
    have hg' : g ∈ ostar c (Lf c) b ++ ostars Lf cs (b + (Lf c).length) := hg
    rcases List.mem_append.mp hg' with h1 | h1
    · exact ostar_gate c (Lf c) b g h1
    · exact ih _ g h1

theorem ostars_rb (Lf : ℕ → List ℕ) (cs : List ℕ) : ∀ b, (∀ c ∈ cs, c < b) →
    (∀ c ∈ cs, ∀ i ∈ Lf c, i < b) → RBo b (ostars Lf cs b) := by
  induction cs with
  | nil => intro b _ _; exact RBo_nil b
  | cons c cs ih =>
    intro b hc hi
    show RBo b (ostar c (Lf c) b ++ ostars Lf cs (b + (Lf c).length))
    apply RBo_append _ _ _ (ostar_rb c (Lf c) b (hc c (List.mem_cons.mpr (Or.inl rfl)))
      (hi c (List.mem_cons.mpr (Or.inl rfl))))
    rw [ostar_len]
    apply ih
    · intro d hd
      have := hc d (List.mem_cons.mpr (Or.inr hd))
      omega
    · intro d hd i hi2
      have := hi d (List.mem_cons.mpr (Or.inr hd)) i hi2
      omega

theorem ostars_val (Lf : ℕ → List ℕ) (cs : List ℕ) : ∀ (b : ℕ) (w : List Bool), w.length = b →
    (∀ c ∈ cs, c < b) → (∀ c ∈ cs, ∀ i ∈ Lf c, i < b) → ∀ d ∈ cs, Lf d ≠ [] →
    ostarW Lf cs b d < b + (ostars Lf cs b).length ∧
    ((W (ostars Lf cs b) w).getD (ostarW Lf cs b d) false = true ↔
      (w.getD d false = true ∧ ∃ i ∈ Lf d, w.getD i false = true)) := by
  induction cs with
  | nil => intro b w _ _ _ d hd; simp at hd
  | cons c cs ih =>
    intro b w hw hc hi d hd hLd
    have hc0 : c < b := hc c (List.mem_cons.mpr (Or.inl rfl))
    have hi0 : ∀ i ∈ Lf c, i < b := hi c (List.mem_cons.mpr (Or.inl rfl))
    have hlen1 : (W (ostar c (Lf c) b) w).length = b + (Lf c).length := by
      rw [W_length, ostar_len, hw]
    have hpre : ∀ a, a < b → (W (ostar c (Lf c) b) w).getD a false = w.getD a false :=
      fun a ha => W_prefix _ w a (by omega)
    have eW : W (ostars Lf (c :: cs) b) w = W (ostars Lf cs (b + (Lf c).length)) (W (ostar c (Lf c) b) w) :=
      W_append _ _ w
    have eL : (ostars Lf (c :: cs) b).length = (Lf c).length + (ostars Lf cs (b + (Lf c).length)).length := by
      show (ostar c (Lf c) b ++ ostars Lf cs (b + (Lf c).length)).length = _
      rw [List.length_append, ostar_len]
    rw [eW, eL]
    by_cases hcd : c = d
    · subst hcd
      have ew : ostarW Lf (c :: cs) b c = b + (Lf c).length - 1 := by
        show (if c = c then b + (Lf c).length - 1 else _) = _
        rw [if_pos rfl]
      have hpos : (Lf c).length ≠ 0 := by
        intro h0
        exact hLd (List.length_eq_zero_iff.mp h0)
      rw [ew]
      refine ⟨by omega, ?_⟩
      rw [W_prefix _ _ _ (by omega)]
      exact ostar_val c (Lf c) b w hLd hw hc0 hi0
    · have ew : ostarW Lf (c :: cs) b d = ostarW Lf cs (b + (Lf c).length) d := by
        show (if c = d then b + (Lf c).length - 1 else _) = _
        rw [if_neg hcd]
      have hd2 : d ∈ cs := by
        rcases List.mem_cons.mp hd with h | h
        · exact absurd h.symm hcd
        · exact h
      have hcs : ∀ e ∈ cs, e < b := fun e he => hc e (List.mem_cons.mpr (Or.inr he))
      have his : ∀ e ∈ cs, ∀ i ∈ Lf e, i < b := fun e he => hi e (List.mem_cons.mpr (Or.inr he))
      obtain ⟨h1, h2⟩ := ih (b + (Lf c).length) _ hlen1
        (fun e he => by have := hcs e he; omega)
        (fun e he i hi2 => by have := his e he i hi2; omega) d hd2 hLd
      rw [ew]
      refine ⟨by omega, ?_⟩
      rw [h2, hpre d (hcs d hd2), oc_ex (Lf d) _ w (fun i hi2 => hpre i (his d hd2 i hi2))]

def ochain : List ℕ → ℕ → List Gate
  | [], _ => []
  | i :: L, b => ocg i L b

def ochainTop : List ℕ → ℕ → ℕ
  | [], _ => 0
  | i :: L, b => octop i L b

theorem ochain_len (L : List ℕ) (b : ℕ) : (ochain L b).length = L.length - 1 := by
  cases L with
  | nil => rfl
  | cons i L =>
    show (ocg i L b).length = L.length + 1 - 1
    rw [ocg_len]
    omega

theorem ochain_gate (L : List ℕ) (b : ℕ) (g : Gate) (hg : g ∈ ochain L b) :
    g.op = GateOp.or ∧ g.inputs.length = 2 := by
  cases L with
  | nil => simp [ochain] at hg
  | cons i L => exact ocg_gate L i b g hg

theorem ochain_rb (L : List ℕ) (b : ℕ) (hL : ∀ i ∈ L, i < b) : RBo b (ochain L b) := by
  cases L with
  | nil => exact RBo_nil b
  | cons i L =>
    exact ocg_rb L i b (hL i (List.mem_cons.mpr (Or.inl rfl)))
      (fun a ha => hL a (List.mem_cons.mpr (Or.inr ha)))

theorem ochain_val (L : List ℕ) (b : ℕ) (w : List Bool) (hL0 : L ≠ []) (hw : w.length = b)
    (hL : ∀ i ∈ L, i < b) :
    ochainTop L b < b + (ochain L b).length ∧
    ((W (ochain L b) w).getD (ochainTop L b) false = true ↔ ∃ i ∈ L, w.getD i false = true) := by
  cases L with
  | nil => exact absurd rfl hL0
  | cons i L =>
    have hi : i < b := hL i (List.mem_cons.mpr (Or.inl rfl))
    have hL2 : ∀ a ∈ L, a < b := fun a ha => hL a (List.mem_cons.mpr (Or.inr ha))
    refine ⟨?_, ?_⟩
    · show octop i L b < b + (ocg i L b).length
      rw [ocg_len]
      exact octop_lt L i b hi
    · show (W (ocg i L b) w).getD (octop i L b) false = true ↔ _
      rw [ocg_val L i b w hw hi hL2]
      constructor
      · rintro (h | ⟨a, ha, h⟩)
        · exact ⟨i, List.mem_cons.mpr (Or.inl rfl), h⟩
        · exact ⟨a, List.mem_cons.mpr (Or.inr ha), h⟩
      · rintro ⟨a, ha, h⟩
        rcases List.mem_cons.mp ha with h2 | h2
        · subst h2
          exact Or.inl h
        · exact Or.inr ⟨a, h2, h⟩

def ochains (Lf : ℕ → List ℕ) : List ℕ → ℕ → List Gate
  | [], _ => []
  | X :: Xs, b => ochain (Lf X) b ++ ochains Lf Xs (b + (ochain (Lf X) b).length)

def ochainsW (Lf : ℕ → List ℕ) : List ℕ → ℕ → ℕ → ℕ
  | [], _, _ => 0
  | X :: Xs, b, d => if X = d then ochainTop (Lf X) b else ochainsW Lf Xs (b + (ochain (Lf X) b).length) d

theorem ochains_len (Lf : ℕ → List ℕ) (Xs : List ℕ) : ∀ b,
    (ochains Lf Xs b).length = (Xs.map fun X => (Lf X).length - 1).sum := by
  induction Xs with
  | nil => intro b; rfl
  | cons X Xs ih =>
    intro b
    show (ochain (Lf X) b ++ ochains Lf Xs (b + (ochain (Lf X) b).length)).length = _
    rw [List.length_append, ochain_len, ih, List.map_cons, List.sum_cons]

theorem ochains_gate (Lf : ℕ → List ℕ) (Xs : List ℕ) : ∀ b (g : Gate), g ∈ ochains Lf Xs b →
    g.op = GateOp.or ∧ g.inputs.length = 2 := by
  induction Xs with
  | nil => intro b g hg; simp [ochains] at hg
  | cons X Xs ih =>
    intro b g hg
    have hg' : g ∈ ochain (Lf X) b ++ ochains Lf Xs (b + (ochain (Lf X) b).length) := hg
    rcases List.mem_append.mp hg' with h1 | h1
    · exact ochain_gate (Lf X) b g h1
    · exact ih _ g h1

theorem ochains_rb (Lf : ℕ → List ℕ) (Xs : List ℕ) : ∀ b, (∀ X ∈ Xs, ∀ i ∈ Lf X, i < b) →
    RBo b (ochains Lf Xs b) := by
  induction Xs with
  | nil => intro b _; exact RBo_nil b
  | cons X Xs ih =>
    intro b hi
    show RBo b (ochain (Lf X) b ++ ochains Lf Xs (b + (ochain (Lf X) b).length))
    apply RBo_append _ _ _ (ochain_rb (Lf X) b (hi X (List.mem_cons.mpr (Or.inl rfl))))
    apply ih
    intro d hd i hi2
    have := hi d (List.mem_cons.mpr (Or.inr hd)) i hi2
    omega

theorem ochains_val (Lf : ℕ → List ℕ) (Xs : List ℕ) : ∀ (b : ℕ) (w : List Bool), w.length = b →
    (∀ X ∈ Xs, ∀ i ∈ Lf X, i < b) → ∀ d ∈ Xs, Lf d ≠ [] →
    ochainsW Lf Xs b d < b + (ochains Lf Xs b).length ∧
    ((W (ochains Lf Xs b) w).getD (ochainsW Lf Xs b d) false = true ↔
      ∃ i ∈ Lf d, w.getD i false = true) := by
  induction Xs with
  | nil => intro b w _ _ d hd; simp at hd
  | cons X Xs ih =>
    intro b w hw hi d hd hLd
    have hi0 : ∀ i ∈ Lf X, i < b := hi X (List.mem_cons.mpr (Or.inl rfl))
    have hlen1 : (W (ochain (Lf X) b) w).length = b + (ochain (Lf X) b).length := by
      rw [W_length, hw]
    have hpre : ∀ a, a < b → (W (ochain (Lf X) b) w).getD a false = w.getD a false :=
      fun a ha => W_prefix _ w a (by omega)
    have eW : W (ochains Lf (X :: Xs) b) w =
        W (ochains Lf Xs (b + (ochain (Lf X) b).length)) (W (ochain (Lf X) b) w) := W_append _ _ w
    have eL : (ochains Lf (X :: Xs) b).length =
        (ochain (Lf X) b).length + (ochains Lf Xs (b + (ochain (Lf X) b).length)).length := by
      show (ochain (Lf X) b ++ ochains Lf Xs (b + (ochain (Lf X) b).length)).length = _
      rw [List.length_append]
    rw [eW, eL]
    by_cases hXd : X = d
    · subst hXd
      have ew : ochainsW Lf (X :: Xs) b X = ochainTop (Lf X) b := by
        show (if X = X then ochainTop (Lf X) b else _) = _
        rw [if_pos rfl]
      obtain ⟨hlt, hv⟩ := ochain_val (Lf X) b w hLd hw hi0
      rw [ew]
      refine ⟨by omega, ?_⟩
      rw [W_prefix _ _ _ (by omega)]
      exact hv
    · have ew : ochainsW Lf (X :: Xs) b d = ochainsW Lf Xs (b + (ochain (Lf X) b).length) d := by
        show (if X = d then ochainTop (Lf X) b else _) = _
        rw [if_neg hXd]
      have hd2 : d ∈ Xs := by
        rcases List.mem_cons.mp hd with h | h
        · exact absurd h.symm hXd
        · exact h
      have his : ∀ e ∈ Xs, ∀ i ∈ Lf e, i < b := fun e he => hi e (List.mem_cons.mpr (Or.inr he))
      obtain ⟨h1, h2⟩ := ih (b + (ochain (Lf X) b).length) _ hlen1
        (fun e he i hi2 => by have := his e he i hi2; omega) d hd2 hLd
      rw [ew]
      refine ⟨by omega, ?_⟩
      rw [h2, oc_ex (Lf d) _ w (fun i hi2 => hpre i (his d hd2 i hi2))]

def lwOf (k off base t : ℕ) : ℕ :=
  if 2 ^ k ≤ t then off + (t - 2 ^ k) else base + (2 ^ k - 1 - t)

def ltGate (k off base j : ℕ) : Gate :=
  ⟨GateOp.or, [lwOf k off base (2 * (2 ^ k - 1 - j)), lwOf k off base (2 * (2 ^ k - 1 - j) + 1)]⟩

def ltree (k off base : ℕ) : List Gate := (List.range (2 ^ k - 1)).map (ltGate k off base)

theorem ltree_len (k off base : ℕ) : (ltree k off base).length = 2 ^ k - 1 := by
  simp [ltree]

theorem lwOf_lt (k off base t : ℕ) (hb : off + 2 ^ k ≤ base) (h1 : 1 ≤ t) (h2 : t < 2 * 2 ^ k) :
    lwOf k off base t < base + (2 ^ k - 1) := by
  unfold lwOf; split_ifs <;> omega

theorem ltree_val (k off base : ℕ) (hb : off + 2 ^ k ≤ base) (x : List Bool) (hx : x.length = base)
    (u : ℕ) (hu : u < 2 ^ k) (hxu : ∀ a, a < 2 ^ k → x.getD (off + a) false = decide (a = u)) :
    ∀ e h t, h + e = k → 2 ^ h ≤ t → t < 2 ^ (h + 1) →
      ((W (ltree k off base) x).getD (lwOf k off base t) false = true ↔ (u + 2 ^ k) / 2 ^ e = t) := by
  intro e
  induction e with
  | zero =>
    intro h t hh h1 h2
    rw [show h = k by omega] at h1 h2
    have hp : 2 ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
    have hw : lwOf k off base t = off + (t - 2 ^ k) := by
      unfold lwOf; rw [if_pos h1]
    rw [hw, W_prefix _ _ _ (by omega), hxu _ (by omega), pow_zero, Nat.div_one, decide_eq_true_iff]
    omega
  | succ e ih =>
    intro h t hh h1 h2
    have hp : 2 ^ (h + 1) = 2 ^ h * 2 := pow_succ 2 h
    have hp2 : 2 ^ (h + 1 + 1) = 2 ^ (h + 1) * 2 := pow_succ 2 (h + 1)
    have hk : 2 ^ (h + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h0 : 0 < 2 ^ h := Nat.two_pow_pos h
    obtain ⟨j, hj⟩ : ∃ j, j = 2 ^ k - 1 - t := ⟨_, rfl⟩
    have hjl : j < (ltree k off base).length := by rw [ltree_len]; omega
    have hw : lwOf k off base t = x.length + j := by
      unfold lwOf; rw [if_neg (by omega)]; omega
    have hg : (ltree k off base)[j] =
        (⟨GateOp.or, [lwOf k off base (2 * t), lwOf k off base (2 * t + 1)]⟩ : Gate) := by
      have ej : 2 ^ k - 1 - j = t := by omega
      have ej' : 2 ^ k - (1 + j) = t := by omega
      have ej'' : 2 ^ k - (j + 1) = t := by omega
      simp [ltree, ltGate, ej, ej', ej'']
    have hc1 : lwOf k off base (2 * t) < x.length + j := by
      unfold lwOf; split_ifs <;> omega
    have hc2 : lwOf k off base (2 * t + 1) < x.length + j := by
      unfold lwOf; split_ifs <;> omega
    rw [hw, W_gate _ _ _ hjl, hg]
    simp only [List.map_cons, List.map_nil]
    rw [if_pos hc1, if_pos hc2, eval_or2, Bool.or_eq_true]
    rw [ih (h + 1) (2 * t) (by omega) (by omega) (by omega),
      ih (h + 1) (2 * t + 1) (by omega) (by omega) (by omega)]
    rw [pow_succ 2 e, ← Nat.div_div_eq_div_mul]
    omega

def lLf (k off base : ℕ) (X : ℕ) : List ℕ :=
  (List.range (2 ^ (X / 2))).map (fun s => lwOf k off base (2 * (2 ^ (X / 2) + s) + X % 2))

def lgates (k off base : ℕ) : List Gate :=
  ltree k off base ++ ochains (lLf k off base) (List.range (2 * k)) (base + (2 ^ k - 1))

def lwire (k off base : ℕ) (i : ℕ) (b : Bool) : ℕ :=
  ochainsW (lLf k off base) (List.range (2 * k)) (base + (2 ^ k - 1)) (2 * (k - 1 - i) + b.toNat)

theorem lsum (k : ℕ) : ((List.range (2 * k)).map fun X => 2 ^ (X / 2) - 1).sum + 2 ≤ 2 * 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
    rw [e, List.range_succ, List.range_succ]
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    have h1 : (2 * k + 1) / 2 = k := by omega
    have h2 : (2 * k) / 2 = k := by omega
    rw [h1, h2, pow_succ]
    have := Nat.two_pow_pos k
    omega

theorem lbit (k u i j b' : ℕ) (hu : u < 2 ^ k) (hk : i + j + 1 = k) (hb : b' < 2) :
    (∃ s, s < 2 ^ j ∧ (u + 2 ^ k) / 2 ^ i = 2 * (2 ^ j + s) + b') ↔ u / 2 ^ i % 2 = b' := by
  have e1 : 2 ^ k = 2 ^ (j + 1) * 2 ^ i := by rw [← pow_add]; congr 1; omega
  have e2 : (u + 2 ^ k) / 2 ^ i = u / 2 ^ i + 2 ^ (j + 1) := by
    rw [e1, Nat.add_mul_div_right _ _ (Nat.two_pow_pos i)]
  have e3 : u / 2 ^ i < 2 ^ (j + 1) :=
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm, ← e1]; exact hu)
  have e4 : 2 ^ (j + 1) = 2 ^ j * 2 := pow_succ 2 j
  rw [e2]
  rw [e4] at e3 ⊢
  generalize u / 2 ^ i = q at e3 ⊢
  generalize 2 ^ j = P at e3 ⊢
  constructor
  · rintro ⟨s, _, h⟩; omega
  · intro h; exact ⟨q / 2, by omega, by omega⟩

theorem lkey_arith (k i s b : ℕ) (hi : i < k) (hs : s < 2 ^ (k - 1 - i)) (hb : b < 2) :
    k - 1 - i + 1 + i = k ∧ 2 ^ (k - 1 - i + 1) ≤ 2 * (2 ^ (k - 1 - i) + s) + b ∧
      2 * (2 ^ (k - 1 - i) + s) + b < 2 ^ (k - 1 - i + 1 + 1) := by
  have p1 : 2 ^ (k - 1 - i + 1) = 2 ^ (k - 1 - i) * 2 := pow_succ 2 _
  have p2 : 2 ^ (k - 1 - i + 1 + 1) = 2 ^ (k - 1 - i + 1) * 2 := pow_succ 2 _
  generalize 2 ^ (k - 1 - i + 1 + 1) = P2 at p2 ⊢
  generalize 2 ^ (k - 1 - i + 1) = P1 at p1 p2 ⊢
  generalize 2 ^ (k - 1 - i) = P0 at p1 hs ⊢
  refine ⟨by omega, by omega, by omega⟩

theorem lcore (k off base : ℕ) (hb : off + 2 ^ k ≤ base) :
    Monotone2 (⟨lgates k off base, 0⟩ : Circuit) ∧ (lgates k off base).length + 3 ≤ 3 * 2 ^ k ∧
    ∀ (x : List Bool) (u : ℕ), x.length = base → u < 2 ^ k →
      (∀ a, a < 2 ^ k → x.getD (off + a) false = decide (a = u)) →
      ∀ i b, i < k → lwire k off base i b < base + (lgates k off base).length ∧
        (W (lgates k off base) x).getD (lwire k off base i b) false = decide (u.testBit i = b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    have hg' : g ∈ ltree k off base ++
        ochains (lLf k off base) (List.range (2 * k)) (base + (2 ^ k - 1)) := hg
    rcases List.mem_append.mp hg' with h | h
    · simp only [ltree, List.mem_map] at h
      obtain ⟨j, _, rfl⟩ := h
      simp [ltGate]
    · obtain ⟨h1, h2⟩ := ochains_gate _ _ _ g h
      rw [h1, h2]; simp
  · rw [lgates, List.length_append, ltree_len, ochains_len]
    have e : (fun X => (lLf k off base X).length - 1) = (fun X => 2 ^ (X / 2) - 1) := by
      funext X; simp [lLf]
    rw [e]
    have := lsum k
    have := Nat.two_pow_pos k
    omega
  · intro x u hx hu hxu i b hi
    have hT := ltree_val k off base hb x hx u hu hxu
    have hlen : (W (ltree k off base) x).length = base + (2 ^ k - 1) := by
      rw [W_length, hx, ltree_len]
    have hall : ∀ X ∈ List.range (2 * k), ∀ a ∈ lLf k off base X, a < base + (2 ^ k - 1) := by
      intro X hX a ha
      simp only [List.mem_range] at hX
      simp only [lLf, List.mem_map, List.mem_range] at ha
      obtain ⟨s, hs, rfl⟩ := ha
      have hp : 2 ^ (X / 2 + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [pow_succ] at hp
      have hm : X % 2 < 2 := Nat.mod_lt _ (by norm_num)
      refine lwOf_lt k off base _ hb ?_ ?_ <;> omega
    have hb2 := Bool.toNat_le b
    have hd : 2 * (k - 1 - i) + b.toNat ∈ List.range (2 * k) := by
      rw [List.mem_range]; omega
    have hne : lLf k off base (2 * (k - 1 - i) + b.toNat) ≠ [] := by
      intro h
      have := congrArg List.length h
      simp [lLf] at this
    obtain ⟨hlt, hv⟩ := ochains_val (lLf k off base) (List.range (2 * k)) _ _ hlen hall _ hd hne
    refine ⟨?_, ?_⟩
    · unfold lgates lwire
      rw [List.length_append, ltree_len]
      omega
    unfold lgates lwire
    rw [W_append, Bool.eq_iff_iff, hv, decide_eq_true_iff]
    have hX2 : (2 * (k - 1 - i) + b.toNat) / 2 = k - 1 - i := by omega
    have hXm : (2 * (k - 1 - i) + b.toNat) % 2 = b.toNat := by omega
    have htb : u.testBit i = b ↔ u / 2 ^ i % 2 = b.toNat := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
      have := Nat.mod_two_eq_zero_or_one (u / 2 ^ i)
      cases b <;> simp <;> omega
    have hlb := lbit k u i (k - 1 - i) b.toNat hu (by omega) (by omega)
    have key : ∀ s, s < 2 ^ (k - 1 - i) →
        ((W (ltree k off base) x).getD (lwOf k off base (2 * (2 ^ (k - 1 - i) + s) + b.toNat))
            false = true ↔
          (u + 2 ^ k) / 2 ^ i = 2 * (2 ^ (k - 1 - i) + s) + b.toNat) := by
      intro s hs
      obtain ⟨q1, q2, q3⟩ := lkey_arith k i s b.toNat hi hs (Nat.lt_succ_of_le hb2)
      exact hT i (k - 1 - i + 1) (2 * (2 ^ (k - 1 - i) + s) + b.toNat) q1 q2 q3
    rw [htb, ← hlb]
    constructor
    · rintro ⟨a, ha, hva⟩
      simp only [lLf, hX2, hXm, List.mem_map, List.mem_range] at ha
      obtain ⟨s, hs, rfl⟩ := ha
      exact ⟨s, hs, (key s hs).mp hva⟩
    · rintro ⟨s, hs, hq⟩
      refine ⟨_, ?_, (key s hs).mpr hq⟩
      simp only [lLf, hX2, hXm, List.mem_map, List.mem_range]
      exact ⟨s, hs, rfl⟩

theorem tidx (n : ℕ) : ∀ j, j < 2 ^ n →
    (Finset.univ.sum fun i : Fin n => if j.testBit i = true then 2 ^ (i : ℕ) else 0) = j := by
  induction n with
  | zero =>
    intro j hj
    rw [pow_zero] at hj
    simp
    omega
  | succ n ih =>
    intro j hj
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    have h1 : (Finset.univ.sum fun i : Fin n => if j.testBit i = true then 2 ^ (i : ℕ) else 0) =
        Finset.univ.sum fun i : Fin n => if (j % 2 ^ n).testBit i = true then 2 ^ (i : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Nat.testBit_mod_two_pow]
      simp [i.isLt]
    have hp : 2 ^ (n + 1) = 2 ^ n * 2 := pow_succ 2 n
    rw [h1, ih _ (Nat.mod_lt _ (Nat.two_pow_pos n))]
    have hm := Nat.mod_add_div j (2 ^ n)
    have hq : j / 2 ^ n < 2 := Nat.div_lt_of_lt_mul (by rw [← hp]; exact hj)
    rw [Nat.testBit_eq_decide_div_mod_eq]
    generalize j / 2 ^ n = q at hm hq ⊢
    generalize j % 2 ^ n = r at hm ⊢
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.lt_succ_iff.mp hq) with h | h <;> subst h <;>
      simp at hm ⊢ <;> omega

def dpos (rp rn : ℕ → ℕ) (g : Gate) : Gate :=
  match g.op with
  | GateOp.or => ⟨GateOp.or, g.inputs.map rp⟩
  | GateOp.not => ⟨GateOp.and, (g.inputs.take 1).map rn⟩
  | _ => ⟨GateOp.and, g.inputs.map rp⟩

def dneg (rp rn : ℕ → ℕ) (g : Gate) : Gate :=
  match g.op with
  | GateOp.or => ⟨GateOp.and, g.inputs.map rn⟩
  | GateOp.not => ⟨GateOp.or, (g.inputs.take 1).map rp⟩
  | _ => ⟨GateOp.or, g.inputs.map rn⟩

theorem dm_or (l : List ℕ) (f : ℕ → Bool) :
    GateOp.or.eval (l.map fun i => !f i) = !GateOp.and.eval (l.map f) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons, GateOp.eval, List.any_cons, List.all_cons] at ih ⊢
    rw [ih]; cases f a <;> rfl

theorem dm_and (l : List ℕ) (f : ℕ → Bool) :
    GateOp.and.eval (l.map fun i => !f i) = !GateOp.or.eval (l.map f) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons, GateOp.eval, List.any_cons, List.all_cons] at ih ⊢
    rw [ih]; cases f a <;> rfl

theorem dpos_shape (rp rn : ℕ → ℕ) (g : Gate) :
    ((dpos rp rn g).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
      (dpos rp rn g).inputs.length ≤ g.inputs.length) ∧
    ((dneg rp rn g).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
      (dneg rp rn g).inputs.length ≤ g.inputs.length) := by
  obtain ⟨op, ins⟩ := g
  cases op <;> simp [dpos, dneg] <;> omega

theorem dpos_lt (rp rn : ℕ → ℕ) (g : Gate) (B : ℕ) (hp : ∀ i, rp i < B) (hn : ∀ i, rn i < B) :
    (∀ a ∈ (dpos rp rn g).inputs, a < B) ∧ (∀ a ∈ (dneg rp rn g).inputs, a < B) := by
  obtain ⟨op, ins⟩ := g
  constructor <;> intro a ha <;> cases op <;> simp only [dpos, dneg, List.mem_map] at ha <;>
    obtain ⟨i, _, rfl⟩ := ha <;> first | exact hp i | exact hn i

theorem dpos_eval (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (rp rn : ℕ → ℕ) (V : ℕ → Bool) (f : ℕ → Bool)
    (hp : ∀ i ∈ g.inputs, V (rp i) = f i) (hn : ∀ i ∈ g.inputs, V (rn i) = !f i) :
    (dpos rp rn g).op.eval ((dpos rp rn g).inputs.map V) = g.op.eval (g.inputs.map f) ∧
    (dneg rp rn g).op.eval ((dneg rp rn g).inputs.map V) = !g.op.eval (g.inputs.map f) := by
  obtain ⟨op, ins⟩ := g
  have ep : ins.map (fun i => V (rp i)) = ins.map f := List.map_congr_left hp
  have en : ins.map (fun i => V (rn i)) = ins.map (fun i => !f i) := List.map_congr_left hn
  rcases hop with h | h | h <;> change op = _ at h <;> subst h
  · simp only [dpos, dneg, List.map_map, Function.comp_def]
    rw [ep, en, dm_or]
    exact ⟨rfl, rfl⟩
  · simp only [dpos, dneg, List.map_map, Function.comp_def]
    rw [ep, en, dm_and]
    exact ⟨rfl, rfl⟩
  · cases ins with
    | nil => exact ⟨rfl, rfl⟩
    | cons a t =>
      have h1 := hp a (List.mem_cons_self ..)
      have h2 := hn a (List.mem_cons_self ..)
      simp only [dpos, dneg, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
        GateOp.eval, List.all_cons, List.all_nil, List.any_cons, List.any_nil, List.headD_cons,
        id, h1, h2]
      cases f a <;> exact ⟨rfl, rfl⟩

def dgates (C : Circuit) (rp rn : ℕ → ℕ → ℕ) : List Gate :=
  (List.range (2 * C.gates.length)).map fun q =>
    if q % 2 = 0 then dpos (rp (q / 2)) (rn (q / 2)) (gateAt C (q / 2))
    else dneg (rp (q / 2)) (rn (q / 2)) (gateAt C (q / 2))

def tL (k l : ℕ) : List Gate := lgates k 0 (2 ^ k + 2 ^ l)
def tB1 (k l : ℕ) : ℕ := 2 ^ k + 2 ^ l + (tL k l).length
def tR (k l : ℕ) : List Gate := lgates l (2 ^ k) (tB1 k l)
def tTW (k l : ℕ) : ℕ := tB1 k l + (tR k l).length
def tlit (k l : ℕ) (b : Bool) (i : ℕ) : ℕ :=
  if i < k then lwire k 0 (2 ^ k + 2 ^ l) i b else lwire l (2 ^ k) (tB1 k l) (i - k) b
def trp (k l j i : ℕ) : ℕ :=
  if i < k + l then tlit k l true i
  else if i < k + l + j then tTW k l + 2 + 2 * (i - (k + l)) else tTW k l + 1
def trn (k l j i : ℕ) : ℕ :=
  if i < k + l then tlit k l false i
  else if i < k + l + j then tTW k l + 2 + 2 * (i - (k + l)) + 1 else tTW k l
def tTF : List Gate := [⟨GateOp.and, []⟩, ⟨GateOp.or, []⟩]
def tD (k l : ℕ) (C : Circuit) : Circuit :=
  ⟨tL k l ++ (tR k l ++ (tTF ++ dgates C (trp k l) (trn k l))), trp k l C.gates.length C.output⟩
def txb (k u v i : ℕ) : Bool := if i < k then u.testBit i else v.testBit (i - k)

theorem tD_size (k l : ℕ) (C : Circuit) :
    (tD k l C).size + 6 ≤ 2 * C.size + 3 * 2 ^ k + 3 * 2 ^ l + 2 := by
  have hL := (lcore k 0 (2 ^ k + 2 ^ l) (by rw [Nat.zero_add]; exact Nat.le_add_right _ _)).2.1
  have hR := (lcore l (2 ^ k) (tB1 k l) (by unfold tB1; omega)).2.1
  simp only [tD, Circuit.size, List.length_append, tTF, dgates, List.length_map, List.length_range,
    List.length_cons, List.length_nil, tL, tR]
  omega

theorem tD_mono (k l : ℕ) (C : Circuit) (hF : FanInTwo C) : Monotone2 (tD k l C) := by
  have hL := (lcore k 0 (2 ^ k + 2 ^ l) (by rw [Nat.zero_add]; exact Nat.le_add_right _ _)).1
  have hR := (lcore l (2 ^ k) (tB1 k l) (by unfold tB1; omega)).1
  intro g hg
  have hg' : g ∈ tL k l ++ (tR k l ++ (tTF ++ dgates C (trp k l) (trn k l))) := hg
  rcases List.mem_append.mp hg' with h | h
  · exact hL g h
  rcases List.mem_append.mp h with h | h
  · exact hR g h
  rcases List.mem_append.mp h with h | h
  · simp only [tTF, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> simp
  · simp only [dgates, List.mem_map, List.mem_range] at h
    obtain ⟨q, hq, rfl⟩ := h
    have hin : (gateAt C (q / 2)).inputs.length ≤ 2 := (hF _ (gateAt_mem (by omega))).2
    have hs := dpos_shape (trp k l (q / 2)) (trn k l (q / 2)) (gateAt C (q / 2))
    split_ifs
    · exact ⟨hs.1.1, le_trans hs.1.2 hin⟩
    · exact ⟨hs.2.1, le_trans hs.2.2 hin⟩

theorem tD_rep (k l : ℕ) (C : Circuit) (hF : FanInTwo C) (u : Fin (2 ^ k)) (v : Fin (2 ^ l)) :
    (tD k l C).eval (PEqualNP.Represents.oneEach u v) =
      C.eval (List.ofFn fun i : Fin (k + l) => txb k u v i) := by
  obtain ⟨hLm, hLl, hLv⟩ := lcore k 0 (2 ^ k + 2 ^ l) (by rw [Nat.zero_add]; exact Nat.le_add_right _ _)
  obtain ⟨hRm, hRl, hRv⟩ := lcore l (2 ^ k) (tB1 k l) (by unfold tB1; omega)
  have hX : (PEqualNP.Represents.oneEach u v).length = 2 ^ k + 2 ^ l := by
    simp [PEqualNP.Represents.oneEach]
  have hxuL : ∀ a, a < 2 ^ k →
      (PEqualNP.Represents.oneEach u v).getD (0 + a) false = decide (a = u.val) := by
    intro a ha
    rw [Nat.zero_add]
    unfold PEqualNP.Represents.oneEach
    rw [getD_app_lt _ _ _ (by simp; exact ha), ofFn_getD _ _ ha]
    simp [Fin.ext_iff]
  have hxuR0 : ∀ a, a < 2 ^ l →
      (PEqualNP.Represents.oneEach u v).getD (2 ^ k + a) false = decide (a = v.val) := by
    intro a ha
    unfold PEqualNP.Represents.oneEach
    rw [List.getD_append_right _ _ _ _ (by simp)]
    have e : 2 ^ k + a - (List.ofFn fun i : Fin (2 ^ k) => decide (i = u)).length = a := by simp
    rw [e, ofFn_getD _ _ ha]
    simp [Fin.ext_iff]
  obtain ⟨X, hXd⟩ : ∃ X, X = PEqualNP.Represents.oneEach u v := ⟨_, rfl⟩
  rw [← hXd] at hX hxuL hxuR0
  obtain ⟨w1, hw1⟩ : ∃ w, w = W (tL k l) X := ⟨_, rfl⟩
  obtain ⟨w2, hw2⟩ : ∃ w, w = W (tR k l) w1 := ⟨_, rfl⟩
  obtain ⟨w3, hw3⟩ : ∃ w, w = W tTF w2 := ⟨_, rfl⟩
  obtain ⟨DG, hDG⟩ : ∃ D, D = dgates C (trp k l) (trn k l) := ⟨_, rfl⟩
  obtain ⟨WD, hWD⟩ : ∃ w, w = W DG w3 := ⟨_, rfl⟩
  have hw1l : w1.length = tB1 k l := by rw [hw1, W_length, hX]; rfl
  have hw2l : w2.length = tTW k l := by rw [hw2, W_length, hw1l]; rfl
  have hw3l : w3.length = tTW k l + 2 := by rw [hw3, W_length, hw2l]; rfl
  have hDGl : DG.length = 2 * C.gates.length := by rw [hDG]; simp [dgates]
  have hxuR : ∀ a, a < 2 ^ l → w1.getD (2 ^ k + a) false = decide (a = v.val) := by
    intro a ha
    rw [hw1, W_prefix _ _ _ (by omega)]
    exact hxuR0 a ha
  -- literal wires
  have hlit : ∀ i, i < k + l → ∀ b, tlit k l b i < tTW k l ∧
      w2.getD (tlit k l b i) false = decide (txb k u v i = b) := by
    intro i hi b
    unfold tlit txb
    by_cases hik : i < k
    · rw [if_pos hik, if_pos hik]
      obtain ⟨h1, h2⟩ := hLv X u.val hX u.isLt hxuL i b hik
      have h1' : lwire k 0 (2 ^ k + 2 ^ l) i b < tB1 k l := h1
      refine ⟨by unfold tTW; omega, ?_⟩
      rw [hw2, W_prefix _ _ _ (by omega), hw1]
      exact h2
    · rw [if_neg hik, if_neg hik]
      obtain ⟨h1, h2⟩ := hRv w1 v.val hw1l v.isLt hxuR (i - k) b (by omega)
      refine ⟨h1, ?_⟩
      rw [hw2]
      exact h2
  have hT : w3.getD (tTW k l) false = true := by
    have h := W_gate tTF w2 0 (by simp [tTF])
    rw [hw2l] at h
    rw [hw3]
    simpa [tTF, GateOp.eval] using h
  have hFw : w3.getD (tTW k l + 1) false = false := by
    have h := W_gate tTF w2 1 (by simp [tTF])
    rw [hw2l] at h
    rw [hw3]
    simpa [tTF, GateOp.eval] using h
  have hp3 : ∀ a, a < tTW k l → w3.getD a false = w2.getD a false := by
    intro a ha; rw [hw3, W_prefix _ _ _ (by omega)]
  have hpD : ∀ a, a < tTW k l + 2 → WD.getD a false = w3.getD a false := by
    intro a ha; rw [hWD, W_prefix _ _ _ (by omega)]
  -- C side
  obtain ⟨xs, hxs⟩ : ∃ xs, xs = List.ofFn fun i : Fin (k + l) => txb k u v i := ⟨_, rfl⟩
  have hxsl : xs.length = k + l := by rw [hxs]; simp
  have hvin : ∀ i, i < k + l → val C xs i = txb k u v i := by
    intro i hi; rw [hxs, val_ofFn_lt C _ i hi]
  -- read lemma
  have hread : ∀ j, (∀ t, t < j → WD.getD (tTW k l + 2 + 2 * t) false = val C xs (k + l + t) ∧
        WD.getD (tTW k l + 2 + 2 * t + 1) false = !val C xs (k + l + t)) →
      ∀ i, WD.getD (trp k l j i) false = (if i < k + l + j then val C xs i else false) ∧
        WD.getD (trn k l j i) false = !(if i < k + l + j then val C xs i else false) := by
    intro j hj i
    unfold trp trn
    by_cases h1 : i < k + l
    · rw [if_pos h1, if_pos h1, if_pos (show i < k + l + j by omega), hvin i h1]
      obtain ⟨hl1, hv1⟩ := hlit i h1 true
      obtain ⟨hl2, hv2⟩ := hlit i h1 false
      rw [hpD (tlit k l true i) (by omega), hp3 _ hl1, hv1, hpD (tlit k l false i) (by omega),
        hp3 _ hl2, hv2]
      cases txb k u v i <;> simp
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : i < k + l + j
      · rw [if_pos h2, if_pos h2, if_pos h2]
        obtain ⟨e1, e2⟩ := hj (i - (k + l)) (by omega)
        have ei : k + l + (i - (k + l)) = i := by omega
        rw [ei] at e1 e2
        exact ⟨e1, e2⟩
      · rw [if_neg h2, if_neg h2, if_neg h2, hpD (tTW k l + 1) (by omega), hpD (tTW k l) (by omega),
          hT, hFw]
        exact ⟨rfl, rfl⟩
  have hbnd : ∀ t i, trp k l t i < tTW k l + 2 + 2 * t ∧ trn k l t i < tTW k l + 2 + 2 * t := by
    intro t i
    unfold trp trn
    by_cases h1 : i < k + l
    · rw [if_pos h1, if_pos h1]
      exact ⟨by have := (hlit i h1 true).1; omega, by have := (hlit i h1 false).1; omega⟩
    · rw [if_neg h1, if_neg h1]
      split_ifs <;> omega
  -- main induction
  have main : ∀ t, t < C.gates.length →
      WD.getD (tTW k l + 2 + 2 * t) false = val C xs (k + l + t) ∧
        WD.getD (tTW k l + 2 + 2 * t + 1) false = !val C xs (k + l + t) := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro ht
      have hr := hread t (fun t' h' => ih t' h' (by omega))
      have hop : (gateAt C t).op = GateOp.and ∨ (gateAt C t).op = GateOp.or ∨
          (gateAt C t).op = GateOp.not := by
        have := (hF _ (gateAt_mem ht)).1
        simpa using this
      have hvg := val_gate (C := C) hxsl ht
      obtain ⟨hpe, hne⟩ := dpos_eval (gateAt C t) hop (trp k l t) (trn k l t)
        (fun a => WD.getD a false) (fun i => if i < k + l + t then val C xs i else false)
        (fun i _ => (hr i).1) (fun i _ => (hr i).2)
      obtain ⟨hlt1, hlt2⟩ := dpos_lt (trp k l t) (trn k l t) (gateAt C t) (tTW k l + 2 + 2 * t)
        (fun i => (hbnd t i).1) (fun i => (hbnd t i).2)
      have hq1 : 2 * t < DG.length := by omega
      have hq2 : 2 * t + 1 < DG.length := by omega
      have hg1 : DG[2 * t] = dpos (trp k l t) (trn k l t) (gateAt C t) := by
        have e1 : 2 * t / 2 = t := by omega
        have e2 : 2 * t % 2 = 0 := by omega
        simp [hDG, dgates, e1, e2]
      have hg2 : DG[2 * t + 1] = dneg (trp k l t) (trn k l t) (gateAt C t) := by
        have e1 : (2 * t + 1) / 2 = t := by omega
        have e2 : (2 * t + 1) % 2 = 1 := by omega
        simp [hDG, dgates, e1, e2]
      have hW1 := W_gate DG w3 (2 * t) hq1
      have hW2 := W_gate DG w3 (2 * t + 1) hq2
      rw [hg1, hw3l] at hW1
      rw [hg2, hw3l] at hW2
      rw [← hWD] at hW1 hW2
      constructor
      · rw [hW1, hvg, ← hpe]
        congr 1
        apply List.map_congr_left
        intro a ha
        rw [if_pos (hlt1 a ha)]
      · rw [show tTW k l + 2 + 2 * t + 1 = tTW k l + 2 + (2 * t + 1) by omega, hW2, hvg, ← hne]
        congr 1
        apply List.map_congr_left
        intro a ha
        rw [if_pos (by have := hlt2 a ha; omega)]
  -- output
  have hout := (hread C.gates.length main C.output).1
  have hev : (tD k l C).eval (PEqualNP.Represents.oneEach u v) =
      WD.getD (trp k l C.gates.length C.output) false := by
    rw [← hXd, eval_W]
    show (W (tL k l ++ (tR k l ++ (tTF ++ dgates C (trp k l) (trn k l)))) X).getD
      (trp k l C.gates.length C.output) false = _
    rw [W_append, W_append, W_append, ← hw1, ← hw2, ← hw3, ← hDG, ← hWD]
  rw [hev, hout, eval_eq_val, ← hxs]
  split_ifs with hlt
  · rfl
  · rw [val_ge hxsl (by omega)]

theorem tadj (k l : ℕ) (A : Fin (2 ^ k) → Fin (2 ^ l) → Bool) (u : Fin (2 ^ k)) (v : Fin (2 ^ l)) :
    PEqualNP.Represents.adjFun A (fun i : Fin (k + l) => txb k u v i) = A u v := by
  have e1 : (fun i : Fin k => txb k u v (Fin.castAdd l i)) = fun i : Fin k => u.val.testBit i := by
    funext i; simp [txb, i.isLt]
  have e2 : (fun j : Fin l => txb k u v (Fin.natAdd k j)) = fun j : Fin l => v.val.testBit j := by
    funext j; simp [txb]
  have h1 : tableIndex (fun i : Fin k => txb k u v (Fin.castAdd l i)) = u.val := by
    rw [e1]; exact tidx k u.val u.isLt
  have h2 : tableIndex (fun j : Fin l => txb k u v (Fin.natAdd k j)) = v.val := by
    rw [e2]; exact tidx l v.val v.isLt
  simp only [PEqualNP.Represents.adjFun, h1, h2]
  congr 1
  · exact Fin.ext (by simp [Nat.mod_eq_of_lt u.isLt])
  · exact Fin.ext (by simp [Nat.mod_eq_of_lt v.isLt])

theorem trep (k l s : ℕ) (A : Fin (2 ^ k) → Fin (2 ^ l) → Bool)
    (h : HasCircuitSize (k + l) (PEqualNP.Represents.adjFun A) s) :
    PEqualNP.Represents.RepSizeAtMost A (2 * s + 3 * 2 ^ k + 3 * 2 ^ l) := by
  obtain ⟨C, hF, hs, hCf⟩ := h
  refine ⟨tD k l C, tD_mono k l C hF, ?_, ?_⟩
  · have := tD_size k l C; omega
  · intro u v
    rw [tD_rep k l C hF u v, hCf, tadj]

theorem main_aux : ∀ (k l s : ℕ) (A : Fin (2 ^ k) → Fin (2 ^ l) → Bool), ¬ PEqualNP.Represents.RepSizeAtMost A (2 * s + 3 * 2 ^ k + 3 * 2 ^ l) → ¬ PEqualNP.MetaComplexity.HasCircuitSize (k + l) (PEqualNP.Represents.adjFun A) s := by
  intro k l s A h hc
  exact h (trep k l s A hc)

end PEqualNP.Outside.L_meta_9022

theorem PEqualNP.Outside.L_meta_9022 : ∀ (k l s : ℕ) (A : Fin (2 ^ k) → Fin (2 ^ l) → Bool), ¬ PEqualNP.Represents.RepSizeAtMost A (2 * s + 3 * 2 ^ k + 3 * 2 ^ l) → ¬ PEqualNP.MetaComplexity.HasCircuitSize (k + l) (PEqualNP.Represents.adjFun A) s :=
  PEqualNP.Outside.L_meta_9022.main_aux
