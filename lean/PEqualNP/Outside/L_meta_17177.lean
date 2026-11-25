import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17177

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


def qind {N : ℕ} (S : Finset (Fin N)) : Fin N → Bool := fun i => decide (i ∈ S)

def rc (g : Gate) : ℕ :=
  match g.op with
  | GateOp.not => 0
  | _ => 1

theorem rc_le (g : Gate) : rc g ≤ 1 := by
  unfold rc
  split <;> simp

theorem rc_sum_le (l : List Gate) : (l.map rc).sum ≤ l.length := by
  induction l with
  | nil => simp
  | cons h l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := rc_le h
    omega

theorem rc_sum_lt (l : List Gate) (g : Gate) (hg : g ∈ l) (hn : g.op = GateOp.not) :
    (l.map rc).sum + 1 ≤ l.length := by
  induction l with
  | nil => simp at hg
  | cons h l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rcases List.mem_cons.mp hg with e | e
    · have h0 : rc h = 0 := by
        rw [← e]
        unfold rc
        rw [hn]
      have := rc_sum_le l
      omega
    · have := ih e
      have := rc_le h
      omega

theorem r2_dep (n : ℕ) (pre : List Gate) (h2 : ∀ g ∈ pre, g.inputs.length ≤ 2) :
    ∀ S : Finset ℕ, ∃ T : Finset ℕ, T.card ≤ (pre.map rc).sum + S.card ∧
      ∀ x y : List Bool, x.length = n → y.length = n →
      (∀ i ∈ T, x.getD i false = y.getD i false) →
      ∀ w ∈ S, (W pre x).getD w false = (W pre y).getD w false := by
  induction pre using List.reverseRecOn with
  | nil =>
    intro S
    exact ⟨S, by simp, fun x y _ _ h w hw => h w hw⟩
  | append_singleton pre g ih =>
    intro S
    have h2p : ∀ g1 ∈ pre, g1.inputs.length ≤ 2 := fun g1 hg1 => h2 g1 (by simp [hg1])
    have hg : g.inputs.length ≤ 2 := h2 g (by simp)
    have key : ∀ (T : Finset ℕ) (S1 : Finset ℕ), (∀ w ∈ S, w ≠ n + pre.length → w ∈ S1) →
        (n + pre.length ∈ S → ∀ x y : List Bool, x.length = n → y.length = n →
          (∀ w ∈ S1, (W pre x).getD w false = (W pre y).getD w false) →
          g.op.eval (g.inputs.map fun i => (W pre x).getD i false) =
            g.op.eval (g.inputs.map fun i => (W pre y).getD i false)) →
        (∀ x y : List Bool, x.length = n → y.length = n →
          (∀ i ∈ T, x.getD i false = y.getD i false) →
          ∀ w ∈ S1, (W pre x).getD w false = (W pre y).getD w false) →
        ∀ x y : List Bool, x.length = n → y.length = n →
          (∀ i ∈ T, x.getD i false = y.getD i false) →
          ∀ w ∈ S, (W (pre ++ [g]) x).getD w false = (W (pre ++ [g]) y).getD w false := by
      intro T S1 hS1 hin hI x y hx hy hag w hw
      have hI2 := hI x y hx hy hag
      rw [W_snoc, W_snoc]
      have hlx : (W pre x).length = n + pre.length := by rw [W_length, hx]
      have hly : (W pre y).length = n + pre.length := by rw [W_length, hy]
      rcases lt_trichotomy w (n + pre.length) with hlt | heq | hgt
      · rw [step_lt _ _ _ (by omega), step_lt _ _ _ (by omega)]
        exact hI2 w (hS1 w hw (by omega))
      · rw [step_last _ _ _ (by omega), step_last _ _ _ (by omega)]
        exact hin (by rw [← heq]; exact hw) x y hx hy hI2
      · rw [getD_ge _ _ (by rw [step_len]; omega), getD_ge _ _ (by rw [step_len]; omega)]
    have hsum : ((pre ++ [g]).map rc).sum = (pre.map rc).sum + rc g := by simp
    by_cases hm : (n + pre.length) ∈ S
    · by_cases hnot : g.op = GateOp.not
      · obtain ⟨T, hT, hTv⟩ := ih h2p (S.erase (n + pre.length) ∪ (g.inputs.take 1).toFinset)
        refine ⟨T, ?_, key T _ ?_ ?_ hTv⟩
        · have h1 := Finset.card_union_le (S.erase (n + pre.length)) (g.inputs.take 1).toFinset
          have h3 := List.toFinset_card_le (g.inputs.take 1)
          have h3' : (g.inputs.take 1).length ≤ 1 := by simp
          have h4 := Finset.card_erase_of_mem hm
          have h5 : 0 < S.card := Finset.card_pos.mpr ⟨_, hm⟩
          rw [hsum]
          omega
        · intro w hw hne
          exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hne, hw⟩)
        · intro _ x y _ _ hS1
          rw [hnot]
          show (!((g.inputs.map fun i => (W pre x).getD i false).headD false)) =
            (!((g.inputs.map fun i => (W pre y).getD i false).headD false))
          have hmem : ∀ i, g.inputs.head? = some i → i ∈ (g.inputs.take 1).toFinset := by
            intro i hi
            rw [List.mem_toFinset]
            rcases hgi : g.inputs with _ | ⟨j, rest⟩
            · rw [hgi] at hi
              simp at hi
            · rw [hgi] at hi
              simp at hi
              simp [hi]
          rcases hgi : g.inputs with _ | ⟨i, rest⟩
          · rfl
          · simp only [List.map_cons, List.headD_cons]
            rw [hS1 i (Finset.mem_union_right _ (hmem i (by rw [hgi]; rfl)))]
      · obtain ⟨T, hT, hTv⟩ := ih h2p (S.erase (n + pre.length) ∪ g.inputs.toFinset)
        refine ⟨T, ?_, key T _ ?_ ?_ hTv⟩
        · have h1 := Finset.card_union_le (S.erase (n + pre.length)) g.inputs.toFinset
          have h3 := List.toFinset_card_le g.inputs
          have h4 := Finset.card_erase_of_mem hm
          have h5 : 0 < S.card := Finset.card_pos.mpr ⟨_, hm⟩
          have hrc : rc g = 1 := by
            unfold rc
            split
            · next h => exact absurd h hnot
            · rfl
          rw [hsum, hrc]
          omega
        · intro w hw hne
          exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hne, hw⟩)
        · intro _ x y _ _ hS1
          have hmap : (g.inputs.map fun i => (W pre x).getD i false) =
              (g.inputs.map fun i => (W pre y).getD i false) :=
            List.map_congr_left (fun i hi =>
              hS1 i (Finset.mem_union_right _ (List.mem_toFinset.mpr hi)))
          rw [hmap]
    · obtain ⟨T, hT, hTv⟩ := ih h2p S
      refine ⟨T, ?_, key T S (fun w hw _ => hw) (fun h => absurd h hm) hTv⟩
      rw [hsum]
      omega

theorem r2_oe (N : ℕ) (a b : Fin N) :
    PEqualNP.Represents.oneEach a b =
      List.ofFn (qind ({Fin.castAdd N a, Fin.natAdd N b} : Finset (Fin (N + N)))) := by
  rw [List.ofFn_add]
  unfold PEqualNP.Represents.oneEach
  congr 1
  · congr 1
    funext i
    simp only [qind]
    apply decide_eq_decide.mpr
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.val_castLE,
      Fin.val_castAdd, Fin.val_natAdd]
    have := i.isLt
    constructor
    · intro h
      exact Or.inl h
    · rintro (h | h)
      · exact h
      · omega
  · congr 1
    funext j
    simp only [qind]
    apply decide_eq_decide.mpr
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.val_castLE,
      Fin.val_castAdd, Fin.val_natAdd]
    have := a.isLt
    constructor
    · intro h
      exact Or.inr (by omega)
    · rintro (h | h)
      · omega
      · omega

theorem r2_getD (N : ℕ) (S : Finset (Fin N)) (i : ℕ) :
    (List.ofFn (qind S)).getD i false = if h : i < N then decide ((⟨i, h⟩ : Fin N) ∈ S) else false := by
  split_ifs with h
  · rw [ofFn_getD (qind S) i h]
    rfl
  · exact ofFn_getD_ge (qind S) i (by omega)

theorem r2_main (N : ℕ) (hN : 2 ≤ N) (A : Fin N → Fin N → Bool) (C : Circuit)
    (hF : PEqualNP.MetaComplexity.FanInTwo C) (hR : PEqualNP.Represents.Represents A C)
    (hdr : ∀ u u' : Fin N, u ≠ u' → ∃ v, A u v ≠ A u' v)
    (hdc : ∀ v v' : Fin N, v ≠ v' → ∃ u, A u v ≠ A u v')
    (hmr : ∀ a : Fin N, ∃ v u', A a v = true ∧ A u' v = false)
    (hmc : ∀ b : Fin N, ∃ u v', A u b = true ∧ A u v' = false) :
    2 * N - 2 ≤ C.size ∧ ((∀ g ∈ C.gates, g.op ≠ GateOp.not) → 2 * N - 1 ≤ C.size) := by
  have h2 : ∀ g ∈ C.gates, g.inputs.length ≤ 2 := fun g hg => (hF g hg).2
  obtain ⟨T, hT, hag⟩ := r2_dep (N + N) C.gates h2 {C.output}
  have hRv : ∀ a b : Fin N, C.eval (List.ofFn (qind ({Fin.castAdd N a, Fin.natAdd N b} :
      Finset (Fin (N + N))))) = A a b := by
    intro a b
    rw [← r2_oe]
    exact hR a b
  have hsame : ∀ S S' : Finset (Fin (N + N)), (∀ i ∈ T, ∀ h : i < N + N,
      ((⟨i, h⟩ : Fin (N + N)) ∈ S ↔ (⟨i, h⟩ : Fin (N + N)) ∈ S')) →
      C.eval (List.ofFn (qind S)) = C.eval (List.ofFn (qind S')) := by
    intro S S' hS
    have := hag (List.ofFn (qind S)) (List.ofFn (qind S')) (by simp) (by simp)
      (fun i hi => by
        rw [r2_getD, r2_getD]
        split_ifs with h
        · exact decide_eq_decide.mpr (hS i hi h)
        · rfl) C.output (Finset.mem_singleton_self _)
    exact this
  -- at most one row wire and one column wire outside T
  have hrow : ∀ u u' : Fin N, u.val ∉ T → u'.val ∉ T → u = u' := by
    intro u u' hu hu'
    by_contra hne
    obtain ⟨v, hv⟩ := hdr u u' hne
    apply hv
    rw [← hRv u v, ← hRv u' v]
    apply hsame
    intro i hi h
    have h1 : (⟨i, h⟩ : Fin (N + N)) ≠ Fin.castAdd N u := by
      intro e
      apply hu
      have := congrArg Fin.val e
      simp at this
      rw [← this]
      exact hi
    have h2' : (⟨i, h⟩ : Fin (N + N)) ≠ Fin.castAdd N u' := by
      intro e
      apply hu'
      have := congrArg Fin.val e
      simp at this
      rw [← this]
      exact hi
    simp only [Finset.mem_insert, Finset.mem_singleton, h1, h2', false_or, or_false]
  have hcol : ∀ v v' : Fin N, N + v.val ∉ T → N + v'.val ∉ T → v = v' := by
    intro v v' hv hv'
    by_contra hne
    obtain ⟨u, hu⟩ := hdc v v' hne
    apply hu
    rw [← hRv u v, ← hRv u v']
    apply hsame
    intro i hi h
    have h1 : (⟨i, h⟩ : Fin (N + N)) ≠ Fin.natAdd N v := by
      intro e
      apply hv
      have := congrArg Fin.val e
      simp at this
      rw [show N + v.val = i by omega]
      exact hi
    have h2' : (⟨i, h⟩ : Fin (N + N)) ≠ Fin.natAdd N v' := by
      intro e
      apply hv'
      have := congrArg Fin.val e
      simp at this
      rw [show N + v'.val = i by omega]
      exact hi
    simp only [Finset.mem_insert, Finset.mem_singleton, h1, h2', false_or, or_false]
  set Rin := Finset.univ.filter (fun u : Fin N => u.val ∈ T) with hRin
  set Cin := Finset.univ.filter (fun v : Fin N => N + v.val ∈ T) with hCin
  have hsub : Rin.image (fun u => u.val) ∪ Cin.image (fun v => N + v.val) ⊆ T := by
    intro t ht
    rw [Finset.mem_union, Finset.mem_image, Finset.mem_image] at ht
    rcases ht with ⟨u, hu, rfl⟩ | ⟨v, hv, rfl⟩
    · rw [hRin, Finset.mem_filter] at hu
      exact hu.2
    · rw [hCin, Finset.mem_filter] at hv
      exact hv.2
  have hdisj : Disjoint (Rin.image (fun u => u.val)) (Cin.image (fun v => N + v.val)) := by
    rw [Finset.disjoint_left]
    intro t h1 h2
    rw [Finset.mem_image] at h1 h2
    obtain ⟨u, _, hu⟩ := h1
    obtain ⟨v, _, hv⟩ := h2
    have := u.isLt
    omega
  have hcardT : Rin.card + Cin.card ≤ T.card := by
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ (fun a b h => Fin.ext h),
      Finset.card_image_of_injective _ (fun a b h => Fin.ext (Nat.add_left_cancel h))] at this
    exact this
  have hRc : N - 1 ≤ Rin.card := by
    have h1 := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin N))) (fun u : Fin N => u.val ∈ T)
    have h2 : (Finset.univ.filter (fun u : Fin N => ¬ u.val ∈ T)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      rw [Finset.mem_filter] at ha hb
      exact hrow a b ha.2 hb.2
    rw [Finset.card_univ, Fintype.card_fin, ← hRin] at h1
    omega
  have hCc : N - 1 ≤ Cin.card := by
    have h1 := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin N))) (fun v : Fin N => N + v.val ∈ T)
    have h2 : (Finset.univ.filter (fun v : Fin N => ¬ N + v.val ∈ T)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      rw [Finset.mem_filter] at ha hb
      exact hcol a b ha.2 hb.2
    rw [Finset.card_univ, Fintype.card_fin, ← hCin] at h1
    omega
  have hsz : C.size = C.gates.length := rfl
  by_cases hnot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, hg, hgn⟩ := hnot
    have := rc_sum_lt C.gates g hg hgn
    simp only [Finset.card_singleton] at hT
    refine ⟨by omega, fun hall => absurd hgn (hall g hg)⟩
  · -- no NOT gate: the circuit is monotone, so every line is read
    have hAO : PEqualNP.EdgeOwnership.AndOrOnly C := by
      intro g hg
      have h1 := (hF g hg).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
      rcases h1 with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1
      · exact absurd ⟨g, hg, h1⟩ hnot
    have hallr : ∀ a : Fin N, a.val ∈ T := by
      intro a
      by_contra ha
      obtain ⟨v, u', h1, h2⟩ := hmr a
      have e : C.eval (List.ofFn (qind ({Fin.natAdd N v} : Finset (Fin (N + N))))) = true := by
        rw [← h1, ← hRv a v]
        apply hsame
        intro i hi h
        have hne : (⟨i, h⟩ : Fin (N + N)) ≠ Fin.castAdd N a := by
          intro e
          apply ha
          have := congrArg Fin.val e
          simp at this
          rw [← this]
          exact hi
        simp only [Finset.mem_insert, Finset.mem_singleton, hne, false_or, or_false]
      have e2 := mono (N + N) C hAO (qind ({Fin.natAdd N v} : Finset (Fin (N + N))))
        (qind ({Fin.castAdd N u', Fin.natAdd N v} : Finset (Fin (N + N))))
        (fun i hi => by
          simp only [qind, decide_eq_true_eq, Finset.mem_singleton] at hi
          simp [qind, hi]) C.output e
      have e3 : C.eval (List.ofFn (qind ({Fin.castAdd N u', Fin.natAdd N v} :
          Finset (Fin (N + N))))) = true := e2
      rw [hRv, h2] at e3
      exact absurd e3 (by decide)
    have hallc : ∀ b : Fin N, N + b.val ∈ T := by
      intro b
      by_contra hb
      obtain ⟨u, v', h1, h2⟩ := hmc b
      have e : C.eval (List.ofFn (qind ({Fin.castAdd N u} : Finset (Fin (N + N))))) = true := by
        rw [← h1, ← hRv u b]
        apply hsame
        intro i hi h
        have hne : (⟨i, h⟩ : Fin (N + N)) ≠ Fin.natAdd N b := by
          intro e
          apply hb
          have := congrArg Fin.val e
          simp at this
          rw [show N + b.val = i by omega]
          exact hi
        simp only [Finset.mem_insert, Finset.mem_singleton, hne, false_or, or_false]
      have e2 := mono (N + N) C hAO (qind ({Fin.castAdd N u} : Finset (Fin (N + N))))
        (qind ({Fin.castAdd N u, Fin.natAdd N v'} : Finset (Fin (N + N))))
        (fun i hi => by
          simp only [qind, decide_eq_true_eq, Finset.mem_singleton] at hi
          simp [qind, hi]) C.output e
      have e3 : C.eval (List.ofFn (qind ({Fin.castAdd N u, Fin.natAdd N v'} :
          Finset (Fin (N + N))))) = true := e2
      rw [hRv, h2] at e3
      exact absurd e3 (by decide)
    have hR1 : Rin.card = N := by
      rw [hRin, Finset.filter_true_of_mem (fun u _ => hallr u), Finset.card_univ, Fintype.card_fin]
    have hC1 : Cin.card = N := by
      rw [hCin, Finset.filter_true_of_mem (fun v _ => hallc v), Finset.card_univ, Fintype.card_fin]
    have := rc_sum_le C.gates
    simp only [Finset.card_singleton] at hT
    exact ⟨by omega, fun _ => by omega⟩

theorem r2_other (N : ℕ) (hN : 2 ≤ N) (a : Fin N) : ∃ b : Fin N, b ≠ a := by
  by_cases h : a.val = 0
  · refine ⟨⟨1, by omega⟩, fun e => ?_⟩
    have := congrArg Fin.val e
    simp at this
    omega
  · refine ⟨⟨0, by omega⟩, fun e => ?_⟩
    have := congrArg Fin.val e
    simp at this
    omega

theorem main_aux : ∀ (N : ℕ), 2 ≤ N → ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents (fun u v : Fin N => decide (u ≠ v)) C → 2 * N - 2 ≤ C.size := by
  intro N hN C hF hR
  have := r2_main N hN _ C hF hR (fun u u' hne => ⟨u, by simp [Ne.symm hne]⟩)
    (fun v v' hne => ⟨v, by simp [hne]⟩)
    (fun a => by
      obtain ⟨b, hb⟩ := r2_other N hN a
      exact ⟨b, b, by simp [Ne.symm hb], by simp⟩)
    (fun b => by
      obtain ⟨c, hc⟩ := r2_other N hN b
      exact ⟨c, c, by simp [hc], by simp⟩)
  exact this.1

end PEqualNP.Outside.L_meta_17177

theorem PEqualNP.Outside.L_meta_17177 : ∀ (N : ℕ), 2 ≤ N → ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents (fun u v : Fin N => decide (u ≠ v)) C → 2 * N - 2 ≤ C.size :=
  PEqualNP.Outside.L_meta_17177.main_aux
