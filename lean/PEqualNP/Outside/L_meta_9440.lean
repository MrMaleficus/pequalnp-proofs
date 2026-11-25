import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9440

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

-- FRAGMENT cones    DEPENDS: fold mono
-- Strict cones (PEqualNP.EdgeOwnership.cones / coneStep / InCone), PEqualNP.Core.coneSet, the leaves of a cone,
-- and: the value of a gate depends only on the inputs read inside its cone.
-- Exports (EO = PEqualNP.EdgeOwnership):
--   cones_len gs cs : (gs.foldl (EO.coneStep n) cs).length = cs.length + gs.length ;  cones_length : (EO.cones n C).length = C.gates.length
--   cones_char gs : i in (gs.foldl (coneStep n) []).getD j [] iff j < gs.length and exists w in (gs.getD j (OR of nothing)).inputs,
--       n <= w, w < n + j, (i = w - n or i in (fold).getD (w - n) [])
--   inCone_iff : EO.InCone n C i j iff j < C.gates.length and exists k, k < j and n + k in (gateAt C j).inputs and (i = k or InCone n C i k)
--   inCone_lt : InCone n C i j -> i < j and j < C.gates.length
--   inCone_of_read (j < C.gates.length) (k < j) (n + k in (gateAt C j).inputs) : InCone n C k j
--   inCone_trans : InCone n C i k -> InCone n C k j -> InCone n C i j
--   inCone_irrefl : not InCone n C j j
--   mem_coneSet : i in PEqualNP.Core.coneSet n C j iff i = j or InCone n C i j
--   self_mem_coneSet : j in coneSet n C j ;  coneSet_mono : InCone n C k j -> coneSet n C k subset coneSet n C j
--   coneSet_le (i in coneSet n C j) : i <= j ;  coneSet_sub_range (j < C.gates.length) : coneSet n C j subset Finset.range C.gates.length
--   def coneLeaves n C j : Finset (Fin n) := the inputs t with t read by some gate of coneSet n C j
--   mem_coneLeaves : t in coneLeaves n C j iff exists i in coneSet n C j, t.val in (gateAt C i).inputs
--   coneLeaves_mono : InCone n C k j -> coneLeaves n C k subset coneLeaves n C j
--   cone_agree (x, x' agree on coneLeaves n C j) : val C (List.ofFn x) (n + j) = val C (List.ofFn x') (n + j)
--   cone_agree_gateVal : same for EO.gateVal n C j x = EO.gateVal n C j x'
--   def coneRd n C z w : n <= w, w < n + C.gates.length, z in (gateAt C (w - n)).inputs  (wire w reads wire z)
--   coneRd_of_input, coneRd_lt (ReadsBack) : coneRd z w -> z < w ;  coneRtg_le (ReadsBack) : ReflTransGen coneRd z w -> z <= w
--   coneRtg_inCone (ReadsBack) : ReflTransGen coneRd w b -> n <= w -> w ne b -> InCone n C (w - n) (b - n)
--   inCone_coneRtg : InCone n C k i -> ReflTransGen coneRd (n + k) (n + i)
--   coneSet_iff_rtg (ReadsBack, j < len) : i in coneSet n C j iff i < C.gates.length and ReflTransGen coneRd (n + i) (n + j)
--   coneRd_reach_iff (ReadsBack, j < len, w ne n + j) : ReflTransGen coneRd w (n + j) iff exists i in coneSet n C j, w in (gateAt C i).inputs
-- Use: inCone_iff to unfold one level, mem_coneSet to move between coneSet and InCone, cone_agree to compare a gate at two inputs.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [PEqualNP.EdgeOwnership.coneStep]
    omega

theorem cones_length (n : ℕ) (C : Circuit) :
    (PEqualNP.EdgeOwnership.cones n C).length = C.gates.length := by
  unfold PEqualNP.EdgeOwnership.cones
  rw [cones_len]; simp

theorem cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (PEqualNP.EdgeOwnership.coneStep n
          (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []) g).getD k [] =
          (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD k [] := by
      intro k hk
      simp only [PEqualNP.EdgeOwnership.coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (PEqualNP.EdgeOwnership.coneStep n
          (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD (w - n) []) := by
        simp only [PEqualNP.EdgeOwnership.coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (PEqualNP.EdgeOwnership.coneStep n
          (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []) g).getD j [] = [] := by
        simp only [PEqualNP.EdgeOwnership.coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

theorem inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    PEqualNP.EdgeOwnership.InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧
      n + k ∈ (gateAt C j).inputs ∧ (i = k ∨ PEqualNP.EdgeOwnership.InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold PEqualNP.EdgeOwnership.InCone PEqualNP.EdgeOwnership.cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

theorem inCone_lt (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, PEqualNP.EdgeOwnership.InCone n C i j → i < j ∧ j < C.gates.length := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k, hk, _, h3 | h3⟩ := h
    · exact ⟨by omega, h0⟩
    · have := (ih k hk h3).1
      exact ⟨by omega, h0⟩

theorem inCone_of_read (n : ℕ) (C : Circuit) (k j : ℕ) (hj : j < C.gates.length) (hk : k < j)
    (hin : n + k ∈ (gateAt C j).inputs) : PEqualNP.EdgeOwnership.InCone n C k j :=
  (inCone_iff n C k j).mpr ⟨hj, k, hk, hin, Or.inl rfl⟩

theorem inCone_trans (n : ℕ) (C : Circuit) (i k : ℕ) (hik : PEqualNP.EdgeOwnership.InCone n C i k) :
    ∀ j, PEqualNP.EdgeOwnership.InCone n C k j → PEqualNP.EdgeOwnership.InCone n C i j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k', hk', hin, h3⟩ := h
    rw [inCone_iff]
    refine ⟨h0, k', hk', hin, Or.inr ?_⟩
    rcases h3 with h3 | h3
    · rw [← h3]; exact hik
    · exact ih k' hk' h3

theorem inCone_irrefl (n : ℕ) (C : Circuit) (j : ℕ) : ¬ PEqualNP.EdgeOwnership.InCone n C j j := by
  intro h
  have := (inCone_lt n C j j h).1
  omega

theorem mem_coneSet (n : ℕ) (C : Circuit) (i j : ℕ) :
    i ∈ PEqualNP.Core.coneSet n C j ↔ i = j ∨ PEqualNP.EdgeOwnership.InCone n C i j := by
  unfold PEqualNP.Core.coneSet
  simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro (h | ⟨_, h⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h
    · have := inCone_lt n C i j h
      exact Or.inr ⟨by omega, h⟩

theorem self_mem_coneSet (n : ℕ) (C : Circuit) (j : ℕ) : j ∈ PEqualNP.Core.coneSet n C j :=
  (mem_coneSet n C j j).mpr (Or.inl rfl)

theorem coneSet_mono (n : ℕ) (C : Circuit) (k j : ℕ) (h : PEqualNP.EdgeOwnership.InCone n C k j) :
    PEqualNP.Core.coneSet n C k ⊆ PEqualNP.Core.coneSet n C j := by
  intro i hi
  rw [mem_coneSet] at hi ⊢
  right
  rcases hi with hi | hi
  · rw [hi]; exact h
  · exact inCone_trans n C i k hi j h

theorem coneSet_le (n : ℕ) (C : Circuit) (i j : ℕ) (h : i ∈ PEqualNP.Core.coneSet n C j) : i ≤ j := by
  rw [mem_coneSet] at h
  rcases h with h | h
  · omega
  · have := (inCone_lt n C i j h).1
    omega

theorem coneSet_sub_range (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    PEqualNP.Core.coneSet n C j ⊆ Finset.range C.gates.length := by
  intro i hi
  have := coneSet_le n C i j hi
  rw [Finset.mem_range]
  omega

def coneLeaves (n : ℕ) (C : Circuit) (j : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun t => ∃ i ∈ PEqualNP.Core.coneSet n C j, t.val ∈ (gateAt C i).inputs

theorem mem_coneLeaves (n : ℕ) (C : Circuit) (j : ℕ) (t : Fin n) :
    t ∈ coneLeaves n C j ↔ ∃ i ∈ PEqualNP.Core.coneSet n C j, t.val ∈ (gateAt C i).inputs := by
  unfold coneLeaves
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem coneLeaves_mono (n : ℕ) (C : Circuit) (k j : ℕ) (h : PEqualNP.EdgeOwnership.InCone n C k j) :
    coneLeaves n C k ⊆ coneLeaves n C j := by
  intro t ht
  rw [mem_coneLeaves] at ht ⊢
  obtain ⟨i, hi, hti⟩ := ht
  exact ⟨i, coneSet_mono n C k j h hi, hti⟩

theorem cone_agree (n : ℕ) (C : Circuit) (x x' : Fin n → Bool) :
    ∀ j, (∀ t ∈ coneLeaves n C j, x t = x' t) →
      val C (List.ofFn x) (n + j) = val C (List.ofFn x') (n + j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hxx
    by_cases hj : j < C.gates.length
    · rw [val_gate (n := n) (by simp) hj, val_gate (n := n) (by simp) hj]
      congr 1
      apply List.map_congr_left
      intro w hw
      by_cases hlt : w < n + j
      · rw [if_pos hlt, if_pos hlt]
        by_cases hwn : w < n
        · rw [val_ofFn_lt C x w hwn, val_ofFn_lt C x' w hwn]
          apply hxx
          rw [mem_coneLeaves]
          exact ⟨j, self_mem_coneSet n C j, hw⟩
        · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
          have hk : k < j := by omega
          apply ih k hk
          intro t ht
          exact hxx t (coneLeaves_mono n C k j (inCone_of_read n C k j hj hk hw) ht)
      · rw [if_neg hlt, if_neg hlt]
    · rw [val_ge (n := n) (by simp) (by omega), val_ge (n := n) (by simp) (by omega)]

theorem cone_agree_gateVal (n : ℕ) (C : Circuit) (x x' : Fin n → Bool) (j : ℕ)
    (hxx : ∀ t ∈ coneLeaves n C j, x t = x' t) :
    PEqualNP.EdgeOwnership.gateVal n C j x = PEqualNP.EdgeOwnership.gateVal n C j x' :=
  cone_agree n C x x' j hxx

def coneRd (n : ℕ) (C : Circuit) (z w : ℕ) : Prop :=
  n ≤ w ∧ w < n + C.gates.length ∧ z ∈ (gateAt C (w - n)).inputs

theorem coneRd_of_input {n : ℕ} {C : Circuit} {t w : ℕ} (ht : t < C.gates.length)
    (hw : w ∈ (gateAt C t).inputs) : coneRd n C w (n + t) :=
  ⟨by omega, by omega, by rw [Nat.add_sub_cancel_left]; exact hw⟩

theorem coneRd_lt {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {z w : ℕ} (h : coneRd n C z w) :
    z < w := by
  obtain ⟨h1, h2, h3⟩ := h
  have := hRB (w - n) (by omega) z h3
  omega

theorem coneRtg_le {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {z w : ℕ}
    (h : Relation.ReflTransGen (coneRd n C) z w) : z ≤ w := by
  induction h with
  | refl => exact le_refl _
  | tail _ hbc ih => have := coneRd_lt hRB hbc; omega

theorem coneRtg_inCone {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) (w b : ℕ)
    (h : Relation.ReflTransGen (coneRd n C) w b) :
    n ≤ w → w ≠ b → PEqualNP.EdgeOwnership.InCone n C (w - n) (b - n) := by
  induction h with
  | refl => intro _ h; exact absurd rfl h
  | @tail b c hab hbc ih =>
    intro hw _
    have hbn : b < c := coneRd_lt hRB hbc
    have hwb : w ≤ b := coneRtg_le hRB hab
    obtain ⟨h1, h2, h3⟩ := hbc
    rw [inCone_iff]
    refine ⟨by omega, b - n, by omega, ?_, ?_⟩
    · have e : n + (b - n) = b := by omega
      rw [e]; exact h3
    · by_cases hwb' : w = b
      · left; rw [hwb']
      · right; exact ih hw hwb'

theorem inCone_coneRtg {n : ℕ} {C : Circuit} : ∀ i k, PEqualNP.EdgeOwnership.InCone n C k i →
    Relation.ReflTransGen (coneRd n C) (n + k) (n + i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro k h
    rw [inCone_iff] at h
    obtain ⟨h0, k', hk', hin, h3⟩ := h
    have hst : coneRd n C (n + k') (n + i) := coneRd_of_input h0 hin
    rcases h3 with rfl | h3
    · exact Relation.ReflTransGen.single hst
    · exact (ih k' hk' k h3).tail hst

theorem coneSet_iff_rtg {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {j : ℕ} (hj : j < C.gates.length)
    (i : ℕ) : i ∈ PEqualNP.Core.coneSet n C j ↔
      i < C.gates.length ∧ Relation.ReflTransGen (coneRd n C) (n + i) (n + j) := by
  rw [mem_coneSet]
  constructor
  · rintro (rfl | hc)
    · exact ⟨hj, Relation.ReflTransGen.refl⟩
    · exact ⟨by have := inCone_lt n C i j hc; omega, inCone_coneRtg j i hc⟩
  · rintro ⟨_, hr⟩
    by_cases hij : i = j
    · left; exact hij
    · right
      have := coneRtg_inCone hRB (n + i) (n + j) hr (by omega) (by omega)
      simpa using this

theorem coneRd_reach_iff {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {j : ℕ}
    (hj : j < C.gates.length) (w : ℕ) (hw : w ≠ n + j) :
    Relation.ReflTransGen (coneRd n C) w (n + j) ↔
      ∃ i ∈ PEqualNP.Core.coneSet n C j, w ∈ (gateAt C i).inputs := by
  constructor
  · intro h
    rcases h.cases_head with h | ⟨c, hc, hcJ⟩
    · exact absurd h hw
    · refine ⟨c - n, ?_, hc.2.2⟩
      rw [coneSet_iff_rtg hRB hj]
      refine ⟨by have := hc.2.1; omega, ?_⟩
      have e : n + (c - n) = c := by have := hc.1; omega
      rw [e]; exact hcJ
  · rintro ⟨i, hiK, hwi⟩
    have hh := (coneSet_iff_rtg hRB hj i).mp hiK
    exact Relation.ReflTransGen.head (coneRd_of_input hh.1 hwi) hh.2

def qind {N : ℕ} (S : Finset (Fin N)) : Fin N → Bool := fun i => decide (i ∈ S)

def qP4 {N : ℕ} (U X V Y : Fin N) (g : (Fin N → Bool) → Bool) : Prop :=
  g (qind {U, V}) = true ∧ g (qind {U, Y}) = true ∧ g (qind {X, V}) = true ∧
  g (qind {X, Y}) = false ∧ g (qind {U}) = false ∧ g (qind {V}) = false

def qDep {N : ℕ} (g : (Fin N → Bool) → Bool) (L : Finset (Fin N)) : Prop :=
  ∀ S S' : Finset (Fin N), (∀ t ∈ L, (t ∈ S ↔ t ∈ S')) → g (qind S) = g (qind S')

def qMon {N : ℕ} (g : (Fin N → Bool) → Bool) : Prop :=
  ∀ S S' : Finset (Fin N), S ⊆ S' → g (qind S) = true → g (qind S') = true

theorem q_nf {b c : Bool} (h : b = true → c = true) (hc : c = false) : b = false := by
  cases b
  · rfl
  · rw [h rfl] at hc
    exact absurd hc (by decide)

theorem q_drop2 {N : ℕ} {g : (Fin N → Bool) → Bool} {L : Finset (Fin N)} (h : qDep g L)
    (a b : Fin N) (hb : b ∉ L) : g (qind {a, b}) = g (qind {a}) := by
  apply h
  intro t ht
  have hne : t ≠ b := fun e => hb (e ▸ ht)
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h1 | h1)
    · exact h1
    · exact absurd h1 hne
  · intro h1
    exact Or.inl h1

theorem q_drop1 {N : ℕ} {g : (Fin N → Bool) → Bool} {L : Finset (Fin N)} (h : qDep g L)
    (a b : Fin N) (ha : a ∉ L) : g (qind {a, b}) = g (qind {b}) := by
  apply h
  intro t ht
  have hne : t ≠ a := fun e => ha (e ▸ ht)
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h1 | h1)
    · exact absurd h1 hne
    · exact h1
  · intro h1
    exact Or.inr h1

theorem q_mon1 {N : ℕ} {g : (Fin N → Bool) → Bool} (h : qMon g) (a b : Fin N)
    (h1 : g (qind {a}) = true) : g (qind {a, b}) = true :=
  h _ _ (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self a {b})) h1

theorem q_mon2 {N : ℕ} {g : (Fin N → Bool) → Bool} (h : qMon g) (a b : Fin N)
    (h1 : g (qind {b}) = true) : g (qind {a, b}) = true :=
  h _ _ (Finset.subset_insert a {b}) h1

theorem q_orcase {N : ℕ} (U X V Y : Fin N) (α β : (Fin N → Bool) → Bool) (La Lb : Finset (Fin N))
    (hα : qDep α La) (hβ : qDep β Lb) (mβ : qMon β)
    (hU : U ∉ La ∨ U ∉ Lb) (hV : V ∉ La ∨ V ∉ Lb)
    (e2 : (α (qind {U, Y}) || β (qind {U, Y})) = true)
    (e3 : (α (qind {X, V}) || β (qind {X, V})) = true)
    (a4 : α (qind {X, Y}) = false) (b4 : β (qind {X, Y}) = false)
    (a5 : α (qind {U}) = false) (a6 : α (qind {V}) = false)
    (a1 : α (qind {U, V}) = true) : qP4 U X V Y α := by
  have hVa : V ∈ La := by
    by_contra hn
    rw [q_drop2 hα U V hn, a5] at a1
    exact absurd a1 (by decide)
  have hUa : U ∈ La := by
    by_contra hn
    rw [q_drop1 hα U V hn, a6] at a1
    exact absurd a1 (by decide)
  have hUb : U ∉ Lb := hU.resolve_left (fun h => h hUa)
  have hVb : V ∉ Lb := hV.resolve_left (fun h => h hVa)
  have b2 : β (qind {U, Y}) = false := by
    rw [q_drop1 hβ U Y hUb]
    exact q_nf (q_mon2 mβ X Y) b4
  have b3 : β (qind {X, V}) = false := by
    rw [q_drop2 hβ X V hVb]
    exact q_nf (q_mon1 mβ X Y) b4
  rw [b2, Bool.or_false] at e2
  rw [b3, Bool.or_false] at e3
  exact ⟨a1, e2, e3, a4, a5, a6⟩

theorem q_andcase {N : ℕ} (U X V Y : Fin N) (α β : (Fin N → Bool) → Bool)
    (La Lb : Finset (Fin N)) (hα : qDep α La) (hβ : qDep β Lb)
    (hU : U ∉ La ∨ U ∉ Lb) (hX : X ∉ La ∨ X ∉ Lb) (hV : V ∉ La ∨ V ∉ Lb) (hY : Y ∉ La ∨ Y ∉ Lb)
    (a1 : α (qind {U, V}) = true) (a2 : α (qind {U, Y}) = true) (a3 : α (qind {X, V}) = true)
    (b1 : β (qind {U, V}) = true) (b2 : β (qind {U, Y}) = true) (b3 : β (qind {X, V}) = true)
    (a4 : α (qind {X, Y}) = false)
    (h5 : α (qind {U}) = false ∨ β (qind {U}) = false)
    (h6 : α (qind {V}) = false ∨ β (qind {V}) = false) : qP4 U X V Y α := by
  have a5 : α (qind {U}) = false := by
    rcases h5 with h5 | h5
    · exact h5
    · exfalso
      have hVb : V ∈ Lb := by
        by_contra hn
        rw [q_drop2 hβ U V hn, h5] at b1
        exact absurd b1 (by decide)
      have hYb : Y ∈ Lb := by
        by_contra hn
        rw [q_drop2 hβ U Y hn, h5] at b2
        exact absurd b2 (by decide)
      have hVa : V ∉ La := hV.resolve_right (fun h => h hVb)
      have hYa : Y ∉ La := hY.resolve_right (fun h => h hYb)
      rw [q_drop2 hα X V hVa] at a3
      rw [q_drop2 hα X Y hYa, a3] at a4
      exact absurd a4 (by decide)
  have a6 : α (qind {V}) = false := by
    rcases h6 with h6 | h6
    · exact h6
    · exfalso
      have hUb : U ∈ Lb := by
        by_contra hn
        rw [q_drop1 hβ U V hn, h6] at b1
        exact absurd b1 (by decide)
      have hXb : X ∈ Lb := by
        by_contra hn
        rw [q_drop1 hβ X V hn, h6] at b3
        exact absurd b3 (by decide)
      have hUa : U ∉ La := hU.resolve_right (fun h => h hUb)
      have hXa : X ∉ La := hX.resolve_right (fun h => h hXb)
      rw [q_drop1 hα U Y hUa] at a2
      rw [q_drop1 hα X Y hXa, a2] at a4
      exact absurd a4 (by decide)
  exact ⟨a1, a2, a3, a4, a5, a6⟩

theorem q_split {N : ℕ} (U X V Y : Fin N) (α β : (Fin N → Bool) → Bool) (La Lb : Finset (Fin N))
    (hα : qDep α La) (hβ : qDep β Lb) (mα : qMon α) (mβ : qMon β)
    (hd : ∀ y : Fin N, y ∉ La ∨ y ∉ Lb) :
    (qP4 U X V Y (fun z => α z && β z) → qP4 U X V Y α ∨ qP4 U X V Y β) ∧
    (qP4 U X V Y (fun z => α z || β z) → qP4 U X V Y α ∨ qP4 U X V Y β) := by
  have hd' : ∀ y : Fin N, y ∉ Lb ∨ y ∉ La := fun y => (hd y).symm
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    simp only [Bool.and_eq_true] at h1 h2 h3
    simp only [Bool.and_eq_false_iff] at h4 h5 h6
    rcases h4 with h4 | h4
    · exact Or.inl (q_andcase U X V Y α β La Lb hα hβ (hd U) (hd X) (hd V) (hd Y)
        h1.1 h2.1 h3.1 h1.2 h2.2 h3.2 h4 h5 h6)
    · exact Or.inr (q_andcase U X V Y β α Lb La hβ hα (hd' U) (hd' X) (hd' V) (hd' Y)
        h1.2 h2.2 h3.2 h1.1 h2.1 h3.1 h4 h5.symm h6.symm)
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    simp only [Bool.or_eq_false_iff] at h4 h5 h6
    simp only [Bool.or_eq_true] at h1
    rcases h1 with h1 | h1
    · exact Or.inl (q_orcase U X V Y α β La Lb hα hβ mβ (hd U) (hd V) h2 h3 h4.1 h4.2 h5.1 h6.1 h1)
    · refine Or.inr (q_orcase U X V Y β α Lb La hβ hα mα (hd' U) (hd' V) ?_ ?_
        h4.2 h4.1 h5.2 h6.2 h1)
      · rw [Bool.or_comm]
        exact h2
      · rw [Bool.or_comm]
        exact h3

theorem q_val_mon (N : ℕ) (C : Circuit) (hAO : PEqualNP.EdgeOwnership.AndOrOnly C) (o : ℕ) :
    qMon (fun x : Fin N → Bool => val C (List.ofFn x) o) := by
  intro S S' hSS h
  exact mono N C hAO (qind S) (qind S') (fun i hi => by
    simp only [qind, decide_eq_true_eq] at hi ⊢
    exact hSS hi) o h

def qpv (C : Circuit) (N k a : ℕ) (x : Fin N → Bool) : Bool :=
  if a < N + k then val C (List.ofFn x) a else false

def qLp (C : Circuit) (N k a : ℕ) : Finset (Fin N) :=
  (Finset.univ.filter fun t : Fin N => t.val = a) ∪
    (if N ≤ a ∧ a < N + k then coneLeaves N C (a - N) else ∅)

theorem q_mem_Lp (C : Circuit) (N k a : ℕ) (t : Fin N) :
    t ∈ qLp C N k a ↔ t.val = a ∨ (N ≤ a ∧ a < N + k ∧ t ∈ coneLeaves N C (a - N)) := by
  unfold qLp
  rw [Finset.mem_union, Finset.mem_filter]
  by_cases h : N ≤ a ∧ a < N + k
  · rw [if_pos h]
    simp only [Finset.mem_univ, true_and]
    constructor
    · rintro (h1 | h1)
      · exact Or.inl h1
      · exact Or.inr ⟨h.1, h.2, h1⟩
    · rintro (h1 | ⟨_, _, h1⟩)
      · exact Or.inl h1
      · exact Or.inr h1
  · rw [if_neg h]
    simp only [Finset.mem_univ, true_and, Finset.notMem_empty, or_false]
    constructor
    · intro h1
      exact Or.inl h1
    · rintro (h1 | ⟨h2, h3, _⟩)
      · exact h1
      · exact absurd ⟨h2, h3⟩ h

theorem q_pv_dep (C : Circuit) (N k a : ℕ) : qDep (qpv C N k a) (qLp C N k a) := by
  intro S S' hS
  unfold qpv
  by_cases hk : a < N + k
  · rw [if_pos hk, if_pos hk]
    by_cases ha : a < N
    · rw [val_ofFn_lt C _ a ha, val_ofFn_lt C _ a ha]
      simp only [qind]
      exact decide_eq_decide.mpr (hS _ ((q_mem_Lp C N k a _).mpr (Or.inl rfl)))
    · obtain ⟨j, rfl⟩ : ∃ j, a = N + j := ⟨a - N, by omega⟩
      apply cone_agree N C (qind S) (qind S') j
      intro t ht
      simp only [qind]
      apply decide_eq_decide.mpr
      apply hS
      rw [q_mem_Lp]
      right
      refine ⟨by omega, hk, ?_⟩
      rw [Nat.add_sub_cancel_left]
      exact ht
  · rw [if_neg hk, if_neg hk]

theorem q_pv_mon (C : Circuit) (hAO : PEqualNP.EdgeOwnership.AndOrOnly C) (N k a : ℕ) :
    qMon (qpv C N k a) := by
  intro S S' hSS h
  unfold qpv at h ⊢
  by_cases hk : a < N + k
  · rw [if_pos hk] at h ⊢
    exact q_val_mon N C hAO a S S' hSS h
  · rw [if_neg hk] at h
    exact absurd h (by decide)

theorem q_input_not (C : Circuit) (N a : ℕ) (ha : a < N) (U X V Y : Fin N) :
    ¬ qP4 U X V Y (fun x => val C (List.ofFn x) a) := by
  rintro ⟨h1, _, _, _, h5, h6⟩
  have e : ∀ x : Fin N → Bool, val C (List.ofFn x) a = x ⟨a, ha⟩ := fun x => val_ofFn_lt C x a ha
  simp only [e, qind, decide_eq_true_eq, decide_eq_false_iff_not, Finset.mem_insert,
    Finset.mem_singleton] at h1 h5 h6
  rcases h1 with h1 | h1
  · exact h5 h1
  · exact h6 h1

theorem q_false_not {N : ℕ} (U X V Y : Fin N) : ¬ qP4 U X V Y (fun _ => false) :=
  fun h => Bool.false_ne_true h.1


theorem q_reader (N : ℕ) (C : Circuit) (k : ℕ) : ∀ j, PEqualNP.EdgeOwnership.InCone N C k j →
    ∃ i ∈ PEqualNP.Core.coneSet N C j, k < i ∧ N + k ∈ (gateAt C i).inputs := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨hj, k', hk', hin, h3⟩ := h
    rcases h3 with h3 | h3
    · rw [← h3] at hk' hin
      exact ⟨j, self_mem_coneSet N C j, hk', hin⟩
    · obtain ⟨i, hi, hki, hin2⟩ := ih k' hk' h3
      exact ⟨i, coneSet_mono N C k' j (inCone_of_read N C k' j hj hk' hin) hi, hki, hin2⟩

theorem q_cs_sub (N : ℕ) (C : Circuit) (k j : ℕ) (hk : k ∈ PEqualNP.Core.coneSet N C j) :
    PEqualNP.Core.coneSet N C k ⊆ PEqualNP.Core.coneSet N C j := by
  rcases (mem_coneSet N C k j).mp hk with h | h
  · subst h
    exact Finset.Subset.refl _
  · exact coneSet_mono N C k j h

def qR (C : Circuit) (k : ℕ) : Finset ℕ := (gateAt C k).inputs.toFinset

theorem q_req (N : ℕ) (C : Circuit) (hAO : PEqualNP.EdgeOwnership.AndOrOnly C) (jo : ℕ)
    (S S0 S' : Finset (Fin N)) (Z : Fin N) (hag : ∀ t, t ≠ Z → (t ∈ S ↔ t ∈ S0))
    (hsub : S0 ⊆ S')
    (hT : val C (List.ofFn (qind S)) (N + jo) = true)
    (hF : val C (List.ofFn (qind S')) (N + jo) = false) : Z ∈ coneLeaves N C jo := by
  by_contra hZ
  have e := cone_agree N C (qind S) (qind S0) jo (fun t ht => by
    have hne : t ≠ Z := fun h => hZ (h ▸ ht)
    simp only [qind]
    exact decide_eq_decide.mpr (hag t hne))
  rw [e] at hT
  have h2 : val C (List.ofFn (qind S')) (N + jo) = true := q_val_mon N C hAO (N + jo) S0 S' hsub hT
  rw [hF] at h2
  exact absurd h2 (by decide)

theorem q_oe (n m : ℕ) (a : Fin n) (b : Fin m) :
    PEqualNP.Represents.oneEach a b =
      List.ofFn (qind ({Fin.castAdd m a, Fin.natAdd n b} : Finset (Fin (n + m)))) := by
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

theorem q_drop0 {N : ℕ} {g : (Fin N → Bool) → Bool} {L : Finset (Fin N)} (h : qDep g L)
    (a : Fin N) (ha : a ∉ L) : g (qind {a}) = g (qind ∅) := by
  apply h
  intro t ht
  have hne : t ≠ a := fun e => ha (e ▸ ht)
  simp only [Finset.mem_singleton, Finset.notMem_empty, iff_false]
  exact hne

theorem q_mon0 {N : ℕ} {g : (Fin N → Bool) → Bool} (h : qMon g) (S : Finset (Fin N))
    (h1 : g (qind ∅) = true) : g (qind S) = true :=
  h _ _ (Finset.empty_subset S) h1

theorem q_p4mem {N : ℕ} {U X V Y : Fin N} {g : (Fin N → Bool) → Bool} {L : Finset (Fin N)}
    (hg : qDep g L) (hP : qP4 U X V Y g) : U ∈ L ∧ X ∈ L ∧ V ∈ L ∧ Y ∈ L := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hP
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_contra hn
    rw [q_drop1 hg U V hn, h6] at h1
    exact absurd h1 (by decide)
  · by_contra hn
    rw [q_drop1 hg X V hn, h6] at h3
    exact absurd h3 (by decide)
  · by_contra hn
    rw [q_drop2 hg U V hn, h5] at h1
    exact absurd h1 (by decide)
  · by_contra hn
    rw [q_drop2 hg U Y hn, h5] at h2
    exact absurd h2 (by decide)

theorem q_split_or {N : ℕ} (U X V Y : Fin N) (α β : (Fin N → Bool) → Bool)
    (La Lb : Finset (Fin N)) (hα : qDep α La) (hβ : qDep β Lb) (mα : qMon α) (mβ : qMon β)
    (hU : U ∉ La ∨ U ∉ Lb) (hV : V ∉ La ∨ V ∉ Lb)
    (hP : qP4 U X V Y (fun z => α z || β z)) : qP4 U X V Y α ∨ qP4 U X V Y β := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hP
  simp only [Bool.or_eq_false_iff] at h4 h5 h6
  simp only [Bool.or_eq_true] at h1
  rcases h1 with h1 | h1
  · exact Or.inl (q_orcase U X V Y α β La Lb hα hβ mβ hU hV h2 h3 h4.1 h4.2 h5.1 h6.1 h1)
  · refine Or.inr (q_orcase U X V Y β α Lb La hβ hα mα hU.symm hV.symm ?_ ?_
      h4.2 h4.1 h5.2 h6.2 h1)
    · rw [Bool.or_comm]
      exact h2
    · rw [Bool.or_comm]
      exact h3

theorem q_split_and {N : ℕ} (U X V Y : Fin N) (α β : (Fin N → Bool) → Bool)
    (La Lb : Finset (Fin N)) (hα : qDep α La) (hβ : qDep β Lb)
    (hU : U ∉ La ∨ U ∉ Lb) (hX : X ∉ La ∨ X ∉ Lb) (hV : V ∉ La ∨ V ∉ Lb) (hY : Y ∉ La ∨ Y ∉ Lb)
    (hP : qP4 U X V Y (fun z => α z && β z)) : qP4 U X V Y α ∨ qP4 U X V Y β := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hP
  simp only [Bool.and_eq_true] at h1 h2 h3
  simp only [Bool.and_eq_false_iff] at h4 h5 h6
  rcases h4 with h4 | h4
  · exact Or.inl (q_andcase U X V Y α β La Lb hα hβ hU hX hV hY
      h1.1 h2.1 h3.1 h1.2 h2.2 h3.2 h4 h5 h6)
  · exact Or.inr (q_andcase U X V Y β α Lb La hβ hα hU.symm hX.symm hV.symm hY.symm
      h1.2 h2.2 h3.2 h1.1 h2.1 h3.1 h4 h5.symm h6.symm)

def qDisj2 (C : Circuit) (N k : ℕ) : Prop :=
  ∀ a b : ℕ, (gateAt C k).inputs = [a, b] → a ≠ b →
    ∀ y : Fin N, y ∉ qLp C N k a ∨ y ∉ qLp C N k b

theorem q_sem2 (C : Circuit) (hM : Monotone2 C) (N : ℕ) (U X V Y : Fin N) :
    ∀ j, j < C.gates.length → (∀ k ∈ PEqualNP.Core.coneSet N C j, qDisj2 C N k) →
      ¬ qP4 U X V Y (fun x => val C (List.ofFn x) (N + j)) := by
  have hAO := andOrOnly_of_monotone2 hM
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj hD hP
    have hfun : (fun x : Fin N → Bool => val C (List.ofFn x) (N + j)) =
        fun x => (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => qpv C N j i x) := by
      funext x
      exact val_gate (n := N) (by simp) hj
    rw [hfun] at hP
    have hg := hM _ (gateAt_mem hj)
    have hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
      have h1 := hg.1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
      exact h1
    have hlen := hg.2
    have hsub : ∀ a ∈ (gateAt C j).inputs, ¬ qP4 U X V Y (qpv C N j a) := by
      intro a ha
      by_cases h1 : a < N
      · have e : qpv C N j a = fun x => val C (List.ofFn x) a := by
          funext x
          unfold qpv
          rw [if_pos (by omega)]
        rw [e]
        exact q_input_not C N a h1 U X V Y
      · by_cases h2 : a < N + j
        · obtain ⟨k', rfl⟩ : ∃ k', a = N + k' := ⟨a - N, by omega⟩
          have e : qpv C N j (N + k') = fun x => val C (List.ofFn x) (N + k') := by
            funext x
            unfold qpv
            rw [if_pos h2]
          rw [e]
          have hk' : k' < j := by omega
          exact ih k' hk' (by omega) (fun k hk => hD k
            (coneSet_mono N C k' j (inCone_of_read N C k' j hj hk' ha) hk))
        · have e : qpv C N j a = fun _ => false := by
            funext x
            unfold qpv
            rw [if_neg h2]
          rw [e]
          exact q_false_not U X V Y
    have hDj := hD j (self_mem_coneSet N C j)
    unfold qDisj2 at hDj
    generalize (gateAt C j).inputs = l at hP hsub hlen hDj
    rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · rcases hop with hop | hop <;> rw [hop] at hP
      · simp [qP4, GateOp.eval] at hP
      · simp [qP4, GateOp.eval] at hP
    · apply hsub a (List.mem_singleton_self a)
      have e : (fun x => (gateAt C j).op.eval ([a].map fun i => qpv C N j i x)) = qpv C N j a := by
        funext x
        rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
      rw [e] at hP
      exact hP
    · by_cases hab : a = b
      · subst hab
        apply hsub a (by simp)
        have e : (fun x => (gateAt C j).op.eval ([a, a].map fun i => qpv C N j i x)) =
            qpv C N j a := by
          funext x
          rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
        rw [e] at hP
        exact hP
      have hd := hDj a b rfl hab
      rcases hop with hop | hop
      · rw [hop] at hP
        have e : (fun x => GateOp.and.eval ([a, b].map fun i => qpv C N j i x)) =
            fun x => qpv C N j a x && qpv C N j b x := by
          funext x
          simp [GateOp.eval]
        rw [e] at hP
        rcases q_split_and U X V Y (qpv C N j a) (qpv C N j b) (qLp C N j a) (qLp C N j b)
          (q_pv_dep C N j a) (q_pv_dep C N j b) (hd U) (hd X) (hd V) (hd Y) hP with h | h
        · exact hsub a (by simp) h
        · exact hsub b (by simp) h
      · rw [hop] at hP
        have e : (fun x => GateOp.or.eval ([a, b].map fun i => qpv C N j i x)) =
            fun x => qpv C N j a x || qpv C N j b x := by
          funext x
          simp [GateOp.eval]
        rw [e] at hP
        rcases q_split_or U X V Y (qpv C N j a) (qpv C N j b) (qLp C N j a) (qLp C N j b)
          (q_pv_dep C N j a) (q_pv_dep C N j b) (q_pv_mon C hAO N j a) (q_pv_mon C hAO N j b)
          (hd U) (hd V) hP with h | h
        · exact hsub a (by simp) h
        · exact hsub b (by simp) h
    · simp at hlen

def qS (C : Circuit) (N k a : ℕ) : Finset ℕ :=
  if N ≤ a ∧ a < N + k then PEqualNP.Core.coneSet N C (a - N) else ∅

theorem q_meet2 (N : ℕ) (C : Circuit) (k ka kb : ℕ) (hkl : k < C.gates.length)
    (hka : ka < k) (hkb : kb < k) (hne : ka ≠ kb)
    (hra : N + ka ∈ (gateAt C k).inputs) (hrb : N + kb ∈ (gateAt C k).inputs)
    (i : ℕ) (hia : i ∈ PEqualNP.Core.coneSet N C ka) (hib : i ∈ PEqualNP.Core.coneSet N C kb) :
    ∃ d1 d2 w, d1 ≠ d2 ∧ d1 ∈ PEqualNP.Core.coneSet N C k ∧
      d2 ∈ PEqualNP.Core.coneSet N C k ∧
      w ∈ (gateAt C d1).inputs ∧ w ∈ (gateAt C d2).inputs ∧ w < N + d1 ∧ w < N + d2 ∧
      d1 ∉ PEqualNP.Core.coneSet N C ka ∧ d2 ∉ PEqualNP.Core.coneSet N C kb := by
  have hsa : PEqualNP.Core.coneSet N C ka ⊆ PEqualNP.Core.coneSet N C k :=
    coneSet_mono N C ka k (inCone_of_read N C ka k hkl hka hra)
  have hsb : PEqualNP.Core.coneSet N C kb ⊆ PEqualNP.Core.coneSet N C k :=
    coneSet_mono N C kb k (inCone_of_read N C kb k hkl hkb hrb)
  have hI : (PEqualNP.Core.coneSet N C ka ∩ PEqualNP.Core.coneSet N C kb).Nonempty :=
    ⟨i, Finset.mem_inter.mpr ⟨hia, hib⟩⟩
  obtain ⟨c, hc, hmax⟩ := Finset.exists_max_image
    (PEqualNP.Core.coneSet N C ka ∩ PEqualNP.Core.coneSet N C kb) (fun t => t) hI
  have hca := (Finset.mem_inter.mp hc).1
  have hcb := (Finset.mem_inter.mp hc).2
  have hle : ∀ t ∈ PEqualNP.Core.coneSet N C ka, t ≤ ka := fun t ht => coneSet_le N C t ka ht
  have hleb : ∀ t ∈ PEqualNP.Core.coneSet N C kb, t ≤ kb := fun t ht => coneSet_le N C t kb ht
  rcases (mem_coneSet N C c ka).mp hca with h1 | h1 <;>
    rcases (mem_coneSet N C c kb).mp hcb with h2 | h2
  · omega
  · obtain ⟨d, hd, hcd, hdin⟩ := q_reader N C c kb h2
    have hdb := hleb d hd
    refine ⟨d, k, N + c, by omega, hsb hd, self_mem_coneSet N C k, hdin,
      by rw [h1]; exact hra, by omega, by omega, ?_, ?_⟩
    · intro hm
      have := hle d hm
      omega
    · intro hm
      have := hleb k hm
      omega
  · obtain ⟨d, hd, hcd, hdin⟩ := q_reader N C c ka h1
    have hda := hle d hd
    refine ⟨k, d, N + c, by omega, self_mem_coneSet N C k, hsa hd, by rw [h2]; exact hrb,
      hdin, by omega, by omega, ?_, ?_⟩
    · intro hm
      have := hle k hm
      omega
    · intro hm
      have := hleb d hm
      omega
  · obtain ⟨d1, hd1, hcd1, hin1⟩ := q_reader N C c ka h1
    obtain ⟨d2, hd2, hcd2, hin2⟩ := q_reader N C c kb h2
    have hd2a : d2 ∉ PEqualNP.Core.coneSet N C ka := by
      intro hm
      have : d2 ≤ c := hmax d2 (Finset.mem_inter.mpr ⟨hm, hd2⟩)
      omega
    have hd1b : d1 ∉ PEqualNP.Core.coneSet N C kb := by
      intro hm
      have : d1 ≤ c := hmax d1 (Finset.mem_inter.mpr ⟨hd1, hm⟩)
      omega
    refine ⟨d2, d1, N + c, ?_, hsb hd2, hsa hd1, hin2, hin1, by omega, by omega, hd2a, hd1b⟩
    intro e
    rw [e] at hd2a
    exact hd2a hd1

theorem q_ovl (N : ℕ) (C : Circuit) (k : ℕ) (hkl : k < C.gates.length) (a b : ℕ) (hab : a ≠ b)
    (ha : a ∈ (gateAt C k).inputs) (hb : b ∈ (gateAt C k).inputs) (y : Fin N)
    (hya : y ∈ qLp C N k a) (hyb : y ∈ qLp C N k b) :
    ∃ d1 d2 w, d1 ≠ d2 ∧ d1 ∈ PEqualNP.Core.coneSet N C k ∧
      d2 ∈ PEqualNP.Core.coneSet N C k ∧
      w ∈ (gateAt C d1).inputs ∧ w ∈ (gateAt C d2).inputs ∧ w < N + d1 ∧ w < N + d2 ∧
      d1 ∉ qS C N k a ∧ d2 ∉ qS C N k b := by
  have y1 := y.isLt
  have hsub : ∀ c, c ∈ (gateAt C k).inputs → N ≤ c → c < N + k →
      PEqualNP.Core.coneSet N C (c - N) ⊆ PEqualNP.Core.coneSet N C k := by
    intro c hc h1 h2
    have hr : N + (c - N) ∈ (gateAt C k).inputs := by
      rw [show N + (c - N) = c by omega]
      exact hc
    exact coneSet_mono N C (c - N) k (inCone_of_read N C (c - N) k hkl (by omega) hr)
  have hSin : ∀ c, N ≤ c → c < N + k → qS C N k c = PEqualNP.Core.coneSet N C (c - N) := by
    intro c h1 h2
    unfold qS
    rw [if_pos ⟨h1, h2⟩]
  have hSout : ∀ c, c < N → qS C N k c = ∅ := by
    intro c h1
    unfold qS
    rw [if_neg (by omega)]
  have hkS : ∀ c, k ∉ qS C N k c := by
    intro c hm
    unfold qS at hm
    split_ifs at hm with h
    · have := coneSet_le N C k (c - N) hm
      omega
    · simp at hm
  rw [q_mem_Lp] at hya hyb
  rcases hya with hya | ⟨ha1, ha2, ha3⟩ <;> rcases hyb with hyb | ⟨hb1, hb2, hb3⟩
  · exact absurd (by omega : a = b) hab
  · rw [mem_coneLeaves] at hb3
    obtain ⟨i, hi, hiy⟩ := hb3
    have hil := coneSet_le N C i (b - N) hi
    refine ⟨i, k, y.val, by omega, hsub b hb hb1 hb2 hi, self_mem_coneSet N C k, hiy,
      by rw [hya]; exact ha, by omega, by omega, ?_, hkS b⟩
    rw [hSout a (by omega)]
    exact Finset.notMem_empty _
  · rw [mem_coneLeaves] at ha3
    obtain ⟨i, hi, hiy⟩ := ha3
    have hil := coneSet_le N C i (a - N) hi
    refine ⟨k, i, y.val, by omega, self_mem_coneSet N C k, hsub a ha ha1 ha2 hi,
      by rw [hyb]; exact hb, hiy, by omega, by omega, hkS a, ?_⟩
    rw [hSout b (by omega)]
    exact Finset.notMem_empty _
  · rw [mem_coneLeaves] at ha3 hb3
    obtain ⟨i1, hi1, hiy1⟩ := ha3
    obtain ⟨i2, hi2, hiy2⟩ := hb3
    have hra : N + (a - N) ∈ (gateAt C k).inputs := by
      rw [show N + (a - N) = a by omega]
      exact ha
    have hrb : N + (b - N) ∈ (gateAt C k).inputs := by
      rw [show N + (b - N) = b by omega]
      exact hb
    rw [hSin a ha1 ha2, hSin b hb1 hb2]
    by_cases h1 : i1 ∈ PEqualNP.Core.coneSet N C (b - N)
    · exact q_meet2 N C k (a - N) (b - N) hkl (by omega) (by omega) (by omega) hra hrb i1 hi1 h1
    by_cases h2 : i2 ∈ PEqualNP.Core.coneSet N C (a - N)
    · exact q_meet2 N C k (a - N) (b - N) hkl (by omega) (by omega) (by omega) hra hrb i2 h2 hi2
    have hne : i2 ≠ i1 := by
      intro e
      rw [e] at hi2
      exact h1 hi2
    refine ⟨i2, i1, y.val, hne, hsub b hb hb1 hb2 hi2, hsub a ha ha1 ha2 hi1, hiy2, hiy1,
      by omega, by omega, h2, h1⟩

theorem q_A0 (N : ℕ) (C : Circuit) (G : Finset ℕ)
    (hG : ∀ k ∈ G, PEqualNP.Core.coneSet N C k ⊆ G)
    (hND : ∀ k1 ∈ G, ∀ k2 ∈ G, k1 ≠ k2 → ∀ w, w ∈ (gateAt C k1).inputs →
      w ∈ (gateAt C k2).inputs → w < N + k1 → w < N + k2 → False) :
    ∀ k' ∈ G, qDisj2 C N k' := by
  intro k' hk' a b hab hne y
  by_contra hcon
  simp only [not_or, not_not] at hcon
  have hkl : k' < C.gates.length := by
    by_contra hge
    rw [gateAt_ge (by omega)] at hab
    simp at hab
  obtain ⟨d1, d2, w, hd, hd1, hd2, hw1, hw2, hb1, hb2, _, _⟩ :=
    q_ovl N C k' hkl a b hne (by rw [hab]; simp) (by rw [hab]; simp) y hcon.1 hcon.2
  exact hND d1 (hG k' hk' hd1) d2 (hG k' hk' hd2) hd w hw1 hw2 hb1 hb2

theorem q_lemA (N : ℕ) (C : Circuit) (G : Finset ℕ)
    (hG : ∀ k ∈ G, PEqualNP.Core.coneSet N C k ⊆ G) (z p1 p2 : ℕ)
    (hz1 : ∀ k3 ∈ G, ∀ k4 ∈ G, k3 ≠ k4 → ∀ w, w ∈ (gateAt C k3).inputs →
      w ∈ (gateAt C k4).inputs → w < N + k3 → w < N + k4 → w = z)
    (hz2 : ∀ k3 ∈ G, z ∈ (gateAt C k3).inputs → z < N + k3 → k3 = p1 ∨ k3 = p2)
    (k : ℕ) (hk : k ∈ G)
    (hns : ¬ (p1 ∈ PEqualNP.Core.coneSet N C k ∧ p2 ∈ PEqualNP.Core.coneSet N C k)) :
    ∀ k' ∈ PEqualNP.Core.coneSet N C k, qDisj2 C N k' := by
  apply q_A0 N C (PEqualNP.Core.coneSet N C k) (fun k' hk' => q_cs_sub N C k' k hk')
  intro k1 hk1 k2 hk2 hne w h1 h2 b1 b2
  have hw := hz1 k1 (hG k hk hk1) k2 (hG k hk hk2) hne w h1 h2 b1 b2
  rw [hw] at h1 h2 b1 b2
  rcases hz2 k1 (hG k hk hk1) h1 b1 with e1 | e1 <;> rcases hz2 k2 (hG k hk hk2) h2 b2 with e2 | e2
  · exact hne (e1.trans e2.symm)
  · rw [e1] at hk1
    rw [e2] at hk2
    exact hns ⟨hk1, hk2⟩
  · rw [e1] at hk1
    rw [e2] at hk2
    exact hns ⟨hk2, hk1⟩
  · exact hne (e1.trans e2.symm)

theorem q_memR (C : Circuit) (k w : ℕ) (h : w ∈ (gateAt C k).inputs) : w ∈ qR C k := by
  unfold qR
  exact List.mem_toFinset.mpr h

theorem q_sv (C : Circuit) (H : Finset ℕ) (k : ℕ) (hk : k ∈ H) :
    (H.biUnion (qR C)).card + (qR C k ∩ (H.erase k).biUnion (qR C)).card ≤
      (qR C k).card + ((H.erase k).biUnion (qR C)).card := by
  have hsub : H.biUnion (qR C) ⊆ qR C k ∪ (H.erase k).biUnion (qR C) := by
    intro t ht
    rw [Finset.mem_biUnion] at ht
    obtain ⟨k', hk', ht'⟩ := ht
    by_cases hkk : k' = k
    · rw [hkk] at ht'
      exact Finset.mem_union_left _ ht'
    · exact Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨k', Finset.mem_erase.mpr ⟨hkk, hk'⟩, ht'⟩)
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_add_card_inter (qR C k) ((H.erase k).biUnion (qR C))
  omega

theorem q_sum (C : Circuit) (H : Finset ℕ) (k : ℕ) (hk : k ∈ H) :
    ∑ a ∈ H, (qR C a).card = (qR C k).card + ∑ a ∈ H.erase k, (qR C a).card :=
  (Finset.add_sum_erase H (fun a => (qR C a).card) hk).symm

theorem q_inter1 (C : Circuit) (H : Finset ℕ) (k k' : ℕ) (hk' : k' ∈ H) (hne : k ≠ k')
    (w : ℕ) (hw : w ∈ (gateAt C k).inputs) (hw' : w ∈ (gateAt C k').inputs) :
    w ∈ qR C k ∩ (H.erase k).biUnion (qR C) :=
  Finset.mem_inter.mpr ⟨q_memR C k w hw, Finset.mem_biUnion.mpr
    ⟨k', Finset.mem_erase.mpr ⟨fun e => hne e.symm, hk'⟩, q_memR C k' w hw'⟩⟩

theorem q_sv1 (C : Circuit) (H : Finset ℕ) (k k' : ℕ) (hk : k ∈ H) (hk' : k' ∈ H)
    (hne : k ≠ k') (w : ℕ) (hw : w ∈ (gateAt C k).inputs) (hw' : w ∈ (gateAt C k').inputs) :
    (H.biUnion (qR C)).card + 1 ≤ ∑ a ∈ H, (qR C a).card := by
  have h1 := q_sv C H k hk
  have h2 := q_sum C H k hk
  have h3 : ((H.erase k).biUnion (qR C)).card ≤ ∑ a ∈ H.erase k, (qR C a).card :=
    Finset.card_biUnion_le
  have h4 : 1 ≤ (qR C k ∩ (H.erase k).biUnion (qR C)).card :=
    Finset.card_pos.mpr ⟨w, q_inter1 C H k k' hk' hne w hw hw'⟩
  omega

theorem q_sv2a (C : Circuit) (H : Finset ℕ) (k k2 k3 k4 : ℕ) (hk : k ∈ H) (hk2 : k2 ∈ H)
    (hk3 : k3 ∈ H) (hk4 : k4 ∈ H) (h12 : k ≠ k2) (h34 : k3 ≠ k4) (hk3' : k3 ≠ k) (hk4' : k4 ≠ k)
    (w w' : ℕ) (hw : w ∈ (gateAt C k).inputs) (hw2 : w ∈ (gateAt C k2).inputs)
    (hw3 : w' ∈ (gateAt C k3).inputs) (hw4 : w' ∈ (gateAt C k4).inputs) :
    (H.biUnion (qR C)).card + 2 ≤ ∑ a ∈ H, (qR C a).card := by
  have h1 := q_sv C H k hk
  have h2 := q_sum C H k hk
  have h3 := q_sv1 C (H.erase k) k3 k4 (Finset.mem_erase.mpr ⟨hk3', hk3⟩)
    (Finset.mem_erase.mpr ⟨hk4', hk4⟩) h34 w' hw3 hw4
  have h4 : 1 ≤ (qR C k ∩ (H.erase k).biUnion (qR C)).card :=
    Finset.card_pos.mpr ⟨w, q_inter1 C H k k2 hk2 h12 w hw hw2⟩
  omega

theorem q_sv2b (C : Circuit) (H : Finset ℕ) (k k2 k4 : ℕ) (hk : k ∈ H) (hk2 : k2 ∈ H)
    (hk4 : k4 ∈ H) (h12 : k ≠ k2) (h14 : k ≠ k4) (w w' : ℕ) (hww : w ≠ w')
    (hw : w ∈ (gateAt C k).inputs) (hw2 : w ∈ (gateAt C k2).inputs)
    (hw' : w' ∈ (gateAt C k).inputs) (hw4 : w' ∈ (gateAt C k4).inputs) :
    (H.biUnion (qR C)).card + 2 ≤ ∑ a ∈ H, (qR C a).card := by
  have h1 := q_sv C H k hk
  have h2 := q_sum C H k hk
  have h3 : ((H.erase k).biUnion (qR C)).card ≤ ∑ a ∈ H.erase k, (qR C a).card :=
    Finset.card_biUnion_le
  have h4 : 2 ≤ (qR C k ∩ (H.erase k).biUnion (qR C)).card := by
    have hsub : ({w, w'} : Finset ℕ) ⊆ qR C k ∩ (H.erase k).biUnion (qR C) := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact q_inter1 C H k k2 hk2 h12 t hw hw2
      · exact q_inter1 C H k k4 hk4 h14 t hw' hw4
    have := Finset.card_le_card hsub
    rw [Finset.card_pair hww] at this
    exact this
  omega

theorem q_low (N : ℕ) (C : Circuit) (G : Finset ℕ) (jo : ℕ) (hjoG : jo ∈ G)
    (hGread : ∀ k ∈ G, k ≠ jo → ∃ i ∈ G, N + k ∈ (gateAt C i).inputs)
    (K : Finset ℕ) (hK1 : ∀ t ∈ K, t < N)
    (hK2 : ∀ t ∈ K, ∃ i ∈ G, t ∈ (gateAt C i).inputs) :
    K.card + (G.card - 1) ≤ (G.biUnion (qR C)).card := by
  have hsub : K ∪ (G.erase jo).image (fun k => N + k) ⊆ G.biUnion (qR C) := by
    intro t ht
    rw [Finset.mem_union] at ht
    rw [Finset.mem_biUnion]
    rcases ht with ht | ht
    · obtain ⟨i, hi, hti⟩ := hK2 t ht
      exact ⟨i, hi, q_memR C i t hti⟩
    · rw [Finset.mem_image] at ht
      obtain ⟨k, hk, rfl⟩ := ht
      rw [Finset.mem_erase] at hk
      obtain ⟨i, hi, hin⟩ := hGread k hk.2 hk.1
      exact ⟨i, hi, q_memR C i _ hin⟩
  have hdisj : Disjoint K ((G.erase jo).image (fun k => N + k)) := by
    rw [Finset.disjoint_left]
    intro t ht ht2
    rw [Finset.mem_image] at ht2
    obtain ⟨k, _, hk⟩ := ht2
    have := hK1 t ht
    omega
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ (fun a b h => Nat.add_left_cancel h),
    Finset.card_erase_of_mem hjoG] at h1
  exact h1

theorem q_count2 (N : ℕ) (C : Circuit) (G : Finset ℕ) (jo : ℕ) (hjoG : jo ∈ G)
    (hR2 : ∀ k ∈ G, (qR C k).card ≤ 2)
    (hGread : ∀ k ∈ G, k ≠ jo → ∃ i ∈ G, N + k ∈ (gateAt C i).inputs)
    (hsav : (G.biUnion (qR C)).card + 2 ≤ ∑ a ∈ G, (qR C a).card)
    (K : Finset ℕ) (hK1 : ∀ t ∈ K, t < N)
    (hK2 : ∀ t ∈ K, ∃ i ∈ G, t ∈ (gateAt C i).inputs) :
    K.card + 1 ≤ G.card := by
  have hGpos : 1 ≤ G.card := Finset.card_pos.mpr ⟨jo, hjoG⟩
  have hlow := q_low N C G jo hjoG hGread K hK1 hK2
  have hs : ∑ a ∈ G, (qR C a).card ≤ 2 * G.card := by
    calc ∑ a ∈ G, (qR C a).card ≤ ∑ a ∈ G, 2 := Finset.sum_le_sum (fun a ha => hR2 a ha)
      _ = 2 * G.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  omega

def qZc (C : Circuit) (N z : ℕ) : Finset ℕ :=
  if N ≤ z ∧ z < N + C.gates.length then PEqualNP.Core.coneSet N C (z - N) else ∅

def qVia {N : ℕ} (g : (Fin N → Bool) → Bool) (Z : Finset (Fin N))
    (zf : (Fin N → Bool) → Bool) : Prop :=
  ∀ S S' : Finset (Fin N), (∀ t, t ∉ Z → (t ∈ S ↔ t ∈ S')) → zf (qind S) = zf (qind S') →
    g (qind S) = g (qind S')

theorem q_zval (C : Circuit) (N z : ℕ) (x : Fin N → Bool) :
    val C (List.ofFn x) z = qpv C N C.gates.length z x := by
  unfold qpv
  split_ifs with h
  · rfl
  · exact val_ge (n := N) (by simp) (by omega)

theorem q_readagree (N : ℕ) (C : Circuit) (G : Finset ℕ)
    (hG : ∀ k ∈ G, PEqualNP.Core.coneSet N C k ⊆ G) (z : ℕ)
    (hz1 : ∀ k3 ∈ G, ∀ k4 ∈ G, k3 ≠ k4 → ∀ w, w ∈ (gateAt C k3).inputs →
      w ∈ (gateAt C k4).inputs → w < N + k3 → w < N + k4 → w = z)
    (hZcG : qZc C N z ⊆ G) (S S' : Finset (Fin N))
    (hS : ∀ t, t ∉ qLp C N C.gates.length z → (t ∈ S ↔ t ∈ S'))
    (hzf : qpv C N C.gates.length z (qind S) = qpv C N C.gates.length z (qind S'))
    (k : ℕ) (hk : k ∈ G) (hkz : k ∉ qZc C N z) (hkl : k < C.gates.length)
    (IH : ∀ t < k, t ∈ G → t ∉ qZc C N z →
      val C (List.ofFn (qind S)) (N + t) = val C (List.ofFn (qind S')) (N + t))
    (r : ℕ) (hr : r ∈ (gateAt C k).inputs) (hrk : r < N + k) :
    val C (List.ofFn (qind S)) r = val C (List.ofFn (qind S')) r := by
  by_cases hrz : r = z
  · rw [hrz, q_zval, q_zval]
    exact hzf
  by_cases hrN : r < N
  · rw [val_ofFn_lt C _ r hrN, val_ofFn_lt C _ r hrN]
    simp only [qind]
    apply decide_eq_decide.mpr
    apply hS
    intro hm
    rw [q_mem_Lp] at hm
    rcases hm with hm | ⟨h1, h2, h3⟩
    · exact hrz hm
    · rw [mem_coneLeaves] at h3
      obtain ⟨i, hi, hin⟩ := h3
      have hiZ : i ∈ qZc C N z := by
        unfold qZc
        rw [if_pos ⟨h1, h2⟩]
        exact hi
      have hik : i ≠ k := by
        intro e
        rw [e] at hiZ
        exact hkz hiZ
      exact hrz (hz1 i (hZcG hiZ) k hk hik r hin hr (by omega) hrk)
  · obtain ⟨t, rfl⟩ : ∃ t, r = N + t := ⟨r - N, by omega⟩
    have htk : t < k := by omega
    have htG : t ∈ G :=
      hG k hk ((mem_coneSet N C t k).mpr (Or.inr (inCone_of_read N C t k hkl htk hr)))
    have htz : t ∉ qZc C N z := by
      intro hm
      unfold qZc at hm
      split_ifs at hm with h
      · rcases (mem_coneSet N C t (z - N)).mp hm with e | e
        · exact hrz (by omega)
        · obtain ⟨d, hd, htd, hdin⟩ := q_reader N C t (z - N) e
          have hdZ : d ∈ qZc C N z := by
            unfold qZc
            rw [if_pos h]
            exact hd
          have hdk : d ≠ k := by
            intro e2
            rw [e2] at hdZ
            exact hkz hdZ
          exact hrz (hz1 d (hZcG hdZ) k hk hdk (N + t) hdin hr (by omega) hrk)
      · simp at hm
    exact IH t htk htG htz

theorem q_D (N : ℕ) (C : Circuit) (G : Finset ℕ)
    (hG : ∀ k ∈ G, PEqualNP.Core.coneSet N C k ⊆ G) (z : ℕ)
    (hz1 : ∀ k3 ∈ G, ∀ k4 ∈ G, k3 ≠ k4 → ∀ w, w ∈ (gateAt C k3).inputs →
      w ∈ (gateAt C k4).inputs → w < N + k3 → w < N + k4 → w = z)
    (hZcG : qZc C N z ⊆ G) (S S' : Finset (Fin N))
    (hS : ∀ t, t ∉ qLp C N C.gates.length z → (t ∈ S ↔ t ∈ S'))
    (hzf : qpv C N C.gates.length z (qind S) = qpv C N C.gates.length z (qind S')) :
    ∀ k, k ∈ G → k ∉ qZc C N z →
      val C (List.ofFn (qind S)) (N + k) = val C (List.ofFn (qind S')) (N + k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hkz
    by_cases hkl : k < C.gates.length
    · rw [val_gate (n := N) (by simp) hkl, val_gate (n := N) (by simp) hkl]
      congr 1
      apply List.map_congr_left
      intro r hr
      by_cases hrk : r < N + k
      · rw [if_pos hrk, if_pos hrk]
        exact q_readagree N C G hG z hz1 hZcG S S' hS hzf k hk hkz hkl
          (fun t ht h1 h2 => ih t ht h1 h2) r hr hrk
      · rw [if_neg hrk, if_neg hrk]
    · rw [val_ge (n := N) (by simp) (by omega), val_ge (n := N) (by simp) (by omega)]

theorem q_viapv (N : ℕ) (C : Circuit) (G : Finset ℕ)
    (hG : ∀ k ∈ G, PEqualNP.Core.coneSet N C k ⊆ G) (z : ℕ)
    (hz1 : ∀ k3 ∈ G, ∀ k4 ∈ G, k3 ≠ k4 → ∀ w, w ∈ (gateAt C k3).inputs →
      w ∈ (gateAt C k4).inputs → w < N + k3 → w < N + k4 → w = z)
    (hZcG : qZc C N z ⊆ G)
    (k : ℕ) (hk : k ∈ G) (hkz : k ∉ qZc C N z) (hkl : k < C.gates.length)
    (a : ℕ) (ha : a ∈ (gateAt C k).inputs) :
    qVia (qpv C N k a) (qLp C N C.gates.length z) (qpv C N C.gates.length z) := by
  intro S S' hS hzf
  show qpv C N k a (qind S) = qpv C N k a (qind S')
  unfold qpv
  by_cases hak : a < N + k
  · rw [if_pos hak, if_pos hak]
    exact q_readagree N C G hG z hz1 hZcG S S' hS hzf k hk hkz hkl
      (fun t _ h1 h2 => q_D N C G hG z hz1 hZcG S S' hS hzf t h1 h2) a ha hak
  · rw [if_neg hak, if_neg hak]

theorem q_meetZ (N : ℕ) (C : Circuit) (G : Finset ℕ)
    (hG : ∀ k ∈ G, PEqualNP.Core.coneSet N C k ⊆ G) (z : ℕ)
    (hz1 : ∀ k3 ∈ G, ∀ k4 ∈ G, k3 ≠ k4 → ∀ w, w ∈ (gateAt C k3).inputs →
      w ∈ (gateAt C k4).inputs → w < N + k3 → w < N + k4 → w = z)
    (k ka kb : ℕ) (hk : k ∈ G) (hkl : k < C.gates.length)
    (hka : ka < k) (hkb : kb < k) (hne : ka ≠ kb)
    (hra : N + ka ∈ (gateAt C k).inputs) (hrb : N + kb ∈ (gateAt C k).inputs)
    (i : ℕ) (hia : i ∈ PEqualNP.Core.coneSet N C ka) (hib : i ∈ PEqualNP.Core.coneSet N C kb) :
    i ∈ qZc C N z := by
  by_contra hiz
  have hsa : PEqualNP.Core.coneSet N C ka ⊆ G := fun t ht =>
    hG k hk (coneSet_mono N C ka k (inCone_of_read N C ka k hkl hka hra) ht)
  have hsb : PEqualNP.Core.coneSet N C kb ⊆ G := fun t ht =>
    hG k hk (coneSet_mono N C kb k (inCone_of_read N C kb k hkl hkb hrb) ht)
  have hF : ((PEqualNP.Core.coneSet N C ka ∩ PEqualNP.Core.coneSet N C kb).filter
      (fun t => t ∉ qZc C N z)).Nonempty :=
    ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_inter.mpr ⟨hia, hib⟩, hiz⟩⟩
  obtain ⟨c, hc, hmax⟩ := Finset.exists_max_image _ (fun t => t) hF
  rw [Finset.mem_filter, Finset.mem_inter] at hc
  obtain ⟨⟨hca, hcb⟩, hcz⟩ := hc
  have hcl : c < C.gates.length := by
    have := coneSet_le N C c ka hca
    omega
  have hzc : ∀ d1 d2, d1 ∈ G → d2 ∈ G → d1 ≠ d2 → N + c ∈ (gateAt C d1).inputs →
      N + c ∈ (gateAt C d2).inputs → N + c < N + d1 → N + c < N + d2 → False := by
    intro d1 d2 h1 h2 h12 i1 i2 b1 b2
    have e := hz1 d1 h1 d2 h2 h12 (N + c) i1 i2 b1 b2
    apply hcz
    unfold qZc
    rw [if_pos ⟨by omega, by omega⟩, show z - N = c by omega]
    exact self_mem_coneSet N C c
  rcases (mem_coneSet N C c ka).mp hca with h1 | h1 <;>
    rcases (mem_coneSet N C c kb).mp hcb with h2 | h2
  · omega
  · obtain ⟨d, hd, hcd, hdin⟩ := q_reader N C c kb h2
    have := coneSet_le N C d kb hd
    exact hzc d k (hsb hd) hk (by omega) hdin (by rw [h1]; exact hra) (by omega) (by omega)
  · obtain ⟨d, hd, hcd, hdin⟩ := q_reader N C c ka h1
    have := coneSet_le N C d ka hd
    exact hzc d k (hsa hd) hk (by omega) hdin (by rw [h2]; exact hrb) (by omega) (by omega)
  · obtain ⟨d1, hd1, hcd1, hin1⟩ := q_reader N C c ka h1
    obtain ⟨d2, hd2, hcd2, hin2⟩ := q_reader N C c kb h2
    by_cases h12 : d1 = d2
    · rw [← h12] at hd2
      have hd1l : d1 < C.gates.length := by
        have := coneSet_le N C d1 ka hd1
        omega
      have hd1z : d1 ∉ qZc C N z := by
        intro hm
        apply hcz
        unfold qZc at hm ⊢
        split_ifs at hm ⊢ with hh
        · exact q_cs_sub N C d1 (z - N) hm
            ((mem_coneSet N C c d1).mpr (Or.inr (inCone_of_read N C c d1 hd1l hcd1 hin1)))
        · simp at hm
      have : d1 ≤ c :=
        hmax d1 (Finset.mem_filter.mpr ⟨Finset.mem_inter.mpr ⟨hd1, hd2⟩, hd1z⟩)
      omega
    · exact hzc d1 d2 (hsa hd1) (hsb hd2) h12 hin1 hin2 (by omega) (by omega)

theorem q_disjZ (N : ℕ) (C : Circuit) (G : Finset ℕ)
    (hG : ∀ k ∈ G, PEqualNP.Core.coneSet N C k ⊆ G) (z : ℕ)
    (hz1 : ∀ k3 ∈ G, ∀ k4 ∈ G, k3 ≠ k4 → ∀ w, w ∈ (gateAt C k3).inputs →
      w ∈ (gateAt C k4).inputs → w < N + k3 → w < N + k4 → w = z)
    (k : ℕ) (hk : k ∈ G) (hkl : k < C.gates.length) (a b : ℕ) (hab : a ≠ b)
    (ha : a ∈ (gateAt C k).inputs) (hb : b ∈ (gateAt C k).inputs) (y : Fin N)
    (hya : y ∈ qLp C N k a) (hyb : y ∈ qLp C N k b) : y ∈ qLp C N C.gates.length z := by
  have y1 := y.isLt
  have hsub : ∀ c, c ∈ (gateAt C k).inputs → N ≤ c → c < N + k →
      PEqualNP.Core.coneSet N C (c - N) ⊆ G := by
    intro c hc h1 h2
    have hr : N + (c - N) ∈ (gateAt C k).inputs := by
      rw [show N + (c - N) = c by omega]
      exact hc
    exact fun t ht => hG k hk
      (coneSet_mono N C (c - N) k (inCone_of_read N C (c - N) k hkl (by omega) hr) ht)
  rw [q_mem_Lp] at hya hyb
  rw [q_mem_Lp]
  rcases hya with hya | ⟨ha1, ha2, ha3⟩ <;> rcases hyb with hyb | ⟨hb1, hb2, hb3⟩
  · exact absurd (by omega : a = b) hab
  · rw [mem_coneLeaves] at hb3
    obtain ⟨i, hi, hiy⟩ := hb3
    have hil := coneSet_le N C i (b - N) hi
    left
    exact hz1 i (hsub b hb hb1 hb2 hi) k hk (by omega) y.val hiy (by rw [hya]; exact ha)
      (by omega) (by omega)
  · rw [mem_coneLeaves] at ha3
    obtain ⟨i, hi, hiy⟩ := ha3
    have hil := coneSet_le N C i (a - N) hi
    left
    exact hz1 i (hsub a ha ha1 ha2 hi) k hk (by omega) y.val hiy (by rw [hyb]; exact hb)
      (by omega) (by omega)
  · rw [mem_coneLeaves] at ha3 hb3
    obtain ⟨i1, hi1, hiy1⟩ := ha3
    obtain ⟨i2, hi2, hiy2⟩ := hb3
    by_cases h12 : i1 = i2
    · rw [← h12] at hi2
      have hra : N + (a - N) ∈ (gateAt C k).inputs := by
        rw [show N + (a - N) = a by omega]
        exact ha
      have hrb : N + (b - N) ∈ (gateAt C k).inputs := by
        rw [show N + (b - N) = b by omega]
        exact hb
      have hiZ := q_meetZ N C G hG z hz1 k (a - N) (b - N) hk hkl (by omega) (by omega)
        (by omega) hra hrb i1 hi1 hi2
      unfold qZc at hiZ
      split_ifs at hiZ with hh
      · right
        refine ⟨hh.1, hh.2, ?_⟩
        rw [mem_coneLeaves]
        exact ⟨i1, hiZ, hiy1⟩
      · simp at hiZ
    · left
      exact hz1 i1 (hsub a ha ha1 ha2 hi1) i2 (hsub b hb hb1 hb2 hi2) h12 y.val hiy1 hiy2
        (by omega) (by omega)

def qPat {N : ℕ} (RR CC : Fin 3 → Fin N) (adj : Fin 3 → Fin 3 → Bool)
    (g : (Fin N → Bool) → Bool) : Prop :=
  (∀ i j, g (qind {RR i, CC j}) = adj i j) ∧ (∀ i j, g (qind {CC j, RR i}) = adj i j) ∧
  (∀ i, g (qind {RR i}) = false) ∧ (∀ j, g (qind {CC j}) = false)

def qIA (adj : Fin 3 → Fin 3 → Bool) (i i2 j j2 : Fin 3) : Prop :=
  adj i j = true ∧ adj i j2 = true ∧ adj i2 j = true ∧ adj i2 j2 = false

def qIB (adj : Fin 3 → Fin 3 → Bool) (j j2 i i2 : Fin 3) : Prop :=
  adj i j = true ∧ adj i2 j = true ∧ adj i j2 = true ∧ adj i2 j2 = false

theorem q_patA {N : ℕ} {RR CC : Fin 3 → Fin N} {adj : Fin 3 → Fin 3 → Bool}
    {g : (Fin N → Bool) → Bool} (hP : qPat RR CC adj g) {i i2 j j2 : Fin 3}
    (hI : qIA adj i i2 j j2) : qP4 (RR i) (RR i2) (CC j) (CC j2) g := by
  obtain ⟨h1, _, h3, h4⟩ := hP
  obtain ⟨e1, e2, e3, e4⟩ := hI
  exact ⟨(h1 i j).trans e1, (h1 i j2).trans e2, (h1 i2 j).trans e3, (h1 i2 j2).trans e4,
    h3 i, h4 j⟩

theorem q_patB {N : ℕ} {RR CC : Fin 3 → Fin N} {adj : Fin 3 → Fin 3 → Bool}
    {g : (Fin N → Bool) → Bool} (hP : qPat RR CC adj g) {i i2 j j2 : Fin 3}
    (hI : qIB adj j j2 i i2) : qP4 (CC j) (CC j2) (RR i) (RR i2) g := by
  obtain ⟨_, h2, h3, h4⟩ := hP
  obtain ⟨e1, e2, e3, e4⟩ := hI
  exact ⟨(h2 i j).trans e1, (h2 i2 j).trans e2, (h2 i j2).trans e3, (h2 i2 j2).trans e4,
    h4 j, h3 i⟩

theorem q_desc1 {N : ℕ} (RR CC : Fin 3 → Fin N) (adj : Fin 3 → Fin 3 → Bool)
    (i i2 j j2 k k2 l l2 : Fin 3) (h1 : qIA adj i i2 j j2) (h2 : qIA adj k k2 l l2)
    (hcov : ∀ r : Fin 3, r = i ∨ r = i2 ∨ r = k ∨ r = k2)
    (hcovc : ∀ c : Fin 3, c = j ∨ c = j2 ∨ c = l ∨ c = l2)
    (s : Fin 3) (hs1 : s = i ∨ s = i2) (hs2 : s = k ∨ s = k2)
    (α β g : (Fin N → Bool) → Bool) (La Lb : Finset (Fin N))
    (hα : qDep α La) (hβ : qDep β Lb) (mα : qMon α) (mβ : qMon β)
    (hd : ∀ y : Fin N, y ∉ La ∨ y ∉ Lb)
    (hg : g = (fun x => α x && β x) ∨ g = (fun x => α x || β x))
    (hP : qPat RR CC adj g) (hA : qP4 (RR i) (RR i2) (CC j) (CC j2) α) :
    qPat RR CC adj α := by
  have hm1 := q_p4mem hα hA
  have hP2 := q_patA hP h2
  have hm2 : RR k ∈ La ∧ RR k2 ∈ La ∧ CC l ∈ La ∧ CC l2 ∈ La := by
    have hor : qP4 (RR k) (RR k2) (CC l) (CC l2) α ∨ qP4 (RR k) (RR k2) (CC l) (CC l2) β := by
      rcases hg with rfl | rfl
      · exact q_split_and _ _ _ _ α β La Lb hα hβ (hd _) (hd _) (hd _) (hd _) hP2
      · exact q_split_or _ _ _ _ α β La Lb hα hβ mα mβ (hd _) (hd _) hP2
    rcases hor with h | h
    · exact q_p4mem hα h
    · exfalso
      have hb := q_p4mem hβ h
      have hsa : RR s ∈ La := by
        rcases hs1 with rfl | rfl
        · exact hm1.1
        · exact hm1.2.1
      have hsb : RR s ∈ Lb := by
        rcases hs2 with rfl | rfl
        · exact hb.1
        · exact hb.2.1
      rcases hd (RR s) with h' | h'
      · exact h' hsa
      · exact h' hsb
  have hrow : ∀ r, RR r ∈ La := by
    intro r
    rcases hcov r with rfl | rfl | rfl | rfl
    · exact hm1.1
    · exact hm1.2.1
    · exact hm2.1
    · exact hm2.2.1
  have hcol : ∀ c, CC c ∈ La := by
    intro c
    rcases hcovc c with rfl | rfl | rfl | rfl
    · exact hm1.2.2.1
    · exact hm1.2.2.2
    · exact hm2.2.2.1
    · exact hm2.2.2.2
  have hnr : ∀ r, RR r ∉ Lb := fun r h => by
    rcases hd (RR r) with h' | h'
    · exact h' (hrow r)
    · exact h' h
  have hnc : ∀ c, CC c ∉ Lb := fun c h => by
    rcases hd (CC c) with h' | h'
    · exact h' (hcol c)
    · exact h' h
  have hb2 : ∀ r c, β (qind {RR r, CC c}) = β (qind ∅) := by
    intro r c
    rw [q_drop2 hβ (RR r) (CC c) (hnc c), q_drop0 hβ (RR r) (hnr r)]
  have hb3 : ∀ r c, β (qind {CC c, RR r}) = β (qind ∅) := by
    intro r c
    rw [q_drop2 hβ (CC c) (RR r) (hnr r), q_drop0 hβ (CC c) (hnc c)]
  have hb4 : ∀ r, β (qind {RR r}) = β (qind ∅) := fun r => q_drop0 hβ (RR r) (hnr r)
  have hb5 : ∀ c, β (qind {CC c}) = β (qind ∅) := fun c => q_drop0 hβ (CC c) (hnc c)
  obtain ⟨p1, p2, p3, p4⟩ := hP
  rcases hg with rfl | rfl
  · cases hb0 : β (qind ∅)
    · exfalso
      have e : (α (qind {RR i, CC j}) && β (qind {RR i, CC j})) = adj i j := p1 i j
      rw [hb2, hb0, Bool.and_false, h1.1] at e
      exact absurd e (by decide)
    · refine ⟨fun r c => ?_, fun r c => ?_, fun r => ?_, fun c => ?_⟩
      · have e : (α (qind {RR r, CC c}) && β (qind {RR r, CC c})) = adj r c := p1 r c
        rw [hb2, hb0, Bool.and_true] at e
        exact e
      · have e : (α (qind {CC c, RR r}) && β (qind {CC c, RR r})) = adj r c := p2 r c
        rw [hb3, hb0, Bool.and_true] at e
        exact e
      · have e : (α (qind {RR r}) && β (qind {RR r})) = false := p3 r
        rw [hb4, hb0, Bool.and_true] at e
        exact e
      · have e : (α (qind {CC c}) && β (qind {CC c})) = false := p4 c
        rw [hb5, hb0, Bool.and_true] at e
        exact e
  · cases hb0 : β (qind ∅)
    · refine ⟨fun r c => ?_, fun r c => ?_, fun r => ?_, fun c => ?_⟩
      · have e : (α (qind {RR r, CC c}) || β (qind {RR r, CC c})) = adj r c := p1 r c
        rw [hb2, hb0, Bool.or_false] at e
        exact e
      · have e : (α (qind {CC c, RR r}) || β (qind {CC c, RR r})) = adj r c := p2 r c
        rw [hb3, hb0, Bool.or_false] at e
        exact e
      · have e : (α (qind {RR r}) || β (qind {RR r})) = false := p3 r
        rw [hb4, hb0, Bool.or_false] at e
        exact e
      · have e : (α (qind {CC c}) || β (qind {CC c})) = false := p4 c
        rw [hb5, hb0, Bool.or_false] at e
        exact e
    · exfalso
      have e : (α (qind {RR i}) || β (qind {RR i})) = false := p3 i
      rw [hb4, hb0, Bool.or_true] at e
      exact absurd e (by decide)

theorem q_desc {N : ℕ} (RR CC : Fin 3 → Fin N) (adj : Fin 3 → Fin 3 → Bool)
    (i i2 j j2 k k2 l l2 : Fin 3) (h1 : qIA adj i i2 j j2) (h2 : qIA adj k k2 l l2)
    (hcov : ∀ r : Fin 3, r = i ∨ r = i2 ∨ r = k ∨ r = k2)
    (hcovc : ∀ c : Fin 3, c = j ∨ c = j2 ∨ c = l ∨ c = l2)
    (s : Fin 3) (hs1 : s = i ∨ s = i2) (hs2 : s = k ∨ s = k2)
    (α β g : (Fin N → Bool) → Bool) (La Lb : Finset (Fin N))
    (hα : qDep α La) (hβ : qDep β Lb) (mα : qMon α) (mβ : qMon β)
    (hd : ∀ y : Fin N, y ∉ La ∨ y ∉ Lb)
    (hg : g = (fun x => α x && β x) ∨ g = (fun x => α x || β x))
    (hP : qPat RR CC adj g) : qPat RR CC adj α ∨ qPat RR CC adj β := by
  have hd' : ∀ y : Fin N, y ∉ Lb ∨ y ∉ La := fun y => (hd y).symm
  have hg' : g = (fun x => β x && α x) ∨ g = (fun x => β x || α x) := by
    rcases hg with rfl | rfl
    · left
      funext x
      exact Bool.and_comm _ _
    · right
      funext x
      exact Bool.or_comm _ _
  have hP1 := q_patA hP h1
  have hor : qP4 (RR i) (RR i2) (CC j) (CC j2) α ∨ qP4 (RR i) (RR i2) (CC j) (CC j2) β := by
    rcases hg with rfl | rfl
    · exact q_split_and _ _ _ _ α β La Lb hα hβ (hd _) (hd _) (hd _) (hd _) hP1
    · exact q_split_or _ _ _ _ α β La Lb hα hβ mα mβ (hd _) (hd _) hP1
  rcases hor with h | h
  · exact Or.inl (q_desc1 RR CC adj i i2 j j2 k k2 l l2 h1 h2 hcov hcovc s hs1 hs2
      α β g La Lb hα hβ mα mβ hd hg hP h)
  · exact Or.inr (q_desc1 RR CC adj i i2 j j2 k k2 l l2 h1 h2 hcov hcovc s hs1 hs2
      β α g Lb La hβ hα mβ mα hd' hg' hP h)

theorem q_o1 {N : ℕ} (Z : Finset (Fin N)) (a b : Fin N) (ha : a ∈ Z) :
    ∀ t, t ∉ Z → (t ∈ ({a, b} : Finset (Fin N)) ↔ t ∈ ({b} : Finset (Fin N))) := by
  intro t ht
  have h1 : t ≠ a := fun e => ht (e ▸ ha)
  simp [h1]

theorem q_o2 {N : ℕ} (Z : Finset (Fin N)) (a b : Fin N) (hb : b ∈ Z) :
    ∀ t, t ∉ Z → (t ∈ ({a, b} : Finset (Fin N)) ↔ t ∈ ({a} : Finset (Fin N))) := by
  intro t ht
  have h1 : t ≠ b := fun e => ht (e ▸ hb)
  simp [h1]

theorem q_o4 {N : ℕ} (Z : Finset (Fin N)) (a b c : Fin N) (ha : a ∈ Z) (hb : b ∈ Z) :
    ∀ t, t ∉ Z → (t ∈ ({a, c} : Finset (Fin N)) ↔ t ∈ ({b, c} : Finset (Fin N))) := by
  intro t ht
  have h1 : t ≠ a := fun e => ht (e ▸ ha)
  have h2 : t ≠ b := fun e => ht (e ▸ hb)
  simp [h1, h2]

theorem q_o5 {N : ℕ} (Z : Finset (Fin N)) (a b c : Fin N) (hb : b ∈ Z) (hc : c ∈ Z) :
    ∀ t, t ∉ Z → (t ∈ ({a, b} : Finset (Fin N)) ↔ t ∈ ({a, c} : Finset (Fin N))) := by
  intro t ht
  have h1 : t ≠ b := fun e => ht (e ▸ hb)
  have h2 : t ≠ c := fun e => ht (e ▸ hc)
  simp [h1, h2]

theorem q_oZ {N : ℕ} (Z S S' : Finset (Fin N)) (hS : ∀ t ∈ S, t ∈ Z) (hS' : ∀ t ∈ S', t ∈ Z) :
    ∀ t, t ∉ Z → (t ∈ S ↔ t ∈ S') := by
  intro t ht
  constructor
  · intro h
    exact absurd (hS t h) ht
  · intro h
    exact absurd (hS' t h) ht

def qRules (adj : Fin 3 → Fin 3 → Bool) (zr zc tr tc : Fin 3 → Bool) : Prop :=
  (∀ i j, adj i j = true → zr i = true → zc j = false → tr i = true) ∧
  (∀ i j, adj i j = true → zc j = true → zr i = false → tc j = true) ∧
  (∀ i j i2, adj i j = true → zr i = true → zc j = true → zr i2 = true → tr i2 = false) ∧
  (∀ i j j2, adj i j = true → zr i = true → zc j = true → zc j2 = true → tc j2 = false) ∧
  (∀ i i2 j, zr i = true → zr i2 = true → zc j = false → tr i = tr i2 → adj i j = adj i2 j) ∧
  (∀ j j2 i, zc j = true → zc j2 = true → zr i = false → tc j = tc j2 → adj i j = adj i j2) ∧
  ¬ ((∀ i, zr i = true) ∧ (∀ j, zc j = true))

theorem q_rules {N : ℕ} (RR CC : Fin 3 → Fin N) (adj : Fin 3 → Fin 3 → Bool)
    (zf g : (Fin N → Bool) → Bool) (Z : Finset (Fin N))
    (vg : qVia g Z zf) (mg : qMon g) (dz : qDep zf Z) (mz : qMon zf)
    (nz : ∀ U X V Y, ¬ qP4 U X V Y zf) (hP : qPat RR CC adj g)
    (i0 i1 j0 j1 : Fin 3) (hI0 : qIA adj i0 i1 j0 j1) :
    qRules adj (fun i => decide (RR i ∈ Z)) (fun j => decide (CC j ∈ Z))
      (fun i => zf (qind {RR i})) (fun j => zf (qind {CC j})) := by
  obtain ⟨P1, P2, P3, P4⟩ := hP
  have hz0 : ∀ a : Fin N, zf (qind {a}) = false → zf (qind ∅) = false := fun a h =>
    q_nf (fun h0 => mz ∅ {a} (Finset.empty_subset _) h0) h
  have hdiff : ∀ S S' : Finset (Fin N), (∀ t ∈ S, t ∈ Z) → (∀ t ∈ S', t ∈ Z) →
      g (qind S) ≠ g (qind S') → zf (qind S) ≠ zf (qind S') := by
    intro S S' hS hS' hne e
    exact hne (vg S S' (q_oZ Z S S' hS hS') e)
  have hin2 : ∀ a b : Fin N, a ∈ Z → b ∈ Z → ∀ t ∈ ({a, b} : Finset (Fin N)), t ∈ Z := by
    intro a b ha hb t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact ha
    · exact hb
  have hin1 : ∀ a : Fin N, a ∈ Z → ∀ t ∈ ({a} : Finset (Fin N)), t ∈ Z := by
    intro a ha t ht
    rw [Finset.mem_singleton] at ht
    rw [ht]
    exact ha
  have hpair : ∀ i j, adj i j = true → RR i ∈ Z → CC j ∈ Z →
      zf (qind {RR i}) = false ∧ zf (qind {CC j}) = false ∧ zf (qind {RR i, CC j}) = true := by
    intro i j hadj hi hj
    have d1 := hdiff {RR i, CC j} {RR i} (hin2 _ _ hi hj) (hin1 _ hi)
      (by rw [P1 i j, P3 i, hadj]; decide)
    have d2 := hdiff {RR i, CC j} {CC j} (hin2 _ _ hi hj) (hin1 _ hj)
      (by rw [P1 i j, P4 j, hadj]; decide)
    have m1 := q_mon1 mz (RR i) (CC j)
    have m2 := q_mon2 mz (RR i) (CC j)
    revert d1 d2 m1 m2
    cases zf (qind {RR i}) <;> cases zf (qind {CC j}) <;> cases zf (qind {RR i, CC j}) <;> decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hadj hzr hzc
    have hzr' : RR i ∈ Z := of_decide_eq_true hzr
    have hzc' : CC j ∉ Z := of_decide_eq_false hzc
    show zf (qind {RR i}) = true
    cases h : zf (qind {RR i})
    · exfalso
      have e := vg {RR i, CC j} {CC j} (q_o1 Z (RR i) (CC j) hzr')
        (by rw [q_drop2 dz (RR i) (CC j) hzc', h, q_drop0 dz (CC j) hzc', hz0 (RR i) h])
      rw [P1 i j, P4 j, hadj] at e
      exact absurd e (by decide)
    · rfl
  · intro i j hadj hzc hzr
    have hzc' : CC j ∈ Z := of_decide_eq_true hzc
    have hzr' : RR i ∉ Z := of_decide_eq_false hzr
    show zf (qind {CC j}) = true
    cases h : zf (qind {CC j})
    · exfalso
      have e := vg {RR i, CC j} {RR i} (q_o2 Z (RR i) (CC j) hzc')
        (by rw [q_drop1 dz (RR i) (CC j) hzr', h, q_drop0 dz (RR i) hzr', hz0 (CC j) h])
      rw [P1 i j, P3 i, hadj] at e
      exact absurd e (by decide)
    · rfl
  · intro i j i2 hadj hzi hzj hzi2
    have hzi' : RR i ∈ Z := of_decide_eq_true hzi
    have hzj' : CC j ∈ Z := of_decide_eq_true hzj
    have hzi2' : RR i2 ∈ Z := of_decide_eq_true hzi2
    show zf (qind {RR i2}) = false
    have hp := hpair i j hadj hzi' hzj'
    cases h : zf (qind {RR i2})
    · rfl
    · exfalso
      exact hdiff {RR i2} {RR i, CC j} (hin1 _ hzi2') (hin2 _ _ hzi' hzj')
        (by rw [P3 i2, P1 i j, hadj]; decide) (by rw [h, hp.2.2])
  · intro i j j2 hadj hzi hzj hzj2
    have hzi' : RR i ∈ Z := of_decide_eq_true hzi
    have hzj' : CC j ∈ Z := of_decide_eq_true hzj
    have hzj2' : CC j2 ∈ Z := of_decide_eq_true hzj2
    show zf (qind {CC j2}) = false
    have hp := hpair i j hadj hzi' hzj'
    cases h : zf (qind {CC j2})
    · rfl
    · exfalso
      exact hdiff {CC j2} {RR i, CC j} (hin1 _ hzj2') (hin2 _ _ hzi' hzj')
        (by rw [P4 j2, P1 i j, hadj]; decide) (by rw [h, hp.2.2])
  · intro i i2 j hzi hzi2 hzj htt
    have hzi' : RR i ∈ Z := of_decide_eq_true hzi
    have hzi2' : RR i2 ∈ Z := of_decide_eq_true hzi2
    have hzj' : CC j ∉ Z := of_decide_eq_false hzj
    rw [← P1 i j, ← P1 i2 j]
    apply vg _ _ (q_o4 Z (RR i) (RR i2) (CC j) hzi' hzi2')
    rw [q_drop2 dz (RR i) (CC j) hzj', q_drop2 dz (RR i2) (CC j) hzj']
    exact htt
  · intro j j2 i hzj hzj2 hzi htt
    have hzj' : CC j ∈ Z := of_decide_eq_true hzj
    have hzj2' : CC j2 ∈ Z := of_decide_eq_true hzj2
    have hzi' : RR i ∉ Z := of_decide_eq_false hzi
    rw [← P1 i j, ← P1 i j2]
    apply vg _ _ (q_o5 Z (RR i) (CC j) (CC j2) hzj' hzj2')
    rw [q_drop1 dz (RR i) (CC j) hzi', q_drop1 dz (RR i) (CC j2) hzi']
    exact htt
  · rintro ⟨hr, hc⟩
    have hr' : ∀ i, RR i ∈ Z := fun i => of_decide_eq_true (hr i)
    have hc' : ∀ j, CC j ∈ Z := fun j => of_decide_eq_true (hc j)
    obtain ⟨e1, e2, e3, e4⟩ := hI0
    have g0 : g (qind ∅) = false :=
      q_nf (fun h0 => mg ∅ {RR i0} (Finset.empty_subset _) h0) (P3 i0)
    have hz2 : ∀ i j, adj i j = true → zf (qind {RR i, CC j}) = true ∧ zf (qind ∅) = false := by
      intro i j hadj
      have d := hdiff {RR i, CC j} ∅ (hin2 _ _ (hr' i) (hc' j)) (by simp)
        (by rw [P1 i j, g0, hadj]; decide)
      have m := mz ∅ {RR i, CC j} (Finset.empty_subset _)
      revert d m
      cases zf (qind {RR i, CC j}) <;> cases zf (qind ∅) <;> decide
    have t1 := hz2 i0 j0 e1
    have t2 := hz2 i0 j1 e2
    have t3 := hz2 i1 j0 e3
    apply nz (RR i0) (RR i1) (CC j0) (CC j1)
    refine ⟨t1.1, t2.1, t3.1, ?_, ?_, ?_⟩
    · have d := hdiff {RR i1, CC j1} {RR i0, CC j0} (hin2 _ _ (hr' i1) (hc' j1))
        (hin2 _ _ (hr' i0) (hc' j0)) (by rw [P1 i1 j1, P1 i0 j0, e4, e1]; decide)
      rw [t1.1] at d
      revert d
      cases zf (qind {RR i1, CC j1}) <;> decide
    · have d := hdiff {RR i0} {RR i0, CC j0} (hin1 _ (hr' i0))
        (hin2 _ _ (hr' i0) (hc' j0)) (by rw [P3 i0, P1 i0 j0, e1]; decide)
      rw [t1.1] at d
      revert d
      cases zf (qind {RR i0}) <;> decide
    · have d := hdiff {CC j0} {RR i0, CC j0} (hin1 _ (hc' j0))
        (hin2 _ _ (hr' i0) (hc' j0)) (by rw [P4 j0, P1 i0 j0, e1]; decide)
      rw [t1.1] at d
      revert d
      cases zf (qind {CC j0}) <;> decide

def qGood (adj : Fin 3 → Fin 3 → Bool) (zr zc : Fin 3 → Bool) : Prop :=
  (∀ i j, adj i j = true → zr i = true → zc j = true → False) ∧
  (∀ i i2, zr i = true → zr i2 = true → i = i2) ∧
  (∀ j j2, zc j = true → zc j2 = true → j = j2)

def qGraph (adj : Fin 3 → Fin 3 → Bool) : Prop :=
  (∀ i, ∃ j, adj i j = true) ∧ (∀ j, ∃ i, adj i j = true) ∧
  (∀ i i2, i ≠ i2 → ∃ j, adj i j ≠ adj i2 j) ∧ (∀ j j2, j ≠ j2 → ∃ i, adj i j ≠ adj i j2) ∧
  (∀ zr zc : Fin 3 → Bool, ((∃ i, zr i = true) ∨ (∃ j, zc j = true)) →
    ((∃ i, zr i = false) ∨ (∃ j, zc j = false)) → ∃ i j, adj i j = true ∧ zr i ≠ zc j)

theorem q_good (adj : Fin 3 → Fin 3 → Bool) (hgr : qGraph adj) (zr zc tr tc : Fin 3 → Bool)
    (hR : qRules adj zr zc tr tc) : qGood adj zr zc := by
  obtain ⟨R1, R1c, R3, R3c, R5, R5c, R6⟩ := hR
  obtain ⟨G1, G1c, G2, G2c, G3⟩ := hgr
  have good1 : ∀ i j, adj i j = true → zr i = true → zc j = true → False := by
    intro i j hadj hzi hzj
    have t0 : ∀ i', zr i' = true → tr i' = false := fun i' h => R3 i j i' hadj hzi hzj h
    have t0c : ∀ j', zc j' = true → tc j' = false := fun j' h => R3c i j j' hadj hzi hzj h
    by_cases h1 : ∀ i', zr i' = true
    · by_cases h2 : ∀ j', zc j' = true
      · exact R6 ⟨h1, h2⟩
      · obtain ⟨j', hj'⟩ := not_forall.mp h2
        have hj'' : zc j' = false := by simpa using hj'
        obtain ⟨i2, j2, hadj2, hne⟩ := G3 zr zc (Or.inl ⟨i, hzi⟩) (Or.inr ⟨j', hj''⟩)
        cases hr : zr i2 <;> cases hc : zc j2
        · rw [hr, hc] at hne
          exact hne rfl
        · have := R1c i2 j2 hadj2 hc hr
          rw [t0c j2 hc] at this
          exact absurd this (by decide)
        · have := R1 i2 j2 hadj2 hr hc
          rw [t0 i2 hr] at this
          exact absurd this (by decide)
        · rw [hr, hc] at hne
          exact hne rfl
    · obtain ⟨i', hi'⟩ := not_forall.mp h1
      have hi'' : zr i' = false := by simpa using hi'
      obtain ⟨i2, j2, hadj2, hne⟩ := G3 zr zc (Or.inl ⟨i, hzi⟩) (Or.inl ⟨i', hi''⟩)
      cases hr : zr i2 <;> cases hc : zc j2
      · rw [hr, hc] at hne
        exact hne rfl
      · have := R1c i2 j2 hadj2 hc hr
        rw [t0c j2 hc] at this
        exact absurd this (by decide)
      · have := R1 i2 j2 hadj2 hr hc
        rw [t0 i2 hr] at this
        exact absurd this (by decide)
      · rw [hr, hc] at hne
        exact hne rfl
  refine ⟨good1, ?_, ?_⟩
  · intro i i2 hzi hzi2
    by_contra hne
    have typ : ∀ r, zr r = true → tr r = true := by
      intro r hzr
      obtain ⟨j0, hj0⟩ := G1 r
      cases hc : zc j0
      · exact R1 r j0 hj0 hzr hc
      · exact absurd (good1 r j0 hj0 hzr hc) id
    obtain ⟨j, hj⟩ := G2 i i2 hne
    apply hj
    cases hc : zc j
    · exact R5 i i2 j hzi hzi2 hc ((typ i hzi).trans (typ i2 hzi2).symm)
    · cases ha : adj i j <;> cases hb : adj i2 j
      · rfl
      · exact absurd (good1 i2 j hb hzi2 hc) id
      · exact absurd (good1 i j ha hzi hc) id
      · rfl
  · intro j j2 hzj hzj2
    by_contra hne
    have typ : ∀ c, zc c = true → tc c = true := by
      intro c hzc
      obtain ⟨i0, hi0⟩ := G1c c
      cases hr : zr i0
      · exact R1c i0 c hi0 hzc hr
      · exact absurd (good1 i0 c hi0 hr hzc) id
    obtain ⟨i, hi⟩ := G2c j j2 hne
    apply hi
    cases hr : zr i
    · exact R5c j j2 i hzj hzj2 hr ((typ j hzj).trans (typ j2 hzj2).symm)
    · cases ha : adj i j <;> cases hb : adj i j2
      · rfl
      · exact absurd (good1 i j2 hb hr hzj2) id
      · exact absurd (good1 i j ha hr hzj) id
      · rfl

def qConds (adj : Fin 3 → Fin 3 → Bool) (zr zc : Fin 3 → Bool) : Prop :=
  ((∃ i i2 j j2, qIA adj i i2 j j2 ∧ zr i = false ∧ zc j = false) ∨
   (∃ j j2 i i2, qIB adj j j2 i i2 ∧ zc j = false ∧ zr i = false)) ∧
  ((∃ i i2 j j2, qIA adj i i2 j j2 ∧ zr i = false ∧ zr i2 = false ∧ zc j = false ∧
      zc j2 = false) ∨
   (∃ j j2 i i2, qIB adj j j2 i i2 ∧ zc j = false ∧ zc j2 = false ∧ zr i = false ∧
      zr i2 = false) ∨
   (∃ u v y x w, zr u = true ∧ zc v = false ∧ zc y = false ∧ zr x = false ∧ zr w = false ∧
      adj x v = true ∧ adj u v = true ∧ adj u y = true ∧ adj w y = true ∧ adj x y = false) ∨
   (∃ u v y x w, zc u = true ∧ zr v = false ∧ zr y = false ∧ zc x = false ∧ zc w = false ∧
      adj v x = true ∧ adj v u = true ∧ adj y u = true ∧ adj y w = true ∧ adj y x = false) ∨
   (∃ v y u u2, zr v = false ∧ zc y = false ∧ adj v y = true ∧ zc u = true ∧ adj v u = true ∧
      zr u2 = true ∧ adj u2 y = true))

theorem q_p5 {N : ℕ} (U X V Y W : Fin N) (α β : (Fin N → Bool) → Bool) (La Lb : Finset (Fin N))
    (hα : qDep α La) (hβ : qDep β Lb) (mα : qMon α) (mβ : qMon β)
    (hV : V ∉ La ∨ V ∉ Lb) (hY : Y ∉ La ∨ Y ∉ Lb) (hW : W ∉ La ∨ W ∉ Lb)
    (a0 : α (qind ∅) = false) (b0 : β (qind ∅) = false)
    (e1 : (α (qind {U, V}) && β (qind {U, V})) = true)
    (e2 : (α (qind {U, Y}) && β (qind {U, Y})) = true)
    (e3 : (α (qind {X, V}) && β (qind {X, V})) = true)
    (e4 : (α (qind {Y, W}) && β (qind {Y, W})) = true)
    (e5 : (α (qind {X, Y}) && β (qind {X, Y})) = false)
    (s1 : (α (qind {U}) && β (qind {U})) = false) : False := by
  simp only [Bool.and_eq_true] at e1 e2 e3 e4
  rw [Bool.and_eq_false_iff] at s1
  rcases s1 with s1 | s1
  · have hVa : V ∈ La := by
      by_contra hn
      have h := e1.1
      rw [q_drop2 hα U V hn, s1] at h
      exact absurd h (by decide)
    have hYa : Y ∈ La := by
      by_contra hn
      have h := e2.1
      rw [q_drop2 hα U Y hn, s1] at h
      exact absurd h (by decide)
    have hVb : V ∉ Lb := hV.resolve_left (fun h => h hVa)
    have hYb : Y ∉ Lb := hY.resolve_left (fun h => h hYa)
    have bX : β (qind {X}) = true := by
      have h := e3.2
      rw [q_drop2 hβ X V hVb] at h
      exact h
    have bW : β (qind {W}) = true := by
      have h := e4.2
      rw [q_drop1 hβ Y W hYb] at h
      exact h
    have hWb : W ∈ Lb := by
      by_contra hn
      rw [q_drop0 hβ W hn, b0] at bW
      exact absurd bW (by decide)
    have hWa : W ∉ La := hW.resolve_right (fun h => h hWb)
    have aY : α (qind {Y}) = true := by
      have h := e4.1
      rw [q_drop2 hα Y W hWa] at h
      exact h
    have h1 := q_mon2 mα X Y aY
    have h2 := q_mon1 mβ X Y bX
    rw [h1, h2] at e5
    exact absurd e5 (by decide)
  · have hVb : V ∈ Lb := by
      by_contra hn
      have h := e1.2
      rw [q_drop2 hβ U V hn, s1] at h
      exact absurd h (by decide)
    have hYb : Y ∈ Lb := by
      by_contra hn
      have h := e2.2
      rw [q_drop2 hβ U Y hn, s1] at h
      exact absurd h (by decide)
    have hVa : V ∉ La := hV.resolve_right (fun h => h hVb)
    have hYa : Y ∉ La := hY.resolve_right (fun h => h hYb)
    have aX : α (qind {X}) = true := by
      have h := e3.1
      rw [q_drop2 hα X V hVa] at h
      exact h
    have aW : α (qind {W}) = true := by
      have h := e4.1
      rw [q_drop1 hα Y W hYa] at h
      exact h
    have hWa : W ∈ La := by
      by_contra hn
      rw [q_drop0 hα W hn, a0] at aW
      exact absurd aW (by decide)
    have hWb : W ∉ Lb := hW.resolve_left (fun h => h hWa)
    have bY : β (qind {Y}) = true := by
      have h := e4.2
      rw [q_drop2 hβ Y W hWb] at h
      exact h
    have h1 := q_mon1 mα X Y aX
    have h2 := q_mon2 mβ X Y bY
    rw [h1, h2] at e5
    exact absurd e5 (by decide)

theorem q_tri {N : ℕ} (U U' V Y : Fin N) (α β : (Fin N → Bool) → Bool) (La Lb : Finset (Fin N))
    (hα : qDep α La) (hβ : qDep β Lb)
    (hV : V ∉ La ∨ V ∉ Lb) (hY : Y ∉ La ∨ Y ∉ Lb)
    (a0 : α (qind ∅) = false) (b0 : β (qind ∅) = false)
    (e1 : (α (qind {U, V}) && β (qind {U, V})) = true)
    (e2 : (α (qind {U', Y}) && β (qind {U', Y})) = true)
    (e3 : (α (qind {V, Y}) && β (qind {V, Y})) = true)
    (s1 : (α (qind {U}) && β (qind {U})) = false)
    (hαU : α (qind {U}) = α (qind {U'})) (hβU : β (qind {U}) = β (qind {U'})) : False := by
  simp only [Bool.and_eq_true] at e1 e2 e3
  rw [Bool.and_eq_false_iff] at s1
  rcases s1 with s1 | s1
  · have s1' : α (qind {U'}) = false := by
      rw [← hαU]
      exact s1
    have hVa : V ∈ La := by
      by_contra hn
      have h := e1.1
      rw [q_drop2 hα U V hn, s1] at h
      exact absurd h (by decide)
    have hYa : Y ∈ La := by
      by_contra hn
      have h := e2.1
      rw [q_drop2 hα U' Y hn, s1'] at h
      exact absurd h (by decide)
    have hVb : V ∉ Lb := hV.resolve_left (fun h => h hVa)
    have hYb : Y ∉ Lb := hY.resolve_left (fun h => h hYa)
    have h := e3.2
    rw [q_drop1 hβ V Y hVb, q_drop0 hβ Y hYb, b0] at h
    exact absurd h (by decide)
  · have s1' : β (qind {U'}) = false := by
      rw [← hβU]
      exact s1
    have hVb : V ∈ Lb := by
      by_contra hn
      have h := e1.2
      rw [q_drop2 hβ U V hn, s1] at h
      exact absurd h (by decide)
    have hYb : Y ∈ Lb := by
      by_contra hn
      have h := e2.2
      rw [q_drop2 hβ U' Y hn, s1'] at h
      exact absurd h (by decide)
    have hVa : V ∉ La := hV.resolve_right (fun h => h hVb)
    have hYa : Y ∉ La := hY.resolve_right (fun h => h hYb)
    have h := e3.1
    rw [q_drop1 hα V Y hVa, q_drop0 hα Y hYa, a0] at h
    exact absurd h (by decide)

theorem q_absA {N : ℕ} (U X V Y : Fin N) (α β : (Fin N → Bool) → Bool)
    (e : ∀ S, α (qind S) = true) (h : qP4 U X V Y (fun x => α x && β x)) : qP4 U X V Y β := by
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := h
  simp only [e, Bool.true_and] at p1 p2 p3 p4 p5 p6
  exact ⟨p1, p2, p3, p4, p5, p6⟩

theorem q_absB {N : ℕ} (U X V Y : Fin N) (α β : (Fin N → Bool) → Bool)
    (e : ∀ S, β (qind S) = true) (h : qP4 U X V Y (fun x => α x && β x)) : qP4 U X V Y α := by
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := h
  simp only [e, Bool.and_true] at p1 p2 p3 p4 p5 p6
  exact ⟨p1, p2, p3, p4, p5, p6⟩

theorem q_core {N : ℕ} (RR CC : Fin 3 → Fin N) (adj : Fin 3 → Fin 3 → Bool)
    (hgr : qGraph adj) (hdec : ∀ zr zc : Fin 3 → Bool, qGood adj zr zc → qConds adj zr zc)
    (i0 i1 j0 j1 : Fin 3) (hI0 : qIA adj i0 i1 j0 j1)
    (α β zf g : (Fin N → Bool) → Bool) (La Lb Z : Finset (Fin N))
    (hα : qDep α La) (hβ : qDep β Lb) (mα : qMon α) (mβ : qMon β)
    (dz : qDep zf Z) (mz : qMon zf) (vα : qVia α Z zf) (vβ : qVia β Z zf)
    (hd : ∀ y, y ∉ Z → y ∉ La ∨ y ∉ Lb)
    (nα : ∀ U X V Y, ¬ qP4 U X V Y α) (nβ : ∀ U X V Y, ¬ qP4 U X V Y β)
    (nz : ∀ U X V Y, ¬ qP4 U X V Y zf)
    (hg : g = (fun x => α x && β x) ∨ g = (fun x => α x || β x))
    (hP : qPat RR CC adj g) : False := by
  have vg : qVia g Z zf := by
    intro S S' h1 h2
    rcases hg with rfl | rfl
    · show (α (qind S) && β (qind S)) = (α (qind S') && β (qind S'))
      rw [vα S S' h1 h2, vβ S S' h1 h2]
    · show (α (qind S) || β (qind S)) = (α (qind S') || β (qind S'))
      rw [vα S S' h1 h2, vβ S S' h1 h2]
  have mg : qMon g := by
    intro S S' hSS h
    rcases hg with rfl | rfl
    · simp only [Bool.and_eq_true] at h ⊢
      exact ⟨mα S S' hSS h.1, mβ S S' hSS h.2⟩
    · simp only [Bool.or_eq_true] at h ⊢
      rcases h with h | h
      · exact Or.inl (mα S S' hSS h)
      · exact Or.inr (mβ S S' hSS h)
  have hrules := q_rules RR CC adj zf g Z vg mg dz mz nz hP i0 i1 j0 j1 hI0
  have hgood := q_good adj hgr _ _ _ _ hrules
  obtain ⟨hor, hand⟩ := hdec _ _ hgood
  have nZr : ∀ i, decide (RR i ∈ Z) = false → RR i ∉ Z := fun i h => of_decide_eq_false h
  have nZc : ∀ j, decide (CC j ∈ Z) = false → CC j ∉ Z := fun j h => of_decide_eq_false h
  have yZr : ∀ i, decide (RR i ∈ Z) = true → RR i ∈ Z := fun i h => of_decide_eq_true h
  have yZc : ∀ j, decide (CC j ∈ Z) = true → CC j ∈ Z := fun j h => of_decide_eq_true h
  have P1 := hP.1
  have P2 := hP.2.1
  have P3 := hP.2.2.1
  have P4 := hP.2.2.2
  rcases hg with rfl | rfl
  · -- AND gate
    have hP4 := q_patA hP hI0
    have a0 : α (qind ∅) = false := by
      cases h : α (qind ∅)
      · rfl
      · exact absurd (q_absA _ _ _ _ α β (fun S => q_mon0 mα S h) hP4) (nβ _ _ _ _)
    have b0 : β (qind ∅) = false := by
      cases h : β (qind ∅)
      · rfl
      · exact absurd (q_absB _ _ _ _ α β (fun S => q_mon0 mβ S h) hP4) (nα _ _ _ _)
    rcases hand with ⟨i, i2, j, j2, hI, z1, z2, z3, z4⟩ | ⟨j, j2, i, i2, hI, z1, z2, z3, z4⟩ |
      ⟨u, v, y, x, w, zu, zv, zy, zx, zw, e1, e2, e3, e4, e5⟩ |
      ⟨u, v, y, x, w, zu, zv, zy, zx, zw, e1, e2, e3, e4, e5⟩ |
      ⟨v, y, u, u2, zv, zy, e1, zu, e2, zu2, e3⟩
    · rcases q_split_and _ _ _ _ α β La Lb hα hβ (hd _ (nZr i z1)) (hd _ (nZr i2 z2))
        (hd _ (nZc j z3)) (hd _ (nZc j2 z4)) (q_patA hP hI) with h | h
      · exact nα _ _ _ _ h
      · exact nβ _ _ _ _ h
    · rcases q_split_and _ _ _ _ α β La Lb hα hβ (hd _ (nZc j z1)) (hd _ (nZc j2 z2))
        (hd _ (nZr i z3)) (hd _ (nZr i2 z4)) (q_patB hP hI) with h | h
      · exact nα _ _ _ _ h
      · exact nβ _ _ _ _ h
    · exact q_p5 (RR u) (RR x) (CC v) (CC y) (RR w) α β La Lb hα hβ mα mβ
        (hd _ (nZc v zv)) (hd _ (nZc y zy)) (hd _ (nZr w zw)) a0 b0
        ((P1 u v).trans e2) ((P1 u y).trans e3) ((P1 x v).trans e1) ((P2 w y).trans e4)
        ((P1 x y).trans e5) (P3 u)
    · exact q_p5 (CC u) (CC x) (RR v) (RR y) (CC w) α β La Lb hα hβ mα mβ
        (hd _ (nZr v zv)) (hd _ (nZr y zy)) (hd _ (nZc w zw)) a0 b0
        ((P2 v u).trans e2) ((P2 y u).trans e3) ((P2 v x).trans e1) ((P1 y w).trans e4)
        ((P2 y x).trans e5) (P4 u)
    · have tu : zf (qind {CC u}) = true := hrules.2.1 v u e2 zu zv
      have tu2 : zf (qind {RR u2}) = true := hrules.1 u2 y e3 zu2 zy
      have hoff : ∀ t, t ∉ Z → (t ∈ ({CC u} : Finset (Fin N)) ↔ t ∈ ({RR u2} : Finset (Fin N))) :=
        q_oZ Z {CC u} {RR u2}
          (by intro t ht; rw [Finset.mem_singleton] at ht; rw [ht]; exact yZc u zu)
          (by intro t ht; rw [Finset.mem_singleton] at ht; rw [ht]; exact yZr u2 zu2)
      have ezf : zf (qind {CC u}) = zf (qind {RR u2}) := by rw [tu, tu2]
      exact q_tri (CC u) (RR u2) (RR v) (CC y) α β La Lb hα hβ
        (hd _ (nZr v zv)) (hd _ (nZc y zy)) a0 b0
        ((P2 v u).trans e2) ((P1 u2 y).trans e3) ((P1 v y).trans e1) (P4 u)
        (vα _ _ hoff ezf) (vβ _ _ hoff ezf)
  · -- OR gate
    rcases hor with ⟨i, i2, j, j2, hI, z1, z2⟩ | ⟨j, j2, i, i2, hI, z1, z2⟩
    · rcases q_split_or _ _ _ _ α β La Lb hα hβ mα mβ (hd _ (nZr i z1)) (hd _ (nZc j z2))
        (q_patA hP hI) with h | h
      · exact nα _ _ _ _ h
      · exact nβ _ _ _ _ h
    · rcases q_split_or _ _ _ _ α β La Lb hα hβ mα mβ (hd _ (nZc j z1)) (hd _ (nZr i z2))
        (q_patB hP hI) with h | h
      · exact nα _ _ _ _ h
      · exact nβ _ _ _ _ h

theorem q_np (N : ℕ) (C : Circuit) (hM : Monotone2 C) (G : Finset ℕ)
    (hG : ∀ k ∈ G, PEqualNP.Core.coneSet N C k ⊆ G) (z p1 p2 : ℕ)
    (hz1 : ∀ k3 ∈ G, ∀ k4 ∈ G, k3 ≠ k4 → ∀ w, w ∈ (gateAt C k3).inputs →
      w ∈ (gateAt C k4).inputs → w < N + k3 → w < N + k4 → w = z)
    (hz2 : ∀ k3 ∈ G, z ∈ (gateAt C k3).inputs → z < N + k3 → k3 = p1 ∨ k3 = p2)
    (t : ℕ) (ht : t ∈ G) (htl : t < C.gates.length)
    (hns : ¬ (p1 ∈ PEqualNP.Core.coneSet N C t ∧ p2 ∈ PEqualNP.Core.coneSet N C t)) :
    ∀ U X V Y : Fin N, ¬ qP4 U X V Y (fun x => val C (List.ofFn x) (N + t)) := by
  intro U X V Y
  exact q_sem2 C hM N U X V Y t htl (q_lemA N C G hG z p1 p2 hz1 hz2 t ht hns)

theorem q_npv (N : ℕ) (C : Circuit) (hM : Monotone2 C) (G : Finset ℕ)
    (hG : ∀ k ∈ G, PEqualNP.Core.coneSet N C k ⊆ G) (z p1 p2 : ℕ)
    (hz1 : ∀ k3 ∈ G, ∀ k4 ∈ G, k3 ≠ k4 → ∀ w, w ∈ (gateAt C k3).inputs →
      w ∈ (gateAt C k4).inputs → w < N + k3 → w < N + k4 → w = z)
    (hz2 : ∀ k3 ∈ G, z ∈ (gateAt C k3).inputs → z < N + k3 → k3 = p1 ∨ k3 = p2)
    (k : ℕ) (hk : k ∈ G) (hkl : k < C.gates.length) (a : ℕ) (ha : a ∈ (gateAt C k).inputs)
    (hns : ¬ (N ≤ a ∧ a < N + k ∧ p1 ∈ PEqualNP.Core.coneSet N C (a - N) ∧
      p2 ∈ PEqualNP.Core.coneSet N C (a - N))) :
    ∀ U X V Y : Fin N, ¬ qP4 U X V Y (qpv C N k a) := by
  intro U X V Y
  by_cases h1 : a < N
  · have e : qpv C N k a = fun x => val C (List.ofFn x) a := by
      funext x
      unfold qpv
      rw [if_pos (by omega)]
    rw [e]
    exact q_input_not C N a h1 U X V Y
  · by_cases h2 : a < N + k
    · obtain ⟨t, rfl⟩ : ∃ t, a = N + t := ⟨a - N, by omega⟩
      have e : qpv C N k (N + t) = fun x => val C (List.ofFn x) (N + t) := by
        funext x
        unfold qpv
        rw [if_pos h2]
      rw [e]
      have htk : t < k := by omega
      have htG : t ∈ G :=
        hG k hk ((mem_coneSet N C t k).mpr (Or.inr (inCone_of_read N C t k hkl htk ha)))
      have hns' : ¬ (p1 ∈ PEqualNP.Core.coneSet N C t ∧ p2 ∈ PEqualNP.Core.coneSet N C t) := by
        intro hh
        apply hns
        refine ⟨by omega, h2, ?_, ?_⟩
        · rw [show N + t - N = t by omega]
          exact hh.1
        · rw [show N + t - N = t by omega]
          exact hh.2
      exact q_np N C hM G hG z p1 p2 hz1 hz2 t htG (by omega) hns' U X V Y
    · have e : qpv C N k a = fun _ => false := by
        funext x
        unfold qpv
        rw [if_neg h2]
      rw [e]
      exact q_false_not U X V Y

theorem q_nz (N : ℕ) (C : Circuit) (hM : Monotone2 C) (G : Finset ℕ)
    (hG : ∀ k ∈ G, PEqualNP.Core.coneSet N C k ⊆ G) (z p1 p2 : ℕ)
    (hz1 : ∀ k3 ∈ G, ∀ k4 ∈ G, k3 ≠ k4 → ∀ w, w ∈ (gateAt C k3).inputs →
      w ∈ (gateAt C k4).inputs → w < N + k3 → w < N + k4 → w = z)
    (hz2 : ∀ k3 ∈ G, z ∈ (gateAt C k3).inputs → z < N + k3 → k3 = p1 ∨ k3 = p2)
    (hZcG : qZc C N z ⊆ G) (hzb1 : z < N + p1) :
    ∀ U X V Y : Fin N, ¬ qP4 U X V Y (qpv C N C.gates.length z) := by
  intro U X V Y
  by_cases h1 : z < N
  · have e : qpv C N C.gates.length z = fun x => val C (List.ofFn x) z := by
      funext x
      unfold qpv
      rw [if_pos (by omega)]
    rw [e]
    exact q_input_not C N z h1 U X V Y
  · by_cases h2 : z < N + C.gates.length
    · obtain ⟨t, rfl⟩ : ∃ t, z = N + t := ⟨z - N, by omega⟩
      have e : qpv C N C.gates.length (N + t) = fun x => val C (List.ofFn x) (N + t) := by
        funext x
        unfold qpv
        rw [if_pos h2]
      rw [e]
      have htZ : t ∈ qZc C N (N + t) := by
        unfold qZc
        rw [if_pos ⟨by omega, h2⟩, show N + t - N = t by omega]
        exact self_mem_coneSet N C t
      have hns : ¬ (p1 ∈ PEqualNP.Core.coneSet N C t ∧ p2 ∈ PEqualNP.Core.coneSet N C t) := by
        intro hh
        have := coneSet_le N C p1 t hh.1
        omega
      exact q_np N C hM G hG (N + t) p1 p2 hz1 hz2 t (hZcG htZ) (by omega) hns U X V Y
    · have e : qpv C N C.gates.length z = fun _ => false := by
        funext x
        unfold qpv
        rw [if_neg h2]
      rw [e]
      exact q_false_not U X V Y

theorem q_lemB (N : ℕ) (C : Circuit) (hM : Monotone2 C) (G : Finset ℕ)
    (hG : ∀ k ∈ G, PEqualNP.Core.coneSet N C k ⊆ G) (hGl : ∀ k ∈ G, k < C.gates.length)
    (z p1 p2 : ℕ)
    (hz1 : ∀ k3 ∈ G, ∀ k4 ∈ G, k3 ≠ k4 → ∀ w, w ∈ (gateAt C k3).inputs →
      w ∈ (gateAt C k4).inputs → w < N + k3 → w < N + k4 → w = z)
    (hz2 : ∀ k3 ∈ G, z ∈ (gateAt C k3).inputs → z < N + k3 → k3 = p1 ∨ k3 = p2)
    (hp1 : p1 ∈ G) (hzp1 : z ∈ (gateAt C p1).inputs) (hzb1 : z < N + p1)
    (RR CC : Fin 3 → Fin N) (adj : Fin 3 → Fin 3 → Bool) (hgr : qGraph adj)
    (hdec : ∀ zr zc : Fin 3 → Bool, qGood adj zr zc → qConds adj zr zc)
    (ii ii2 jj jj2 kk kk2 ll ll2 : Fin 3) (h1 : qIA adj ii ii2 jj jj2) (h2 : qIA adj kk kk2 ll ll2)
    (hcov : ∀ r : Fin 3, r = ii ∨ r = ii2 ∨ r = kk ∨ r = kk2)
    (hcovc : ∀ c : Fin 3, c = jj ∨ c = jj2 ∨ c = ll ∨ c = ll2)
    (s : Fin 3) (hs1 : s = ii ∨ s = ii2) (hs2 : s = kk ∨ s = kk2) :
    ∀ k, k ∈ G → p1 ∈ PEqualNP.Core.coneSet N C k → p2 ∈ PEqualNP.Core.coneSet N C k →
      ¬ qPat RR CC adj (fun x => val C (List.ofFn x) (N + k)) := by
  have hAO := andOrOnly_of_monotone2 hM
  have hZcG : qZc C N z ⊆ G := by
    intro t ht
    unfold qZc at ht
    split_ifs at ht with h
    · have hr : N + (z - N) ∈ (gateAt C p1).inputs := by
        rw [show N + (z - N) = z by omega]
        exact hzp1
      exact hG p1 hp1 (coneSet_mono N C (z - N) p1
        (inCone_of_read N C (z - N) p1 (hGl p1 hp1) (by omega) hr) ht)
    · simp at ht
  have nz := q_nz N C hM G hG z p1 p2 hz1 hz2 hZcG hzb1
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hp1k hp2k hP
    have hkl := hGl k hk
    have hkz : k ∉ qZc C N z := by
      intro hm
      unfold qZc at hm
      split_ifs at hm with h
      · have := coneSet_le N C k (z - N) hm
        have := coneSet_le N C p1 k hp1k
        omega
      · simp at hm
    have hfun : (fun x : Fin N → Bool => val C (List.ofFn x) (N + k)) =
        fun x => (gateAt C k).op.eval ((gateAt C k).inputs.map fun i => qpv C N k i x) := by
      funext x
      exact val_gate (n := N) (by simp) hkl
    rw [hfun] at hP
    have hg := hM _ (gateAt_mem hkl)
    have hop : (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or := by
      have h0 := hg.1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h0
      exact h0
    have hlen := hg.2
    have hok : ∀ a ∈ (gateAt C k).inputs, ¬ qPat RR CC adj (qpv C N k a) := by
      intro a ha hPa
      by_cases hsa : N ≤ a ∧ a < N + k ∧ p1 ∈ PEqualNP.Core.coneSet N C (a - N) ∧
          p2 ∈ PEqualNP.Core.coneSet N C (a - N)
      · obtain ⟨a1, a2, a3, a4⟩ := hsa
        obtain ⟨t, rfl⟩ : ∃ t, a = N + t := ⟨a - N, by omega⟩
        rw [show N + t - N = t by omega] at a3 a4
        have e : qpv C N k (N + t) = fun x => val C (List.ofFn x) (N + t) := by
          funext x
          unfold qpv
          rw [if_pos a2]
        rw [e] at hPa
        have htk : t < k := by omega
        have htG : t ∈ G :=
          hG k hk ((mem_coneSet N C t k).mpr (Or.inr (inCone_of_read N C t k hkl htk ha)))
        exact ih t htk htG a3 a4 hPa
      · exact q_npv N C hM G hG z p1 p2 hz1 hz2 k hk hkl a ha hsa _ _ _ _ (q_patA hPa h1)
    obtain ⟨l, hl⟩ : ∃ l, (gateAt C k).inputs = l := ⟨_, rfl⟩
    rw [hl] at hP hlen
    rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · rcases hop with hop | hop <;> rw [hop] at hP
      · have := hP.2.2.1 ii
        simp [GateOp.eval] at this
      · have := hP.1 ii jj
        rw [h1.1] at this
        simp [GateOp.eval] at this
    · have e : (fun x => (gateAt C k).op.eval ([a].map fun i => qpv C N k i x)) = qpv C N k a := by
        funext x
        rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
      rw [e] at hP
      exact hok a (by rw [hl]; simp) hP
    · have ha : a ∈ (gateAt C k).inputs := by
        rw [hl]
        simp
      have hb : b ∈ (gateAt C k).inputs := by
        rw [hl]
        simp
      by_cases hab : a = b
      · rw [← hab] at hP
        have e : (fun x => (gateAt C k).op.eval ([a, a].map fun i => qpv C N k i x)) =
            qpv C N k a := by
          funext x
          rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
        rw [e] at hP
        exact hok a ha hP
      have hg' : (fun x => (gateAt C k).op.eval ([a, b].map fun i => qpv C N k i x)) =
            (fun x => qpv C N k a x && qpv C N k b x) ∨
          (fun x => (gateAt C k).op.eval ([a, b].map fun i => qpv C N k i x)) =
            (fun x => qpv C N k a x || qpv C N k b x) := by
        rcases hop with hop | hop
        · left
          funext x
          rw [hop]
          simp [GateOp.eval]
        · right
          funext x
          rw [hop]
          simp [GateOp.eval]
      have hpair : ∀ y : Fin N, y ∈ qLp C N k a → y ∈ qLp C N k b →
          ∃ d1 d2, d1 ∉ qS C N k a ∧ d2 ∉ qS C N k b ∧ (d1 = p1 ∨ d1 = p2) ∧
            (d2 = p1 ∨ d2 = p2) := by
        intro y hya hyb
        obtain ⟨d1, d2, w, hd, hd1, hd2, hw1, hw2, hb1, hb2, hn1, hn2⟩ :=
          q_ovl N C k hkl a b hab ha hb y hya hyb
        have hd1G := hG k hk hd1
        have hd2G := hG k hk hd2
        have hwz := hz1 d1 hd1G d2 hd2G hd w hw1 hw2 hb1 hb2
        rw [hwz] at hw1 hw2 hb1 hb2
        exact ⟨d1, d2, hn1, hn2, hz2 d1 hd1G hw1 hb1, hz2 d2 hd2G hw2 hb2⟩
      by_cases hsa : N ≤ a ∧ a < N + k ∧ p1 ∈ PEqualNP.Core.coneSet N C (a - N) ∧
          p2 ∈ PEqualNP.Core.coneSet N C (a - N)
      · have hd : ∀ y : Fin N, y ∉ qLp C N k a ∨ y ∉ qLp C N k b := by
          intro y
          by_contra hc
          simp only [not_or, not_not] at hc
          obtain ⟨d1, d2, hn1, _, e1, _⟩ := hpair y hc.1 hc.2
          apply hn1
          unfold qS
          rw [if_pos ⟨hsa.1, hsa.2.1⟩]
          rcases e1 with e1 | e1
          · rw [e1]
            exact hsa.2.2.1
          · rw [e1]
            exact hsa.2.2.2
        rcases q_desc RR CC adj ii ii2 jj jj2 kk kk2 ll ll2 h1 h2 hcov hcovc s hs1 hs2
          (qpv C N k a) (qpv C N k b) _ (qLp C N k a) (qLp C N k b)
          (q_pv_dep C N k a) (q_pv_dep C N k b) (q_pv_mon C hAO N k a) (q_pv_mon C hAO N k b)
          hd hg' hP with h | h
        · exact hok a ha h
        · exact hok b hb h
      by_cases hsb : N ≤ b ∧ b < N + k ∧ p1 ∈ PEqualNP.Core.coneSet N C (b - N) ∧
          p2 ∈ PEqualNP.Core.coneSet N C (b - N)
      · have hd : ∀ y : Fin N, y ∉ qLp C N k a ∨ y ∉ qLp C N k b := by
          intro y
          by_contra hc
          simp only [not_or, not_not] at hc
          obtain ⟨d1, d2, _, hn2, _, e2⟩ := hpair y hc.1 hc.2
          apply hn2
          unfold qS
          rw [if_pos ⟨hsb.1, hsb.2.1⟩]
          rcases e2 with e2 | e2
          · rw [e2]
            exact hsb.2.2.1
          · rw [e2]
            exact hsb.2.2.2
        rcases q_desc RR CC adj ii ii2 jj jj2 kk kk2 ll ll2 h1 h2 hcov hcovc s hs1 hs2
          (qpv C N k a) (qpv C N k b) _ (qLp C N k a) (qLp C N k b)
          (q_pv_dep C N k a) (q_pv_dep C N k b) (q_pv_mon C hAO N k a) (q_pv_mon C hAO N k b)
          hd hg' hP with h | h
        · exact hok a ha h
        · exact hok b hb h
      have hdZ : ∀ y, y ∉ qLp C N C.gates.length z → y ∉ qLp C N k a ∨ y ∉ qLp C N k b := by
        intro y hy
        by_contra hc
        simp only [not_or, not_not] at hc
        exact hy (q_disjZ N C G hG z hz1 k hk hkl a b hab ha hb y hc.1 hc.2)
      exact q_core RR CC adj hgr hdec ii ii2 jj jj2 h1 (qpv C N k a) (qpv C N k b)
        (qpv C N C.gates.length z) _ (qLp C N k a) (qLp C N k b) (qLp C N C.gates.length z)
        (q_pv_dep C N k a) (q_pv_dep C N k b) (q_pv_mon C hAO N k a) (q_pv_mon C hAO N k b)
        (q_pv_dep C N C.gates.length z) (q_pv_mon C hAO N C.gates.length z)
        (q_viapv N C G hG z hz1 hZcG k hk hkz hkl a ha)
        (q_viapv N C G hG z hz1 hZcG k hk hkz hkl b hb) hdZ
        (q_npv N C hM G hG z p1 p2 hz1 hz2 k hk hkl a ha hsa)
        (q_npv N C hM G hG z p1 p2 hz1 hz2 k hk hkl b hb hsb) nz hg' hP
    · simp at hlen

theorem q_main (n m s : ℕ) (A : Fin n → Fin m → Bool) (rr : Fin 3 → Fin n) (cc : Fin 3 → Fin m)
    (adj : Fin 3 → Fin 3 → Bool) (hA : ∀ i j, A (rr i) (cc j) = adj i j)
    (hrw : ∀ i, ∃ j, adj i j = false) (hcl : ∀ j, ∃ i, adj i j = false)
    (hgr : qGraph adj) (hdec : ∀ zr zc : Fin 3 → Bool, qGood adj zr zc → qConds adj zr zc)
    (ii ii2 jj jj2 kk kk2 ll ll2 : Fin 3) (h1 : qIA adj ii ii2 jj jj2) (h2 : qIA adj kk kk2 ll ll2)
    (hcov : ∀ r : Fin 3, r = ii ∨ r = ii2 ∨ r = kk ∨ r = kk2)
    (hcovc : ∀ c : Fin 3, c = jj ∨ c = jj2 ∨ c = ll ∨ c = ll2)
    (sx : Fin 3) (hs1 : sx = ii ∨ sx = ii2) (hs2 : sx = kk ∨ sx = kk2)
    (hrep : PEqualNP.Represents.RepSizeAtMost A s) :
    (Finset.univ.filter (fun a : Fin n => ∃ b : Fin m, A a b = true ∧
        ∃ a' : Fin n, A a' b = false)).card +
      (Finset.univ.filter (fun b : Fin m => ∃ a : Fin n, A a b = true ∧
        ∃ b' : Fin m, A a b' = false)).card + 1 ≤ s := by
  obtain ⟨C, hM, hs, hR⟩ := hrep
  have hAO := andOrOnly_of_monotone2 hM
  have hRv : ∀ a b, val C (List.ofFn (qind ({Fin.castAdd m a, Fin.natAdd n b} :
      Finset (Fin (n + m))))) C.output = A a b := by
    intro a b
    rw [← q_oe]
    exact hR a b
  have hmono := q_val_mon (n + m) C hAO C.output
  let RR : Fin 3 → Fin (n + m) := fun i => Fin.castAdd m (rr i)
  let CC : Fin 3 → Fin (n + m) := fun j => Fin.natAdd n (cc j)
  have hPo : qPat RR CC adj (fun z => val C (List.ofFn z) C.output) := by
    refine ⟨fun i j => ?_, fun i j => ?_, fun i => ?_, fun j => ?_⟩
    · exact (hRv (rr i) (cc j)).trans (hA i j)
    · show val C (List.ofFn (qind {Fin.natAdd n (cc j), Fin.castAdd m (rr i)})) C.output = adj i j
      rw [Finset.pair_comm]
      exact (hRv (rr i) (cc j)).trans (hA i j)
    · obtain ⟨j, hj⟩ := hrw i
      exact q_nf (q_mon1 hmono (Fin.castAdd m (rr i)) (Fin.natAdd n (cc j)))
        ((hRv (rr i) (cc j)).trans ((hA i j).trans hj))
    · obtain ⟨i, hi⟩ := hcl j
      exact q_nf (q_mon2 hmono (Fin.castAdd m (rr i)) (Fin.natAdd n (cc j)))
        ((hRv (rr i) (cc j)).trans ((hA i j).trans hi))
  by_cases hlo : C.output < n + m
  · exact absurd (q_patA hPo h1) (q_input_not C (n + m) C.output hlo _ _ _ _)
  by_cases hhi : n + m + C.gates.length ≤ C.output
  · have e : (fun z : Fin (n + m) → Bool => val C (List.ofFn z) C.output) = fun _ => false := by
      funext z
      exact val_ge (n := n + m) (by simp) hhi
    rw [e] at hPo
    exact absurd (q_patA hPo h1) (q_false_not _ _ _ _)
  obtain ⟨jo, hjo⟩ : ∃ jo, C.output = n + m + jo := ⟨C.output - (n + m), by omega⟩
  have hjol : jo < C.gates.length := by omega
  rw [hjo] at hPo hRv
  have hGsub : ∀ k ∈ PEqualNP.Core.coneSet (n + m) C jo,
      PEqualNP.Core.coneSet (n + m) C k ⊆ PEqualNP.Core.coneSet (n + m) C jo :=
    fun k hk => q_cs_sub (n + m) C k jo hk
  have hGlen : ∀ k ∈ PEqualNP.Core.coneSet (n + m) C jo, k < C.gates.length := by
    intro k hk
    have := coneSet_le (n + m) C k jo hk
    omega
  -- counting setup
  have hcount : (∑ a ∈ PEqualNP.Core.coneSet (n + m) C jo, (qR C a).card) ≥
      ((PEqualNP.Core.coneSet (n + m) C jo).biUnion (qR C)).card + 2 →
      (Finset.univ.filter (fun a : Fin n => ∃ b : Fin m, A a b = true ∧
          ∃ a' : Fin n, A a' b = false)).card +
        (Finset.univ.filter (fun b : Fin m => ∃ a : Fin n, A a b = true ∧
          ∃ b' : Fin m, A a b' = false)).card + 1 ≤ s := by
    intro hsav
    set Rf := Finset.univ.filter
      (fun a : Fin n => ∃ b : Fin m, A a b = true ∧ ∃ a' : Fin n, A a' b = false) with hRf
    set Cf := Finset.univ.filter
      (fun b : Fin m => ∃ a : Fin n, A a b = true ∧ ∃ b' : Fin m, A a b' = false) with hCf
    have hcard : (Rf.image (fun a => a.val) ∪ Cf.image (fun b => n + b.val)).card =
        Rf.card + Cf.card := by
      rw [Finset.card_union_of_disjoint,
        Finset.card_image_of_injective _ (fun a b h => Fin.ext h),
        Finset.card_image_of_injective _ (fun a b h => Fin.ext (Nat.add_left_cancel h))]
      rw [Finset.disjoint_left]
      intro t h1 h2
      rw [Finset.mem_image] at h1 h2
      obtain ⟨a, _, ha⟩ := h1
      obtain ⟨b, _, hb⟩ := h2
      have := a.isLt
      omega
    have hK1 : ∀ t ∈ Rf.image (fun a => a.val) ∪ Cf.image (fun b => n + b.val), t < n + m := by
      intro t ht
      rw [Finset.mem_union, Finset.mem_image, Finset.mem_image] at ht
      rcases ht with ⟨a, _, ha⟩ | ⟨b, _, hb⟩
      · have := a.isLt
        omega
      · have := b.isLt
        omega
    have hK2 : ∀ t ∈ Rf.image (fun a => a.val) ∪ Cf.image (fun b => n + b.val),
        ∃ i ∈ PEqualNP.Core.coneSet (n + m) C jo, t ∈ (gateAt C i).inputs := by
      intro t ht
      rw [Finset.mem_union, Finset.mem_image, Finset.mem_image] at ht
      rcases ht with ⟨a, ha, hta⟩ | ⟨b, hb, htb⟩
      · rw [hRf, Finset.mem_filter] at ha
        obtain ⟨b, hab, a', ha'b⟩ := ha.2
        have hL := q_req (n + m) C hAO jo {Fin.castAdd m a, Fin.natAdd n b} {Fin.natAdd n b}
          {Fin.castAdd m a', Fin.natAdd n b} (Fin.castAdd m a) (fun t ht => by
            simp only [Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro (h | h)
              · exact absurd h ht
              · exact h
            · intro h
              exact Or.inr h)
          (Finset.subset_insert _ _) ((hRv a b).trans hab) ((hRv a' b).trans ha'b)
        rw [mem_coneLeaves] at hL
        obtain ⟨i, hi, hin⟩ := hL
        refine ⟨i, hi, ?_⟩
        rw [← hta]
        exact hin
      · rw [hCf, Finset.mem_filter] at hb
        obtain ⟨a, hab, b', hab'⟩ := hb.2
        have hL := q_req (n + m) C hAO jo {Fin.castAdd m a, Fin.natAdd n b} {Fin.castAdd m a}
          {Fin.castAdd m a, Fin.natAdd n b'} (Fin.natAdd n b) (fun t ht => by
            simp only [Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro (h | h)
              · exact h
              · exact absurd h ht
            · intro h
              exact Or.inl h)
          (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _))
          ((hRv a b).trans hab) ((hRv a b').trans hab')
        rw [mem_coneLeaves] at hL
        obtain ⟨i, hi, hin⟩ := hL
        refine ⟨i, hi, ?_⟩
        rw [← htb]
        exact hin
    have hR2 : ∀ k ∈ PEqualNP.Core.coneSet (n + m) C jo, (qR C k).card ≤ 2 := by
      intro k hk
      unfold qR
      exact le_trans (List.toFinset_card_le _) (monotone2_len hM (gateAt_mem (hGlen k hk)))
    have hGread : ∀ k ∈ PEqualNP.Core.coneSet (n + m) C jo, k ≠ jo →
        ∃ i ∈ PEqualNP.Core.coneSet (n + m) C jo, n + m + k ∈ (gateAt C i).inputs := by
      intro k hk hne
      rcases (mem_coneSet (n + m) C k jo).mp hk with h | h
      · exact absurd h hne
      · obtain ⟨i, hi, _, hin⟩ := q_reader (n + m) C k jo h
        exact ⟨i, hi, hin⟩
    have hc := q_count2 (n + m) C (PEqualNP.Core.coneSet (n + m) C jo) jo
      (self_mem_coneSet (n + m) C jo) hR2 hGread hsav _ hK1 hK2
    rw [hcard] at hc
    have h1 : (PEqualNP.Core.coneSet (n + m) C jo).card ≤ C.gates.length := by
      have := Finset.card_le_card (coneSet_sub_range (n + m) C jo hjol)
      rwa [Finset.card_range] at this
    have h2 : C.size = C.gates.length := rfl
    omega
  by_cases hDR : ∃ p1 ∈ PEqualNP.Core.coneSet (n + m) C jo,
      ∃ p2 ∈ PEqualNP.Core.coneSet (n + m) C jo, p1 ≠ p2 ∧
        ∃ z, z ∈ (gateAt C p1).inputs ∧ z ∈ (gateAt C p2).inputs ∧ z < n + m + p1 ∧
          z < n + m + p2
  · obtain ⟨p1, hp1, p2, hp2, hp12, z, hz1in, hz2in, hzb1, hzb2⟩ := hDR
    by_cases hz1 : ∀ k3 ∈ PEqualNP.Core.coneSet (n + m) C jo,
        ∀ k4 ∈ PEqualNP.Core.coneSet (n + m) C jo, k3 ≠ k4 → ∀ w, w ∈ (gateAt C k3).inputs →
          w ∈ (gateAt C k4).inputs → w < n + m + k3 → w < n + m + k4 → w = z
    · by_cases hz2 : ∀ k3 ∈ PEqualNP.Core.coneSet (n + m) C jo, z ∈ (gateAt C k3).inputs →
          z < n + m + k3 → k3 = p1 ∨ k3 = p2
      · exfalso
        exact q_lemB (n + m) C hM (PEqualNP.Core.coneSet (n + m) C jo) hGsub hGlen z p1 p2 hz1 hz2
          hp1 hz1in hzb1 RR CC adj hgr hdec ii ii2 jj jj2 kk kk2 ll ll2 h1 h2 hcov hcovc sx hs1 hs2
          jo (self_mem_coneSet (n + m) C jo) hp1 hp2 hPo
      · apply hcount
        push_neg at hz2
        obtain ⟨k5, hk5, hzk5, _, hk51, hk52⟩ := hz2
        exact q_sv2a C _ p1 p2 p2 k5 hp1 hp2 hp2 hk5 hp12 (fun e => hk52 e.symm)
          (fun e => hp12 e.symm) hk51 z z hz1in hz2in hz2in hzk5
    · apply hcount
      push_neg at hz1
      obtain ⟨k3, hk3, k4, hk4, h34, w, hw3, hw4, _, _, hwz⟩ := hz1
      by_cases e3 : k3 = p1
      · rw [e3] at hw3
        have h14 : p1 ≠ k4 := by rw [← e3]; exact h34
        exact q_sv2b C _ p1 p2 k4 hp1 hp2 hk4 hp12 h14 z w (fun e => hwz e.symm)
          hz1in hz2in hw3 hw4
      by_cases e4 : k4 = p1
      · rw [e4] at hw4
        have h13 : p1 ≠ k3 := fun e => e3 e.symm
        exact q_sv2b C _ p1 p2 k3 hp1 hp2 hk3 hp12 h13 z w (fun e => hwz e.symm)
          hz1in hz2in hw4 hw3
      exact q_sv2a C _ p1 p2 k3 k4 hp1 hp2 hk3 hk4 hp12 h34 e3 e4 z w hz1in hz2in hw3 hw4
  · exfalso
    have hD := q_A0 (n + m) C (PEqualNP.Core.coneSet (n + m) C jo) hGsub
      (fun k1 hk1 k2 hk2 hne w h1 h2 b1 b2 => hDR ⟨k1, hk1, k2, hk2, hne, w, h1, h2, b1, b2⟩)
    exact q_sem2 C hM (n + m) _ _ _ _ jo hjol hD (q_patA hPo h1)

theorem q_fun3 (f : Fin 3 → Bool) : f = ![f 0, f 1, f 2] := by
  funext i
  fin_cases i <;> rfl

def qC6adj : Fin 3 → Fin 3 → Bool :=
  ![![true, true, false], ![false, true, true], ![true, false, true]]

theorem q_c6graph : qGraph qC6adj := by
  refine ⟨by unfold qC6adj; decide, by unfold qC6adj; decide, by unfold qC6adj; decide,
    by unfold qC6adj; decide, ?_⟩
  intro zr zc
  rw [q_fun3 zr, q_fun3 zc]
  generalize zr 0 = a0
  generalize zr 1 = a1
  generalize zr 2 = a2
  generalize zc 0 = b0
  generalize zc 1 = b1
  generalize zc 2 = b2
  cases a0 <;> cases a1 <;> cases a2 <;> cases b0 <;> cases b1 <;> cases b2 <;>
    (unfold qC6adj; decide)

theorem q_c6dec : ∀ zr zc : Fin 3 → Bool, qGood qC6adj zr zc → qConds qC6adj zr zc := by
  intro zr zc
  rw [q_fun3 zr, q_fun3 zc]
  generalize zr 0 = a0
  generalize zr 1 = a1
  generalize zr 2 = a2
  generalize zc 0 = b0
  generalize zc 1 = b1
  generalize zc 2 = b2
  cases a0 <;> cases a1 <;> cases a2 <;> cases b0 <;> cases b1 <;> cases b2 <;> intro hg <;>
    first
    | exact absurd hg (by unfold qGood qC6adj; decide)
    | exact ⟨Or.inl ⟨0, 1, 1, 0, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl⟩, Or.inl ⟨0, 1, 1, 0, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩⟩
    | exact ⟨Or.inl ⟨1, 0, 1, 2, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl⟩, Or.inl ⟨1, 2, 2, 1, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩⟩
    | exact ⟨Or.inl ⟨0, 1, 1, 0, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl⟩, Or.inl ⟨0, 2, 0, 1, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩⟩
    | exact ⟨Or.inl ⟨0, 1, 1, 0, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl⟩, Or.inl ⟨0, 1, 1, 0, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩⟩
    | exact ⟨Or.inl ⟨0, 1, 1, 0, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl⟩, Or.inl ⟨1, 0, 1, 2, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩⟩
    | exact ⟨Or.inl ⟨0, 1, 1, 0, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl⟩, Or.inr (Or.inr (Or.inl ⟨1, 1, 2, 0, 2, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩))⟩
    | exact ⟨Or.inl ⟨0, 2, 0, 1, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl⟩, Or.inl ⟨2, 0, 0, 2, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩⟩
    | exact ⟨Or.inl ⟨0, 2, 0, 1, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl⟩, Or.inr (Or.inr (Or.inl ⟨2, 0, 2, 0, 1, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩))⟩
    | exact ⟨Or.inl ⟨0, 1, 1, 0, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl⟩, Or.inl ⟨0, 1, 1, 0, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩⟩
    | exact ⟨Or.inl ⟨1, 0, 1, 2, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl⟩, Or.inr (Or.inr (Or.inl ⟨0, 0, 1, 2, 1, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩))⟩


theorem main_aux : ∀ (n m s : ℕ) (A : Fin n → Fin m → Bool) (r1 r2 r3 : Fin n) (c1 c2 c3 : Fin m), A r1 c1 = true → A r1 c2 = true → A r2 c2 = true → A r2 c3 = true → A r3 c3 = true → A r3 c1 = true → A r1 c3 = false → A r2 c1 = false → A r3 c2 = false → PEqualNP.Represents.RepSizeAtMost A s → (Finset.univ.filter (fun a : Fin n => ∃ b : Fin m, A a b = true ∧ ∃ a' : Fin n, A a' b = false)).card + (Finset.univ.filter (fun b : Fin m => ∃ a : Fin n, A a b = true ∧ ∃ b' : Fin m, A a b' = false)).card + 1 ≤ s := by
  intro n m s A r1 r2 r3 c1 c2 c3 h11 h12 h22 h23 h33 h31 h13 h21 h32 hrep
  refine q_main n m s A ![r1, r2, r3] ![c1, c2, c3] qC6adj ?_ (by unfold qC6adj; decide)
    (by unfold qC6adj; decide) q_c6graph q_c6dec 0 1 1 0 2 1 2 0
    (by unfold qIA qC6adj; decide) (by unfold qIA qC6adj; decide) (by decide) (by decide)
    1 (by decide) (by decide) hrep
  intro i j
  fin_cases i <;> fin_cases j
  exacts [h11, h12, h13, h21, h22, h23, h31, h32, h33]

end PEqualNP.Outside.L_meta_9440

theorem PEqualNP.Outside.L_meta_9440 : ∀ (n m s : ℕ) (A : Fin n → Fin m → Bool) (r1 r2 r3 : Fin n) (c1 c2 c3 : Fin m), A r1 c1 = true → A r1 c2 = true → A r2 c2 = true → A r2 c3 = true → A r3 c3 = true → A r3 c1 = true → A r1 c3 = false → A r2 c1 = false → A r3 c2 = false → PEqualNP.Represents.RepSizeAtMost A s → (Finset.univ.filter (fun a : Fin n => ∃ b : Fin m, A a b = true ∧ ∃ a' : Fin n, A a' b = false)).card + (Finset.univ.filter (fun b : Fin m => ∃ a : Fin n, A a b = true ∧ ∃ b' : Fin m, A a b' = false)).card + 1 ≤ s :=
  PEqualNP.Outside.L_meta_9440.main_aux
