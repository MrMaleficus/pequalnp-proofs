import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7638

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

-- Body for row 7638. Paper proof: the counted lines are leaves of the output cone. Counting reads
-- in the cone gives (lines) + (cone gates) - 1 <= (distinct wires read) <= 2 (cone gates), with one
-- saving as soon as a wire is read by two cone gates or a cone gate reads fewer than two wires.
-- Without such a saving the two operands of every cone gate have disjoint leaf sets, and an AND or
-- OR of two functions on disjoint leaves never has the induced four-vertex path pattern
-- (q_split), so by induction no cone wire has it, but the output does.

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

def qDisj (C : Circuit) (N k : ℕ) : Prop :=
  ∀ a b : ℕ, (gateAt C k).inputs = [a, b] → ∀ y : Fin N, y ∉ qLp C N k a ∨ y ∉ qLp C N k b

theorem q_sem (C : Circuit) (hM : Monotone2 C) (N : ℕ) (U X V Y : Fin N) :
    ∀ j, j < C.gates.length → (∀ k ∈ PEqualNP.Core.coneSet N C j, qDisj C N k) →
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
    unfold qDisj at hDj
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
    · have hd := hDj a b rfl
      have hs := q_split U X V Y (qpv C N j a) (qpv C N j b) (qLp C N j a) (qLp C N j b)
        (q_pv_dep C N j a) (q_pv_dep C N j b) (q_pv_mon C hAO N j a) (q_pv_mon C hAO N j b) hd
      rcases hop with hop | hop
      · rw [hop] at hP
        have e : (fun x => GateOp.and.eval ([a, b].map fun i => qpv C N j i x)) =
            fun x => qpv C N j a x && qpv C N j b x := by
          funext x
          simp [GateOp.eval]
        rw [e] at hP
        rcases hs.1 hP with h | h
        · exact hsub a (by simp) h
        · exact hsub b (by simp) h
      · rw [hop] at hP
        have e : (fun x => GateOp.or.eval ([a, b].map fun i => qpv C N j i x)) =
            fun x => qpv C N j a x || qpv C N j b x := by
          funext x
          simp [GateOp.eval]
        rw [e] at hP
        rcases hs.2 hP with h | h
        · exact hsub a (by simp) h
        · exact hsub b (by simp) h
    · simp at hlen

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

theorem q_meet (N : ℕ) (C : Circuit) (G : Finset ℕ)
    (hND : ∀ k1 ∈ G, ∀ k2 ∈ G, ∀ w0, w0 ∈ (gateAt C k1).inputs → w0 ∈ (gateAt C k2).inputs →
      k1 = k2)
    (k ka kb : ℕ) (hk : k ∈ G) (hka : ka < k) (hkb : kb < k) (hne : ka ≠ kb)
    (hra : N + ka ∈ (gateAt C k).inputs) (hrb : N + kb ∈ (gateAt C k).inputs)
    (hsa : PEqualNP.Core.coneSet N C ka ⊆ G) (hsb : PEqualNP.Core.coneSet N C kb ⊆ G)
    (i : ℕ) (hia : i ∈ PEqualNP.Core.coneSet N C ka) (hib : i ∈ PEqualNP.Core.coneSet N C kb) :
    False := by
  have hI : (PEqualNP.Core.coneSet N C ka ∩ PEqualNP.Core.coneSet N C kb).Nonempty :=
    ⟨i, Finset.mem_inter.mpr ⟨hia, hib⟩⟩
  obtain ⟨c, hc, hmax⟩ := Finset.exists_max_image
    (PEqualNP.Core.coneSet N C ka ∩ PEqualNP.Core.coneSet N C kb) (fun t => t) hI
  have hca := (Finset.mem_inter.mp hc).1
  have hcb := (Finset.mem_inter.mp hc).2
  rcases (mem_coneSet N C c ka).mp hca with h1 | h1 <;>
    rcases (mem_coneSet N C c kb).mp hcb with h2 | h2
  · omega
  · obtain ⟨d, hd, _, hdin⟩ := q_reader N C c kb h2
    have hdk : d = k := hND d (hsb hd) k hk (N + c) hdin (by rw [h1]; exact hra)
    have := coneSet_le N C d kb hd
    omega
  · obtain ⟨d, hd, _, hdin⟩ := q_reader N C c ka h1
    have hdk : d = k := hND d (hsa hd) k hk (N + c) hdin (by rw [h2]; exact hrb)
    have := coneSet_le N C d ka hd
    omega
  · obtain ⟨d1, hd1, hcd1, hin1⟩ := q_reader N C c ka h1
    obtain ⟨d2, hd2, _, hin2⟩ := q_reader N C c kb h2
    have h12 : d1 = d2 := hND d1 (hsa hd1) d2 (hsb hd2) (N + c) hin1 hin2
    have hdI : d1 ∈ PEqualNP.Core.coneSet N C ka ∩ PEqualNP.Core.coneSet N C kb :=
      Finset.mem_inter.mpr ⟨hd1, h12 ▸ hd2⟩
    have : d1 ≤ c := hmax d1 hdI
    omega

theorem q_disj (N : ℕ) (C : Circuit) (G : Finset ℕ)
    (hG : ∀ k ∈ G, PEqualNP.Core.coneSet N C k ⊆ G)
    (hND : ∀ k1 ∈ G, ∀ k2 ∈ G, ∀ w0, w0 ∈ (gateAt C k1).inputs → w0 ∈ (gateAt C k2).inputs →
      k1 = k2)
    (k : ℕ) (hk : k ∈ G) (hkl : k < C.gates.length) (a b : ℕ) (hab : a ≠ b)
    (ha : a ∈ (gateAt C k).inputs) (hb : b ∈ (gateAt C k).inputs)
    (y : Fin N) : y ∉ qLp C N k a ∨ y ∉ qLp C N k b := by
  by_contra hcon
  simp only [not_or, not_not] at hcon
  obtain ⟨hya, hyb⟩ := hcon
  rw [q_mem_Lp] at hya hyb
  have hsub : ∀ c, c ∈ (gateAt C k).inputs → N ≤ c → c < N + k →
      PEqualNP.Core.coneSet N C (c - N) ⊆ G := by
    intro c hc h1 h2
    have hr : N + (c - N) ∈ (gateAt C k).inputs := by
      rw [show N + (c - N) = c by omega]
      exact hc
    exact fun t ht => hG k hk
      (coneSet_mono N C (c - N) k (inCone_of_read N C (c - N) k hkl (by omega) hr) ht)
  rcases hya with hya | ⟨ha1, ha2, ha3⟩ <;> rcases hyb with hyb | ⟨hb1, hb2, hb3⟩
  · exact hab (by omega)
  · rw [mem_coneLeaves] at hb3
    obtain ⟨i, hi, hiy⟩ := hb3
    have h1 := hND i (hsub b hb hb1 hb2 hi) k hk y.val hiy (by rw [hya]; exact ha)
    have h2 := coneSet_le N C i (b - N) hi
    omega
  · rw [mem_coneLeaves] at ha3
    obtain ⟨i, hi, hiy⟩ := ha3
    have h1 := hND i (hsub a ha ha1 ha2 hi) k hk y.val hiy (by rw [hyb]; exact hb)
    have h2 := coneSet_le N C i (a - N) hi
    omega
  · rw [mem_coneLeaves] at ha3 hb3
    obtain ⟨i1, hi1, hiy1⟩ := ha3
    obtain ⟨i2, hi2, hiy2⟩ := hb3
    have h12 := hND i1 (hsub a ha ha1 ha2 hi1) i2 (hsub b hb hb1 hb2 hi2) y.val hiy1 hiy2
    subst h12
    exact q_meet N C G hND k (a - N) (b - N) hk (by omega) (by omega) (by omega)
      (by rw [show N + (a - N) = a by omega]; exact ha)
      (by rw [show N + (b - N) = b by omega]; exact hb)
      (hsub a ha ha1 ha2) (hsub b hb hb1 hb2) _ hi1 hi2

def qR (C : Circuit) (k : ℕ) : Finset ℕ := (gateAt C k).inputs.toFinset

theorem q_count (N : ℕ) (C : Circuit) (G : Finset ℕ) (jo : ℕ) (hjoG : jo ∈ G)
    (hR2 : ∀ k ∈ G, (qR C k).card ≤ 2)
    (hGread : ∀ k ∈ G, k ≠ jo → ∃ i ∈ G, N + k ∈ (gateAt C i).inputs)
    (hDR : (∃ k1 ∈ G, ∃ k2 ∈ G, k1 ≠ k2 ∧
        ∃ w0, w0 ∈ (gateAt C k1).inputs ∧ w0 ∈ (gateAt C k2).inputs) ∨
      (∃ k ∈ G, (qR C k).card ≤ 1))
    (K : Finset ℕ) (hK1 : ∀ t ∈ K, t < N)
    (hK2 : ∀ t ∈ K, ∃ i ∈ G, t ∈ (gateAt C i).inputs) :
    K.card ≤ G.card := by
  have hGpos : 1 ≤ G.card := Finset.card_pos.mpr ⟨jo, hjoG⟩
  have hup : ∀ k ∈ G, (G.biUnion (qR C)).card + (qR C k ∩ (G.erase k).biUnion (qR C)).card ≤
      (qR C k).card + 2 * (G.card - 1) := by
    intro k hk
    have hsub : G.biUnion (qR C) ⊆ qR C k ∪ (G.erase k).biUnion (qR C) := by
      intro t ht
      rw [Finset.mem_biUnion] at ht
      obtain ⟨k', hk', ht'⟩ := ht
      by_cases hkk : k' = k
      · rw [hkk] at ht'
        exact Finset.mem_union_left _ ht'
      · exact Finset.mem_union_right _
          (Finset.mem_biUnion.mpr ⟨k', Finset.mem_erase.mpr ⟨hkk, hk'⟩, ht'⟩)
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_add_card_inter (qR C k) ((G.erase k).biUnion (qR C))
    have h3 : ((G.erase k).biUnion (qR C)).card ≤ 2 * (G.card - 1) := by
      refine le_trans Finset.card_biUnion_le ?_
      rw [← Finset.card_erase_of_mem hk]
      calc ∑ a ∈ G.erase k, (qR C a).card ≤ ∑ a ∈ G.erase k, 2 :=
            Finset.sum_le_sum (fun a ha => hR2 a (Finset.mem_of_mem_erase ha))
        _ = 2 * (G.erase k).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    omega
  have hupper : (G.biUnion (qR C)).card + 1 ≤ 2 * G.card := by
    rcases hDR with ⟨k1, hk1, k2, hk2, hne, w0, hw1, hw2⟩ | ⟨k, hk, hc⟩
    · have h := hup k1 hk1
      have hpos : 1 ≤ (qR C k1 ∩ (G.erase k1).biUnion (qR C)).card := by
        apply Finset.card_pos.mpr
        refine ⟨w0, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
        · unfold qR
          exact List.mem_toFinset.mpr hw1
        · apply Finset.mem_biUnion.mpr
          refine ⟨k2, Finset.mem_erase.mpr ⟨fun e => hne e.symm, hk2⟩, ?_⟩
          unfold qR
          exact List.mem_toFinset.mpr hw2
      have := hR2 k1 hk1
      omega
    · have h := hup k hk
      omega
  have hlow : K.card + (G.card - 1) ≤ (G.biUnion (qR C)).card := by
    have hsub : K ∪ (G.erase jo).image (fun k => N + k) ⊆ G.biUnion (qR C) := by
      intro t ht
      rw [Finset.mem_union] at ht
      rw [Finset.mem_biUnion]
      rcases ht with ht | ht
      · obtain ⟨i, hi, hti⟩ := hK2 t ht
        refine ⟨i, hi, ?_⟩
        unfold qR
        exact List.mem_toFinset.mpr hti
      · rw [Finset.mem_image] at ht
        obtain ⟨k, hk, rfl⟩ := ht
        rw [Finset.mem_erase] at hk
        obtain ⟨i, hi, hin⟩ := hGread k hk.2 hk.1
        refine ⟨i, hi, ?_⟩
        unfold qR
        exact List.mem_toFinset.mpr hin
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
  omega

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

theorem main_aux : ∀ (n m s : ℕ) (A : Fin n → Fin m → Bool) (u x : Fin n) (v w : Fin m), A u v = true → A u w = true → A x v = true → A x w = false → (∃ w' : Fin m, A u w' = false) → (∃ u' : Fin n, A u' v = false) → PEqualNP.Represents.RepSizeAtMost A s → (Finset.univ.filter (fun a : Fin n => ∃ b : Fin m, A a b = true ∧ ∃ a' : Fin n, A a' b = false)).card + (Finset.univ.filter (fun b : Fin m => ∃ a : Fin n, A a b = true ∧ ∃ b' : Fin m, A a b' = false)).card ≤ s := by
  intro n m s A u x v w huv huw hxv hxw hw' hu' hrep
  obtain ⟨w', huw'⟩ := hw'
  obtain ⟨u', hu'v⟩ := hu'
  obtain ⟨C, hM, hs, hR⟩ := hrep
  have hAO := andOrOnly_of_monotone2 hM
  have hRv : ∀ a b, val C (List.ofFn (qind ({Fin.castAdd m a, Fin.natAdd n b} :
      Finset (Fin (n + m))))) C.output = A a b := by
    intro a b
    rw [← q_oe]
    exact hR a b
  have hmono := q_val_mon (n + m) C hAO C.output
  have hP : qP4 (Fin.castAdd m u) (Fin.castAdd m x) (Fin.natAdd n v) (Fin.natAdd n w)
      (fun z => val C (List.ofFn z) C.output) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (hRv u v).trans huv
    · exact (hRv u w).trans huw
    · exact (hRv x v).trans hxv
    · exact (hRv x w).trans hxw
    · exact q_nf (q_mon1 hmono (Fin.castAdd m u) (Fin.natAdd n w')) ((hRv u w').trans huw')
    · exact q_nf (q_mon2 hmono (Fin.castAdd m u') (Fin.natAdd n v)) ((hRv u' v).trans hu'v)
  by_cases hlo : C.output < n + m
  · exact absurd hP (q_input_not C (n + m) C.output hlo _ _ _ _)
  by_cases hhi : n + m + C.gates.length ≤ C.output
  · have e : (fun z : Fin (n + m) → Bool => val C (List.ofFn z) C.output) = fun _ => false := by
      funext z
      exact val_ge (n := n + m) (by simp) hhi
    rw [e] at hP
    exact absurd hP (q_false_not _ _ _ _)
  obtain ⟨jo, hjo⟩ : ∃ jo, C.output = n + m + jo := ⟨C.output - (n + m), by omega⟩
  have hjol : jo < C.gates.length := by omega
  rw [hjo] at hP hRv
  have hGsub : ∀ k ∈ PEqualNP.Core.coneSet (n + m) C jo,
      PEqualNP.Core.coneSet (n + m) C k ⊆ PEqualNP.Core.coneSet (n + m) C jo :=
    fun k hk => q_cs_sub (n + m) C k jo hk
  have hGlen : ∀ k ∈ PEqualNP.Core.coneSet (n + m) C jo, k < C.gates.length := by
    intro k hk
    have := coneSet_le (n + m) C k jo hk
    omega
  by_cases hDR : (∃ k1 ∈ PEqualNP.Core.coneSet (n + m) C jo,
      ∃ k2 ∈ PEqualNP.Core.coneSet (n + m) C jo, k1 ≠ k2 ∧
        ∃ w0, w0 ∈ (gateAt C k1).inputs ∧ w0 ∈ (gateAt C k2).inputs) ∨
      (∃ k ∈ PEqualNP.Core.coneSet (n + m) C jo, (qR C k).card ≤ 1)
  · set Rf := Finset.univ.filter
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
    have hc := q_count (n + m) C (PEqualNP.Core.coneSet (n + m) C jo) jo
      (self_mem_coneSet (n + m) C jo) hR2 hGread hDR _ hK1 hK2
    rw [hcard] at hc
    have h1 : (PEqualNP.Core.coneSet (n + m) C jo).card ≤ C.gates.length := by
      have := Finset.card_le_card (coneSet_sub_range (n + m) C jo hjol)
      rwa [Finset.card_range] at this
    have h2 : C.size = C.gates.length := rfl
    omega
  · exfalso
    apply q_sem C hM (n + m) _ _ _ _ jo hjol _ hP
    intro k hk
    unfold qDisj
    intro a b hab y
    have ha : a ∈ (gateAt C k).inputs := by
      rw [hab]
      simp
    have hb : b ∈ (gateAt C k).inputs := by
      rw [hab]
      simp
    have hne : a ≠ b := by
      intro e
      apply hDR
      right
      refine ⟨k, hk, ?_⟩
      unfold qR
      rw [hab, e]
      simp
    exact q_disj (n + m) C (PEqualNP.Core.coneSet (n + m) C jo) hGsub
      (fun k1 hk1 k2 hk2 w0 h1 h2 => by
        by_contra hne2
        exact hDR (Or.inl ⟨k1, hk1, k2, hk2, hne2, w0, h1, h2⟩))
      k hk (hGlen k hk) a b hne ha hb y

end PEqualNP.Outside.L_meta_7638

theorem PEqualNP.Outside.L_meta_7638 : ∀ (n m s : ℕ) (A : Fin n → Fin m → Bool) (u x : Fin n) (v w : Fin m), A u v = true → A u w = true → A x v = true → A x w = false → (∃ w' : Fin m, A u w' = false) → (∃ u' : Fin n, A u' v = false) → PEqualNP.Represents.RepSizeAtMost A s → (Finset.univ.filter (fun a : Fin n => ∃ b : Fin m, A a b = true ∧ ∃ a' : Fin n, A a' b = false)).card + (Finset.univ.filter (fun b : Fin m => ∃ a : Fin n, A a b = true ∧ ∃ b' : Fin m, A a b' = false)).card ≤ s :=
  PEqualNP.Outside.L_meta_7638.main_aux
