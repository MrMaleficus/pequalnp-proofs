import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4632

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

-- FRAGMENT flow    DEPENDS: fold mono
-- Transport of wire values between two runs whose gate lists are related by a renaming of read indices
-- (rename inputs, delete or insert a gate, redirect reads of a wire to an equivalent wire).
-- Exports:
--   def rgate f g := gate g with every read index i replaced by f i (same op) ;  rgate_op, rgate_len (inputs length kept)
--   rgate_id : gs.map (rgate id) = gs ;  rgate_eval : value of rgate f g on w = g.op.eval (g.inputs.map fun i => w.getD (f i) false)
--   def gateRel R g : for all a b, (R (a i) (b i) for i in g.inputs) -> R (g on a) (g on b)
--   gateRel_eq g : gateRel Eq g (any op) ;  gateRel_of_opMono (OpMono R) (g.op = and or or) : gateRel R g
--   flow_step_ne (i ne w.length) : (step w g).getD i false = w.getD i false
--   flow_span R p q gs w v (all g in gs, gateRel R g) (for k < gs.length: p i = w.length + k iff q i = v.length + k)
--       (for all i, R (w at p i) (v at q i)) : for all i, R ((W (gs.map (rgate p)) w) at p i) ((W (gs.map (rgate q)) v) at q i)
--   flow_map R f gs w v (gateRel) (i = w.length + k iff f i = v.length + k) (R (w at i) (v at f i)) :
--       for all i, R ((W gs w) at i) ((W (gs.map (rgate f)) v) at f i)       (flow_span with p = id)
--   flow_map_eq : flow_map with R = Eq, any ops ;  flow_map_mono : R = (a = true -> b = true), all gates and/or
--   flow_rename f n (f i = i for n <= i) (f i < n for i < n) (x.length = y.length, n <= x.length)
--       (x at i = y at f i for i < x.length) : for all i, (W gs x) at i = (W (gs.map (rgate f)) y) at f i
--   flow_rename_eval : same hypotheses, Circuit.eval (gates C.gates.map (rgate f), output f C.output) y = C.eval x
--   def flow_del L t i := if i < L then i else if i = L then t else i - 1      (delete wire L, its readers read t)
--   flow_drop g rest w t (t < w.length or w.length + rest.length <= t) (value of g on w = w at t) :
--       for all o, (W (g :: rest) w) at o = (W (rest.map (rgate (flow_del w.length t))) w) at (flow_del w.length t o)
--   flow_drop_mid pre post g w t (t < w.length + pre.length or w.length + pre.length + post.length <= t)
--       (value of g on W pre w = (W pre w) at t) : for all o, (W (pre ++ g :: post) w) at o
--       = (W (pre ++ post.map (rgate (flow_del (w.length + pre.length) t))) w) at (flow_del (w.length + pre.length) t o)
--   flow_drop_eval (C.gates = pre ++ g :: post) (x.length = n) ... : C.eval x = eval of
--       (gates pre ++ post.map (rgate (flow_del (n + pre.length) t)), output flow_del (n + pre.length) t C.output) at x
--   flow_drop_len : (pre ++ post.map h).length + 1 = (pre ++ g :: post).length
--   flow_bool, flow_gate t op (and or or) : (inputs p i = t -> q i = t) -> op on p = t -> op on q = t
--   flow_redirect t f gs w v (w.length = v.length) (and/or gates) (reads i of gate k with f i ne i : i, f i < w.length + k)
--       (f i ne i -> run at i = t -> run at f i = t) (w at i = t -> v at i = t) :
--       for all i, (W gs w) at i = t -> (W (gs.map (rgate f)) v) at i = t
--   flow_redirect_fun n C w w2 (Monotone2 C) (ReadsBack n C) (gates reading w are after w2) (w true -> w2 true)
--       (w2 true -> w true or C true) : circuitFun n (gates map (rgate (if ii = w then w2 else ii)), output redirected)
--       = circuitFun n C
-- Use: to compare a circuit with a renamed / shortened one, write both runs as W of mapped gate lists and apply
-- flow_map (Eq for equal values, mono for monotone implications both ways with different inputs) or flow_drop.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def rgate (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

theorem rgate_op (f : ℕ → ℕ) (g : Gate) : (rgate f g).op = g.op := rfl

theorem rgate_len (f : ℕ → ℕ) (g : Gate) : (rgate f g).inputs.length = g.inputs.length := by
  simp [rgate]

theorem rgate_id (gs : List Gate) : gs.map (rgate id) = gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, ih]
    cases g
    simp [rgate]

theorem rgate_eval (f : ℕ → ℕ) (g : Gate) (w : List Bool) :
    (rgate f g).op.eval ((rgate f g).inputs.map fun i => w.getD i false)
      = g.op.eval (g.inputs.map fun i => w.getD (f i) false) := by
  show g.op.eval ((g.inputs.map f).map fun i => w.getD i false) = _
  rw [List.map_map]
  rfl

def gateRel (R : Bool → Bool → Prop) (g : Gate) : Prop :=
  ∀ a b : ℕ → Bool, (∀ i ∈ g.inputs, R (a i) (b i)) →
    R (g.op.eval (g.inputs.map a)) (g.op.eval (g.inputs.map b))

theorem gateRel_eq (g : Gate) : gateRel Eq g := by
  intro a b h
  rw [List.map_congr_left h]

theorem gateRel_of_opMono {R : Bool → Bool → Prop} (hR : OpMono R) {g : Gate}
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) : gateRel R g :=
  fun a b h => hR g.op hop g.inputs a b h

theorem flow_step_ne (w : List Bool) (g : Gate) (i : ℕ) (h : i ≠ w.length) :
    (step w g).getD i false = w.getD i false := by
  by_cases hi : i < w.length
  · exact step_lt w g i hi
  · rw [getD_ge _ _ (by rw [step_len]; omega), getD_ge _ _ (by omega)]

theorem flow_span (R : Bool → Bool → Prop) (p q : ℕ → ℕ) (gs : List Gate) :
    ∀ (w v : List Bool),
    (∀ g ∈ gs, gateRel R g) →
    (∀ i k, k < gs.length → (p i = w.length + k ↔ q i = v.length + k)) →
    (∀ i, R (w.getD (p i) false) (v.getD (q i) false)) →
    ∀ i, R ((W (gs.map (rgate p)) w).getD (p i) false)
      ((W (gs.map (rgate q)) v).getD (q i) false) := by
  induction gs with
  | nil =>
    intro w v _ _ hf i
    exact hf i
  | cons g gs ih =>
    intro w v hops hs hf
    rw [List.map_cons, List.map_cons, W_cons, W_cons]
    refine ih (step w (rgate p g)) (step v (rgate q g))
      (fun a ha => hops a (List.mem_cons_of_mem _ ha)) ?_ ?_
    · intro i k hk
      have h0 := hs i (k + 1) (by rw [List.length_cons]; omega)
      rw [step_len, step_len]
      have e1 : w.length + 1 + k = w.length + (k + 1) := by omega
      have e2 : v.length + 1 + k = v.length + (k + 1) := by omega
      rw [e1, e2]
      exact h0
    · intro j
      have h0 := hs j 0 (by rw [List.length_cons]; omega)
      simp only [Nat.add_zero] at h0
      by_cases hp : p j = w.length
      · have hq := h0.mp hp
        rw [step_last _ _ _ hp, step_last _ _ _ hq, rgate_eval, rgate_eval]
        exact hops g List.mem_cons_self (fun i => w.getD (p i) false)
          (fun i => v.getD (q i) false) (fun i _ => hf i)
      · have hq : q j ≠ v.length := fun h => hp (h0.mpr h)
        rw [flow_step_ne _ _ _ hp, flow_step_ne _ _ _ hq]
        exact hf j

theorem flow_map (R : Bool → Bool → Prop) (f : ℕ → ℕ) (gs : List Gate) (w v : List Bool)
    (hops : ∀ g ∈ gs, gateRel R g)
    (hs : ∀ i k, k < gs.length → (i = w.length + k ↔ f i = v.length + k))
    (hf : ∀ i, R (w.getD i false) (v.getD (f i) false)) :
    ∀ i, R ((W gs w).getD i false) ((W (gs.map (rgate f)) v).getD (f i) false) := by
  have h := flow_span R id f gs w v hops hs hf
  rw [rgate_id] at h
  exact h

theorem flow_map_eq (f : ℕ → ℕ) (gs : List Gate) (w v : List Bool)
    (hs : ∀ i k, k < gs.length → (i = w.length + k ↔ f i = v.length + k))
    (hf : ∀ i, w.getD i false = v.getD (f i) false) :
    ∀ i, (W gs w).getD i false = (W (gs.map (rgate f)) v).getD (f i) false :=
  flow_map Eq f gs w v (fun g _ => gateRel_eq g) hs hf

theorem flow_map_mono (f : ℕ → ℕ) (gs : List Gate) (w v : List Bool)
    (hops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hs : ∀ i k, k < gs.length → (i = w.length + k ↔ f i = v.length + k))
    (hf : ∀ i, w.getD i false = true → v.getD (f i) false = true) :
    ∀ i, (W gs w).getD i false = true → (W (gs.map (rgate f)) v).getD (f i) false = true :=
  flow_map (fun a b => a = true → b = true) f gs w v
    (fun g hg => gateRel_of_opMono opMono_imp (hops g hg)) hs hf

theorem flow_rename (f : ℕ → ℕ) (n : ℕ) (hf1 : ∀ i, n ≤ i → f i = i) (hf2 : ∀ i, i < n → f i < n)
    (gs : List Gate) (x y : List Bool) (hl : x.length = y.length) (hn : n ≤ x.length)
    (hxy : ∀ i, i < x.length → x.getD i false = y.getD (f i) false) :
    ∀ i, (W gs x).getD i false = (W (gs.map (rgate f)) y).getD (f i) false := by
  refine flow_map_eq f gs x y ?_ ?_
  · intro i k _
    by_cases hi : i < n
    · have := hf2 i hi
      constructor <;> intro h <;> omega
    · rw [hf1 i (by omega), ← hl]
  · intro i
    by_cases hi : i < x.length
    · exact hxy i hi
    · rw [hf1 i (by omega), getD_ge x i (by omega), getD_ge y i (by omega)]

theorem flow_rename_eval (C : Circuit) (f : ℕ → ℕ) (n : ℕ) (hf1 : ∀ i, n ≤ i → f i = i)
    (hf2 : ∀ i, i < n → f i < n) (x y : List Bool) (hl : x.length = y.length) (hn : n ≤ x.length)
    (hxy : ∀ i, i < x.length → x.getD i false = y.getD (f i) false) :
    Circuit.eval ⟨C.gates.map (rgate f), f C.output⟩ y = C.eval x :=
  (flow_rename f n hf1 hf2 C.gates x y hl hn hxy C.output).symm

def flow_del (L t i : ℕ) : ℕ := if i < L then i else if i = L then t else i - 1

theorem flow_drop (g : Gate) (rest : List Gate) (w : List Bool) (t : ℕ)
    (ht : t < w.length ∨ w.length + rest.length ≤ t)
    (hval : g.op.eval (g.inputs.map fun i => w.getD i false) = w.getD t false) :
    ∀ o, (W (g :: rest) w).getD o false
      = (W (rest.map (rgate (flow_del w.length t))) w).getD (flow_del w.length t o) false := by
  rw [W_cons]
  refine flow_map_eq (flow_del w.length t) rest (step w g) w ?_ ?_
  · intro i k hk
    rw [step_len]
    unfold flow_del
    split_ifs <;> constructor <;> intro h <;> omega
  · intro i
    unfold flow_del
    split_ifs with h1 h2
    · exact step_lt w g i h1
    · rw [step_last w g i h2]
      exact hval
    · rw [getD_ge _ i (by rw [step_len]; omega), getD_ge w (i - 1) (by omega)]

theorem flow_drop_mid (pre post : List Gate) (g : Gate) (w : List Bool) (t : ℕ)
    (ht : t < w.length + pre.length ∨ w.length + pre.length + post.length ≤ t)
    (hval : g.op.eval (g.inputs.map fun i => (W pre w).getD i false) = (W pre w).getD t false) :
    ∀ o, (W (pre ++ g :: post) w).getD o false
      = (W (pre ++ post.map (rgate (flow_del (w.length + pre.length) t))) w).getD
          (flow_del (w.length + pre.length) t o) false := by
  intro o
  rw [W_append, W_append]
  have hl := W_length pre w
  rw [← hl]
  exact flow_drop g post (W pre w) t (by rw [hl]; exact ht) hval o

theorem flow_drop_eval (C : Circuit) (pre post : List Gate) (g : Gate) (hC : C.gates = pre ++ g :: post)
    (n : ℕ) (x : List Bool) (hx : x.length = n) (t : ℕ)
    (ht : t < n + pre.length ∨ n + pre.length + post.length ≤ t)
    (hval : g.op.eval (g.inputs.map fun i => (W pre x).getD i false) = (W pre x).getD t false) :
    C.eval x = Circuit.eval ⟨pre ++ post.map (rgate (flow_del (n + pre.length) t)),
      flow_del (n + pre.length) t C.output⟩ x := by
  subst hx
  show (W C.gates x).getD C.output false = _
  rw [hC]
  exact flow_drop_mid pre post g x t ht hval C.output

theorem flow_drop_len (pre post : List Gate) (g : Gate) (h : Gate → Gate) :
    (pre ++ post.map h).length + 1 = (pre ++ g :: post).length := by
  simp
  omega

theorem flow_bool (t b b' c c' : Bool)
    (hb : b = t → b' = t) (hc : c = t → c' = t) :
    ((b && c) = t → (b' && c') = t) ∧ ((b || c) = t → (b' || c') = t) := by
  cases t <;> cases b <;> cases b' <;> cases c <;> cases c' <;> simp_all

theorem flow_gate (t : Bool) (op : GateOp) (hop : op = .and ∨ op = .or)
    (ins : List ℕ) (p q : ℕ → Bool)
    (h : ∀ i ∈ ins, p i = t → q i = t) :
    op.eval (ins.map p) = t → op.eval (ins.map q) = t := by
  induction ins with
  | nil => exact id
  | cons i ins ih =>
    have ih' := ih (fun j hj => h j (List.mem_cons_of_mem _ hj))
    have hi := h i List.mem_cons_self
    rcases hop with rfl | rfl
    · simp only [GateOp.eval, List.map_cons, List.all_cons, id_eq] at ih' ⊢
      exact (flow_bool t _ _ _ _ hi ih').1
    · simp only [GateOp.eval, List.map_cons, List.any_cons, id_eq] at ih' ⊢
      exact (flow_bool t _ _ _ _ hi ih').2

theorem flow_redirect (t : Bool) (f : ℕ → ℕ) (gs : List Gate) : ∀ (w v : List Bool),
    w.length = v.length →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    (∀ k < gs.length, ∀ i ∈ (gs.getD k ⟨GateOp.or, []⟩).inputs, f i ≠ i →
      i < w.length + k ∧ f i < w.length + k) →
    (∀ i, f i ≠ i → (W gs w).getD i false = t → (W gs w).getD (f i) false = t) →
    (∀ i, w.getD i false = t → v.getD i false = t) →
    ∀ i, (W gs w).getD i false = t → (W (gs.map (rgate f)) v).getD i false = t := by
  induction gs with
  | nil =>
    intro w v _ _ _ _ hf i h
    exact hf i h
  | cons g gs ih =>
    intro w v hl hops hr hab hf
    rw [List.map_cons, W_cons, W_cons]
    rw [W_cons] at hab
    have hside : ∀ i ∈ g.inputs, w.getD i false = t → v.getD (f i) false = t := by
      intro i hi h1
      by_cases hfi : f i = i
      · rw [hfi]
        exact hf i h1
      · obtain ⟨hk1, hk2⟩ := hr 0 (by rw [List.length_cons]; omega) i
          (by simpa [List.getD_cons_zero] using hi) hfi
        have h2 : (W gs (step w g)).getD i false = t := by
          rw [W_prefix gs _ i (by rw [step_len]; omega), step_lt w g i (by omega)]
          exact h1
        have h3 := hab i hfi h2
        rw [W_prefix gs _ (f i) (by rw [step_len]; omega), step_lt w g (f i) (by omega)] at h3
        exact hf _ h3
    have hstep : g.op.eval (g.inputs.map fun i => w.getD i false) = t →
        (rgate f g).op.eval ((rgate f g).inputs.map fun i => v.getD i false) = t := by
      rw [rgate_eval]
      exact flow_gate t g.op (hops g List.mem_cons_self) g.inputs
        (fun i => w.getD i false) (fun i => v.getD (f i) false) hside
    refine ih (step w g) (step v (rgate f g)) (by rw [step_len, step_len, hl])
      (fun a ha => hops a (List.mem_cons_of_mem _ ha)) ?_ hab ?_
    · intro k hk i hm hfi
      obtain ⟨h1, h2⟩ := hr (k + 1) (by rw [List.length_cons]; omega) i
        (by simpa [List.getD_cons_succ] using hm) hfi
      rw [step_len]
      exact ⟨by omega, by omega⟩
    · intro i hi
      by_cases h1 : i < w.length
      · rw [step_lt w g i h1] at hi
        rw [step_lt v _ i (by omega)]
        exact hf i hi
      · by_cases h2 : i = w.length
        · rw [step_last w g i h2] at hi
          rw [step_last v _ i (by omega)]
          exact hstep hi
        · rw [getD_ge _ _ (by rw [step_len]; omega)] at hi
          rw [getD_ge _ _ (by rw [step_len]; omega)]
          exact hi

theorem flow_redirect_fun (n : ℕ) (C : Circuit) (w w' : ℕ) (hm : Monotone2 C) (hrb : ReadsBack n C)
    (hread : ∀ k < C.gates.length, w ∈ (gateAt C k).inputs → w' < n + k)
    (h4 : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD w false = true →
      (C.wires (List.ofFn x)).getD w' false = true)
    (h5 : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD w' false = true →
      (C.wires (List.ofFn x)).getD w false = true ∨ circuitFun n C x = true) :
    circuitFun n ⟨C.gates.map (rgate fun ii => if ii = w then w' else ii),
      if C.output = w then w' else C.output⟩ = circuitFun n C := by
  have hops : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    simpa using (hm g hg).1
  funext x
  have hy : (List.ofFn x).length = n := List.length_ofFn
  have hr : ∀ k < C.gates.length, ∀ i ∈ (C.gates.getD k ⟨GateOp.or, []⟩).inputs,
      (fun ii => if ii = w then w' else ii) i ≠ i →
      i < (List.ofFn x).length + k ∧ (fun ii => if ii = w then w' else ii) i < (List.ofFn x).length + k := by
    intro k hk i hi hfi
    have hiw : i = w := by
      by_contra hc
      exact hfi (if_neg hc)
    rw [hiw] at hi
    show i < (List.ofFn x).length + k ∧ (if i = w then w' else i) < (List.ofFn x).length + k
    rw [if_pos hiw, hy, hiw]
    exact ⟨hrb k hk w hi, hread k hk hi⟩
  have key : ∀ t : Bool, ((W C.gates (List.ofFn x)).getD w false = t →
      (W C.gates (List.ofFn x)).getD w' false = t) →
      ∀ i, (W C.gates (List.ofFn x)).getD i false = t →
      (W (C.gates.map (rgate fun ii => if ii = w then w' else ii)) (List.ofFn x)).getD i false = t := by
    intro t ht
    refine flow_redirect t (fun ii => if ii = w then w' else ii) C.gates (List.ofFn x) (List.ofFn x)
      rfl hops hr ?_ (fun i h => h)
    intro i hfi
    have hiw : i = w := by
      by_contra hc
      exact hfi (if_neg hc)
    show _ → (W C.gates (List.ofFn x)).getD (if i = w then w' else i) false = t
    rw [if_pos hiw, hiw]
    exact ht
  have h4x : (W C.gates (List.ofFn x)).getD w false = true →
      (W C.gates (List.ofFn x)).getD w' false = true := h4 x
  have h5x : (W C.gates (List.ofFn x)).getD w' false = true →
      (W C.gates (List.ofFn x)).getD w false = true ∨
        (W C.gates (List.ofFn x)).getD C.output false = true := h5 x
  show (W (C.gates.map (rgate fun ii => if ii = w then w' else ii)) (List.ofFn x)).getD
      (if C.output = w then w' else C.output) false
    = (W C.gates (List.ofFn x)).getD C.output false
  generalize W C.gates (List.ofFn x) = WW at key h4x h5x ⊢
  generalize W (C.gates.map (rgate fun ii => if ii = w then w' else ii)) (List.ofFn x) = VV
    at key ⊢
  have hup := key true h4x
  by_cases heq : WW.getD w false = WW.getD w' false
  · have hdn := key false (fun h => by rw [← heq]; exact h)
    have hall : ∀ i, VV.getD i false = WW.getD i false := by
      intro i
      cases hW : WW.getD i false
      · exact hdn i hW
      · exact hup i hW
    by_cases ho : C.output = w
    · rw [if_pos ho, hall, ho, heq]
    · rw [if_neg ho, hall]
  · have hw : WW.getD w false = false := by
      cases h1 : WW.getD w false
      · rfl
      · exact absurd (h1.trans (h4x h1).symm) heq
    have hw' : WW.getD w' false = true := by
      cases h2 : WW.getD w' false
      · exact absurd (hw.trans h2.symm) heq
      · rfl
    have ho1 : WW.getD C.output false = true := by
      rcases h5x hw' with h | h
      · rw [hw] at h
        exact absurd h Bool.false_ne_true
      · exact h
    rw [ho1]
    by_cases ho : C.output = w
    · rw [if_pos ho]
      exact hup w' hw'
    · rw [if_neg ho]
      exact hup _ ho1

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

-- FRAGMENT monocmp    DEPENDS: fold mono flow
-- One-directional (or equality) comparison of two runs, old circuit C on input x and new circuit D on input y,
-- through a wire map f (old wire u corresponds to new wire f u), on a domain dom of old wires. Generalises
-- flow_map_mono / agreeP_full: the gate lists need not be in lockstep, some new gates may be free, and some old
-- wires may be handled by hand (special wires: removed gates re-served elsewhere, rewritten gates).
-- R is a relation on Bool with OpMono R: Eq (opMono_eq), old -> new (opMono_imp), new -> old (opMono_rimp).
-- Exports:
--   opMono_rimp : OpMono (fun a b => b = true -> a = true)
--   mc_ind a b dom f (h : for u in dom, (for v < u in dom, R (a v) (b (f v))) -> R (a u) (b (f u))) :
--       for u in dom, R (a u) (b (f u))       (strong induction on old wires)
--   mc_copy (OpMono R) (x.length = n) (y.length = n) f (j < C.len) (p < D.len) (op of old gate j and/or)
--       (gateAt D p = rgate f (gateAt C j)) (each input i of old gate j: i < n + j and f i < n + p)
--       (each input i: R (val C x i) (val D y (f i))) : R (val C x (n + j)) (val D y (n + p))
--   mc_run (OpMono R) (x.length = n) (y.length = n) dom f
--       (h : for u in dom, IH below u -> R (val C x u) (val D y (f u)) OR u is a copied gate: exists j p,
--        u = n + j, f u = n + p, j < C.len, p < D.len, op and/or, gateAt D p = rgate f (gateAt C j),
--        each input i of gate j: i < n + j, f i < n + p, dom i) :
--       for u in dom, R (val C x u) (val D y (f u))
--   mc_input (x.length = n) (y.length = n) (u < n) : val C x u = x.getD u false and val D y u = y.getD u false
--   rgate_id1 g : rgate id g = g ;  rgate_inputs f g : (rgate f g).inputs = g.inputs.map f
-- Use: pick dom and f, prove each wire of dom is an input (left case with mc_input), a copied gate (right case),
-- or special (left case, using the IH for its operands), then mc_run. For new <= old use opMono_rimp.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem opMono_rimp : OpMono (fun a b => b = true → a = true) := by
  intro op hop l f g h
  exact opMono_imp op hop l g f (fun i hi => h i hi)

theorem rgate_id1 (g : Gate) : rgate id g = g := by
  cases g with
  | mk op inputs => simp [rgate]

theorem rgate_inputs (f : ℕ → ℕ) (g : Gate) : (rgate f g).inputs = g.inputs.map f := rfl

theorem mc_ind {R : Bool → Bool → Prop} (a b : ℕ → Bool) (dom : ℕ → Prop) (f : ℕ → ℕ)
    (h : ∀ u, dom u → (∀ v, v < u → dom v → R (a v) (b (f v))) → R (a u) (b (f u))) :
    ∀ u, dom u → R (a u) (b (f u)) := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu
    exact h u hu (fun v hv hd => ih v hv hd)

theorem mc_input {C D : Circuit} {n : ℕ} {x y : List Bool} (hx : x.length = n) (hy : y.length = n)
    {u : ℕ} (hu : u < n) : val C x u = x.getD u false ∧ val D y u = y.getD u false :=
  ⟨val_input hx hu, val_input hy hu⟩

theorem mc_copy {R : Bool → Bool → Prop} (hR : OpMono R) {C D : Circuit} {n : ℕ} {x y : List Bool}
    (hx : x.length = n) (hy : y.length = n) (f : ℕ → ℕ) {j p : ℕ}
    (hj : j < C.gates.length) (hp : p < D.gates.length)
    (hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or)
    (hg : gateAt D p = rgate f (gateAt C j))
    (hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j ∧ f i < n + p)
    (hin : ∀ i ∈ (gateAt C j).inputs, R (val C x i) (val D y (f i))) :
    R (val C x (n + j)) (val D y (n + p)) := by
  have hrbD : ∀ i ∈ (gateAt D p).inputs, i < n + p := by
    intro i hi
    rw [hg, rgate_inputs] at hi
    obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hi
    exact (hrb i0 hi0).2
  rw [val_gate_rb hx hj (fun i hi => (hrb i hi).1), val_gate_rb hy hp hrbD, hg]
  show R _ ((gateAt C j).op.eval (((gateAt C j).inputs.map f).map fun i => val D y i))
  rw [List.map_map]
  exact hR _ hop _ (val C x) (fun i => val D y (f i)) hin

theorem mc_run {R : Bool → Bool → Prop} (hR : OpMono R) {C D : Circuit} {n : ℕ} {x y : List Bool}
    (hx : x.length = n) (hy : y.length = n) (dom : ℕ → Prop) (f : ℕ → ℕ)
    (h : ∀ u, dom u → (∀ v, v < u → dom v → R (val C x v) (val D y (f v))) →
      R (val C x u) (val D y (f u)) ∨
      ∃ j p, u = n + j ∧ f u = n + p ∧ j < C.gates.length ∧ p < D.gates.length ∧
        ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
        gateAt D p = rgate f (gateAt C j) ∧
        ∀ i ∈ (gateAt C j).inputs, i < n + j ∧ f i < n + p ∧ dom i) :
    ∀ u, dom u → R (val C x u) (val D y (f u)) := by
  refine mc_ind (R := R) (val C x) (val D y) dom f ?_
  intro u hu ih
  rcases h u hu ih with h1 | ⟨j, p, hu1, hf, hj, hp, hop, hg, hin⟩
  · exact h1
  · rw [hf, hu1]
    exact mc_copy hR hx hy f hj hp hop hg (fun i hi => ⟨(hin i hi).1, (hin i hi).2.1⟩)
      (fun i hi => ih i (by have := (hin i hi).1; omega) (hin i hi).2.2)

-- FRAGMENT reorder    DEPENDS: fold mono flow restrict monocmp
-- Rebuilding a circuit as A ++ mid ++ B: the old gates of the set A (in old order), then a free middle block mid,
-- then the old gates of the set B (in old order), every read i remapped by the wire map
-- roMap n C A B mid red i = i (input) / n + roP A (i - n) (A gate) / n + roOff C A mid + roP B (i - n) (B gate) /
-- red i (any other wire: removed gates re-served by a wire of the head part or of mid). Old gates outside A and B
-- are dropped. Abbreviations: len = C.gates.length, D = roC n C A B mid red o, f = roMap n C A B mid red,
-- Hs = the shape hypotheses (hAl : A below len) (hBl : B below len) (hAB : A, B disjoint)
--      (hAcl : every input of an A gate is an input wire or an A gate)
--      (hBrd : every input i of a B gate that is a gate wire outside A and B has red i < n + roOff C A mid).
-- Exports:
--   def roL P m := (List.range m).filter (in P) ;  def roP P j := (roL P j).length (new rank of old gate j inside P)
--   roL_succ_in / roL_succ_out ;  roP_mono (a <= b) ;  roP_lt (j < m) (j in P) : roP P j < roP P m
--   roP_card (P below m) : roP P m = P.card ;  roL_getD (j in P) (j < m) : (roL P m).getD (roP P j) 0 = j
--   def roG C P f m := (roL P m).map (fun j => rgate f (gateAt C j)) ;  roG_len : length = roP P m
--   roG_getD (j in P) (j < m) : (roG C P f m).getD (roP P j) (OR of nothing) = rgate f (gateAt C j)
--   roG_mem : g in roG C P f m -> exists j in P, j < m and g = rgate f (gateAt C j)
--   roG_rb (for j in P, every input i of j has f i < base + roP P j) : RBo base (roG C P f m)
--   def roOff C A mid := roP A len + mid.length ;  def roF / roMap (the map above) ;  def roGates ;  def roC (output o)
--   roF_in (i < n) : f i = i ;  roF_A (not i < n) (i - n in A) : f i = n + roP A (i - n)
--   roF_B (not i < n) (i - n not in A) (i - n in B) : f i = n + roOff C A mid + roP B (i - n) ;  roF_red (others) : f i = red i
--   ro_len : D.gates.length = roP A len + mid.length + roP B len ;  ro_size (Hs) : D.size = A.card + mid.length + B.card
--   ro_gateA (j in A) (j < len) : gateAt D (roP A j) = rgate f (gateAt C j)
--   ro_gateB (j in B) (j < len) : gateAt D (roOff C A mid + roP B j) = rgate f (gateAt C j)
--   ro_fA (ReadsBack n C) Hs (j in A) (i input of j) : f i < n + roP A j
--   ro_fB (ReadsBack n C) Hs (j in B) (i input of j) : f i < n + roOff C A mid + roP B j
--   ro_rb (ReadsBack n C) Hs (RBo (n + roP A len) mid) : ReadsBack n D
--   ro_isAO2 (IsAO2 n C) Hs (RBo (n + roP A len) mid) (mid gates and/or with 2 inputs) : IsAO2 n D
--   ro_val (OpMono R) (AndOrOnly C) (ReadsBack n C) Hs (x.length = n) (y.length = n) dom
--       (hdomA / hdomB : inputs of A / B gates whose wire is in dom are in dom)
--       (hin : R (x.getD i) (y.getD i) for inputs i in dom)
--       (hred : for gate wires i in dom with i - n outside A and B, R (val C x i) (val D y (red i))) :
--       for i in dom, R (val C x i) (val D y (f i))
-- Use: A = kept gates whose cone avoids the removed set (downward closed), mid = new gates (e.g. frag orchain stars,
-- placed at b = n + roP A len), B = the other kept gates; prove the values of the head part first (ro_val with R = Eq,
-- dom = inputs and A wires), then the mid wires from them, then ro_val again on the whole domain.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def roL (P : Finset ℕ) (m : ℕ) : List ℕ := (List.range m).filter (fun j => decide (j ∈ P))

def roP (P : Finset ℕ) (j : ℕ) : ℕ := (roL P j).length

theorem roL_succ_in (P : Finset ℕ) (m : ℕ) (h : m ∈ P) : roL P (m + 1) = roL P m ++ [m] := by
  simp [roL, List.range_succ, List.filter_append, h]

theorem roL_succ_out (P : Finset ℕ) (m : ℕ) (h : m ∉ P) : roL P (m + 1) = roL P m := by
  simp [roL, List.range_succ, List.filter_append, h]

theorem roP_mono (P : Finset ℕ) (a b : ℕ) (h : a ≤ b) : roP P a ≤ roP P b := by
  unfold roP roL
  exact ((List.range_sublist.mpr h).filter _).length_le

theorem roP_lt (P : Finset ℕ) (j m : ℕ) (hj : j < m) (hP : j ∈ P) : roP P j < roP P m := by
  have h1 : roP P (j + 1) = roP P j + 1 := by
    unfold roP
    rw [roL_succ_in P j hP, List.length_append, List.length_singleton]
  have h2 := roP_mono P (j + 1) m hj
  omega

theorem roP_card (P : Finset ℕ) (m : ℕ) (hP : ∀ j ∈ P, j < m) : roP P m = P.card := by
  have hnd : (roL P m).Nodup := List.Nodup.filter _ List.nodup_range
  have he : (roL P m).toFinset = P := by
    ext j
    simp only [roL, List.mem_toFinset, List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hP j h, h⟩⟩
  unfold roP
  rw [← List.toFinset_card_of_nodup hnd, he]

theorem roL_getD (P : Finset ℕ) (j : ℕ) (hP : j ∈ P) : ∀ m, j < m → (roL P m).getD (roP P j) 0 = j := by
  intro m
  induction m with
  | zero => intro h; omega
  | succ m ih =>
    intro hjm
    by_cases hlt : j < m
    · have hk : roP P j < (roL P m).length := roP_lt P j m hlt hP
      by_cases hm : m ∈ P
      · rw [roL_succ_in P m hm, List.getD_append _ _ _ _ hk]
        exact ih hlt
      · rw [roL_succ_out P m hm]
        exact ih hlt
    · have hj : j = m := by omega
      subst hj
      rw [roL_succ_in P j hP]
      show (roL P j ++ [j]).getD (roL P j).length 0 = j
      rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
      simp

theorem ro_map_getD (g : ℕ → Gate) (l : List ℕ) : ∀ k, k < l.length →
    (l.map g).getD k ⟨GateOp.or, []⟩ = g (l.getD k 0) := by
  induction l with
  | nil => intro k h; simp at h
  | cons a l ih =>
    intro k hk
    cases k with
    | zero => simp
    | succ k =>
      simp only [List.map_cons, List.getD_cons_succ]
      exact ih k (by simp at hk; omega)

def roG (C : Circuit) (P : Finset ℕ) (f : ℕ → ℕ) (m : ℕ) : List Gate :=
  (roL P m).map (fun j => rgate f (gateAt C j))

theorem roG_len (C : Circuit) (P : Finset ℕ) (f : ℕ → ℕ) (m : ℕ) : (roG C P f m).length = roP P m := by
  unfold roG roP
  rw [List.length_map]

theorem roG_getD (C : Circuit) (P : Finset ℕ) (f : ℕ → ℕ) (m j : ℕ) (hP : j ∈ P) (hj : j < m) :
    (roG C P f m).getD (roP P j) ⟨GateOp.or, []⟩ = rgate f (gateAt C j) := by
  unfold roG
  rw [ro_map_getD _ _ _ (roP_lt P j m hj hP), roL_getD P j hP m hj]

theorem roG_mem (C : Circuit) (P : Finset ℕ) (f : ℕ → ℕ) (m : ℕ) (g : Gate) (hg : g ∈ roG C P f m) :
    ∃ j, j ∈ P ∧ j < m ∧ g = rgate f (gateAt C j) := by
  unfold roG at hg
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg
  simp only [roL, List.mem_filter, List.mem_range, decide_eq_true_eq] at hj
  exact ⟨j, hj.2, hj.1, rfl⟩

theorem roG_rb (C : Circuit) (P : Finset ℕ) (f : ℕ → ℕ) (base : ℕ)
    (hf : ∀ j ∈ P, ∀ i ∈ (gateAt C j).inputs, f i < base + roP P j) :
    ∀ m, RBo base (roG C P f m) := by
  intro m
  induction m with
  | zero => exact RBo_nil base
  | succ m ih =>
    by_cases hm : m ∈ P
    · have e : roG C P f (m + 1) = roG C P f m ++ [rgate f (gateAt C m)] := by
        unfold roG
        rw [roL_succ_in P m hm, List.map_append, List.map_singleton]
      rw [e]
      apply RBo_append _ _ _ ih
      apply RBo_cons _ _ _ _ (RBo_nil _)
      intro i hi
      rw [rgate_inputs] at hi
      obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hi
      rw [roG_len]
      exact hf m hm i0 hi0
    · have e : roG C P f (m + 1) = roG C P f m := by
        unfold roG
        rw [roL_succ_out P m hm]
      rw [e]
      exact ih

def roOff (C : Circuit) (A : Finset ℕ) (mid : List Gate) : ℕ := roP A C.gates.length + mid.length

def roF (n : ℕ) (A B : Finset ℕ) (off : ℕ) (red : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i < n then i else if i - n ∈ A then n + roP A (i - n)
  else if i - n ∈ B then n + off + roP B (i - n) else red i

def roMap (n : ℕ) (C : Circuit) (A B : Finset ℕ) (mid : List Gate) (red : ℕ → ℕ) : ℕ → ℕ :=
  roF n A B (roOff C A mid) red

def roGates (n : ℕ) (C : Circuit) (A B : Finset ℕ) (mid : List Gate) (red : ℕ → ℕ) : List Gate :=
  roG C A (roMap n C A B mid red) C.gates.length ++ mid ++ roG C B (roMap n C A B mid red) C.gates.length

def roC (n : ℕ) (C : Circuit) (A B : Finset ℕ) (mid : List Gate) (red : ℕ → ℕ) (o : ℕ) : Circuit :=
  ⟨roGates n C A B mid red, o⟩

theorem roF_in {n : ℕ} {C : Circuit} {A B : Finset ℕ} {mid : List Gate} {red : ℕ → ℕ} {i : ℕ}
    (h : i < n) : roMap n C A B mid red i = i := by
  unfold roMap roF
  rw [if_pos h]

theorem roF_A {n : ℕ} {C : Circuit} {A B : Finset ℕ} {mid : List Gate} {red : ℕ → ℕ} {i : ℕ}
    (h : ¬ i < n) (hA : i - n ∈ A) : roMap n C A B mid red i = n + roP A (i - n) := by
  unfold roMap roF
  rw [if_neg h, if_pos hA]

theorem roF_B {n : ℕ} {C : Circuit} {A B : Finset ℕ} {mid : List Gate} {red : ℕ → ℕ} {i : ℕ}
    (h : ¬ i < n) (hA : i - n ∉ A) (hB : i - n ∈ B) :
    roMap n C A B mid red i = n + roOff C A mid + roP B (i - n) := by
  unfold roMap roF
  rw [if_neg h, if_neg hA, if_pos hB]

theorem roF_red {n : ℕ} {C : Circuit} {A B : Finset ℕ} {mid : List Gate} {red : ℕ → ℕ} {i : ℕ}
    (h : ¬ i < n) (hA : i - n ∉ A) (hB : i - n ∉ B) : roMap n C A B mid red i = red i := by
  unfold roMap roF
  rw [if_neg h, if_neg hA, if_neg hB]

theorem ro_len (n : ℕ) (C : Circuit) (A B : Finset ℕ) (mid : List Gate) (red : ℕ → ℕ) (o : ℕ) :
    (roC n C A B mid red o).gates.length = roP A C.gates.length + mid.length + roP B C.gates.length := by
  show (roGates n C A B mid red).length = _
  unfold roGates
  rw [List.length_append, List.length_append, roG_len, roG_len]

theorem ro_size (n : ℕ) (C : Circuit) (A B : Finset ℕ) (mid : List Gate) (red : ℕ → ℕ) (o : ℕ)
    (hAl : ∀ j ∈ A, j < C.gates.length) (hBl : ∀ j ∈ B, j < C.gates.length) :
    (roC n C A B mid red o).size = A.card + mid.length + B.card := by
  show (roC n C A B mid red o).gates.length = _
  rw [ro_len, roP_card A _ hAl, roP_card B _ hBl]

theorem ro_gateA (n : ℕ) (C : Circuit) (A B : Finset ℕ) (mid : List Gate) (red : ℕ → ℕ) (o : ℕ)
    (j : ℕ) (hj : j ∈ A) (hjl : j < C.gates.length) :
    gateAt (roC n C A B mid red o) (roP A j) = rgate (roMap n C A B mid red) (gateAt C j) := by
  show (roG C A (roMap n C A B mid red) C.gates.length ++ mid ++
    roG C B (roMap n C A B mid red) C.gates.length).getD (roP A j) ⟨GateOp.or, []⟩ = _
  have hk : roP A j < (roG C A (roMap n C A B mid red) C.gates.length).length := by
    rw [roG_len]; exact roP_lt A j _ hjl hj
  rw [List.append_assoc, List.getD_append _ _ _ _ hk]
  exact roG_getD C A _ _ j hj hjl

theorem ro_gateB (n : ℕ) (C : Circuit) (A B : Finset ℕ) (mid : List Gate) (red : ℕ → ℕ) (o : ℕ)
    (j : ℕ) (hj : j ∈ B) (hjl : j < C.gates.length) :
    gateAt (roC n C A B mid red o) (roOff C A mid + roP B j) =
      rgate (roMap n C A B mid red) (gateAt C j) := by
  show (roG C A (roMap n C A B mid red) C.gates.length ++ mid ++
    roG C B (roMap n C A B mid red) C.gates.length).getD (roOff C A mid + roP B j) ⟨GateOp.or, []⟩ = _
  have hl1 : (roG C A (roMap n C A B mid red) C.gates.length).length = roP A C.gates.length := roG_len _ _ _ _
  have e1 : roOff C A mid + roP B j = (roG C A (roMap n C A B mid red) C.gates.length ++ mid).length + roP B j := by
    rw [List.length_append, hl1]; rfl
  rw [e1, List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]
  exact roG_getD C B _ _ j hj hjl

theorem ro_fA (n : ℕ) (C : Circuit) (A B : Finset ℕ) (mid : List Gate) (red : ℕ → ℕ)
    (hRB : ReadsBack n C) (hAl : ∀ j ∈ A, j < C.gates.length)
    (hAcl : ∀ j ∈ A, ∀ i ∈ (gateAt C j).inputs, i < n ∨ i - n ∈ A)
    (j : ℕ) (hj : j ∈ A) (i : ℕ) (hi : i ∈ (gateAt C j).inputs) :
    roMap n C A B mid red i < n + roP A j := by
  have hlt : i < n + j := hRB j (hAl j hj) i hi
  by_cases h1 : i < n
  · rw [roF_in h1]; omega
  · have h2 : i - n ∈ A := by
      rcases hAcl j hj i hi with h | h
      · exact absurd h h1
      · exact h
    rw [roF_A h1 h2]
    have := roP_lt A (i - n) j (by omega) h2
    omega

theorem ro_fB (n : ℕ) (C : Circuit) (A B : Finset ℕ) (mid : List Gate) (red : ℕ → ℕ)
    (hRB : ReadsBack n C) (hAl : ∀ j ∈ A, j < C.gates.length) (hBl : ∀ j ∈ B, j < C.gates.length)
    (hBrd : ∀ j ∈ B, ∀ i ∈ (gateAt C j).inputs, n ≤ i → i - n ∉ A → i - n ∉ B →
      red i < n + roOff C A mid)
    (j : ℕ) (hj : j ∈ B) (i : ℕ) (hi : i ∈ (gateAt C j).inputs) :
    roMap n C A B mid red i < n + roOff C A mid + roP B j := by
  have hlt : i < n + j := hRB j (hBl j hj) i hi
  by_cases h1 : i < n
  · rw [roF_in h1]; omega
  · by_cases h2 : i - n ∈ A
    · rw [roF_A h1 h2]
      have := roP_lt A (i - n) C.gates.length (hAl _ h2) h2
      unfold roOff
      omega
    · by_cases h3 : i - n ∈ B
      · rw [roF_B h1 h2 h3]
        have := roP_lt B (i - n) j (by omega) h3
        omega
      · rw [roF_red h1 h2 h3]
        have := hBrd j hj i hi (by omega) h2 h3
        omega

theorem ro_rb (n : ℕ) (C : Circuit) (A B : Finset ℕ) (mid : List Gate) (red : ℕ → ℕ) (o : ℕ)
    (hRB : ReadsBack n C) (hAl : ∀ j ∈ A, j < C.gates.length) (hBl : ∀ j ∈ B, j < C.gates.length)
    (hAcl : ∀ j ∈ A, ∀ i ∈ (gateAt C j).inputs, i < n ∨ i - n ∈ A)
    (hBrd : ∀ j ∈ B, ∀ i ∈ (gateAt C j).inputs, n ≤ i → i - n ∉ A → i - n ∉ B →
      red i < n + roOff C A mid)
    (hmid : RBo (n + roP A C.gates.length) mid) :
    ReadsBack n (roC n C A B mid red o) := by
  have h : RBo n (roGates n C A B mid red) := by
    unfold roGates
    rw [List.append_assoc]
    apply RBo_append
    · exact roG_rb C A _ n (fun j hj i hi => ro_fA n C A B mid red hRB hAl hAcl j hj i hi) _
    · rw [roG_len]
      apply RBo_append _ _ _ hmid
      have e : n + roP A C.gates.length + mid.length = n + roOff C A mid := by
        unfold roOff; omega
      rw [e]
      exact roG_rb C B _ _ (fun j hj i hi => ro_fB n C A B mid red hRB hAl hBl hBrd j hj i hi) _
  exact h

theorem ro_isAO2 (n : ℕ) (C : Circuit) (A B : Finset ℕ) (mid : List Gate) (red : ℕ → ℕ) (o : ℕ)
    (hC : PEqualNP.TopForm.IsAO2 n C) (hAl : ∀ j ∈ A, j < C.gates.length) (hBl : ∀ j ∈ B, j < C.gates.length)
    (hAcl : ∀ j ∈ A, ∀ i ∈ (gateAt C j).inputs, i < n ∨ i - n ∈ A)
    (hBrd : ∀ j ∈ B, ∀ i ∈ (gateAt C j).inputs, n ≤ i → i - n ∉ A → i - n ∉ B →
      red i < n + roOff C A mid)
    (hmid : RBo (n + roP A C.gates.length) mid)
    (hmidg : ∀ g ∈ mid, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) :
    PEqualNP.TopForm.IsAO2 n (roC n C A B mid red o) := by
  obtain ⟨hao, hRB, h2⟩ := hC
  have hg : ∀ g ∈ (roC n C A B mid red o).gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
    intro g hgm
    have hgm' : g ∈ roG C A (roMap n C A B mid red) C.gates.length ++ mid ++
      roG C B (roMap n C A B mid red) C.gates.length := hgm
    have hold : ∀ (P : Finset ℕ), g ∈ roG C P (roMap n C A B mid red) C.gates.length →
        (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
      intro P hP
      obtain ⟨j, _, hjl, rfl⟩ := roG_mem C P _ _ g hP
      exact ⟨by rw [rgate_op]; exact hao _ (gateAt_mem hjl), by rw [rgate_len]; exact h2 _ (gateAt_mem hjl)⟩
    rcases List.mem_append.mp hgm' with h1 | h1
    · rcases List.mem_append.mp h1 with h3 | h3
      · exact hold A h3
      · exact hmidg g h3
    · exact hold B h1
  exact ⟨fun g hgm => (hg g hgm).1, ro_rb n C A B mid red o hRB hAl hBl hAcl hBrd hmid,
    fun g hgm => (hg g hgm).2⟩

theorem ro_val {R : Bool → Bool → Prop} (hR : OpMono R) (n : ℕ) (C : Circuit) (A B : Finset ℕ)
    (mid : List Gate) (red : ℕ → ℕ) (o : ℕ)
    (hAO : PEqualNP.EdgeOwnership.AndOrOnly C) (hRB : ReadsBack n C)
    (hAl : ∀ j ∈ A, j < C.gates.length) (hBl : ∀ j ∈ B, j < C.gates.length)
    (hAcl : ∀ j ∈ A, ∀ i ∈ (gateAt C j).inputs, i < n ∨ i - n ∈ A)
    (hBrd : ∀ j ∈ B, ∀ i ∈ (gateAt C j).inputs, n ≤ i → i - n ∉ A → i - n ∉ B →
      red i < n + roOff C A mid)
    (x y : List Bool) (hx : x.length = n) (hy : y.length = n) (dom : ℕ → Prop)
    (hdomA : ∀ j ∈ A, dom (n + j) → ∀ i ∈ (gateAt C j).inputs, dom i)
    (hdomB : ∀ j ∈ B, dom (n + j) → ∀ i ∈ (gateAt C j).inputs, dom i)
    (hin : ∀ i, i < n → dom i → R (x.getD i false) (y.getD i false))
    (hred : ∀ i, dom i → n ≤ i → i - n ∉ A → i - n ∉ B →
      R (val C x i) (val (roC n C A B mid red o) y (red i))) :
    ∀ i, dom i → R (val C x i) (val (roC n C A B mid red o) y (roMap n C A B mid red i)) := by
  have hlen := ro_len n C A B mid red o
  refine mc_run hR hx hy dom (roMap n C A B mid red) ?_
  intro u hu _
  by_cases h1 : u < n
  · left
    rw [roF_in h1, (mc_input (C := C) (D := roC n C A B mid red o) hx hy h1).1,
      (mc_input (C := C) (D := roC n C A B mid red o) hx hy h1).2]
    exact hin u h1 hu
  · by_cases h2 : u - n ∈ A
    · right
      have hjl := hAl _ h2
      have hp := roP_lt A (u - n) _ hjl h2
      refine ⟨u - n, roP A (u - n), by omega, roF_A h1 h2, hjl, by omega, hAO _ (gateAt_mem hjl),
        ro_gateA n C A B mid red o _ h2 hjl, ?_⟩
      intro i hi
      have hu2 : dom (n + (u - n)) := by
        have e : n + (u - n) = u := by omega
        rw [e]; exact hu
      exact ⟨hRB _ hjl i hi, ro_fA n C A B mid red hRB hAl hAcl _ h2 i hi, hdomA _ h2 hu2 i hi⟩
    · by_cases h3 : u - n ∈ B
      · right
        have hjl := hBl _ h3
        have hp := roP_lt B (u - n) _ hjl h3
        have hoff : roOff C A mid = roP A C.gates.length + mid.length := rfl
        refine ⟨u - n, roOff C A mid + roP B (u - n), by omega, by rw [roF_B h1 h2 h3]; omega, hjl,
          by omega, hAO _ (gateAt_mem hjl), ro_gateB n C A B mid red o _ h3 hjl, ?_⟩
        intro i hi
        have hu2 : dom (n + (u - n)) := by
          have e : n + (u - n) = u := by omega
          rw [e]; exact hu
        refine ⟨hRB _ hjl i hi, ?_, hdomB _ h3 hu2 i hi⟩
        have := ro_fB n C A B mid red hRB hAl hBl hBrd _ h3 i hi
        omega
      · left
        rw [roF_red h1 h2 h3]
        exact hred u hu (by omega) h2 h3

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

-- FRAGMENT falseprop    DEPENDS: fold mono flow restrict monocmp reorder
-- Forcing a set Z of gates of an IsAO2 circuit to false and propagating the constant upward: fzC C Z is C with
-- every gate of Z replaced by the constant-false gate (OR of nothing); S = fzS n C Z is the set of gates that are
-- false at every input of fzC C Z (it contains Z, every AND reading S and every OR reading two S wires). The
-- gates of S are removed; a kept OR gate reading one S wire a and another wire b becomes OR(b, b). Result: an IsAO2
-- circuit with |S| gates fewer whose output is the output of fzC C Z.
-- Abbreviations: len = C.gates.length, S = fzS n C Z, S-wire i means n <= i and i - n in S.
-- Exports:
--   def fzC C Z (same length and output; gate j is OR of nothing if j in Z, else gateAt C j)
--   fzC_len ;  fzC_gateAt (j < len) : gateAt (fzC C Z) j = if j in Z then OR of nothing else gateAt C j
--   fz_valZ (j in Z) (j < len) (x.length = n) : val (fzC C Z) x (n + j) = false
--   fz_le (AndOrOnly C) (ReadsBack n C) (x.length = n) : val (fzC C Z) x w = true -> val C x w = true  (all w)
--   def fzS n C Z := gates j < len with val (fzC C Z) (ofFn x) (n + j) = false for every x : Fin n -> Bool
--   mem_fzS : j in fzS n C Z iff j < len and for all x, val (fzC C Z) (List.ofFn x) (n + j) = false
--   fz_sub (Z below len) : Z subset fzS n C Z ;  fzS_lt : j in fzS n C Z -> j < len
--   def fzG n S g (OR(b, b) / OR(a, a) rewrite when operand a / b is an S-wire) ;  def fz1 n C Z (fzG on every gate)
--   fz_two (IsAO2) (k < len) (k not in Z) (inputs of k = [a, b]) (x.length = n) :
--       val (fzC C Z) x (n + k) = (gateAt C k).op.eval [val (fzC C Z) x a, val (fzC C Z) x b]
--   fz_case (IsAO2) (Z below len) (k < len) (k not in S) (inputs [a, b]) : a S-wire -> op = or and b not S-wire
--       (and the symmetric fz_case2 for b)
--   fz1_isAO2 (IsAO2 n C) : IsAO2 n (fz1 n C Z) ;  fz_cl : no kept gate of fz1 reads an S-wire (hcl of frag restrict)
--   fz_eq (IsAO2) (Z below len) z : for u < n or (n <= u, u - n < len, u - n not in S),
--       val (fz1 n C Z) (ofFn z) u = val (fzC C Z) (ofFn z) u
--   fz_circ (IsAO2 n C) (Z below len) (o < len) (o not in S) (C.output = n + o) :
--       exists D, IsAO2 n D and D.size + S.card <= C.size and
--       for all x : Fin n -> Bool, circuitFun n D x = val (fzC C Z) (List.ofFn x) (n + o)
-- Use: to remove gates that accept nothing useful (e.g. readers false at every edge-pair input), take Z = them
-- (plus any removed gates only read by them), show o not in S with an input where fzC is true at the output
-- (compare fzC with C by mc_run on the inputs of interest), then compare the output values with fz_le and monotonicity.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def fzC (C : Circuit) (Z : Finset ℕ) : Circuit :=
  ⟨(List.range C.gates.length).map (fun j => if j ∈ Z then (⟨GateOp.or, []⟩ : Gate) else gateAt C j),
    C.output⟩

theorem fzC_len (C : Circuit) (Z : Finset ℕ) : (fzC C Z).gates.length = C.gates.length := by
  simp [fzC]

theorem fz_range_getD (m j : ℕ) (hj : j < m) : (List.range m).getD j 0 = j := by
  simp [List.getD_eq_getElem?_getD, hj]

theorem fzC_gateAt (C : Circuit) (Z : Finset ℕ) (j : ℕ) (hj : j < C.gates.length) :
    gateAt (fzC C Z) j = if j ∈ Z then (⟨GateOp.or, []⟩ : Gate) else gateAt C j := by
  show ((List.range C.gates.length).map
    (fun j => if j ∈ Z then (⟨GateOp.or, []⟩ : Gate) else gateAt C j)).getD j ⟨GateOp.or, []⟩ = _
  rw [ro_map_getD _ _ j (by simpa using hj), fz_range_getD _ _ hj]

theorem fz_valZ {n : ℕ} (C : Circuit) (Z : Finset ℕ) (j : ℕ) (hZ : j ∈ Z) (hj : j < C.gates.length)
    (x : List Bool) (hx : x.length = n) : val (fzC C Z) x (n + j) = false := by
  rw [val_gate hx (by rw [fzC_len]; exact hj), fzC_gateAt C Z j hj, if_pos hZ]
  rfl

theorem fz_le {n : ℕ} (C : Circuit) (Z : Finset ℕ) (hAO : PEqualNP.EdgeOwnership.AndOrOnly C)
    (hRB : ReadsBack n C) (x : List Bool) (hx : x.length = n) :
    ∀ w, val (fzC C Z) x w = true → val C x w = true := by
  intro w
  refine mc_run opMono_imp (C := fzC C Z) (D := C) hx hx (fun _ => True) id ?_ w trivial
  intro u _ _
  by_cases h1 : u < n
  · left
    show val (fzC C Z) x u = true → val C x u = true
    rw [(mc_input (C := fzC C Z) (D := C) hx hx h1).1, (mc_input (C := fzC C Z) (D := C) hx hx h1).2]
    exact id
  · by_cases h2 : u < n + C.gates.length
    · have hj : u - n < C.gates.length := by omega
      have e : u = n + (u - n) := by omega
      by_cases hZ : u - n ∈ Z
      · left
        rw [e, fz_valZ C Z _ hZ hj x hx]
        intro h; cases h
      · right
        have hg : gateAt (fzC C Z) (u - n) = gateAt C (u - n) := by
          rw [fzC_gateAt C Z _ hj, if_neg hZ]
        refine ⟨u - n, u - n, e, e, by rw [fzC_len]; exact hj, hj, ?_, ?_, ?_⟩
        · rw [hg]; exact hAO _ (gateAt_mem hj)
        · rw [hg, rgate_id1]
        · intro i hi
          rw [hg] at hi
          have := hRB _ hj i hi
          exact ⟨this, this, trivial⟩
    · left
      rw [val_ge hx (by rw [fzC_len]; omega)]
      intro h; cases h

def fzS (n : ℕ) (C : Circuit) (Z : Finset ℕ) : Finset ℕ :=
  (Finset.range C.gates.length).filter
    (fun j => ∀ x : Fin n → Bool, val (fzC C Z) (List.ofFn x) (n + j) = false)

theorem mem_fzS (n : ℕ) (C : Circuit) (Z : Finset ℕ) (j : ℕ) :
    j ∈ fzS n C Z ↔ j < C.gates.length ∧ ∀ x : Fin n → Bool, val (fzC C Z) (List.ofFn x) (n + j) = false := by
  simp [fzS]

theorem fzS_lt (n : ℕ) (C : Circuit) (Z : Finset ℕ) (j : ℕ) (h : j ∈ fzS n C Z) : j < C.gates.length :=
  ((mem_fzS n C Z j).mp h).1

theorem fz_sub (n : ℕ) (C : Circuit) (Z : Finset ℕ) (hZ : ∀ j ∈ Z, j < C.gates.length) :
    Z ⊆ fzS n C Z := by
  intro j hj
  rw [mem_fzS]
  exact ⟨hZ j hj, fun x => fz_valZ C Z j hj (hZ j hj) (List.ofFn x) (by simp)⟩

def fzG (n : ℕ) (S : Finset ℕ) (g : Gate) : Gate :=
  if n ≤ g.inputs.getD 0 0 ∧ g.inputs.getD 0 0 - n ∈ S then
    ⟨g.op, [g.inputs.getD 1 0, g.inputs.getD 1 0]⟩
  else if n ≤ g.inputs.getD 1 0 ∧ g.inputs.getD 1 0 - n ∈ S then
    ⟨g.op, [g.inputs.getD 0 0, g.inputs.getD 0 0]⟩
  else g

def fz1 (n : ℕ) (C : Circuit) (Z : Finset ℕ) : Circuit :=
  ⟨(List.range C.gates.length).map (fun j => fzG n (fzS n C Z) (gateAt C j)), C.output⟩

theorem fz1_len (n : ℕ) (C : Circuit) (Z : Finset ℕ) : (fz1 n C Z).gates.length = C.gates.length := by
  simp [fz1]

theorem fz1_gateAt (n : ℕ) (C : Circuit) (Z : Finset ℕ) (j : ℕ) (hj : j < C.gates.length) :
    gateAt (fz1 n C Z) j = fzG n (fzS n C Z) (gateAt C j) := by
  show ((List.range C.gates.length).map
    (fun j => fzG n (fzS n C Z) (gateAt C j))).getD j ⟨GateOp.or, []⟩ = _
  rw [ro_map_getD _ _ j (by simpa using hj), fz_range_getD _ _ hj]

theorem fzG_ab (n : ℕ) (S : Finset ℕ) (g : Gate) (a b : ℕ) (hab : g.inputs = [a, b]) :
    fzG n S g = if n ≤ a ∧ a - n ∈ S then (⟨g.op, [b, b]⟩ : Gate)
      else if n ≤ b ∧ b - n ∈ S then (⟨g.op, [a, a]⟩ : Gate) else g := by
  unfold fzG
  rw [hab]
  rfl

theorem fzG_op (n : ℕ) (S : Finset ℕ) (g : Gate) : (fzG n S g).op = g.op := by
  unfold fzG
  split_ifs <;> rfl

theorem fzG_sub (n : ℕ) (S : Finset ℕ) (g : Gate) (h2 : g.inputs.length = 2) (i : ℕ)
    (hi : i ∈ (fzG n S g).inputs) : i ∈ g.inputs ∧ (fzG n S g).inputs.length = 2 := by
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp h2
  rw [fzG_ab n S g a b hab] at hi ⊢
  rw [hab]
  split_ifs at hi ⊢ with c1 c2
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
    exact ⟨by omega, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
    exact ⟨by omega, rfl⟩
  · rw [hab] at hi
    exact ⟨hi, hab ▸ rfl⟩

theorem fz_two {n : ℕ} (C : Circuit) (Z : Finset ℕ) (hC : PEqualNP.TopForm.IsAO2 n C) (k : ℕ)
    (hk : k < C.gates.length) (hkZ : k ∉ Z) (a b : ℕ) (hab : (gateAt C k).inputs = [a, b])
    (x : List Bool) (hx : x.length = n) :
    val (fzC C Z) x (n + k) = (gateAt C k).op.eval [val (fzC C Z) x a, val (fzC C Z) x b] := by
  have hg : gateAt (fzC C Z) k = gateAt C k := by rw [fzC_gateAt C Z k hk, if_neg hkZ]
  have hrb : ∀ i ∈ (gateAt (fzC C Z) k).inputs, i < n + k := by
    intro i hi
    rw [hg] at hi
    exact hC.2.1 k hk i hi
  rw [val_gate_rb hx (by rw [fzC_len]; exact hk) hrb, hg, hab]
  rfl

theorem fz_Swire (n : ℕ) (C : Circuit) (Z : Finset ℕ) (i : ℕ) (h : n ≤ i ∧ i - n ∈ fzS n C Z)
    (x : Fin n → Bool) : val (fzC C Z) (List.ofFn x) i = false := by
  have h1 := ((mem_fzS n C Z (i - n)).mp h.2).2 x
  have e : n + (i - n) = i := by omega
  rw [e] at h1
  exact h1

theorem fz_inS (n : ℕ) (C : Circuit) (Z : Finset ℕ) (hC : PEqualNP.TopForm.IsAO2 n C) (k : ℕ)
    (hk : k < C.gates.length) (hkZ : k ∉ Z) (a b : ℕ) (hab : (gateAt C k).inputs = [a, b])
    (h : ∀ x : Fin n → Bool, (gateAt C k).op.eval [val (fzC C Z) (List.ofFn x) a,
      val (fzC C Z) (List.ofFn x) b] = false) : k ∈ fzS n C Z := by
  rw [mem_fzS]
  refine ⟨hk, fun x => ?_⟩
  rw [fz_two C Z hC k hk hkZ a b hab (List.ofFn x) (by simp)]
  exact h x

theorem fz_case (n : ℕ) (C : Circuit) (Z : Finset ℕ) (hC : PEqualNP.TopForm.IsAO2 n C)
    (hZ : ∀ j ∈ Z, j < C.gates.length) (k : ℕ) (hk : k < C.gates.length) (hkS : k ∉ fzS n C Z)
    (a b : ℕ) (hab : (gateAt C k).inputs = [a, b]) (ha : n ≤ a ∧ a - n ∈ fzS n C Z) :
    (gateAt C k).op = GateOp.or ∧ ¬ (n ≤ b ∧ b - n ∈ fzS n C Z) := by
  have hkZ : k ∉ Z := fun h => hkS (fz_sub n C Z hZ h)
  rcases hC.1 _ (gateAt_mem hk) with hop | hop
  · exfalso
    apply hkS
    apply fz_inS n C Z hC k hk hkZ a b hab
    intro x
    rw [hop, fz_Swire n C Z a ha x]
    rfl
  · refine ⟨hop, fun hb => hkS ?_⟩
    apply fz_inS n C Z hC k hk hkZ a b hab
    intro x
    rw [hop, fz_Swire n C Z a ha x, fz_Swire n C Z b hb x]
    rfl

theorem fz_case2 (n : ℕ) (C : Circuit) (Z : Finset ℕ) (hC : PEqualNP.TopForm.IsAO2 n C)
    (hZ : ∀ j ∈ Z, j < C.gates.length) (k : ℕ) (hk : k < C.gates.length) (hkS : k ∉ fzS n C Z)
    (a b : ℕ) (hab : (gateAt C k).inputs = [a, b]) (hb : n ≤ b ∧ b - n ∈ fzS n C Z) :
    (gateAt C k).op = GateOp.or ∧ ¬ (n ≤ a ∧ a - n ∈ fzS n C Z) := by
  have hkZ : k ∉ Z := fun h => hkS (fz_sub n C Z hZ h)
  rcases hC.1 _ (gateAt_mem hk) with hop | hop
  · exfalso
    apply hkS
    apply fz_inS n C Z hC k hk hkZ a b hab
    intro x
    rw [hop, fz_Swire n C Z b hb x]
    simp [GateOp.eval]
  · refine ⟨hop, fun ha => hkS ?_⟩
    apply fz_inS n C Z hC k hk hkZ a b hab
    intro x
    rw [hop, fz_Swire n C Z a ha x, fz_Swire n C Z b hb x]
    rfl

theorem fz_notS (n : ℕ) (S : Finset ℕ) (i : ℕ) (h : ¬ (n ≤ i ∧ i - n ∈ S)) : i < n ∨ i - n ∉ S := by
  by_cases h1 : i < n
  · exact Or.inl h1
  · exact Or.inr (fun h2 => h ⟨by omega, h2⟩)

theorem fz_cl (n : ℕ) (C : Circuit) (Z : Finset ℕ) (hC : PEqualNP.TopForm.IsAO2 n C)
    (hZ : ∀ j ∈ Z, j < C.gates.length) :
    ∀ k < (fz1 n C Z).gates.length, k ∉ fzS n C Z →
      ∀ i ∈ (gateAt (fz1 n C Z) k).inputs, i < n ∨ i - n ∉ fzS n C Z := by
  intro k hk1 hkS i hi
  have hk : k < C.gates.length := by rw [fz1_len] at hk1; exact hk1
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hC.2.2 _ (gateAt_mem hk))
  rw [fz1_gateAt n C Z k hk, fzG_ab n _ _ a b hab] at hi
  split_ifs at hi with c1 c2
  · have := (fz_case n C Z hC hZ k hk hkS a b hab c1).2
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hi
    subst hi
    exact fz_notS n _ i this
  · simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hi
    subst hi
    exact fz_notS n _ i c1
  · rw [hab] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact fz_notS n _ i c1
    · exact fz_notS n _ i c2

theorem fz1_isAO2 (n : ℕ) (C : Circuit) (Z : Finset ℕ) (hC : PEqualNP.TopForm.IsAO2 n C) :
    PEqualNP.TopForm.IsAO2 n (fz1 n C Z) := by
  obtain ⟨hao, hRB, h2⟩ := hC
  have hmem : ∀ g ∈ (fz1 n C Z).gates, ∃ j, j < C.gates.length ∧ g = fzG n (fzS n C Z) (gateAt C j) := by
    intro g hg
    have hg' : g ∈ (List.range C.gates.length).map (fun j => fzG n (fzS n C Z) (gateAt C j)) := hg
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg'
    exact ⟨j, List.mem_range.mp hj, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := hmem g hg
    rw [fzG_op]
    exact hao _ (gateAt_mem hj)
  · intro j hj i hi
    have hj' : j < C.gates.length := by rw [fz1_len] at hj; exact hj
    rw [fz1_gateAt n C Z j hj'] at hi
    exact hRB j hj' i (fzG_sub n _ _ (h2 _ (gateAt_mem hj')) i hi).1
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := hmem g hg
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem hj))
    rw [fzG_ab n _ _ a b hab]
    split_ifs
    · rfl
    · rfl
    · rw [hab]; rfl

theorem fz_eq (n : ℕ) (C : Circuit) (Z : Finset ℕ) (hC : PEqualNP.TopForm.IsAO2 n C)
    (hZ : ∀ j ∈ Z, j < C.gates.length) (z : Fin n → Bool) :
    ∀ u, (u < n ∨ (n ≤ u ∧ u - n < C.gates.length ∧ u - n ∉ fzS n C Z)) →
      val (fz1 n C Z) (List.ofFn z) u = val (fzC C Z) (List.ofFn z) u := by
  intro u hu
  have hx : (List.ofFn z).length = n := by simp
  have key := mc_run opMono_eq (C := fzC C Z) (D := fz1 n C Z) hx hx
    (fun u => u < n ∨ (n ≤ u ∧ u - n < C.gates.length ∧ u - n ∉ fzS n C Z)) id ?_ u hu
  · exact key.symm
  intro u hu ih
  rcases hu with h1 | ⟨h1, hk, hkS⟩
  · left
    show val (fzC C Z) (List.ofFn z) u = val (fz1 n C Z) (List.ofFn z) u
    rw [(mc_input (C := fzC C Z) (D := fz1 n C Z) hx hx h1).1,
      (mc_input (C := fzC C Z) (D := fz1 n C Z) hx hx h1).2]
  · have e : u = n + (u - n) := by omega
    have hkZ : u - n ∉ Z := fun h => hkS (fz_sub n C Z hZ h)
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hC.2.2 _ (gateAt_mem hk))
    have hra : a < n + (u - n) := hC.2.1 _ hk a (by rw [hab]; simp)
    have hrb : b < n + (u - n) := hC.2.1 _ hk b (by rw [hab]; simp)
    have hdom : ∀ i, i < n + (u - n) → ¬ (n ≤ i ∧ i - n ∈ fzS n C Z) →
        (i < n ∨ (n ≤ i ∧ i - n < C.gates.length ∧ i - n ∉ fzS n C Z)) := by
      intro i hi hn
      by_cases h3 : i < n
      · exact Or.inl h3
      · exact Or.inr ⟨by omega, by omega, fun h4 => hn ⟨by omega, h4⟩⟩
    have hgate : gateAt (fz1 n C Z) (u - n) = fzG n (fzS n C Z) (gateAt C (u - n)) :=
      fz1_gateAt n C Z _ hk
    rw [fzG_ab n _ _ a b hab] at hgate
    have hv1 : val (fzC C Z) (List.ofFn z) u =
        (gateAt C (u - n)).op.eval [val (fzC C Z) (List.ofFn z) a, val (fzC C Z) (List.ofFn z) b] := by
      have h := fz_two C Z hC _ hk hkZ a b hab _ hx
      rw [← e] at h
      exact h
    have hv0 : ∀ c, (gateAt (fz1 n C Z) (u - n)).inputs = [c, c] → c < n + (u - n) →
        (gateAt C (u - n)).op = GateOp.or →
        val (fz1 n C Z) (List.ofFn z) u = val (fz1 n C Z) (List.ofFn z) c := by
      intro c hcc hc hop
      have hrb2 : ∀ i ∈ (gateAt (fz1 n C Z) (u - n)).inputs, i < n + (u - n) := by
        rw [hcc]
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hi
        omega
      have h := val_gate_rb (C := fz1 n C Z) hx (j := u - n) (by rw [fz1_len]; exact hk) hrb2
      rw [← e] at h
      rw [h, hcc]
      have hop2 : (gateAt (fz1 n C Z) (u - n)).op = GateOp.or := by
        rw [fz1_gateAt n C Z _ hk, fzG_op]; exact hop
      rw [hop2]
      simp [GateOp.eval]
    split_ifs at hgate with c1 c2
    · left
      obtain ⟨hop, hb⟩ := fz_case n C Z hC hZ _ hk hkS a b hab c1
      have hv2 := hv0 b (by rw [hgate]) hrb hop
      have ihb : val (fzC C Z) (List.ofFn z) b = val (fz1 n C Z) (List.ofFn z) b :=
        ih b (by omega) (hdom b hrb hb)
      show val (fzC C Z) (List.ofFn z) u = val (fz1 n C Z) (List.ofFn z) u
      rw [hv1, hv2, hop, fz_Swire n C Z a c1 z, ← ihb]
      simp [GateOp.eval]
    · left
      obtain ⟨hop, ha⟩ := fz_case2 n C Z hC hZ _ hk hkS a b hab c2
      have hv2 := hv0 a (by rw [hgate]) hra hop
      have iha : val (fzC C Z) (List.ofFn z) a = val (fz1 n C Z) (List.ofFn z) a :=
        ih a (by omega) (hdom a hra ha)
      show val (fzC C Z) (List.ofFn z) u = val (fz1 n C Z) (List.ofFn z) u
      rw [hv1, hv2, hop, fz_Swire n C Z b c2 z, ← iha]
      simp [GateOp.eval]
    · right
      have hg0 : gateAt (fzC C Z) (u - n) = gateAt C (u - n) := by
        rw [fzC_gateAt C Z _ hk, if_neg hkZ]
      refine ⟨u - n, u - n, e, e, by rw [fzC_len]; exact hk, by rw [fz1_len]; exact hk, ?_, ?_, ?_⟩
      · rw [hg0]; exact hC.1 _ (gateAt_mem hk)
      · rw [hg0, rgate_id1, hgate]
      · intro i hi
        rw [hg0, hab] at hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact ⟨hra, hra, hdom _ hra c1⟩
        · exact ⟨hrb, hrb, hdom _ hrb c2⟩

theorem fz_circ (n : ℕ) (C : Circuit) (Z : Finset ℕ) (hC : PEqualNP.TopForm.IsAO2 n C)
    (hZ : ∀ j ∈ Z, j < C.gates.length) (o : ℕ) (ho : o < C.gates.length) (hoS : o ∉ fzS n C Z)
    (hout : C.output = n + o) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size + (fzS n C Z).card ≤ C.size ∧
      ∀ x : Fin n → Bool, circuitFun n D x = val (fzC C Z) (List.ofFn x) (n + o) := by
  obtain ⟨D, hD, hfun, hsize⟩ := restrict_circ n (fz1 n C Z) (fzS n C Z) (fz1_isAO2 n C Z hC)
    (fz_cl n C Z hC hZ) (fun j hj => by rw [fz1_len]; exact fzS_lt n C Z j hj) o
    (by rw [fz1_len]; exact ho) hoS hout
  refine ⟨D, hD, ?_, ?_⟩
  · have e : (fz1 n C Z).size = C.size := fz1_len n C Z
    omega
  · intro x
    rw [hfun]
    show val (fz1 n C Z) (List.ofFn x) (fz1 n C Z).output = _
    show val (fz1 n C Z) (List.ofFn x) C.output = _
    rw [hout]
    exact fz_eq n C Z hC hZ x (n + o) (Or.inr ⟨by omega, by omega, by rw [Nat.add_sub_cancel_left]; exact hoS⟩)

theorem m29_gF {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphFun]

theorem m29_pair_comm {n : ℕ} (u v : Fin n) :
    PEqualNP.EdgeOwnership.pairInput u v = PEqualNP.EdgeOwnership.pairInput v u := by
  funext w
  simp only [PEqualNP.EdgeOwnership.pairInput, or_comm]

theorem m29_pair_u {n : ℕ} (u v : Fin n) : PEqualNP.EdgeOwnership.pairInput u v u = true := by
  simp [PEqualNP.EdgeOwnership.pairInput]

theorem m29_pair_v {n : ℕ} (u v : Fin n) : PEqualNP.EdgeOwnership.pairInput u v v = true := by
  simp [PEqualNP.EdgeOwnership.pairInput]

theorem m29_pairF {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) (h : G.Adj u v) :
    graphFun G ∅ (PEqualNP.EdgeOwnership.pairInput u v) = true :=
  (m29_gF G _).mpr ⟨u, v, h, m29_pair_u u v, m29_pair_v u v⟩

theorem m29_unitF {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (p : Fin n) :
    graphFun G ∅ (PEqualNP.SplitCount.unitInput p) = false := by
  cases h : graphFun G ∅ (PEqualNP.SplitCount.unitInput p)
  · rfl
  · obtain ⟨u, v, hadj, hu, hv⟩ := (m29_gF G _).mp h
    simp only [PEqualNP.SplitCount.unitInput, decide_eq_true_eq] at hu hv
    subst hu
    subst hv
    exact absurd hadj G.irrefl

theorem m29_out {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hfun : circuitFun n C = graphFun G ∅) (u v : Fin n) (huv : G.Adj u v) :
    n ≤ C.output ∧ C.output < n + C.gates.length := by
  constructor
  · by_contra hlt
    have hlt2 : C.output < n := by omega
    have h1 := congrFun hfun (PEqualNP.SplitCount.unitInput ⟨C.output, hlt2⟩)
    rw [m29_unitF, circuitFun_val, val_ofFn_lt C _ _ hlt2] at h1
    simp [PEqualNP.SplitCount.unitInput] at h1
  · by_contra hge
    have hge2 : n + C.gates.length ≤ C.output := by omega
    have h1 := congrFun hfun (PEqualNP.EdgeOwnership.pairInput u v)
    rw [m29_pairF G u v huv, circuitFun_val, val_ge (n := n) (by simp) hge2] at h1
    cases h1

theorem m29_card (n : ℕ) (C : Circuit) (Om Rd : Finset ℕ)
    (hOm : ∀ k ∈ Om, k < C.gates.length ∧ C.output ≠ n + k)
    (hRd : ∀ X : ℕ, X ∈ Rd ↔ (X < C.gates.length ∧ X ∉ Om ∧ ∃ k ∈ Om, n + k ∈ (gateAt C X).inputs)) :
    Om.card + Rd.card ≤ C.gates.length := by
  have hdisj : Disjoint Om Rd := Finset.disjoint_left.mpr (fun j h1 h2 => ((hRd j).mp h2).2.1 h1)
  rw [← Finset.card_union_of_disjoint hdisj]
  have hsub : Om ∪ Rd ⊆ Finset.range C.gates.length := by
    intro j hj
    rw [Finset.mem_range]
    rcases Finset.mem_union.mp hj with h | h
    · exact (hOm j h).1
    · exact ((hRd j).mp h).1
  have := Finset.card_le_card hsub
  rwa [Finset.card_range] at this

theorem m29_noStar {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (Om Rd : Finset ℕ)
    (hC : PEqualNP.TopForm.IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (hOm : ∀ k ∈ Om, k < C.gates.length ∧ C.output ≠ n + k)
    (hRd : ∀ X : ℕ, X ∈ Rd ↔ (X < C.gates.length ∧ X ∉ Om ∧ ∃ k ∈ Om, n + k ∈ (gateAt C X).inputs))
    (hzero : ∀ X ∈ Rd, ∀ u v : Fin n, G.Adj u v →
      PEqualNP.EdgeOwnership.gateVal n C X (PEqualNP.EdgeOwnership.pairInput u v) = false)
    (u0 v0 : Fin n) (huv : G.Adj u0 v0) (o : ℕ) (ho : o < C.gates.length) (hout : C.output = n + o) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧
      D.size + Om.card + Rd.card ≤ C.size := by
  have hoOm : o ∉ Om := fun h => (hOm o h).2 hout
  have hZ : ∀ j ∈ Om ∪ Rd, j < C.gates.length := by
    intro j hj
    rcases Finset.mem_union.mp hj with h | h
    · exact (hOm j h).1
    · exact ((hRd j).mp h).1
  have hdisj : Disjoint Om Rd := Finset.disjoint_left.mpr (fun j h1 h2 => ((hRd j).mp h2).2.1 h1)
  have hcard : (Om ∪ Rd).card = Om.card + Rd.card := Finset.card_union_of_disjoint hdisj
  have hagree : ∀ u v : Fin n, G.Adj u v → ∀ w, (w < n ∨ (n ≤ w ∧ w - n < C.gates.length ∧ w - n ∉ Om)) →
      val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v)) w =
        val (fzC C (Om ∪ Rd)) (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v)) w := by
    intro u v huv w hw
    have hx : (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v)).length = n := by simp
    refine mc_run opMono_eq (C := C) (D := fzC C (Om ∪ Rd)) hx hx
      (fun t => t < n ∨ (n ≤ t ∧ t - n < C.gates.length ∧ t - n ∉ Om)) id ?_ w hw
    intro t ht _
    have ht' : t < n ∨ (n ≤ t ∧ t - n < C.gates.length ∧ t - n ∉ Om) := ht
    rcases ht' with h1 | ⟨h1, hk, hkOm⟩
    · left
      show val C _ t = val (fzC C (Om ∪ Rd)) _ t
      rw [(mc_input (C := C) (D := fzC C (Om ∪ Rd)) hx hx h1).1,
        (mc_input (C := C) (D := fzC C (Om ∪ Rd)) hx hx h1).2]
    · have e : t = n + (t - n) := by omega
      by_cases hR : t - n ∈ Rd
      · left
        show val C _ t = val (fzC C (Om ∪ Rd)) _ t
        rw [e, fz_valZ C (Om ∪ Rd) _ (Finset.mem_union_right _ hR) hk _ hx]
        exact hzero _ hR u v huv
      · right
        have hnZ : t - n ∉ Om ∪ Rd := by
          intro h
          rcases Finset.mem_union.mp h with h | h
          · exact hkOm h
          · exact hR h
        have hg0 : gateAt (fzC C (Om ∪ Rd)) (t - n) = gateAt C (t - n) := by
          rw [fzC_gateAt C _ _ hk, if_neg hnZ]
        refine ⟨t - n, t - n, e, e, hk, by rw [fzC_len]; exact hk, hC.1 _ (gateAt_mem hk),
          by rw [hg0, rgate_id1], ?_⟩
        intro i hi
        have hi1 := hC.2.1 _ hk i hi
        refine ⟨hi1, hi1, ?_⟩
        by_cases hin : i < n
        · exact Or.inl hin
        · refine Or.inr ⟨by omega, by omega, fun hiOm => hR ?_⟩
          rw [hRd]
          exact ⟨hk, hkOm, i - n, hiOm, by rw [show n + (i - n) = i by omega]; exact hi⟩
  have hdo : n + o < n ∨ (n ≤ n + o ∧ n + o - n < C.gates.length ∧ n + o - n ∉ Om) :=
    Or.inr ⟨by omega, by omega, by rw [Nat.add_sub_cancel_left]; exact hoOm⟩
  have hoS : o ∉ fzS n C (Om ∪ Rd) := by
    intro h
    have h1 := ((mem_fzS n C _ o).mp h).2 (PEqualNP.EdgeOwnership.pairInput u0 v0)
    have h2 := hagree u0 v0 huv (n + o) hdo
    have h3 := congrFun hfun (PEqualNP.EdgeOwnership.pairInput u0 v0)
    rw [m29_pairF G u0 v0 huv, circuitFun_val, hout] at h3
    rw [← h2, h3] at h1
    cases h1
  obtain ⟨D, hD, hsize, hval⟩ := fz_circ n C (Om ∪ Rd) hC hZ o ho hoS hout
  refine ⟨D, hD, ?_, ?_⟩
  · funext x
    rw [hval x]
    cases hF : graphFun G ∅ x
    · cases hv : val (fzC C (Om ∪ Rd)) (List.ofFn x) (n + o)
      · rfl
      · have h1 := fz_le C (Om ∪ Rd) hC.1 hC.2.1 (List.ofFn x) (by simp) (n + o) hv
        rw [← hout, ← circuitFun_val, hfun, hF] at h1
        cases h1
    · obtain ⟨u, v, huv2, hu, hv⟩ := (m29_gF G x).mp hF
      have h2 := hagree u v huv2 (n + o) hdo
      have h3 := congrFun hfun (PEqualNP.EdgeOwnership.pairInput u v)
      rw [m29_pairF G u v huv2, circuitFun_val, hout, h2] at h3
      have h4 : circuitFun n D (PEqualNP.EdgeOwnership.pairInput u v) = true := by
        rw [hval]; exact h3
      have hle : ∀ t : Fin n, PEqualNP.EdgeOwnership.pairInput u v t = true → x t = true := by
        intro t ht
        simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq] at ht
        rcases ht with rfl | rfl
        · exact hu
        · exact hv
      have h5 := circuitFun_mono n D hD.1 _ x hle h4
      rw [hval] at h5
      exact h5
  · have h1 := Finset.card_le_card (fz_sub n C (Om ∪ Rd) hZ)
    omega

theorem m29_main {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (Om Rd : Finset ℕ)
    (cls : ℕ → Fin n) (O : Fin n → Finset ℕ)
    (hC : PEqualNP.TopForm.IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (hOm : ∀ k ∈ Om, k < C.gates.length ∧ C.output ≠ n + k)
    (hRd : ∀ X : ℕ, X ∈ Rd ↔ (X < C.gates.length ∧ X ∉ Om ∧ ∃ k ∈ Om, n + k ∈ (gateAt C X).inputs))
    (hRd2 : ∀ X ∈ Rd, (gateAt C X).op = GateOp.and ∧ PEqualNP.TopForm.BelowF G C X ∧
      ∀ u v : Fin n, G.Adj u v →
        PEqualNP.EdgeOwnership.gateVal n C X (PEqualNP.EdgeOwnership.pairInput u v) = true →
        u = cls X ∨ v = cls X)
    (hO : ∀ c : Fin n, ∀ w ∈ O c,
      (w < n ∨ (n ≤ w ∧ w - n < C.gates.length ∧ ∀ k ∈ Om, k ≠ w - n ∧
        ¬ PEqualNP.EdgeOwnership.InCone n C k (w - n))) ∧
      ∃ Z : Finset (Fin n), Z.Nonempty ∧ (∀ z ∈ Z, G.Adj c z) ∧
        ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD w false = decide (∃ z ∈ Z, x z = true))
    (hcov : ∀ X ∈ Rd, ∀ q : Fin n, G.Adj (cls X) q →
      PEqualNP.EdgeOwnership.gateVal n C X (PEqualNP.EdgeOwnership.pairInput (cls X) q) = true →
      ∃ w ∈ O (cls X), (C.wires (List.ofFn (PEqualNP.SplitCount.unitInput q))).getD w false = true)
    (o : ℕ) (ho : o < C.gates.length) (hout : C.output = n + o)
    (c0 : Fin n) (hc0 : c0 ∈ Rd.image cls) (hc0n : (O c0).Nonempty) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧
      D.size + Om.card + Rd.card ≤ C.size + ∑ c ∈ Rd.image cls, (O c).card := by
  have hRB : ReadsBack n C := hC.2.1
  have hoOm : o ∉ Om := fun h => (hOm o h).2 hout
  obtain ⟨A, hA⟩ : ∃ A : Finset ℕ, ∀ j, j ∈ A ↔
      (j < C.gates.length ∧ j ∉ Om ∧ ∀ k ∈ Om, ¬ PEqualNP.EdgeOwnership.InCone n C k j) :=
    ⟨(Finset.range C.gates.length).filter
      (fun j => j ∉ Om ∧ ∀ k ∈ Om, ¬ PEqualNP.EdgeOwnership.InCone n C k j),
      fun j => by rw [Finset.mem_filter, Finset.mem_range]⟩
  obtain ⟨B, hB⟩ : ∃ B : Finset ℕ, ∀ j, j ∈ B ↔ (j < C.gates.length ∧ j ∉ Om ∧ j ∉ Rd ∧ j ∉ A) :=
    ⟨(Finset.range C.gates.length).filter (fun j => j ∉ Om ∧ j ∉ Rd ∧ j ∉ A),
      fun j => by rw [Finset.mem_filter, Finset.mem_range]⟩
  have hAl : ∀ j ∈ A, j < C.gates.length := fun j hj => ((hA j).mp hj).1
  have hBl : ∀ j ∈ B, j < C.gates.length := fun j hj => ((hB j).mp hj).1
  have hAnRd : ∀ j ∈ A, j ∉ Rd := by
    intro j hj hjR
    obtain ⟨hjl, _, k, hk, hread⟩ := (hRd j).mp hjR
    have hk2 : n + k < n + j := hRB j hjl _ hread
    exact ((hA j).mp hj).2.2 k hk (inCone_of_read n C k j hjl (by omega) hread)
  have hAcl : ∀ j ∈ A, ∀ i ∈ (gateAt C j).inputs, i < n ∨ i - n ∈ A := by
    intro j hj i hi
    obtain ⟨hjl, _, hcone⟩ := (hA j).mp hj
    have hi1 := hRB j hjl i hi
    by_cases hin : i < n
    · exact Or.inl hin
    · right
      have hrd : n + (i - n) ∈ (gateAt C j).inputs := by
        rw [show n + (i - n) = i by omega]; exact hi
      have hkc := inCone_of_read n C (i - n) j hjl (by omega) hrd
      rw [hA]
      exact ⟨by omega, fun hm => hcone _ hm hkc,
        fun k hk hk2 => hcone k hk (inCone_trans n C k (i - n) hk2 j hkc)⟩
  have hBread : ∀ j ∈ B, ∀ i ∈ (gateAt C j).inputs, n ≤ i → i - n ∉ Om := by
    intro j hj i hi hni him
    obtain ⟨hjl, hjOm, hjRd, _⟩ := (hB j).mp hj
    apply hjRd
    rw [hRd]
    exact ⟨hjl, hjOm, i - n, him, by rw [show n + (i - n) = i by omega]; exact hi⟩
  have hOw : ∀ c : Fin n, ∀ w ∈ O c, w < n ∨ (¬ w < n ∧ w - n ∈ A) := by
    intro c w hw
    rcases (hO c w hw).1 with h | ⟨h1, h2, h3⟩
    · exact Or.inl h
    · right
      refine ⟨by omega, ?_⟩
      rw [hA]
      exact ⟨h2, fun hm => (h3 _ hm).1 rfl, fun k hk => (h3 k hk).2⟩
  -- the middle block of stars
  obtain ⟨b, hb⟩ : ∃ b, b = n + roP A C.gates.length := ⟨_, rfl⟩
  obtain ⟨psi, hpsi⟩ : ∃ psi : ℕ → ℕ, ∀ w, psi w = if w < n then w else n + roP A (w - n) :=
    ⟨_, fun w => rfl⟩
  have hpsib : ∀ w, (w < n ∨ (¬ w < n ∧ w - n ∈ A)) → psi w < b := by
    intro w hw
    rw [hpsi, hb]
    rcases hw with h | ⟨h1, h2⟩
    · rw [if_pos h]; omega
    · rw [if_neg h1]
      have := roP_lt A (w - n) _ (hAl _ h2) h2
      omega
  obtain ⟨Lf, hLf⟩ : ∃ Lf : ℕ → List ℕ, ∀ c : Fin n, Lf c.val = (O c).toList.map psi :=
    ⟨fun c => if h : c < n then (O ⟨c, h⟩).toList.map psi else [], fun c => by simp [c.isLt]⟩
  obtain ⟨cs, hcs, hsum⟩ : ∃ cs : List ℕ, (∀ d, d ∈ cs ↔ ∃ c ∈ Rd.image cls, c.val = d) ∧
      (cs.map fun c => (Lf c).length).sum = ∑ c ∈ Rd.image cls, (O c).card := by
    refine ⟨(Rd.image cls).toList.map Fin.val, fun d => ?_, ?_⟩
    · simp only [List.mem_map, Finset.mem_toList]
    · rw [List.map_map, Finset.sum_map_toList]
      apply Finset.sum_congr rfl
      intro c _
      show (Lf c.val).length = (O c).card
      rw [hLf, List.length_map, Finset.length_toList]
  obtain ⟨cen, hcen1, hcen2⟩ : ∃ cen : ℕ → ℕ, (∀ X, (O (cls X)).Nonempty → cen X = (cls X).val) ∧
      (∀ X ∈ Rd, ∃ c : Fin n, c ∈ Rd.image cls ∧ (O c).Nonempty ∧ cen X = c.val) := by
    refine ⟨fun X => if (O (cls X)).Nonempty then (cls X).val else c0.val, fun X h => ?_, fun X hX => ?_⟩
    · simp only [if_pos h]
    · by_cases h : (O (cls X)).Nonempty
      · exact ⟨cls X, Finset.mem_image_of_mem cls hX, h, by simp only [if_pos h]⟩
      · exact ⟨c0, hc0, hc0n, by simp only [if_neg h]⟩
  have hcsb : ∀ c ∈ cs, c < b := by
    intro c hc
    obtain ⟨c', _, rfl⟩ := (hcs c).mp hc
    have := c'.isLt
    omega
  have hLfb : ∀ c ∈ cs, ∀ i ∈ Lf c, i < b := by
    intro c hc i hi
    obtain ⟨c', _, rfl⟩ := (hcs c).mp hc
    rw [hLf] at hi
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hi
    exact hpsib w (hOw c' w (Finset.mem_toList.mp hw))
  have hLfne : ∀ c : Fin n, (O c).Nonempty → Lf c.val ≠ [] := by
    intro c hne h
    rw [hLf, List.map_eq_nil_iff] at h
    exact hne.toList_ne_nil h
  have hcenin : ∀ X ∈ Rd, cen X ∈ cs ∧ Lf (cen X) ≠ [] := by
    intro X hX
    obtain ⟨c, hc, hne, he⟩ := hcen2 X hX
    rw [he]
    exact ⟨(hcs _).mpr ⟨c, hc, rfl⟩, hLfne c hne⟩
  obtain ⟨mid, hmid⟩ : ∃ mid : List Gate, mid = ostars Lf cs b := ⟨_, rfl⟩
  obtain ⟨red, hred⟩ : ∃ red : ℕ → ℕ, ∀ i, red i = ostarW Lf cs b (cen (i - n)) := ⟨_, fun i => rfl⟩
  have hredb : ∀ X ∈ Rd, red (n + X) < b + mid.length := by
    intro X hX
    rw [hred, Nat.add_sub_cancel_left, hmid]
    exact (ostars_val Lf cs b (List.replicate b false) (by simp) hcsb hLfb (cen X) (hcenin X hX).1
      (hcenin X hX).2).1
  have hBrd : ∀ j ∈ B, ∀ i ∈ (gateAt C j).inputs, n ≤ i → i - n ∉ A → i - n ∉ B →
      red i < n + roOff C A mid := by
    intro j hj i hi hni hnA hnB
    have hX : i - n ∈ Rd := by
      by_contra hnR
      apply hnB
      rw [hB]
      have := hRB j (hBl j hj) i hi
      have := hBl j hj
      exact ⟨by omega, hBread j hj i hi hni, hnR, hnA⟩
    have := hredb (i - n) hX
    rw [show n + (i - n) = i by omega] at this
    unfold roOff
    omega
  have hmidrb : RBo (n + roP A C.gates.length) mid := by
    rw [hmid, ← hb]
    exact ostars_rb Lf cs b hcsb hLfb
  have hmidg : ∀ g ∈ mid, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
    intro g hg
    rw [hmid] at hg
    exact ostars_gate Lf cs b g hg
  have hDao := ro_isAO2 n C A B mid red (roMap n C A B mid red C.output) hC hAl hBl hAcl hBrd
    hmidrb hmidg
  -- size
  have hsize : (roC n C A B mid red (roMap n C A B mid red C.output)).size + Om.card + Rd.card ≤
      C.size + ∑ c ∈ Rd.image cls, (O c).card := by
    rw [ro_size n C A B mid red _ hAl hBl]
    have hml : mid.length = ∑ c ∈ Rd.image cls, (O c).card := by
      rw [hmid, ostars_len, hsum]
    have hAB : Disjoint A B := Finset.disjoint_left.mpr (fun j h1 h2 => ((hB j).mp h2).2.2.2 h1)
    have hABO : Disjoint (A ∪ B) Om := Finset.disjoint_left.mpr (fun j h1 h2 => by
      rcases Finset.mem_union.mp h1 with h | h
      · exact ((hA j).mp h).2.1 h2
      · exact ((hB j).mp h).2.1 h2)
    have hABOR : Disjoint (A ∪ B ∪ Om) Rd := Finset.disjoint_left.mpr (fun j h1 h2 => by
      rcases Finset.mem_union.mp h1 with h | h
      · rcases Finset.mem_union.mp h with h' | h'
        · exact hAnRd j h' h2
        · exact ((hB j).mp h').2.2.1 h2
      · exact ((hRd j).mp h2).2.1 h)
    have hsub : A ∪ B ∪ Om ∪ Rd ⊆ Finset.range C.gates.length := by
      intro j hj
      rw [Finset.mem_range]
      rcases Finset.mem_union.mp hj with h | h
      · rcases Finset.mem_union.mp h with h' | h'
        · rcases Finset.mem_union.mp h' with h'' | h''
          · exact hAl j h''
          · exact hBl j h''
        · exact (hOm j h').1
      · exact ((hRd j).mp h).1
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_range, Finset.card_union_of_disjoint hABOR, Finset.card_union_of_disjoint hABO,
      Finset.card_union_of_disjoint hAB] at h1
    show A.card + mid.length + B.card + Om.card + Rd.card ≤ C.gates.length + _
    omega
  -- values of the kept head part
  have hV1 : ∀ z : Fin n → Bool, ∀ w, (w < n ∨ (¬ w < n ∧ w - n ∈ A)) →
      val (roC n C A B mid red (roMap n C A B mid red C.output)) (List.ofFn z) (psi w) =
        val C (List.ofFn z) w := by
    intro z w hw
    have hx : (List.ofFn z).length = n := by simp
    obtain ⟨dA, hdA⟩ : ∃ dA : ℕ → Prop, ∀ i, dA i ↔ (i < n ∨ (¬ i < n ∧ i - n ∈ A)) :=
      ⟨_, fun i => Iff.rfl⟩
    have k1 : ∀ j ∈ A, dA (n + j) → ∀ i ∈ (gateAt C j).inputs, dA i := by
      intro j hj _ i hi
      rw [hdA]
      rcases hAcl j hj i hi with h1 | h1
      · exact Or.inl h1
      · by_cases h2 : i < n
        · exact Or.inl h2
        · exact Or.inr ⟨h2, h1⟩
    have k2 : ∀ j ∈ B, dA (n + j) → ∀ i ∈ (gateAt C j).inputs, dA i := by
      intro j hj hd
      exfalso
      rw [hdA] at hd
      rcases hd with h1 | ⟨_, h2⟩
      · omega
      · rw [Nat.add_sub_cancel_left] at h2
        exact ((hB j).mp hj).2.2.2 h2
    have k4 : ∀ i, dA i → n ≤ i → i - n ∉ A → i - n ∉ B →
        val C (List.ofFn z) i = val (roC n C A B mid red (roMap n C A B mid red C.output)) (List.ofFn z) (red i) := by
      intro i hd hni hnA _
      exfalso
      rw [hdA] at hd
      rcases hd with h1 | ⟨_, h2⟩
      · omega
      · exact hnA h2
    have h := ro_val opMono_eq n C A B mid red (roMap n C A B mid red C.output) hC.1 hRB hAl hBl hAcl hBrd
      (List.ofFn z) (List.ofFn z) hx hx dA k1 k2 (fun i _ _ => rfl) k4 w ((hdA w).mpr hw)
    have e : roMap n C A B mid red w = psi w := by
      rw [hpsi]
      rcases hw with h1 | ⟨h1, h2⟩
      · rw [roF_in h1, if_pos h1]
      · rw [roF_A h1 h2, if_neg h1]
    rw [← e]
    exact h.symm
  -- values of the stars
  have hstar : ∀ z : Fin n → Bool, ∀ c : Fin n, c ∈ Rd.image cls → (O c).Nonempty →
      (val (roC n C A B mid red (roMap n C A B mid red C.output)) (List.ofFn z) (ostarW Lf cs b c.val) = true ↔
        (z c = true ∧ ∃ w ∈ O c, val C (List.ofFn z) w = true)) := by
    intro z c hc hne
    have hx : (List.ofFn z).length = n := by simp
    have hP0 : (W (roG C A (roMap n C A B mid red) C.gates.length) (List.ofFn z)).length = b := by
      rw [W_length, roG_len, hx, hb]
    have hcs' : c.val ∈ cs := (hcs _).mpr ⟨c, hc, rfl⟩
    obtain ⟨hlt, hiff⟩ := ostars_val Lf cs b _ hP0 hcsb hLfb c.val hcs' (hLfne c hne)
    have hsplit : ∀ v, v < b + mid.length →
        val (roC n C A B mid red (roMap n C A B mid red C.output)) (List.ofFn z) v =
          (W mid (W (roG C A (roMap n C A B mid red) C.gates.length) (List.ofFn z))).getD v false := by
      intro v hv
      show (W (roGates n C A B mid red) (List.ofFn z)).getD v false = _
      unfold roGates
      rw [W_append, W_append]
      exact W_prefix _ _ _ (by rw [W_length, hP0]; exact hv)
    have hpre : ∀ v, v < b →
        (W (roG C A (roMap n C A B mid red) C.gates.length) (List.ofFn z)).getD v false =
          val (roC n C A B mid red (roMap n C A B mid red C.output)) (List.ofFn z) v := by
      intro v hv
      rw [hsplit v (by omega)]
      exact (W_prefix _ _ _ (by rw [hP0]; exact hv)).symm
    rw [← hmid] at hiff hlt
    rw [hsplit _ hlt, hiff]
    have h1 : (W (roG C A (roMap n C A B mid red) C.gates.length) (List.ofFn z)).getD c.val false = z c := by
      rw [W_prefix _ _ _ (by rw [hx]; exact c.isLt), ofFn_getD z c.val c.isLt]
    rw [h1]
    constructor
    · rintro ⟨hz, i, hi, hv⟩
      rw [hLf] at hi
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hi
      have hw' := Finset.mem_toList.mp hw
      have hwA := hOw c w hw'
      rw [hpre _ (hpsib w hwA), hV1 z w hwA] at hv
      exact ⟨hz, w, hw', hv⟩
    · rintro ⟨hz, w, hw, hv⟩
      have hwA := hOw c w hw
      refine ⟨hz, psi w, by rw [hLf]; exact List.mem_map.mpr ⟨w, Finset.mem_toList.mpr hw, rfl⟩, ?_⟩
      rw [hpre _ (hpsib w hwA), hV1 z w hwA]
      exact hv
  -- the whole domain
  obtain ⟨dm, hdm⟩ : ∃ dm : ℕ → Prop, ∀ i, dm i ↔ (i < n ∨ (n ≤ i ∧ i - n < C.gates.length ∧ i - n ∉ Om)) :=
    ⟨_, fun i => Iff.rfl⟩
  have hdA : ∀ j ∈ A, dm (n + j) → ∀ i ∈ (gateAt C j).inputs, dm i := by
    intro j hj _ i hi
    rw [hdm]
    rcases hAcl j hj i hi with h1 | h1
    · exact Or.inl h1
    · by_cases h2 : i < n
      · exact Or.inl h2
      · obtain ⟨h3, h4, _⟩ := (hA _).mp h1
        exact Or.inr ⟨by omega, h3, h4⟩
  have hdB : ∀ j ∈ B, dm (n + j) → ∀ i ∈ (gateAt C j).inputs, dm i := by
    intro j hj _ i hi
    rw [hdm]
    have hi1 := hRB j (hBl j hj) i hi
    have hjl := hBl j hj
    by_cases h2 : i < n
    · exact Or.inl h2
    · exact Or.inr ⟨by omega, by omega, hBread j hj i hi (by omega)⟩
  have hdRd : ∀ i, dm i → n ≤ i → i - n ∉ A → i - n ∉ B → i - n ∈ Rd := by
    intro i hd hni hnA hnB
    rw [hdm] at hd
    rcases hd with h1 | ⟨_, h2, h3⟩
    · omega
    · by_contra hnR
      exact hnB ((hB _).mpr ⟨h2, h3, hnR, hnA⟩)
  have hdout : dm C.output := by
    rw [hdm, hout]
    exact Or.inr ⟨by omega, by omega, by rw [Nat.add_sub_cancel_left]; exact hoOm⟩
  have hlow : ∀ z : Fin n → Bool, graphFun G ∅ z = false →
      circuitFun n (roC n C A B mid red (roMap n C A B mid red C.output)) z = false := by
    intro z hF
    have hx : (List.ofFn z).length = n := by simp
    have hredv : ∀ i, dm i → n ≤ i → i - n ∉ A → i - n ∉ B →
        (val (roC n C A B mid red (roMap n C A B mid red C.output)) (List.ofFn z) (red i) = true →
          val C (List.ofFn z) i = true) := by
      intro i hd hni hnA hnB hv
      exfalso
      have hX := hdRd i hd hni hnA hnB
      obtain ⟨c, hc, hne, he⟩ := hcen2 _ hX
      rw [hred, he] at hv
      obtain ⟨hz, w, hw, hvw⟩ := (hstar z c hc hne).mp hv
      obtain ⟨_, Zs, _, hadj, hval⟩ := hO c w hw
      have h2 : val C (List.ofFn z) w = decide (∃ z' ∈ Zs, z z' = true) := hval z
      rw [hvw] at h2
      obtain ⟨z', hz'Z, hzz⟩ := of_decide_eq_true h2.symm
      have hF2 := (m29_gF G z).mpr ⟨c, z', hadj z' hz'Z, hz, hzz⟩
      rw [hF] at hF2
      cases hF2
    have h := ro_val opMono_rimp n C A B mid red (roMap n C A B mid red C.output) hC.1 hRB hAl hBl hAcl
      hBrd (List.ofFn z) (List.ofFn z) hx hx dm hdA hdB (fun i _ _ h => h) hredv C.output hdout
    cases hD : circuitFun n (roC n C A B mid red (roMap n C A B mid red C.output)) z
    · rfl
    · exfalso
      have h1 : val C (List.ofFn z) C.output = true := h hD
      rw [← circuitFun_val, hfun, hF] at h1
      cases h1
  have hhigh : ∀ u v : Fin n, G.Adj u v →
      circuitFun n (roC n C A B mid red (roMap n C A B mid red C.output))
        (PEqualNP.EdgeOwnership.pairInput u v) = true := by
    intro u v huv
    have hx : (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v)).length = n := by simp
    have hredv : ∀ i, dm i → n ≤ i → i - n ∉ A → i - n ∉ B →
        (val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v)) i = true →
          val (roC n C A B mid red (roMap n C A B mid red C.output))
            (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v)) (red i) = true) := by
      intro i hd hni hnA hnB hv
      have hX := hdRd i hd hni hnA hnB
      have hgv : PEqualNP.EdgeOwnership.gateVal n C (i - n) (PEqualNP.EdgeOwnership.pairInput u v) = true := by
        show val C _ (n + (i - n)) = true
        rw [show n + (i - n) = i by omega]
        exact hv
      obtain ⟨q, hq, hgq, hpq, hpc⟩ : ∃ q : Fin n, G.Adj (cls (i - n)) q ∧
          PEqualNP.EdgeOwnership.gateVal n C (i - n) (PEqualNP.EdgeOwnership.pairInput (cls (i - n)) q) = true ∧
          PEqualNP.EdgeOwnership.pairInput u v q = true ∧
          PEqualNP.EdgeOwnership.pairInput u v (cls (i - n)) = true := by
        rcases (hRd2 _ hX).2.2 u v huv hgv with hu | hv2
        · rw [← hu]
          exact ⟨v, huv, hgv, m29_pair_v u v, m29_pair_u u v⟩
        · rw [← hv2]
          refine ⟨u, huv.symm, ?_, m29_pair_u u v, m29_pair_v u v⟩
          rw [m29_pair_comm]
          exact hgv
      obtain ⟨w, hw, hwv⟩ := hcov _ hX q hq hgq
      have hne : (O (cls (i - n))).Nonempty := ⟨w, hw⟩
      rw [hred, hcen1 _ hne]
      apply (hstar _ (cls (i - n)) (Finset.mem_image_of_mem cls hX) hne).mpr
      refine ⟨hpc, w, hw, ?_⟩
      have hle : ∀ t : Fin n, PEqualNP.SplitCount.unitInput q t = true →
          PEqualNP.EdgeOwnership.pairInput u v t = true := by
        intro t ht
        simp only [PEqualNP.SplitCount.unitInput, decide_eq_true_eq] at ht
        rw [ht]
        exact hpq
      exact mono n C hC.1 _ _ hle w hwv
    have h := ro_val opMono_imp n C A B mid red (roMap n C A B mid red C.output) hC.1 hRB hAl hBl hAcl
      hBrd _ _ hx hx dm hdA hdB (fun i _ _ h => h) hredv C.output hdout
    have h1 : val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v)) C.output = true := by
      rw [← circuitFun_val, hfun]
      exact m29_pairF G u v huv
    exact h h1
  refine ⟨roC n C A B mid red (roMap n C A B mid red C.output), hDao, ?_, hsize⟩
  funext z
  cases hF : graphFun G ∅ z
  · exact hlow z hF
  · obtain ⟨u, v, huv, hu, hv⟩ := (m29_gF G z).mp hF
    have hle : ∀ t : Fin n, PEqualNP.EdgeOwnership.pairInput u v t = true → z t = true := by
      intro t ht
      simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq] at ht
      rcases ht with rfl | rfl
      · exact hu
      · exact hv
    exact circuitFun_mono n _ hDao.1 _ z hle (hhigh u v huv)

theorem main_aux : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit)
    (Om Rd : Finset ℕ) (cls : ℕ → Fin n) (O : Fin n → Finset ℕ),
  PEqualNP.TopForm.IsAO2 n C →
  PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
  (∀ k ∈ Om, k < C.gates.length ∧ C.output ≠ n + k) →
  (∀ X : ℕ, X ∈ Rd ↔ (X < C.gates.length ∧ X ∉ Om ∧
      ∃ k ∈ Om, n + k ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C X).inputs)) →
  (∀ X ∈ Rd, (PEqualNP.MetaComplexity.NestedCover.gateAt C X).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
      PEqualNP.TopForm.BelowF G C X ∧
      ∀ u v : Fin n, G.Adj u v → PEqualNP.EdgeOwnership.gateVal n C X (PEqualNP.EdgeOwnership.pairInput u v) = true →
        u = cls X ∨ v = cls X) →
  (∀ c : Fin n, ∀ w ∈ O c,
      (w < n ∨ (n ≤ w ∧ w - n < C.gates.length ∧ ∀ k ∈ Om, k ≠ w - n ∧ ¬ PEqualNP.EdgeOwnership.InCone n C k (w - n))) ∧
      ∃ Z : Finset (Fin n), Z.Nonempty ∧ (∀ z ∈ Z, G.Adj c z) ∧
        ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD w false = decide (∃ z ∈ Z, x z = true)) →
  (∀ X ∈ Rd, ∀ q : Fin n, G.Adj (cls X) q →
      PEqualNP.EdgeOwnership.gateVal n C X (PEqualNP.EdgeOwnership.pairInput (cls X) q) = true →
      ∃ w ∈ O (cls X), (C.wires (List.ofFn (PEqualNP.SplitCount.unitInput q))).getD w false = true) →
  ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n D ∧
    PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
    D.size + Om.card + Rd.card ≤ C.size + ∑ c ∈ Rd.image cls, (O c).card := by
  intro n G hG C Om Rd cls O hC hfun hOm hRd hRd2 hO hcov
  by_cases hE : ∃ u v : Fin n, G.Adj u v
  · obtain ⟨u0, v0, huv⟩ := hE
    obtain ⟨h1, h2⟩ := m29_out G C hfun u0 v0 huv
    have hout : C.output = n + (C.output - n) := by omega
    have ho : C.output - n < C.gates.length := by omega
    by_cases hS : ∃ c ∈ Rd.image cls, (O c).Nonempty
    · obtain ⟨c0, hc0, hc0n⟩ := hS
      exact m29_main G C Om Rd cls O hC hfun hOm hRd hRd2 hO hcov _ ho hout c0 hc0 hc0n
    · have hS' : ∀ c ∈ Rd.image cls, ¬ (O c).Nonempty := fun c hc hn => hS ⟨c, hc, hn⟩
      have hzero : ∀ X ∈ Rd, ∀ u v : Fin n, G.Adj u v →
          PEqualNP.EdgeOwnership.gateVal n C X (PEqualNP.EdgeOwnership.pairInput u v) = false := by
        intro X hX u v huv2
        cases hg : PEqualNP.EdgeOwnership.gateVal n C X (PEqualNP.EdgeOwnership.pairInput u v)
        · rfl
        · exfalso
          have hne : ¬ (O (cls X)).Nonempty := hS' (cls X) (Finset.mem_image_of_mem cls hX)
          rcases (hRd2 X hX).2.2 u v huv2 hg with hu | hv
          · subst hu
            obtain ⟨w, hw, _⟩ := hcov X hX v huv2 hg
            exact hne ⟨w, hw⟩
          · subst hv
            rw [m29_pair_comm] at hg
            obtain ⟨w, hw, _⟩ := hcov X hX u huv2.symm hg
            exact hne ⟨w, hw⟩
      obtain ⟨D, hD, hDf, hDs⟩ := m29_noStar G C Om Rd hC hfun hOm hRd hzero u0 v0 huv _ ho hout
      exact ⟨D, hD, hDf, by omega⟩
  · refine ⟨⟨[], n⟩, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · intro g hg
      simp at hg
    · intro j hj
      simp at hj
    · intro g hg
      simp at hg
    · funext x
      have hF : graphFun G ∅ x = false := by
        cases h : graphFun G ∅ x
        · rfl
        · obtain ⟨u, v, huv, _, _⟩ := (m29_gF G x).mp h
          exact (hE ⟨u, v, huv⟩).elim
      rw [hF]
      show (List.ofFn x).getD n false = false
      exact ofFn_getD_ge x n le_rfl
    · have := m29_card n C Om Rd hOm hRd
      show 0 + Om.card + Rd.card ≤ C.gates.length + _
      omega

end PEqualNP.Outside.L_meta_4632

theorem PEqualNP.Outside.L_meta_4632 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit)
    (Om Rd : Finset ℕ) (cls : ℕ → Fin n) (O : Fin n → Finset ℕ),
  PEqualNP.TopForm.IsAO2 n C →
  PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
  (∀ k ∈ Om, k < C.gates.length ∧ C.output ≠ n + k) →
  (∀ X : ℕ, X ∈ Rd ↔ (X < C.gates.length ∧ X ∉ Om ∧
      ∃ k ∈ Om, n + k ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C X).inputs)) →
  (∀ X ∈ Rd, (PEqualNP.MetaComplexity.NestedCover.gateAt C X).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
      PEqualNP.TopForm.BelowF G C X ∧
      ∀ u v : Fin n, G.Adj u v → PEqualNP.EdgeOwnership.gateVal n C X (PEqualNP.EdgeOwnership.pairInput u v) = true →
        u = cls X ∨ v = cls X) →
  (∀ c : Fin n, ∀ w ∈ O c,
      (w < n ∨ (n ≤ w ∧ w - n < C.gates.length ∧ ∀ k ∈ Om, k ≠ w - n ∧ ¬ PEqualNP.EdgeOwnership.InCone n C k (w - n))) ∧
      ∃ Z : Finset (Fin n), Z.Nonempty ∧ (∀ z ∈ Z, G.Adj c z) ∧
        ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD w false = decide (∃ z ∈ Z, x z = true)) →
  (∀ X ∈ Rd, ∀ q : Fin n, G.Adj (cls X) q →
      PEqualNP.EdgeOwnership.gateVal n C X (PEqualNP.EdgeOwnership.pairInput (cls X) q) = true →
      ∃ w ∈ O (cls X), (C.wires (List.ofFn (PEqualNP.SplitCount.unitInput q))).getD w false = true) →
  ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n D ∧
    PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
    D.size + Om.card + Rd.card ≤ C.size + ∑ c ∈ Rd.image cls, (O c).card :=
  PEqualNP.Outside.L_meta_4632.main_aux
