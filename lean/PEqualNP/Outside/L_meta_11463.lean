import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_11463

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

-- autoshapes prelude (pass 2 of autosolve.py): helper lemmas for the shape candidates.
-- Needs fragments fold mono flow. All names start with as_.

theorem as_imp_of_le (a b : Bool) (h : a ≤ b) : a = true → b = true := by
  revert h
  cases a <;> cases b <;> decide

theorem as_le_of_imp (a b : Bool) (h : a = true → b = true) : a ≤ b := by
  revert h
  cases a <;> cases b <;> decide

def as_sig (n : ℕ) (σ : Fin n → Fin n) (i : ℕ) : ℕ := if h : i < n then (σ ⟨i, h⟩).val else i

theorem as_gd_app_lt (a b : List Bool) (i : ℕ) (h : i < a.length) :
    (a ++ b).getD i false = a.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem as_gd_app_ge (a b : List Bool) (i : ℕ) (h : a.length ≤ i) :
    (a ++ b).getD i false = b.getD (i - a.length) false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem as_sig_ge (n : ℕ) (σ : Fin n → Fin n) (i : ℕ) (h : n ≤ i) : as_sig n σ i = i := by
  unfold as_sig
  rw [dif_neg (by omega)]

theorem as_sig_lt (n : ℕ) (σ : Fin n → Fin n) (i : ℕ) (h : i < n) : as_sig n σ i < n := by
  unfold as_sig
  rw [dif_pos h]
  exact (σ ⟨i, h⟩).isLt

theorem as_perm_eval (n : ℕ) (σ : Fin n → Fin n) (C : Circuit) (x : Fin n → Bool) (rest : List Bool) :
    Circuit.eval ⟨C.gates.map (rgate (as_sig n σ)), as_sig n σ C.output⟩ (List.ofFn x ++ rest) =
      C.eval (List.ofFn (fun i => x (σ i)) ++ rest) := by
  apply flow_rename_eval C (as_sig n σ) n (as_sig_ge n σ) (as_sig_lt n σ)
  · simp
  · simp
  · intro i hi
    by_cases h : i < n
    · have hs : as_sig n σ i = (σ ⟨i, h⟩).val := by
        unfold as_sig
        rw [dif_pos h]
      rw [hs, as_gd_app_lt (List.ofFn (fun i => x (σ i))) rest i (by rw [List.length_ofFn]; exact h),
        as_gd_app_lt (List.ofFn x) rest _ (by rw [List.length_ofFn]; exact (σ ⟨i, h⟩).isLt),
        ofFn_getD _ _ h, ofFn_getD _ _ (σ ⟨i, h⟩).isLt]
    · rw [as_sig_ge n σ i (by omega),
        as_gd_app_ge (List.ofFn (fun i => x (σ i))) rest i (by rw [List.length_ofFn]; omega),
        as_gd_app_ge (List.ofFn x) rest i (by rw [List.length_ofFn]; omega)]
      simp

theorem as_perm_eval0 (n : ℕ) (σ : Fin n → Fin n) (C : Circuit) (x : Fin n → Bool) :
    Circuit.eval ⟨C.gates.map (rgate (as_sig n σ)), as_sig n σ C.output⟩ (List.ofFn x) =
      C.eval (List.ofFn (fun i => x (σ i))) := by
  have h := as_perm_eval n σ C x []
  rw [List.append_nil, List.append_nil] at h
  exact h

theorem as_gateAt_map (C : Circuit) (f : ℕ → ℕ) (o : ℕ) (j : ℕ) (hj : j < C.gates.length) :
    gateAt ⟨C.gates.map (rgate f), o⟩ j = rgate f (gateAt C j) := by
  unfold gateAt
  simp [List.getD_eq_getElem?_getD, hj]

theorem as_perm_rb (n : ℕ) (σ : Fin n → Fin n) (C : Circuit) (o : ℕ) (hR : ReadsBack n C) :
    ReadsBack n ⟨C.gates.map (rgate (as_sig n σ)), o⟩ := by
  intro j hj i hi
  have hj' : j < C.gates.length := by simpa using hj
  rw [as_gateAt_map C _ _ j hj'] at hi
  obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hi
  have h0 := hR j hj' i0 hi0
  by_cases h : i0 < n
  · have := as_sig_lt n σ i0 h
    omega
  · rw [as_sig_ge n σ i0 (by omega)]
    exact h0

theorem as_perm_fanin (n : ℕ) (C : Circuit) (σ : Fin n → Fin n) (h : FanInTwo C) :
    ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧ ∀ (x : Fin n → Bool) (rest : List Bool),
      D.eval (List.ofFn x ++ rest) = C.eval (List.ofFn (x ∘ σ) ++ rest) := by
  refine ⟨⟨C.gates.map (rgate (as_sig n σ)), as_sig n σ C.output⟩, ?_, by simp [Circuit.size], ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    exact ⟨(h g0 hg0).1, by rw [rgate_len]; exact (h g0 hg0).2⟩
  · intro x rest
    exact as_perm_eval n σ C x rest

theorem as_perm_fanin0 (n : ℕ) (C : Circuit) (σ : Fin n → Fin n) (h : FanInTwo C) :
    ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧ ∀ (x : Fin n → Bool),
      D.eval (List.ofFn x) = C.eval (List.ofFn (x ∘ σ)) := by
  obtain ⟨D, h1, h2, h3⟩ := as_perm_fanin n C σ h
  refine ⟨D, h1, h2, fun x => ?_⟩
  have := h3 x []
  rw [List.append_nil, List.append_nil] at this
  exact this

theorem as_perm_mono2 (n : ℕ) (C : Circuit) (σ : Fin n → Fin n) (h : Monotone2 C) :
    ∃ D : Circuit, Monotone2 D ∧ D.size = C.size ∧ ∀ (x : Fin n → Bool) (rest : List Bool),
      D.eval (List.ofFn x ++ rest) = C.eval (List.ofFn (x ∘ σ) ++ rest) := by
  refine ⟨⟨C.gates.map (rgate (as_sig n σ)), as_sig n σ C.output⟩, ?_, by simp [Circuit.size], ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    exact ⟨(h g0 hg0).1, by rw [rgate_len]; exact (h g0 hg0).2⟩
  · intro x rest
    exact as_perm_eval n σ C x rest

theorem as_perm_mono20 (n : ℕ) (C : Circuit) (σ : Fin n → Fin n) (h : Monotone2 C) :
    ∃ D : Circuit, Monotone2 D ∧ D.size = C.size ∧ ∀ (x : Fin n → Bool),
      D.eval (List.ofFn x) = C.eval (List.ofFn (x ∘ σ)) := by
  obtain ⟨D, h1, h2, h3⟩ := as_perm_mono2 n C σ h
  refine ⟨D, h1, h2, fun x => ?_⟩
  have := h3 x []
  rw [List.append_nil, List.append_nil] at this
  exact this

theorem as_perm_ao2 (n : ℕ) (C : Circuit) (σ : Fin n → Fin n) (h : PEqualNP.TopForm.IsAO2 n C) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size = C.size ∧ ∀ (x : Fin n → Bool) (rest : List Bool),
      D.eval (List.ofFn x ++ rest) = C.eval (List.ofFn (x ∘ σ) ++ rest) := by
  obtain ⟨hA, hR, hL⟩ := h
  refine ⟨⟨C.gates.map (rgate (as_sig n σ)), as_sig n σ C.output⟩, ⟨?_, as_perm_rb n σ C _ hR, ?_⟩,
    by simp [Circuit.size], ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    exact hA g0 hg0
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    rw [rgate_len]
    exact hL g0 hg0
  · intro x rest
    exact as_perm_eval n σ C x rest

theorem as_perm_ao20 (n : ℕ) (C : Circuit) (σ : Fin n → Fin n) (h : PEqualNP.TopForm.IsAO2 n C) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size = C.size ∧ ∀ (x : Fin n → Bool),
      D.eval (List.ofFn x) = C.eval (List.ofFn (x ∘ σ)) := by
  obtain ⟨D, h1, h2, h3⟩ := as_perm_ao2 n C σ h
  refine ⟨D, h1, h2, fun x => ?_⟩
  have := h3 x []
  rw [List.append_nil, List.append_nil] at this
  exact this

set_option maxHeartbeats 400000 in
theorem main_aux : ∀ (x1 : Fin (7 : ℕ) → Bool), ∃ x2 ∈ [(127 : ℕ), (244 : ℕ), (480 : ℕ), (720 : ℕ), (1188 : ℕ), (3008 : ℕ), (16256 : ℕ)], ∃ (x3 : Fin (7 : ℕ)), (∀ (x4 : Fin (7 : ℕ)), x1 x4 = Bool.true → x2.testBit ↑(x4 + x3) = Bool.true) ∧ ∀ (x4 : Fin (7 : ℕ)), x1 x4 = Bool.false → x1 (x4 + (1 : Fin (7 : ℕ))) = Bool.false → x1 (x4 + (3 : Fin (7 : ℕ))) = Bool.false → x2.testBit ((7 : ℕ) + ↑(x4 + x3)) = Bool.true :=
  by
  decide +kernel

end PEqualNP.Outside.L_meta_11463

theorem PEqualNP.Outside.L_meta_11463 : ∀ (x1 : Fin (7 : ℕ) → Bool), ∃ x2 ∈ [(127 : ℕ), (244 : ℕ), (480 : ℕ), (720 : ℕ), (1188 : ℕ), (3008 : ℕ), (16256 : ℕ)], ∃ (x3 : Fin (7 : ℕ)), (∀ (x4 : Fin (7 : ℕ)), x1 x4 = Bool.true → x2.testBit ↑(x4 + x3) = Bool.true) ∧ ∀ (x4 : Fin (7 : ℕ)), x1 x4 = Bool.false → x1 (x4 + (1 : Fin (7 : ℕ))) = Bool.false → x1 (x4 + (3 : Fin (7 : ℕ))) = Bool.false → x2.testBit ((7 : ℕ) + ↑(x4 + x3)) = Bool.true :=
  PEqualNP.Outside.L_meta_11463.main_aux
