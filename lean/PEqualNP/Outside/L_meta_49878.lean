import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_49878

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

-- FRAGMENT gensize    DEPENDS: fold mono table1a
-- Lower bounds for HasCircuitSize n f (AND, OR, NOT of fan-in at most 2, every gate counted) by a profile search.
-- Profiles over a list ms of input masks (input k is gs_inp n (ms.getD k 0), wire i reads bit i of the mask);
-- m = ms.length, profile = t1_bits of the wire values (fragment table1a).  Two searches:
--   M (no NOT gate at all): AND / OR of two profiles, base gs_base = 0, full, the inputs; k - 1 steps;
--   A (some NOT gate, so at most len - 1 AND/OR gates): profiles taken modulo complement (gs_nz), steps
--     gs_opsA = the four AND-type gates x AND y, x AND not y, not x AND y, not x AND not y; NOT gates are free; k - 2 steps.
-- Search gs_srch ops leaf ext T r l S: fresh profiles only, canonical order (a new profile is larger than the
-- previous one l unless it reads l), last step by the leaf test (t1_one for M, gs_leafA for A), and two steps
-- before the end the new profile must give T with one more operand (ext: gs_extM / gs_extA).
-- Exports:
--   def gs_full m := t1_bits (fun _ => true) m ;  gs_bits_not : t1_bits (not f) m = gs_full m xor t1_bits f m
--   def gs_nz m p (if bit 0 then complement) ;  gs_nz_compl (1 <= m) : gs_nz m (gs_full m xor p) = gs_nz m p
--   def gs_opsM a b := [a land b, a lor b] ;  def gs_opsA m a b (4 normalized AND-type results)
--   gs_A_and : gs_nz m (a land b) in gs_opsA m (gs_nz m a) (gs_nz m b) ;  gs_A_or (bits operands) the same for lor
--   def gs_Step ops S p ;  def gs_G ops T r S (reach within r steps) ;  gs_G_sub, gs_G_succ, gs_G_le
--   gs_chain : stutter-or-step chains give gs_G len, and gs_G (len - 1) when some step stutters
--   def gs_Bld ops S L ;  gs_Bld_mono, gs_Bld_erase ;  gs_G_Bld ;  gs_min
--   def gs_cand, gs_cand2, gs_srch ops leaf ext T r l S ;  gs_pick ;  gs_srch_sound (completeness of the pruned search w.r.t. gs_Bld lists)
--   def gs_extM, gs_preA, gs_extA (two steps before the end: the new profile must reach T in one more step) ;  gs_extM_sound, gs_extA_sound
--   def gs_inp, gs_prof, gs_xs, gs_base, gs_St ;  gs_St_prof ;  gs_gate_fg, gs_gate_not
--   gs_lower n f ms k T TA RM RA (hm : 1 <= ms.length) (hT : t1_bits (fun j => f (fun i => (ms.getD j 0).testBit i)) m = T)
--     (hTA : gs_nz m T = TA) (hBM : every x in gs_base n ms is in 0 :: RM) (hBA : the same for (gs_base n ms).map (gs_nz m) and 0 :: RA)
--     (hM : gs_srch gs_opsM (t1_one T) (gs_extM T) T (k - 1) 0 (0 :: RM) = false)
--     (hA : gs_srch (gs_opsA m) (gs_leafA m TA) (gs_extA m TA) TA (k - 2) 0 (0 :: RA) = false) : forall t, HasCircuitSize n f t -> k <= t
-- Use: SP/tools/gensize_lb.py N writes whole files (every hypothesis by decide +kernel).

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def gs_full (m : ℕ) : ℕ := t1_bits (fun _ => true) m

theorem gs_bits_not (f : ℕ → Bool) (m : ℕ) :
    t1_bits (fun k => ! f k) m = gs_full m ^^^ t1_bits f m := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor, t1_bits_testBit, gs_full]
  cases decide (i < m) <;> cases f i <;> rfl

theorem gs_xor_xor (a b : ℕ) : a ^^^ (a ^^^ b) = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> rfl

def gs_nz (m p : ℕ) : ℕ := if p.testBit 0 then gs_full m ^^^ p else p

theorem gs_full_bit0 (m : ℕ) (hm : 1 ≤ m) : (gs_full m).testBit 0 = true := by
  unfold gs_full
  rw [t1_bits_testBit]
  simp only [Bool.and_true, decide_eq_true_eq]
  omega

theorem gs_nz_compl (m p : ℕ) (hm : 1 ≤ m) : gs_nz m (gs_full m ^^^ p) = gs_nz m p := by
  unfold gs_nz
  rw [Nat.testBit_xor, gs_full_bit0 m hm]
  cases hp : p.testBit 0 <;> simp [gs_xor_xor]

theorem gs_nz_cases (m p : ℕ) : p = gs_nz m p ∨ p = gs_full m ^^^ gs_nz m p := by
  unfold gs_nz
  split
  · right
    exact (gs_xor_xor _ _).symm
  · left
    rfl

theorem gs_nz_eq (m z T : ℕ) (h : gs_nz m z = T) : z = T ∨ z = gs_full m ^^^ T := by
  unfold gs_nz at h
  split at h
  · right
    rw [← h, gs_xor_xor]
  · left
    exact h

def gs_opsM (a b : ℕ) : List ℕ := [a &&& b, a ||| b]

def gs_opsA (m a b : ℕ) : List ℕ :=
  [gs_nz m (a &&& b), gs_nz m (a &&& (gs_full m ^^^ b)), gs_nz m ((gs_full m ^^^ a) &&& b),
    gs_nz m ((gs_full m ^^^ a) &&& (gs_full m ^^^ b))]

theorem gs_A_and (m a b : ℕ) : gs_nz m (a &&& b) ∈ gs_opsA m (gs_nz m a) (gs_nz m b) := by
  generalize ea : gs_nz m a = a'
  generalize eb : gs_nz m b = b'
  have ha := gs_nz_cases m a
  have hb := gs_nz_cases m b
  rw [ea] at ha
  rw [eb] at hb
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> subst ha <;> subst hb <;> simp [gs_opsA]

theorem gs_or_dm (m : ℕ) (f g : ℕ → Bool) :
    t1_bits f m ||| t1_bits g m =
      gs_full m ^^^ ((gs_full m ^^^ t1_bits f m) &&& (gs_full m ^^^ t1_bits g m)) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor, Nat.testBit_lor, Nat.testBit_land, t1_bits_testBit, gs_full]
  cases decide (i < m) <;> cases f i <;> cases g i <;> rfl

theorem gs_A_or (m : ℕ) (hm : 1 ≤ m) (f g : ℕ → Bool) :
    gs_nz m (t1_bits f m ||| t1_bits g m) ∈
      gs_opsA m (gs_nz m (t1_bits f m)) (gs_nz m (t1_bits g m)) := by
  rw [gs_or_dm, gs_nz_compl m _ hm]
  have hx := gs_A_and m (gs_full m ^^^ t1_bits f m) (gs_full m ^^^ t1_bits g m)
  rw [gs_nz_compl m _ hm, gs_nz_compl m _ hm] at hx
  exact hx

def gs_Step (ops : ℕ → ℕ → List ℕ) (S : List ℕ) (p : ℕ) : Prop := ∃ a ∈ S, ∃ b ∈ S, p ∈ ops a b

theorem gs_Step_mono (ops : ℕ → ℕ → List ℕ) {S S2 : List ℕ} (hs : ∀ x ∈ S, x ∈ S2) {p : ℕ}
    (h : gs_Step ops S p) : gs_Step ops S2 p := by
  obtain ⟨a, ha, b, hb, hp⟩ := h
  exact ⟨a, hs a ha, b, hs b hb, hp⟩

def gs_G (ops : ℕ → ℕ → List ℕ) (T : ℕ) : ℕ → List ℕ → Prop
  | 0, S => T ∈ S
  | r + 1, S => T ∈ S ∨ ∃ p, gs_Step ops S p ∧ gs_G ops T r (p :: S)

theorem gs_G_sub (ops : ℕ → ℕ → List ℕ) (T r : ℕ) :
    ∀ S S2 : List ℕ, (∀ x ∈ S, x ∈ S2) → gs_G ops T r S → gs_G ops T r S2 := by
  induction r with
  | zero => intro S S2 hs h; exact hs _ h
  | succ r ih =>
    intro S S2 hs h
    rcases h with h | ⟨p, hp, hg⟩
    · exact Or.inl (hs _ h)
    · refine Or.inr ⟨p, gs_Step_mono ops hs hp, ih (p :: S) (p :: S2) ?_ hg⟩
      intro x hx
      rcases List.mem_cons.mp hx with e | e
      · exact List.mem_cons.mpr (Or.inl e)
      · exact List.mem_cons_of_mem _ (hs _ e)

theorem gs_G_succ (ops : ℕ → ℕ → List ℕ) (T r : ℕ) :
    ∀ S : List ℕ, gs_G ops T r S → gs_G ops T (r + 1) S := by
  induction r with
  | zero => intro S h; exact Or.inl h
  | succ r ih =>
    intro S h
    rcases h with h | ⟨p, hp, hg⟩
    · exact Or.inl h
    · exact Or.inr ⟨p, hp, ih _ hg⟩

theorem gs_G_le (ops : ℕ → ℕ → List ℕ) (T r : ℕ) (S : List ℕ) (h : gs_G ops T r S) :
    ∀ d, gs_G ops T (r + d) S := by
  intro d
  induction d with
  | zero => exact h
  | succ d ih => exact gs_G_succ ops T (r + d) S ih

theorem gs_chain (ops : ℕ → ℕ → List ℕ) (T : ℕ) (St : ℕ → List ℕ) (P : ℕ → ℕ) (len : ℕ)
    (hst : ∀ j, j < len → St (j + 1) = P j :: St j ∧ (P j ∈ St j ∨ gs_Step ops (St j) (P j)))
    (hT : T ∈ St len) :
    ∀ d j, j + d = len → gs_G ops T d (St j) ∧
      ((∃ i, j ≤ i ∧ i < len ∧ P i ∈ St i) → gs_G ops T (d - 1) (St j)) := by
  intro d
  induction d with
  | zero =>
    intro j hj
    have e : j = len := by omega
    subst e
    refine ⟨hT, ?_⟩
    rintro ⟨i, h1, h2, _⟩
    omega
  | succ d ih =>
    intro j hj
    obtain ⟨hs, hcase⟩ := hst j (by omega)
    obtain ⟨h1, h2⟩ := ih (j + 1) (by omega)
    rw [hs] at h1 h2
    have hsub : P j ∈ St j → gs_G ops T d (St j) := by
      intro hm
      apply gs_G_sub ops T d (P j :: St j) (St j) _ h1
      intro x hx
      rcases List.mem_cons.mp hx with e | e
      · rw [e]; exact hm
      · exact e
    rw [Nat.add_sub_cancel]
    rcases hcase with hm | hstep
    · exact ⟨gs_G_succ ops T d _ (hsub hm), fun _ => hsub hm⟩
    · refine ⟨Or.inr ⟨P j, hstep, h1⟩, ?_⟩
      rintro ⟨i, hi1, hi2, hi3⟩
      by_cases hij : i = j
      · subst hij
        exact hsub hi3
      · obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
        have h3 := h2 ⟨i, by omega, hi2, hi3⟩
        rw [Nat.add_sub_cancel] at h3
        exact Or.inr ⟨P j, hstep, h3⟩

def gs_Bld (ops : ℕ → ℕ → List ℕ) : List ℕ → List ℕ → Prop
  | _, [] => True
  | S, p :: L => gs_Step ops S p ∧ gs_Bld ops (p :: S) L

theorem gs_Bld_nil (ops : ℕ → ℕ → List ℕ) (S : List ℕ) : gs_Bld ops S [] := True.intro

theorem gs_Bld_cons (ops : ℕ → ℕ → List ℕ) (S : List ℕ) (p : ℕ) (L : List ℕ) :
    gs_Bld ops S (p :: L) ↔ gs_Step ops S p ∧ gs_Bld ops (p :: S) L := Iff.rfl

theorem gs_Bld_mono (ops : ℕ → ℕ → List ℕ) (L : List ℕ) :
    ∀ S S2 : List ℕ, (∀ x ∈ S, x ∈ S2) → gs_Bld ops S L → gs_Bld ops S2 L := by
  induction L with
  | nil => intro S S2 _ _; exact gs_Bld_nil ops S2
  | cons p L ih =>
    intro S S2 hs h
    obtain ⟨h1, h2⟩ := (gs_Bld_cons ops S p L).mp h
    refine (gs_Bld_cons ops S2 p L).mpr ⟨gs_Step_mono ops hs h1, ih (p :: S) (p :: S2) ?_ h2⟩
    intro x hx
    rcases List.mem_cons.mp hx with e | e
    · exact List.mem_cons.mpr (Or.inl e)
    · exact List.mem_cons_of_mem _ (hs _ e)

theorem gs_Bld_erase (ops : ℕ → ℕ → List ℕ) (q : ℕ) (L : List ℕ) :
    ∀ S : List ℕ, gs_Bld ops S L → q ∈ L → gs_Step ops S q → gs_Bld ops (q :: S) (L.erase q) := by
  induction L with
  | nil => intro S _ hq _; simp at hq
  | cons p L ih =>
    intro S h hq hs
    obtain ⟨hh1, hh2⟩ := (gs_Bld_cons ops S p L).mp h
    by_cases hpq : p = q
    · subst hpq
      have e : (p :: L).erase p = L := by simp
      rw [e]
      exact hh2
    · have e : (p :: L).erase q = p :: L.erase q := by simp [List.erase_cons, hpq]
      rw [e]
      have hqL : q ∈ L := by
        rcases List.mem_cons.mp hq with e2 | e2
        · exact absurd e2.symm hpq
        · exact e2
      have hsub : ∀ x ∈ S, x ∈ q :: S := fun x hx => List.mem_cons_of_mem _ hx
      refine (gs_Bld_cons ops (q :: S) p (L.erase q)).mpr ⟨gs_Step_mono ops hsub hh1, ?_⟩
      have h3 := ih (p :: S) hh2 hqL (gs_Step_mono ops (fun x hx => List.mem_cons_of_mem _ hx) hs)
      apply gs_Bld_mono ops _ (q :: p :: S) (p :: q :: S) _ h3
      intro x hx
      simp only [List.mem_cons] at hx ⊢
      tauto

theorem gs_G_Bld (ops : ℕ → ℕ → List ℕ) (T : ℕ) : ∀ (r : ℕ) (S : List ℕ), gs_G ops T r S →
    ∃ L : List ℕ, gs_Bld ops S L ∧ (T ∈ S ∨ T ∈ L) ∧ L.length ≤ r ∧ L.Nodup ∧ ∀ p ∈ L, p ∉ S
  | 0, S, h => ⟨[], gs_Bld_nil ops S, Or.inl h, by simp, List.nodup_nil, by simp⟩
  | r + 1, S, h => by
    rcases h with h | ⟨p, hp, hg⟩
    · exact ⟨[], gs_Bld_nil ops S, Or.inl h, by simp, List.nodup_nil, by simp⟩
    · obtain ⟨L, hB, hT, hl, hn, hd⟩ := gs_G_Bld ops T r (p :: S) hg
      by_cases hpS : p ∈ S
      · refine ⟨L, gs_Bld_mono ops L (p :: S) S ?_ hB, ?_, by omega, hn, ?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with e | e
          · rw [e]; exact hpS
          · exact e
        · rcases hT with hT | hT
          · left
            rcases List.mem_cons.mp hT with e | e
            · rw [e]; exact hpS
            · exact e
          · right; exact hT
        · intro x hx hxS
          exact hd x hx (List.mem_cons_of_mem _ hxS)
      · refine ⟨p :: L, (gs_Bld_cons ops S p L).mpr ⟨hp, hB⟩, ?_, by simp only [List.length_cons]; omega, ?_, ?_⟩
        · rcases hT with hT | hT
          · rcases List.mem_cons.mp hT with e | e
            · right; rw [e]; exact List.mem_cons.mpr (Or.inl rfl)
            · left; exact e
          · right; exact List.mem_cons_of_mem _ hT
        · exact List.nodup_cons.mpr ⟨fun h => hd p h (List.mem_cons.mpr (Or.inl rfl)), hn⟩
        · intro x hx hxS
          rcases List.mem_cons.mp hx with e | e
          · rw [e] at hxS; exact hpS hxS
          · exact hd x e (List.mem_cons_of_mem _ hxS)

theorem gs_min (P : ℕ → Prop) (L : List ℕ) (h : ∃ p ∈ L, P p) :
    ∃ q ∈ L, P q ∧ ∀ p ∈ L, P p → q ≤ p := by
  induction L with
  | nil => obtain ⟨p, hp, _⟩ := h; simp at hp
  | cons a L ih =>
    by_cases hL : ∃ p ∈ L, P p
    · obtain ⟨q, hq, hPq, hmin⟩ := ih hL
      by_cases ha : P a ∧ a ≤ q
      · refine ⟨a, List.mem_cons.mpr (Or.inl rfl), ha.1, ?_⟩
        intro p hp hPp
        rcases List.mem_cons.mp hp with e | e
        · omega
        · exact le_trans ha.2 (hmin p e hPp)
      · refine ⟨q, List.mem_cons_of_mem _ hq, hPq, ?_⟩
        intro p hp hPp
        rcases List.mem_cons.mp hp with e | e
        · rw [e] at hPp ⊢
          by_contra hc
          exact ha ⟨hPp, by omega⟩
        · exact hmin p e hPp
    · obtain ⟨p, hp, hPp⟩ := h
      rcases List.mem_cons.mp hp with e | e
      · rw [e] at hPp
        refine ⟨a, List.mem_cons.mpr (Or.inl rfl), hPp, ?_⟩
        intro p2 hp2 hP2
        rcases List.mem_cons.mp hp2 with e2 | e2
        · omega
        · exact absurd ⟨p2, e2, hP2⟩ hL
      · exact absurd ⟨p, e, hPp⟩ hL

def gs_cand (ops : ℕ → ℕ → List ℕ) (rec : ℕ → List ℕ → Bool) (l : ℕ) (S : List ℕ) (a b : ℕ) : Bool :=
  (ops a b).any (fun p => (decide (l < p) || (a == l || b == l)) && !t1_mem p S && rec p (p :: S))

def gs_cand2 (ops : ℕ → ℕ → List ℕ) (ext : ℕ → List ℕ → Bool) (l : ℕ) (S : List ℕ) (a b : ℕ) : Bool :=
  (ops a b).any (fun p => (decide (l < p) || (a == l || b == l)) && ext p S && !t1_mem p S)

def gs_srch (ops : ℕ → ℕ → List ℕ) (leaf : List ℕ → Bool) (ext : ℕ → List ℕ → Bool) (T : ℕ) :
    ℕ → ℕ → List ℕ → Bool
  | 0, _, S => t1_mem T S
  | 1, _, S => t1_mem T S || leaf S
  | 2, l, S => t1_mem T S || leaf S || t1_pany (gs_cand2 ops ext l S) S
  | r + 3, l, S => t1_mem T S || t1_pany (gs_cand ops (gs_srch ops leaf ext T (r + 2)) l S) S

theorem gs_cand_symm (ops : ℕ → ℕ → List ℕ) (hsym : ∀ a b p, p ∈ ops a b → p ∈ ops b a)
    (rec : ℕ → List ℕ → Bool) (l : ℕ) (S : List ℕ) (x y : ℕ) :
    gs_cand ops rec l S x y = gs_cand ops rec l S y x := by
  unfold gs_cand
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨p, hp, h⟩
    exact ⟨p, hsym x y p hp, by rw [Bool.or_comm (y == l)]; exact h⟩
  · rintro ⟨p, hp, h⟩
    exact ⟨p, hsym y x p hp, by rw [Bool.or_comm (x == l)]; exact h⟩

theorem gs_cand2_symm (ops : ℕ → ℕ → List ℕ) (hsym : ∀ a b p, p ∈ ops a b → p ∈ ops b a)
    (ext : ℕ → List ℕ → Bool) (l : ℕ) (S : List ℕ) (x y : ℕ) :
    gs_cand2 ops ext l S x y = gs_cand2 ops ext l S y x := by
  unfold gs_cand2
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨p, hp, h⟩
    exact ⟨p, hsym x y p hp, by rw [Bool.or_comm (y == l)]; exact h⟩
  · rintro ⟨p, hp, h⟩
    exact ⟨p, hsym y x p hp, by rw [Bool.or_comm (x == l)]; exact h⟩

theorem gs_pick (ops : ℕ → ℕ → List ℕ) (T l : ℕ) (S L : List ℕ) (hB : gs_Bld ops (l :: S) L)
    (hTL : T ∈ L) (hn : L.Nodup) (hd : ∀ p ∈ L, p ∉ l :: S) (hc : ∀ p ∈ L, gs_Step ops S p → l < p) :
    ∃ q a b, a ∈ l :: S ∧ b ∈ l :: S ∧ q ∈ ops a b ∧ (decide (l < q) || (a == l || b == l)) = true ∧
      (!t1_mem q (l :: S)) = true ∧ gs_Bld ops (q :: l :: S) (L.erase q) ∧ (T = q ∨ T ∈ L.erase q) ∧
      (L.erase q).length + 1 = L.length ∧ (L.erase q).Nodup ∧ (∀ p ∈ L.erase q, p ∉ q :: l :: S) ∧
      (∀ p ∈ L.erase q, gs_Step ops (l :: S) p → q < p) := by
  have hex : ∃ p ∈ L, gs_Step ops (l :: S) p := by
    rcases L with _ | ⟨p, L⟩
    · simp at hTL
    · exact ⟨p, List.mem_cons.mpr (Or.inl rfl), ((gs_Bld_cons ops _ _ _).mp hB).1⟩
  obtain ⟨q, hqL, hqS, hqmin⟩ := gs_min _ L hex
  obtain ⟨a, ha, b, hb, hqab⟩ := hqS
  have hqn : q ∉ l :: S := hd q hqL
  have hcond : (decide (l < q) || (a == l || b == l)) = true := by
    by_cases hS : gs_Step ops S q
    · have := hc q hqL hS
      simp [this]
    · have hab : a = l ∨ b = l := by
        by_contra hne
        push_neg at hne
        apply hS
        refine ⟨a, ?_, b, ?_, hqab⟩
        · rcases List.mem_cons.mp ha with e | e
          · exact absurd e hne.1
          · exact e
        · rcases List.mem_cons.mp hb with e | e
          · exact absurd e hne.2
          · exact e
      rcases hab with e | e
      · subst e; simp
      · subst e; simp
  have hmem : (!t1_mem q (l :: S)) = true := by
    rw [t1_mem_false q _ hqn]; rfl
  refine ⟨q, a, b, ha, hb, hqab, hcond, hmem, gs_Bld_erase ops q L (l :: S) hB hqL ⟨a, ha, b, hb, hqab⟩,
    ?_, ?_, hn.erase q, ?_, ?_⟩
  · by_cases hTq : T = q
    · left; exact hTq
    · right; exact (List.mem_erase_of_ne hTq).mpr hTL
  · rw [List.length_erase_of_mem hqL]
    have : 0 < L.length := List.length_pos_of_mem hqL
    omega
  · intro p hp
    rw [hn.mem_erase_iff] at hp
    intro hpS
    rcases List.mem_cons.mp hpS with e | e
    · exact hp.1 e
    · exact hd p hp.2 e
  · intro p hp hpS
    rw [hn.mem_erase_iff] at hp
    have h1 := hqmin p hp.2 hpS
    have h2 : p ≠ q := hp.1
    omega

theorem gs_srch_sound (ops : ℕ → ℕ → List ℕ) (leaf : List ℕ → Bool) (ext : ℕ → List ℕ → Bool) (T : ℕ)
    (hsym : ∀ a b p, p ∈ ops a b → p ∈ ops b a)
    (hleaf : ∀ S : List ℕ, gs_Step ops S T → leaf S = true)
    (hext : ∀ p (S : List ℕ) c, c ∈ p :: S → T ∈ ops p c → ext p S = true) :
    ∀ (r l : ℕ) (S L : List ℕ), gs_Bld ops (l :: S) L → (T ∈ l :: S ∨ T ∈ L) → L.length ≤ r →
      L.Nodup → (∀ p ∈ L, p ∉ l :: S) → (∀ p ∈ L, gs_Step ops S p → l < p) →
      gs_srch ops leaf ext T r l (l :: S) = true
  | 0, l, S, L, _, hT, hl, _, _, _ => by
    have e : L = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst e
    rcases hT with hT | hT
    · exact t1_mem_of T _ hT
    · simp at hT
  | 1, l, S, L, hB, hT, hl, _, _, _ => by
    show (t1_mem T (l :: S) || leaf (l :: S)) = true
    rw [Bool.or_eq_true]
    rcases hT with hT | hT
    · exact Or.inl (t1_mem_of T _ hT)
    · right
      rcases L with _ | ⟨p, L⟩
      · simp at hT
      · have e : L = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at hl; omega)
        subst e
        have e2 : T = p := by simpa using hT
        subst e2
        exact hleaf _ ((gs_Bld_cons ops _ _ _).mp hB).1
  | 2, l, S, L, hB, hT, hl, hn, hd, hc => by
    show (t1_mem T (l :: S) || leaf (l :: S) || t1_pany (gs_cand2 ops ext l (l :: S)) (l :: S)) = true
    rw [Bool.or_eq_true, Bool.or_eq_true]
    by_cases hTS : T ∈ l :: S
    · exact Or.inl (Or.inl (t1_mem_of T _ hTS))
    have hTL : T ∈ L := by
      rcases hT with h | h
      · exact absurd h hTS
      · exact h
    obtain ⟨q, a, b, ha, hb, hqab, hcond, hmem, hB2, hT2, hlen2, -, -, -⟩ := gs_pick ops T l S L hB hTL hn hd hc
    rcases hT2 with hTq | hTq
    · subst hTq
      exact Or.inl (Or.inr (hleaf _ ⟨a, ha, b, hb, hqab⟩))
    · generalize hE : L.erase q = E at hB2 hTq hlen2
      rcases E with _ | ⟨x, E⟩
      · simp at hTq
      · have hE0 : E = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at hlen2; omega)
        subst hE0
        have hx : T = x := by simpa using hTq
        subst hx
        obtain ⟨c, hc', d, hd', hT3⟩ := ((gs_Bld_cons ops _ _ _).mp hB2).1
        by_cases hcq : c = q
        · rw [hcq] at hT3
          right
          apply t1_pany_of _ (gs_cand2_symm ops hsym ext l (l :: S)) (l :: S) a b ha hb
          unfold gs_cand2
          rw [List.any_eq_true]
          refine ⟨q, hqab, ?_⟩
          rw [Bool.and_eq_true, Bool.and_eq_true]
          exact ⟨⟨hcond, hext q (l :: S) d hd' hT3⟩, hmem⟩
        · by_cases hdq : d = q
          · rw [hdq] at hT3
            right
            apply t1_pany_of _ (gs_cand2_symm ops hsym ext l (l :: S)) (l :: S) a b ha hb
            unfold gs_cand2
            rw [List.any_eq_true]
            refine ⟨q, hqab, ?_⟩
            rw [Bool.and_eq_true, Bool.and_eq_true]
            exact ⟨⟨hcond, hext q (l :: S) c hc' (hsym c q T hT3)⟩, hmem⟩
          · left; right
            apply hleaf
            refine ⟨c, ?_, d, ?_, hT3⟩
            · rcases List.mem_cons.mp hc' with e | e
              · exact absurd e hcq
              · exact e
            · rcases List.mem_cons.mp hd' with e | e
              · exact absurd e hdq
              · exact e
  | r + 3, l, S, L, hB, hT, hl, hn, hd, hc => by
    show (t1_mem T (l :: S) ||
      t1_pany (gs_cand ops (gs_srch ops leaf ext T (r + 2)) l (l :: S)) (l :: S)) = true
    rw [Bool.or_eq_true]
    by_cases hTS : T ∈ l :: S
    · exact Or.inl (t1_mem_of T _ hTS)
    right
    have hTL : T ∈ L := by
      rcases hT with h | h
      · exact absurd h hTS
      · exact h
    obtain ⟨q, a, b, ha, hb, hqab, hcond, hmem, hB2, hT2, hlen2, hn2, hd2, hc2⟩ :=
      gs_pick ops T l S L hB hTL hn hd hc
    apply t1_pany_of _ (gs_cand_symm ops hsym _ l (l :: S)) (l :: S) a b ha hb
    unfold gs_cand
    rw [List.any_eq_true]
    refine ⟨q, hqab, ?_⟩
    have hrec : gs_srch ops leaf ext T (r + 2) q (q :: l :: S) = true := by
      apply gs_srch_sound ops leaf ext T hsym hleaf hext (r + 2) q (l :: S) (L.erase q) hB2
      · rcases hT2 with h | h
        · left; rw [h]; exact List.mem_cons.mpr (Or.inl rfl)
        · right; exact h
      · omega
      · exact hn2
      · exact hd2
      · exact hc2
    rw [Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨⟨hcond, hmem⟩, hrec⟩

def gs_extM (T p : ℕ) (S : List ℕ) : Bool :=
  (p ||| T == T || p &&& T == T) && (p :: S).any (fun c => p &&& c == T || p ||| c == T)

theorem gs_extM_sound (T p : ℕ) (S : List ℕ) (c : ℕ) (hc : c ∈ p :: S) (h : T ∈ gs_opsM p c) :
    gs_extM T p S = true := by
  simp only [gs_opsM, List.mem_cons, List.not_mem_nil, or_false] at h
  unfold gs_extM
  rw [Bool.and_eq_true, List.any_eq_true]
  rcases h with e | e
  · refine ⟨?_, c, hc, ?_⟩
    · rw [e, t1_land_absl]; simp
    · rw [← e]; simp
  · refine ⟨?_, c, hc, ?_⟩
    · rw [e, t1_lor_absl]; simp
    · rw [← e]; simp

def gs_preA (m T p : ℕ) : Bool :=
  (p &&& T == T) || ((gs_full m ^^^ p) &&& T == T) || (p &&& (gs_full m ^^^ T) == gs_full m ^^^ T) ||
    ((gs_full m ^^^ p) &&& (gs_full m ^^^ T) == gs_full m ^^^ T)

def gs_extA (m T p : ℕ) (S : List ℕ) : Bool :=
  gs_preA m T p && (p :: S).any (fun c => (gs_opsA m p c).any (fun z => z == T))

theorem gs_preA_of (m T p x y : ℕ) (hx : x = p ∨ x = gs_full m ^^^ p)
    (h : x &&& y = T ∨ x &&& y = gs_full m ^^^ T) : gs_preA m T p = true := by
  unfold gs_preA
  rcases hx with rfl | rfl <;> rcases h with h | h <;> rw [← h, t1_land_absl] <;> simp

theorem gs_extA_sound (m T p : ℕ) (S : List ℕ) (c : ℕ) (hc : c ∈ p :: S) (h : T ∈ gs_opsA m p c) :
    gs_extA m T p S = true := by
  unfold gs_extA
  rw [Bool.and_eq_true, List.any_eq_true]
  refine ⟨?_, c, hc, List.any_eq_true.mpr ⟨T, h, beq_self_eq_true _⟩⟩
  simp only [gs_opsA, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with e | e | e | e
  · exact gs_preA_of m T p p c (Or.inl rfl) (gs_nz_eq m _ T e.symm)
  · exact gs_preA_of m T p p _ (Or.inl rfl) (gs_nz_eq m _ T e.symm)
  · exact gs_preA_of m T p _ c (Or.inr rfl) (gs_nz_eq m _ T e.symm)
  · exact gs_preA_of m T p _ _ (Or.inr rfl) (gs_nz_eq m _ T e.symm)


def gs_inp (n v : ℕ) : List Bool := List.ofFn (fun i : Fin n => v.testBit i)

theorem gs_inp_len (n v : ℕ) : (gs_inp n v).length = n := by simp [gs_inp]

def gs_prof (n : ℕ) (ms : List ℕ) (C : Circuit) (w : ℕ) : ℕ :=
  t1_bits (fun k => val C (gs_inp n (ms.getD k 0)) w) ms.length

def gs_xs (n : ℕ) (ms : List ℕ) : List ℕ :=
  (List.range n).map (fun i => t1_bits (fun k => (ms.getD k 0).testBit i) ms.length)

def gs_base (n : ℕ) (ms : List ℕ) : List ℕ := 0 :: gs_full ms.length :: gs_xs n ms

def gs_St (n : ℕ) (ms : List ℕ) (C : Circuit) : ℕ → List ℕ
  | 0 => gs_base n ms
  | j + 1 => gs_prof n ms C (n + j) :: gs_St n ms C j

theorem gs_St_base (n : ℕ) (ms : List ℕ) (C : Circuit) {x : ℕ} (hx : x ∈ gs_base n ms) (j : ℕ) :
    x ∈ gs_St n ms C j := by
  induction j with
  | zero => exact hx
  | succ j ih => exact List.mem_cons_of_mem _ ih

theorem gs_St_prof (n : ℕ) (ms : List ℕ) (C : Circuit) (j : ℕ) :
    ∀ i, i < n + j → gs_prof n ms C i ∈ gs_St n ms C j := by
  induction j with
  | zero =>
    intro i hi
    have e : gs_prof n ms C i = t1_bits (fun k => (ms.getD k 0).testBit i) ms.length := by
      unfold gs_prof
      congr 1
      funext k
      exact val_ofFn_lt C (fun i : Fin n => (ms.getD k 0).testBit i) i (by omega)
    rw [e]
    show _ ∈ 0 :: gs_full ms.length :: gs_xs n ms
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    exact List.mem_map.mpr ⟨i, List.mem_range.mpr (by omega), rfl⟩
  | succ j ih =>
    intro i hi
    by_cases h : i < n + j
    · exact List.mem_cons_of_mem _ (ih i h)
    · have e : i = n + j := by omega
      subst e
      exact List.mem_cons.mpr (Or.inl rfl)

theorem gs_zero_mem (n : ℕ) (ms : List ℕ) (C : Circuit) (j : ℕ) : (0 : ℕ) ∈ gs_St n ms C j :=
  gs_St_base n ms C (List.mem_cons.mpr (Or.inl rfl)) j

theorem gs_full_mem (n : ℕ) (ms : List ℕ) (C : Circuit) (j : ℕ) :
    gs_full ms.length ∈ gs_St n ms C j :=
  gs_St_base n ms C (List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl rfl))) j

theorem gs_gate_fg (m : ℕ) (S : List ℕ) (R : ℕ → ℕ → Bool) (op : GateOp) (l : List ℕ)
    (hop : op = GateOp.and ∨ op = GateOp.or) (hl : l.length ≤ 2)
    (hR : ∀ i ∈ l, t1_bits (fun k => R k i) m ∈ S) (h0 : (0 : ℕ) ∈ S) (h1 : gs_full m ∈ S) :
    ∃ f g : ℕ → Bool, t1_bits f m ∈ S ∧ t1_bits g m ∈ S ∧
      ((∀ k, op.eval (l.map (R k)) = (f k && g k)) ∨ (∀ k, op.eval (l.map (R k)) = (f k || g k))) := by
  have h0' : t1_bits (fun _ => false) m ∈ S := by rw [t1_bits_false]; exact h0
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · rcases hop with rfl | rfl
    · exact ⟨fun _ => true, fun _ => true, h1, h1, Or.inl (fun k => by simp [GateOp.eval])⟩
    · exact ⟨fun _ => false, fun _ => false, h0', h0', Or.inr (fun k => by simp [GateOp.eval])⟩
  · have ha := hR a (by simp)
    rcases hop with rfl | rfl
    · exact ⟨fun k => R k a, fun _ => true, ha, h1, Or.inl (fun k => by simp [GateOp.eval])⟩
    · exact ⟨fun k => R k a, fun _ => false, ha, h0', Or.inr (fun k => by simp [GateOp.eval])⟩
  · have ha := hR a (by simp)
    have hb := hR b (by simp)
    rcases hop with rfl | rfl
    · exact ⟨fun k => R k a, fun k => R k b, ha, hb, Or.inl (fun k => by simp [GateOp.eval])⟩
    · exact ⟨fun k => R k a, fun k => R k b, ha, hb, Or.inr (fun k => by simp [GateOp.eval])⟩
  · simp only [List.length_cons] at hl
    omega

theorem gs_gate_not (m : ℕ) (S : List ℕ) (R : ℕ → ℕ → Bool) (l : List ℕ)
    (hR : ∀ i ∈ l, t1_bits (fun k => R k i) m ∈ S) (h0 : (0 : ℕ) ∈ S) :
    ∃ f : ℕ → Bool, t1_bits f m ∈ S ∧ ∀ k, GateOp.not.eval (l.map (R k)) = ! f k := by
  rcases l with _ | ⟨a, l⟩
  · refine ⟨fun _ => false, by rw [t1_bits_false]; exact h0, fun k => by simp [GateOp.eval]⟩
  · exact ⟨fun k => R k a, hR a (by simp), fun k => by simp [GateOp.eval]⟩

theorem gs_gate_R (n : ℕ) (ms : List ℕ) (C : Circuit) (j : ℕ) :
    ∀ i ∈ (gateAt C j).inputs, t1_bits (fun k => (fun k i => if i < n + j then
      val C (gs_inp n (ms.getD k 0)) i else false) k i) ms.length ∈ gs_St n ms C j := by
  intro i _
  by_cases hi : i < n + j
  · simp only [hi, ↓reduceIte]
    exact gs_St_prof n ms C j i hi
  · simp only [hi, ↓reduceIte]
    rw [t1_bits_false]
    exact gs_zero_mem n ms C j

theorem gs_prof_gate (n : ℕ) (ms : List ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gs_prof n ms C (n + j) = t1_bits (fun k => (gateAt C j).op.eval ((gateAt C j).inputs.map
      ((fun k i => if i < n + j then val C (gs_inp n (ms.getD k 0)) i else false) k))) ms.length := by
  unfold gs_prof
  congr 1
  funext k
  exact val_gate (gs_inp_len n _) hj

theorem gs_ops_cases (C : Circuit) (hfan : FanInTwo C) (j : ℕ) (hj : j < C.gates.length) :
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or ∨ (gateAt C j).op = GateOp.not) ∧
      (gateAt C j).inputs.length ≤ 2 := by
  have hg := hfan _ (gateAt_mem hj)
  exact ⟨by simpa using hg.1, hg.2⟩

def gs_andhit (U : ℕ) (L : List ℕ) : Bool :=
  t1_pany (fun x y => x &&& y == U) (L.filter (fun x => x &&& U == U))

theorem gs_andhit_of (U : ℕ) (L : List ℕ) (x y : ℕ) (hx : x ∈ L) (hy : y ∈ L) (h : x &&& y = U) :
    gs_andhit U L = true := by
  unfold gs_andhit
  have hsym : ∀ a b, (fun a b => a &&& b == U) a b = (fun a b => a &&& b == U) b a := by
    intro a b; show (a &&& b == U) = (b &&& a == U); rw [t1_land_comm]
  exact t1_pany_of _ hsym _ x y
    (List.mem_filter.mpr ⟨hx, by rw [← h, t1_land_absl]; exact beq_self_eq_true _⟩)
    (List.mem_filter.mpr ⟨hy, by rw [← h, t1_land_absr]; exact beq_self_eq_true _⟩)
    (by simp [h])

def gs_cmpl (m : ℕ) (S : List ℕ) : List ℕ := S ++ S.map (fun a => gs_full m ^^^ a)

def gs_leafA (m T : ℕ) (S : List ℕ) : Bool :=
  gs_andhit T (gs_cmpl m S) || gs_andhit (gs_full m ^^^ T) (gs_cmpl m S)

theorem gs_leafA_sound (m T : ℕ) (S : List ℕ) (h : gs_Step (gs_opsA m) S T) : gs_leafA m T S = true := by
  obtain ⟨a, ha, b, hb, hT⟩ := h
  have hA : a ∈ gs_cmpl m S := List.mem_append_left _ ha
  have hB : b ∈ gs_cmpl m S := List.mem_append_left _ hb
  have hA' : gs_full m ^^^ a ∈ gs_cmpl m S := List.mem_append_right _ (List.mem_map.mpr ⟨a, ha, rfl⟩)
  have hB' : gs_full m ^^^ b ∈ gs_cmpl m S := List.mem_append_right _ (List.mem_map.mpr ⟨b, hb, rfl⟩)
  have key : ∀ x y, x ∈ gs_cmpl m S → y ∈ gs_cmpl m S → gs_nz m (x &&& y) = T → gs_leafA m T S = true := by
    intro x y hx hy he
    unfold gs_leafA
    rw [Bool.or_eq_true]
    rcases gs_nz_eq m _ T he with e | e
    · exact Or.inl (gs_andhit_of _ _ x y hx hy e)
    · exact Or.inr (gs_andhit_of _ _ x y hx hy e)
  simp only [gs_opsA, List.mem_cons, List.not_mem_nil, or_false] at hT
  rcases hT with e | e | e | e
  · exact key a b hA hB e.symm
  · exact key a _ hA hB' e.symm
  · exact key _ b hA' hB e.symm
  · exact key _ _ hA' hB' e.symm

theorem gs_symM (a b p : ℕ) (h : p ∈ gs_opsM a b) : p ∈ gs_opsM b a := by
  simp only [gs_opsM, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  rw [t1_land_comm b a, t1_lor_comm b a]
  exact h

theorem gs_symA (m a b p : ℕ) (h : p ∈ gs_opsA m a b) : p ∈ gs_opsA m b a := by
  simp only [gs_opsA, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  rw [t1_land_comm b a, t1_land_comm b (gs_full m ^^^ a), t1_land_comm (gs_full m ^^^ b) a,
    t1_land_comm (gs_full m ^^^ b) (gs_full m ^^^ a)]
  tauto

theorem gs_leafM_sound (T : ℕ) (S : List ℕ) (h : gs_Step gs_opsM S T) : t1_one T S = true := by
  obtain ⟨a, ha, b, hb, hT⟩ := h
  simp only [gs_opsM, List.mem_cons, List.not_mem_nil, or_false] at hT
  apply t1_one_of T S a b ha hb
  rcases hT with e | e
  · exact Or.inl e.symm
  · exact Or.inr e.symm

theorem gs_lower (n : ℕ) (f : (Fin n → Bool) → Bool) (ms : List ℕ) (k T TA : ℕ) (RM RA : List ℕ)
    (hm : 1 ≤ ms.length)
    (hT : t1_bits (fun j => f (fun i : Fin n => (ms.getD j 0).testBit i)) ms.length = T)
    (hTA : gs_nz ms.length T = TA)
    (hBM : ∀ x ∈ gs_base n ms, x ∈ 0 :: RM)
    (hBA : ∀ x ∈ (gs_base n ms).map (gs_nz ms.length), x ∈ 0 :: RA)
    (hM : gs_srch gs_opsM (t1_one T) (gs_extM T) T (k - 1) 0 (0 :: RM) = false)
    (hA : gs_srch (gs_opsA ms.length) (gs_leafA ms.length TA) (gs_extA ms.length TA) TA (k - 2) 0 (0 :: RA) = false) :
    ∀ t, HasCircuitSize n f t → k ≤ t := by
  intro t ht
  obtain ⟨C, hfan, hsize, hf⟩ := ht
  have hlen : C.gates.length ≤ t := hsize
  by_contra hlt
  push_neg at hlt
  have hout : gs_prof n ms C C.output = T := by
    rw [← hT]
    unfold gs_prof
    apply t1_bits_ext
    intro j _
    exact hf (fun i : Fin n => (ms.getD j 0).testBit i)
  have hTin : T ∈ gs_St n ms C C.gates.length := by
    rw [← hout]
    by_cases ho : C.output < n + C.gates.length
    · exact gs_St_prof n ms C _ _ ho
    · have e : gs_prof n ms C C.output = t1_bits (fun _ => false) ms.length := by
        unfold gs_prof
        apply t1_bits_ext
        intro j _
        exact val_ge (gs_inp_len n _) (by omega)
      rw [e, t1_bits_false]
      exact gs_zero_mem n ms C _
  have hnm : ∀ j, j < C.gates.length → (gateAt C j).op = GateOp.not →
      gs_nz ms.length (gs_prof n ms C (n + j)) ∈ (gs_St n ms C j).map (gs_nz ms.length) := by
    intro j hj hop
    rw [gs_prof_gate n ms C j hj, hop]
    obtain ⟨f1, hf1, he⟩ := gs_gate_not ms.length _ _ _ (gs_gate_R n ms C j) (gs_zero_mem n ms C j)
    rw [t1_bits_ext (fun k _ => he k), gs_bits_not, gs_nz_compl _ _ hm]
    exact List.mem_map.mpr ⟨_, hf1, rfl⟩
  by_cases hnot : ∃ j, j < C.gates.length ∧ (gateAt C j).op = GateOp.not
  · -- some NOT gate: search A
    obtain ⟨j0, hj0, hop0⟩ := hnot
    have hst : ∀ j, j < C.gates.length →
        (gs_St n ms C (j + 1)).map (gs_nz ms.length) =
          gs_nz ms.length (gs_prof n ms C (n + j)) :: (gs_St n ms C j).map (gs_nz ms.length) ∧
        (gs_nz ms.length (gs_prof n ms C (n + j)) ∈ (gs_St n ms C j).map (gs_nz ms.length) ∨
          gs_Step (gs_opsA ms.length) ((gs_St n ms C j).map (gs_nz ms.length))
            (gs_nz ms.length (gs_prof n ms C (n + j)))) := by
      intro j hj
      refine ⟨rfl, ?_⟩
      obtain ⟨hop, hl⟩ := gs_ops_cases C hfan j hj
      rw [gs_prof_gate n ms C j hj]
      rcases hop with hop | hop | hop
      · obtain ⟨f1, g1, hf1, hg1, he⟩ := gs_gate_fg ms.length _ _ _ _ (Or.inl hop) hl
          (gs_gate_R n ms C j) (gs_zero_mem n ms C j) (gs_full_mem n ms C j)
        right
        refine ⟨_, List.mem_map.mpr ⟨_, hf1, rfl⟩, _, List.mem_map.mpr ⟨_, hg1, rfl⟩, ?_⟩
        rcases he with he | he
        · rw [t1_bits_ext (fun k _ => he k), t1_bits_and]; exact gs_A_and _ _ _
        · rw [t1_bits_ext (fun k _ => he k), t1_bits_or]; exact gs_A_or _ hm _ _
      · obtain ⟨f1, g1, hf1, hg1, he⟩ := gs_gate_fg ms.length _ _ _ _ (Or.inr hop) hl
          (gs_gate_R n ms C j) (gs_zero_mem n ms C j) (gs_full_mem n ms C j)
        right
        refine ⟨_, List.mem_map.mpr ⟨_, hf1, rfl⟩, _, List.mem_map.mpr ⟨_, hg1, rfl⟩, ?_⟩
        rcases he with he | he
        · rw [t1_bits_ext (fun k _ => he k), t1_bits_and]; exact gs_A_and _ _ _
        · rw [t1_bits_ext (fun k _ => he k), t1_bits_or]; exact gs_A_or _ hm _ _
      · left
        rw [← gs_prof_gate n ms C j hj]
        exact hnm j hj hop
    have hTA' : TA ∈ (gs_St n ms C C.gates.length).map (gs_nz ms.length) :=
      List.mem_map.mpr ⟨T, hTin, hTA⟩
    have hch := (gs_chain (gs_opsA ms.length) TA (fun j => (gs_St n ms C j).map (gs_nz ms.length))
      (fun j => gs_nz ms.length (gs_prof n ms C (n + j))) C.gates.length hst hTA'
      C.gates.length 0 (by omega)).2 ⟨j0, Nat.zero_le _, hj0, hnm j0 hj0 hop0⟩
    have hG := gs_G_le _ _ _ _ hch (k - 2 - (C.gates.length - 1))
    rw [show C.gates.length - 1 + (k - 2 - (C.gates.length - 1)) = k - 2 by omega] at hG
    have hG0 : gs_G (gs_opsA ms.length) TA (k - 2) (0 :: RA) := by
      exact gs_G_sub _ _ _ _ _ hBA hG
    obtain ⟨L, hB, hTL, hl, hn, hd⟩ := gs_G_Bld _ _ _ _ hG0
    have h1 := gs_srch_sound (gs_opsA ms.length) (gs_leafA ms.length TA) (gs_extA ms.length TA) TA
      (gs_symA ms.length) (gs_leafA_sound ms.length TA) (gs_extA_sound ms.length TA) (k - 2) 0 RA L hB hTL hl hn hd (by
        intro p hp _
        have h2 := hd p hp
        have h3 : p ≠ 0 := by
          rintro rfl
          exact h2 (List.mem_cons.mpr (Or.inl rfl))
        omega)
    rw [hA] at h1
    exact Bool.false_ne_true h1
  · -- no NOT gate: search M
    push_neg at hnot
    have hst : ∀ j, j < C.gates.length →
        gs_St n ms C (j + 1) = gs_prof n ms C (n + j) :: gs_St n ms C j ∧
        (gs_prof n ms C (n + j) ∈ gs_St n ms C j ∨
          gs_Step gs_opsM (gs_St n ms C j) (gs_prof n ms C (n + j))) := by
      intro j hj
      refine ⟨rfl, Or.inr ?_⟩
      obtain ⟨hop, hl⟩ := gs_ops_cases C hfan j hj
      have hop' : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
        rcases hop with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h (hnot j hj)
      rw [gs_prof_gate n ms C j hj]
      obtain ⟨f1, g1, hf1, hg1, he⟩ := gs_gate_fg ms.length _ _ _ _ hop' hl
        (gs_gate_R n ms C j) (gs_zero_mem n ms C j) (gs_full_mem n ms C j)
      refine ⟨_, hf1, _, hg1, ?_⟩
      rcases he with he | he
      · rw [t1_bits_ext (fun k _ => he k), t1_bits_and]
        simp [gs_opsM]
      · rw [t1_bits_ext (fun k _ => he k), t1_bits_or]
        simp [gs_opsM]
    have hch := (gs_chain gs_opsM T (gs_St n ms C) (fun j => gs_prof n ms C (n + j)) C.gates.length
      hst hTin C.gates.length 0 (by omega)).1
    have hG := gs_G_le _ _ _ _ hch (k - 1 - C.gates.length)
    rw [show C.gates.length + (k - 1 - C.gates.length) = k - 1 by omega] at hG
    have hG0 : gs_G gs_opsM T (k - 1) (0 :: RM) := by
      exact gs_G_sub _ _ _ _ _ hBM hG
    obtain ⟨L, hB, hTL, hl, hn, hd⟩ := gs_G_Bld _ _ _ _ hG0
    have h1 := gs_srch_sound gs_opsM (t1_one T) (gs_extM T) T gs_symM (gs_leafM_sound T) (gs_extM_sound T)
      (k - 1) 0 RM L hB hTL hl hn hd
      (by
        intro p hp _
        have h2 := hd p hp
        have h3 : p ≠ 0 := by
          rintro rfl
          exact h2 (List.mem_cons.mpr (Or.inl rfl))
        omega)
    rw [hM] at h1
    exact Bool.false_ne_true h1

-- FRAGMENT lev3    DEPENDS: fold mono table1a gensize
-- Lower bounds for ordered-outputs rows: circuits on the 4 + 2 wires (four inputs, then the constants
-- false and true) read at the five thermometer levels t = 0 .. 4 (first t inputs on). The profile of a
-- wire is the 5-bit mask of its values at the five levels; a set of profiles is a 32-bit mask.
-- Exports:
--   def lv_lev t, lv_pv D w (profile), lv_Sm f k (mask of the profiles of wires below k)
--   def lv_ao S (masks of AND/OR results and S itself), lv_nt S (complements), lv_miss tg S, lv_srch tg k n S
--   lv_main tg (tg.Nodup) (S0 = lv_Sm pin 6) (search false) : no circuit with at most G gates, at most K NOTs
--     and taps carrying the targets of tg.

instance lvDecOp : DecidableEq GateOp := lineDegreeGateOpDecEq

def lv_lev (t : ℕ) : List Bool := (List.ofFn (fun i : Fin 4 => decide (i.val < t))) ++ [false, true]

theorem lv_lev_len (t : ℕ) : (lv_lev t).length = 6 := by simp [lv_lev]

def lv_pv (D : Circuit) (w : ℕ) : ℕ := t1_bits (fun t => (D.wires (lv_lev t)).getD w false) 5

theorem lv_lt32 (f : ℕ → Bool) : t1_bits f 5 < 32 := by
  have : t1_bits f 5 < 2 ^ 5 := by
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    rw [t1_bits_testBit]
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt]
    exact Or.inl hi
  simpa using this

theorem lv_pv_lt (D : Circuit) (w : ℕ) : lv_pv D w < 32 := lv_lt32 _

def lv_Sm (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => lv_Sm f k ||| (1 <<< f k)

theorem lv_bit1 (p q : ℕ) : (1 <<< p).testBit q = decide (q = p) := by
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
  by_cases h : q = p
  · subst h; simp
  · simp [h, Ne.symm h]

theorem lv_Sm_mem (f : ℕ → ℕ) : ∀ k w, w < k → (lv_Sm f k).testBit (f w) = true := by
  intro k
  induction k with
  | zero => intro w hw; omega
  | succ k ih =>
    intro w hw
    simp only [lv_Sm, Nat.testBit_or, lv_bit1, Bool.or_eq_true, decide_eq_true_eq]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hw with h | h
    · exact Or.inl (ih w h)
    · exact Or.inr (by rw [h])

theorem lv_Sm_congr (f g : ℕ → ℕ) : ∀ k, (∀ w, w < k → f w = g w) → lv_Sm f k = lv_Sm g k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro h
    simp only [lv_Sm]
    rw [ih (fun w hw => h w (by omega)), h k (by omega)]

-- candidate masks over the 32 profile values
def lv_inner (S a : ℕ) : List ℕ → ℕ → ℕ
  | [], acc => acc
  | b :: bs, acc => lv_inner S a bs (if S.testBit b then acc ||| (1 <<< (a &&& b)) ||| (1 <<< (a ||| b)) else acc)

def lv_outer (S : ℕ) : List ℕ → ℕ → ℕ
  | [], acc => acc
  | a :: as, acc => lv_outer S as (if S.testBit a then lv_inner S a (List.range 32) acc else acc)

def lv_ao (S : ℕ) : ℕ := lv_outer S (List.range 32) S

def lv_ntl (S : ℕ) : List ℕ → ℕ → ℕ
  | [], acc => acc
  | a :: as, acc => lv_ntl S as (if S.testBit a then acc ||| (1 <<< (31 ^^^ a)) else acc)

def lv_nt (S : ℕ) : ℕ := lv_ntl S (List.range 32) 0

theorem lv_inner_keep (S a : ℕ) : ∀ (L : List ℕ) (acc q : ℕ), acc.testBit q = true →
    (lv_inner S a L acc).testBit q = true := by
  intro L
  induction L with
  | nil => intro acc q h; exact h
  | cons b bs ih =>
    intro acc q h
    simp only [lv_inner]
    apply ih
    split
    · simp [Nat.testBit_or, h]
    · exact h

theorem lv_inner_add (S a : ℕ) : ∀ (L : List ℕ) (acc b : ℕ), b ∈ L → S.testBit b = true →
    (lv_inner S a L acc).testBit (a &&& b) = true ∧ (lv_inner S a L acc).testBit (a ||| b) = true := by
  intro L
  induction L with
  | nil => intro acc b hb; simp at hb
  | cons c cs ih =>
    intro acc b hb hS
    simp only [lv_inner]
    rcases List.mem_cons.1 hb with h | h
    · subst h
      simp only [hS, if_true]
      constructor
      · apply lv_inner_keep; simp [Nat.testBit_or, lv_bit1]
      · apply lv_inner_keep; simp [Nat.testBit_or, lv_bit1]
    · exact ih _ b h hS

theorem lv_outer_keep (S : ℕ) : ∀ (L : List ℕ) (acc q : ℕ), acc.testBit q = true →
    (lv_outer S L acc).testBit q = true := by
  intro L
  induction L with
  | nil => intro acc q h; exact h
  | cons a as ih =>
    intro acc q h
    simp only [lv_outer]
    apply ih
    split
    · exact lv_inner_keep S a _ _ _ h
    · exact h

theorem lv_outer_add (S : ℕ) : ∀ (L : List ℕ) (acc a b : ℕ), a ∈ L → S.testBit a = true → b < 32 →
    S.testBit b = true →
    (lv_outer S L acc).testBit (a &&& b) = true ∧ (lv_outer S L acc).testBit (a ||| b) = true := by
  intro L
  induction L with
  | nil => intro acc a b ha; simp at ha
  | cons c cs ih =>
    intro acc a b ha hSa hb hSb
    simp only [lv_outer]
    rcases List.mem_cons.1 ha with h | h
    · subst h
      simp only [hSa, if_true]
      have := lv_inner_add S a (List.range 32) acc b (List.mem_range.2 hb) hSb
      exact ⟨lv_outer_keep S cs _ _ this.1, lv_outer_keep S cs _ _ this.2⟩
    · exact ih _ a b h hSa hb hSb

theorem lv_ao_self (S q : ℕ) (h : S.testBit q = true) : (lv_ao S).testBit q = true :=
  lv_outer_keep S _ _ _ h

theorem lv_ao_pair (S a b : ℕ) (ha : a < 32) (hb : b < 32) (hSa : S.testBit a = true) (hSb : S.testBit b = true) :
    (lv_ao S).testBit (a &&& b) = true ∧ (lv_ao S).testBit (a ||| b) = true :=
  lv_outer_add S _ S a b (List.mem_range.2 ha) hSa hb hSb

theorem lv_ntl_keep (S : ℕ) : ∀ (L : List ℕ) (acc q : ℕ), acc.testBit q = true →
    (lv_ntl S L acc).testBit q = true := by
  intro L
  induction L with
  | nil => intro acc q h; exact h
  | cons b bs ih =>
    intro acc q h
    simp only [lv_ntl]
    apply ih
    split
    · simp [Nat.testBit_or, h]
    · exact h

theorem lv_nt_comp (S a : ℕ) (ha : a < 32) (hS : S.testBit a = true) : (lv_nt S).testBit (31 ^^^ a) = true := by
  have key : ∀ (L : List ℕ) (acc : ℕ), a ∈ L → (lv_ntl S L acc).testBit (31 ^^^ a) = true := by
    intro L
    induction L with
    | nil => intro acc h; simp at h
    | cons c cs ih =>
      intro acc h
      simp only [lv_ntl]
      rcases List.mem_cons.1 h with h | h
      · subst h
        simp only [hS, if_true]
        apply lv_ntl_keep; simp [Nat.testBit_or, lv_bit1]
      · exact ih _ h
  exact key _ _ (List.mem_range.2 ha)

-- the search
def lv_miss (tg : List ℕ) (S : ℕ) : ℕ := (tg.filter (fun p => !S.testBit p)).length

def lv_srch (tg : List ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, _, S => lv_miss tg S == 0
  | k + 1, n, S => lv_miss tg S == 0 || (decide (lv_miss tg S ≤ k + 1) &&
      (List.range 32).any (fun p => !S.testBit p &&
        (((lv_ao S).testBit p && lv_srch tg k n (S ||| (1 <<< p))) ||
         (decide (0 < n) && (lv_nt S).testBit p && lv_srch tg k (n - 1) (S ||| (1 <<< p))))))

theorem lv_srch_miss (tg : List ℕ) : ∀ k n S, lv_srch tg k n S = true → lv_miss tg S ≤ k := by
  intro k
  cases k with
  | zero => intro n S h; simp [lv_srch] at h; omega
  | succ k =>
    intro n S h
    rw [lv_srch.eq_2] at h
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with h | ⟨h, _⟩ <;> omega

theorem lv_srch_mono_k (tg : List ℕ) : ∀ k n S, lv_srch tg k n S = true → lv_srch tg (k + 1) n S = true := by
  intro k
  induction k with
  | zero =>
    intro n S h
    simp only [lv_srch] at h
    simp [lv_srch, h]
  | succ k ih =>
    intro n S h
    have hm := lv_srch_miss tg _ _ _ h
    rw [lv_srch.eq_2] at h ⊢
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq,
      List.any_eq_true] at h ⊢
    rcases h with h | ⟨_, p, hp, hb⟩
    · exact Or.inl h
    · refine Or.inr ⟨by omega, p, hp, ?_⟩
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hb ⊢
      rcases hb with ⟨h1, (⟨h2, h3⟩ | ⟨⟨h4, h5⟩, h6⟩)⟩
      · exact ⟨h1, Or.inl ⟨h2, ih _ _ h3⟩⟩
      · exact ⟨h1, Or.inr ⟨⟨h4, h5⟩, ih _ _ h6⟩⟩

theorem lv_srch_mono_n (tg : List ℕ) : ∀ k n S, lv_srch tg k n S = true → lv_srch tg k (n + 1) S = true := by
  intro k
  induction k with
  | zero => intro n S h; simpa [lv_srch] using h
  | succ k ih =>
    intro n S h
    rw [lv_srch.eq_2] at h ⊢
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq,
      List.any_eq_true] at h ⊢
    rcases h with h | ⟨hm, p, hp, hb⟩
    · exact Or.inl h
    · refine Or.inr ⟨hm, p, hp, ?_⟩
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hb ⊢
      rcases hb with ⟨h1, (⟨h2, h3⟩ | ⟨⟨h4, h5⟩, h6⟩)⟩
      · exact ⟨h1, Or.inl ⟨h2, ih _ _ h3⟩⟩
      · refine ⟨h1, Or.inr ⟨⟨by omega, h5⟩, ?_⟩⟩
        have : n + 1 - 1 = (n - 1) + 1 := by omega
        rw [this]
        exact ih _ _ h6

theorem lv_miss_or (tg : List ℕ) (htg : tg.Nodup) (S p : ℕ) :
    lv_miss tg S ≤ lv_miss tg (S ||| (1 <<< p)) + 1 := by
  unfold lv_miss
  have hf : tg.filter (fun q => !(S ||| (1 <<< p)).testBit q) =
      (tg.filter (fun q => !S.testBit q)).filter (fun q => !decide (q = p)) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro q _
    simp only [Nat.testBit_or, lv_bit1]
    cases S.testBit q <;> by_cases hq : q = p <;> simp [hq]
  rw [hf]
  have hnd : (tg.filter (fun q => !S.testBit q)).Nodup := htg.filter _
  generalize tg.filter (fun q => !S.testBit q) = L at hnd ⊢
  have e : L.filter (fun q => !decide (q = p)) = L.erase p := by
    rw [hnd.erase_eq_filter]
    apply List.filter_congr
    intro q _
    by_cases hq : q = p <;> simp [hq]
  rw [e, List.length_erase]
  split <;> omega

theorem lv_step_ao (tg : List ℕ) (htg : tg.Nodup) (k n S p : ℕ) (hp : p < 32)
    (hc : (lv_ao S).testBit p = true) (h : lv_srch tg k n (S ||| (1 <<< p)) = true) :
    lv_srch tg (k + 1) n S = true := by
  by_cases hS : S.testBit p = true
  · have : S ||| (1 <<< p) = S := by
      apply Nat.eq_of_testBit_eq; intro q
      simp only [Nat.testBit_or, lv_bit1]
      by_cases hq : q = p
      · subst hq; simp [hS]
      · simp [hq]
    rw [this] at h
    exact lv_srch_mono_k tg _ _ _ h
  · have hm := lv_srch_miss tg _ _ _ h
    have hm2 := lv_miss_or tg htg S p
    rw [lv_srch.eq_2]
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
    refine Or.inr ⟨by omega, p, List.mem_range.2 hp, ?_⟩
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true']
    simp only [Bool.not_eq_true] at hS
    exact ⟨hS, Or.inl ⟨hc, h⟩⟩

theorem lv_step_nt (tg : List ℕ) (htg : tg.Nodup) (k n S p : ℕ) (hp : p < 32)
    (hc : (lv_nt S).testBit p = true) (h : lv_srch tg k n (S ||| (1 <<< p)) = true) :
    lv_srch tg (k + 1) (n + 1) S = true := by
  by_cases hS : S.testBit p = true
  · have : S ||| (1 <<< p) = S := by
      apply Nat.eq_of_testBit_eq; intro q
      simp only [Nat.testBit_or, lv_bit1]
      by_cases hq : q = p
      · subst hq; simp [hS]
      · simp [hq]
    rw [this] at h
    exact lv_srch_mono_n tg _ _ _ (lv_srch_mono_k tg _ _ _ h)
  · have hm := lv_srch_miss tg _ _ _ h
    have hm2 := lv_miss_or tg htg S p
    rw [lv_srch.eq_2]
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
    refine Or.inr ⟨by omega, p, List.mem_range.2 hp, ?_⟩
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq]
    simp only [Bool.not_eq_true] at hS
    refine ⟨hS, Or.inr ⟨⟨by omega, hc⟩, ?_⟩⟩
    simpa using h

theorem lv_srch_mono (tg : List ℕ) (k n S k' n' : ℕ) (hk : k ≤ k') (hn : n ≤ n')
    (h : lv_srch tg k n S = true) : lv_srch tg k' n' S = true := by
  have h1 : ∀ d, lv_srch tg (k + d) n S = true := by
    intro d
    induction d with
    | zero => simpa using h
    | succ d ih => exact lv_srch_mono_k tg _ _ _ ih
  have h2 : ∀ d, lv_srch tg k' (n + d) S = true := by
    intro d
    induction d with
    | zero => have := h1 (k' - k); rwa [show k + (k' - k) = k' by omega] at this
    | succ d ih => exact lv_srch_mono_n tg _ _ _ ih
  have := h2 (n' - n)
  rwa [show n + (n' - n) = n' by omega] at this

theorem lv_val_prefix (D : Circuit) (t w : ℕ) (hw : w < 6) :
    (D.wires (lv_lev t)).getD w false = (lv_lev t).getD w false := by
  rw [wires_W]
  exact W_prefix D.gates (lv_lev t) w (by rw [lv_lev_len]; exact hw)

theorem lv_val_gate (D : Circuit) (hRB : ReadsBack 6 D) (j : ℕ) (hj : j < D.gates.length) (t : ℕ) :
    (D.wires (lv_lev t)).getD (6 + j) false =
      (D.gates[j]).op.eval ((D.gates[j]).inputs.map fun i => (D.wires (lv_lev t)).getD i false) := by
  rw [wires_W]
  have h := W_gate D.gates (lv_lev t) j hj
  rw [lv_lev_len] at h
  rw [h]
  congr 1
  apply List.map_congr_left
  intro i hi
  have := hRB j hj i (by rw [gateAt_eq hj]; exact hi)
  simp [this]

theorem lv_pv_in (D : Circuit) (w : ℕ) (hw : w < 6) :
    lv_pv D w = t1_bits (fun t => (lv_lev t).getD w false) 5 := by
  unfold lv_pv
  apply t1_bits_ext
  intro k _
  exact lv_val_prefix D k w hw

theorem lv_pv4 (D : Circuit) : lv_pv D 4 = 0 := by
  rw [lv_pv_in D 4 (by omega)]; decide

theorem lv_pv5 (D : Circuit) : lv_pv D 5 = 31 := by
  rw [lv_pv_in D 5 (by omega)]; decide

theorem lv_gate_step (D : Circuit) (hF : FanInTwo D) (hRB : ReadsBack 6 D) (j : ℕ) (hj : j < D.gates.length) :
    let S := lv_Sm (lv_pv D) (6 + j)
    ((D.gates[j]).op ≠ GateOp.not → (lv_ao S).testBit (lv_pv D (6 + j)) = true) ∧
    ((D.gates[j]).op = GateOp.not → (lv_nt S).testBit (lv_pv D (6 + j)) = true) := by
  intro S
  have hg := hF _ (List.getElem_mem hj)
  obtain ⟨hop, hlen⟩ := hg
  have hrb : ∀ i ∈ (D.gates[j]).inputs, i < 6 + j := by
    intro i hi; exact hRB j hj i (by rw [gateAt_eq hj]; exact hi)
  have hS : ∀ w, w < 6 + j → S.testBit (lv_pv D w) = true := fun w hw => lv_Sm_mem _ _ w hw
  have h0 : S.testBit 0 = true := by rw [← lv_pv4 D]; exact hS 4 (by omega)
  have h31 : S.testBit 31 = true := by rw [← lv_pv5 D]; exact hS 5 (by omega)
  have hv : lv_pv D (6 + j) = t1_bits (fun t => (D.gates[j]).op.eval
      ((D.gates[j]).inputs.map fun i => (D.wires (lv_lev t)).getD i false)) 5 := by
    unfold lv_pv
    apply t1_bits_ext
    intro k _
    exact lv_val_gate D hRB j hj k
  generalize hgj : D.gates[j] = g at hop hlen hrb hv ⊢
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hins : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · -- no inputs
    rw [hins] at hv
    rcases hop with hop | hop | hop <;> rw [hop] at hv ⊢ <;>
      simp only [GateOp.eval, List.map_nil, List.all_nil, List.any_nil, List.headD_nil,
        Bool.not_false] at hv
    · refine ⟨fun _ => ?_, fun h => absurd h (by decide)⟩
      rw [hv, show t1_bits (fun _ => true) 5 = 31 by decide]; exact lv_ao_self _ _ h31
    · refine ⟨fun _ => ?_, fun h => absurd h (by decide)⟩
      rw [hv, show t1_bits (fun _ => false) 5 = 0 by decide]; exact lv_ao_self _ _ h0
    · refine ⟨fun h => absurd rfl h, fun _ => ?_⟩
      rw [hv, show t1_bits (fun _ => true) 5 = 31 ^^^ 0 by decide]
      exact lv_nt_comp _ _ (by omega) h0
  · -- one input
    rw [hins] at hv hrb
    have ha : a < 6 + j := hrb a (by simp)
    have hSa := hS a ha
    rcases hop with hop | hop | hop <;> rw [hop] at hv ⊢ <;>
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
        List.any_cons, List.any_nil, List.headD_cons, id, Bool.and_true, Bool.or_false] at hv
    · refine ⟨fun _ => ?_, fun h => absurd h (by decide)⟩
      rw [hv]; exact lv_ao_self _ _ hSa
    · refine ⟨fun _ => ?_, fun h => absurd h (by decide)⟩
      rw [hv]; exact lv_ao_self _ _ hSa
    · refine ⟨fun h => absurd rfl h, fun _ => ?_⟩
      rw [hv, gs_bits_not, show gs_full 5 = 31 by decide]
      exact lv_nt_comp _ _ (lv_pv_lt D a) hSa
  · -- two inputs
    rw [hins] at hv hrb
    have ha : a < 6 + j := hrb a (by simp)
    have hb : b < 6 + j := hrb b (by simp)
    have hSa := hS a ha
    have hSb := hS b hb
    rcases hop with hop | hop | hop <;> rw [hop] at hv ⊢ <;>
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
        List.any_cons, List.any_nil, List.headD_cons, id, Bool.and_true, Bool.or_false] at hv
    · refine ⟨fun _ => ?_, fun h => absurd h (by decide)⟩
      rw [hv, t1_bits_and]
      exact (lv_ao_pair _ _ _ (lv_pv_lt D a) (lv_pv_lt D b) hSa hSb).1
    · refine ⟨fun _ => ?_, fun h => absurd h (by decide)⟩
      rw [hv, t1_bits_or]
      exact (lv_ao_pair _ _ _ (lv_pv_lt D a) (lv_pv_lt D b) hSa hSb).2
    · refine ⟨fun h => absurd rfl h, fun _ => ?_⟩
      rw [hv, gs_bits_not, show gs_full 5 = 31 by decide]
      exact lv_nt_comp _ _ (lv_pv_lt D a) hSa
  · -- three or more inputs: impossible
    rw [hins] at hlen; simp at hlen

def lv_nn (D : Circuit) (j : ℕ) : ℕ :=
  ((D.gates.drop j).filter fun g => decide (g.op = GateOp.not)).length

theorem lv_nn_succ (D : Circuit) (j : ℕ) (hj : j < D.gates.length) :
    lv_nn D j = lv_nn D (j + 1) + (if (D.gates[j]).op = GateOp.not then 1 else 0) := by
  unfold lv_nn
  rw [List.drop_eq_getElem_cons hj, List.filter_cons]
  split <;> simp_all <;> omega

theorem lv_sound (tg : List ℕ) (htg : tg.Nodup) (D : Circuit) (hF : FanInTwo D) (hRB : ReadsBack 6 D)
    (htaps : ∀ T ∈ tg, ∃ w, w < 6 + D.gates.length ∧ lv_pv D w = T) :
    lv_srch tg D.gates.length (lv_nn D 0) (lv_Sm (lv_pv D) 6) = true := by
  have key : ∀ i, i ≤ D.gates.length →
      lv_srch tg i (lv_nn D (D.gates.length - i)) (lv_Sm (lv_pv D) (6 + (D.gates.length - i))) = true := by
    intro i
    induction i with
    | zero =>
      intro _
      simp only [lv_srch, beq_iff_eq, Nat.sub_zero]
      unfold lv_miss
      rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
      intro T hT
      obtain ⟨w, hw, hwT⟩ := htaps T hT
      rw [← hwT, lv_Sm_mem _ _ w hw]
      simp
    | succ i ih =>
      intro hi
      have ih' := ih (by omega)
      set j := D.gates.length - (i + 1) with hjdef
      have hj : j < D.gates.length := by omega
      have hj1 : D.gates.length - i = j + 1 := by omega
      rw [hj1, show 6 + (j + 1) = (6 + j) + 1 by omega] at ih'
      simp only [lv_Sm] at ih'
      have st := lv_gate_step D hF hRB j hj
      rw [lv_nn_succ D j hj]
      by_cases hnot : (D.gates[j]).op = GateOp.not
      · rw [if_pos hnot]
        exact lv_step_nt tg htg i _ _ _ (lv_pv_lt D _) (st.2 hnot) ih'
      · rw [if_neg hnot, Nat.add_zero]
        exact lv_step_ao tg htg i _ _ _ (lv_pv_lt D _) (st.1 hnot) ih'
  have := key D.gates.length le_rfl
  simpa using this

-- a tap reading the thermometer values of a 5-bit target has that profile
theorem lv_tap (D : Circuit) (w T : ℕ) (h : ∀ t : Fin 5, (D.wires (lv_lev t.val)).getD w false = T.testBit t.val) :
    lv_pv D w = t1_bits (fun t => T.testBit t) 5 := by
  unfold lv_pv
  apply t1_bits_ext
  intro k hk
  exact h ⟨k, hk⟩

theorem lv_fail : lv_srch [2, 10, 12] 5 2 (lv_Sm (fun w => t1_bits (fun t => (lv_lev t).getD w false) 5) 6) = false := by
  decide +kernel

theorem main_aux : ¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (6+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 6 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 5,
    let xs := (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (2 : Nat).testBit t.val ∧
    w.getD q.val false = (10 : Nat).testBit t.val ∧
    w.getD r.val false = (12 : Nat).testBit t.val) := by
  rintro ⟨D, p, q, r, hF, hRB, hN, hS, hall⟩
  have hp := lv_tap D p.val 2 (fun t => (hall t).1)
  have hq := lv_tap D q.val 10 (fun t => (hall t).2.1)
  have hr := lv_tap D r.val 12 (fun t => (hall t).2.2)
  have hs := lv_sound [2, 10, 12] (by decide) D hF hRB (by
    intro T hT
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hT
    rcases hT with rfl | rfl | rfl
    · first
      | exact ⟨p.val, p.isLt, by rw [hp]; decide⟩
      | exact ⟨q.val, q.isLt, by rw [hq]; decide⟩
      | exact ⟨r.val, r.isLt, by rw [hr]; decide⟩
    · first
      | exact ⟨p.val, p.isLt, by rw [hp]; decide⟩
      | exact ⟨q.val, q.isLt, by rw [hq]; decide⟩
      | exact ⟨r.val, r.isLt, by rw [hr]; decide⟩
    · first
      | exact ⟨p.val, p.isLt, by rw [hp]; decide⟩
      | exact ⟨q.val, q.isLt, by rw [hq]; decide⟩
      | exact ⟨r.val, r.isLt, by rw [hr]; decide⟩)
  rw [lv_Sm_congr _ _ 6 (fun w hw => lv_pv_in D w hw)] at hs
  have hm := lv_srch_mono _ _ _ _ 5 2 hS hN hs
  rw [lv_fail] at hm
  exact absurd hm (by decide)

end PEqualNP.Outside.L_meta_49878

theorem PEqualNP.Outside.L_meta_49878 : ¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (6+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 6 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 5,
    let xs := (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (2 : Nat).testBit t.val ∧
    w.getD q.val false = (10 : Nat).testBit t.val ∧
    w.getD r.val false = (12 : Nat).testBit t.val) :=
  PEqualNP.Outside.L_meta_49878.main_aux
