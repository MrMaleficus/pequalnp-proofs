import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4383

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

def q_val (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def q_run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [q_val g w]) w

theorem q_run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    q_run (g :: gs) w = q_run gs (w ++ [q_val g w]) := rfl

def q_rn (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

theorem q_getD_last (y : List Bool) (v : Bool) : (y ++ [v]).getD y.length false = v := by
  simp

theorem q_run_prefix (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (q_run gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [q_run_cons, ih (w ++ [q_val g w]) i (by rw [List.length_append]; omega)]
    exact List.getD_append w [q_val g w] false i hi

theorem q_bool_flow (t b b' c c' : Bool)
    (hb : b = t → b' = t) (hc : c = t → c' = t) :
    ((b && c) = t → (b' && c') = t) ∧ ((b || c) = t → (b' || c') = t) := by
  cases t <;> cases b <;> cases b' <;> cases c <;> cases c' <;> simp_all

theorem q_gate_flow (t : Bool) (op : GateOp) (hop : op = .and ∨ op = .or)
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
      exact (q_bool_flow t _ _ _ _ hi ih').1
    · simp only [GateOp.eval, List.map_cons, List.any_cons, id_eq] at ih' ⊢
      exact (q_bool_flow t _ _ _ _ hi ih').2

theorem q_mono (t : Bool) (a b : ℕ) (gs : List Gate) : ∀ (w v : List Bool),
    w.length = v.length →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    (∀ k < gs.length, a ∈ (gs.getD k ⟨GateOp.or, []⟩).inputs →
      a < w.length + k ∧ b < w.length + k) →
    ((q_run gs w).getD a false = t → (q_run gs w).getD b false = t) →
    (∀ i, w.getD i false = t → v.getD i false = t) →
    ∀ i, (q_run gs w).getD i false = t →
      (q_run (gs.map (q_rn (fun ii => if ii = a then b else ii))) v).getD i false = t := by
  induction gs with
  | nil =>
    intro w v _ _ _ _ hf i h
    exact hf i h
  | cons g gs ih =>
    intro w v hl hops hr hab hf
    rw [List.map_cons, q_run_cons, q_run_cons]
    rw [q_run_cons] at hab
    have hside : ∀ i ∈ g.inputs, (fun i => w.getD i false) i = t →
        (fun i => v.getD (if i = a then b else i) false) i = t := by
      intro i hi
      show w.getD i false = t → v.getD (if i = a then b else i) false = t
      by_cases hia : i = a
      · rw [hia] at hi ⊢
        rw [if_pos rfl]
        obtain ⟨hk1, hk2⟩ := hr 0 (by rw [List.length_cons]; omega)
          (by simpa [List.getD_cons_zero] using hi)
        intro h1
        have h2 : (q_run gs (w ++ [q_val g w])).getD a false = t := by
          rw [q_run_prefix gs _ a (by rw [List.length_append]; omega),
            List.getD_append w [q_val g w] false a (by omega)]
          exact h1
        have h3 := hab h2
        rw [q_run_prefix gs _ b (by rw [List.length_append]; omega),
          List.getD_append w [q_val g w] false b (by omega)] at h3
        exact hf b h3
      · rw [if_neg hia]
        exact hf i
    have hstep : q_val g w = t → q_val (q_rn (fun ii => if ii = a then b else ii) g) v = t := by
      have h0 := q_gate_flow t g.op (hops g List.mem_cons_self) g.inputs
        (fun i => w.getD i false) (fun i => v.getD (if i = a then b else i) false) hside
      simpa only [q_val, q_rn, List.map_map, Function.comp_def] using h0
    refine ih (w ++ [q_val g w]) (v ++ [q_val (q_rn (fun ii => if ii = a then b else ii) g) v])
      (by simp [hl]) (fun x hx => hops x (List.mem_cons_of_mem _ hx)) ?_ hab ?_
    · intro k hk hm
      obtain ⟨h1, h2⟩ := hr (k + 1) (by rw [List.length_cons]; omega)
        (by simpa [List.getD_cons_succ] using hm)
      rw [List.length_append, List.length_singleton]
      exact ⟨by omega, by omega⟩
    · intro i hi
      by_cases h1 : i < w.length
      · rw [List.getD_append w [q_val g w] false i h1] at hi
        rw [List.getD_append v _ false i (by omega)]
        exact hf i hi
      · by_cases h2 : i = w.length
        · subst h2
          rw [q_getD_last] at hi
          rw [hl, q_getD_last]
          exact hstep hi
        · have h3 : (w ++ [q_val g w]).length ≤ i := by
            rw [List.length_append, List.length_singleton]; omega
          have h4 : (v ++ [q_val (q_rn (fun ii => if ii = a then b else ii) g) v]).length ≤ i := by
            rw [List.length_append, List.length_singleton]; omega
          rw [List.getD_eq_default _ _ h3] at hi
          rw [List.getD_eq_default _ _ h4]
          exact hi


theorem subst_eq (C : Circuit) (n j y : ℕ) :
    PEqualNP.FactorSubst.substReads C n j (fun _ => y) =
      ({ gates := C.gates.map (q_rn (fun ii => if ii = n + j then y else ii)),
         output := C.output } : Circuit) := by
  unfold PEqualNP.FactorSubst.substReads
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [q_rn]

theorem main_aux : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (j w y : ℕ) (v : Fin n),
  PEqualNP.TopForm.IsAO2 n C → j < C.gates.length →
  (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
  ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [w, ↑v] ∨
    (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [↑v, w]) →
  (∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x =
      decide (∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true)) →
  y < n + j →
  (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD y false =
      (x v && decide (∃ u : Fin n, G.Adj u v ∧ x u = true ∧
        (C.wires (List.ofFn (fun i => decide (i = u ∨ i = v)))).getD w false = true))) →
  ∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n (PEqualNP.FactorSubst.substReads C n j (fun _ => y)) x =
      decide (∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true) := by
  intro n G _ C j w y v hAO hj hop hin hf hyj hy
  have hAOO : PEqualNP.EdgeOwnership.AndOrOnly C := andOrOnly_of_isAO2 hAO
  have hops : ∀ gg ∈ C.gates, gg.op = GateOp.and ∨ gg.op = GateOp.or := hAOO
  have hgv : ∀ z : Fin n → Bool, val C (List.ofFn z) (n + j)
      = (val C (List.ofFn z) w && z v) := by
    intro z
    rw [and_val n C hAO _ (by simp) j hj hop]
    rcases hin with h | h <;> rw [h] <;> simp [val_ofFn, Bool.and_comm]
  have hyv : ∀ z : Fin n → Bool, val C (List.ofFn z) y = (z v && decide (∃ u : Fin n, G.Adj u v ∧
      z u = true ∧ val C (List.ofFn (fun i => decide (i = u ∨ i = v))) w = true)) :=
    fun z => hy z
  have hr : ∀ (z : Fin n → Bool), ∀ k < C.gates.length,
      n + j ∈ (C.gates.getD k ⟨GateOp.or, []⟩).inputs →
      n + j < (List.ofFn z).length + k ∧ y < (List.ofFn z).length + k := by
    intro z k hk hm
    have h1 : n + j < n + k := isAO2_rb hAO hk hm
    rw [List.length_ofFn]
    exact ⟨h1, by omega⟩
  have key : ∀ (t : Bool) (z x : Fin n → Bool), (∀ i : Fin n, z i = t → x i = t) →
      (val C (List.ofFn z) (n + j) = t → val C (List.ofFn z) y = t) →
      val C (List.ofFn z) C.output = t →
      (q_run (C.gates.map (q_rn (fun ii => if ii = n + j then y else ii))) (List.ofFn x)).getD
        C.output false = t := by
    intro t z x hzx hga ho
    refine q_mono t (n + j) y C.gates (List.ofFn z) (List.ofFn x) (by simp) hops (hr z) hga ?_
      C.output ho
    intro i hi
    by_cases hin' : i < n
    · rw [ofFn_getD z i hin'] at hi
      rw [ofFn_getD x i hin']
      exact hzx _ hi
    · rw [ofFn_getD_ge z i (by omega)] at hi
      rw [ofFn_getD_ge x i (by omega)]
      exact hi
  have hfx : ∀ z : Fin n → Bool, val C (List.ofFn z) C.output
      = decide (∃ a b : Fin n, G.Adj a b ∧ z a = true ∧ z b = true) := by
    intro z
    rw [← hf z]
    exact (circuitFun_val n C z).symm
  intro x
  rw [subst_eq]
  show (q_run (C.gates.map (q_rn (fun ii => if ii = n + j then y else ii))) (List.ofFn x)).getD
      C.output false = _
  by_cases hE : ∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true
  · rw [decide_eq_true hE]
    obtain ⟨a, b, hab, hxa, hxb⟩ := hE
    obtain ⟨z, hz⟩ : ∃ z : Fin n → Bool, ∀ i, z i = decide (i = a ∨ i = b) := ⟨_, fun i => rfl⟩
    have hza : z a = true := by rw [hz]; simp
    have hzb : z b = true := by rw [hz]; simp
    have hzx : ∀ i, z i = true → x i = true := by
      intro i hi
      rw [hz] at hi
      simp only [decide_eq_true_eq] at hi
      rcases hi with h | h
      · rw [h]; exact hxa
      · rw [h]; exact hxb
    have hoz : val C (List.ofFn z) C.output = true := by
      rw [hfx z]
      exact decide_eq_true ⟨a, b, hab, hza, hzb⟩
    refine key true z x hzx ?_ hoz
    intro hg
    rw [hgv z] at hg
    rw [hyv z]
    have hzv : z v = true := by
      cases h : z v
      · rw [h, Bool.and_false] at hg
        exact hg
      · rfl
    have hzw : val C (List.ofFn z) w = true := by
      cases h : val C (List.ofFn z) w
      · rw [h, Bool.false_and] at hg
        exact hg
      · rfl
    rw [hzv, Bool.true_and]
    apply decide_eq_true
    have hv' : v = a ∨ v = b := by
      rw [hz] at hzv
      simpa using hzv
    rcases hv' with hva | hvb
    · refine ⟨b, by rw [hva]; exact hab.symm, hzb, ?_⟩
      have hzz : (fun i => decide (i = b ∨ i = v)) = z := by
        funext i
        show decide (i = b ∨ i = v) = z i
        rw [hz, hva]
        exact decide_eq_decide.mpr or_comm
      rw [hzz]
      exact hzw
    · refine ⟨a, by rw [hvb]; exact hab, hza, ?_⟩
      have hzz : (fun i => decide (i = a ∨ i = v)) = z := by
        funext i
        show decide (i = a ∨ i = v) = z i
        rw [hz, hvb]
      rw [hzz]
      exact hzw
  · rw [decide_eq_false hE]
    have hox : val C (List.ofFn x) C.output = false := by
      rw [hfx x]
      exact decide_eq_false hE
    refine key false x x (fun i h => h) ?_ hox
    intro hg
    rw [hgv x] at hg
    rw [hyv x]
    cases hxv : x v
    · rfl
    · rw [Bool.true_and]
      apply decide_eq_false
      rintro ⟨u, _, hxu, hw⟩
      have hmono : val C (List.ofFn x) w = true := mono n C hAOO _ x (fun i hi => by
        simp only [decide_eq_true_eq] at hi
        rcases hi with h | h
        · rw [h]; exact hxu
        · rw [h]; exact hxv) w hw
      rw [hmono, hxv] at hg
      simp at hg

end PEqualNP.Outside.L_meta_4383

theorem PEqualNP.Outside.L_meta_4383 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (j w y : ℕ) (v : Fin n),
  PEqualNP.TopForm.IsAO2 n C → j < C.gates.length →
  (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
  ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [w, ↑v] ∨
    (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [↑v, w]) →
  (∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x =
      decide (∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true)) →
  y < n + j →
  (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD y false =
      (x v && decide (∃ u : Fin n, G.Adj u v ∧ x u = true ∧
        (C.wires (List.ofFn (fun i => decide (i = u ∨ i = v)))).getD w false = true))) →
  ∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n (PEqualNP.FactorSubst.substReads C n j (fun _ => y)) x =
      decide (∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true) :=
  PEqualNP.Outside.L_meta_4383.main_aux
