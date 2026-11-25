import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3280

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

-- FRAGMENT orreach    DEPENDS: fold mono
-- OR closures (PEqualNP.CleanedNonEdge.orStep / orSets / OrReaches), PEqualNP.TopForm.orIn, and the
-- value facts: a true gate makes every wire OR-reaching it true.
-- Exports (CNE = PEqualNP.CleanedNonEdge, TF = PEqualNP.TopForm):
--   wireVal_eq_val : CNE.wireVal n C w x = val C (List.ofFn x) w   (rfl)
--   gateVal_eq_val : PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j)   (rfl)
--   readVal_eq : CNE.readVal n C a w x = if w < n + a then val C (List.ofFn x) w else false   (rfl)
--   orSets_len gs cs : (gs.foldl (CNE.orStep n) cs).length = cs.length + gs.length
--   orSets_length : (CNE.orSets n C).length = C.gates.length
--   orSets_char gs : i in (gs.foldl (orStep n) []).getD j [] iff j < gs.length and (i = j or
--       (gs.getD j (OR of nothing)).op = or and exists w in its inputs, n <= w, w < n + j, i in (fold).getD (w - n) [])
--   orSets_mem_iff (hk : k < C.gates.length) : x in (orSets n C).getD k [] iff x = k or
--       ((gateAt C k).op = or and exists w in (gateAt C k).inputs, n <= w and w < n + k and x in (orSets n C).getD (w - n) [])
--   orReaches_iff : CNE.OrReaches n C (n + k) g iff k < C.gates.length and (g = k or
--       ((gateAt C k).op = or and exists i in (gateAt C k).inputs, i < n + k and OrReaches n C i g))
--   orReaches_self (hj : j < C.gates.length) : OrReaches n C (n + j) j
--   orReaches_step (j an OR gate, i in its inputs, i < n + j, OrReaches n C i g) : OrReaches n C (n + j) g
--   orReaches_bound : OrReaches n C w g -> n + g <= w and w < n + C.gates.length
--   orReaches_trans : OrReaches n C w (k) -> OrReaches n C (n + k) g -> OrReaches n C w g
--   reach_up (hx : x.length = n) (val C x (n + j) = true) : for all b, OrReaches n C b j -> val C x b = true
--   reach_up_wire : CNE.wireVal n C (n + j) x = true -> OrReaches n C b j -> CNE.wireVal n C b x = true
--   orIn_mem_filter : membership in Finset.filter with an arbitrary decidability proof
--   mem_orIn : i in TF.orIn n C w iff (i = w or exists k < C.gates.length, OrReaches n C w k and
--       (gateAt C k).op = or and i in (gateAt C k).inputs)
--   orIn_self (i : Fin n) : i in TF.orIn n C i
--   orIn_up (j an OR gate, i in its inputs, i < n + j) : a in orIn n C i -> a in orIn n C (n + j)
--   orIn_reach : OrReaches n C b k -> a in orIn n C (n + k) -> a in orIn n C b
--   orIn_val (hx : x.length = n) : a in orIn n C b -> val C x a = true -> val C x b = true
-- Use: orReaches_iff to unfold one level, reach_up / orIn_val to push truth up OR chains.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem wireVal_eq_val (n : ℕ) (C : Circuit) (w : ℕ) (x : Fin n → Bool) :
    PEqualNP.CleanedNonEdge.wireVal n C w x = val C (List.ofFn x) w := rfl

theorem gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

theorem readVal_eq (n : ℕ) (C : Circuit) (a w : ℕ) (x : Fin n → Bool) :
    PEqualNP.CleanedNonEdge.readVal n C a w x =
      if w < n + a then val C (List.ofFn x) w else false := rfl

theorem orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [PEqualNP.CleanedNonEdge.orStep]
    omega

theorem orSets_length (n : ℕ) (C : Circuit) :
    (PEqualNP.CleanedNonEdge.orSets n C).length = C.gates.length := by
  unfold PEqualNP.CleanedNonEdge.orSets
  rw [orSets_len]; simp

theorem orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (PEqualNP.CleanedNonEdge.orStep n (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD k [] =
          (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD k [] := by
      intro k hk
      simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (PEqualNP.CleanedNonEdge.orStep n
            (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD (w - n) []) := by
          simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (PEqualNP.CleanedNonEdge.orStep n
            (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (PEqualNP.CleanedNonEdge.orStep n
          (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD j [] = [] := by
        simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

theorem orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
        x ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD (w - n) []) := by
  have h := orSets_char n C.gates x k
  unfold PEqualNP.CleanedNonEdge.orSets gateAt
  rw [h]
  constructor
  · rintro ⟨_, h3⟩; exact h3
  · intro h3; exact ⟨hk, h3⟩

theorem orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + k) g ↔ k < C.gates.length ∧
      (g = k ∨ ((gateAt C k).op = GateOp.or ∧
        ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ PEqualNP.CleanedNonEdge.OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold PEqualNP.CleanedNonEdge.OrReaches PEqualNP.CleanedNonEdge.orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

theorem orReaches_self (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + j) j :=
  (orReaches_iff n C j j).mpr ⟨hj, Or.inl rfl⟩

theorem orReaches_step (n : ℕ) (C : Circuit) (j i g : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : PEqualNP.CleanedNonEdge.OrReaches n C i g) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + j) g :=
  (orReaches_iff n C j g).mpr ⟨hj, Or.inr ⟨hop, i, hi, hlt, h⟩⟩

theorem orReaches_bound (n : ℕ) (C : Circuit) (g : ℕ) :
    ∀ w : ℕ, PEqualNP.CleanedNonEdge.OrReaches n C w g → n + g ≤ w ∧ w < n + C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hr
    have hnw : n ≤ w := hr.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp hr
    rcases h3 with h3 | ⟨_, i, _, hlt, hri⟩
    · omega
    · have := ih i hlt hri
      omega

theorem orReaches_trans (n : ℕ) (C : Circuit) (k g : ℕ) (hkg : PEqualNP.CleanedNonEdge.OrReaches n C (n + k) g) :
    ∀ w : ℕ, PEqualNP.CleanedNonEdge.OrReaches n C w k → PEqualNP.CleanedNonEdge.OrReaches n C w g := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hr
    have hnw : n ≤ w := hr.1
    obtain ⟨m, rfl⟩ : ∃ m, w = n + m := ⟨w - n, by omega⟩
    obtain ⟨hm, h3⟩ := (orReaches_iff n C m k).mp hr
    rcases h3 with h3 | ⟨hop, i, hi, hlt, hri⟩
    · rw [← h3]; exact hkg
    · exact orReaches_step n C m i g hm hop hi hlt (ih i hlt hri)

theorem reach_up (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n) (j : ℕ)
    (hv : val C x (n + j) = true) :
    ∀ b : ℕ, PEqualNP.CleanedNonEdge.OrReaches n C b j → val C x b = true := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro hr
    have hnb : n ≤ b := hr.1
    obtain ⟨k, rfl⟩ : ∃ k, b = n + k := ⟨b - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k j).mp hr
    rcases h3 with h3 | ⟨hop, i, hi, hlt, hri⟩
    · rw [← h3]
      exact hv
    · exact (val_or hx hk hop).mpr ⟨i, hi, hlt, ih i hlt hri⟩

theorem reach_up_wire (n : ℕ) (C : Circuit) (x : Fin n → Bool) (j b : ℕ)
    (hv : PEqualNP.CleanedNonEdge.wireVal n C (n + j) x = true)
    (hr : PEqualNP.CleanedNonEdge.OrReaches n C b j) :
    PEqualNP.CleanedNonEdge.wireVal n C b x = true :=
  reach_up n C (List.ofFn x) (by simp) j hv b hr

theorem orIn_mem_filter {α : Type} (p : α → Prop) (d : DecidablePred p) (s : Finset α) (a : α) :
    a ∈ @Finset.filter α p d s ↔ a ∈ s ∧ p a :=
  @Finset.mem_filter α p d s a

theorem mem_orIn (n : ℕ) (C : Circuit) (w : ℕ) (i : Fin n) :
    i ∈ PEqualNP.TopForm.orIn n C w ↔ ((i : ℕ) = w ∨ ∃ k < C.gates.length,
      PEqualNP.CleanedNonEdge.OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧
        (i : ℕ) ∈ (gateAt C k).inputs) := by
  unfold PEqualNP.TopForm.orIn
  exact ⟨fun h => ((orIn_mem_filter _ _ _ _).1 h).2,
    fun h => (orIn_mem_filter _ _ _ _).2 ⟨Finset.mem_univ _, h⟩⟩

theorem orIn_self (n : ℕ) (C : Circuit) (i : Fin n) : i ∈ PEqualNP.TopForm.orIn n C i :=
  (mem_orIn n C i i).mpr (Or.inl rfl)

theorem orIn_up (n : ℕ) (C : Circuit) (j i : ℕ) (a : Fin n) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : a ∈ PEqualNP.TopForm.orIn n C i) : a ∈ PEqualNP.TopForm.orIn n C (n + j) := by
  rw [mem_orIn] at h ⊢
  right
  rcases h with h | ⟨k, hk, hr, hopk, hin⟩
  · exact ⟨j, hj, orReaches_self n C j hj, hop, by rw [h]; exact hi⟩
  · exact ⟨k, hk, orReaches_step n C j i k hj hop hi hlt hr, hopk, hin⟩

theorem orIn_reach (n : ℕ) (C : Circuit) (b k : ℕ) (a : Fin n)
    (hr : PEqualNP.CleanedNonEdge.OrReaches n C b k)
    (h : a ∈ PEqualNP.TopForm.orIn n C (n + k)) : a ∈ PEqualNP.TopForm.orIn n C b := by
  rw [mem_orIn] at h ⊢
  right
  rcases h with h | ⟨m, hm, hrm, hopm, hin⟩
  · exfalso; have := a.isLt; omega
  · exact ⟨m, hm, orReaches_trans n C k m hrm b hr, hopm, hin⟩

theorem orIn_val (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n) (a : Fin n) (b : ℕ)
    (h : a ∈ PEqualNP.TopForm.orIn n C b) (hv : val C x a = true) : val C x b = true := by
  rw [mem_orIn] at h
  rcases h with hw | ⟨k, hk, hr, hop, hin⟩
  · rw [← hw]; exact hv
  · refine reach_up n C x hx k ?_ b hr
    refine (val_or hx hk hop).mpr ⟨a.val, hin, ?_, hv⟩
    have := a.isLt
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

-- FRAGMENT factor    DEPENDS: fold mono orreach cones
-- Factor substitution (PEqualNP.FactorSubst: substReads, orClosure, frontier, liveGates, liveSize).
-- Abbreviations used in this header: F-set = PEqualNP.FactorSubst, C2 = F-set.substReads C n c sigma, O = F-set.orClosure n C c,
-- rho k i = if i = n + c then sigma k else i, RD = PEqualNP.TopForm.readers n C c, OR = CleanedNonEdge.OrReaches.
-- Exports:
--   fs_len : C2.gates.length = C.gates.length ;  fs_output : C2.output = C.output (rfl)
--   fs_gateAt k : gateAt C2 k = (op of gateAt C k, inputs mapped by rho k)   (every k)
--   fs_mem_O : w in O iff w < len, w ne c, OR n C (n + w) c ;  fs_O_gt : w in O -> c < w ;  fs_O_or : w in O -> op w = or
--   fs_mem_readers : r in RD iff r < len and n + c in inputs r
--   fs_mem_frontier : k in F-set.frontier n C c iff k < len, k ne c, k not in O, exists w in insert c O, n + w in inputs k
--   fs_ab (IsAO2, inputs c = [a, b]) : a < n + c and b < n + c ;  fs_notO_lt (v <= n + c) : v is no wire of O
--   fs_sig (k reads n + c) : k in RD, c < k, sigma k < n + c, sigma k = a or b
--   fs_rb : C2 reads back (gate k reads wires below n + k) ;  fs_cv : val C x (n + c) = (val a and val b)
--   fs_val (k < len) : val C2 x (n + k) = op k evaluated on (inputs k).map (fun i => val C2 x (rho k i))
--   def fsH1 n C c a b sigma x : hypothesis H1 of the factor lemma at one input list x (val C x instead of wireVal)
--   fs_H1_local : H1 as stated in rows 3222/3280/3297 (wireVal, all inputs) -> fsH1 at List.ofFn z
--   def fsP : wire invariant (wire not in O: same value in C2; wire of O: C <= C2 and C2 true -> C true or a reader
--       r of c with OR v r has val (sigma r) true)
--   fs_all (IsAO2, c an AND of [a, b], sigma reads in {a, b}, fsH1 at x) : for all v, fsP .. x v
--   fs_gateVal_eq (same, H1 as in the rows) : k < len, k ne c, k not in O -> gateVal n C2 k z = gateVal n C k z
--   fs_cone : InCone n C2 j m -> InCone n C j m and j ne c
--   fs_live_sub (output ne n + c) : F-set.liveGates n C2 subset (F-set.liveGates n C).erase c
--   fs_count (c live, output ne n + c) : F-set.liveSize n C2 + 1 <= F-set.liveSize n C
-- Use: fs_gateVal_eq and fs_count give the two conclusions of the factor substitution rows; for a variant of H1
-- prove fsH1 for it and call fs_all directly (the frontier step is fs_front_core).

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem fs_len (C : Circuit) (n c : ℕ) (sigma : ℕ → ℕ) :
    (PEqualNP.FactorSubst.substReads C n c sigma).gates.length = C.gates.length := by
  simp [PEqualNP.FactorSubst.substReads]

theorem fs_output (C : Circuit) (n c : ℕ) (sigma : ℕ → ℕ) :
    (PEqualNP.FactorSubst.substReads C n c sigma).output = C.output := rfl

theorem fs_gateAt (C : Circuit) (n c : ℕ) (sigma : ℕ → ℕ) (k : ℕ) :
    gateAt (PEqualNP.FactorSubst.substReads C n c sigma) k =
      ⟨(gateAt C k).op, (gateAt C k).inputs.map fun i => if i = n + c then sigma k else i⟩ := by
  unfold gateAt PEqualNP.FactorSubst.substReads
  simp only [List.getD_eq_getElem?_getD, List.getElem?_mapIdx]
  cases C.gates[k]? <;> simp

theorem fs_mem_O (n : ℕ) (C : Circuit) (c w : ℕ) :
    w ∈ PEqualNP.FactorSubst.orClosure n C c ↔
      w < C.gates.length ∧ w ≠ c ∧ PEqualNP.CleanedNonEdge.OrReaches n C (n + w) c := by
  unfold PEqualNP.FactorSubst.orClosure
  simp only [orIn_mem_filter, Finset.mem_range]

theorem fs_mem_readers (n : ℕ) (C : Circuit) (c r : ℕ) :
    r ∈ PEqualNP.TopForm.readers n C c ↔ r < C.gates.length ∧ n + c ∈ (gateAt C r).inputs := by
  unfold PEqualNP.TopForm.readers
  simp only [orIn_mem_filter, Finset.mem_range]

theorem fs_mem_frontier (n : ℕ) (C : Circuit) (c k : ℕ) :
    k ∈ PEqualNP.FactorSubst.frontier n C c ↔ k < C.gates.length ∧ k ≠ c ∧
      k ∉ PEqualNP.FactorSubst.orClosure n C c ∧
      ∃ w ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), n + w ∈ (gateAt C k).inputs := by
  unfold PEqualNP.FactorSubst.frontier
  simp only [orIn_mem_filter, Finset.mem_range]

theorem fs_O_gt (n : ℕ) (C : Circuit) (c w : ℕ) (h : w ∈ PEqualNP.FactorSubst.orClosure n C c) :
    c < w := by
  rw [fs_mem_O] at h
  have := (orReaches_bound n C c (n + w) h.2.2).1
  omega

theorem fs_O_or (n : ℕ) (C : Circuit) (c w : ℕ) (h : w ∈ PEqualNP.FactorSubst.orClosure n C c) :
    (gateAt C w).op = GateOp.or := by
  rw [fs_mem_O] at h
  obtain ⟨_, hne, hr⟩ := h
  rcases (orReaches_iff n C w c).1 hr with ⟨_, h1 | h1⟩
  · exact absurd h1.symm hne
  · exact h1.1

theorem fs_ab (n : ℕ) (C : Circuit) (c a b : ℕ) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hc : c < C.gates.length) (hcin : (gateAt C c).inputs = [a, b]) : a < n + c ∧ b < n + c :=
  ⟨isAO2_rb hAO hc (by rw [hcin]; simp), isAO2_rb hAO hc (by rw [hcin]; simp)⟩

theorem fs_notO_lt (n : ℕ) (C : Circuit) (c v : ℕ) (hv : v < n + c + 1) :
    ∀ w ∈ PEqualNP.FactorSubst.orClosure n C c, v ≠ n + w := by
  intro w hw h
  have := fs_O_gt n C c w hw
  omega

theorem fs_sig (n : ℕ) (C : Circuit) (c a b : ℕ) (sigma : ℕ → ℕ)
    (hAO : PEqualNP.TopForm.IsAO2 n C) (hc : c < C.gates.length)
    (hcin : (gateAt C c).inputs = [a, b])
    (hsig : ∀ r ∈ PEqualNP.TopForm.readers n C c, sigma r = a ∨ sigma r = b)
    (k : ℕ) (hk : k < C.gates.length) (hkc : n + c ∈ (gateAt C k).inputs) :
    k ∈ PEqualNP.TopForm.readers n C c ∧ c < k ∧ sigma k < n + c ∧
      (sigma k = a ∨ sigma k = b) := by
  have hr : k ∈ PEqualNP.TopForm.readers n C c := (fs_mem_readers n C c k).2 ⟨hk, hkc⟩
  have h1 := isAO2_rb hAO hk hkc
  have h2 := fs_ab n C c a b hAO hc hcin
  refine ⟨hr, by omega, ?_, hsig k hr⟩
  rcases hsig k hr with h | h <;> omega

theorem fs_rb (n : ℕ) (C : Circuit) (c a b : ℕ) (sigma : ℕ → ℕ)
    (hAO : PEqualNP.TopForm.IsAO2 n C) (hc : c < C.gates.length)
    (hcin : (gateAt C c).inputs = [a, b])
    (hsig : ∀ r ∈ PEqualNP.TopForm.readers n C c, sigma r = a ∨ sigma r = b)
    (k : ℕ) (hk : k < C.gates.length) :
    ∀ i ∈ (gateAt (PEqualNP.FactorSubst.substReads C n c sigma) k).inputs, i < n + k := by
  intro i hi
  rw [fs_gateAt] at hi
  obtain ⟨j, hj, hji⟩ := List.mem_map.1 hi
  rw [← hji]
  have hjk := isAO2_rb hAO hk hj
  by_cases hjc : j = n + c
  · rw [if_pos hjc]
    have h3 := fs_sig n C c a b sigma hAO hc hcin hsig k hk (by rw [← hjc]; exact hj)
    omega
  · rw [if_neg hjc]
    exact hjk

theorem fs_cv (n : ℕ) (C : Circuit) (c a b : ℕ) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hc : c < C.gates.length) (hcop : (gateAt C c).op = GateOp.and)
    (hcin : (gateAt C c).inputs = [a, b]) (x : List Bool) (hx : x.length = n) :
    val C x (n + c) = (val C x a && val C x b) := by
  rw [and_val n C hAO x hx c hc hcop, hcin]
  try rfl

theorem fs_val (n : ℕ) (C : Circuit) (c a b : ℕ) (sigma : ℕ → ℕ)
    (hAO : PEqualNP.TopForm.IsAO2 n C) (hc : c < C.gates.length)
    (hcin : (gateAt C c).inputs = [a, b])
    (hsig : ∀ r ∈ PEqualNP.TopForm.readers n C c, sigma r = a ∨ sigma r = b)
    (x : List Bool) (hx : x.length = n) (k : ℕ) (hk : k < C.gates.length) :
    val (PEqualNP.FactorSubst.substReads C n c sigma) x (n + k) =
      (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
        val (PEqualNP.FactorSubst.substReads C n c sigma) x (if i = n + c then sigma k else i)) := by
  rw [val_gate_rb hx (by rw [fs_len]; exact hk) (fs_rb n C c a b sigma hAO hc hcin hsig k hk),
    fs_gateAt]
  show (gateAt C k).op.eval (((gateAt C k).inputs.map fun i => if i = n + c then sigma k else i).map
      fun i => val (PEqualNP.FactorSubst.substReads C n c sigma) x i) = _
  rw [List.map_map]
  try rfl

abbrev fsH1 (n : ℕ) (C : Circuit) (c a b : ℕ) (sigma : ℕ → ℕ) (x : List Bool) : Prop :=
  ∀ g ∈ PEqualNP.FactorSubst.frontier n C c, (gateAt C g).op = GateOp.and →
    ∀ u y : ℕ, ((gateAt C g).inputs = [u, y] ∨ (gateAt C g).inputs = [y, u]) →
      (∃ w ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), u = n + w) →
        (∀ w' ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), y ≠ n + w') ∧
          ∀ r ∈ PEqualNP.TopForm.readers n C c,
            (r = g ∨ PEqualNP.CleanedNonEdge.OrReaches n C u r) →
              (sigma r = b → val C x y = true → val C x a = true) ∧
              (sigma r = a → val C x y = true → val C x b = true)

theorem fs_H1_local (n : ℕ) (C : Circuit) (c a b : ℕ) (sigma : ℕ → ℕ)
    (hF : ∀ g ∈ PEqualNP.FactorSubst.frontier n C c, (gateAt C g).op = GateOp.and →
      ∀ u y : ℕ, ((gateAt C g).inputs = [u, y] ∨ (gateAt C g).inputs = [y, u]) →
        (∃ w ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), u = n + w) →
          (∀ w' ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), y ≠ n + w') ∧
            ∀ r ∈ PEqualNP.TopForm.readers n C c,
              (r = g ∨ PEqualNP.CleanedNonEdge.OrReaches n C u r) →
                (sigma r = b → ∀ x : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C y x = true →
                  PEqualNP.CleanedNonEdge.wireVal n C a x = true) ∧
                (sigma r = a → ∀ x' : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C y x' = true →
                  PEqualNP.CleanedNonEdge.wireVal n C b x' = true))
    (z : Fin n → Bool) : fsH1 n C c a b sigma (List.ofFn z) := by
  intro g hg hop u y hin hu
  obtain ⟨h1, h2⟩ := hF g hg hop u y hin hu
  exact ⟨h1, fun r hr hrr => ⟨fun hs hy => (h2 r hr hrr).1 hs z hy,
    fun hs hy => (h2 r hr hrr).2 hs z hy⟩⟩

abbrev fsP (n : ℕ) (C : Circuit) (c : ℕ) (sigma : ℕ → ℕ) (x : List Bool) (v : ℕ) : Prop :=
  ((∀ w ∈ PEqualNP.FactorSubst.orClosure n C c, v ≠ n + w) →
      val (PEqualNP.FactorSubst.substReads C n c sigma) x v = val C x v) ∧
  (∀ w ∈ PEqualNP.FactorSubst.orClosure n C c, v = n + w →
      (val C x v = true → val (PEqualNP.FactorSubst.substReads C n c sigma) x v = true) ∧
      (val (PEqualNP.FactorSubst.substReads C n c sigma) x v = true → val C x v = true ∨
        ∃ r ∈ PEqualNP.TopForm.readers n C c,
          PEqualNP.CleanedNonEdge.OrReaches n C v r ∧ val C x (sigma r) = true))

theorem fs_bool1 (A B Y : Bool) (h : Y = true → B = true) : (A && Y) = ((A && B) && Y) := by
  cases A <;> cases B <;> cases Y <;> simp_all

theorem fs_bool2 (A B Y : Bool) (h : Y = true → A = true) : (B && Y) = ((A && B) && Y) := by
  cases A <;> cases B <;> cases Y <;> simp_all

theorem fs_bool3 (U U' Y : Bool) (h1 : U = true → U' = true) (h2 : U' = true → Y = true → U = true) :
    (U' && Y) = (U && Y) := by
  cases U <;> cases U' <;> cases Y <;> simp_all

theorem fs_step_O (n : ℕ) (C : Circuit) (c a b : ℕ) (sigma : ℕ → ℕ)
    (hAO : PEqualNP.TopForm.IsAO2 n C) (hc : c < C.gates.length)
    (hcop : (gateAt C c).op = GateOp.and) (hcin : (gateAt C c).inputs = [a, b])
    (hsig : ∀ r ∈ PEqualNP.TopForm.readers n C c, sigma r = a ∨ sigma r = b)
    (x : List Bool) (hx : x.length = n) (k : ℕ)
    (hkO : k ∈ PEqualNP.FactorSubst.orClosure n C c)
    (IH : ∀ v < n + k, fsP n C c sigma x v) :
    (val C x (n + k) = true → val (PEqualNP.FactorSubst.substReads C n c sigma) x (n + k) = true) ∧
    (val (PEqualNP.FactorSubst.substReads C n c sigma) x (n + k) = true → val C x (n + k) = true ∨
      ∃ r ∈ PEqualNP.TopForm.readers n C c,
        PEqualNP.CleanedNonEdge.OrReaches n C (n + k) r ∧ val C x (sigma r) = true) := by
  have hk : k < C.gates.length := ((fs_mem_O n C c k).1 hkO).1
  have hop := fs_O_or n C c k hkO
  have hv := fs_val n C c a b sigma hAO hc hcin hsig x hx k hk
  have hv0 := val_gate_rb (C := C) hx hk (fun i hi => isAO2_rb hAO hk hi)
  rw [hop] at hv hv0
  have hcv := fs_cv n C c a b hAO hc hcop hcin x hx
  rw [hv, hv0]
  simp only [eval_or_iff]
  constructor
  · rintro ⟨i, hi, hvi⟩
    refine ⟨i, hi, ?_⟩
    have hik := isAO2_rb hAO hk hi
    by_cases hic : i = n + c
    · rw [if_pos hic]
      obtain ⟨_, _, hslt, hs⟩ :=
        fs_sig n C c a b sigma hAO hc hcin hsig k hk (by rw [← hic]; exact hi)
      rw [(IH (sigma k) (by omega)).1 (fs_notO_lt n C c _ (by omega))]
      rw [hic, hcv, Bool.and_eq_true] at hvi
      rcases hs with h | h
      · rw [h]; exact hvi.1
      · rw [h]; exact hvi.2
    · rw [if_neg hic]
      by_cases hiO : ∃ w ∈ PEqualNP.FactorSubst.orClosure n C c, i = n + w
      · obtain ⟨w, hw, hiw⟩ := hiO
        exact ((IH i hik).2 w hw hiw).1 hvi
      · push_neg at hiO
        rw [(IH i hik).1 hiO]; exact hvi
  · rintro ⟨i, hi, hvi⟩
    have hik := isAO2_rb hAO hk hi
    by_cases hic : i = n + c
    · rw [if_pos hic] at hvi
      obtain ⟨hr, _, hslt, _⟩ :=
        fs_sig n C c a b sigma hAO hc hcin hsig k hk (by rw [← hic]; exact hi)
      rw [(IH (sigma k) (by omega)).1 (fs_notO_lt n C c _ (by omega))] at hvi
      exact Or.inr ⟨k, hr, orReaches_self n C k hk, hvi⟩
    · rw [if_neg hic] at hvi
      by_cases hiO : ∃ w ∈ PEqualNP.FactorSubst.orClosure n C c, i = n + w
      · obtain ⟨w, hw, hiw⟩ := hiO
        rcases ((IH i hik).2 w hw hiw).2 hvi with h | ⟨r, hr, hreach, hsr⟩
        · exact Or.inl ⟨i, hi, h⟩
        · refine Or.inr ⟨r, hr, ?_, hsr⟩
          have hwk : PEqualNP.CleanedNonEdge.OrReaches n C (n + k) w :=
            orReaches_step n C k i w hk hop hi hik
              (by rw [hiw]; exact orReaches_self n C w ((fs_mem_O n C c w).1 hw).1)
          exact orReaches_trans n C w r (by rw [← hiw]; exact hreach) (n + k) hwk
      · push_neg at hiO
        rw [(IH i hik).1 hiO] at hvi
        exact Or.inl ⟨i, hi, hvi⟩

theorem fs_front_core (n : ℕ) (C : Circuit) (c a b : ℕ) (sigma : ℕ → ℕ)
    (hAO : PEqualNP.TopForm.IsAO2 n C) (hc : c < C.gates.length)
    (hcop : (gateAt C c).op = GateOp.and) (hcin : (gateAt C c).inputs = [a, b])
    (hsig : ∀ r ∈ PEqualNP.TopForm.readers n C c, sigma r = a ∨ sigma r = b)
    (x : List Bool) (hx : x.length = n) (hF : fsH1 n C c a b sigma x)
    (k : ℕ) (hk : k < C.gates.length) (hfront : k ∈ PEqualNP.FactorSubst.frontier n C c)
    (hop : (gateAt C k).op = GateOp.and) (u y : ℕ)
    (hin : (gateAt C k).inputs = [u, y] ∨ (gateAt C k).inputs = [y, u])
    (hu : ∃ w ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), u = n + w)
    (IH : ∀ v < n + k, fsP n C c sigma x v) :
    val (PEqualNP.FactorSubst.substReads C n c sigma) x (n + k) = val C x (n + k) := by
  obtain ⟨hyO, hR⟩ := hF k hfront hop u y hin hu
  have huin : u ∈ (gateAt C k).inputs := by rcases hin with h | h <;> rw [h] <;> simp
  have hyin : y ∈ (gateAt C k).inputs := by rcases hin with h | h <;> rw [h] <;> simp
  have hulk := isAO2_rb hAO hk huin
  have hylk := isAO2_rb hAO hk hyin
  have hyc : y ≠ n + c := hyO c (Finset.mem_insert_self c _)
  have hyv : val (PEqualNP.FactorSubst.substReads C n c sigma) x y = val C x y :=
    (IH y hylk).1 (fun w hw => hyO w (Finset.mem_insert_of_mem hw))
  have hcv := fs_cv n C c a b hAO hc hcop hcin x hx
  have e1 : val (PEqualNP.FactorSubst.substReads C n c sigma) x (n + k) =
      (val (PEqualNP.FactorSubst.substReads C n c sigma) x (if u = n + c then sigma k else u) &&
        val (PEqualNP.FactorSubst.substReads C n c sigma) x y) := by
    rw [fs_val n C c a b sigma hAO hc hcin hsig x hx k hk]
    rcases hin with h | h
    · rw [h, hop]
      simp only [List.map_cons, List.map_nil, eval_and2, if_neg hyc]
    · rw [h, hop]
      simp only [List.map_cons, List.map_nil, eval_and2, if_neg hyc]
      exact Bool.and_comm _ _
  have e2 : val C x (n + k) = (val C x u && val C x y) := by
    rw [val_gate_rb (C := C) hx hk (fun i hi => isAO2_rb hAO hk hi)]
    rcases hin with h | h
    · rw [h, hop]
      simp only [List.map_cons, List.map_nil, eval_and2]
    · rw [h, hop]
      simp only [List.map_cons, List.map_nil, eval_and2]
      exact Bool.and_comm _ _
  rw [e1, e2, hyv]
  obtain ⟨w, hw, huw⟩ := hu
  rcases Finset.mem_insert.1 hw with hwc | hwO
  · have huc : u = n + c := by rw [huw, hwc]
    rw [if_pos huc]
    obtain ⟨hr, _, hslt, hs⟩ :=
      fs_sig n C c a b sigma hAO hc hcin hsig k hk (by rw [← huc]; exact huin)
    rw [(IH (sigma k) (by omega)).1 (fs_notO_lt n C c _ (by omega)), huc, hcv]
    have hRk := hR k hr (Or.inl rfl)
    rcases hs with h | h
    · rw [h]; exact fs_bool1 _ _ _ (hRk.2 h)
    · rw [h]; exact fs_bool2 _ _ _ (hRk.1 h)
  · have hcw := fs_O_gt n C c w hwO
    have huc : u ≠ n + c := by omega
    rw [if_neg huc]
    have hP := (IH u hulk).2 w hwO huw
    apply fs_bool3 _ _ _ hP.1
    intro hU' hY
    rcases hP.2 hU' with h | ⟨r, hr, hreach, hsr⟩
    · exact h
    · have hRr := hR r hr (Or.inr hreach)
      have hcT : val C x (n + c) = true := by
        rw [hcv]
        rcases hsig r hr with hs | hs
        · rw [hs] at hsr
          simp [hsr, hRr.2 hs hY]
        · rw [hs] at hsr
          simp [hsr, hRr.1 hs hY]
      exact reach_up n C x hx c hcT u (by rw [huw]; exact ((fs_mem_O n C c w).1 hwO).2.2)

theorem fs_front (n : ℕ) (C : Circuit) (c a b : ℕ) (sigma : ℕ → ℕ)
    (hAO : PEqualNP.TopForm.IsAO2 n C) (hc : c < C.gates.length)
    (hcop : (gateAt C c).op = GateOp.and) (hcin : (gateAt C c).inputs = [a, b])
    (hsig : ∀ r ∈ PEqualNP.TopForm.readers n C c, sigma r = a ∨ sigma r = b)
    (x : List Bool) (hx : x.length = n) (hF : fsH1 n C c a b sigma x)
    (k : ℕ) (hk : k < C.gates.length) (hkO : k ∉ PEqualNP.FactorSubst.orClosure n C c)
    (hkc : k ≠ c)
    (hfr : ∃ w ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), n + w ∈ (gateAt C k).inputs)
    (IH : ∀ v < n + k, fsP n C c sigma x v) :
    val (PEqualNP.FactorSubst.substReads C n c sigma) x (n + k) = val C x (n + k) := by
  have hfront : k ∈ PEqualNP.FactorSubst.frontier n C c :=
    (fs_mem_frontier n C c k).2 ⟨hk, hkc, hkO, hfr⟩
  obtain ⟨w, hw, hwi⟩ := hfr
  have hmem : gateAt C k ∈ C.gates := gateAt_mem hk
  have hreach : PEqualNP.CleanedNonEdge.OrReaches n C (n + w) c := by
    rcases Finset.mem_insert.1 hw with h | h
    · rw [h]; exact orReaches_self n C c hc
    · exact ((fs_mem_O n C c w).1 h).2.2
  have hop : (gateAt C k).op = GateOp.and := by
    rcases hAO.1 _ hmem with h | h
    · exact h
    · exact absurd ((fs_mem_O n C c k).2 ⟨hk, hkc,
        orReaches_step n C k (n + w) c hk h hwi (isAO2_rb hAO hk hwi) hreach⟩) hkO
  obtain ⟨p, q, hpq⟩ := List.length_eq_two.1 (isAO2_len hAO hmem)
  rw [hpq] at hwi
  rcases List.mem_cons.1 hwi with h | h
  · exact fs_front_core n C c a b sigma hAO hc hcop hcin hsig x hx hF k hk hfront hop (n + w) q
      (Or.inl (by rw [hpq, h])) ⟨w, hw, rfl⟩ IH
  · have h2 := List.mem_singleton.1 h
    exact fs_front_core n C c a b sigma hAO hc hcop hcin hsig x hx hF k hk hfront hop (n + w) p
      (Or.inr (by rw [hpq, h2])) ⟨w, hw, rfl⟩ IH

theorem fs_step_out (n : ℕ) (C : Circuit) (c a b : ℕ) (sigma : ℕ → ℕ)
    (hAO : PEqualNP.TopForm.IsAO2 n C) (hc : c < C.gates.length)
    (hcop : (gateAt C c).op = GateOp.and) (hcin : (gateAt C c).inputs = [a, b])
    (hsig : ∀ r ∈ PEqualNP.TopForm.readers n C c, sigma r = a ∨ sigma r = b)
    (x : List Bool) (hx : x.length = n) (hF : fsH1 n C c a b sigma x)
    (k : ℕ) (hk : k < C.gates.length) (hkO : k ∉ PEqualNP.FactorSubst.orClosure n C c)
    (IH : ∀ v < n + k, fsP n C c sigma x v) :
    val (PEqualNP.FactorSubst.substReads C n c sigma) x (n + k) = val C x (n + k) := by
  by_cases hfr : ∃ w ∈ insert c (PEqualNP.FactorSubst.orClosure n C c),
      n + w ∈ (gateAt C k).inputs
  · by_cases hkc : k = c
    · exfalso
      obtain ⟨w, hw, hwi⟩ := hfr
      have h1 := isAO2_rb hAO hk hwi
      rcases Finset.mem_insert.1 hw with h | h
      · omega
      · have := fs_O_gt n C c w h
        omega
    · exact fs_front n C c a b sigma hAO hc hcop hcin hsig x hx hF k hk hkO hkc hfr IH
  · push_neg at hfr
    rw [fs_val n C c a b sigma hAO hc hcin hsig x hx k hk,
      val_gate_rb (C := C) hx hk (fun i hi => isAO2_rb hAO hk hi)]
    congr 1
    apply List.map_congr_left
    intro i hi
    have hic : i ≠ n + c := fun h => hfr c (Finset.mem_insert_self c _) (h ▸ hi)
    rw [if_neg hic]
    exact (IH i (isAO2_rb hAO hk hi)).1
      (fun w hw h => hfr w (Finset.mem_insert_of_mem hw) (h ▸ hi))

theorem fs_step (n : ℕ) (C : Circuit) (c a b : ℕ) (sigma : ℕ → ℕ)
    (hAO : PEqualNP.TopForm.IsAO2 n C) (hc : c < C.gates.length)
    (hcop : (gateAt C c).op = GateOp.and) (hcin : (gateAt C c).inputs = [a, b])
    (hsig : ∀ r ∈ PEqualNP.TopForm.readers n C c, sigma r = a ∨ sigma r = b)
    (x : List Bool) (hx : x.length = n) (hF : fsH1 n C c a b sigma x)
    (k : ℕ) (hk : k < C.gates.length) (IH : ∀ v < n + k, fsP n C c sigma x v) :
    fsP n C c sigma x (n + k) := by
  refine ⟨fun hnot => ?_, fun w hw hwk => ?_⟩
  · have hkO : k ∉ PEqualNP.FactorSubst.orClosure n C c := fun h => hnot k h rfl
    exact fs_step_out n C c a b sigma hAO hc hcop hcin hsig x hx hF k hk hkO IH
  · have hwk2 : w = k := by omega
    subst hwk2
    exact fs_step_O n C c a b sigma hAO hc hcop hcin hsig x hx w hw IH

theorem fs_all (n : ℕ) (C : Circuit) (c a b : ℕ) (sigma : ℕ → ℕ)
    (hAO : PEqualNP.TopForm.IsAO2 n C) (hc : c < C.gates.length)
    (hcop : (gateAt C c).op = GateOp.and) (hcin : (gateAt C c).inputs = [a, b])
    (hsig : ∀ r ∈ PEqualNP.TopForm.readers n C c, sigma r = a ∨ sigma r = b)
    (x : List Bool) (hx : x.length = n) (hF : fsH1 n C c a b sigma x) :
    ∀ v, fsP n C c sigma x v := by
  intro v
  refine Nat.strong_induction_on v ?_
  intro v IH
  by_cases hv1 : v < n
  · refine ⟨fun _ => ?_, fun w _ h => by omega⟩
    rw [val_input hx hv1, val_input hx hv1]
  · by_cases hv2 : n + C.gates.length ≤ v
    · refine ⟨fun _ => ?_, fun w hw h => ?_⟩
      · rw [val_ge hx hv2,
          val_ge (C := PEqualNP.FactorSubst.substReads C n c sigma) hx (by rw [fs_len]; exact hv2)]
      · have := ((fs_mem_O n C c w).1 hw).1
        omega
    · obtain ⟨k, rfl⟩ : ∃ k, v = n + k := ⟨v - n, by omega⟩
      exact fs_step n C c a b sigma hAO hc hcop hcin hsig x hx hF k (by omega) IH

theorem fs_gateVal_eq (n : ℕ) (C : Circuit) (c a b : ℕ) (sigma : ℕ → ℕ)
    (hAO : PEqualNP.TopForm.IsAO2 n C) (hc : c < C.gates.length)
    (hcop : (gateAt C c).op = GateOp.and) (hcin : (gateAt C c).inputs = [a, b])
    (hsig : ∀ r ∈ PEqualNP.TopForm.readers n C c, sigma r = a ∨ sigma r = b)
    (hF : ∀ z : Fin n → Bool, fsH1 n C c a b sigma (List.ofFn z))
    (k : ℕ) (hkc : k ≠ c) (hkO : k ∉ PEqualNP.FactorSubst.orClosure n C c) (z : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n (PEqualNP.FactorSubst.substReads C n c sigma) k z =
      PEqualNP.EdgeOwnership.gateVal n C k z := by
  have hall := fs_all n C c a b sigma hAO hc hcop hcin hsig (List.ofFn z) (by simp) (hF z) (n + k)
  exact hall.1 (fun w hw h => hkO (by
    have hwk : w = k := by omega
    rw [← hwk]; exact hw))

theorem fs_cone (n : ℕ) (C : Circuit) (c a b : ℕ) (sigma : ℕ → ℕ)
    (hAO : PEqualNP.TopForm.IsAO2 n C) (hc : c < C.gates.length)
    (hcin : (gateAt C c).inputs = [a, b])
    (hsig : ∀ r ∈ PEqualNP.TopForm.readers n C c, sigma r = a ∨ sigma r = b) :
    ∀ m j, PEqualNP.EdgeOwnership.InCone n (PEqualNP.FactorSubst.substReads C n c sigma) j m →
      PEqualNP.EdgeOwnership.InCone n C j m ∧ j ≠ c := by
  intro m
  refine Nat.strong_induction_on m ?_
  intro m IH j hj
  rw [inCone_iff] at hj
  obtain ⟨hm, k, hkm, hkin, hjk⟩ := hj
  rw [fs_len] at hm
  rw [fs_gateAt] at hkin
  obtain ⟨i, hi, hik⟩ := List.mem_map.1 hkin
  have hk : PEqualNP.EdgeOwnership.InCone n C k m ∧ k ≠ c := by
    by_cases hic : i = n + c
    · rw [if_pos hic] at hik
      obtain ⟨_, hcm, hslt, hs⟩ :=
        fs_sig n C c a b sigma hAO hc hcin hsig m hm (by rw [← hic]; exact hi)
      have hkc : n + k ∈ (gateAt C c).inputs := by
        rw [hcin, ← hik]
        rcases hs with h | h <;> rw [h] <;> simp
      have hkc' : k < c := by omega
      exact ⟨inCone_trans n C k c (inCone_of_read n C k c hc hkc' hkc) m
        (inCone_of_read n C c m hm hcm (by rw [← hic]; exact hi)), by omega⟩
    · rw [if_neg hic] at hik
      refine ⟨inCone_of_read n C k m hm hkm (by rw [← hik]; exact hi), ?_⟩
      intro hkc
      exact hic (by rw [hik, hkc])
  rcases hjk with h | h
  · rw [h]; exact hk
  · obtain ⟨h1, h2⟩ := IH k hkm j h
    exact ⟨inCone_trans n C j k h1 m hk.1, h2⟩

theorem fs_live_sub (n : ℕ) (C : Circuit) (c a b : ℕ) (sigma : ℕ → ℕ)
    (hAO : PEqualNP.TopForm.IsAO2 n C) (hc : c < C.gates.length)
    (hcin : (gateAt C c).inputs = [a, b])
    (hsig : ∀ r ∈ PEqualNP.TopForm.readers n C c, sigma r = a ∨ sigma r = b)
    (hout : C.output ≠ n + c) :
    PEqualNP.FactorSubst.liveGates n (PEqualNP.FactorSubst.substReads C n c sigma) ⊆
      (PEqualNP.FactorSubst.liveGates n C).erase c := by
  intro j hj
  unfold PEqualNP.FactorSubst.liveGates at hj ⊢
  rw [Finset.mem_erase]
  simp only [orIn_mem_filter, Finset.mem_range] at hj ⊢
  rw [fs_len, fs_output] at hj
  obtain ⟨hjl, hno, hjo⟩ := hj
  rcases hjo with h | h
  · exact ⟨by omega, hjl, hno, Or.inl h⟩
  · obtain ⟨h1, h2⟩ := fs_cone n C c a b sigma hAO hc hcin hsig _ j h
    exact ⟨h2, hjl, hno, Or.inr h1⟩

theorem fs_count (n : ℕ) (C : Circuit) (c a b : ℕ) (sigma : ℕ → ℕ)
    (hAO : PEqualNP.TopForm.IsAO2 n C) (hc : c < C.gates.length)
    (hcin : (gateAt C c).inputs = [a, b])
    (hsig : ∀ r ∈ PEqualNP.TopForm.readers n C c, sigma r = a ∨ sigma r = b)
    (hout : C.output ≠ n + c) (hlive : c ∈ PEqualNP.FactorSubst.liveGates n C) :
    PEqualNP.FactorSubst.liveSize n (PEqualNP.FactorSubst.substReads C n c sigma) + 1 ≤
      PEqualNP.FactorSubst.liveSize n C := by
  unfold PEqualNP.FactorSubst.liveSize
  have h1 := Finset.card_le_card (fs_live_sub n C c a b sigma hAO hc hcin hsig hout)
  have h2 := Finset.card_erase_of_mem hlive
  have h3 := Finset.card_pos.2 ⟨c, hlive⟩
  omega

theorem main_aux : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (c a b : ℕ) (sigma : ℕ → ℕ), PEqualNP.TopForm.IsAO2 n C → c < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C c).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt C c).inputs = [a, b] → (∀ r ∈ PEqualNP.TopForm.readers n C c, sigma r = a ∨ sigma r = b) → (∀ g ∈ PEqualNP.FactorSubst.frontier n C c, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ u y : ℕ, ((PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs = [u, y] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs = [y, u]) → (∃ w ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), u = n + w) → (∀ w' ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), y ≠ n + w') ∧ ∀ r ∈ PEqualNP.TopForm.readers n C c, (r = g ∨ PEqualNP.CleanedNonEdge.OrReaches n C u r) → (sigma r = b → ∀ x : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C y x = true → PEqualNP.CleanedNonEdge.wireVal n C a x = true) ∧ (sigma r = a → ∀ x' : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C y x' = true → PEqualNP.CleanedNonEdge.wireVal n C b x' = true)) → (∀ g2 ∈ PEqualNP.FactorSubst.frontier n C c, ∀ u2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C g2).inputs, ∀ r1 ∈ PEqualNP.TopForm.readers n C c, ∀ r2 ∈ PEqualNP.TopForm.readers n C c, PEqualNP.CleanedNonEdge.OrReaches n C u2 r1 → PEqualNP.CleanedNonEdge.OrReaches n C u2 r2 → sigma r1 = sigma r2) → (∀ w3 ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), C.output ≠ n + w3) → c ∈ PEqualNP.FactorSubst.liveGates n C → (∀ k < C.gates.length, k ≠ c → k ∉ PEqualNP.FactorSubst.orClosure n C c → ∀ z : Fin n → Bool, PEqualNP.EdgeOwnership.gateVal n (PEqualNP.FactorSubst.substReads C n c sigma) k z = PEqualNP.EdgeOwnership.gateVal n C k z) ∧ PEqualNP.FactorSubst.liveSize n (PEqualNP.FactorSubst.substReads C n c sigma) + 1 ≤ PEqualNP.FactorSubst.liveSize n C := by
  intro n C c a b sigma hAO hc hcop hcin hsig hF _ hout hlive
  have hout' : C.output ≠ n + c := hout c (Finset.mem_insert_self c _)
  exact ⟨fun k _ hkc hkO z => fs_gateVal_eq n C c a b sigma hAO hc hcop hcin hsig
    (fs_H1_local n C c a b sigma hF) k hkc hkO z,
    fs_count n C c a b sigma hAO hc hcin hsig hout' hlive⟩

end PEqualNP.Outside.L_meta_3280

theorem PEqualNP.Outside.L_meta_3280 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (c a b : ℕ) (sigma : ℕ → ℕ), PEqualNP.TopForm.IsAO2 n C → c < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C c).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt C c).inputs = [a, b] → (∀ r ∈ PEqualNP.TopForm.readers n C c, sigma r = a ∨ sigma r = b) → (∀ g ∈ PEqualNP.FactorSubst.frontier n C c, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ u y : ℕ, ((PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs = [u, y] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs = [y, u]) → (∃ w ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), u = n + w) → (∀ w' ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), y ≠ n + w') ∧ ∀ r ∈ PEqualNP.TopForm.readers n C c, (r = g ∨ PEqualNP.CleanedNonEdge.OrReaches n C u r) → (sigma r = b → ∀ x : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C y x = true → PEqualNP.CleanedNonEdge.wireVal n C a x = true) ∧ (sigma r = a → ∀ x' : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C y x' = true → PEqualNP.CleanedNonEdge.wireVal n C b x' = true)) → (∀ g2 ∈ PEqualNP.FactorSubst.frontier n C c, ∀ u2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C g2).inputs, ∀ r1 ∈ PEqualNP.TopForm.readers n C c, ∀ r2 ∈ PEqualNP.TopForm.readers n C c, PEqualNP.CleanedNonEdge.OrReaches n C u2 r1 → PEqualNP.CleanedNonEdge.OrReaches n C u2 r2 → sigma r1 = sigma r2) → (∀ w3 ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), C.output ≠ n + w3) → c ∈ PEqualNP.FactorSubst.liveGates n C → (∀ k < C.gates.length, k ≠ c → k ∉ PEqualNP.FactorSubst.orClosure n C c → ∀ z : Fin n → Bool, PEqualNP.EdgeOwnership.gateVal n (PEqualNP.FactorSubst.substReads C n c sigma) k z = PEqualNP.EdgeOwnership.gateVal n C k z) ∧ PEqualNP.FactorSubst.liveSize n (PEqualNP.FactorSubst.substReads C n c sigma) + 1 ≤ PEqualNP.FactorSubst.liveSize n C :=
  PEqualNP.Outside.L_meta_3280.main_aux
