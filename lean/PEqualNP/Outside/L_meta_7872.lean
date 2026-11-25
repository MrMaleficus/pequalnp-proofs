import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7872

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

-- FRAGMENT elimvar    DEPENDS: fold
-- Gate elimination of one variable: fixing input v := b in a FanInTwo circuit (AND, OR, NOT, fan-in <= 2) and
-- propagating constants (the Stat simplifier: each old wire becomes a constant Sum.inl c or a new wire Sum.inr j)
-- removes every gate that reads v, so the restricted function has a circuit with at least one gate less.
-- Exports:
--   elim_one_var (v : Fin m) (b) (HasCircuitSize m F s) (F depends on v somewhere) (F with v := b is not constant) :
--       1 <= s and HasCircuitSize m (fun x => F (Function.update x v b)) (s - 1)
--   ev_elim_last n C (FanInTwo C) (C.eval (ofFn x ++ [false]) not constant in x) (some x: C.eval (ofFn x ++ [true]) ne
--       C.eval (ofFn x ++ [false])) : exists D, FanInTwo D, D.size < C.size, D.eval (ofFn x ++ [false]) = C.eval (ofFn x ++ [false])
--   ev_W_cons : W (g :: gs) w = W gs (w ++ [value of g]) (rfl) ;  ev_getD_snoc_lt / _eq / _ne : getD on l ++ [x] (any type)
--   def ev_OkGate g : op in and/or/not and fan-in <= 2 (FanInTwo per gate) ;  ev_NOkGate : also NOT has fan-in <= 1
--   def ev_normGate (NOT keeps its first input) ;  ev_normGate_eval, ev_normGate_nok, ev_W_norm : W (gs.map ev_normGate) w = W gs w
--   def ev_statVal w (Sum.inl c => c, Sum.inr j => w.getD j false) ;  def ev_statValid m s : a Sum.inr j has j < m
--   def ev_simp op m ins : (optional new gate, stat of the result) for AND/OR/NOT over stats (ev_simpAnd/Or/Not)
--   ev_simp_ok : new gates are ev_OkGate ;  ev_simp_sound : value preserved ;  ev_simp_none_of_const : a constant read gives no gate
--   ev_simp_and_false / ev_simp_or_true / ev_simp_not_const : explicit constant cases
--   def ev_elimStep m acc g / ev_elimPass m gs acc : the pass (acc = stats of old wires, new gate list)
--   ev_elimPass_cons/_append/_nil/_fst_len/_getD_lt/_ok ;  ev_elimPass_len : new length <= old + gs.length
--   ev_elimPass_len_lt (const wire k read by a gate of gs) : new + 1 <= ;  ev_elimPass_len_two (read by >= 2 gates) : new + 2 <=
--   def ev_Inv m w_in w_old acc : the invariant (stats valid and evaluate to the old wires) ;  ev_Inv_step, ev_Inv_pass
--   def ev_initVar m v b : stats of the inputs with v := b ;  ev_Inv_initVar ;  ev_ofFn_getD_lt (any type)
--   ev_W_agree : two wire lists agreeing outside B stay so if no gate reads B
--   ev_ofFn_snoc_eq : ofFn (Fin.snoc x b) = ofFn x ++ [b] ;  ev_eval_update_snoc
-- Use: elim_one_var for HasCircuitSize rows (2535); ev_elim_last for rows on C.eval (ofFn x ++ [b]) (2315);
-- for a two-gate saving reuse the proof of elim_one_var with ev_elimPass_len_two.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem ev_W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem ev_getD_snoc_lt {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

theorem ev_getD_snoc_eq {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
    (l ++ [x]).getD i d = x := by
  subst hi
  simp [List.getD]

theorem ev_getD_snoc_ne {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i ≠ l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  by_cases hlt : i < l.length
  · exact ev_getD_snoc_lt l x d i hlt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

def ev_OkGate (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def ev_NOkGate (g : Gate) : Prop :=
  ev_OkGate g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

def ev_normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem ev_normGate_eval (g : Gate) (F : ℕ → Bool) :
    (ev_normGate g).op.eval ((ev_normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [ev_normGate]
  cases inputs <;> simp [GateOp.eval]

theorem ev_normGate_nok (g : Gate) (h : ev_OkGate g) : ev_NOkGate (ev_normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this
    exact ⟨⟨Or.inl rfl, hlen⟩, by simp [ev_normGate]⟩
  · have : op = GateOp.or := h
    subst this
    exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [ev_normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩
    · simp [ev_normGate]
    · simp [ev_normGate]

theorem ev_W_norm (gs : List Gate) (w : List Bool) :
    W (gs.map ev_normGate) w = W gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, ev_W_cons, ev_W_cons, ev_normGate_eval, ih]

def ev_statVal (w : List Bool) : Bool ⊕ ℕ → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def ev_statValid (m : ℕ) : Bool ⊕ ℕ → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def ev_simpNot (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def ev_simpAnd (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def ev_simpOr (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def ev_simp (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    Option Gate × (Bool ⊕ ℕ) :=
  match op with
  | GateOp.and => ev_simpAnd m ins
  | GateOp.or => ev_simpOr m ins
  | GateOp.not => ev_simpNot m ins
  | _ => (none, Sum.inl false)

theorem ev_simp_ok (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    ∀ g ∈ (ev_simp op m ins).1, ev_OkGate g := by
  intro g hg
  cases op <;> simp only [ev_simp] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [ev_simpAnd] at hg
    subst hg; simp [ev_OkGate]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [ev_simpOr] at hg
    subst hg; simp [ev_OkGate]
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [ev_simpNot] at hg
    subst hg; simp [ev_OkGate]
  · simp at hg
  · simp at hg

theorem ev_simp_none_of_const (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (ev_simp op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [ev_simp, ev_simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [ev_simp, ev_simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [ev_simp, ev_simpNot]

theorem ev_simp_and_false (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hlen : ins.length ≤ 2) (hf : Sum.inl false ∈ ins) :
    ev_simp GateOp.and m ins = (none, Sum.inl false) := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
  · simp at hf
  · cases a <;> simp_all [ev_simp, ev_simpAnd]
  · cases a with
    | inl c =>
      cases b with
      | inl d => cases c <;> cases d <;> simp_all [ev_simp, ev_simpAnd]
      | inr j => cases c <;> simp_all [ev_simp, ev_simpAnd]
    | inr i =>
      cases b with
      | inl d => cases d <;> simp_all [ev_simp, ev_simpAnd]
      | inr j => simp at hf
  · simp at hlen

theorem ev_simp_not_const (m : ℕ) (c : Bool) :
    ev_simp GateOp.not m [Sum.inl c] = (none, Sum.inl (!c)) := rfl

theorem ev_simp_sound (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List (Bool ⊕ ℕ)) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, ev_statValid w.length s) :
    ev_statValid (w.length + (ev_simp op w.length ins).1.toList.length)
      (ev_simp op w.length ins).2 ∧
    ev_statVal (W (ev_simp op w.length ins).1.toList w)
      (ev_simp op w.length ins).2 = op.eval (ins.map (ev_statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [ev_simp, ev_simpAnd, ev_statValid, ev_statVal, GateOp.eval]
    · cases a <;> simp_all [ev_simp, ev_simpAnd, ev_statValid, ev_statVal, GateOp.eval, W, step]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp_all [ev_simp, ev_simpAnd, ev_statValid, ev_statVal, GateOp.eval]
        | inr j => cases c <;> simp_all [ev_simp, ev_simpAnd, ev_statValid, ev_statVal, GateOp.eval, W, step]
      | inr i =>
        cases b with
        | inl d => cases d <;> simp_all [ev_simp, ev_simpAnd, ev_statValid, ev_statVal, GateOp.eval, W, step]
        | inr j => simp_all [ev_simp, ev_simpAnd, ev_statValid, ev_statVal, GateOp.eval, W, step]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [ev_simp, ev_simpOr, ev_statValid, ev_statVal, GateOp.eval]
    · cases a <;> simp_all [ev_simp, ev_simpOr, ev_statValid, ev_statVal, GateOp.eval, W, step]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp_all [ev_simp, ev_simpOr, ev_statValid, ev_statVal, GateOp.eval]
        | inr j => cases c <;> simp_all [ev_simp, ev_simpOr, ev_statValid, ev_statVal, GateOp.eval, W, step]
      | inr i =>
        cases b with
        | inl d => cases d <;> simp_all [ev_simp, ev_simpOr, ev_statValid, ev_statVal, GateOp.eval, W, step]
        | inr j => simp_all [ev_simp, ev_simpOr, ev_statValid, ev_statVal, GateOp.eval, W, step]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [ev_simp, ev_simpNot, ev_statValid, ev_statVal, GateOp.eval]
    · cases a <;> simp_all [ev_simp, ev_simpNot, ev_statValid, ev_statVal, GateOp.eval, W, step]

def ev_elimStep (m : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  let r := ev_simp g.op (m + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
  (acc.1 ++ [r.2], acc.2 ++ r.1.toList)

def ev_elimPass (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  gs.foldl (ev_elimStep m) acc

theorem ev_elimPass_cons (m : ℕ) (g : Gate) (gs : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) :
    ev_elimPass m (g :: gs) acc = ev_elimPass m gs (ev_elimStep m acc g) := rfl

theorem ev_elimPass_append (m : ℕ) (gs₁ gs₂ : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) :
    ev_elimPass m (gs₁ ++ gs₂) acc = ev_elimPass m gs₂ (ev_elimPass m gs₁ acc) := by
  induction gs₁ generalizing acc with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, ev_elimPass_cons, ih]

theorem ev_elimPass_fst_len (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    (ev_elimPass m gs acc).1.length = acc.1.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [ev_elimPass]
  | cons g gs ih =>
    rw [ev_elimPass_cons, ih]
    simp [ev_elimStep]
    omega

theorem ev_elimPass_getD_lt (m k : ℕ) (d : Bool ⊕ ℕ) (gs : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) (hk : k < acc.1.length) :
    (ev_elimPass m gs acc).1.getD k d = acc.1.getD k d := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    rw [ev_elimPass_cons, ih _ (by simp [ev_elimStep]; omega)]
    exact ev_getD_snoc_lt _ _ _ _ hk

theorem ev_toList_len_le {α : Type*} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem ev_elimPass_ok (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (h : ∀ g ∈ acc.2, ev_OkGate g) : ∀ g ∈ (ev_elimPass m gs acc).2, ev_OkGate g := by
  induction gs generalizing acc with
  | nil => exact h
  | cons g gs ih =>
    rw [ev_elimPass_cons]
    apply ih
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact ev_simp_ok _ _ _ g' (by simpa using h1)

theorem ev_elimPass_len (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    (ev_elimPass m gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [ev_elimPass]
  | cons g gs ih =>
    rw [ev_elimPass_cons, List.length_cons]
    have h1 := ih (ev_elimStep m acc g)
    have h2 : (ev_elimStep m acc g).2.length ≤ acc.2.length + 1 := by
      simp only [ev_elimStep, List.length_append]
      have := ev_toList_len_le (ev_simp g.op (m + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    omega

theorem ev_elimPass_len_lt (m k : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, ev_NOkGate g) (hk : k < acc.1.length)
    (hc : ∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c)
    (hex : ∃ g ∈ gs, k ∈ g.inputs) :
    (ev_elimPass m gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => obtain ⟨g, hg, _⟩ := hex; simp at hg
  | cons g gs ih =>
    rw [ev_elimPass_cons, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (ev_simp g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply ev_simp_none_of_const
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (ev_elimStep m acc g).2.length = acc.2.length := by
        simp only [ev_elimStep, hnone, Option.toList_none, List.append_nil]
      have := ev_elimPass_len m gs (ev_elimStep m acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (ev_elimStep m acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [ev_elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          exact ⟨c, by simp only [ev_elimStep]; rw [ev_getD_snoc_lt _ _ _ _ hk]; exact hc⟩)
        hex'
      have h2 : (ev_elimStep m acc g).2.length ≤ acc.2.length + 1 := by
        simp only [ev_elimStep, List.length_append]
        have := ev_toList_len_le (ev_simp g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

theorem ev_elimPass_len_two (m k : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, ev_NOkGate g) (hk : k < acc.1.length)
    (hc : ∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c)
    (htwo : 2 ≤ (gs.filter (fun g => decide (k ∈ g.inputs))).length) :
    (ev_elimPass m gs acc).2.length + 2 ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp at htwo
  | cons g gs ih =>
    rw [ev_elimPass_cons, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (ev_simp g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply ev_simp_none_of_const
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (ev_elimStep m acc g).2.length = acc.2.length := by
        simp only [ev_elimStep, hnone, Option.toList_none, List.append_nil]
      have hfilt : 1 ≤ (gs.filter (fun g => decide (k ∈ g.inputs))).length := by
        simp [hkg] at htwo
        omega
      have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        have hne : gs.filter (fun g => decide (k ∈ g.inputs)) ≠ [] := by
          intro hnil; rw [hnil] at hfilt; simp at hfilt
        obtain ⟨g', hg'⟩ := List.exists_mem_of_ne_nil _ hne
        rw [List.mem_filter] at hg'
        exact ⟨g', hg'.1, of_decide_eq_true hg'.2⟩
      have h1 := ev_elimPass_len_lt m k gs (ev_elimStep m acc g)
        (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [ev_elimStep]; omega)
        ⟨c, by simp only [ev_elimStep]; rw [ev_getD_snoc_lt _ _ _ _ hk]; exact hc⟩
        hex'
      omega
    · have htwo' : 2 ≤ (gs.filter (fun g => decide (k ∈ g.inputs))).length := by
        simpa [hkg] using htwo
      have h1 := ih (ev_elimStep m acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [ev_elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          exact ⟨c, by simp only [ev_elimStep]; rw [ev_getD_snoc_lt _ _ _ _ hk]; exact hc⟩)
        htwo'
      have h2 : (ev_elimStep m acc g).2.length ≤ acc.2.length + 1 := by
        simp only [ev_elimStep, List.length_append]
        have := ev_toList_len_le (ev_simp g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

def ev_Inv (m : ℕ) (w_in w_old : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) : Prop :=
  w_in.length = m ∧
  acc.1.length = w_old.length ∧
  ∀ i : ℕ,
    ev_statValid (m + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    ev_statVal (W acc.2 w_in) (acc.1.getD i (Sum.inl false)) = w_old.getD i false

theorem ev_Inv_step (m : ℕ) (w_in w_old : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) (hok : ev_OkGate g)
    (hinv : ev_Inv m w_in w_old acc) :
    ev_Inv m w_in (w_old ++ [g.op.eval (g.inputs.map fun i => w_old.getD i false)])
      (ev_elimStep m acc g) := by
  obtain ⟨hwin, hlen, hi⟩ := hinv
  set w_new := W acc.2 w_in with hw_new
  have hw_len : w_new.length = m + acc.2.length := by
    rw [hw_new, W_length, hwin]
  set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
  have hins_len : ins.length ≤ 2 := by simp [hins]; exact hok.2
  have hins_val : ∀ s ∈ ins, ev_statValid w_new.length s := by
    intro s hs
    obtain ⟨idx, _, rfl⟩ := List.mem_map.1 hs
    rw [hw_len]
    exact (hi idx).1
  have hsound := ev_simp_sound g.op hok.1 w_new ins hins_len hins_val
  rw [hw_len] at hsound
  refine ⟨hwin, by simp [ev_elimStep, hlen], ?_⟩
  intro i
  simp only [ev_elimStep]
  by_cases hieq : i = acc.1.length
  · rw [ev_getD_snoc_eq _ _ _ _ hieq, ev_getD_snoc_eq _ _ _ _ (by omega)]
    refine ⟨?_, ?_⟩
    · rw [List.length_append, ← Nat.add_assoc]
      exact hsound.1
    · rw [W_append, ← hw_new, hsound.2]
      congr 1
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro idx _
      exact (hi idx).2
  · rw [ev_getD_snoc_ne _ _ _ _ hieq, ev_getD_snoc_ne _ _ _ _ (by omega)]
    have ⟨hv, hval⟩ := hi i
    refine ⟨?_, ?_⟩
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c => trivial
      | inr j =>
        rw [hst] at hv
        simp only [ev_statValid, List.length_append] at hv ⊢
        omega
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c =>
        rw [hst] at hval
        exact hval
      | inr j =>
        rw [hst] at hv hval
        simp only [ev_statValid] at hv
        simp only [ev_statVal] at hval ⊢
        rw [W_append, ← hw_new, W_prefix _ _ _ (by omega)]
        exact hval

theorem ev_Inv_pass (m : ℕ) (w_in : List Bool) (gs : List Gate)
    (w_old : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, ev_OkGate g) (hinv : ev_Inv m w_in w_old acc) :
    ev_Inv m w_in (W gs w_old) (ev_elimPass m gs acc) := by
  induction gs generalizing w_old acc with
  | nil => exact hinv
  | cons g gs ih =>
    rw [ev_W_cons, ev_elimPass_cons]
    exact ih _ _ (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (ev_Inv_step m w_in w_old acc g (hok g List.mem_cons_self) hinv)

theorem ev_ofFn_getD_lt {α : Type*} {m : ℕ} (f : Fin m → α) (d : α) (i : ℕ) (hi : i < m) :
    (List.ofFn f).getD i d = f ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simp; exact hi), List.getElem_ofFn]

def ev_initVar (m : ℕ) (v : Fin m) (b : Bool) : List (Bool ⊕ ℕ) :=
  List.ofFn fun i : Fin m => if i = v then Sum.inl b else Sum.inr (i : ℕ)

theorem ev_Inv_initVar (m : ℕ) (v : Fin m) (b : Bool) (x : Fin m → Bool) :
    ev_Inv m (List.ofFn x) (List.ofFn (Function.update x v b)) (ev_initVar m v b, []) := by
  refine ⟨by simp, by simp [ev_initVar], ?_⟩
  intro i
  by_cases hi : i < m
  · have hget : (ev_initVar m v b).getD i (Sum.inl false) =
        if (⟨i, hi⟩ : Fin m) = v then Sum.inl b else Sum.inr i := by
      rw [ev_initVar, ev_ofFn_getD_lt _ _ _ hi]
    rw [hget]
    by_cases heq : (⟨i, hi⟩ : Fin m) = v
    · simp only [heq, ↓reduceIte, ev_statValid, ev_statVal]
      rw [ev_ofFn_getD_lt _ _ _ hi, heq, Function.update_self]
      exact ⟨trivial, rfl⟩
    · simp only [heq, ↓reduceIte, ev_statValid, ev_statVal, W_nil]
      refine ⟨by omega, ?_⟩
      rw [ev_ofFn_getD_lt _ _ _ hi, ev_ofFn_getD_lt _ _ _ hi, Function.update_of_ne heq]
  · rw [List.getD_eq_default _ _ (by simp [ev_initVar]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem ev_simp_or_true (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hlen : ins.length ≤ 2) (ht : Sum.inl true ∈ ins) :
    ev_simp GateOp.or m ins = (none, Sum.inl true) := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
  · simp at ht
  · cases a <;> simp_all [ev_simp, ev_simpOr]
  · cases a with
    | inl c =>
      cases b with
      | inl d => cases c <;> cases d <;> simp_all [ev_simp, ev_simpOr]
      | inr j => cases c <;> simp_all [ev_simp, ev_simpOr]
    | inr i =>
      cases b with
      | inl d => cases d <;> simp_all [ev_simp, ev_simpOr]
      | inr j => simp at ht
  · simp at hlen

theorem ev_elimPass_nil (m : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) :
    ev_elimPass m [] acc = acc := rfl

theorem ev_W_agree (gs : List Gate) (B : Set ℕ) (w₁ w₂ : List Bool)
    (hlen : w₁.length = w₂.length) (hB : ∀ b ∈ B, b < w₁.length)
    (hagree : ∀ i ∉ B, w₁.getD i false = w₂.getD i false)
    (hread : ∀ g ∈ gs, ∀ i ∈ g.inputs, i ∉ B) :
    (W gs w₁).length = (W gs w₂).length ∧
    ∀ i ∉ B, (W gs w₁).getD i false = (W gs w₂).getD i false := by
  induction gs generalizing w₁ w₂ with
  | nil => exact ⟨hlen, hagree⟩
  | cons g gs ih =>
    rw [ev_W_cons, ev_W_cons]
    have hmap : (g.inputs.map fun i => w₁.getD i false) =
        (g.inputs.map fun i => w₂.getD i false) := by
      apply List.map_congr_left
      intro i hi
      exact hagree i (hread g List.mem_cons_self i hi)
    rw [hmap]
    apply ih
    · simp [hlen]
    · intro b hb; simp; have := hB b hb; omega
    · intro i hi
      by_cases hlt : i < w₁.length
      · rw [ev_getD_snoc_lt _ _ _ _ hlt, ev_getD_snoc_lt _ _ _ _ (by omega)]
        exact hagree i hi
      · by_cases heq : i = w₁.length
        · rw [ev_getD_snoc_eq _ _ _ _ heq, ev_getD_snoc_eq _ _ _ _ (by omega)]
        · rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp; omega)]
    · intro g' hg'
      exact hread g' (List.mem_cons_of_mem _ hg')

theorem elim_one_var {m s : ℕ} {F : (Fin m → Bool) → Bool} (v : Fin m) (b : Bool)
    (hC : HasCircuitSize m F s)
    (hdep : ∃ x : Fin m → Bool, F (Function.update x v false) ≠ F (Function.update x v true))
    (hnc : ∃ x x' : Fin m → Bool, F (Function.update x v b) ≠ F (Function.update x' v b)) :
    1 ≤ s ∧ HasCircuitSize m (fun x => F (Function.update x v b)) (s - 1) := by
  obtain ⟨C, hok, hsz, hev⟩ := hC
  set gs := C.gates.map ev_normGate with hgs
  have hnok : ∀ g ∈ gs, ev_NOkGate g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ev_normGate_nok g0 (hok g0 hg0)
  have hout_ne : C.output ≠ (v : ℕ) := by
    intro heq
    obtain ⟨x, x', hne⟩ := hnc
    have h1 := hev (Function.update x v b)
    have h2 := hev (Function.update x' v b)
    have hw1 : (C.wires (List.ofFn (Function.update x v b))).getD (v : ℕ) false = b := by
      show (W C.gates (List.ofFn (Function.update x v b))).getD (v : ℕ) false = b
      rw [W_prefix _ _ _ (by simp), ev_ofFn_getD_lt _ _ _ v.isLt]
      simp
    have hw2 : (C.wires (List.ofFn (Function.update x' v b))).getD (v : ℕ) false = b := by
      show (W C.gates (List.ofFn (Function.update x' v b))).getD (v : ℕ) false = b
      rw [W_prefix _ _ _ (by simp), ev_ofFn_getD_lt _ _ _ v.isLt]
      simp
    have e1 : F (Function.update x v b) = b := by
      rw [← h1]; show (C.wires _).getD C.output false = b; rw [heq]; exact hw1
    have e2 : F (Function.update x' v b) = b := by
      rw [← h2]; show (C.wires _).getD C.output false = b; rw [heq]; exact hw2
    exact hne (e1.trans e2.symm)
  have hex : ∃ g ∈ gs, (v : ℕ) ∈ g.inputs := by
    by_contra hno
    have hno' : ∀ g ∈ gs, (v : ℕ) ∉ g.inputs := fun g hg hv => hno ⟨g, hg, hv⟩
    obtain ⟨x, hne⟩ := hdep
    have hag := ev_W_agree gs {(v : ℕ)}
      (List.ofFn (Function.update x v false))
      (List.ofFn (Function.update x v true))
      (by simp)
      (by intro u hu; simp at hu; subst hu; simp)
      (by
        intro i hi
        simp at hi
        by_cases hlt : i < m
        · have hne' : (⟨i, hlt⟩ : Fin m) ≠ v := by
            intro h; apply hi; exact congrArg Fin.val h
          rw [ev_ofFn_getD_lt _ _ _ hlt, ev_ofFn_getD_lt _ _ _ hlt,
              Function.update_of_ne hne', Function.update_of_ne hne']
        · rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp; omega)])
      (by
        intro g hg i hi hmem
        simp at hmem
        subst hmem
        exact hno' g hg hi)
    have hco : C.output ∉ ({(v : ℕ)} : Set ℕ) := by simpa using hout_ne
    have hEq := hag.2 C.output hco
    rw [hgs, ev_W_norm, ev_W_norm] at hEq
    exact hne ((hev _).symm.trans (hEq.trans (hev _)))
  set acc := ev_elimPass m gs (ev_initVar m v b, []) with hacc
  have hlen : acc.2.length + 1 ≤ gs.length := by
    have := ev_elimPass_len_lt m (v : ℕ) gs (ev_initVar m v b, []) hnok
      (by simp [ev_initVar])
      ⟨b, by rw [ev_initVar, ev_ofFn_getD_lt _ _ _ v.isLt]; simp⟩
      hex
    rw [← hacc] at this
    simpa using this
  have hgs_len : gs.length = C.gates.length := by simp [hgs]
  have hsz' : C.gates.length ≤ s := hsz
  have hval : ∀ x : Fin m → Bool,
      ev_statVal (W acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) =
        F (Function.update x v b) := by
    intro x
    have hinv := ev_Inv_pass m (List.ofFn x) gs _ (ev_initVar m v b, [])
      (fun g hg => (hnok g hg).1) (ev_Inv_initVar m v b x)
    rw [← hacc] at hinv
    rw [(hinv.2.2 C.output).2, hgs, ev_W_norm]
    exact hev (Function.update x v b)
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    obtain ⟨x, x', hne⟩ := hnc
    have hx := hval x; have hx' := hval x'
    rw [hst] at hx hx'
    exact absurd (hx.symm.trans hx') hne
  | inr j =>
    refine ⟨by omega, ⟨acc.2, j⟩, ev_elimPass_ok m gs _ (by simp), ?_, ?_⟩
    · show acc.2.length ≤ s - 1
      omega
    · intro x
      have := hval x
      rw [hst] at this
      exact this


theorem ev_ofFn_snoc_eq {n : ℕ} (x : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc (α := fun _ => Bool) x b) = List.ofFn x ++ [b] := by
  rw [List.ofFn_succ', List.concat_eq_append]
  simp

theorem ev_eval_update_snoc {n : ℕ} (C : Circuit) (x : Fin n → Bool) (b c : Bool) :
    C.eval (List.ofFn (Function.update (Fin.snoc (α := fun _ => Bool) x c) (Fin.last n) b)) =
      C.eval (List.ofFn x ++ [b]) := by
  rw [Fin.update_snoc_last, ev_ofFn_snoc_eq]

theorem ev_elim_last : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (∃ (x4 : Fin x1 → Bool) (x5 : Fin x1 → Bool), x2.eval (List.ofFn x4 ++ [Bool.false]) ≠ x2.eval (List.ofFn x5 ++ [Bool.false])) → (∃ (x5 : Fin x1 → Bool), x2.eval (List.ofFn x5 ++ [Bool.true]) ≠ x2.eval (List.ofFn x5 ++ [Bool.false])) → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x6 ∧ x6.size < x2.size ∧ ∀ (x7 : Fin x1 → Bool), x6.eval (List.ofFn x7 ++ [Bool.false]) = x2.eval (List.ofFn x7 ++ [Bool.false]) := by
  intro n C hfan hnc0 hdep0
  have hdep : ∃ y : Fin (n + 1) → Bool,
      (fun z : Fin (n + 1) → Bool => C.eval (List.ofFn z)) (Function.update y (Fin.last n) false) ≠
      (fun z : Fin (n + 1) → Bool => C.eval (List.ofFn z)) (Function.update y (Fin.last n) true) := by
    obtain ⟨x, hx⟩ := hdep0
    refine ⟨Fin.snoc (α := fun _ => Bool) x false, ?_⟩
    show C.eval (List.ofFn (Function.update (Fin.snoc (α := fun _ => Bool) x false) (Fin.last n) false)) ≠
      C.eval (List.ofFn (Function.update (Fin.snoc (α := fun _ => Bool) x false) (Fin.last n) true))
    rw [ev_eval_update_snoc, ev_eval_update_snoc]
    exact fun h => hx h.symm
  have hnc : ∃ y y' : Fin (n + 1) → Bool,
      (fun z : Fin (n + 1) → Bool => C.eval (List.ofFn z)) (Function.update y (Fin.last n) false) ≠
      (fun z : Fin (n + 1) → Bool => C.eval (List.ofFn z)) (Function.update y' (Fin.last n) false) := by
    obtain ⟨x, x', hx⟩ := hnc0
    refine ⟨Fin.snoc (α := fun _ => Bool) x false, Fin.snoc (α := fun _ => Bool) x' false, ?_⟩
    show C.eval (List.ofFn (Function.update (Fin.snoc (α := fun _ => Bool) x false) (Fin.last n) false)) ≠
      C.eval (List.ofFn (Function.update (Fin.snoc (α := fun _ => Bool) x' false) (Fin.last n) false))
    rw [ev_eval_update_snoc, ev_eval_update_snoc]
    exact hx
  obtain ⟨hs, D, hD, hDs, hDv⟩ := elim_one_var (m := n + 1) (s := C.size)
    (F := fun z : Fin (n + 1) → Bool => C.eval (List.ofFn z)) (Fin.last n) false
    ⟨C, hfan, le_refl _, fun _ => rfl⟩ hdep hnc
  refine ⟨D, hD, by omega, ?_⟩
  intro x
  have h := hDv (Fin.snoc (α := fun _ => Bool) x false)
  have h' : D.eval (List.ofFn (Fin.snoc (α := fun _ => Bool) x false)) =
      C.eval (List.ofFn (Function.update (Fin.snoc (α := fun _ => Bool) x false) (Fin.last n) false)) := h
  rw [ev_eval_update_snoc, ev_ofFn_snoc_eq] at h'
  exact h'

theorem rx_gd2 {α : Type*} {n m : ℕ} (p : Fin n → α) (q : Fin m → α) (d : α) (i : ℕ) :
    (List.ofFn p ++ List.ofFn q).getD i d =
      if h : i < n then p ⟨i, h⟩ else if h2 : i - n < m then q ⟨i - n, h2⟩ else d := by
  split_ifs with h h2
  · rw [List.getD_eq_getElem _ _ (by simp only [List.length_append, List.length_ofFn]; omega),
      List.getElem_append_left (by simp only [List.length_ofFn]; omega)]
    simp
  · rw [List.getD_eq_getElem _ _ (by simp only [List.length_append, List.length_ofFn]; omega),
      List.getElem_append_right (by simp only [List.length_ofFn]; omega)]
    simp
  · rw [List.getD_eq_default _ _ (by simp only [List.length_append, List.length_ofFn]; omega)]

def rx_MOk (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem rx_mok_op (g : Gate) (h : rx_MOk g) : g.op = GateOp.and ∨ g.op = GateOp.or := by
  have h1 := h.1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
  exact h1

theorem rx_simp_some (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (m : ℕ)
    (ins : List (Bool ⊕ ℕ)) (hlen : ins.length ≤ 2) (hs : (ev_simp op m ins).1.isSome = true) :
    (∀ s ∈ ins, s.isLeft = false) ∧ (ev_simp op m ins).2.isLeft = false := by
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [ev_simp, ev_simpAnd] at hs
    · cases a <;> simp [ev_simp, ev_simpAnd] at hs ⊢
    · cases a with
      | inl c => cases b <;> cases c <;> simp [ev_simp, ev_simpAnd] at hs ⊢
      | inr i => cases b with
        | inl c => cases c <;> simp [ev_simp, ev_simpAnd] at hs ⊢
        | inr j => simp [ev_simp, ev_simpAnd]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [ev_simp, ev_simpOr] at hs
    · cases a <;> simp [ev_simp, ev_simpOr] at hs ⊢
    · cases a with
      | inl c => cases b <;> cases c <;> simp [ev_simp, ev_simpOr] at hs ⊢
      | inr i => cases b with
        | inl c => cases c <;> simp [ev_simp, ev_simpOr] at hs ⊢
        | inr j => simp [ev_simp, ev_simpOr]
    · simp at hlen

theorem rx_simp_two (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (m : ℕ) (c d : Bool) :
    (ev_simp op m [Sum.inl c, Sum.inl d]).2.isLeft = true := by
  rcases hop with rfl | rfl <;> rfl

theorem rx_simp_op (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (m : ℕ)
    (ins : List (Bool ⊕ ℕ)) : ∀ g ∈ (ev_simp op m ins).1, rx_MOk g := by
  intro g hg
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [ev_simp, ev_simpAnd] at hg
    subst hg; simp [rx_MOk]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [ev_simp, ev_simpOr] at hg
    subst hg; simp [rx_MOk]

theorem rx_pass_ok (N : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hgs : ∀ g ∈ gs, rx_MOk g) (h : ∀ g ∈ acc.2, rx_MOk g) :
    ∀ g ∈ (ev_elimPass N gs acc).2, rx_MOk g := by
  induction gs generalizing acc with
  | nil => exact h
  | cons g gs ih =>
    rw [ev_elimPass_cons]
    apply ih _ (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact rx_simp_op _ (rx_mok_op g (hgs g List.mem_cons_self)) _ _ g' (by simpa using h1)

theorem rx_two (l : List ℕ) (a b : ℕ) (hl : l.length ≤ 2) (ha : a ∈ l) (hb : b ∈ l)
    (hab : a ≠ b) : l = [a, b] ∨ l = [b, a] := by
  rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, t⟩⟩⟩
  · simp at ha
  · simp at ha hb; subst ha; subst hb; exact absurd rfl hab
  · simp at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all
  · simp at hl

def rx_gk (gs : List Gate) (j : ℕ) : Gate := gs.getD j ⟨GateOp.or, []⟩

def rx_PSk (N : ℕ) (gs : List Gate) (ini : List (Bool ⊕ ℕ)) (k : ℕ) :
    List (Bool ⊕ ℕ) × List Gate :=
  ev_elimPass N (gs.take k) (ini, [])

def rx_Ls (N : ℕ) (gs : List Gate) (ini : List (Bool ⊕ ℕ)) (i : ℕ) : Bool ⊕ ℕ :=
  (ev_elimPass N gs (ini, [])).1.getD i (Sum.inl false)

theorem rx_PSk_len (N : ℕ) (gs : List Gate) (ini : List (Bool ⊕ ℕ)) (k : ℕ) (hk : k ≤ gs.length) :
    (rx_PSk N gs ini k).1.length = ini.length + k := by
  simp only [rx_PSk, ev_elimPass_fst_len, List.length_take]
  omega

theorem rx_Ls_eq (N : ℕ) (gs : List Gate) (ini : List (Bool ⊕ ℕ)) (k i : ℕ) (hk : k ≤ gs.length)
    (hi : i < ini.length + k) :
    (rx_PSk N gs ini k).1.getD i (Sum.inl false) = rx_Ls N gs ini i := by
  have h : ev_elimPass N gs (ini, []) = ev_elimPass N (gs.drop k) (rx_PSk N gs ini k) := by
    unfold rx_PSk
    rw [← ev_elimPass_append, List.take_append_drop]
  unfold rx_Ls
  rw [h, ev_elimPass_getD_lt N i (Sum.inl false) (gs.drop k) (rx_PSk N gs ini k)
    (by rw [rx_PSk_len _ _ _ _ hk]; exact hi)]

theorem rx_PSk_succ (N : ℕ) (gs : List Gate) (ini : List (Bool ⊕ ℕ)) (k : ℕ) (hk : k < gs.length) :
    rx_PSk N gs ini (k + 1) = ev_elimStep N (rx_PSk N gs ini k) (rx_gk gs k) := by
  unfold rx_PSk rx_gk
  rw [List.take_succ, ev_elimPass_append, List.getElem?_eq_getElem hk,
    List.getD_eq_getElem _ _ hk]
  rfl

theorem rx_gk_mem (gs : List Gate) (k : ℕ) (hk : k < gs.length) : rx_gk gs k ∈ gs := by
  unfold rx_gk
  rw [List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem hk

def rx_Pk (N : ℕ) (gs : List Gate) (ini : List (Bool ⊕ ℕ)) (k : ℕ) : Finset ℕ :=
  (Finset.range (N + k)).filter (fun i => (rx_Ls N gs ini i).isLeft = true ∧
    ∀ j < k, ¬ (i ∈ (rx_gk gs j).inputs ∧ i < N + j))

theorem rx_cnt (N : ℕ) (gs : List Gate) (ini : List (Bool ⊕ ℕ)) (hN : ini.length = N)
    (hgs : ∀ g ∈ gs, rx_MOk g) : ∀ k ≤ gs.length,
    ((Finset.range N).filter (fun i => (rx_Ls N gs ini i).isLeft = true)).card
      + (rx_PSk N gs ini k).2.length ≤ k + (rx_Pk N gs ini k).card := by
  intro k
  induction k with
  | zero =>
    intro _
    have : rx_Pk N gs ini 0 = (Finset.range N).filter (fun i => (rx_Ls N gs ini i).isLeft = true) := by
      unfold rx_Pk
      ext i
      simp
    rw [this]
    simp [rx_PSk, ev_elimPass]
  | succ k ih =>
    intro hk
    have ih' := ih (by omega)
    have hkl : k < gs.length := by omega
    have hmk := hgs _ (rx_gk_mem gs k hkl)
    have hlen : (rx_gk gs k).inputs.length ≤ 2 := hmk.2
    have hop' := rx_mok_op _ hmk
    obtain ⟨acc, hacc⟩ : ∃ a, a = rx_PSk N gs ini k := ⟨_, rfl⟩
    have haccl : acc.1.length = N + k := by rw [hacc, rx_PSk_len _ _ _ _ (by omega), hN]
    obtain ⟨ins, hins⟩ : ∃ l, l = (rx_gk gs k).inputs.map (fun i => acc.1.getD i (Sum.inl false)) :=
      ⟨_, rfl⟩
    obtain ⟨r, hr⟩ : ∃ r, r = ev_simp (rx_gk gs k).op (N + acc.2.length) ins := ⟨_, rfl⟩
    have hsucc : rx_PSk N gs ini (k + 1) = (acc.1 ++ [r.2], acc.2 ++ r.1.toList) := by
      rw [rx_PSk_succ _ _ _ _ hkl, ← hacc, hr, hins]
      rfl
    have hLk : rx_Ls N gs ini (N + k) = r.2 := by
      rw [← rx_Ls_eq N gs ini (k + 1) (N + k) hk (by rw [hN]; omega), hsucc]
      exact ev_getD_snoc_eq _ _ _ _ haccl.symm
    have hLi : ∀ i, i < N + k → acc.1.getD i (Sum.inl false) = rx_Ls N gs ini i := by
      intro i hi
      rw [hacc]
      exact rx_Ls_eq N gs ini k i (by omega) (by rw [hN]; exact hi)
    have hinsl : ins.length ≤ 2 := by rw [hins, List.length_map]; exact hlen
    rw [← hacc] at ih'
    rw [hsucc]
    cases hr1 : r.1 with
    | some gn =>
      have hsome : (ev_simp (rx_gk gs k).op (N + acc.2.length) ins).1.isSome = true := by
        rw [← hr]; simp [hr1]
      obtain ⟨hall, hres⟩ := rx_simp_some _ hop' _ _ hinsl hsome
      rw [← hr] at hres
      have hP : rx_Pk N gs ini (k + 1) = rx_Pk N gs ini k := by
        ext i
        simp only [rx_Pk, Finset.mem_filter, Finset.mem_range]
        constructor
        · rintro ⟨h1, h2, h3⟩
          have hik : i ≠ N + k := by
            rintro rfl
            rw [hLk, hres] at h2
            exact absurd h2 (by simp)
          exact ⟨by omega, h2, fun j hj => h3 j (by omega)⟩
        · rintro ⟨h1, h2, h3⟩
          refine ⟨by omega, h2, fun j hj => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
          · exact h3 j hj
          · subst hj
            rintro ⟨hm, _⟩
            have := hall (acc.1.getD i (Sum.inl false))
              (by rw [hins]; exact List.mem_map.2 ⟨i, hm, rfl⟩)
            rw [hLi i h1, h2] at this
            exact absurd this (by simp)
      rw [hP]
      simp only [List.length_append, Option.toList_some, List.length_singleton]
      omega
    | none =>
      simp only [List.length_append, Option.toList_none, List.length_nil, add_zero]
      suffices hs : (rx_Pk N gs ini k).card ≤ (rx_Pk N gs ini (k + 1)).card + 1 by omega
      have hQT := Finset.card_filter_add_card_filter_not (s := rx_Pk N gs ini k)
        (fun i => i ∈ (rx_gk gs k).inputs)
      have hQsub : (rx_Pk N gs ini k).filter (fun i => ¬ i ∈ (rx_gk gs k).inputs) ⊆
          rx_Pk N gs ini (k + 1) := by
        intro i hi
        simp only [rx_Pk, Finset.mem_filter, Finset.mem_range] at hi ⊢
        obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hi
        refine ⟨by omega, h2, fun j hj => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
        · exact h3 j hj
        · subst hj
          exact fun h => h4 h.1
      have hTle : ((rx_Pk N gs ini k).filter (fun i => i ∈ (rx_gk gs k).inputs)).card ≤ 2 := by
        calc ((rx_Pk N gs ini k).filter (fun i => i ∈ (rx_gk gs k).inputs)).card
            ≤ (rx_gk gs k).inputs.toFinset.card := by
              apply Finset.card_le_card
              intro i hi
              simp only [Finset.mem_filter] at hi
              exact List.mem_toFinset.2 hi.2
          _ ≤ (rx_gk gs k).inputs.length := List.toFinset_card_le _
          _ ≤ 2 := hlen
      have hQle := Finset.card_le_card hQsub
      by_cases hT2 : ((rx_Pk N gs ini k).filter (fun i => i ∈ (rx_gk gs k).inputs)).card = 2
      · obtain ⟨a, b, hab, hTab⟩ := Finset.card_eq_two.1 hT2
        have ha : a ∈ (rx_Pk N gs ini k).filter (fun i => i ∈ (rx_gk gs k).inputs) := by
          rw [hTab]; simp
        have hb : b ∈ (rx_Pk N gs ini k).filter (fun i => i ∈ (rx_gk gs k).inputs) := by
          rw [hTab]; simp
        simp only [rx_Pk, Finset.mem_filter, Finset.mem_range] at ha hb
        obtain ⟨⟨ha1, ha2, -⟩, ha3⟩ := ha
        obtain ⟨⟨hb1, hb2, -⟩, hb3⟩ := hb
        have hl := rx_two (rx_gk gs k).inputs a b hlen ha3 hb3 hab
        obtain ⟨c, hc⟩ := Sum.isLeft_iff.1 ha2
        obtain ⟨d, hd⟩ := Sum.isLeft_iff.1 hb2
        have hr2 : r.2.isLeft = true := by
          rcases hl with hl | hl
          · have hi2 : ins = [Sum.inl c, Sum.inl d] := by
              rw [hins, hl]
              simp only [List.map_cons, List.map_nil, hLi a ha1, hLi b hb1, hc, hd]
            rw [hr, hi2]
            exact rx_simp_two _ hop' _ c d
          · have hi2 : ins = [Sum.inl d, Sum.inl c] := by
              rw [hins, hl]
              simp only [List.map_cons, List.map_nil, hLi a ha1, hLi b hb1, hc, hd]
            rw [hr, hi2]
            exact rx_simp_two _ hop' _ d c
        have hNk : N + k ∈ rx_Pk N gs ini (k + 1) := by
          simp only [rx_Pk, Finset.mem_filter, Finset.mem_range]
          refine ⟨by omega, by rw [hLk]; exact hr2, fun j hj h => ?_⟩
          have := h.2
          omega
        have hNkQ : N + k ∉ (rx_Pk N gs ini k).filter (fun i => ¬ i ∈ (rx_gk gs k).inputs) := by
          intro h
          simp only [rx_Pk, Finset.mem_filter, Finset.mem_range] at h
          exact absurd h.1.1 (by omega)
        have hins2 := Finset.card_le_card (Finset.insert_subset hNk hQsub)
        rw [Finset.card_insert_of_notMem hNkQ] at hins2
        omega
      · omega

theorem rx_final (N : ℕ) (gs : List Gate) (ini : List (Bool ⊕ ℕ)) (hN : ini.length = N)
    (hgs : ∀ g ∈ gs, rx_MOk g) (o : ℕ) (hout : (rx_Ls N gs ini o).isLeft = false)
    (hmin : ∀ j < gs.length, N + j ≠ o →
      ∃ k, j < k ∧ k < gs.length ∧ N + j ∈ (rx_gk gs k).inputs) :
    (((Finset.range N).filter (fun i => (rx_Ls N gs ini i).isLeft = true)).filter
      (fun i => ∃ j < gs.length, i ∈ (rx_gk gs j).inputs)).card
      + (ev_elimPass N gs (ini, [])).2.length ≤ gs.length := by
  have h := rx_cnt N gs ini hN hgs gs.length le_rfl
  have hPS : rx_PSk N gs ini gs.length = ev_elimPass N gs (ini, []) := by
    unfold rx_PSk
    rw [List.take_length]
  rw [hPS] at h
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.range N).filter (fun i => (rx_Ls N gs ini i).isLeft = true))
    (fun i => ∃ j < gs.length, i ∈ (rx_gk gs j).inputs)
  have hsub : rx_Pk N gs ini gs.length ⊆
      ((Finset.range N).filter (fun i => (rx_Ls N gs ini i).isLeft = true)).filter
        (fun i => ¬ ∃ j < gs.length, i ∈ (rx_gk gs j).inputs) := by
    intro i hi
    simp only [rx_Pk, Finset.mem_filter, Finset.mem_range] at hi ⊢
    obtain ⟨h1, h2, h3⟩ := hi
    have hiN : i < N := by
      by_contra hc
      have hio : N + (i - N) ≠ o := by
        intro he
        rw [show i = N + (i - N) by omega, he, hout] at h2
        exact absurd h2 (by simp)
      obtain ⟨k, hk1, hk2, hk3⟩ := hmin (i - N) (by omega) hio
      exact h3 k hk2 ⟨by rw [show i = N + (i - N) by omega]; exact hk3, by omega⟩
    refine ⟨⟨hiN, h2⟩, ?_⟩
    rintro ⟨j, hj, hm⟩
    exact h3 j hj ⟨hm, by omega⟩
  have := Finset.card_le_card hsub
  omega

def rx_ini {n m : ℕ} (kr : Fin n → Bool) (kc : Fin m → Bool) : List (Bool ⊕ ℕ) :=
  List.ofFn (fun i : Fin n => if kr i then Sum.inr (i : ℕ) else Sum.inl false) ++
    List.ofFn (fun j : Fin m => if kc j then Sum.inr (n + (j : ℕ)) else Sum.inl false)

theorem rx_ini_len {n m : ℕ} (kr : Fin n → Bool) (kc : Fin m → Bool) :
    (rx_ini kr kc).length = n + m := by
  simp [rx_ini]

theorem rx_inv_ini {n m : ℕ} (kr : Fin n → Bool) (kc : Fin m → Bool) (p : Fin n → Bool)
    (q : Fin m → Bool) :
    ev_Inv (n + m) (List.ofFn p ++ List.ofFn q)
      (List.ofFn (fun i => p i && kr i) ++ List.ofFn (fun j => q j && kc j)) (rx_ini kr kc, []) := by
  refine ⟨by simp, by simp [rx_ini], ?_⟩
  intro i
  show ev_statValid (n + m) ((rx_ini kr kc).getD i (Sum.inl false)) ∧
    ev_statVal (List.ofFn p ++ List.ofFn q) ((rx_ini kr kc).getD i (Sum.inl false)) =
      (List.ofFn (fun i => p i && kr i) ++ List.ofFn (fun j => q j && kc j)).getD i false
  by_cases h : i < n
  · have hw : (List.ofFn (fun i => p i && kr i) ++ List.ofFn (fun j => q j && kc j)).getD i false
        = (p ⟨i, h⟩ && kr ⟨i, h⟩) := by rw [rx_gd2, dif_pos h]
    rw [hw]
    cases hk : kr ⟨i, h⟩
    · have hs : (rx_ini kr kc).getD i (Sum.inl false) = Sum.inl false := by
        rw [rx_ini, rx_gd2, dif_pos h]; simp [hk]
      rw [hs]
      exact ⟨trivial, by simp [ev_statVal]⟩
    · have hs : (rx_ini kr kc).getD i (Sum.inl false) = Sum.inr i := by
        rw [rx_ini, rx_gd2, dif_pos h]; simp [hk]
      have hv : (List.ofFn p ++ List.ofFn q).getD i false = p ⟨i, h⟩ := by rw [rx_gd2, dif_pos h]
      rw [hs]
      refine ⟨?_, ?_⟩
      · show i < n + m
        omega
      · show (List.ofFn p ++ List.ofFn q).getD i false = (p ⟨i, h⟩ && true)
        rw [hv, Bool.and_true]
  · by_cases h2 : i - n < m
    · have hw : (List.ofFn (fun i => p i && kr i) ++ List.ofFn (fun j => q j && kc j)).getD i false
          = (q ⟨i - n, h2⟩ && kc ⟨i - n, h2⟩) := by rw [rx_gd2, dif_neg h, dif_pos h2]
      rw [hw]
      cases hk : kc ⟨i - n, h2⟩
      · have hs : (rx_ini kr kc).getD i (Sum.inl false) = Sum.inl false := by
          rw [rx_ini, rx_gd2, dif_neg h, dif_pos h2]; simp [hk]
        rw [hs]
        exact ⟨trivial, by simp [ev_statVal]⟩
      · have hs : (rx_ini kr kc).getD i (Sum.inl false) = Sum.inr (n + (i - n)) := by
          rw [rx_ini, rx_gd2, dif_neg h, dif_pos h2]; simp [hk]
        have hv : (List.ofFn p ++ List.ofFn q).getD (n + (i - n)) false = q ⟨i - n, h2⟩ := by
          rw [rx_gd2, dif_neg (show ¬ n + (i - n) < n by omega),
            dif_pos (show n + (i - n) - n < m by omega)]
          exact congrArg q (Fin.ext (show n + (i - n) - n = i - n by omega))
        rw [hs]
        refine ⟨?_, ?_⟩
        · show n + (i - n) < n + m
          omega
        · show (List.ofFn p ++ List.ofFn q).getD (n + (i - n)) false = (q ⟨i - n, h2⟩ && true)
          rw [hv, Bool.and_true]
    · have hs : (rx_ini kr kc).getD i (Sum.inl false) = Sum.inl false := by
        rw [rx_ini, rx_gd2, dif_neg h, dif_neg h2]
      have hw : (List.ofFn (fun i => p i && kr i) ++ List.ofFn (fun j => q j && kc j)).getD i false
          = false := by rw [rx_gd2, dif_neg h, dif_neg h2]
      rw [hs, hw]
      exact ⟨trivial, rfl⟩

theorem rx_mok_of {C : Circuit} (hC : Monotone2 C) : ∀ g ∈ C.gates, rx_MOk g :=
  fun g hg => hC g hg

theorem rx_sem {n m : ℕ} (C : Circuit) (hC : Monotone2 C) (kr : Fin n → Bool) (kc : Fin m → Bool)
    (p : Fin n → Bool) (q : Fin m → Bool) :
    ev_statVal (W (ev_elimPass (n + m) C.gates (rx_ini kr kc, [])).2 (List.ofFn p ++ List.ofFn q))
      (rx_Ls (n + m) C.gates (rx_ini kr kc) C.output) =
      C.eval (List.ofFn (fun i => p i && kr i) ++ List.ofFn (fun j => q j && kc j)) := by
  have hok : ∀ g ∈ C.gates, ev_OkGate g := by
    intro g hg
    have h := rx_mok_op g (hC g hg)
    refine ⟨?_, (hC g hg).2⟩
    rcases h with h | h <;> rw [h] <;> simp
  have hinv := ev_Inv_pass (n + m) _ C.gates _ _ hok (rx_inv_ini kr kc p q)
  exact (hinv.2.2 C.output).2

theorem rx_mono {n m : ℕ} (C : Circuit) (hC : Monotone2 C) (p p' : Fin n → Bool)
    (q q' : Fin m → Bool)
    (hp : ∀ i, p i = true → p' i = true) (hq : ∀ j, q j = true → q' j = true)
    (h : C.eval (List.ofFn p ++ List.ofFn q) = true) :
    C.eval (List.ofFn p' ++ List.ofFn q') = true := by
  rw [← List.ofFn_fin_append] at h ⊢
  refine mono (n + m) C (andOrOnly_of_monotone2 hC) (Fin.append p q) (Fin.append p' q') ?_
    C.output h
  intro i
  induction i using Fin.addCases with
  | left a => simp only [Fin.append_left]; exact hp a
  | right b => simp only [Fin.append_right]; exact hq b

theorem rx_zero {n m : ℕ} (A : Fin n → Fin m → Bool) (C : Circuit) (hC : Monotone2 C)
    (hrep : PEqualNP.Represents.Represents A C) (p : Fin n → Bool) (q : Fin m → Bool) (a : Fin n)
    (b : Fin m) (hp : ∀ i, p i = true → i = a) (hq : ∀ j, q j = true → j = b)
    (hab : A a b = false) :
    C.eval (List.ofFn p ++ List.ofFn q) = false := by
  by_contra hc
  have h1 := rx_mono C hC p (fun i => decide (i = a)) q (fun j => decide (j = b))
    (fun i hi => by simp [hp i hi]) (fun j hj => by simp [hq j hj]) (by simpa using hc)
  have h2 := hrep a b
  unfold PEqualNP.Represents.oneEach at h2
  rw [h2, hab] at h1
  exact absurd h1 (by simp)

theorem rx_drop {n m : ℕ} (A : Fin n → Fin m → Bool) (C : Circuit) (hC : Monotone2 C)
    (hrep : PEqualNP.Represents.Represents A C) (j : ℕ) (hj : j < C.gates.length)
    (hjo : n + m + j ≠ C.output)
    (hno : ∀ k, j < k → k < C.gates.length → n + m + j ∉ (rx_gk C.gates k).inputs) :
    PEqualNP.Represents.RepSizeAtMost A (C.gates.length - 1) := by
  set N := n + m with hNdef
  set pre := C.gates.take j with hpre
  set post := C.gates.drop (j + 1) with hpost
  have hprel : pre.length = j := by rw [hpre, List.length_take]; omega
  have hpostl : post.length = C.gates.length - (j + 1) := by rw [hpost, List.length_drop]
  have hsplit : C.gates = pre ++ C.gates[j] :: post := by
    rw [hpre, hpost, List.getElem_cons_drop, List.take_append_drop]
  set g0 : Gate := ⟨GateOp.or, []⟩ with hg0
  set f := flow_del (N + pre.length) (N + C.gates.length) with hf
  set C' : Circuit := ⟨pre ++ post.map (rgate f), f C.output⟩ with hC'
  have hread : ∀ g ∈ post, ∀ i ∈ g.inputs, i ∉ ({N + j} : Set ℕ) := by
    intro g hg i hi hiB
    simp only [Set.mem_singleton_iff] at hiB
    subst hiB
    obtain ⟨t, ht, hgt⟩ := List.mem_iff_getElem.1 hg
    have ht' : j + 1 + t < C.gates.length := by rw [hpostl] at ht; omega
    apply hno (j + 1 + t) (by omega) ht'
    unfold rx_gk
    rw [List.getD_eq_getElem _ _ ht']
    have hpt : post[t] = C.gates[j + 1 + t] := by simp only [hpost, List.getElem_drop]
    rw [← hpt, hgt]
    exact hi
  have heval : ∀ x : List Bool, x.length = N → C.eval x = C'.eval x := by
    intro x hx
    have hwl : (W pre x).length = N + j := by rw [W_length, hx, hprel]
    have hstep1 : C.eval x = (W (pre ++ g0 :: post) x).getD C.output false := by
      rw [eval_W, hsplit, W_append, W_append, W_cons, W_cons]
      have hag := ev_W_agree post {N + j} (step (W pre x) C.gates[j]) (step (W pre x) g0)
        (by rw [step_len, step_len])
        (by intro b hb; simp only [Set.mem_singleton_iff] at hb; rw [step_len]; omega)
        (by
          intro i hi
          simp only [Set.mem_singleton_iff] at hi
          rw [flow_step_ne _ _ _ (by omega), flow_step_ne _ _ _ (by omega)])
        hread
      exact hag.2 C.output (by simp only [Set.mem_singleton_iff]; omega)
    rw [hstep1]
    have hd := flow_drop_eval ⟨pre ++ g0 :: post, C.output⟩ pre post g0 rfl N x hx
      (N + C.gates.length) (Or.inr (by rw [hprel, hpostl]; omega))
      (by rw [List.getD_eq_default _ _ (by rw [hwl]; omega)] <;> rfl)
    exact hd
  refine ⟨C', ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with h | h
    · exact hC g (List.mem_of_mem_take h)
    · obtain ⟨g1, hg1, rfl⟩ := List.mem_map.1 h
      have := hC g1 (List.mem_of_mem_drop hg1)
      exact ⟨by rw [rgate_op]; exact this.1, by rw [rgate_len]; exact this.2⟩
  · show (pre ++ post.map (rgate f)).length ≤ C.gates.length - 1
    have := flow_drop_len pre post C.gates[j] (rgate f)
    rw [← hsplit] at this
    omega
  · intro u v
    rw [← heval (PEqualNP.Represents.oneEach u v)
      (by simp [PEqualNP.Represents.oneEach, hNdef])]
    exact hrep u v

theorem rx_core {n m s : ℕ} (A : Fin n → Fin m → Bool) (R : Finset (Fin n)) (K : Finset (Fin m))
    (h1 : ∀ u ∈ R, ∃ v ∈ K, A u v = false) (h2 : ∀ v ∈ K, ∃ u ∈ R, A u v = false)
    (h3 : ∃ u ∈ R, ∃ v ∈ K, A u v = true) (C : Circuit) (hC : Monotone2 C) (hsz : C.size ≤ s)
    (hrep : PEqualNP.Represents.Represents A C)
    (hmin : ∀ j < C.gates.length, n + m + j ≠ C.output →
      ∃ k, j < k ∧ k < C.gates.length ∧ n + m + j ∈ (rx_gk C.gates k).inputs) :
    ∃ s' : ℕ, PEqualNP.Represents.RepSizeAtMost (fun u v => A u v && decide (u ∈ R) && decide (v ∈ K)) s' ∧ s' + ((Finset.univ.filter (fun a : Fin n => ∃ b : Fin m, A a b = true ∧ ∃ a' : Fin n, A a' b = false)).card + (Finset.univ.filter (fun b : Fin m => ∃ a : Fin n, A a b = true ∧ ∃ b' : Fin m, A a b' = false)).card) ≤ s + ((R.filter (fun a => ∃ b ∈ K, A a b = true)).card + (K.filter (fun b => ∃ a ∈ R, A a b = true)).card) := by
  set kr : Fin n → Bool := fun a => decide (a ∈ R ∧ ∃ b ∈ K, A a b = true) with hkr
  set kc : Fin m → Bool := fun b => decide (b ∈ K ∧ ∃ a ∈ R, A a b = true) with hkc
  have hsem := rx_sem C hC kr kc
  have hzero := rx_zero A C hC hrep
  have hpt : ∀ (u : Fin n) (v : Fin m),
      C.eval (List.ofFn (fun i => decide (i = u) && kr i) ++
        List.ofFn (fun j => decide (j = v) && kc j))
        = (A u v && decide (u ∈ R) && decide (v ∈ K)) := by
    intro u v
    by_cases hu : kr u = true
    · by_cases hv : kc v = true
      · have e1 : (fun i => decide (i = u) && kr i) = (fun i => decide (i = u)) := by
          funext i
          by_cases hi : i = u
          · subst hi; simp [hu]
          · simp [hi]
        have e2 : (fun j => decide (j = v) && kc j) = (fun j => decide (j = v)) := by
          funext j
          by_cases hj : j = v
          · subst hj; simp [hv]
          · simp [hj]
        rw [e1, e2]
        have := hrep u v
        unfold PEqualNP.Represents.oneEach at this
        rw [this]
        simp only [hkr, decide_eq_true_eq] at hu
        simp only [hkc, decide_eq_true_eq] at hv
        simp [hu.1, hv.1]
      · simp only [hkr, decide_eq_true_eq] at hu
        obtain ⟨v', hv'K, hv'⟩ := h1 u hu.1
        have hB : (A u v && decide (u ∈ R) && decide (v ∈ K)) = false := by
          by_contra hc
          simp only [Bool.not_eq_false, Bool.and_eq_true, decide_eq_true_eq] at hc
          apply hv
          simp only [hkc, decide_eq_true_eq]
          exact ⟨hc.2, u, hc.1.2, hc.1.1⟩
        rw [hB]
        apply hzero _ _ u v'
        · intro i hi
          simp at hi
          exact hi.1
        · intro j hj
          simp at hj
          obtain ⟨rfl, hj2⟩ := hj
          exact absurd hj2 hv
        · exact hv'
    · have hB : (A u v && decide (u ∈ R) && decide (v ∈ K)) = false := by
        by_contra hc
        simp only [Bool.not_eq_false, Bool.and_eq_true, decide_eq_true_eq] at hc
        apply hu
        simp only [hkr, decide_eq_true_eq]
        exact ⟨hc.1.2, v, hc.2, hc.1.1⟩
      rw [hB]
      by_cases hv : kc v = true
      · have hv2 := hv
        simp only [hkc, decide_eq_true_eq] at hv2
        obtain ⟨u', hu'R, hu'⟩ := h2 v hv2.1
        apply hzero _ _ u' v
        · intro i hi
          simp at hi
          obtain ⟨rfl, hi2⟩ := hi
          exact absurd hi2 hu
        · intro j hj
          simp at hj
          exact hj.1
        · exact hu'
      · obtain ⟨u0, hu0, v0, hv0, -⟩ := h3
        obtain ⟨v1, -, hv1⟩ := h1 u0 hu0
        apply hzero _ _ u0 v1
        · intro i hi
          simp at hi
          obtain ⟨rfl, hi2⟩ := hi
          exact absurd hi2 hu
        · intro j hj
          simp at hj
          obtain ⟨rfl, hj2⟩ := hj
          exact absurd hj2 hv
        · exact hv1
  obtain ⟨u0, hu0, v0, hv0, huv0⟩ := h3
  obtain ⟨v1, hv1K, hv1⟩ := h1 u0 hu0
  have hout : (rx_Ls (n + m) C.gates (rx_ini kr kc) C.output).isLeft = false := by
    by_contra hc
    simp only [Bool.not_eq_false] at hc
    obtain ⟨c, hc⟩ := Sum.isLeft_iff.1 hc
    have e1 := (hsem (fun i => decide (i = u0)) (fun j => decide (j = v0))).trans (hpt u0 v0)
    have e2 := (hsem (fun i => decide (i = u0)) (fun j => decide (j = v1))).trans (hpt u0 v1)
    rw [hc] at e1 e2
    simp only [ev_statVal] at e1 e2
    rw [e1] at e2
    simp [huv0, hv1, hu0, hv0, hv1K] at e2
  obtain ⟨jo, hjo⟩ : ∃ jo, rx_Ls (n + m) C.gates (rx_ini kr kc) C.output = Sum.inr jo := by
    cases h : rx_Ls (n + m) C.gates (rx_ini kr kc) C.output with
    | inl c => rw [h] at hout; simp at hout
    | inr jo => exact ⟨jo, rfl⟩
  set D : Circuit := ⟨(ev_elimPass (n + m) C.gates (rx_ini kr kc, [])).2, jo⟩ with hD
  have hDeval : ∀ (p : Fin n → Bool) (q : Fin m → Bool), D.eval (List.ofFn p ++ List.ofFn q) =
      C.eval (List.ofFn (fun i => p i && kr i) ++ List.ofFn (fun j => q j && kc j)) := by
    intro p q
    rw [← hsem p q, hjo]
    rfl
  have hDrep : PEqualNP.Represents.Represents
      (fun u v => A u v && decide (u ∈ R) && decide (v ∈ K)) D := by
    intro u v
    exact (hDeval (fun i => decide (i = u)) (fun j => decide (j = v))).trans (hpt u v)
  have hDmono : Monotone2 D := by
    intro g hg
    exact rx_pass_ok (n + m) C.gates _ (rx_mok_of hC) (by intro g hg; simp at hg) g hg
  set Zread := ((Finset.range (n + m)).filter
      (fun i => (rx_Ls (n + m) C.gates (rx_ini kr kc) i).isLeft = true)).filter
      (fun i => ∃ j < C.gates.length, i ∈ (rx_gk C.gates j).inputs) with hZread
  have hfin : Zread.card + (ev_elimPass (n + m) C.gates (rx_ini kr kc, [])).2.length
      ≤ C.gates.length :=
    rx_final (n + m) C.gates (rx_ini kr kc) (rx_ini_len kr kc) (rx_mok_of hC) C.output hout hmin
  have hLsi : ∀ i, i < n + m →
      rx_Ls (n + m) C.gates (rx_ini kr kc) i = (rx_ini kr kc).getD i (Sum.inl false) := by
    intro i hi
    exact (rx_Ls_eq (n + m) C.gates (rx_ini kr kc) 0 i (Nat.zero_le _)
      (by rw [rx_ini_len]; omega)).symm
  have hunread : ∀ w, w < n + m → rx_Ls (n + m) C.gates (rx_ini kr kc) w = Sum.inl false →
      (∀ j < C.gates.length, w ∉ (rx_gk C.gates j).inputs) →
      ∀ x1 x2 : List Bool, x1.length = n + m → x2.length = n + m →
        (∀ i, i ≠ w → x1.getD i false = x2.getD i false) → C.eval x1 = C.eval x2 := by
    intro w hw hLw hnr x1 x2 hx1 hx2 hag
    have hrd : ∀ g ∈ C.gates, ∀ i ∈ g.inputs, i ∉ ({w} : Set ℕ) := by
      intro g hg i hi hiw
      simp only [Set.mem_singleton_iff] at hiw
      subst hiw
      obtain ⟨t, ht, hgt⟩ := List.mem_iff_getElem.1 hg
      apply hnr t ht
      unfold rx_gk
      rw [List.getD_eq_getElem _ _ ht, hgt]
      exact hi
    have h := ev_W_agree C.gates {w} x1 x2 (by rw [hx1, hx2])
      (by intro b hb; simp only [Set.mem_singleton_iff] at hb; omega)
      (by intro i hi; simp only [Set.mem_singleton_iff] at hi; exact hag i hi) hrd
    have hwo : C.output ≠ w := by
      intro he
      rw [he, hLw] at hout
      simp at hout
    exact h.2 C.output (by simp only [Set.mem_singleton_iff]; exact hwo)
  set Zr := (Finset.univ.filter (fun a : Fin n => ∃ b : Fin m, A a b = true ∧ ∃ a' : Fin n, A a' b = false)) \ (R.filter (fun a => ∃ b ∈ K, A a b = true)) with hZr
  set Zc := (Finset.univ.filter (fun b : Fin m => ∃ a : Fin n, A a b = true ∧ ∃ b' : Fin m, A a b' = false)) \ (K.filter (fun b => ∃ a ∈ R, A a b = true)) with hZc
  have hmemr : ∀ a ∈ Zr, (a : ℕ) ∈ Zread := by
    intro a ha
    have haL := a.isLt
    simp only [hZr, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    obtain ⟨⟨b, hab, a', ha'b⟩, hnot⟩ := ha
    have hka : kr a = false := by
      simp only [hkr, decide_eq_false_iff_not]
      exact hnot
    have hLa : rx_Ls (n + m) C.gates (rx_ini kr kc) a = Sum.inl false := by
      rw [hLsi a (by omega), rx_ini, rx_gd2, dif_pos a.isLt]
      simp [hka]
    simp only [hZread, Finset.mem_filter, Finset.mem_range]
    refine ⟨⟨by omega, by rw [hLa]; rfl⟩, ?_⟩
    by_contra hnr
    push_neg at hnr
    have e := hunread a (by omega) hLa hnr
      (List.ofFn (fun i => decide (i = a)) ++ List.ofFn (fun j => decide (j = b)))
      (List.ofFn (fun _ : Fin n => false) ++ List.ofFn (fun j => decide (j = b)))
      (by simp) (by simp)
      (by
        intro i hi
        rw [rx_gd2, rx_gd2]
        by_cases h : i < n
        · simp only [dif_pos h, decide_eq_false_iff_not]
          intro he
          apply hi
          exact congrArg Fin.val he
        · simp [h])
    have e1 := hrep a b
    unfold PEqualNP.Represents.oneEach at e1
    rw [e1, hab, hzero (fun _ => false) (fun j => decide (j = b)) a' b (by simp)
      (by intro j hj; simpa using hj) ha'b] at e
    exact absurd e (by simp)
  have hmemc : ∀ b ∈ Zc, n + (b : ℕ) ∈ Zread := by
    intro b hb
    have hbL := b.isLt
    simp only [hZc, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hb
    obtain ⟨⟨a, hab, b', hab'⟩, hnot⟩ := hb
    have hkb : kc b = false := by
      simp only [hkc, decide_eq_false_iff_not]
      exact hnot
    have hLb : rx_Ls (n + m) C.gates (rx_ini kr kc) (n + b) = Sum.inl false := by
      rw [hLsi (n + b) (by omega), rx_ini, rx_gd2, dif_neg (by omega), dif_pos (by omega)]
      have hfb : (⟨n + (b : ℕ) - n, by omega⟩ : Fin m) = b := Fin.ext (by simp)
      simp [hfb, hkb]
    simp only [hZread, Finset.mem_filter, Finset.mem_range]
    refine ⟨⟨by omega, by rw [hLb]; rfl⟩, ?_⟩
    by_contra hnr
    push_neg at hnr
    have e := hunread (n + b) (by omega) hLb hnr
      (List.ofFn (fun i => decide (i = a)) ++ List.ofFn (fun j => decide (j = b)))
      (List.ofFn (fun i => decide (i = a)) ++ List.ofFn (fun _ : Fin m => false))
      (by simp) (by simp)
      (by
        intro i hi
        rw [rx_gd2, rx_gd2]
        by_cases h : i < n
        · simp [h]
        · by_cases h2 : i - n < m
          · simp only [dif_neg h, dif_pos h2, decide_eq_false_iff_not]
            intro he
            apply hi
            have h3 : i - n = (b : ℕ) := congrArg Fin.val he
            omega
          · simp [h, h2])
    have e1 := hrep a b
    unfold PEqualNP.Represents.oneEach at e1
    rw [e1, hab, hzero (fun i => decide (i = a)) (fun _ => false) a b' (by intro i hi; simpa using hi)
      (by simp) hab'] at e
    exact absurd e (by simp)
  have hcardZ : Zr.card + Zc.card ≤ Zread.card := by
    have hinj : Function.Injective (fun b : Fin m => n + (b : ℕ)) := by
      intro x y h
      exact Fin.ext (by simpa using h)
    have hdisj : Disjoint (Zr.map ⟨fun a : Fin n => (a : ℕ), Fin.val_injective⟩)
        (Zc.map ⟨fun b : Fin m => n + (b : ℕ), hinj⟩) := by
      rw [Finset.disjoint_left]
      intro i hi1 hi2
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hi1 hi2
      obtain ⟨a, -, rfl⟩ := hi1
      obtain ⟨b, -, hb⟩ := hi2
      have := a.isLt
      omega
    have hsub : (Zr.map ⟨fun a : Fin n => (a : ℕ), Fin.val_injective⟩) ∪
        (Zc.map ⟨fun b : Fin m => n + (b : ℕ), hinj⟩) ⊆ Zread := by
      intro i hi
      rcases Finset.mem_union.1 hi with hi | hi
      · simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hi
        obtain ⟨a, ha, rfl⟩ := hi
        exact hmemr a ha
      · simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hi
        obtain ⟨b, hb, rfl⟩ := hi
        exact hmemc b hb
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_map, Finset.card_map] at this
    exact this
  have hsubr : R.filter (fun a => ∃ b ∈ K, A a b = true) ⊆
      Finset.univ.filter (fun a : Fin n => ∃ b : Fin m, A a b = true ∧ ∃ a' : Fin n, A a' b = false) := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    obtain ⟨-, b, hbK, hab⟩ := ha
    obtain ⟨a', -, ha'⟩ := h2 b hbK
    exact ⟨b, hab, a', ha'⟩
  have hsubc : K.filter (fun b => ∃ a ∈ R, A a b = true) ⊆
      Finset.univ.filter (fun b : Fin m => ∃ a : Fin n, A a b = true ∧ ∃ b' : Fin m, A a b' = false) := by
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    obtain ⟨-, a, haR, hab⟩ := hb
    obtain ⟨b', -, hb'⟩ := h1 a haR
    exact ⟨a, hab, b', hb'⟩
  have er := Finset.card_sdiff_add_card_eq_card hsubr
  have ec := Finset.card_sdiff_add_card_eq_card hsubc
  rw [← hZr] at er
  rw [← hZc] at ec
  refine ⟨D.size, ⟨D, hDmono, le_rfl, hDrep⟩, ?_⟩
  have hDs : D.size = (ev_elimPass (n + m) C.gates (rx_ini kr kc, [])).2.length := rfl
  have hCs : C.size = C.gates.length := rfl
  omega

theorem main_aux : ∀ (n m s : ℕ) (A : Fin n → Fin m → Bool) (R : Finset (Fin n)) (K : Finset (Fin m)), (∀ u ∈ R, ∃ v ∈ K, A u v = false) → (∀ v ∈ K, ∃ u ∈ R, A u v = false) → (∃ u ∈ R, ∃ v ∈ K, A u v = true) → PEqualNP.Represents.RepSizeAtMost A s → ∃ s' : ℕ, PEqualNP.Represents.RepSizeAtMost (fun u v => A u v && decide (u ∈ R) && decide (v ∈ K)) s' ∧ s' + ((Finset.univ.filter (fun a : Fin n => ∃ b : Fin m, A a b = true ∧ ∃ a' : Fin n, A a' b = false)).card + (Finset.univ.filter (fun b : Fin m => ∃ a : Fin n, A a b = true ∧ ∃ b' : Fin m, A a b' = false)).card) ≤ s + ((R.filter (fun a => ∃ b ∈ K, A a b = true)).card + (K.filter (fun b => ∃ a ∈ R, A a b = true)).card) := by
  intro n m s A R K h1 h2 h3 hs
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    obtain ⟨C, hC, hsz, hrep⟩ := hs
    by_cases hmin : ∀ j < C.gates.length, n + m + j ≠ C.output →
        ∃ k, j < k ∧ k < C.gates.length ∧ n + m + j ∈ (rx_gk C.gates k).inputs
    · exact rx_core A R K h1 h2 h3 C hC hsz hrep hmin
    · push_neg at hmin
      obtain ⟨j, hj, hjo, hno⟩ := hmin
      have hs' := rx_drop A C hC hrep j hj hjo hno
      have hCs : C.size = C.gates.length := rfl
      obtain ⟨s', hs1, hs2⟩ := ih (C.gates.length - 1) (by omega) hs'
      exact ⟨s', hs1, by omega⟩

end PEqualNP.Outside.L_meta_7872

theorem PEqualNP.Outside.L_meta_7872 : ∀ (n m s : ℕ) (A : Fin n → Fin m → Bool) (R : Finset (Fin n)) (K : Finset (Fin m)), (∀ u ∈ R, ∃ v ∈ K, A u v = false) → (∀ v ∈ K, ∃ u ∈ R, A u v = false) → (∃ u ∈ R, ∃ v ∈ K, A u v = true) → PEqualNP.Represents.RepSizeAtMost A s → ∃ s' : ℕ, PEqualNP.Represents.RepSizeAtMost (fun u v => A u v && decide (u ∈ R) && decide (v ∈ K)) s' ∧ s' + ((Finset.univ.filter (fun a : Fin n => ∃ b : Fin m, A a b = true ∧ ∃ a' : Fin n, A a' b = false)).card + (Finset.univ.filter (fun b : Fin m => ∃ a : Fin n, A a b = true ∧ ∃ b' : Fin m, A a b' = false)).card) ≤ s + ((R.filter (fun a => ∃ b ∈ K, A a b = true)).card + (K.filter (fun b => ∃ a ∈ R, A a b = true)).card) :=
  PEqualNP.Outside.L_meta_7872.main_aux
