import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18250

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

def kx_MOk (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem kx_mok_op (g : Gate) (h : kx_MOk g) : g.op = GateOp.and ∨ g.op = GateOp.or := by
  have h1 := h.1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
  exact h1

theorem kx_simp_op (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (m : ℕ)
    (ins : List (Bool ⊕ ℕ)) : ∀ g ∈ (ev_simp op m ins).1, kx_MOk g := by
  intro g hg
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [ev_simp, ev_simpAnd] at hg
    subst hg; simp [kx_MOk]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [ev_simp, ev_simpOr] at hg
    subst hg; simp [kx_MOk]

def kx_step (N : ℕ) (K : Finset ℕ) (ov : ℕ → Bool ⊕ ℕ) (acc : List (Bool ⊕ ℕ) × List Gate)
    (g : Gate) : List (Bool ⊕ ℕ) × List Gate :=
  if acc.1.length - N ∈ K then
    (acc.1 ++ [Sum.elim Sum.inl (fun w => acc.1.getD w (Sum.inl false)) (ov (acc.1.length - N))],
      acc.2)
  else ev_elimStep N acc g

def kx_pass (N : ℕ) (K : Finset ℕ) (ov : ℕ → Bool ⊕ ℕ) (gs : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) : List (Bool ⊕ ℕ) × List Gate :=
  gs.foldl (kx_step N K ov) acc

def kx_ini (N : ℕ) : List (Bool ⊕ ℕ) := (List.range N).map Sum.inr

theorem kx_pass_snoc (N : ℕ) (K : Finset ℕ) (ov : ℕ → Bool ⊕ ℕ) (gs : List Gate) (g : Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) :
    kx_pass N K ov (gs ++ [g]) acc = kx_step N K ov (kx_pass N K ov gs acc) g := by
  unfold kx_pass
  rw [List.foldl_append]
  rfl

theorem kx_step_len (N : ℕ) (K : Finset ℕ) (ov : ℕ → Bool ⊕ ℕ) (acc : List (Bool ⊕ ℕ) × List Gate)
    (g : Gate) : (kx_step N K ov acc g).1.length = acc.1.length + 1 := by
  unfold kx_step
  split_ifs
  · simp
  · simp [ev_elimStep]

theorem kx_len (N : ℕ) (K : Finset ℕ) (ov : ℕ → Bool ⊕ ℕ) (gs : List Gate) :
    ∀ acc : List (Bool ⊕ ℕ) × List Gate, (kx_pass N K ov gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    show (kx_pass N K ov gs (kx_step N K ov acc g)).1.length = _
    rw [ih, kx_step_len, List.length_cons]
    omega

theorem kx_getD_lt (N : ℕ) (K : Finset ℕ) (ov : ℕ → Bool ⊕ ℕ) (gs : List Gate) :
    ∀ (acc : List (Bool ⊕ ℕ) × List Gate) (i : ℕ), i < acc.1.length →
      (kx_pass N K ov gs acc).1.getD i (Sum.inl false) = acc.1.getD i (Sum.inl false) := by
  induction gs with
  | nil => intro acc i _; rfl
  | cons g gs ih =>
    intro acc i hi
    show (kx_pass N K ov gs (kx_step N K ov acc g)).1.getD i (Sum.inl false) = _
    rw [ih _ i (by rw [kx_step_len]; omega)]
    unfold kx_step
    split_ifs
    · exact ev_getD_snoc_lt _ _ _ _ hi
    · exact ev_getD_snoc_lt _ _ _ _ hi

theorem kx_ok (N : ℕ) (K : Finset ℕ) (ov : ℕ → Bool ⊕ ℕ) (gs : List Gate)
    (hgs : ∀ g ∈ gs, kx_MOk g) :
    ∀ acc : List (Bool ⊕ ℕ) × List Gate, (∀ g ∈ acc.2, kx_MOk g) →
      ∀ g ∈ (kx_pass N K ov gs acc).2, kx_MOk g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    intro g' hg'
    unfold kx_step at hg'
    split_ifs at hg'
    · exact h g' hg'
    · rcases List.mem_append.1 hg' with h1 | h1
      · exact h g' h1
      · exact kx_simp_op _ (kx_mok_op g (hgs g List.mem_cons_self)) _ _ g' (by simpa using h1)

theorem kx_step_snd (N : ℕ) (K : Finset ℕ) (ov : ℕ → Bool ⊕ ℕ)
    (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) (h : acc.1.length - N ∈ K) :
    (kx_step N K ov acc g).2 = acc.2 := by
  unfold kx_step
  rw [if_pos h]

theorem kx_step_snd_le (N : ℕ) (K : Finset ℕ) (ov : ℕ → Bool ⊕ ℕ)
    (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
    (kx_step N K ov acc g).2.length ≤ acc.2.length + 1 := by
  unfold kx_step
  split_ifs
  · simp
  · simp only [ev_elimStep, List.length_append]
    have := ev_toList_len_le (ev_simp g.op (N + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
    omega

theorem kx_cnt (N : ℕ) (K : Finset ℕ) (ov : ℕ → Bool ⊕ ℕ) (gs : List Gate) :
    ∀ k ≤ gs.length, (kx_pass N K ov (gs.take k) (kx_ini N, [])).2.length +
      ((Finset.range k).filter (fun j => j ∈ K)).card ≤ k := by
  intro k
  induction k with
  | zero => intro _; simp [kx_pass]
  | succ k ih =>
    intro hk
    have ih' := ih (by omega)
    have hkl : k < gs.length := by omega
    have htake : gs.take (k + 1) = gs.take k ++ [gs[k]] := by
      rw [List.take_succ, List.getElem?_eq_getElem hkl]
      rfl
    have hlen1 : (kx_pass N K ov (gs.take k) (kx_ini N, [])).1.length = N + k := by
      rw [kx_len]
      simp [kx_ini]; omega
    rw [htake, kx_pass_snoc]
    by_cases hkK : k ∈ K
    · have hf : (Finset.range (k + 1)).filter (fun j => j ∈ K) =
          insert k ((Finset.range k).filter (fun j => j ∈ K)) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
        constructor
        · rintro ⟨h1, h2⟩
          by_cases hj : j = k
          · left; exact hj
          · right; exact ⟨by omega, h2⟩
        · rintro (rfl | ⟨h1, h2⟩)
          · exact ⟨by omega, hkK⟩
          · exact ⟨by omega, h2⟩
      have hnot : k ∉ (Finset.range k).filter (fun j => j ∈ K) := by simp
      rw [hf, Finset.card_insert_of_notMem hnot,
        kx_step_snd _ _ _ _ _ (by rw [hlen1, show N + k - N = k by omega]; exact hkK)]
      omega
    · have hf : (Finset.range (k + 1)).filter (fun j => j ∈ K) =
          (Finset.range k).filter (fun j => j ∈ K) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_range]
        constructor
        · rintro ⟨h1, h2⟩
          have hj : j ≠ k := by rintro rfl; exact hkK h2
          exact ⟨by omega, h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨by omega, h2⟩
      rw [hf]
      have := kx_step_snd_le N K ov (kx_pass N K ov (gs.take k) (kx_ini N, [])) gs[k]
      omega

theorem kx_ini_getD (N i : ℕ) (hi : i < N) : (kx_ini N).getD i (Sum.inl false) = Sum.inr i := by
  unfold kx_ini
  rw [List.getD_eq_getElem _ _ (by simp; exact hi)]
  simp

theorem kx_inv (N : ℕ) (K : Finset ℕ) (ov : ℕ → Bool ⊕ ℕ) (gs : List Gate) (x : List Bool)
    (hx : x.length = N) (hok : ∀ g ∈ gs, ev_OkGate g)
    (hK : ∀ j ∈ K, j < gs.length →
      (∀ b, ov j = Sum.inl b → (W gs x).getD (N + j) false = b) ∧
      (∀ w, ov j = Sum.inr w → w < N + j ∧ (W gs x).getD (N + j) false = (W gs x).getD w false)) :
    ∀ k ≤ gs.length, ev_Inv N x (W (gs.take k) x) (kx_pass N K ov (gs.take k) (kx_ini N, [])) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨hx, by simp [kx_ini, hx, kx_pass, W], ?_⟩
    intro i
    show ev_statValid (N + 0) ((kx_ini N).getD i (Sum.inl false)) ∧
      ev_statVal (W [] x) ((kx_ini N).getD i (Sum.inl false)) = (W [] x).getD i false
    by_cases hi : i < N
    · rw [kx_ini_getD N i hi]
      exact ⟨by show i < N + 0; omega, rfl⟩
    · rw [List.getD_eq_default _ _ (by simp [kx_ini]; omega)]
      refine ⟨trivial, ?_⟩
      show false = x.getD i false
      rw [getD_ge _ _ (by omega)]
  | succ k ih =>
    intro hk
    have hkl : k < gs.length := by omega
    have ih' := ih (by omega)
    have htake : gs.take (k + 1) = gs.take k ++ [gs[k]] := by
      rw [List.take_succ, List.getElem?_eq_getElem hkl]
      rfl
    rw [htake, kx_pass_snoc, W_snoc]
    obtain ⟨acc, hacc⟩ : ∃ a, a = kx_pass N K ov (gs.take k) (kx_ini N, []) := ⟨_, rfl⟩
    obtain ⟨wold, hwold⟩ : ∃ w, w = W (gs.take k) x := ⟨_, rfl⟩
    rw [← hacc, ← hwold]
    rw [← hacc, ← hwold] at ih'
    have hwl : wold.length = N + k := by
      rw [hwold, W_length, hx, List.length_take]
      omega
    have hal : acc.1.length = N + k := by rw [ih'.2.1, hwl]
    have hpre : ∀ i, i < N + k → (W gs x).getD i false = wold.getD i false := by
      intro i hi
      rw [W_split gs x k, W_prefix _ _ _ (by rw [← hwold, hwl]; exact hi), hwold]
    have hpre1 : (W gs x).getD (N + k) false = (step wold gs[k]).getD (N + k) false := by
      rw [W_split gs x (k + 1), htake, W_snoc, ← hwold]
      exact W_prefix _ _ _ (by rw [step_len, hwl]; omega)
    unfold kx_step
    rw [hal, show N + k - N = k by omega]
    by_cases hkK : k ∈ K
    · rw [if_pos hkK]
      obtain ⟨hb, hw⟩ := hK k hkK hkl
      obtain ⟨_, _, hi⟩ := ih'
      refine ⟨hx, by simp [step_len, hal, hwl], ?_⟩
      intro i
      dsimp only
      by_cases hlt : i < N + k
      · rw [ev_getD_snoc_lt _ _ _ _ (by rw [hal]; exact hlt), step_lt _ _ _ (by rw [hwl]; exact hlt)]
        exact hi i
      · by_cases heq : i = N + k
        · subst heq
          rw [ev_getD_snoc_eq _ _ _ _ hal.symm, ← hpre1]
          cases hov : ov k with
          | inl b =>
            refine ⟨trivial, ?_⟩
            show b = _
            rw [hb b hov]
          | inr w =>
            obtain ⟨hwlt, hweq⟩ := hw w hov
            refine ⟨(hi w).1, ?_⟩
            show ev_statVal (W acc.2 x) (acc.1.getD w (Sum.inl false)) = _
            rw [(hi w).2, hweq, hpre w hwlt]
        · rw [List.getD_eq_default _ _ (by simp; omega), getD_ge _ _ (by rw [step_len]; omega)]
          exact ⟨trivial, rfl⟩
    · rw [if_neg hkK]
      exact ev_Inv_step N x wold acc gs[k] (hok _ (List.getElem_mem hkl)) ih'

theorem main_aux : ∀ (n m : ℕ) (A : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (ZL : Finset (Fin n)) (ZR : Finset (Fin m))
  (K : Finset ℕ), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.Represents.Represents A C →
  (∀ j ∈ K, j < C.gates.length ∧ n + m + j ≠ C.output ∧
    ((∃ b : Bool, ∀ (u : Fin n) (v : Fin m), u ∉ ZL → v ∉ ZR →
        (C.wires (PEqualNP.Represents.oneEach u v)).getD (n + m + j) false = b) ∨
     (∃ w < n + m + j, ∀ (u : Fin n) (v : Fin m), u ∉ ZL → v ∉ ZR →
        (C.wires (PEqualNP.Represents.oneEach u v)).getD (n + m + j) false =
          (C.wires (PEqualNP.Represents.oneEach u v)).getD w false))) →
  ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C' ∧ C'.size + K.card ≤ C.size ∧
    ∀ (u : Fin n) (v : Fin m), u ∉ ZL → v ∉ ZR → C'.eval (PEqualNP.Represents.oneEach u v) = A u v := by
  intro n m A C ZL ZR K hC hrep hK
  have hok : ∀ g ∈ C.gates, ev_OkGate g := by
    intro g hg
    have h := kx_mok_op g (hC g hg)
    refine ⟨?_, (hC g hg).2⟩
    rcases h with h | h <;> rw [h] <;> simp
  have hex : ∀ j, ∃ o : Bool ⊕ ℕ, j ∈ K →
      (∀ b, o = Sum.inl b → ∀ (u : Fin n) (v : Fin m), u ∉ ZL → v ∉ ZR →
        (C.wires (PEqualNP.Represents.oneEach u v)).getD (n + m + j) false = b) ∧
      (∀ w, o = Sum.inr w → w < n + m + j ∧ ∀ (u : Fin n) (v : Fin m), u ∉ ZL → v ∉ ZR →
        (C.wires (PEqualNP.Represents.oneEach u v)).getD (n + m + j) false =
          (C.wires (PEqualNP.Represents.oneEach u v)).getD w false) := by
    intro j
    by_cases hj : j ∈ K
    · obtain ⟨-, -, h⟩ := hK j hj
      rcases h with ⟨b, hb⟩ | ⟨w, hw, hw2⟩
      · refine ⟨Sum.inl b, fun _ => ⟨?_, ?_⟩⟩
        · intro b' hb'
          cases hb'
          exact hb
        · intro w' hw'
          cases hw'
      · refine ⟨Sum.inr w, fun _ => ⟨?_, ?_⟩⟩
        · intro b' hb'
          cases hb'
        · intro w' hw'
          cases hw'
          exact ⟨hw, hw2⟩
    · exact ⟨Sum.inl false, fun h => absurd h hj⟩
  choose ov hov using hex
  have hKl : ∀ j ∈ K, j < C.gates.length := fun j hj => (hK j hj).1
  have hKo : ∀ j ∈ K, n + m + j ≠ C.output := fun j hj => (hK j hj).2.1
  set N := n + m with hN
  set F := kx_pass N K ov C.gates (kx_ini N, []) with hF
  have hFl : F.1.length = N + C.gates.length := by
    rw [hF, kx_len]
    simp [kx_ini]
  have hcnt := kx_cnt N K ov C.gates C.gates.length le_rfl
  rw [List.take_length, ← hF] at hcnt
  have hKf : (Finset.range C.gates.length).filter (fun j => j ∈ K) = K := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨hKl j h, h⟩⟩
  rw [hKf] at hcnt
  have hFok : ∀ g ∈ F.2, kx_MOk g :=
    kx_ok N K ov C.gates (fun g hg => hC g hg) _ (by intro g hg; simp at hg)
  have hval : ∀ (u : Fin n) (v : Fin m), u ∉ ZL → v ∉ ZR →
      ev_statVal (W F.2 (PEqualNP.Represents.oneEach u v)) (F.1.getD C.output (Sum.inl false)) =
        A u v := by
    intro u v hu hv
    have hxl : (PEqualNP.Represents.oneEach u v).length = N := by
      simp [PEqualNP.Represents.oneEach, hN]
    have hinv := kx_inv N K ov C.gates (PEqualNP.Represents.oneEach u v) hxl hok
      (by
        intro j hj _
        refine ⟨fun b hb => ((hov j hj).1 b hb) u v hu hv, fun w hw => ?_⟩
        obtain ⟨h1, h2⟩ := (hov j hj).2 w hw
        exact ⟨h1, h2 u v hu hv⟩)
      C.gates.length le_rfl
    rw [List.take_length, ← hF] at hinv
    rw [(hinv.2.2 C.output).2]
    exact hrep u v
  cases hso : F.1.getD C.output (Sum.inl false) with
  | inr jo =>
    refine ⟨⟨F.2, jo⟩, hFok, by show F.2.length + K.card ≤ C.gates.length; omega, ?_⟩
    intro u v hu hv
    have := hval u v hu hv
    rw [hso] at this
    exact this
  | inl b =>
    cases b with
    | false =>
      refine ⟨⟨F.2, N + C.gates.length⟩, hFok,
        by show F.2.length + K.card ≤ C.gates.length; omega, ?_⟩
      intro u v hu hv
      have := hval u v hu hv
      rw [hso] at this
      have hxl : (PEqualNP.Represents.oneEach u v).length = N := by
        simp [PEqualNP.Represents.oneEach, hN]
      show (W F.2 (PEqualNP.Represents.oneEach u v)).getD (N + C.gates.length) false = A u v
      rw [W_ge _ _ _ (by rw [hxl]; omega)]
      exact this
    | true =>
      have hoN : N ≤ C.output := by
        by_contra hlt
        push_neg at hlt
        have h1 := kx_getD_lt N K ov C.gates (kx_ini N, []) C.output
          (by simp [kx_ini]; exact hlt)
        rw [← hF, hso] at h1
        cases (h1.trans (kx_ini_getD N _ hlt))
      have hoL : C.output < N + C.gates.length := by
        by_contra hge
        push_neg at hge
        rw [List.getD_eq_default _ _ (by rw [hFl]; exact hge)] at hso
        cases hso
      have hjo : C.output - N ∉ K := by
        intro hj
        exact hKo _ hj (by omega)
      have hsub : insert (C.output - N) K ⊆ Finset.range C.gates.length := by
        intro j hj
        rcases Finset.mem_insert.1 hj with h | h
        · rw [h, Finset.mem_range]; omega
        · exact Finset.mem_range.2 (hKl j h)
      have hc := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hjo, Finset.card_range] at hc
      refine ⟨⟨[⟨GateOp.and, []⟩], N⟩, ?_, ?_, ?_⟩
      · intro g hg
        simp at hg
        subst hg
        simp
      · show 1 + K.card ≤ C.gates.length
        omega
      · intro u v hu hv
        have := hval u v hu hv
        rw [hso] at this
        have hxl : (PEqualNP.Represents.oneEach u v).length = N := by
          simp [PEqualNP.Represents.oneEach, hN]
        show (W [⟨GateOp.and, []⟩] (PEqualNP.Represents.oneEach u v)).getD N false = A u v
        rw [W_single, step_last _ _ _ hxl.symm]
        exact this

end PEqualNP.Outside.L_meta_18250

theorem PEqualNP.Outside.L_meta_18250 : ∀ (n m : ℕ) (A : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (ZL : Finset (Fin n)) (ZR : Finset (Fin m))
  (K : Finset ℕ), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.Represents.Represents A C →
  (∀ j ∈ K, j < C.gates.length ∧ n + m + j ≠ C.output ∧
    ((∃ b : Bool, ∀ (u : Fin n) (v : Fin m), u ∉ ZL → v ∉ ZR →
        (C.wires (PEqualNP.Represents.oneEach u v)).getD (n + m + j) false = b) ∨
     (∃ w < n + m + j, ∀ (u : Fin n) (v : Fin m), u ∉ ZL → v ∉ ZR →
        (C.wires (PEqualNP.Represents.oneEach u v)).getD (n + m + j) false =
          (C.wires (PEqualNP.Represents.oneEach u v)).getD w false))) →
  ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C' ∧ C'.size + K.card ≤ C.size ∧
    ∀ (u : Fin n) (v : Fin m), u ∉ ZL → v ∉ ZR → C'.eval (PEqualNP.Represents.oneEach u v) = A u v :=
  PEqualNP.Outside.L_meta_18250.main_aux
