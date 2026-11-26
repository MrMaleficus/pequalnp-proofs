import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20784

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

theorem ev_not1 (a : Bool) : GateOp.not.eval [a] = !a := rfl

def par (L : List Bool) (k : ℕ) : Bool := decide ((L.take (k + 1)).count true % 2 = 1)

theorem par_zero (L : List Bool) : par L 0 = L.getD 0 false := by
  cases L with
  | nil => simp [par]
  | cons a t => cases a <;> simp [par]

theorem par_succ (L : List Bool) (k : ℕ) (hk : k + 1 < L.length) :
    par L (k + 1) = xor (par L k) (L.getD (k + 1) false) := by
  unfold par
  have e : L.take (k + 1 + 1) = L.take (k + 1) ++ [L.getD (k + 1) false] := by
    rw [List.take_succ, List.getElem?_eq_getElem hk]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  rw [e, List.count_append]
  generalize (L.take (k + 1)).count true = c
  cases L.getD (k + 1) false
  · rw [show List.count true [false] = 0 from rfl, Nat.add_zero]
    cases decide (c % 2 = 1) <;> rfl
  · rw [show List.count true [true] = 1 from rfl]
    by_cases h : c % 2 = 1
    · rw [decide_eq_true h, decide_eq_false (by omega)]
      rfl
    · rw [decide_eq_false h, decide_eq_true (by omega)]
      rfl

def gt (n j : ℕ) : Gate :=
  if j % 4 = 0 then ⟨GateOp.or, [if j / 4 = 0 then 0 else n + j - 1, j / 4 + 1]⟩
  else if j % 4 = 1 then ⟨GateOp.and, [if j / 4 = 0 then 0 else n + j - 2, j / 4 + 1]⟩
  else if j % 4 = 2 then ⟨GateOp.not, [n + j - 1]⟩
  else ⟨GateOp.and, [n + j - 3, n + j - 1]⟩

def gl (n : ℕ) : List Gate := (List.range (4 * (n - 1))).map (gt n)

def spec (L : List Bool) (j : ℕ) : Bool :=
  if j % 4 = 0 then (par L (j / 4) || L.getD (j / 4 + 1) false)
  else if j % 4 = 1 then (par L (j / 4) && L.getD (j / 4 + 1) false)
  else if j % 4 = 2 then !(par L (j / 4) && L.getD (j / 4 + 1) false)
  else par L (j / 4 + 1)

def rv (L : List Bool) (n i : ℕ) : Bool := if i < n then L.getD i false else spec L (i - n)

theorem rv_in (L : List Bool) (n i : ℕ) (h : i < n) : rv L n i = L.getD i false := by
  unfold rv
  rw [if_pos h]

theorem rv_gate (L : List Bool) (n k : ℕ) : rv L n (n + k) = spec L k := by
  unfold rv
  rw [if_neg (by omega)]
  congr 1
  omega

theorem sp0 (L : List Bool) (b : ℕ) : spec L (4 * b) = (par L b || L.getD (b + 1) false) := by
  unfold spec
  rw [if_pos (by omega), show 4 * b / 4 = b by omega]

theorem sp1 (L : List Bool) (b : ℕ) : spec L (4 * b + 1) = (par L b && L.getD (b + 1) false) := by
  unfold spec
  rw [if_neg (by omega), if_pos (by omega), show (4 * b + 1) / 4 = b by omega]

theorem sp2 (L : List Bool) (b : ℕ) : spec L (4 * b + 2) = !(par L b && L.getD (b + 1) false) := by
  unfold spec
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), show (4 * b + 2) / 4 = b by omega]

theorem sp3 (L : List Bool) (b : ℕ) : spec L (4 * b + 3) = par L (b + 1) := by
  unfold spec
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), show (4 * b + 3) / 4 = b by omega]

theorem racc (L : List Bool) (n b : ℕ) (hb : b + 1 < n) :
    rv L n (if b = 0 then 0 else n + 4 * b - 1) = par L b := by
  by_cases h0 : b = 0
  · subst h0
    rw [if_pos rfl, rv_in L n 0 (by omega), par_zero]
  · rw [if_neg h0]
    obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
    rw [show n + 4 * (c + 1) - 1 = n + (4 * c + 3) by omega, rv_gate, sp3]

theorem step_in (n j : ℕ) (hj : j < 4 * (n - 1)) : ∀ i ∈ (gt n j).inputs, i < n + j := by
  intro i hi
  unfold gt at hi
  split_ifs at hi <;> simp at hi <;> omega

theorem step_ok (n : ℕ) (L : List Bool) (j : ℕ) (hL : L.length = n) (hj : j < 4 * (n - 1)) :
    (gt n j).op.eval ((gt n j).inputs.map (rv L n)) = spec L j := by
  obtain ⟨b, r, hr, rfl⟩ : ∃ b r, r < 4 ∧ j = 4 * b + r := ⟨j / 4, j % 4, by omega, by omega⟩
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl
  · rw [Nat.add_zero] at hj ⊢
    have hg : gt n (4 * b) = ⟨GateOp.or, [if b = 0 then 0 else n + 4 * b - 1, b + 1]⟩ := by
      unfold gt
      rw [if_pos (by omega), show 4 * b / 4 = b by omega]
    rw [hg, sp0]
    show GateOp.or.eval [rv L n (if b = 0 then 0 else n + 4 * b - 1), rv L n (b + 1)] = _
    rw [eval_or2, racc L n b (by omega), rv_in L n (b + 1) (by omega)]
  · have hg : gt n (4 * b + 1) =
        ⟨GateOp.and, [if b = 0 then 0 else n + (4 * b + 1) - 2, b + 1]⟩ := by
      unfold gt
      rw [if_neg (by omega), if_pos (by omega), show (4 * b + 1) / 4 = b by omega]
    rw [hg, sp1]
    show GateOp.and.eval [rv L n (if b = 0 then 0 else n + (4 * b + 1) - 2), rv L n (b + 1)] = _
    rw [show n + (4 * b + 1) - 2 = n + 4 * b - 1 by omega, eval_and2, racc L n b (by omega),
      rv_in L n (b + 1) (by omega)]
  · have hg : gt n (4 * b + 2) = ⟨GateOp.not, [n + (4 * b + 2) - 1]⟩ := by
      unfold gt
      rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    rw [hg, sp2]
    show GateOp.not.eval [rv L n (n + (4 * b + 2) - 1)] = _
    rw [show n + (4 * b + 2) - 1 = n + (4 * b + 1) by omega, ev_not1, rv_gate, sp1]
  · have hg : gt n (4 * b + 3) = ⟨GateOp.and, [n + (4 * b + 3) - 3, n + (4 * b + 3) - 1]⟩ := by
      unfold gt
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    rw [hg, sp3]
    show GateOp.and.eval [rv L n (n + (4 * b + 3) - 3), rv L n (n + (4 * b + 3) - 1)] = _
    rw [show n + (4 * b + 3) - 3 = n + 4 * b by omega,
      show n + (4 * b + 3) - 1 = n + (4 * b + 2) by omega, eval_and2, rv_gate, rv_gate, sp0, sp2,
      par_succ L b (by omega)]
    cases par L b <;> cases L.getD (b + 1) false <;> rfl

theorem wires_ok (n : ℕ) (L : List Bool) (hL : L.length = n) :
    ∀ j, j < 4 * (n - 1) → (W (gl n) L).getD (n + j) false = spec L j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    have hlen : j < (gl n).length := by
      simp only [gl, List.length_map, List.length_range]
      omega
    have h := W_gate (gl n) L j hlen
    rw [hL] at h
    rw [h]
    have hg : (gl n)[j] = gt n j := by simp [gl]
    rw [hg, ← step_ok n L j hL hj]
    congr 1
    apply List.map_congr_left
    intro i hi
    have hi1 := step_in n j hj i hi
    rw [if_pos hi1]
    by_cases hi3 : i < n
    · rw [W_prefix _ _ _ (by omega), rv_in L n i hi3]
    · have h2 := ih (i - n) (by omega) (by omega)
      rw [show n + (i - n) = i by omega] at h2
      rw [h2]
      unfold rv
      rw [if_neg hi3]

theorem main_aux : ∀ n : ℕ, 1 ≤ n → PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => decide ((List.ofFn x).count true % 2 = 1)) (4 * (n - 1)) := by
  intro n hn
  refine ⟨⟨gl n, if n = 1 then 0 else n + (4 * (n - 1) - 1)⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [gl, List.mem_map, List.mem_range] at hg
    obtain ⟨j, hj, rfl⟩ := hg
    unfold gt
    split_ifs <;> simp
  · show (gl n).length ≤ 4 * (n - 1)
    simp [gl]
  · intro x
    have hL : (List.ofFn x).length = n := List.length_ofFn
    show (W (gl n) (List.ofFn x)).getD (if n = 1 then 0 else n + (4 * (n - 1) - 1)) false = _
    by_cases h1 : n = 1
    · subst h1
      rw [if_pos rfl, W_prefix _ _ _ (by simp), ← par_zero]
      unfold par
      rw [List.take_of_length_le (by simp)]
    · rw [if_neg h1, wires_ok n _ hL _ (by omega)]
      obtain ⟨c, rfl⟩ : ∃ c, n = c + 2 := ⟨n - 2, by omega⟩
      rw [show 4 * (c + 2 - 1) - 1 = 4 * c + 3 by omega, sp3]
      unfold par
      rw [List.take_of_length_le (by simp)]

end PEqualNP.Outside.L_meta_20784

theorem PEqualNP.Outside.L_meta_20784 : ∀ n : ℕ, 1 ≤ n → PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => decide ((List.ofFn x).count true % 2 = 1)) (4 * (n - 1)) :=
  PEqualNP.Outside.L_meta_20784.main_aux
