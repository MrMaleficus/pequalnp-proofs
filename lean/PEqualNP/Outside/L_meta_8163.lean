import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8163

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

-- FRAGMENT bitmask    DEPENDS: fold
-- Truth tables of explicit circuits as Nat bitmasks: bit m of the mask of a wire is its value on the
-- input numbered m (input wire i reads bit i of m). AND, OR and NOT gates (any fan-in); MOD and MAJ unsupported.
-- Exports:
--   def bm_op K op l : mask of a gate from input masks (AND: foldr land (2^K - 1), OR: foldr lor 0, NOT: xor (2^K - 1) (head))
--   def bm_okop op : Bool (true for and, or, not) ;  def bm_ok C : Bool := C.gates.all (bm_okop of op)
--   def bm_step K m g := m ++ [bm_op K g.op (masks of g.inputs)] ;  def bm_W K gs m := gs.foldl (bm_step K) m
--   bm_step_len, bm_step_lt, bm_step_last : as step_len / step_lt / step_last for masks (default 0)
--   bm_op_bit (k < K) (bm_okop op) (fw i = testBit (fm i) k) : testBit (bm_op K op (l.map fm)) k = op.eval (l.map fw)
--   def bm_Rep k w m : w.length = m.length and every w.getD t false = testBit (m.getD t 0) k
--   bm_rep_step, bm_rep_fold (k < K, all ops ok) : bm_Rep k w m -> bm_Rep k (W gs w) (bm_W K gs m)
--   def bm_num : List Bool -> Nat (low bit first) ;  bm_num_lt : bm_num l < 2 ^ l.length
--   bm_num_bit : testBit (bm_num l) i = l.getD i false ;  bm_num_append : bm_num (a ++ b) = bm_num a + 2 ^ a.length * bm_num b
--   def bm_tab p n : mask over 2^n inputs of input wire p ;  bm_tab_spec p m : bm_tab p m < 2^2^m and for k < 2^m, testBit (bm_tab p m) k = testBit k p
--   def bm_init n := (List.range n).map (bm_tab . n) ;  bm_init_len ;  bm_rep_init (x.length = n) : bm_Rep (bm_num x) x (bm_init n)
--   def bm_out n C := (bm_W (2^n) C.gates (bm_init n)).getD C.output 0      (the output mask, computable by decide)
--   bm_eval (bm_ok C) (x.length = n) : C.eval x = testBit (bm_out n C) (bm_num x)
--   def bm_code (x : Fin n -> Bool) := bm_num (List.ofFn x) ;  bm_code_lt : bm_code x < 2 ^ n
--   def bm_input n m : Fin n -> Bool := fun i => testBit m i
--   bm_input_code : bm_input n (bm_code x) = x ;  bm_code_input (m < 2^n) : bm_code (bm_input n m) = m
--   bm_circuitFun (bm_ok C) : circuitFun n C x = testBit (bm_out n C) (bm_code x)
--   bm_circuitFun_num (bm_ok C) (m < 2^n) : circuitFun n C (bm_input n m) = testBit (bm_out n C) m
--   bm_forall_iff : (forall x, P x) iff forall m, m < 2^n -> P (bm_input n m) ;  bm_exists_iff : same for exists (m < 2^n and P ..)
--   bm_fun_eq (bm_ok C) f (h : forall m, m < 2^n -> testBit (bm_out n C) m = f (bm_input n m)) : forall x, circuitFun n C x = f x
--   bm_eval_two (bm_ok C) x y : C.eval (ofFn x ++ ofFn y) = testBit (bm_out (n1 + n2) C) (bm_code x + 2 ^ n1 * bm_code y)
--   bm_fun_eq2 (bm_ok C) f (h : forall a < 2^n1, forall b < 2^n2, testBit (bm_out (n1+n2) C) (a + 2^n1 * b) = f (bm_input n1 a) (bm_input n2 b))
--       : forall x y, C.eval (ofFn x ++ ofFn y) = f x y
-- Use: theorem t : forall x : Fin 3 -> Bool, circuitFun 3 C x = f x := bm_fun_eq 3 C (by decide) _ (by decide +kernel)
--   (C the explicit circuit, f the Boolean formula in x). Other shapes: rw [bm_circuitFun_num n C (by decide) m hm] or
--   rw [bm_eval n C (by decide) x hx], then decide +kernel on the concrete mask (bm_out n C reduces to a numeral).
--   Rows on two input blocks (eval on ofFn x ++ ofFn y): bm_fun_eq2; decide then runs 2^(n1+n2) checks (tested n = 3: whole test 21 s).

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def bm_op (K : ℕ) (op : GateOp) (l : List ℕ) : ℕ :=
  match op with
  | GateOp.and => l.foldr Nat.land (2 ^ K - 1)
  | GateOp.or => l.foldr Nat.lor 0
  | GateOp.not => Nat.xor (2 ^ K - 1) (l.headD 0)
  | _ => 0

def bm_okop (op : GateOp) : Bool :=
  match op with
  | GateOp.and => true
  | GateOp.or => true
  | GateOp.not => true
  | _ => false

def bm_ok (C : Circuit) : Bool := C.gates.all (fun g => bm_okop g.op)

def bm_step (K : ℕ) (m : List ℕ) (g : Gate) : List ℕ :=
  m ++ [bm_op K g.op (g.inputs.map fun i => m.getD i 0)]

def bm_W (K : ℕ) (gs : List Gate) (m : List ℕ) : List ℕ := gs.foldl (bm_step K) m

theorem bm_step_len (K : ℕ) (m : List ℕ) (g : Gate) :
    (bm_step K m g).length = m.length + 1 := by
  simp [bm_step]

theorem bm_step_lt (K : ℕ) (m : List ℕ) (g : Gate) (i : ℕ) (hi : i < m.length) :
    (bm_step K m g).getD i 0 = m.getD i 0 := by
  simp [bm_step, List.getD, List.getElem?_append_left hi]

theorem bm_step_last (K : ℕ) (m : List ℕ) (g : Gate) (k : ℕ) (hk : k = m.length) :
    (bm_step K m g).getD k 0 = bm_op K g.op (g.inputs.map fun i => m.getD i 0) := by
  subst hk
  simp [bm_step, List.getD]

theorem bm_op_bit (K k : ℕ) (hk : k < K) (op : GateOp) (hop : bm_okop op = true)
    (inputs : List ℕ) (fm : ℕ → ℕ) (fw : ℕ → Bool) (h : ∀ i, fw i = Nat.testBit (fm i) k) :
    Nat.testBit (bm_op K op (inputs.map fm)) k = op.eval (inputs.map fw) := by
  cases op with
  | and =>
    show Nat.testBit (List.foldr Nat.land (2 ^ K - 1) (List.map fm inputs)) k =
      (List.map fw inputs).all id
    induction inputs with
    | nil => simp [Nat.testBit_two_pow_sub_one, hk]
    | cons a l ih =>
      show Nat.testBit (fm a &&& List.foldr Nat.land (2 ^ K - 1) (List.map fm l)) k =
        (fw a && (List.map fw l).all id)
      rw [Nat.testBit_and, ih, h a]
  | or =>
    show Nat.testBit (List.foldr Nat.lor 0 (List.map fm inputs)) k =
      (List.map fw inputs).any id
    induction inputs with
    | nil => simp
    | cons a l ih =>
      show Nat.testBit (fm a ||| List.foldr Nat.lor 0 (List.map fm l)) k =
        (fw a || (List.map fw l).any id)
      rw [Nat.testBit_or, ih, h a]
  | not =>
    cases inputs with
    | nil =>
      show Nat.testBit ((2 ^ K - 1) ^^^ 0) k = !false
      simp [Nat.testBit_two_pow_sub_one, hk]
    | cons a l =>
      show Nat.testBit ((2 ^ K - 1) ^^^ fm a) k = !(fw a)
      rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, h a]
      simp [hk]
  | mod m => simp [bm_okop] at hop
  | maj => simp [bm_okop] at hop

def bm_Rep (k : ℕ) (w : List Bool) (m : List ℕ) : Prop :=
  w.length = m.length ∧ ∀ t, w.getD t false = Nat.testBit (m.getD t 0) k

theorem bm_rep_step (K k : ℕ) (hk : k < K) (g : Gate) (hop : bm_okop g.op = true)
    (w : List Bool) (m : List ℕ) (h : bm_Rep k w m) : bm_Rep k (step w g) (bm_step K m g) := by
  have h1 := h.1
  refine ⟨by rw [step_len, bm_step_len, h1], fun t => ?_⟩
  by_cases hlt : t < w.length
  · rw [step_lt w g t hlt, bm_step_lt K m g t (by omega)]
    exact h.2 t
  · by_cases heq : t = w.length
    · rw [step_last w g t heq, bm_step_last K m g t (heq.trans h1)]
      exact (bm_op_bit K k hk g.op hop g.inputs (fun i => m.getD i 0)
        (fun i => w.getD i false) h.2).symm
    · rw [getD_ge (step w g) t (by rw [step_len]; omega),
        List.getD_eq_default (bm_step K m g) 0 (by rw [bm_step_len]; omega)]
      exact (Nat.zero_testBit k).symm

theorem bm_rep_fold (K k : ℕ) (hk : k < K) (gs : List Gate)
    (hg : ∀ g ∈ gs, bm_okop g.op = true) :
    ∀ (w : List Bool) (m : List ℕ), bm_Rep k w m → bm_Rep k (W gs w) (bm_W K gs m) := by
  induction gs with
  | nil =>
    intro w m h
    exact h
  | cons g gs ih =>
    intro w m h
    show bm_Rep k (W gs (step w g)) (bm_W K gs (bm_step K m g))
    exact ih (fun g' hg' => hg g' (List.mem_cons.mpr (Or.inr hg'))) _ _
      (bm_rep_step K k hk g (hg g (List.mem_cons.mpr (Or.inl rfl))) w m h)

def bm_num : List Bool → ℕ
  | [] => 0
  | b :: l => Nat.bit b (bm_num l)

theorem bm_num_lt : ∀ l : List Bool, bm_num l < 2 ^ l.length
  | [] => by decide
  | b :: l => by
    have ih := bm_num_lt l
    have h2 : bm_num (b :: l) = 2 * bm_num l + b.toNat := Nat.bit_val b (bm_num l)
    have hb : b.toNat ≤ 1 := by cases b <;> decide
    rw [h2, List.length_cons, pow_succ]
    omega

theorem bm_num_bit : ∀ (l : List Bool) (i : ℕ), Nat.testBit (bm_num l) i = l.getD i false
  | [], i => by
    first
    | exact Nat.zero_testBit i
    | simp [bm_num]
  | b :: l, 0 => by
    rw [List.getD_cons_zero]
    exact Nat.testBit_bit_zero b (bm_num l)
  | b :: l, i + 1 => by
    rw [List.getD_cons_succ]
    exact (Nat.testBit_bit_succ i b (bm_num l)).trans (bm_num_bit l i)

theorem bm_num_append : ∀ (a b : List Bool), bm_num (a ++ b) = bm_num a + 2 ^ a.length * bm_num b
  | [], b => by simp [bm_num]
  | c :: a, b => by
    have ih := bm_num_append a b
    show Nat.bit c (bm_num (a ++ b)) = Nat.bit c (bm_num a) + 2 ^ (a.length + 1) * bm_num b
    rw [Nat.bit_val, Nat.bit_val, ih, pow_succ]
    ring

-- Mask over the 2 ^ m numbers k below 2 ^ m of bit p of k.
def bm_tab (p : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 =>
    if m = p then 2 ^ 2 ^ m * (2 ^ 2 ^ m - 1) + 0 else (2 ^ 2 ^ m + 1) * bm_tab p m

theorem bm_bnd (A t : ℕ) (h : t < A) : A * t + t < A * A := by
  have h1 := Nat.mul_le_mul_left A (Nat.succ_le_of_lt h)
  rw [Nat.mul_succ] at h1
  omega

theorem bm_tab_spec (p : ℕ) : ∀ m : ℕ, bm_tab p m < 2 ^ 2 ^ m ∧
    ∀ k : ℕ, k < 2 ^ m → Nat.testBit (bm_tab p m) k = Nat.testBit k p := by
  intro m
  induction m with
  | zero =>
    refine ⟨?_, fun k hk => ?_⟩
    · show (0 : ℕ) < 2 ^ 2 ^ 0
      exact Nat.two_pow_pos _
    · have hk0 : k = 0 := by simpa using hk
      rw [hk0]
      show Nat.testBit 0 0 = Nat.testBit 0 p
      rw [Nat.zero_testBit, Nat.zero_testBit]
  | succ m ih =>
    obtain ⟨hb, hbits⟩ := ih
    have hA : 0 < 2 ^ 2 ^ m := Nat.two_pow_pos _
    have hpm : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := Nat.two_pow_succ m
    have hpow : 2 ^ 2 ^ (m + 1) = 2 ^ 2 ^ m * 2 ^ 2 ^ m := by
      rw [hpm, Nat.pow_add]
    by_cases hmp : m = p
    · have hdef : bm_tab p (m + 1) = 2 ^ 2 ^ m * (2 ^ 2 ^ m - 1) + 0 := by
        rw [bm_tab, if_pos hmp]
      rw [hdef, ← hmp]
      refine ⟨?_, fun k hk => ?_⟩
      · have h1 := bm_bnd (2 ^ 2 ^ m) (2 ^ 2 ^ m - 1) (by omega)
        rw [hpow]
        omega
      · rw [Nat.testBit_two_pow_mul_add (2 ^ 2 ^ m - 1) hA k]
        by_cases hlt : k < 2 ^ m
        · rw [if_pos hlt, Nat.zero_testBit, Nat.testBit_lt_two_pow hlt]
        · rw [if_neg hlt, Nat.testBit_two_pow_sub_one]
          have h1 : Nat.testBit k m = true := by
            have h2 := Nat.testBit_two_pow_add_eq (k - 2 ^ m) m
            rw [show 2 ^ m + (k - 2 ^ m) = k from by omega,
              Nat.testBit_lt_two_pow (show k - 2 ^ m < 2 ^ m from by omega)] at h2
            exact h2
          rw [h1]
          exact decide_eq_true (by omega)
    · have hdef : bm_tab p (m + 1) = 2 ^ 2 ^ m * bm_tab p m + bm_tab p m := by
        rw [bm_tab, if_neg hmp]
        ring
      rw [hdef]
      refine ⟨?_, fun k hk => ?_⟩
      · have h1 := bm_bnd (2 ^ 2 ^ m) (bm_tab p m) hb
        rw [hpow]
        exact h1
      · rw [Nat.testBit_two_pow_mul_add (bm_tab p m) hb k]
        by_cases hlt : k < 2 ^ m
        · rw [if_pos hlt]
          exact hbits k hlt
        · rw [if_neg hlt, hbits (k - 2 ^ m) (by omega)]
          rcases Nat.lt_or_gt_of_ne hmp with hlt2 | hgt
          · have hle : 2 ^ (m + 1) ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hlt2
            rw [Nat.testBit_lt_two_pow (show k - 2 ^ m < 2 ^ p from by omega),
              Nat.testBit_lt_two_pow (show k < 2 ^ p from by omega)]
          · have h2 := Nat.testBit_two_pow_add_gt hgt (k - 2 ^ m)
            rw [show 2 ^ m + (k - 2 ^ m) = k from by omega] at h2
            exact h2.symm

def bm_init (n : ℕ) : List ℕ := (List.range n).map (fun p => bm_tab p n)

theorem bm_init_len (n : ℕ) : (bm_init n).length = n := by simp [bm_init]

theorem bm_rep_init (n : ℕ) (x : List Bool) (hx : x.length = n) :
    bm_Rep (bm_num x) x (bm_init n) := by
  have hk : bm_num x < 2 ^ n := by
    have h := bm_num_lt x
    rw [hx] at h
    exact h
  refine ⟨by rw [bm_init_len, hx], fun t => ?_⟩
  by_cases ht : t < n
  · rw [List.getD_eq_getElem (bm_init n) 0 (by rw [bm_init_len]; exact ht)]
    simp only [bm_init, List.getElem_map, List.getElem_range]
    rw [(bm_tab_spec t n).2 _ hk, bm_num_bit]
  · rw [getD_ge x t (by omega), List.getD_eq_default (bm_init n) 0 (by rw [bm_init_len]; omega)]
    exact (Nat.zero_testBit _).symm

def bm_out (n : ℕ) (C : Circuit) : ℕ := (bm_W (2 ^ n) C.gates (bm_init n)).getD C.output 0

theorem bm_eval (n : ℕ) (C : Circuit) (hC : bm_ok C = true) (x : List Bool) (hx : x.length = n) :
    C.eval x = Nat.testBit (bm_out n C) (bm_num x) := by
  have hk : bm_num x < 2 ^ n := by
    have h := bm_num_lt x
    rw [hx] at h
    exact h
  have hg : ∀ g ∈ C.gates, bm_okop g.op = true := fun g hgm => List.all_eq_true.mp hC g hgm
  have h := bm_rep_fold (2 ^ n) (bm_num x) hk C.gates hg x (bm_init n) (bm_rep_init n x hx)
  rw [eval_W]
  exact h.2 C.output

def bm_code {n : ℕ} (x : Fin n → Bool) : ℕ := bm_num (List.ofFn x)

def bm_input (n m : ℕ) : Fin n → Bool := fun i => Nat.testBit m i.val

theorem bm_code_lt {n : ℕ} (x : Fin n → Bool) : bm_code x < 2 ^ n := by
  have h := bm_num_lt (List.ofFn x)
  rw [List.length_ofFn] at h
  exact h

theorem bm_input_code {n : ℕ} (x : Fin n → Bool) : bm_input n (bm_code x) = x := by
  funext i
  show Nat.testBit (bm_num (List.ofFn x)) i.val = x i
  rw [bm_num_bit, ofFn_getD x i.val i.isLt]

theorem bm_code_input (n m : ℕ) (hm : m < 2 ^ n) : bm_code (bm_input n m) = m := by
  apply Nat.eq_of_testBit_eq
  intro i
  show Nat.testBit (bm_num (List.ofFn (bm_input n m))) i = Nat.testBit m i
  rw [bm_num_bit]
  by_cases hi : i < n
  · rw [ofFn_getD _ i hi]
    rfl
  · rw [ofFn_getD_ge _ i (by omega)]
    have hle : 2 ^ n ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact (Nat.testBit_lt_two_pow (show m < 2 ^ i from by omega)).symm

theorem bm_circuitFun (n : ℕ) (C : Circuit) (hC : bm_ok C = true) (x : Fin n → Bool) :
    circuitFun n C x = Nat.testBit (bm_out n C) (bm_code x) :=
  bm_eval n C hC (List.ofFn x) (List.length_ofFn)

theorem bm_circuitFun_num (n : ℕ) (C : Circuit) (hC : bm_ok C = true) (m : ℕ) (hm : m < 2 ^ n) :
    circuitFun n C (bm_input n m) = Nat.testBit (bm_out n C) m := by
  rw [bm_circuitFun n C hC, bm_code_input n m hm]

theorem bm_forall_iff (n : ℕ) (P : (Fin n → Bool) → Prop) :
    (∀ x, P x) ↔ ∀ m, m < 2 ^ n → P (bm_input n m) := by
  constructor
  · intro h m _
    exact h _
  · intro h x
    have e := h (bm_code x) (bm_code_lt x)
    rw [bm_input_code] at e
    exact e

theorem bm_exists_iff (n : ℕ) (P : (Fin n → Bool) → Prop) :
    (∃ x, P x) ↔ ∃ m, m < 2 ^ n ∧ P (bm_input n m) := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨bm_code x, bm_code_lt x, ?_⟩
    rw [bm_input_code]
    exact hx
  · rintro ⟨m, _, hm⟩
    exact ⟨_, hm⟩

theorem bm_fun_eq (n : ℕ) (C : Circuit) (hC : bm_ok C = true) (f : (Fin n → Bool) → Bool)
    (h : ∀ m, m < 2 ^ n → Nat.testBit (bm_out n C) m = f (bm_input n m)) :
    ∀ x, circuitFun n C x = f x := by
  intro x
  rw [bm_circuitFun n C hC x]
  have e := h (bm_code x) (bm_code_lt x)
  rw [bm_input_code] at e
  exact e

theorem bm_eval_two (n1 n2 : ℕ) (C : Circuit) (hC : bm_ok C = true)
    (x : Fin n1 → Bool) (y : Fin n2 → Bool) :
    C.eval (List.ofFn x ++ List.ofFn y) =
      Nat.testBit (bm_out (n1 + n2) C) (bm_code x + 2 ^ n1 * bm_code y) := by
  show C.eval (List.ofFn x ++ List.ofFn y) =
    Nat.testBit (bm_out (n1 + n2) C) (bm_num (List.ofFn x) + 2 ^ n1 * bm_num (List.ofFn y))
  rw [bm_eval (n1 + n2) C hC (List.ofFn x ++ List.ofFn y) (by simp), bm_num_append, List.length_ofFn]

theorem bm_fun_eq2 (n1 n2 : ℕ) (C : Circuit) (hC : bm_ok C = true)
    (f : (Fin n1 → Bool) → (Fin n2 → Bool) → Bool)
    (h : ∀ a, a < 2 ^ n1 → ∀ b, b < 2 ^ n2 →
      Nat.testBit (bm_out (n1 + n2) C) (a + 2 ^ n1 * b) = f (bm_input n1 a) (bm_input n2 b)) :
    ∀ x y, C.eval (List.ofFn x ++ List.ofFn y) = f x y := by
  intro x y
  rw [bm_eval_two n1 n2 C hC x y]
  have e := h (bm_code x) (bm_code_lt x) (bm_code y) (bm_code_lt y)
  rw [bm_input_code, bm_input_code] at e
  exact e

def ni_opc : GateOp → ℕ
  | GateOp.and => 0
  | GateOp.or => 1
  | GateOp.not => 2
  | GateOp.mod _ => 3
  | GateOp.maj => 4

def ni_wmap (σ : Equiv.Perm (Fin 11)) (w : ℕ) : ℕ :=
  if 6 ≤ w then 6 + (σ (Fin.ofNat 11 (w - 6))).val else w

def ni_Iso (C D : Circuit) (σ : Equiv.Perm (Fin 11)) : Prop :=
  ∀ j : Fin 11, (gateAt D (σ j).val).op = (gateAt C j.val).op ∧
    (gateAt D (σ j).val).inputs.Perm ((gateAt C j.val).inputs.map (ni_wmap σ))

def ni_cl (k : ℕ → ℕ) (w : ℕ) : ℕ := if w < 6 then w else 6 + k ((w - 6) % 11)

def ni_hs (c : ℕ) : ℕ := c * c * c + 7 * c + 1

def ni_nx (C : Circuit) (k : ℕ → ℕ) (j : ℕ) : ℕ :=
  ni_opc (gateAt C j).op * 1000003 + ((gateAt C j).inputs.map (fun w => ni_hs (ni_cl k w))).sum

def ni_k0 (C : Circuit) (j : ℕ) : ℕ := ni_opc (gateAt C j).op

def ni_K2 (C : Circuit) : ℕ → ℕ := ni_nx C (ni_nx C (ni_k0 C))

def ni_inv (C : Circuit) : ℕ := ((List.finRange 11).map (fun j : Fin 11 => ni_hs (ni_K2 C j.val))).sum

def ni_Inv (σ : Equiv.Perm (Fin 11)) (kC kD : ℕ → ℕ) : Prop := ∀ j : Fin 11, kD (σ j).val = kC j.val

theorem ni_cl_map (σ : Equiv.Perm (Fin 11)) (kC kD : ℕ → ℕ) (h : ni_Inv σ kC kD) (w : ℕ) :
    ni_cl kD (ni_wmap σ w) = ni_cl kC w := by
  have hv := (σ (Fin.ofNat 11 (w - 6))).isLt
  unfold ni_cl ni_wmap
  by_cases hw : 6 ≤ w
  · have e0 : ¬ (6 + (σ (Fin.ofNat 11 (w - 6))).val < 6) := by omega
    have e1 : (6 + (σ (Fin.ofNat 11 (w - 6))).val - 6) % 11 = (σ (Fin.ofNat 11 (w - 6))).val := by
      omega
    have e2 : ¬ (w < 6) := by omega
    rw [if_pos hw, if_neg e0, if_neg e2, e1, h (Fin.ofNat 11 (w - 6))]
    rfl
  · have e2 : w < 6 := by omega
    rw [if_neg hw, if_pos e2, if_pos e2]

theorem ni_nx_inv (C D : Circuit) (σ : Equiv.Perm (Fin 11)) (H : ni_Iso C D σ) (kC kD : ℕ → ℕ)
    (h : ni_Inv σ kC kD) : ni_Inv σ (ni_nx C kC) (ni_nx D kD) := by
  intro j
  obtain ⟨hop, hp⟩ := H j
  have e : (gateAt C j.val).inputs.map ((fun w => ni_hs (ni_cl kD w)) ∘ ni_wmap σ) =
      (gateAt C j.val).inputs.map (fun w => ni_hs (ni_cl kC w)) :=
    List.map_congr_left (fun w _ => by
      simp only [Function.comp_apply]
      rw [ni_cl_map σ kC kD h w])
  unfold ni_nx
  rw [hop, (hp.map (fun w => ni_hs (ni_cl kD w))).sum_eq, List.map_map, e]

theorem ni_k0_inv (C D : Circuit) (σ : Equiv.Perm (Fin 11)) (H : ni_Iso C D σ) :
    ni_Inv σ (ni_k0 C) (ni_k0 D) := by
  intro j
  unfold ni_k0
  rw [(H j).1]

theorem ni_inv_eq (C D : Circuit) (σ : Equiv.Perm (Fin 11)) (H : ni_Iso C D σ) :
    ni_inv C = ni_inv D := by
  have h2 : ni_Inv σ (ni_K2 C) (ni_K2 D) :=
    ni_nx_inv C D σ H _ _ (ni_nx_inv C D σ H _ _ (ni_k0_inv C D σ H))
  unfold ni_inv
  rw [← Fin.sum_univ_def, ← Fin.sum_univ_def]
  have hc := Equiv.sum_comp σ (fun j : Fin 11 => ni_hs (ni_K2 D j.val))
  beta_reduce at hc
  rw [← hc]
  exact Finset.sum_congr rfl (fun j _ => by rw [h2 j])

def mx_f (x : Fin 6 → Bool) : Bool :=
  ((!(x 0) && !(x 1) && x 2) || (x 0 && !(x 1) && x 3) || (!(x 0) && x 1 && x 4) || (x 0 && x 1 && x 5))

def mx_shape (g : Gate) : Bool :=
  ((ni_opc g.op == 0 || ni_opc g.op == 1) && g.inputs.length == 2) ||
    (ni_opc g.op == 2 && g.inputs.length == 1)

def mx_rb (C : Circuit) : Bool :=
  (List.range C.gates.length).all (fun j => (gateAt C j).inputs.all (fun i => decide (i < 6 + j)))

def mx_fan (C : Circuit) : Bool :=
  (List.range 17).all (fun w => decide ((C.gates.map fun g => g.inputs.count w).sum ≤ if w < 6 then 3 else 2))

def mx_in (C : Circuit) : Bool := C.gates.all (fun g => g.inputs.all (fun i => decide (i < 17)))

def mx_val (C : Circuit) : Bool :=
  (List.range (2 ^ 6)).all (fun m => Nat.testBit (bm_out 6 C) m == mx_f (bm_input 6 m))

def mx_ok (C : Circuit) : Bool :=
  C.gates.all mx_shape && mx_rb C && (C.gates.length == 11) && decide (C.output < 17) && mx_fan C &&
    mx_in C && bm_ok C && mx_val C

theorem mx_shape_ok (g : Gate) (h : mx_shape g = true) :
    ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1) := by
  rcases g with ⟨op, ins⟩
  cases op <;> simp_all [mx_shape, ni_opc]

theorem mx_rb_ok (C : Circuit) (h : mx_rb C = true) : ReadsBack 6 C := by
  intro j hj i hi
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 h j (List.mem_range.2 hj)) i hi
  exact of_decide_eq_true h1

theorem mx_fan_ok (C : Circuit) (h1 : mx_fan C = true) (h2 : mx_in C = true) :
    ∀ w : ℕ, (C.gates.map fun g => g.inputs.count w).sum ≤ if w < 6 then 3 else 2 := by
  intro w
  by_cases hw : w < 17
  · exact of_decide_eq_true (List.all_eq_true.1 h1 w (List.mem_range.2 hw))
  · have h0 : (C.gates.map fun g => g.inputs.count w).sum = 0 := by
      apply List.sum_eq_zero
      intro c hc
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hc
      apply List.count_eq_zero.2
      intro hm
      have h3 := of_decide_eq_true (List.all_eq_true.1 (List.all_eq_true.1 h2 g hg) w hm)
      omega
    rw [h0]
    exact Nat.zero_le _

theorem mx_val_ok (C : Circuit) (h1 : bm_ok C = true) (h2 : mx_val C = true) :
    ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) =
      ((!(x 0) && !(x 1) && x 2) || (x 0 && !(x 1) && x 3) || (!(x 0) && x 1 && x 4) || (x 0 && x 1 && x 5)) := by
  have h := bm_fun_eq 6 C h1 mx_f (fun m hm => beq_iff_eq.1 (List.all_eq_true.1 h2 m (List.mem_range.2 hm)))
  intro x
  exact h x

theorem mx_ok_sound (C : Circuit) (h : mx_ok C = true) :
    (∀ g ∈ C.gates, ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1)) ∧ ReadsBack 6 C ∧ C.size = 11 ∧ C.output < 17 ∧
    (∀ w : ℕ, (C.gates.map fun g => g.inputs.count w).sum ≤ if w < 6 then 3 else 2) ∧
    ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) =
      ((!(x 0) && !(x 1) && x 2) || (x 0 && !(x 1) && x 3) || (!(x 0) && x 1 && x 4) || (x 0 && x 1 && x 5)) := by
  unfold mx_ok at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hs, hrb⟩, hlen⟩, hout⟩, hfan⟩, hin⟩, hbm⟩, hval⟩ := h
  refine ⟨fun g hg => mx_shape_ok g (List.all_eq_true.1 hs g hg), mx_rb_ok C hrb, ?_,
    of_decide_eq_true hout, mx_fan_ok C hfan hin, mx_val_ok C hbm hval⟩
  exact beq_iff_eq.1 hlen

def mx_L : List Circuit := [
  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.not, [1]⟩, ⟨GateOp.and, [6, 2]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.and, [7, 10]⟩, ⟨GateOp.and, [6, 4]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.and, [1, 14]⟩, ⟨GateOp.or, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.not, [1]⟩, ⟨GateOp.and, [6, 2]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.and, [7, 10]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [6, 5]⟩, ⟨GateOp.and, [12, 13]⟩, ⟨GateOp.and, [1, 14]⟩, ⟨GateOp.or, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.not, [1]⟩, ⟨GateOp.and, [6, 2]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.and, [7, 10]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [6, 5]⟩, ⟨GateOp.and, [1, 12]⟩, ⟨GateOp.and, [14, 13]⟩, ⟨GateOp.or, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.not, [1]⟩, ⟨GateOp.and, [6, 2]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.and, [7, 10]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [6, 5]⟩, ⟨GateOp.and, [1, 13]⟩, ⟨GateOp.and, [14, 12]⟩, ⟨GateOp.or, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.not, [1]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [8, 9]⟩, ⟨GateOp.and, [7, 10]⟩, ⟨GateOp.and, [6, 4]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.and, [1, 14]⟩, ⟨GateOp.or, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.not, [1]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [7, 8]⟩, ⟨GateOp.and, [10, 9]⟩, ⟨GateOp.and, [6, 4]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.and, [1, 14]⟩, ⟨GateOp.or, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.not, [1]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [7, 9]⟩, ⟨GateOp.and, [10, 8]⟩, ⟨GateOp.and, [6, 4]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.and, [1, 14]⟩, ⟨GateOp.or, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.not, [1]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [8, 9]⟩, ⟨GateOp.and, [7, 10]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [6, 5]⟩, ⟨GateOp.and, [12, 13]⟩, ⟨GateOp.and, [1, 14]⟩, ⟨GateOp.or, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.not, [1]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [8, 9]⟩, ⟨GateOp.and, [7, 10]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [6, 5]⟩, ⟨GateOp.and, [1, 12]⟩, ⟨GateOp.and, [14, 13]⟩, ⟨GateOp.or, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.not, [1]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [8, 9]⟩, ⟨GateOp.and, [7, 10]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [6, 5]⟩, ⟨GateOp.and, [1, 13]⟩, ⟨GateOp.and, [14, 12]⟩, ⟨GateOp.or, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.not, [1]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [7, 8]⟩, ⟨GateOp.and, [10, 9]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [6, 5]⟩, ⟨GateOp.and, [12, 13]⟩, ⟨GateOp.and, [1, 14]⟩, ⟨GateOp.or, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.not, [1]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [7, 8]⟩, ⟨GateOp.and, [10, 9]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [6, 5]⟩, ⟨GateOp.and, [1, 12]⟩, ⟨GateOp.and, [14, 13]⟩, ⟨GateOp.or, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.not, [1]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [7, 8]⟩, ⟨GateOp.and, [10, 9]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [6, 5]⟩, ⟨GateOp.and, [1, 13]⟩, ⟨GateOp.and, [14, 12]⟩, ⟨GateOp.or, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.not, [1]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [7, 9]⟩, ⟨GateOp.and, [10, 8]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [6, 5]⟩, ⟨GateOp.and, [12, 13]⟩, ⟨GateOp.and, [1, 14]⟩, ⟨GateOp.or, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.not, [1]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [7, 9]⟩, ⟨GateOp.and, [10, 8]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [6, 5]⟩, ⟨GateOp.and, [1, 12]⟩, ⟨GateOp.and, [14, 13]⟩, ⟨GateOp.or, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.not, [1]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [7, 9]⟩, ⟨GateOp.and, [10, 8]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [6, 5]⟩, ⟨GateOp.and, [1, 13]⟩, ⟨GateOp.and, [14, 12]⟩, ⟨GateOp.or, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.not, [1]⟩, ⟨GateOp.and, [6, 2]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [1, 10]⟩, ⟨GateOp.and, [6, 4]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.or, [7, 14]⟩, ⟨GateOp.and, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.not, [1]⟩, ⟨GateOp.and, [6, 2]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [1, 10]⟩, ⟨GateOp.and, [6, 4]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.or, [7, 12]⟩, ⟨GateOp.or, [14, 13]⟩, ⟨GateOp.and, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.not, [1]⟩, ⟨GateOp.and, [6, 2]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [1, 10]⟩, ⟨GateOp.and, [6, 4]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.or, [7, 13]⟩, ⟨GateOp.or, [14, 12]⟩, ⟨GateOp.and, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.not, [1]⟩, ⟨GateOp.and, [6, 2]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.or, [1, 8]⟩, ⟨GateOp.or, [10, 9]⟩, ⟨GateOp.and, [6, 4]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.or, [7, 14]⟩, ⟨GateOp.and, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.not, [1]⟩, ⟨GateOp.and, [6, 2]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.or, [1, 8]⟩, ⟨GateOp.or, [10, 9]⟩, ⟨GateOp.and, [6, 4]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.or, [7, 12]⟩, ⟨GateOp.or, [14, 13]⟩, ⟨GateOp.and, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.not, [1]⟩, ⟨GateOp.and, [6, 2]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.or, [1, 8]⟩, ⟨GateOp.or, [10, 9]⟩, ⟨GateOp.and, [6, 4]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.or, [7, 13]⟩, ⟨GateOp.or, [14, 12]⟩, ⟨GateOp.and, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.not, [1]⟩, ⟨GateOp.and, [6, 2]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.or, [1, 9]⟩, ⟨GateOp.or, [10, 8]⟩, ⟨GateOp.and, [6, 4]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.or, [7, 14]⟩, ⟨GateOp.and, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.not, [1]⟩, ⟨GateOp.and, [6, 2]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.or, [1, 9]⟩, ⟨GateOp.or, [10, 8]⟩, ⟨GateOp.and, [6, 4]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.or, [7, 12]⟩, ⟨GateOp.or, [14, 13]⟩, ⟨GateOp.and, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.not, [1]⟩, ⟨GateOp.and, [6, 2]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.or, [1, 9]⟩, ⟨GateOp.or, [10, 8]⟩, ⟨GateOp.and, [6, 4]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.or, [7, 13]⟩, ⟨GateOp.or, [14, 12]⟩, ⟨GateOp.and, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.not, [1]⟩, ⟨GateOp.and, [6, 2]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [1, 10]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [6, 5]⟩, ⟨GateOp.and, [12, 13]⟩, ⟨GateOp.or, [7, 14]⟩, ⟨GateOp.and, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.not, [1]⟩, ⟨GateOp.and, [6, 2]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.or, [1, 8]⟩, ⟨GateOp.or, [10, 9]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [6, 5]⟩, ⟨GateOp.and, [12, 13]⟩, ⟨GateOp.or, [7, 14]⟩, ⟨GateOp.and, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.not, [1]⟩, ⟨GateOp.and, [6, 2]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.or, [1, 9]⟩, ⟨GateOp.or, [10, 8]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [6, 5]⟩, ⟨GateOp.and, [12, 13]⟩, ⟨GateOp.or, [7, 14]⟩, ⟨GateOp.and, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.not, [1]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [8, 9]⟩, ⟨GateOp.or, [1, 10]⟩, ⟨GateOp.and, [6, 4]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.or, [7, 14]⟩, ⟨GateOp.and, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.not, [1]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [8, 9]⟩, ⟨GateOp.or, [1, 10]⟩, ⟨GateOp.and, [6, 4]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.or, [7, 12]⟩, ⟨GateOp.or, [14, 13]⟩, ⟨GateOp.and, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.not, [1]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [8, 9]⟩, ⟨GateOp.or, [1, 10]⟩, ⟨GateOp.and, [6, 4]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.or, [7, 13]⟩, ⟨GateOp.or, [14, 12]⟩, ⟨GateOp.and, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.not, [1]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [8, 9]⟩, ⟨GateOp.or, [1, 10]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [6, 5]⟩, ⟨GateOp.and, [12, 13]⟩, ⟨GateOp.or, [7, 14]⟩, ⟨GateOp.and, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.and, [6, 2]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.and, [7, 10]⟩, ⟨GateOp.and, [6, 3]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.and, [0, 14]⟩, ⟨GateOp.or, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.and, [6, 2]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.and, [7, 10]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.or, [6, 5]⟩, ⟨GateOp.and, [12, 13]⟩, ⟨GateOp.and, [0, 14]⟩, ⟨GateOp.or, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.and, [6, 2]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.and, [7, 10]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.or, [6, 5]⟩, ⟨GateOp.and, [0, 12]⟩, ⟨GateOp.and, [14, 13]⟩, ⟨GateOp.or, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.and, [6, 2]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.and, [7, 10]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.or, [6, 5]⟩, ⟨GateOp.and, [0, 13]⟩, ⟨GateOp.and, [14, 12]⟩, ⟨GateOp.or, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 4]⟩, ⟨GateOp.and, [8, 9]⟩, ⟨GateOp.and, [7, 10]⟩, ⟨GateOp.and, [6, 3]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.and, [0, 14]⟩, ⟨GateOp.or, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 4]⟩, ⟨GateOp.and, [7, 8]⟩, ⟨GateOp.and, [10, 9]⟩, ⟨GateOp.and, [6, 3]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.and, [0, 14]⟩, ⟨GateOp.or, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 4]⟩, ⟨GateOp.and, [7, 9]⟩, ⟨GateOp.and, [10, 8]⟩, ⟨GateOp.and, [6, 3]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.and, [0, 14]⟩, ⟨GateOp.or, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 4]⟩, ⟨GateOp.and, [8, 9]⟩, ⟨GateOp.and, [7, 10]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.or, [6, 5]⟩, ⟨GateOp.and, [12, 13]⟩, ⟨GateOp.and, [0, 14]⟩, ⟨GateOp.or, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 4]⟩, ⟨GateOp.and, [8, 9]⟩, ⟨GateOp.and, [7, 10]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.or, [6, 5]⟩, ⟨GateOp.and, [0, 12]⟩, ⟨GateOp.and, [14, 13]⟩, ⟨GateOp.or, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 4]⟩, ⟨GateOp.and, [8, 9]⟩, ⟨GateOp.and, [7, 10]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.or, [6, 5]⟩, ⟨GateOp.and, [0, 13]⟩, ⟨GateOp.and, [14, 12]⟩, ⟨GateOp.or, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 4]⟩, ⟨GateOp.and, [7, 8]⟩, ⟨GateOp.and, [10, 9]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.or, [6, 5]⟩, ⟨GateOp.and, [12, 13]⟩, ⟨GateOp.and, [0, 14]⟩, ⟨GateOp.or, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 4]⟩, ⟨GateOp.and, [7, 8]⟩, ⟨GateOp.and, [10, 9]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.or, [6, 5]⟩, ⟨GateOp.and, [0, 12]⟩, ⟨GateOp.and, [14, 13]⟩, ⟨GateOp.or, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 4]⟩, ⟨GateOp.and, [7, 8]⟩, ⟨GateOp.and, [10, 9]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.or, [6, 5]⟩, ⟨GateOp.and, [0, 13]⟩, ⟨GateOp.and, [14, 12]⟩, ⟨GateOp.or, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 4]⟩, ⟨GateOp.and, [7, 9]⟩, ⟨GateOp.and, [10, 8]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.or, [6, 5]⟩, ⟨GateOp.and, [12, 13]⟩, ⟨GateOp.and, [0, 14]⟩, ⟨GateOp.or, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 4]⟩, ⟨GateOp.and, [7, 9]⟩, ⟨GateOp.and, [10, 8]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.or, [6, 5]⟩, ⟨GateOp.and, [0, 12]⟩, ⟨GateOp.and, [14, 13]⟩, ⟨GateOp.or, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 4]⟩, ⟨GateOp.and, [7, 9]⟩, ⟨GateOp.and, [10, 8]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.or, [6, 5]⟩, ⟨GateOp.and, [0, 13]⟩, ⟨GateOp.and, [14, 12]⟩, ⟨GateOp.or, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.and, [6, 2]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [0, 10]⟩, ⟨GateOp.and, [6, 3]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.or, [7, 14]⟩, ⟨GateOp.and, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.and, [6, 2]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [0, 10]⟩, ⟨GateOp.and, [6, 3]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.or, [7, 12]⟩, ⟨GateOp.or, [14, 13]⟩, ⟨GateOp.and, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.and, [6, 2]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [0, 10]⟩, ⟨GateOp.and, [6, 3]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.or, [7, 13]⟩, ⟨GateOp.or, [14, 12]⟩, ⟨GateOp.and, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.and, [6, 2]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [0, 8]⟩, ⟨GateOp.or, [10, 9]⟩, ⟨GateOp.and, [6, 3]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.or, [7, 14]⟩, ⟨GateOp.and, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.and, [6, 2]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [0, 8]⟩, ⟨GateOp.or, [10, 9]⟩, ⟨GateOp.and, [6, 3]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.or, [7, 12]⟩, ⟨GateOp.or, [14, 13]⟩, ⟨GateOp.and, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.and, [6, 2]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [0, 8]⟩, ⟨GateOp.or, [10, 9]⟩, ⟨GateOp.and, [6, 3]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.or, [7, 13]⟩, ⟨GateOp.or, [14, 12]⟩, ⟨GateOp.and, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.and, [6, 2]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [0, 9]⟩, ⟨GateOp.or, [10, 8]⟩, ⟨GateOp.and, [6, 3]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.or, [7, 14]⟩, ⟨GateOp.and, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.and, [6, 2]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [0, 9]⟩, ⟨GateOp.or, [10, 8]⟩, ⟨GateOp.and, [6, 3]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.or, [7, 12]⟩, ⟨GateOp.or, [14, 13]⟩, ⟨GateOp.and, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.and, [6, 2]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [0, 9]⟩, ⟨GateOp.or, [10, 8]⟩, ⟨GateOp.and, [6, 3]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.or, [7, 13]⟩, ⟨GateOp.or, [14, 12]⟩, ⟨GateOp.and, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.and, [6, 2]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [0, 10]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.or, [6, 5]⟩, ⟨GateOp.and, [12, 13]⟩, ⟨GateOp.or, [7, 14]⟩, ⟨GateOp.and, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.and, [6, 2]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [0, 8]⟩, ⟨GateOp.or, [10, 9]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.or, [6, 5]⟩, ⟨GateOp.and, [12, 13]⟩, ⟨GateOp.or, [7, 14]⟩, ⟨GateOp.and, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.and, [6, 2]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [0, 9]⟩, ⟨GateOp.or, [10, 8]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.or, [6, 5]⟩, ⟨GateOp.and, [12, 13]⟩, ⟨GateOp.or, [7, 14]⟩, ⟨GateOp.and, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 4]⟩, ⟨GateOp.and, [8, 9]⟩, ⟨GateOp.or, [0, 10]⟩, ⟨GateOp.and, [6, 3]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.or, [7, 14]⟩, ⟨GateOp.and, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 4]⟩, ⟨GateOp.and, [8, 9]⟩, ⟨GateOp.or, [0, 10]⟩, ⟨GateOp.and, [6, 3]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.or, [7, 12]⟩, ⟨GateOp.or, [14, 13]⟩, ⟨GateOp.and, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 4]⟩, ⟨GateOp.and, [8, 9]⟩, ⟨GateOp.or, [0, 10]⟩, ⟨GateOp.and, [6, 3]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.or, [7, 13]⟩, ⟨GateOp.or, [14, 12]⟩, ⟨GateOp.and, [11, 15]⟩], 16⟩,
  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 4]⟩, ⟨GateOp.and, [8, 9]⟩, ⟨GateOp.or, [0, 10]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.or, [6, 5]⟩, ⟨GateOp.and, [12, 13]⟩, ⟨GateOp.or, [7, 14]⟩, ⟨GateOp.and, [11, 15]⟩], 16⟩]

theorem mx_all : mx_L.all mx_ok = true := by decide +kernel

theorem mx_invs : mx_L.map ni_inv = [1754510371527502601535704304362257726709864610655194940557, 1761535988915291321773780294267368944657197837087884044219, 1755513216593682520933866991175505697633375508979560097083, 1755513216593681741745491399569686297403470625086545850683, 1545136842457187691411740291020788467941241315000330383061, 1755155613518342294769365907545374951461653613582539715365, 1755583684902178904181680739461157700020457421350528803365, 1552162459844976411649816280925972951767487090405051198283, 1546139687523367610809902977833644437620166159323120016587, 1546139687523366831621527386227825037390261275430105770187, 1762181230906131015007441897450599500342584007463796913947, 1756158458584522214167528594357996527600368911596746356891, 1756158458584521434979153002752177127370464027703732110491, 1762609302289967624419756729366382248901387815231786001947, 1756586529968358823579843426273779276159172719364735444891, 1756586529968358044391467834667959875929267835471721198491, 1762560266936556649471854898239808135810861653389601179263, 1546159278909818993854964780055399067461579963397946657743, 1546159278854378708736107519191998101120184847267236161743, 1762567060153203710210739301082423896154291558885054129263, 1546166063716778026162297543646347079322081621513559607743, 1546166063661337741043440282782946112980686505382849111743, 1762567060153845802444333628753161786830515845782324544303, 1546166063717420118395891871317084969998305908410830022783, 1546166063661979833277034610453684003656910792280119526783, 1553188458687033052353326488545746362124729938930679655597, 1553195248267405701932665763602107966822810498026683005597, 1553195248268047794166260091272845857499034784923953420637, 1769574465281909722443199346035968509972569108483415385159, 1553173481759738735711327403985041964028908894706877663639, 1553173481704298450592470143121640997687513778576167167639, 1560202658980120818673202911353984888184374042483074267765, 1754523900378907259833611772054865577174051989093345621765, 1761548218337973046483301117823950440552558037266316386711, 1755526421224688846065332825058600353109681320437877747295, 1755526421224688070325946055058771600248016678282828275295, 1545157153649830735880897230893953366558188194293157180985, 1755175380896117140278470192303548897983161288015242246537, 1755629416886147805589518307040521313324862902138977414537, 1552181471608896522530586576663107890539388858138268388819, 1546159674495612322112618283897289912603246058037369794523, 1546159674495611546373231513897461159741581415882320322523, 1762199698855182926928159538072741426071413067895545889443, 1756177901741898726510191245306647584968272838169838579627, 1756177901741897950770804475306818832106608196014789107627, 1762653734845213592239207652809713841413114682019281057443, 1756631937731929391821239360043620000309974452293573747627, 1756631937731928616081852590043791247448309810138524275627, 1762573506359727973263044999522845765668490153299673412943, 1546177422993408071411558290351822617849693024304264150623, 1546177422948518223843238931694164505440161854658598430303, 1762580516847213277336195265236915425214575732955176404751, 1546184424802216729473122505681925178628400920791580262431, 1546184424757326881904803147024267066218869751145914542111, 1762580516847852080124025427605530935170049477910366364431, 1546184424802855532260952668050540688583874665746770222111, 1546184424757965684692633309392882576174343496101104501791, 1553205303199796831126077469497842244570440051210227120033, 1553212309934699431908045037760188752624579962668632281441, 1553212309935338234695875200128804262580053707623822241121, 1769589582837988497703226746081816629851045315766344739203, 1553193503976109220064312202774032765871194003422450356883, 1553193503931219372495992844116374653461662833776784636563, 1560221381625737551396589096433641935243301905331200252885] := by decide +kernel

theorem mx_nodup : List.Pairwise (fun a b : ℕ => a ≠ b) [1754510371527502601535704304362257726709864610655194940557, 1761535988915291321773780294267368944657197837087884044219, 1755513216593682520933866991175505697633375508979560097083, 1755513216593681741745491399569686297403470625086545850683, 1545136842457187691411740291020788467941241315000330383061, 1755155613518342294769365907545374951461653613582539715365, 1755583684902178904181680739461157700020457421350528803365, 1552162459844976411649816280925972951767487090405051198283, 1546139687523367610809902977833644437620166159323120016587, 1546139687523366831621527386227825037390261275430105770187, 1762181230906131015007441897450599500342584007463796913947, 1756158458584522214167528594357996527600368911596746356891, 1756158458584521434979153002752177127370464027703732110491, 1762609302289967624419756729366382248901387815231786001947, 1756586529968358823579843426273779276159172719364735444891, 1756586529968358044391467834667959875929267835471721198491, 1762560266936556649471854898239808135810861653389601179263, 1546159278909818993854964780055399067461579963397946657743, 1546159278854378708736107519191998101120184847267236161743, 1762567060153203710210739301082423896154291558885054129263, 1546166063716778026162297543646347079322081621513559607743, 1546166063661337741043440282782946112980686505382849111743, 1762567060153845802444333628753161786830515845782324544303, 1546166063717420118395891871317084969998305908410830022783, 1546166063661979833277034610453684003656910792280119526783, 1553188458687033052353326488545746362124729938930679655597, 1553195248267405701932665763602107966822810498026683005597, 1553195248268047794166260091272845857499034784923953420637, 1769574465281909722443199346035968509972569108483415385159, 1553173481759738735711327403985041964028908894706877663639, 1553173481704298450592470143121640997687513778576167167639, 1560202658980120818673202911353984888184374042483074267765, 1754523900378907259833611772054865577174051989093345621765, 1761548218337973046483301117823950440552558037266316386711, 1755526421224688846065332825058600353109681320437877747295, 1755526421224688070325946055058771600248016678282828275295, 1545157153649830735880897230893953366558188194293157180985, 1755175380896117140278470192303548897983161288015242246537, 1755629416886147805589518307040521313324862902138977414537, 1552181471608896522530586576663107890539388858138268388819, 1546159674495612322112618283897289912603246058037369794523, 1546159674495611546373231513897461159741581415882320322523, 1762199698855182926928159538072741426071413067895545889443, 1756177901741898726510191245306647584968272838169838579627, 1756177901741897950770804475306818832106608196014789107627, 1762653734845213592239207652809713841413114682019281057443, 1756631937731929391821239360043620000309974452293573747627, 1756631937731928616081852590043791247448309810138524275627, 1762573506359727973263044999522845765668490153299673412943, 1546177422993408071411558290351822617849693024304264150623, 1546177422948518223843238931694164505440161854658598430303, 1762580516847213277336195265236915425214575732955176404751, 1546184424802216729473122505681925178628400920791580262431, 1546184424757326881904803147024267066218869751145914542111, 1762580516847852080124025427605530935170049477910366364431, 1546184424802855532260952668050540688583874665746770222111, 1546184424757965684692633309392882576174343496101104501791, 1553205303199796831126077469497842244570440051210227120033, 1553212309934699431908045037760188752624579962668632281441, 1553212309935338234695875200128804262580053707623822241121, 1769589582837988497703226746081816629851045315766344739203, 1553193503976109220064312202774032765871194003422450356883, 1553193503931219372495992844116374653461662833776784636563, 1560221381625737551396589096433641935243301905331200252885] := by decide +kernel

theorem main_aux : ∃ L : List PEqualNP.CircuitLowerBounds.Circuit, L.length = 64 ∧ (∀ C ∈ L, (∀ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 6 C ∧ C.size = 11 ∧ C.output < 17 ∧ (∀ w : ℕ, (C.gates.map fun g => g.inputs.count w).sum ≤ if w < 6 then 3 else 2) ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = ((!(x 0) && !(x 1) && x 2) || (x 0 && !(x 1) && x 3) || (!(x 0) && x 1 && x 4) || (x 0 && x 1 && x 5))) ∧ L.Pairwise (fun C D => ¬ ∃ σ : Equiv.Perm (Fin 11), D.output = (fun w : ℕ => (if 6 ≤ w then 6 + (σ (Fin.ofNat 11 (w - 6))).val else w)) C.output ∧ ∀ j : Fin 11, (PEqualNP.MetaComplexity.NestedCover.gateAt D (σ j).val).op = (PEqualNP.MetaComplexity.NestedCover.gateAt C j.val).op ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D (σ j).val).inputs.Perm ((PEqualNP.MetaComplexity.NestedCover.gateAt C j.val).inputs.map fun w => (if 6 ≤ w then 6 + (σ (Fin.ofNat 11 (w - 6))).val else w))) := by
  refine ⟨mx_L, rfl, fun C hC => mx_ok_sound C (List.all_eq_true.1 mx_all C hC), ?_⟩
  have hn : List.Pairwise (fun a b : ℕ => a ≠ b) (mx_L.map ni_inv) := by
    rw [mx_invs]
    exact mx_nodup
  have hp := List.pairwise_map.1 hn
  refine hp.imp ?_
  intro C D hne hex
  obtain ⟨σ, _, hσ⟩ := hex
  exact hne (ni_inv_eq C D σ hσ)

end PEqualNP.Outside.L_meta_8163

theorem PEqualNP.Outside.L_meta_8163 : ∃ L : List PEqualNP.CircuitLowerBounds.Circuit, L.length = 64 ∧ (∀ C ∈ L, (∀ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 6 C ∧ C.size = 11 ∧ C.output < 17 ∧ (∀ w : ℕ, (C.gates.map fun g => g.inputs.count w).sum ≤ if w < 6 then 3 else 2) ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = ((!(x 0) && !(x 1) && x 2) || (x 0 && !(x 1) && x 3) || (!(x 0) && x 1 && x 4) || (x 0 && x 1 && x 5))) ∧ L.Pairwise (fun C D => ¬ ∃ σ : Equiv.Perm (Fin 11), D.output = (fun w : ℕ => (if 6 ≤ w then 6 + (σ (Fin.ofNat 11 (w - 6))).val else w)) C.output ∧ ∀ j : Fin 11, (PEqualNP.MetaComplexity.NestedCover.gateAt D (σ j).val).op = (PEqualNP.MetaComplexity.NestedCover.gateAt C j.val).op ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D (σ j).val).inputs.Perm ((PEqualNP.MetaComplexity.NestedCover.gateAt C j.val).inputs.map fun w => (if 6 ≤ w then 6 + (σ (Fin.ofNat 11 (w - 6))).val else w))) :=
  PEqualNP.Outside.L_meta_8163.main_aux
