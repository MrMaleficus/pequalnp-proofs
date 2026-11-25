import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5585

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

-- FRAGMENT explicit    DEPENDS: fold bitmask
-- Support lemmas for explicit-circuit rows (used by explicit.py; usable by hand too).
-- Exports:
--   def ex_dg : Gate := or-gate with no inputs (the default of gateAt) ;  def ex_dp : Circuit x Nat := (empty circuit, 0)
--   def ex_okop op / ex_okopn op : Bool (and, or / and, or, not)
--   ex_mono2 (h : C.gates.all (fun g => ex_okop g.op and decide (g.inputs.length <= 2)) = true) : Monotone2 C
--   ex_fanin2 (h : C.gates.all (fun g => ex_okopn g.op and decide (g.inputs.length <= 2)) = true) : FanInTwo C
--   ex_get_some (h : l[k]? = some g) : k < l.length and l.getD k ex_dg = g
--   ex_get_none (h : l[k]? = some g) (hk : l.length <= k) : False
--   def ex_wm n p : Nat := mask of wire p.2 of circuit p.1 on n inputs (bit m = value on input number m)
--   ex_wire (bm_ok p.1) (x.length = n) : (p.1.wires x).getD p.2 false = testBit (ex_wm n p) (bm_num x)
--   def ex_ok L : Bool (all circuits of L are bm_ok) ;  def ex_val L l i : Bool := wire (L.getD i ex_dp).2 of circuit (L.getD i ex_dp).1 on l
--   ex_all1 n L (ex_ok L) Q (h : forall m < 2^n, Q (bm_input n m) (fun i => testBit (ex_wm n (L.getD i ex_dp)) m))
--       : forall x : Fin n -> Bool, Q x (ex_val L (List.ofFn x))
--   ex_all1s n h (h <= n) L (ex_ok L) Q (hQ : forall a < 2^h, forall b < 2^(n-h), Q at m = a + 2^h * b) : same as ex_all1
--       (use it for n > 9: a single bounded quantifier over 2^n values recurses too deep in the kernel)
--   ex_all2 n1 n2 L (ex_ok L) Q (h : forall a < 2^n1, forall b < 2^n2, Q (bm_input n1 a) (bm_input n2 b) (masks at a + 2^n1 * b))
--       : forall x y, Q x y (ex_val L (List.ofFn x ++ List.ofFn y))
--   ex_all1f / ex_all2f : the same with the masks quantified as a b : Fin (2 ^ k) (Decidable synthesis succeeds on
--       bodies where the bounded Nat form fails to synthesize Decidable; explicit.py uses these two)
--   ex_nex (h : forall x, not P x) : not (exists x, P x)
-- Use: exact ex_all1f 14 7 (by decide) [(c0, 44)] (by decide +kernel) (fun x v => BODY with each circuit value replaced by v i)
--   (by beta_reduce; decide +kernel)   (one decide over 2^n masks instead of 2^n circuit runs).

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def ex_dg : Gate := ⟨GateOp.or, []⟩

def ex_dp : Circuit × ℕ := (⟨[], 0⟩, 0)

def ex_okop (op : GateOp) : Bool :=
  match op with
  | GateOp.and => true
  | GateOp.or => true
  | _ => false

def ex_okopn (op : GateOp) : Bool :=
  match op with
  | GateOp.and => true
  | GateOp.or => true
  | GateOp.not => true
  | _ => false

theorem ex_okop_mem (op : GateOp) (h : ex_okop op = true) :
    op ∈ ({GateOp.and, GateOp.or} : Set GateOp) := by
  cases op
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ rfl
  all_goals simp [ex_okop] at h

theorem ex_okopn_mem (op : GateOp) (h : ex_okopn op = true) :
    op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) := by
  cases op
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)
  all_goals simp [ex_okopn] at h

theorem ex_mono2 (C : Circuit)
    (h : C.gates.all (fun g => ex_okop g.op && decide (g.inputs.length ≤ 2)) = true) :
    Monotone2 C := by
  intro g hg
  have h1 := List.all_eq_true.mp h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  exact ⟨ex_okop_mem g.op h1.1, h1.2⟩

theorem ex_fanin2 (C : Circuit)
    (h : C.gates.all (fun g => ex_okopn g.op && decide (g.inputs.length ≤ 2)) = true) :
    FanInTwo C := by
  intro g hg
  have h1 := List.all_eq_true.mp h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  exact ⟨ex_okopn_mem g.op h1.1, h1.2⟩

theorem ex_get_some {l : List Gate} {k : ℕ} {g : Gate} (h : l[k]? = some g) :
    k < l.length ∧ l.getD k ex_dg = g := by
  rcases Nat.lt_or_ge k l.length with hk | hk
  · refine ⟨hk, ?_⟩
    rw [List.getElem?_eq_getElem hk] at h
    rw [List.getD_eq_getElem _ _ hk]
    exact Option.some.inj h
  · rw [List.getElem?_eq_none hk] at h
    exact absurd h (by simp)

theorem ex_get_none {l : List Gate} {k : ℕ} {g : Gate} (h : l[k]? = some g) (hk : l.length ≤ k) :
    False := by
  have := (ex_get_some h).1
  omega

def ex_wm (n : ℕ) (p : Circuit × ℕ) : ℕ := (bm_W (2 ^ n) p.1.gates (bm_init n)).getD p.2 0

theorem ex_wire (n : ℕ) (p : Circuit × ℕ) (hC : bm_ok p.1 = true) (x : List Bool)
    (hx : x.length = n) :
    (p.1.wires x).getD p.2 false = Nat.testBit (ex_wm n p) (bm_num x) := by
  have hk : bm_num x < 2 ^ n := by
    have h := bm_num_lt x
    rw [hx] at h
    exact h
  have hg : ∀ g ∈ p.1.gates, bm_okop g.op = true := fun g hgm => List.all_eq_true.mp hC g hgm
  have h := bm_rep_fold (2 ^ n) (bm_num x) hk p.1.gates hg x (bm_init n) (bm_rep_init n x hx)
  rw [wires_W]
  exact h.2 p.2

def ex_ok (L : List (Circuit × ℕ)) : Bool := L.all (fun p => bm_ok p.1)

def ex_val (L : List (Circuit × ℕ)) (l : List Bool) (i : ℕ) : Bool :=
  ((L.getD i ex_dp).1.wires l).getD (L.getD i ex_dp).2 false

theorem ex_ok_get (L : List (Circuit × ℕ)) (h : ex_ok L = true) (i : ℕ) :
    bm_ok (L.getD i ex_dp).1 = true := by
  rcases Nat.lt_or_ge i L.length with hi | hi
  · rw [List.getD_eq_getElem _ _ hi]
    exact List.all_eq_true.mp h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ hi]
    rfl

theorem ex_val_eq (n : ℕ) (L : List (Circuit × ℕ)) (h : ex_ok L = true) (l : List Bool)
    (hl : l.length = n) (i : ℕ) :
    ex_val L l i = Nat.testBit (ex_wm n (L.getD i ex_dp)) (bm_num l) :=
  ex_wire n _ (ex_ok_get L h i) l hl

theorem ex_all1 (n : ℕ) (L : List (Circuit × ℕ)) (hok : ex_ok L = true)
    (Q : (Fin n → Bool) → (ℕ → Bool) → Prop)
    (h : ∀ m, m < 2 ^ n → Q (bm_input n m) (fun i => Nat.testBit (ex_wm n (L.getD i ex_dp)) m)) :
    ∀ x : Fin n → Bool, Q x (ex_val L (List.ofFn x)) := by
  intro x
  have e := h (bm_code x) (bm_code_lt x)
  rw [bm_input_code] at e
  have hv : ex_val L (List.ofFn x) =
      fun i => Nat.testBit (ex_wm n (L.getD i ex_dp)) (bm_code x) := by
    funext i
    exact ex_val_eq n L hok (List.ofFn x) (List.length_ofFn) i
  rw [hv]
  exact e

theorem ex_all1s (n h : ℕ) (hh : h ≤ n) (L : List (Circuit × ℕ)) (hok : ex_ok L = true)
    (Q : (Fin n → Bool) → (ℕ → Bool) → Prop)
    (hQ : ∀ a, a < 2 ^ h → ∀ b, b < 2 ^ (n - h) → Q (bm_input n (a + 2 ^ h * b))
      (fun i => Nat.testBit (ex_wm n (L.getD i ex_dp)) (a + 2 ^ h * b))) :
    ∀ x : Fin n → Bool, Q x (ex_val L (List.ofFn x)) := by
  apply ex_all1 n L hok Q
  intro m hm
  have hpos : 0 < 2 ^ h := Nat.two_pow_pos h
  have e : m % 2 ^ h + 2 ^ h * (m / 2 ^ h) = m := Nat.mod_add_div m (2 ^ h)
  have h1 : m % 2 ^ h < 2 ^ h := Nat.mod_lt _ hpos
  have h2 : m / 2 ^ h < 2 ^ (n - h) := by
    rw [Nat.div_lt_iff_lt_mul hpos, ← pow_add, Nat.sub_add_cancel hh]
    exact hm
  have hq := hQ _ h1 _ h2
  rw [e] at hq
  exact hq

theorem ex_all2 (n1 n2 : ℕ) (L : List (Circuit × ℕ)) (hok : ex_ok L = true)
    (Q : (Fin n1 → Bool) → (Fin n2 → Bool) → (ℕ → Bool) → Prop)
    (h : ∀ a, a < 2 ^ n1 → ∀ b, b < 2 ^ n2 → Q (bm_input n1 a) (bm_input n2 b)
      (fun i => Nat.testBit (ex_wm (n1 + n2) (L.getD i ex_dp)) (a + 2 ^ n1 * b))) :
    ∀ x y, Q x y (ex_val L (List.ofFn x ++ List.ofFn y)) := by
  intro x y
  have e := h (bm_code x) (bm_code_lt x) (bm_code y) (bm_code_lt y)
  rw [bm_input_code, bm_input_code] at e
  have hv : ex_val L (List.ofFn x ++ List.ofFn y) =
      fun i => Nat.testBit (ex_wm (n1 + n2) (L.getD i ex_dp)) (bm_code x + 2 ^ n1 * bm_code y) := by
    funext i
    rw [ex_val_eq (n1 + n2) L hok _ (by simp) i, bm_num_append, List.length_ofFn]
    rfl
  rw [hv]
  exact e

theorem ex_all1f (n h : ℕ) (hh : h ≤ n) (L : List (Circuit × ℕ)) (hok : ex_ok L = true)
    (Q : (Fin n → Bool) → (ℕ → Bool) → Prop)
    (hQ : ∀ a : Fin (2 ^ h), ∀ b : Fin (2 ^ (n - h)), Q (bm_input n ((a : ℕ) + 2 ^ h * (b : ℕ)))
      (fun i => Nat.testBit (ex_wm n (L.getD i ex_dp)) ((a : ℕ) + 2 ^ h * (b : ℕ)))) :
    ∀ x : Fin n → Bool, Q x (ex_val L (List.ofFn x)) :=
  ex_all1s n h hh L hok Q (fun a ha b hb => hQ ⟨a, ha⟩ ⟨b, hb⟩)

theorem ex_all2f (n1 n2 : ℕ) (L : List (Circuit × ℕ)) (hok : ex_ok L = true)
    (Q : (Fin n1 → Bool) → (Fin n2 → Bool) → (ℕ → Bool) → Prop)
    (h : ∀ a : Fin (2 ^ n1), ∀ b : Fin (2 ^ n2), Q (bm_input n1 a) (bm_input n2 b)
      (fun i => Nat.testBit (ex_wm (n1 + n2) (L.getD i ex_dp)) ((a : ℕ) + 2 ^ n1 * (b : ℕ)))) :
    ∀ x y, Q x y (ex_val L (List.ofFn x ++ List.ofFn y)) :=
  ex_all2 n1 n2 L hok Q (fun a ha b hb => h ⟨a, ha⟩ ⟨b, hb⟩)

theorem ex_nex {α : Type} {P : α → Prop} (h : ∀ x, ¬ P x) : ¬ ∃ x, P x :=
  fun ⟨x, hx⟩ => h x hx

-- FRAGMENT depth    DEPENDS: fold bitmask explicit
-- Least depth of AND/OR fan-in-2 circuits on the literals (inputs x then their negations, n = m + m wires):
-- truth tables over the 2^m inputs as Nat bitmasks, depth sets D k, and a kernel-checkable lower bound.
-- Exports:
--   def dp_step d g := d ++ [max of d over g.inputs + 1] ;  def dp_W gs d := gs.foldl dp_step d
--   dp_depth_W : C.depth n = (dp_W C.gates (List.replicate n 0)).getD C.output 0   (rfl)
--   dp_nat_lt / dp_nat_len / dp_nat_ge : getD 0 on Nat lists (head part, appended last, past the end)
--   def dp_D L0 : Nat -> Nat -> Prop : dp_D L0 0 a = (a in L0), dp_D L0 (k+1) a = dp_D L0 k a or a = b land c or b lor c with b c in dp_D L0 k
--   dp_D_mono (k <= k2) : dp_D L0 k a -> dp_D L0 k2 a ;  dp_D_lt (all of L0 below 2^N) : dp_D L0 k a -> a < 2^N
--   def dp_Inv L0 N ws d : lengths agree and every wire u has a table a in dp_D L0 (depth of u) with bit j = (ws j).getD u false for j < N
--   dp_gate, dp_inv_step, dp_inv_W : the invariant through one gate / the whole fold (gates AND or OR, fan-in at most 2;
--       AND of nothing = full table, OR of nothing = 0, one input copies, a missing wire reads false at depth 0)
--   def dp_inp m j := ofFn (bm_input m j) ++ ofFn (not of it) ;  def dp_tab m u : table of wire u ;  dp_tab_bit, dp_tab_lt
--   def dp_L0 m := 0 :: (2^2^m - 1) :: tables of the m + m literals ;  dp_L0_lt ;  dp_inv_init
--   dp_ops_of_mono2 : Monotone2 C -> every gate is AND or OR with at most 2 inputs
--   dp_out (gates AND/OR fan-in 2) : exists a, dp_D (dp_L0 m) (C.depth (m+m)) a and a has bit j = C.eval (dp_inp m j) for j < 2^m
--   def dp_has L a : Bool (a in L) ;  dp_has_mem ;  def dp_cl L0 L1 : Bool (L0 in L1, all land / lor of two L0 elements in L1)
--   dp_lvl1 (dp_cl L0 L1 = true) : dp_D L0 1 a -> a in L1
--   def dp_good T Mo Ma b, def dp_chk T L Mo Ma : Bool  (Mo: tables below T covering every candidate below T, no two with union T;
--       Ma: tables above T under every candidate above T, no two with meet T; candidates = L and land / lor of two L elements)
--   dp_chk_sound (dp_D L0 k a -> a in L) (dp_chk T L Mo Ma = true) : not dp_D L0 (k + 2) T
--   dp_lower (hC ops) (T < 2^2^m) (F (bm_input m j) = testBit T j for j < 2^m) (hf : eval on ofFn x ++ ofFn not x = F x)
--       (hL : dp_D (dp_L0 m) k a -> a in L) (dp_chk T L Mo Ma = true) : k + 3 <= C.depth (m + m)
--   dp_upper (C.eval (dp_inp m j) = F (bm_input m j) for j < 2^m) : forall x, C.eval (ofFn x ++ ofFn not x) = F x
-- Use: tools/depth.py N writes the certificate lists (L = level-1 tables, Mo, Ma) and the depth-d circuit;
--   lower part: dp_lower m C (dp_ops_of_mono2 C hm) _ T (by decide +kernel) (by decide +kernel) hf 1 L1 Mo Ma
--   (dp_lvl1 _ _ (by decide +kernel)) (by decide +kernel)  gives 4 <= depth; with k = 0 use L = dp_L0 m and hL = fun a h => h.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def dp_step (d : List ℕ) (g : Gate) : List ℕ :=
  d ++ [(g.inputs.map fun i => d.getD i 0).foldr max 0 + 1]

def dp_W (gs : List Gate) (d : List ℕ) : List ℕ := gs.foldl dp_step d

theorem dp_depth_W (C : Circuit) (n : ℕ) :
    C.depth n = (dp_W C.gates (List.replicate n 0)).getD C.output 0 := rfl

theorem dp_nat_lt (l l2 : List ℕ) (i : ℕ) (h : i < l.length) :
    (l ++ l2).getD i 0 = l.getD i 0 := by
  simp [List.getD, List.getElem?_append_left h]

theorem dp_nat_len (l : List ℕ) (v : ℕ) : (l ++ [v]).getD l.length 0 = v := by
  simp [List.getD]

theorem dp_nat_ge (l : List ℕ) (i : ℕ) (h : l.length ≤ i) : l.getD i 0 = 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

def dp_D (L0 : List ℕ) : ℕ → ℕ → Prop
  | 0, a => a ∈ L0
  | k + 1, a => dp_D L0 k a ∨ ∃ b c, dp_D L0 k b ∧ dp_D L0 k c ∧ (a = b &&& c ∨ a = b ||| c)

theorem dp_D_succ_iff (L0 : List ℕ) (k a : ℕ) :
    dp_D L0 (k + 1) a ↔ (dp_D L0 k a ∨ ∃ b c, dp_D L0 k b ∧ dp_D L0 k c ∧ (a = b &&& c ∨ a = b ||| c)) :=
  Iff.rfl

theorem dp_D_mono (L0 : List ℕ) {k k2 a : ℕ} (hk : k ≤ k2) (h : dp_D L0 k a) : dp_D L0 k2 a := by
  induction hk with
  | refl => exact h
  | step _ ih => exact (dp_D_succ_iff L0 _ a).2 (Or.inl ih)

theorem dp_D_lt (L0 : List ℕ) (N : ℕ) (h0 : ∀ a ∈ L0, a < 2 ^ N) :
    ∀ k a, dp_D L0 k a → a < 2 ^ N
  | 0, a, h => h0 a h
  | k + 1, a, h => by
    rcases (dp_D_succ_iff L0 k a).1 h with h | ⟨b, c, hb, hc, he | he⟩
    · exact dp_D_lt L0 N h0 k a h
    · rw [he]; exact Nat.and_lt_two_pow _ (dp_D_lt L0 N h0 k c hc)
    · rw [he]; exact Nat.or_lt_two_pow (dp_D_lt L0 N h0 k b hb) (dp_D_lt L0 N h0 k c hc)

def dp_Inv (L0 : List ℕ) (N : ℕ) (ws : ℕ → List Bool) (d : List ℕ) : Prop :=
  (∀ j, j < N → (ws j).length = d.length) ∧
  ∀ u, ∃ a, dp_D L0 (d.getD u 0) a ∧ ∀ j, j < N → a.testBit j = (ws j).getD u false

theorem dp_gate (L0 : List ℕ) (N full : ℕ) (h0 : 0 ∈ L0) (hf : full ∈ L0)
    (hfull : ∀ j, j < N → full.testBit j = true)
    (ws : ℕ → List Bool) (d : List ℕ) (op : GateOp) (ins : List ℕ)
    (hop : op = GateOp.and ∨ op = GateOp.or) (hlen : ins.length ≤ 2)
    (hv : ∀ u, ∃ a, dp_D L0 (d.getD u 0) a ∧ ∀ j, j < N → a.testBit j = (ws j).getD u false) :
    ∃ a, dp_D L0 ((ins.map fun i => d.getD i 0).foldr max 0 + 1) a ∧
      ∀ j, j < N → a.testBit j = op.eval (ins.map fun i => (ws j).getD i false) := by
  rcases ins with _ | ⟨i1, _ | ⟨i2, _ | ⟨i3, rest⟩⟩⟩
  · rcases hop with h | h <;> subst h
    · exact ⟨full, (dp_D_succ_iff L0 0 full).2 (Or.inl hf), fun j hj => by rw [hfull j hj]; rfl⟩
    · exact ⟨0, (dp_D_succ_iff L0 0 0).2 (Or.inl h0), fun j _ => by rw [Nat.zero_testBit]; rfl⟩
  · obtain ⟨a, ha, hb⟩ := hv i1
    have hm : ([i1].map fun i => d.getD i 0).foldr max 0 = d.getD i1 0 := by
      show max (d.getD i1 0) 0 = d.getD i1 0
      omega
    rw [hm]
    refine ⟨a, (dp_D_succ_iff L0 _ a).2 (Or.inl ha), fun j hj => ?_⟩
    rcases hop with h | h <;> subst h
    · show _ = GateOp.and.eval [(ws j).getD i1 false]
      rw [eval_and1, hb j hj]
    · show _ = GateOp.or.eval [(ws j).getD i1 false]
      rw [eval_or1, hb j hj]
  · obtain ⟨a1, ha1, hb1⟩ := hv i1
    obtain ⟨a2, ha2, hb2⟩ := hv i2
    have hm : ([i1, i2].map fun i => d.getD i 0).foldr max 0 =
        max (d.getD i1 0) (max (d.getD i2 0) 0) := rfl
    rw [hm]
    have e1 := dp_D_mono L0 (le_max_left (d.getD i1 0) (max (d.getD i2 0) 0)) ha1
    have e2 := dp_D_mono L0 (le_trans (le_max_left (d.getD i2 0) 0)
      (le_max_right (d.getD i1 0) (max (d.getD i2 0) 0))) ha2
    rcases hop with h | h <;> subst h
    · refine ⟨a1 &&& a2, (dp_D_succ_iff L0 _ _).2 (Or.inr ⟨a1, a2, e1, e2, Or.inl rfl⟩), fun j hj => ?_⟩
      show _ = GateOp.and.eval [(ws j).getD i1 false, (ws j).getD i2 false]
      rw [eval_and2, Nat.testBit_and, hb1 j hj, hb2 j hj]
    · refine ⟨a1 ||| a2, (dp_D_succ_iff L0 _ _).2 (Or.inr ⟨a1, a2, e1, e2, Or.inr rfl⟩), fun j hj => ?_⟩
      show _ = GateOp.or.eval [(ws j).getD i1 false, (ws j).getD i2 false]
      rw [eval_or2, Nat.testBit_or, hb1 j hj, hb2 j hj]
  · have h3 := hlen
    simp only [List.length_cons] at h3
    omega

theorem dp_inv_step (L0 : List ℕ) (N full : ℕ) (h0 : 0 ∈ L0) (hf : full ∈ L0)
    (hfull : ∀ j, j < N → full.testBit j = true)
    (ws : ℕ → List Bool) (d : List ℕ) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length ≤ 2)
    (h : dp_Inv L0 N ws d) :
    dp_Inv L0 N (fun j => step (ws j) g) (dp_step d g) := by
  obtain ⟨hl, hv⟩ := h
  refine ⟨fun j hj => by simp [step, dp_step, hl j hj], ?_⟩
  intro u
  rcases Nat.lt_trichotomy u d.length with hu | hu | hu
  · obtain ⟨a, ha, hb⟩ := hv u
    refine ⟨a, ?_, fun j hj => ?_⟩
    · rw [show dp_step d g = d ++ _ from rfl, dp_nat_lt _ _ _ hu]; exact ha
    · show a.testBit j = (step (ws j) g).getD u false
      rw [step_lt _ _ _ (by rw [hl j hj]; exact hu)]; exact hb j hj
  · subst hu
    obtain ⟨a, ha, hb⟩ := dp_gate L0 N full h0 hf hfull ws d g.op g.inputs hop hlen hv
    refine ⟨a, ?_, fun j hj => ?_⟩
    · rw [show dp_step d g = d ++ _ from rfl, dp_nat_len]; exact ha
    · show a.testBit j = (step (ws j) g).getD d.length false
      rw [step_last _ _ _ (hl j hj).symm]; exact hb j hj
  · refine ⟨0, ?_, fun j hj => ?_⟩
    · rw [dp_nat_ge (dp_step d g) u (by simp [dp_step]; omega)]; exact h0
    · show Nat.testBit 0 j = (step (ws j) g).getD u false
      rw [Nat.zero_testBit, getD_ge (step (ws j) g) u (by rw [step_len, hl j hj]; omega)]

theorem dp_inv_W (L0 : List ℕ) (N full : ℕ) (h0 : 0 ∈ L0) (hf : full ∈ L0)
    (hfull : ∀ j, j < N → full.testBit j = true) :
    ∀ (gs : List Gate) (ws : ℕ → List Bool) (d : List ℕ),
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
    dp_Inv L0 N ws d → dp_Inv L0 N (fun j => W gs (ws j)) (dp_W gs d)
  | [], _, _, _, h => h
  | g :: gs, ws, d, hg, h => by
    have hg0 := hg g (by simp)
    have h1 := dp_inv_step L0 N full h0 hf hfull ws d g hg0.1 hg0.2 h
    exact dp_inv_W L0 N full h0 hf hfull gs (fun j => step (ws j) g) (dp_step d g)
      (fun g2 hg2 => hg g2 (List.mem_cons_of_mem _ hg2)) h1

def dp_inp (m j : ℕ) : List Bool :=
  List.ofFn (bm_input m j) ++ List.ofFn (fun i => !bm_input m j i)

def dp_tab (m u : ℕ) : ℕ :=
  bm_num ((List.range (2 ^ m)).map fun j => (dp_inp m j).getD u false)

theorem dp_tab_bit (m u j : ℕ) (hj : j < 2 ^ m) :
    (dp_tab m u).testBit j = (dp_inp m j).getD u false := by
  rw [dp_tab, bm_num_bit]
  simp [List.getD_eq_getElem?_getD, hj]

theorem dp_tab_lt (m u : ℕ) : dp_tab m u < 2 ^ 2 ^ m := by
  have h := bm_num_lt ((List.range (2 ^ m)).map fun j => (dp_inp m j).getD u false)
  rw [List.length_map, List.length_range] at h
  exact h

def dp_L0 (m : ℕ) : List ℕ := 0 :: (2 ^ 2 ^ m - 1) :: (List.range (m + m)).map (dp_tab m)

theorem dp_L0_lt (m : ℕ) : ∀ a ∈ dp_L0 m, a < 2 ^ 2 ^ m := by
  intro a ha
  simp only [dp_L0, List.mem_cons, List.mem_map, List.mem_range] at ha
  have hp : 0 < 2 ^ 2 ^ m := Nat.two_pow_pos _
  rcases ha with h | h | ⟨u, _, h⟩
  · rw [h]; exact hp
  · rw [h]; omega
  · rw [← h]; exact dp_tab_lt m u

theorem dp_inp_len (m j : ℕ) : (dp_inp m j).length = m + m := by
  simp [dp_inp]

theorem dp_inv_init (m : ℕ) : dp_Inv (dp_L0 m) (2 ^ m) (dp_inp m) (List.replicate (m + m) 0) := by
  refine ⟨fun j _ => by rw [dp_inp_len]; simp, fun u => ?_⟩
  have hd : (List.replicate (m + m) 0).getD u 0 = 0 := by
    by_cases hu : u < m + m
    · exact List.getD_replicate (0 : ℕ) hu
    · exact dp_nat_ge (List.replicate (m + m) 0) u (by simp; omega)
  rw [hd]
  by_cases hu : u < m + m
  · refine ⟨dp_tab m u, ?_, fun j hj => dp_tab_bit m u j hj⟩
    show dp_tab m u ∈ dp_L0 m
    simp only [dp_L0, List.mem_cons, List.mem_map, List.mem_range]
    exact Or.inr (Or.inr ⟨u, hu, rfl⟩)
  · refine ⟨0, ?_, fun j _ => ?_⟩
    · show 0 ∈ dp_L0 m
      simp [dp_L0]
    · rw [Nat.zero_testBit, getD_ge (dp_inp m j) u (by rw [dp_inp_len]; omega)]

theorem dp_ops_of_mono2 (C : Circuit) (hm : Monotone2 C) :
    ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  have h := hm g hg
  refine ⟨?_, h.2⟩
  have h1 := h.1
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h1

theorem dp_out (m : ℕ) (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∃ a, dp_D (dp_L0 m) (C.depth (m + m)) a ∧
      ∀ j, j < 2 ^ m → a.testBit j = C.eval (dp_inp m j) := by
  have h := dp_inv_W (dp_L0 m) (2 ^ m) (2 ^ 2 ^ m - 1) (by simp [dp_L0]) (by simp [dp_L0])
    (fun j hj => by rw [Nat.testBit_two_pow_sub_one]; simp [hj]) C.gates (dp_inp m)
    (List.replicate (m + m) 0) hC (dp_inv_init m)
  exact h.2 C.output

def dp_has (L : List ℕ) (a : ℕ) : Bool := L.any fun b => b == a

theorem dp_has_mem {L : List ℕ} {a : ℕ} (h : dp_has L a = true) : a ∈ L := by
  obtain ⟨b, hb, he⟩ := List.any_eq_true.1 h
  rw [beq_iff_eq] at he
  exact he ▸ hb

def dp_cl (L0 L1 : List ℕ) : Bool :=
  L0.all (dp_has L1) && L0.all (fun p => L0.all fun q => dp_has L1 (p &&& q) && dp_has L1 (p ||| q))

theorem dp_lvl1 (L0 L1 : List ℕ) (h : dp_cl L0 L1 = true) : ∀ a, dp_D L0 1 a → a ∈ L1 := by
  intro a ha
  simp only [dp_cl, Bool.and_eq_true, List.all_eq_true] at h
  rcases (dp_D_succ_iff L0 0 a).1 ha with ha | ⟨b, c, hb, hc, he | he⟩
  · exact dp_has_mem (h.1 a ha)
  · rw [he]; exact dp_has_mem (h.2 b hb c hc).1
  · rw [he]; exact dp_has_mem (h.2 b hb c hc).2

def dp_good (T : ℕ) (Mo Ma : List ℕ) (b : ℕ) : Bool :=
  (b &&& T != b || Mo.any fun m => b &&& m == b) && (b ||| T != b || Ma.any fun m => m &&& b == m)

def dp_chk (T : ℕ) (L Mo Ma : List ℕ) : Bool :=
  L.all (dp_good T Mo Ma) &&
  L.all (fun p => L.all fun q => dp_good T Mo Ma (p &&& q) && dp_good T Mo Ma (p ||| q)) &&
  Mo.all (fun m => m &&& T == m) && Ma.all (fun m => m ||| T == m) &&
  Mo.all (fun a => Mo.all fun b => a ||| b != T) && Ma.all (fun a => Ma.all fun b => a &&& b != T)

theorem dp_good_or {T b : ℕ} {Mo Ma : List ℕ} (hg : dp_good T Mo Ma b = true) (hs : b &&& T = b) :
    ∃ m, m ∈ Mo ∧ b &&& m = b := by
  simp only [dp_good, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, List.any_eq_true,
    beq_iff_eq] at hg
  rcases hg.1 with h | h
  · exact absurd hs h
  · exact h

theorem dp_good_and {T b : ℕ} {Mo Ma : List ℕ} (hg : dp_good T Mo Ma b = true) (hs : b ||| T = b) :
    ∃ m, m ∈ Ma ∧ m &&& b = m := by
  simp only [dp_good, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, List.any_eq_true,
    beq_iff_eq] at hg
  rcases hg.2 with h | h
  · exact absurd hs h
  · exact h

theorem dp_sub_l (b c T : ℕ) (h : b ||| c = T) : b &&& T = b := by
  apply Nat.eq_of_testBit_eq; intro i
  have e := congrArg (fun z => Nat.testBit z i) h
  simp only [Nat.testBit_and, Nat.testBit_or] at e ⊢
  revert e
  cases Nat.testBit b i <;> cases Nat.testBit c i <;> cases Nat.testBit T i <;> decide

theorem dp_sub_r (b c T : ℕ) (h : b ||| c = T) : c &&& T = c := by
  apply Nat.eq_of_testBit_eq; intro i
  have e := congrArg (fun z => Nat.testBit z i) h
  simp only [Nat.testBit_and, Nat.testBit_or] at e ⊢
  revert e
  cases Nat.testBit b i <;> cases Nat.testBit c i <;> cases Nat.testBit T i <;> decide

theorem dp_sup_l (b c T : ℕ) (h : b &&& c = T) : b ||| T = b := by
  apply Nat.eq_of_testBit_eq; intro i
  have e := congrArg (fun z => Nat.testBit z i) h
  simp only [Nat.testBit_and, Nat.testBit_or] at e ⊢
  revert e
  cases Nat.testBit b i <;> cases Nat.testBit c i <;> cases Nat.testBit T i <;> decide

theorem dp_sup_r (b c T : ℕ) (h : b &&& c = T) : c ||| T = c := by
  apply Nat.eq_of_testBit_eq; intro i
  have e := congrArg (fun z => Nat.testBit z i) h
  simp only [Nat.testBit_and, Nat.testBit_or] at e ⊢
  revert e
  cases Nat.testBit b i <;> cases Nat.testBit c i <;> cases Nat.testBit T i <;> decide

theorem dp_bw_or {b c m1 m2 T : ℕ} (hb : b &&& m1 = b) (hc : c &&& m2 = c) (h1 : m1 &&& T = m1)
    (h2 : m2 &&& T = m2) (h : b ||| c = T) : m1 ||| m2 = T := by
  apply Nat.eq_of_testBit_eq; intro i
  have e1 := congrArg (fun z => Nat.testBit z i) hb
  have e2 := congrArg (fun z => Nat.testBit z i) hc
  have e3 := congrArg (fun z => Nat.testBit z i) h1
  have e4 := congrArg (fun z => Nat.testBit z i) h2
  have e5 := congrArg (fun z => Nat.testBit z i) h
  simp only [Nat.testBit_and, Nat.testBit_or] at e1 e2 e3 e4 e5 ⊢
  revert e1 e2 e3 e4 e5
  cases Nat.testBit b i <;> cases Nat.testBit c i <;> cases Nat.testBit m1 i <;>
    cases Nat.testBit m2 i <;> cases Nat.testBit T i <;> decide

theorem dp_bw_and {b c m1 m2 T : ℕ} (hb : m1 &&& b = m1) (hc : m2 &&& c = m2) (h1 : m1 ||| T = m1)
    (h2 : m2 ||| T = m2) (h : b &&& c = T) : m1 &&& m2 = T := by
  apply Nat.eq_of_testBit_eq; intro i
  have e1 := congrArg (fun z => Nat.testBit z i) hb
  have e2 := congrArg (fun z => Nat.testBit z i) hc
  have e3 := congrArg (fun z => Nat.testBit z i) h1
  have e4 := congrArg (fun z => Nat.testBit z i) h2
  have e5 := congrArg (fun z => Nat.testBit z i) h
  simp only [Nat.testBit_and, Nat.testBit_or] at e1 e2 e3 e4 e5 ⊢
  revert e1 e2 e3 e4 e5
  cases Nat.testBit b i <;> cases Nat.testBit c i <;> cases Nat.testBit m1 i <;>
    cases Nat.testBit m2 i <;> cases Nat.testBit T i <;> decide

theorem dp_or_self (a : ℕ) : a ||| a = a := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_or, Bool.or_self]

theorem dp_chk_sound (L0 L : List ℕ) (k T : ℕ) (Mo Ma : List ℕ) (hL : ∀ a, dp_D L0 k a → a ∈ L)
    (h : dp_chk T L Mo Ma = true) : ¬ dp_D L0 (k + 2) T := by
  simp only [dp_chk, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  have hg : ∀ b, dp_D L0 (k + 1) b → dp_good T Mo Ma b = true := by
    intro b hb
    rcases (dp_D_succ_iff L0 k b).1 hb with hb | ⟨p, q, hp, hq, he | he⟩
    · exact h1 b (hL b hb)
    · rw [he]; exact (h2 p (hL p hp) q (hL q hq)).1
    · rw [he]; exact (h2 p (hL p hp) q (hL q hq)).2
  have hor : ∀ b c, dp_D L0 (k + 1) b → dp_D L0 (k + 1) c → b ||| c = T → False := by
    intro b c hb hc he
    obtain ⟨m1, hm1, e1⟩ := dp_good_or (hg b hb) (dp_sub_l b c T he)
    obtain ⟨m2, hm2, e2⟩ := dp_good_or (hg c hc) (dp_sub_r b c T he)
    exact h5 m1 hm1 m2 hm2 (dp_bw_or e1 e2 (h3 m1 hm1) (h3 m2 hm2) he)
  have hand : ∀ b c, dp_D L0 (k + 1) b → dp_D L0 (k + 1) c → b &&& c = T → False := by
    intro b c hb hc he
    obtain ⟨m1, hm1, e1⟩ := dp_good_and (hg b hb) (dp_sup_l b c T he)
    obtain ⟨m2, hm2, e2⟩ := dp_good_and (hg c hc) (dp_sup_r b c T he)
    exact h6 m1 hm1 m2 hm2 (dp_bw_and e1 e2 (h4 m1 hm1) (h4 m2 hm2) he)
  intro hT
  rcases (dp_D_succ_iff L0 (k + 1) T).1 hT with hT | ⟨b, c, hb, hc, he | he⟩
  · exact hor T T hT hT (dp_or_self T)
  · exact hand b c hb hc he.symm
  · exact hor b c hb hc he.symm

theorem dp_lower (m : ℕ) (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (F : (Fin m → Bool) → Bool) (T : ℕ) (hT : T < 2 ^ 2 ^ m)
    (hFT : ∀ j, j < 2 ^ m → F (bm_input m j) = T.testBit j)
    (hf : ∀ x : Fin m → Bool, C.eval (List.ofFn x ++ List.ofFn (fun i => !x i)) = F x)
    (k : ℕ) (L Mo Ma : List ℕ) (hL : ∀ a, dp_D (dp_L0 m) k a → a ∈ L)
    (hchk : dp_chk T L Mo Ma = true) : k + 3 ≤ C.depth (m + m) := by
  obtain ⟨a, ha, hb⟩ := dp_out m C hC
  by_contra hlt
  have hd : C.depth (m + m) ≤ k + 2 := by omega
  have ha2 := dp_D_mono (dp_L0 m) hd ha
  have hlt2 := dp_D_lt (dp_L0 m) (2 ^ m) (dp_L0_lt m) _ _ ha
  have haT : a = T := by
    apply Nat.eq_of_testBit_eq; intro i
    by_cases hi : i < 2 ^ m
    · rw [hb i hi, ← hFT i hi]
      exact hf (bm_input m i)
    · have hle : 2 ^ 2 ^ m ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (not_lt.1 hi)
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt2 hle), Nat.testBit_lt_two_pow (lt_of_lt_of_le hT hle)]
  exact dp_chk_sound (dp_L0 m) L k T Mo Ma hL hchk (by rw [← haT]; exact ha2)

theorem dp_upper (m : ℕ) (C : Circuit) (F : (Fin m → Bool) → Bool)
    (h : ∀ j, j < 2 ^ m → C.eval (dp_inp m j) = F (bm_input m j)) :
    ∀ x : Fin m → Bool, C.eval (List.ofFn x ++ List.ofFn (fun i => !x i)) = F x :=
  (bm_forall_iff m (fun x => C.eval (List.ofFn x ++ List.ofFn (fun i => !x i)) = F x)).2 h

def circ_up : Circuit := { gates := [{ op := GateOp.or, inputs := [0, 2] }, { op := GateOp.or, inputs := [1, 7] }, { op := GateOp.and, inputs := [8, 9] }, { op := GateOp.or, inputs := [3, 5] }, { op := GateOp.or, inputs := [4, 6] }, { op := GateOp.and, inputs := [11, 12] }, { op := GateOp.and, inputs := [10, 13] }, { op := GateOp.and, inputs := [0, 2] }, { op := GateOp.and, inputs := [4, 6] }, { op := GateOp.or, inputs := [15, 16] }, { op := GateOp.or, inputs := [1, 3] }, { op := GateOp.or, inputs := [5, 7] }, { op := GateOp.and, inputs := [18, 19] }, { op := GateOp.and, inputs := [17, 20] }, { op := GateOp.or, inputs := [14, 21] }], output := 22 }

def tab_T : ℕ := 27030

def lvl_L : List ℕ := [0, 15, 51, 85, 170, 204, 240, 255, 771, 1285, 2570, 3084, 3840, 3855, 4095, 4369, 8738, 12336, 13056, 13107, 13311, 16191, 17476, 20560, 21760, 21845, 22015, 24415, 30583, 34952, 41120, 43520, 43690, 43775, 44975, 48059, 49344, 52224, 52428, 52479, 53199, 56797, 61166, 61440, 61680, 61695, 62451, 62965, 64250, 64764, 65280, 65295, 65331, 65365, 65450, 65484, 65520, 65535]

def lvl_Mo : List ℕ := [16384, 2, 2048, 4, 128, 8192, 256, 16]

def lvl_Ma : List ℕ := [64511, 32767, 65023, 65527, 65503, 61439, 65534, 65471]

theorem main_aux : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 8 C ∧ C.depth 8 ≤ 4 ∧ ∀ x : Fin 4 → Bool, C.eval (List.ofFn x ++ List.ofFn (fun i => !x i)) = (fun a b : Bool => xor a b) ((fun u v : Bool => xor u v) (x 0) (x 1)) ((fun u v : Bool => xor u v) (x 2) (x 3))) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack 8 C → (∀ x : Fin 4 → Bool, C.eval (List.ofFn x ++ List.ofFn (fun i => !x i)) = (fun a b : Bool => xor a b) ((fun u v : Bool => xor u v) (x 0) (x 1)) ((fun u v : Bool => xor u v) (x 2) (x 3))) → 4 ≤ C.depth 8) := by
  refine ⟨⟨circ_up, ex_mono2 _ (by decide +kernel), by decide +kernel, by decide +kernel,
    dp_upper 4 circ_up _ (by decide +kernel)⟩, ?_⟩
  intro C hm _ hf
  exact dp_lower 4 C (dp_ops_of_mono2 C hm) _ tab_T (by decide +kernel) (by decide +kernel) hf
    1 lvl_L lvl_Mo lvl_Ma (dp_lvl1 _ _ (by decide +kernel)) (by decide +kernel)

end PEqualNP.Outside.L_meta_5585

theorem PEqualNP.Outside.L_meta_5585 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 8 C ∧ C.depth 8 ≤ 4 ∧ ∀ x : Fin 4 → Bool, C.eval (List.ofFn x ++ List.ofFn (fun i => !x i)) = (fun a b : Bool => xor a b) ((fun u v : Bool => xor u v) (x 0) (x 1)) ((fun u v : Bool => xor u v) (x 2) (x 3))) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack 8 C → (∀ x : Fin 4 → Bool, C.eval (List.ofFn x ++ List.ofFn (fun i => !x i)) = (fun a b : Bool => xor a b) ((fun u v : Bool => xor u v) (x 0) (x 1)) ((fun u v : Bool => xor u v) (x 2) (x 3))) → 4 ≤ C.depth 8) :=
  PEqualNP.Outside.L_meta_5585.main_aux
