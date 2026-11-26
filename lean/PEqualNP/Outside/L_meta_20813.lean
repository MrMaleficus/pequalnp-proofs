import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20813

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

theorem sum_count (N : ℕ) : ∀ l : List ℕ, (∀ a ∈ l, a < N) →
    ∑ w ∈ Finset.range N, l.count w = l.length := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a l ih =>
    intro h
    have ha : a < N := h a (List.mem_cons_self ..)
    have hl := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.count_cons, Finset.sum_add_distrib, hl, List.length_cons]
    congr 1
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · intro hn
      exact absurd (Finset.mem_range.2 ha) hn

theorem main_aux : ∀ (m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
  (∀ g ∈ C.gates,
    ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        g.inputs.length = 2) ∨
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack m C →
  0 < C.size →
  (∀ j < C.size,
    (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j) = 0 ↔ j + 1 = C.size)) →
  (C.size + C.size =
      (∑ w ∈ Finset.range m, PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w) +
      (∑ j ∈ Finset.range C.size,
        PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j)) +
      (@Finset.filter ℕ (fun k => (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op =
          PEqualNP.CircuitLowerBounds.GateOp.not) (fun d1 => Classical.propDecidable _)
          (Finset.range C.size)).card) ∧
  (C.size + 1 =
      (∑ w ∈ Finset.range m, PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w) +
      (∑ j ∈ @Finset.filter ℕ (fun i => i + 1 < C.size) (fun d2 => Classical.propDecidable _)
          (Finset.range C.size),
        (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j) - 1)) +
      (@Finset.filter ℕ (fun k2 => (PEqualNP.MetaComplexity.NestedCover.gateAt C k2).op =
          PEqualNP.CircuitLowerBounds.GateOp.not) (fun d3 => Classical.propDecidable _)
          (Finset.range C.size)).card) := by
  intro m C hg hrb hpos hlast
  have hs : C.size = C.gates.length := rfl
  have hsum : ∑ w ∈ Finset.range m, PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w +
      ∑ j ∈ Finset.range C.size, PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j)
      = ∑ j ∈ Finset.range C.size, (gateAt C j).inputs.length := by
    rw [← Finset.sum_range_add]
    unfold PEqualNP.MetaComplexity.NestedCover.readsIn
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    apply sum_count
    intro a ha
    have := hrb j (by rw [← hs]; exact hj) a ha
    omega
  have hlen : ∀ j ∈ Finset.range C.size,
      (gateAt C j).inputs.length +
        @ite ℕ ((gateAt C j).op = GateOp.not) (Classical.propDecidable _) 1 0 = 2 := by
    intro j hj
    rw [Finset.mem_range] at hj
    rcases hg (gateAt C j) (gateAt_mem (by rw [← hs]; exact hj)) with ⟨hop, hl⟩ | ⟨hop, hl⟩
    · rw [hl, if_neg]
      rcases hop with h | h <;> rw [h] <;> exact fun e => GateOp.noConfusion e
    · rw [hl, if_pos hop]
  have hnot : (@Finset.filter ℕ (fun k => (gateAt C k).op = GateOp.not)
      (fun d1 => Classical.propDecidable _) (Finset.range C.size)).card =
      ∑ j ∈ Finset.range C.size, @ite ℕ ((gateAt C j).op = GateOp.not) (Classical.propDecidable _) 1 0 := by
    rw [Finset.card_filter]
  have htot : ∑ j ∈ Finset.range C.size, (gateAt C j).inputs.length +
      ∑ j ∈ Finset.range C.size, @ite ℕ ((gateAt C j).op = GateOp.not) (Classical.propDecidable _) 1 0
      = C.size + C.size := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl hlen]
    simp
    ring
  have hF : (@Finset.filter ℕ (fun i => i + 1 < C.size) (fun d2 => Classical.propDecidable _)
      (Finset.range C.size)) = Finset.range (C.size - 1) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  obtain ⟨t, ht⟩ : ∃ t, C.size = t + 1 := ⟨C.size - 1, by omega⟩
  have hge : ∀ j ∈ Finset.range t,
      1 ≤ PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j) := by
    intro j hj
    rw [Finset.mem_range] at hj
    by_contra h0
    have := (hlast j (by omega)).1 (by omega)
    omega
  have hz : PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + t) = 0 :=
    (hlast t (by omega)).2 (by omega)
  have hsplit : ∑ j ∈ Finset.range C.size,
      PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j) =
      ∑ j ∈ Finset.range t, PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j) := by
    have e := Finset.sum_range_succ (fun j => PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j)) t
    rw [← ht, hz, Nat.add_zero] at e
    exact e
  have hsub : ∑ j ∈ Finset.range t,
      (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j) - 1) + t =
      ∑ j ∈ Finset.range t, PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j) := by
    have e2 : ∑ j ∈ Finset.range t, (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j) - 1 + 1) =
        ∑ j ∈ Finset.range t, (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j) - 1) + t := by
      rw [Finset.sum_add_distrib]
      simp
    have e3 : ∑ j ∈ Finset.range t, (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j) - 1 + 1) =
        ∑ j ∈ Finset.range t, PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j) :=
      Finset.sum_congr rfl (fun j hj => by have := hge j hj; omega)
    omega
  rw [hF, show C.size - 1 = t by omega, hnot]
  constructor
  · omega
  · omega

end PEqualNP.Outside.L_meta_20813

theorem PEqualNP.Outside.L_meta_20813 : ∀ (m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
  (∀ g ∈ C.gates,
    ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        g.inputs.length = 2) ∨
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack m C →
  0 < C.size →
  (∀ j < C.size,
    (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j) = 0 ↔ j + 1 = C.size)) →
  (C.size + C.size =
      (∑ w ∈ Finset.range m, PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w) +
      (∑ j ∈ Finset.range C.size,
        PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j)) +
      (@Finset.filter ℕ (fun k => (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op =
          PEqualNP.CircuitLowerBounds.GateOp.not) (fun d1 => Classical.propDecidable _)
          (Finset.range C.size)).card) ∧
  (C.size + 1 =
      (∑ w ∈ Finset.range m, PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w) +
      (∑ j ∈ @Finset.filter ℕ (fun i => i + 1 < C.size) (fun d2 => Classical.propDecidable _)
          (Finset.range C.size),
        (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j) - 1)) +
      (@Finset.filter ℕ (fun k2 => (PEqualNP.MetaComplexity.NestedCover.gateAt C k2).op =
          PEqualNP.CircuitLowerBounds.GateOp.not) (fun d3 => Classical.propDecidable _)
          (Finset.range C.size)).card) :=
  PEqualNP.Outside.L_meta_20813.main_aux
