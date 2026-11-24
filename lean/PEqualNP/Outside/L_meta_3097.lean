import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3097

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def val (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [val g w]) w

theorem run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w = run gs (w ++ [val g w]) := rfl

def rn (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

theorem getD_last (y : List Bool) (v : Bool) : (y ++ [v]).getD y.length false = v := by
  simp

theorem run_prefix (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (run gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [run_cons, ih (w ++ [val g w]) i (by rw [List.length_append]; omega)]
    exact List.getD_append w [val g w] false i hi

theorem bool_flow (t b b' c c' : Bool)
    (hb : b = t → b' = t) (hc : c = t → c' = t) :
    ((b && c) = t → (b' && c') = t) ∧ ((b || c) = t → (b' || c') = t) := by
  cases t <;> cases b <;> cases b' <;> cases c <;> cases c' <;> simp_all

theorem gate_flow (t : Bool) (op : GateOp) (hop : op = .and ∨ op = .or)
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
      exact (bool_flow t _ _ _ _ hi ih').1
    · simp only [GateOp.eval, List.map_cons, List.any_cons, id_eq] at ih' ⊢
      exact (bool_flow t _ _ _ _ hi ih').2

theorem mono (t : Bool) (a b : ℕ) (gs : List Gate) : ∀ (w v : List Bool),
    w.length = v.length →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    (∀ k < gs.length, a ∈ (gs.getD k ⟨GateOp.or, []⟩).inputs →
      a < w.length + k ∧ b < w.length + k) →
    ((run gs w).getD a false = t → (run gs w).getD b false = t) →
    (∀ i, w.getD i false = t → v.getD i false = t) →
    ∀ i, (run gs w).getD i false = t →
      (run (gs.map (rn (fun ii => if ii = a then b else ii))) v).getD i false = t := by
  induction gs with
  | nil =>
    intro w v _ _ _ _ hf i h
    exact hf i h
  | cons g gs ih =>
    intro w v hl hops hr hab hf
    rw [List.map_cons, run_cons, run_cons]
    rw [run_cons] at hab
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
        have h2 : (run gs (w ++ [val g w])).getD a false = t := by
          rw [run_prefix gs _ a (by rw [List.length_append]; omega),
            List.getD_append w [val g w] false a (by omega)]
          exact h1
        have h3 := hab h2
        rw [run_prefix gs _ b (by rw [List.length_append]; omega),
          List.getD_append w [val g w] false b (by omega)] at h3
        exact hf b h3
      · rw [if_neg hia]
        exact hf i
    have hstep : val g w = t → val (rn (fun ii => if ii = a then b else ii) g) v = t := by
      have h0 := gate_flow t g.op (hops g List.mem_cons_self) g.inputs
        (fun i => w.getD i false) (fun i => v.getD (if i = a then b else i) false) hside
      simpa only [val, rn, List.map_map, Function.comp_def] using h0
    refine ih (w ++ [val g w]) (v ++ [val (rn (fun ii => if ii = a then b else ii) g) v])
      (by simp [hl]) (fun x hx => hops x (List.mem_cons_of_mem _ hx)) ?_ hab ?_
    · intro k hk hm
      obtain ⟨h1, h2⟩ := hr (k + 1) (by rw [List.length_cons]; omega)
        (by simpa [List.getD_cons_succ] using hm)
      rw [List.length_append, List.length_singleton]
      exact ⟨by omega, by omega⟩
    · intro i hi
      by_cases h1 : i < w.length
      · rw [List.getD_append w [val g w] false i h1] at hi
        rw [List.getD_append v _ false i (by omega)]
        exact hf i hi
      · by_cases h2 : i = w.length
        · subst h2
          rw [getD_last] at hi
          rw [hl, getD_last]
          exact hstep hi
        · have h3 : (w ++ [val g w]).length ≤ i := by
            rw [List.length_append, List.length_singleton]; omega
          have h4 : (v ++ [val (rn (fun ii => if ii = a then b else ii) g) v]).length ≤ i := by
            rw [List.length_append, List.length_singleton]; omega
          rw [List.getD_eq_default _ _ h3] at hi
          rw [List.getD_eq_default _ _ h4]
          exact hi

theorem main_aux : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (w w' : ℕ),
  PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack n C →
  (∀ k < C.gates.length, w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs → w' < n + k) →
  (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD w false = true →
    (C.wires (List.ofFn x)).getD w' false = true) →
  (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD w' false = true →
    (C.wires (List.ofFn x)).getD w false = true ∨ PEqualNP.MetaComplexity.circuitFun n C x = true) →
  PEqualNP.MetaComplexity.circuitFun n
      ({ gates := C.gates.map (fun gg => ({ op := gg.op, inputs := gg.inputs.map (fun ii => if ii = w then w' else ii) } : PEqualNP.CircuitLowerBounds.Gate)),
         output := if C.output = w then w' else C.output } : PEqualNP.CircuitLowerBounds.Circuit)
    = PEqualNP.MetaComplexity.circuitFun n C ∧
  ({ gates := C.gates.map (fun gg => ({ op := gg.op, inputs := gg.inputs.map (fun ii => if ii = w then w' else ii) } : PEqualNP.CircuitLowerBounds.Gate)),
      output := if C.output = w then w' else C.output } : PEqualNP.CircuitLowerBounds.Circuit).size = C.size := by
  intro n C w w' hm hrb hread h4 h5
  have hops : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    simpa using (hm g hg).1
  refine ⟨?_, ?_⟩
  · funext x
    have hy : (List.ofFn x).length = n := List.length_ofFn
    have hr : ∀ k < C.gates.length, w ∈ (C.gates.getD k ⟨GateOp.or, []⟩).inputs →
        w < (List.ofFn x).length + k ∧ w' < (List.ofFn x).length + k := by
      intro k hk hm'
      rw [hy]
      exact ⟨hrb k hk w hm', hread k hk hm'⟩
    have key : ∀ t : Bool, ((run C.gates (List.ofFn x)).getD w false = t →
        (run C.gates (List.ofFn x)).getD w' false = t) →
        ∀ i, (run C.gates (List.ofFn x)).getD i false = t →
        (run (C.gates.map (rn (fun ii => if ii = w then w' else ii))) (List.ofFn x)).getD i false
          = t :=
      fun t ht => mono t w w' C.gates (List.ofFn x) (List.ofFn x) rfl hops hr ht (fun i h => h)
    have h4x : (run C.gates (List.ofFn x)).getD w false = true →
        (run C.gates (List.ofFn x)).getD w' false = true := h4 x
    have h5x : (run C.gates (List.ofFn x)).getD w' false = true →
        (run C.gates (List.ofFn x)).getD w false = true ∨
          (run C.gates (List.ofFn x)).getD C.output false = true := h5 x
    show (run (C.gates.map (rn (fun ii => if ii = w then w' else ii))) (List.ofFn x)).getD
        (if C.output = w then w' else C.output) false
      = (run C.gates (List.ofFn x)).getD C.output false
    generalize run C.gates (List.ofFn x) = W at key h4x h5x ⊢
    generalize run (C.gates.map (rn (fun ii => if ii = w then w' else ii))) (List.ofFn x) = V
      at key ⊢
    have hup := key true h4x
    by_cases heq : W.getD w false = W.getD w' false
    · have hdn := key false (fun h => by rw [← heq]; exact h)
      have hall : ∀ i, V.getD i false = W.getD i false := by
        intro i
        cases hW : W.getD i false
        · exact hdn i hW
        · exact hup i hW
      by_cases ho : C.output = w
      · rw [if_pos ho, hall, ho, heq]
      · rw [if_neg ho, hall]
    · have hw : W.getD w false = false := by
        cases h1 : W.getD w false
        · rfl
        · exact absurd (h1.trans (h4x h1).symm) heq
      have hw' : W.getD w' false = true := by
        cases h2 : W.getD w' false
        · exact absurd (hw.trans h2.symm) heq
        · rfl
      have ho1 : W.getD C.output false = true := by
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
  · show (C.gates.map _).length = C.gates.length
    exact List.length_map _

end PEqualNP.Outside.L_meta_3097

theorem PEqualNP.Outside.L_meta_3097 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (w w' : ℕ),
  PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack n C →
  (∀ k < C.gates.length, w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs → w' < n + k) →
  (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD w false = true →
    (C.wires (List.ofFn x)).getD w' false = true) →
  (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD w' false = true →
    (C.wires (List.ofFn x)).getD w false = true ∨ PEqualNP.MetaComplexity.circuitFun n C x = true) →
  PEqualNP.MetaComplexity.circuitFun n
      ({ gates := C.gates.map (fun gg => ({ op := gg.op, inputs := gg.inputs.map (fun ii => if ii = w then w' else ii) } : PEqualNP.CircuitLowerBounds.Gate)),
         output := if C.output = w then w' else C.output } : PEqualNP.CircuitLowerBounds.Circuit)
    = PEqualNP.MetaComplexity.circuitFun n C ∧
  ({ gates := C.gates.map (fun gg => ({ op := gg.op, inputs := gg.inputs.map (fun ii => if ii = w then w' else ii) } : PEqualNP.CircuitLowerBounds.Gate)),
      output := if C.output = w then w' else C.output } : PEqualNP.CircuitLowerBounds.Circuit).size = C.size :=
  PEqualNP.Outside.L_meta_3097.main_aux
