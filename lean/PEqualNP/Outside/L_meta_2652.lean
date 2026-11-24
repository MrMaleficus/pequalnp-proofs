import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2652

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def val (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [val g w]) w

theorem run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w = run gs (w ++ [val g w]) := rfl

theorem eval_run (C : Circuit) (y : List Bool) :
    C.eval y = (run C.gates y).getD C.output false := rfl

theorem run_append (gs hs : List Gate) (w : List Bool) :
    run (gs ++ hs) w = run hs (run gs w) := by
  unfold run
  rw [List.foldl_append]

theorem run_length (gs : List Gate) :
    ∀ w : List Bool, (run gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    rw [run_cons, ih, List.length_append, List.length_singleton, List.length_cons]
    omega

def rn (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

def g0 (a b : ℕ) : Gate := ⟨GateOp.and, [a, b]⟩

def sh (n t i : ℕ) : ℕ := if i < n then i else if i = n then t else i - 1

def rl (p : List ℕ) (i : ℕ) : ℕ := if i < 14 then p.getD i 0 else i

def yy (p : List ℕ) (x : Fin 14 → Bool) : Fin 14 → Bool :=
  fun k => (List.ofFn x).getD (p.getD k 0) false

def ind (u v : Fin 14) : Fin 14 → Bool := fun i => decide (i = u ∨ i = v)

def E : List (ℕ × ℕ) := [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]

abbrev F (x : Fin 14 → Bool) : Prop :=
  ∃ (u : Fin 14) (v : Fin 14), ((u : ℕ), (v : ℕ)) ∈ E ∧ x u = true ∧ x v = true

def tab : List (ℕ × ℕ × List ℕ × List ℕ) := [
  (0, 7, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]),
  (7, 0, [7, 8, 9, 10, 11, 12, 13, 0, 1, 2, 3, 4, 5, 6], [7, 8, 9, 10, 11, 12, 13, 0, 1, 2, 3, 4, 5, 6]),
  (0, 8, [0, 2, 1, 6, 4, 5, 3, 8, 7, 12, 10, 11, 9, 13], [0, 2, 1, 6, 4, 5, 3, 8, 7, 12, 10, 11, 9, 13]),
  (8, 0, [7, 9, 8, 13, 11, 12, 10, 1, 0, 5, 3, 4, 2, 6], [8, 7, 12, 10, 11, 9, 13, 0, 2, 1, 6, 4, 5, 3]),
  (0, 10, [0, 2, 4, 6, 1, 3, 5, 8, 10, 12, 7, 9, 11, 13], [0, 4, 1, 5, 2, 6, 3, 10, 7, 11, 8, 12, 9, 13]),
  (10, 0, [7, 9, 11, 13, 8, 10, 12, 1, 3, 5, 0, 2, 4, 6], [10, 7, 11, 8, 12, 9, 13, 0, 4, 1, 5, 2, 6, 3]),
  (1, 7, [1, 0, 2, 3, 6, 5, 4, 7, 13, 10, 9, 11, 12, 8], [1, 0, 2, 3, 6, 5, 4, 7, 13, 10, 9, 11, 12, 8]),
  (7, 1, [8, 7, 9, 10, 13, 12, 11, 0, 6, 3, 2, 4, 5, 1], [7, 13, 10, 9, 11, 12, 8, 1, 0, 2, 3, 6, 5, 4]),
  (1, 9, [2, 0, 4, 6, 5, 3, 1, 8, 13, 7, 12, 9, 11, 10], [1, 6, 0, 5, 2, 4, 3, 9, 7, 11, 13, 12, 10, 8]),
  (9, 1, [9, 7, 11, 13, 12, 10, 8, 1, 6, 0, 5, 2, 4, 3], [9, 7, 11, 13, 12, 10, 8, 1, 6, 0, 5, 2, 4, 3]),
  (1, 13, [2, 0, 1, 6, 3, 5, 4, 8, 13, 10, 12, 11, 9, 7], [1, 2, 0, 4, 6, 5, 3, 13, 7, 12, 9, 11, 10, 8]),
  (13, 1, [9, 7, 8, 13, 10, 12, 11, 1, 6, 3, 5, 4, 2, 0], [13, 7, 12, 9, 11, 10, 8, 1, 2, 0, 4, 6, 5, 3]),
  (2, 8, [1, 2, 0, 4, 6, 5, 3, 13, 7, 12, 9, 11, 10, 8], [2, 0, 1, 6, 3, 5, 4, 8, 13, 10, 12, 11, 9, 7]),
  (8, 2, [8, 9, 7, 11, 13, 12, 10, 6, 0, 5, 2, 4, 3, 1], [8, 13, 10, 12, 11, 9, 7, 2, 0, 1, 6, 3, 5, 4]),
  (2, 12, [2, 4, 0, 1, 5, 3, 6, 13, 8, 11, 12, 9, 7, 10], [2, 3, 0, 5, 1, 4, 6, 12, 8, 11, 13, 9, 10, 7]),
  (12, 2, [9, 11, 7, 8, 12, 10, 13, 6, 1, 4, 5, 2, 0, 3], [12, 8, 11, 13, 9, 10, 7, 2, 3, 0, 5, 1, 4, 6]),
  (2, 13, [2, 1, 0, 4, 3, 5, 6, 13, 8, 9, 12, 11, 10, 7], [2, 1, 0, 4, 3, 5, 6, 13, 8, 9, 12, 11, 10, 7]),
  (13, 2, [9, 8, 7, 11, 10, 12, 13, 6, 1, 2, 5, 4, 3, 0], [13, 8, 9, 12, 11, 10, 7, 2, 1, 0, 4, 3, 5, 6]),
  (3, 7, [1, 3, 2, 0, 5, 6, 4, 7, 13, 11, 9, 10, 8, 12], [3, 0, 2, 1, 6, 4, 5, 7, 12, 10, 11, 9, 13, 8]),
  (7, 3, [8, 10, 9, 7, 12, 13, 11, 0, 6, 4, 2, 3, 1, 5], [7, 12, 10, 11, 9, 13, 8, 3, 0, 2, 1, 6, 4, 5]),
  (3, 11, [2, 6, 4, 0, 3, 5, 1, 8, 13, 9, 12, 7, 10, 11], [3, 6, 0, 4, 2, 5, 1, 11, 7, 9, 12, 13, 10, 8]),
  (11, 3, [9, 13, 11, 7, 10, 12, 8, 1, 6, 2, 5, 0, 3, 4], [11, 7, 9, 12, 13, 10, 8, 3, 6, 0, 4, 2, 5, 1]),
  (3, 12, [2, 6, 1, 0, 5, 3, 4, 8, 13, 11, 12, 10, 7, 9], [3, 2, 0, 5, 6, 4, 1, 12, 7, 13, 11, 9, 10, 8]),
  (12, 3, [9, 13, 8, 7, 12, 10, 11, 1, 6, 4, 5, 3, 0, 2], [12, 7, 13, 11, 9, 10, 8, 3, 2, 0, 5, 6, 4, 1]),
  (4, 10, [1, 2, 6, 4, 0, 3, 5, 13, 9, 12, 7, 10, 11, 8], [4, 0, 1, 5, 3, 6, 2, 10, 13, 8, 11, 12, 9, 7]),
  (10, 4, [8, 9, 13, 11, 7, 10, 12, 6, 2, 5, 0, 3, 4, 1], [10, 13, 8, 11, 12, 9, 7, 4, 0, 1, 5, 3, 6, 2]),
  (4, 11, [2, 4, 5, 1, 0, 6, 3, 13, 12, 11, 8, 7, 9, 10], [4, 3, 0, 6, 1, 2, 5, 11, 10, 12, 13, 9, 8, 7]),
  (11, 4, [9, 11, 12, 8, 7, 13, 10, 6, 5, 4, 1, 0, 2, 3], [11, 10, 12, 13, 9, 8, 7, 4, 3, 0, 6, 1, 2, 5]),
  (4, 13, [2, 1, 3, 4, 0, 6, 5, 13, 12, 9, 8, 10, 11, 7], [4, 1, 0, 2, 3, 6, 5, 13, 10, 9, 11, 12, 8, 7]),
  (13, 4, [9, 8, 10, 11, 7, 13, 12, 6, 5, 2, 1, 3, 4, 0], [13, 10, 9, 11, 12, 8, 7, 4, 1, 0, 2, 3, 6, 5]),
  (5, 9, [2, 1, 5, 4, 6, 0, 3, 13, 12, 7, 8, 11, 10, 9], [5, 1, 0, 6, 3, 2, 4, 9, 10, 13, 12, 11, 8, 7]),
  (9, 5, [9, 8, 12, 11, 13, 7, 10, 6, 5, 0, 1, 4, 3, 2], [9, 10, 13, 12, 11, 8, 7, 5, 1, 0, 6, 3, 2, 4]),
  (5, 10, [1, 2, 5, 4, 3, 0, 6, 13, 9, 8, 7, 11, 10, 12], [5, 0, 1, 4, 3, 2, 6, 10, 9, 8, 12, 11, 13, 7]),
  (10, 5, [8, 9, 12, 11, 10, 7, 13, 6, 2, 1, 0, 4, 3, 5], [10, 9, 8, 12, 11, 13, 7, 5, 0, 1, 4, 3, 2, 6]),
  (5, 12, [2, 4, 3, 1, 6, 0, 5, 13, 12, 10, 8, 9, 7, 11], [5, 3, 0, 2, 1, 6, 4, 12, 10, 11, 9, 13, 8, 7]),
  (12, 5, [9, 11, 10, 8, 13, 7, 12, 6, 5, 3, 1, 2, 0, 4], [12, 10, 11, 9, 13, 8, 7, 5, 3, 0, 2, 1, 6, 4]),
  (6, 8, [1, 2, 3, 4, 5, 6, 0, 13, 7, 8, 9, 10, 11, 12], [6, 0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 7]),
  (8, 6, [8, 9, 10, 11, 12, 13, 7, 6, 0, 1, 2, 3, 4, 5], [8, 9, 10, 11, 12, 13, 7, 6, 0, 1, 2, 3, 4, 5]),
  (6, 9, [2, 1, 6, 4, 5, 3, 0, 13, 8, 7, 12, 10, 11, 9], [6, 1, 0, 5, 3, 4, 2, 9, 8, 13, 11, 12, 10, 7]),
  (9, 6, [9, 8, 13, 11, 12, 10, 7, 6, 1, 0, 5, 3, 4, 2], [9, 8, 13, 11, 12, 10, 7, 6, 1, 0, 5, 3, 4, 2]),
  (6, 11, [2, 4, 6, 1, 3, 5, 0, 13, 8, 10, 12, 7, 9, 11], [6, 3, 0, 4, 1, 5, 2, 11, 8, 12, 9, 13, 10, 7]),
  (11, 6, [9, 11, 13, 8, 10, 12, 7, 6, 1, 3, 5, 0, 2, 4], [11, 8, 12, 9, 13, 10, 7, 6, 3, 0, 4, 1, 5, 2])]

abbrev Good (a b : ℕ) (p q : List ℕ) : Prop :=
  a < 14 ∧ b < 14 ∧ p.getD a 0 = 0 ∧ p.getD b 0 = 7 ∧
  (∀ e ∈ E, (p.getD e.1 0, p.getD e.2 0) ∈ E ∨ (p.getD e.2 0, p.getD e.1 0) ∈ E) ∧
  (∀ e ∈ E, (q.getD e.1 0, q.getD e.2 0) ∈ E ∨ (q.getD e.2 0, q.getD e.1 0) ∈ E) ∧
  (∀ i ∈ List.range 14, p.getD (q.getD i 0) 0 = i ∧ q.getD i 0 < 14 ∧ p.getD i 0 < 14)

theorem tab_good : ∀ r ∈ tab, Good r.1 r.2.1 r.2.2.1 r.2.2.2 := by decide +kernel

theorem tab_cover : ∀ e ∈ E, (∃ r ∈ tab, r.1 = e.1 ∧ r.2.1 = e.2) ∧
    (∃ r ∈ tab, r.1 = e.2 ∧ r.2.1 = e.1) := by decide +kernel

theorem ind_l (u v : Fin 14) : ind u v u = true := by simp [ind]

theorem ind_r (u v : Fin 14) : ind u v v = true := by simp [ind]

theorem ind_of (u v i : Fin 14) (h : ind u v i = true) : i = u ∨ i = v := by
  simpa [ind] using h

theorem rn_id (gs : List Gate) : gs.map (rn id) = gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, ih]
    cases g
    simp [rn]

theorem val_and (a b : ℕ) (y : List Bool) :
    val (g0 a b) y = (y.getD a false && y.getD b false) := by
  simp [val, g0, GateOp.eval]

theorem val_or1 (i : ℕ) (y : List Bool) :
    val ⟨GateOp.or, [i]⟩ y = y.getD i false := by
  simp [val, GateOp.eval]

theorem val_or2 (i j : ℕ) (y : List Bool) :
    val ⟨GateOp.or, [i, j]⟩ y = (y.getD i false || y.getD j false) := by
  simp [val, GateOp.eval]

theorem getD_last (y : List Bool) (v : Bool) : (y ++ [v]).getD y.length false = v := by
  simp

theorem ofFn_getD (x : Fin 14 → Bool) (i : ℕ) (hi : i < 14) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  have h1 : i < (List.ofFn x).length := by rw [List.length_ofFn]; exact hi
  rw [List.getD_eq_getElem _ _ h1, List.getElem_ofFn]

theorem mono_of (L : List Gate) (o : ℕ)
    (h : ∀ g ∈ L, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    Monotone2 ⟨L, o⟩ := by
  intro g hgm
  have h1 := h g hgm
  have h2 : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) := by simpa using h1.1
  exact ⟨h2, h1.2⟩

theorem of_mono (C : Circuit) (hm : Monotone2 C) :
    ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hgm
  have h0 := hm g hgm
  exact ⟨by simpa using h0.1, h0.2⟩

theorem bool_flow (t b b' c c' : Bool)
    (hb : b = t → b' = t) (hc : c = t → c' = t) :
    ((b && c) = t → (b' && c') = t) ∧ ((b || c) = t → (b' || c') = t) := by
  cases t <;> cases b <;> cases b' <;> cases c <;> cases c' <;> simp_all

theorem gate_flow (t : Bool) (op : GateOp) (hop : op = .and ∨ op = .or)
    (ins : List ℕ) (p q : ℕ → Bool)
    (h : ∀ i, p i = t → q i = t) :
    op.eval (ins.map p) = t → op.eval (ins.map q) = t := by
  induction ins with
  | nil => exact id
  | cons i ins ih =>
    rcases hop with rfl | rfl
    · simp only [GateOp.eval, List.map_cons, List.all_cons, id_eq] at ih ⊢
      exact (bool_flow t _ _ _ _ (h i) ih).1
    · simp only [GateOp.eval, List.map_cons, List.any_cons, id_eq] at ih ⊢
      exact (bool_flow t _ _ _ _ (h i) ih).2

theorem flow (p q : ℕ → ℕ) (gs : List Gate) :
    ∀ (w v : List Bool),
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    (∀ i k, k < gs.length → p i = w.length + k → q i = v.length + k) →
    (∀ i, w.getD (p i) false = true → v.getD (q i) false = true) →
    ∀ i, (run (gs.map (rn p)) w).getD (p i) false = true →
      (run (gs.map (rn q)) v).getD (q i) false = true := by
  induction gs with
  | nil =>
    intro w v _ _ hf i h
    exact hf i h
  | cons g gs ih =>
    intro w v hops hs hf i
    rw [List.map_cons, List.map_cons, run_cons, run_cons]
    have hstep : val (rn p g) w = true → val (rn q g) v = true := by
      have h0 := gate_flow true g.op (hops g List.mem_cons_self) g.inputs
        (fun i => w.getD (p i) false) (fun i => v.getD (q i) false) hf
      simpa only [val, rn, List.map_map, Function.comp_def] using h0
    refine ih (w ++ [val (rn p g) w]) (v ++ [val (rn q g) v])
      (fun a ha => hops a (List.mem_cons_of_mem _ ha)) ?_ ?_ i
    · intro j k hk hj
      rw [List.length_append, List.length_singleton] at hj ⊢
      have h0 := hs j (k + 1) (by rw [List.length_cons]; omega) (by omega)
      omega
    · intro j hj
      by_cases h1 : p j < w.length
      · rw [List.getD_append _ _ _ _ h1] at hj
        have h2 := hf j hj
        have h3 : q j < v.length := by
          by_contra hc
          rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hc)] at h2
          exact Bool.false_ne_true h2
        rw [List.getD_append _ _ _ _ h3]
        exact h2
      · by_cases h4 : p j = w.length
        · have h5 := hs j 0 (by rw [List.length_cons]; omega) (by omega)
          rw [h4, getD_last] at hj
          rw [h5, Nat.add_zero, getD_last]
          exact hstep hj
        · have h6 : (w ++ [val (rn p g) w]).length ≤ p j := by
            rw [List.length_append, List.length_singleton]
            omega
          rw [List.getD_eq_default _ _ h6] at hj
          exact absurd hj Bool.false_ne_true

theorem down (n : ℕ) (y : List Bool) (hy : y.length = n) (g : Gate) (rest : List Gate) (t : ℕ)
    (hops : ∀ g ∈ rest, g.op = GateOp.and ∨ g.op = GateOp.or)
    (ht : t < n ∨ t = n + rest.length)
    (h14 : y.getD t false = true → val g y = true) (o : ℕ)
    (h : (run (rest.map (rn (sh n t))) y).getD (sh n t o) false = true) :
    (run (g :: rest) y).getD o false = true := by
  rw [run_cons]
  have key : (run (rest.map (rn id)) (y ++ [val g y])).getD (id o) false = true := by
    refine flow (sh n t) id rest y (y ++ [val g y]) hops ?_ ?_ o h
    · intro i k hk hi
      rw [List.length_append, List.length_singleton, hy]
      rw [hy] at hi
      show i = n + 1 + k
      unfold sh at hi
      split_ifs at hi <;> omega
    · intro i hi
      show (y ++ [val g y]).getD i false = true
      by_cases h1 : i < n
      · have e0 : sh n t i = i := by unfold sh; rw [if_pos h1]
        have h1' : i < y.length := by omega
        rw [List.getD_append _ _ _ _ h1']
        rw [e0] at hi
        exact hi
      · by_cases h2 : i = n
        · have e1 : sh n t i = t := by unfold sh; rw [if_neg h1, if_pos h2]
          rw [e1] at hi
          have e2 := getD_last y (val g y)
          rw [hy] at e2
          rw [h2, e2]
          exact h14 hi
        · have e3 : sh n t i = i - 1 := by unfold sh; rw [if_neg h1, if_neg h2]
          have h6 : y.length ≤ i - 1 := by omega
          rw [e3, List.getD_eq_default _ _ h6] at hi
          exact absurd hi Bool.false_ne_true
  rw [rn_id] at key
  exact key

theorem up (n : ℕ) (y z : List Bool) (hy : y.length = n) (hz : z.length = n) (g : Gate)
    (rest : List Gate) (t : ℕ)
    (hops : ∀ g ∈ rest, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hle : ∀ i, i < n → y.getD i false = true → z.getD i false = true)
    (h14 : val g y = true → z.getD t false = true) (o : ℕ)
    (h : (run (g :: rest) y).getD o false = true) :
    (run (rest.map (rn (sh n t))) z).getD (sh n t o) false = true := by
  rw [run_cons] at h
  have h' : (run (rest.map (rn id)) (y ++ [val g y])).getD (id o) false = true := by
    rw [rn_id]
    exact h
  refine flow id (sh n t) rest (y ++ [val g y]) z hops ?_ ?_ o h'
  · intro i k hk hi
    rw [List.length_append, List.length_singleton, hy] at hi
    rw [hz]
    have hi' : i = n + 1 + k := hi
    unfold sh
    split_ifs <;> omega
  · intro i hi
    have hi' : (y ++ [val g y]).getD i false = true := hi
    by_cases h1 : i < n
    · have e0 : sh n t i = i := by unfold sh; rw [if_pos h1]
      have h1' : i < y.length := by omega
      rw [List.getD_append _ _ _ _ h1'] at hi'
      rw [e0]
      exact hle i h1 hi'
    · by_cases h2 : i = n
      · have e1 : sh n t i = t := by unfold sh; rw [if_neg h1, if_pos h2]
        have e2 := getD_last y (val g y)
        rw [hy] at e2
        rw [h2, e2] at hi'
        rw [e1]
        exact h14 hi'
      · have h6 : (y ++ [val g y]).length ≤ i := by
          rw [List.length_append, List.length_singleton]
          omega
        rw [List.getD_eq_default _ _ h6] at hi'
        exact absurd hi' Bool.false_ne_true

theorem pick0 (op : GateOp) (ins : List ℕ) (n B : ℕ) (hB : n ≤ B) (hmem : B ∈ ins)
    (hop : op = GateOp.and ∨ op = GateOp.or) (hlen : ins.length ≤ 2) :
    ∃ u, ∀ y : List Bool, y.length = n → val ⟨op, ins⟩ y = y.getD u false := by
  have hBf : ∀ y : List Bool, y.length = n → y.getD B false = false := by
    intro y hy
    have h6 : y.length ≤ B := by omega
    exact List.getD_eq_default _ _ h6
  rcases hop with rfl | rfl
  · refine ⟨B, ?_⟩
    intro y hy
    rw [hBf y hy]
    show (ins.map fun i => y.getD i false).all id = false
    rw [Bool.eq_false_iff]
    intro hall
    rw [List.all_eq_true] at hall
    have h1 : id (y.getD B false) = true := hall _ (List.mem_map_of_mem hmem)
    have h2 : y.getD B false = true := h1
    rw [hBf y hy] at h2
    exact Bool.false_ne_true h2
  · rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
    · exact absurd hmem (by simp)
    · have e : B = i := List.mem_singleton.1 hmem
      refine ⟨B, ?_⟩
      intro y hy
      rw [← e, val_or1]
    · rcases List.mem_cons.1 hmem with e | e
      · refine ⟨j, ?_⟩
        intro y hy
        rw [val_or2, ← e, hBf y hy, Bool.false_or]
      · have e' : B = j := List.mem_singleton.1 e
        refine ⟨i, ?_⟩
        intro y hy
        rw [val_or2, ← e', hBf y hy, Bool.or_false]
    · exfalso
      rw [List.length_cons, List.length_cons, List.length_cons] at hlen
      omega

theorem pick (op : GateOp) (ins : List ℕ) (n m B : ℕ) (hB : n ≤ B) (hnm : n ≤ m)
    (hmem : B ∈ ins) (hop : op = GateOp.and ∨ op = GateOp.or) (hlen : ins.length ≤ 2) :
    ∃ t, (t < n ∨ t = m) ∧
      ∀ y : List Bool, y.length = n → val ⟨op, ins⟩ y = y.getD t false := by
  obtain ⟨u, hu⟩ := pick0 op ins n B hB hmem hop hlen
  by_cases h : u < n
  · exact ⟨u, Or.inl h, hu⟩
  · refine ⟨m, Or.inr rfl, ?_⟩
    intro y hy
    have h1 : y.length ≤ u := by omega
    have h2 : y.length ≤ m := by omega
    rw [hu y hy, List.getD_eq_default _ _ h1, List.getD_eq_default _ _ h2]

theorem weq (p : List ℕ) (x : Fin 14 → Bool) (i : ℕ) :
    (List.ofFn (yy p x)).getD i false = (List.ofFn x).getD (rl p i) false := by
  by_cases h1 : i < 14
  · have e0 : rl p i = p.getD i 0 := by unfold rl; rw [if_pos h1]
    rw [e0]
    exact ofFn_getD (yy p x) i h1
  · have e2 : rl p i = i := by unfold rl; rw [if_neg h1]
    have h6 : (List.ofFn (yy p x)).length ≤ i := by rw [List.length_ofFn]; omega
    have h7 : (List.ofFn x).length ≤ i := by rw [List.length_ofFn]; omega
    rw [e2, List.getD_eq_default _ _ h6, List.getD_eq_default _ _ h7]

theorem relabel_eval (C : Circuit) (p : List ℕ)
    (hops : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hp : ∀ i, i < 14 → p.getD i 0 < 14) (x : Fin 14 → Bool) :
    (run (C.gates.map (rn (rl p))) (List.ofFn x)).getD (rl p C.output) false = true ↔
      C.eval (List.ofFn (yy p x)) = true := by
  have hw := weq p x
  have hWl : (List.ofFn (yy p x)).length = 14 := List.length_ofFn
  have hVl : (List.ofFn x).length = 14 := List.length_ofFn
  have hCe : C.eval (List.ofFn (yy p x)) =
      (run (C.gates.map (rn id)) (List.ofFn (yy p x))).getD C.output false := by
    rw [rn_id, eval_run]
  rw [hCe]
  constructor
  · intro h
    refine flow (rl p) id C.gates (List.ofFn x) (List.ofFn (yy p x)) hops ?_ ?_ C.output h
    · intro i k hk hi
      rw [hVl] at hi
      rw [hWl]
      show i = 14 + k
      unfold rl at hi
      by_cases h1 : i < 14
      · rw [if_pos h1] at hi
        have h2 := hp i h1
        omega
      · rw [if_neg h1] at hi
        exact hi
    · intro i hi
      show (List.ofFn (yy p x)).getD i false = true
      rw [hw i]
      exact hi
  · intro h
    have h' : (run (C.gates.map (rn id)) (List.ofFn (yy p x))).getD (id C.output) false
        = true := h
    refine flow id (rl p) C.gates (List.ofFn (yy p x)) (List.ofFn x) hops ?_ ?_ C.output h'
    · intro i k hk hi
      rw [hWl] at hi
      rw [hVl]
      have hi' : i = 14 + k := hi
      have h1 : ¬ i < 14 := by omega
      unfold rl
      rw [if_neg h1]
      exact hi'
    · intro i hi
      have hi' : (List.ofFn (yy p x)).getD i false = true := hi
      rw [hw i] at hi'
      exact hi'

theorem fequiv (p q : List ℕ) (x : Fin 14 → Bool)
    (h3 : ∀ e ∈ E, (p.getD e.1 0, p.getD e.2 0) ∈ E ∨ (p.getD e.2 0, p.getD e.1 0) ∈ E)
    (h4 : ∀ e ∈ E, (q.getD e.1 0, q.getD e.2 0) ∈ E ∨ (q.getD e.2 0, q.getD e.1 0) ∈ E)
    (h5 : ∀ i ∈ List.range 14, p.getD (q.getD i 0) 0 = i ∧ q.getD i 0 < 14 ∧ p.getD i 0 < 14) :
    F (yy p x) ↔ F x := by
  have hp : ∀ i, i < 14 → p.getD i 0 < 14 := fun i hi => (h5 i (List.mem_range.2 hi)).2.2
  have hq : ∀ i, i < 14 → q.getD i 0 < 14 := fun i hi => (h5 i (List.mem_range.2 hi)).2.1
  have hpq : ∀ i, i < 14 → p.getD (q.getD i 0) 0 = i := fun i hi => (h5 i (List.mem_range.2 hi)).1
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    have hu' : x ⟨p.getD u 0, hp u u.isLt⟩ = true :=
      (ofFn_getD x (p.getD u 0) (hp u u.isLt)).symm.trans hu
    have hv' : x ⟨p.getD v 0, hp v v.isLt⟩ = true :=
      (ofFn_getD x (p.getD v 0) (hp v v.isLt)).symm.trans hv
    rcases h3 ((u : ℕ), (v : ℕ)) huv with h | h
    · exact ⟨⟨p.getD u 0, hp u u.isLt⟩, ⟨p.getD v 0, hp v v.isLt⟩, h, hu', hv'⟩
    · exact ⟨⟨p.getD v 0, hp v v.isLt⟩, ⟨p.getD u 0, hp u u.isLt⟩, h, hv', hu'⟩
  · rintro ⟨u, v, huv, hu, hv⟩
    have hu' : yy p x ⟨q.getD u 0, hq u u.isLt⟩ = true := by
      show (List.ofFn x).getD (p.getD (q.getD u 0) 0) false = true
      rw [hpq u u.isLt]
      exact (ofFn_getD x u u.isLt).trans hu
    have hv' : yy p x ⟨q.getD v 0, hq v v.isLt⟩ = true := by
      show (List.ofFn x).getD (p.getD (q.getD v 0) 0) false = true
      rw [hpq v v.isLt]
      exact (ofFn_getD x v v.isLt).trans hv
    rcases h4 ((u : ℕ), (v : ℕ)) huv with h | h
    · exact ⟨⟨q.getD u 0, hq u u.isLt⟩, ⟨q.getD v 0, hq v v.isLt⟩, h, hu', hv'⟩
    · exact ⟨⟨q.getD v 0, hq v v.isLt⟩, ⟨q.getD u 0, hq u u.isLt⟩, h, hv', hu'⟩

theorem relabel (C : Circuit) (rest : List Gate) (a b : ℕ)
    (hg : C.gates = g0 a b :: rest) (hedge : (a, b) ∈ E ∨ (b, a) ∈ E) (hm : Monotone2 C)
    (hC : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ F x) :
    ∃ (C' : Circuit) (rest' : List Gate), C'.gates = g0 0 7 :: rest' ∧ Monotone2 C' ∧
      C'.size = C.size ∧ ∀ x : Fin 14 → Bool, C'.eval (List.ofFn x) = true ↔ F x := by
  have hr : ∃ r ∈ tab, r.1 = a ∧ r.2.1 = b := by
    rcases hedge with h | h
    · exact (tab_cover (a, b) h).1
    · exact (tab_cover (b, a) h).2
  obtain ⟨r, hr, hra, hrb⟩ := hr
  obtain ⟨ha, hb, h1, h2, h3, h4, h5⟩ := tab_good r hr
  rw [hra] at ha h1
  rw [hrb] at hb h2
  have hp : ∀ i, i < 14 → r.2.2.1.getD i 0 < 14 :=
    fun i hi => (h5 i (List.mem_range.2 hi)).2.2
  have hmm := of_mono C hm
  refine ⟨⟨C.gates.map (rn (rl r.2.2.1)), rl r.2.2.1 C.output⟩, rest.map (rn (rl r.2.2.1)),
    ?_, ?_, ?_, ?_⟩
  · show C.gates.map (rn (rl r.2.2.1)) = g0 0 7 :: rest.map (rn (rl r.2.2.1))
    rw [hg, List.map_cons]
    have e : rn (rl r.2.2.1) (g0 a b) = g0 0 7 := by
      show (⟨GateOp.and, [rl r.2.2.1 a, rl r.2.2.1 b]⟩ : Gate) = ⟨GateOp.and, [0, 7]⟩
      have ea : rl r.2.2.1 a = 0 := by unfold rl; rw [if_pos ha]; exact h1
      have eb : rl r.2.2.1 b = 7 := by unfold rl; rw [if_pos hb]; exact h2
      rw [ea, eb]
    rw [e]
  · apply mono_of
    intro g hgm
    obtain ⟨g1, hg1, rfl⟩ := List.mem_map.1 hgm
    have h6 := hmm g1 hg1
    refine ⟨h6.1, ?_⟩
    show (g1.inputs.map (rl r.2.2.1)).length ≤ 2
    rw [List.length_map]
    exact h6.2
  · show (C.gates.map (rn (rl r.2.2.1))).length = C.gates.length
    rw [List.length_map]
  · intro x
    show (run (C.gates.map (rn (rl r.2.2.1))) (List.ofFn x)).getD (rl r.2.2.1 C.output) false
      = true ↔ F x
    rw [relabel_eval C r.2.2.1 (fun g hgm => (hmm g hgm).1) hp x, hC (yy r.2.2.1 x)]
    exact fequiv r.2.2.1 r.2.2.2 x h3 h4 h5

theorem core07 (C : Circuit) (rest : List Gate)
    (hg : C.gates = g0 0 7 :: rest) (hm : Monotone2 C)
    (hC : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ F x) :
    ∃ D : Circuit, Monotone2 D ∧
      ((D.size + 2 ≤ C.size ∧
          ((∀ x : Fin 14 → Bool, x 0 = false ∨ x 7 = false →
              (D.eval (List.ofFn x) = true ↔ F x)) ∧
            D.eval (List.ofFn (ind 0 7)) = false)) ∨
       (D.size + 1 ≤ C.size ∧ ∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = true ↔ F x)) := by
  have hmm := of_mono C hm
  have hops : ∀ g ∈ rest, g.op = GateOp.and ∨ g.op = GateOp.or :=
    fun g hgm => (hmm g (by rw [hg]; exact List.mem_cons_of_mem _ hgm)).1
  have hlen2 : ∀ g ∈ rest, g.inputs.length ≤ 2 :=
    fun g hgm => (hmm g (by rw [hg]; exact List.mem_cons_of_mem _ hgm)).2
  have hy : ∀ x : Fin 14 → Bool, (List.ofFn x).length = 14 := fun x => List.length_ofFn
  have hval : ∀ x : Fin 14 → Bool, val (g0 0 7) (List.ofFn x) = (x 0 && x 7) := by
    intro x
    have e7 : (List.ofFn x).getD 0 false = x 0 := ofFn_getD x 0 (by omega)
    have e8 : (List.ofFn x).getD 7 false = x 7 := ofFn_getD x 7 (by omega)
    rw [val_and, e7, e8]
  have hCr : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) =
      (run (g0 0 7 :: rest) (List.ofFn x)).getD C.output false := by
    intro x
    rw [eval_run, hg]
  have hC2 : C.gates.length = rest.length + 1 := by rw [hg, List.length_cons]
  obtain ⟨B, hB⟩ : ∃ B : ℕ, B = 14 + rest.length := ⟨_, rfl⟩
  obtain ⟨L1, hL1⟩ : ∃ L1 : List Gate, L1 = rest.map (rn (sh 14 B)) := ⟨_, rfl⟩
  obtain ⟨o1, ho1⟩ : ∃ o1 : ℕ, o1 = sh 14 B C.output := ⟨_, rfl⟩
  have hL1len : L1.length = rest.length := by rw [hL1, List.length_map]
  have hm1 : ∀ g ∈ L1, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hgm
    rw [hL1] at hgm
    obtain ⟨g1, hg1, rfl⟩ := List.mem_map.1 hgm
    refine ⟨hops g1 hg1, ?_⟩
    show (g1.inputs.map (sh 14 B)).length ≤ 2
    rw [List.length_map]
    exact hlen2 g1 hg1
  have F1 : ∀ x : Fin 14 → Bool, (run L1 (List.ofFn x)).getD o1 false = true → F x := by
    intro x h
    apply (hC x).1
    rw [hCr]
    rw [hL1, ho1] at h
    refine down 14 (List.ofFn x) (hy x) (g0 0 7) rest B hops (Or.inr hB) ?_ C.output h
    intro h14
    have h6 : (List.ofFn x).length ≤ B := by
      have h7 := hy x
      omega
    rw [List.getD_eq_default _ _ h6] at h14
    exact absurd h14 Bool.false_ne_true
  have F2 : ∀ x : Fin 14 → Bool, (x 0 && x 7) = false → F x →
      (run L1 (List.ofFn x)).getD o1 false = true := by
    intro x hx hF
    have h := (hC x).2 hF
    rw [hCr] at h
    rw [hL1, ho1]
    refine up 14 (List.ofFn x) (List.ofFn x) (hy x) (hy x) (g0 0 7) rest B hops
      (fun i _ hi => hi) ?_ C.output h
    intro h14
    rw [hval x, hx] at h14
    exact absurd h14 Bool.false_ne_true
  have F3 : ∀ x : Fin 14 → Bool, x 0 = true → x 7 = true →
      (run L1 (List.ofFn (ind 0 7))).getD o1 false = true →
      (run L1 (List.ofFn x)).getD o1 false = true := by
    intro x h0 h7 h
    have h' : (run (L1.map (rn id)) (List.ofFn (ind 0 7))).getD (id o1) false = true := by
      rw [rn_id]
      exact h
    have key : (run (L1.map (rn id)) (List.ofFn x)).getD (id o1) false = true := by
      refine flow id id L1 (List.ofFn (ind 0 7)) (List.ofFn x) (fun g hgm => (hm1 g hgm).1)
        ?_ ?_ o1 h'
      · intro i k hk hi
        rw [hy x]
        rw [hy (ind 0 7)] at hi
        exact hi
      · intro i hi
        have hi' : (List.ofFn (ind 0 7)).getD i false = true := hi
        show (List.ofFn x).getD i false = true
        by_cases h1 : i < 14
        · rw [ofFn_getD (ind 0 7) i h1] at hi'
          rw [ofFn_getD x i h1]
          rcases ind_of 0 7 _ hi' with e | e
          · rw [e]
            exact h0
          · rw [e]
            exact h7
        · have h6 : (List.ofFn (ind 0 7)).length ≤ i := by
            have h7 := hy (ind 0 7)
            omega
          rw [List.getD_eq_default _ _ h6] at hi'
          exact absurd hi' Bool.false_ne_true
    rw [rn_id] at key
    exact key
  by_cases hD : (run L1 (List.ofFn (ind 0 7))).getD o1 false = true
  · refine ⟨⟨L1, o1⟩, mono_of L1 o1 hm1, Or.inr ⟨?_, ?_⟩⟩
    · show L1.length + 1 ≤ C.gates.length
      omega
    · intro x
      constructor
      · exact F1 x
      · intro hF
        show (run L1 (List.ofFn x)).getD o1 false = true
        by_cases hx : (x 0 && x 7) = true
        · simp only [Bool.and_eq_true] at hx
          exact F3 x hx.1 hx.2 hD
        · exact F2 x (Bool.eq_false_iff.2 hx) hF
  · have hreader : ∃ g2 ∈ L1, B ∈ g2.inputs := by
      by_contra hno
      have hne14 : ∀ g ∈ rest, ∀ i ∈ g.inputs, i ≠ 14 := by
        intro g hgm i hi h14
        apply hno
        refine ⟨rn (sh 14 B) g, ?_, ?_⟩
        · rw [hL1]
          exact List.mem_map_of_mem hgm
        · have e : sh 14 B 14 = B := by unfold sh; simp
          have hmem : sh 14 B i ∈ g.inputs.map (sh 14 B) := List.mem_map_of_mem hi
          rw [h14, e] at hmem
          exact hmem
      have hL1' : L1 = rest.map (rn (sh 14 0)) := by
        rw [hL1]
        apply List.map_congr_left
        intro g hgm
        show (⟨g.op, g.inputs.map (sh 14 B)⟩ : Gate) = ⟨g.op, g.inputs.map (sh 14 0)⟩
        have e : g.inputs.map (sh 14 B) = g.inputs.map (sh 14 0) := by
          apply List.map_congr_left
          intro i hi
          have h9 := hne14 g hgm i hi
          unfold sh
          split_ifs <;> first | rfl | omega
        rw [e]
      by_cases hout : C.output = 14
      · have ho : o1 = B := by
          rw [ho1, hout]
          unfold sh
          simp
        have hF : F (ind 0 8) := ⟨0, 8, by decide +kernel, ind_l 0 8, ind_r 0 8⟩
        have h1 := F2 (ind 0 8) (by decide +kernel) hF
        have h6 : (run L1 (List.ofFn (ind 0 8))).length ≤ o1 := by
          have e1 := run_length L1 (List.ofFn (ind 0 8))
          have e2 := hy (ind 0 8)
          omega
        rw [List.getD_eq_default _ _ h6] at h1
        exact Bool.false_ne_true h1
      · have ho : o1 = sh 14 0 C.output := by
          rw [ho1]
          unfold sh
          split_ifs <;> first | rfl | omega
        have hCe : (run (g0 0 7 :: rest) (List.ofFn (ind 0 7))).getD C.output false = true := by
          rw [← hCr]
          exact (hC (ind 0 7)).2 ⟨0, 7, by decide +kernel, ind_l 0 7, ind_r 0 7⟩
        have hz : (List.ofFn (ind 0 7)).getD 0 false = true :=
          (ofFn_getD (ind 0 7) 0 (by omega)).trans (ind_l 0 7)
        have h1 := up 14 (List.ofFn (ind 0 7)) (List.ofFn (ind 0 7)) (hy _) (hy _) (g0 0 7)
          rest 0 hops (fun i _ hi => hi) (fun _ => hz) C.output hCe
        rw [← hL1', ← ho] at h1
        exact hD h1
    obtain ⟨g2, hg2, hBm⟩ := hreader
    obtain ⟨front, tail, hsplit⟩ := List.append_of_mem hg2
    have hlenL : L1.length = front.length + (tail.length + 1) := by
      rw [hsplit, List.length_append, List.length_cons]
    have hfm : ∀ g ∈ front, g ∈ L1 := by
      intro g hgm
      rw [hsplit]
      exact List.mem_append_left _ hgm
    have htm : ∀ g ∈ tail, g ∈ L1 := by
      intro g hgm
      rw [hsplit]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ hgm)
    obtain ⟨t, ht, hpick⟩ := pick g2.op g2.inputs (14 + front.length)
      (14 + front.length + tail.length) B (by omega) (by omega) hBm
      (hm1 g2 hg2).1 (hm1 g2 hg2).2
    have hEq : ∀ x : Fin 14 → Bool,
        (run (front ++ tail.map (rn (sh (14 + front.length) t))) (List.ofFn x)).getD
          (sh (14 + front.length) t o1) false = true ↔
        (run L1 (List.ofFn x)).getD o1 false = true := by
      intro x
      have hyl : (run front (List.ofFn x)).length = 14 + front.length := by
        rw [run_length, hy x]
      have hv : val g2 (run front (List.ofFn x)) = (run front (List.ofFn x)).getD t false :=
        hpick _ hyl
      rw [hsplit, run_append, run_append]
      constructor
      · intro h
        exact down (14 + front.length) (run front (List.ofFn x)) hyl g2 tail t
          (fun g hgm => (hm1 g (htm g hgm)).1) ht (fun h14 => hv.trans h14) o1 h
      · intro h
        exact up (14 + front.length) (run front (List.ofFn x)) (run front (List.ofFn x))
          hyl hyl g2 tail t (fun g hgm => (hm1 g (htm g hgm)).1) (fun i _ hi => hi)
          (fun h14 => hv.symm.trans h14) o1 h
    refine ⟨⟨front ++ tail.map (rn (sh (14 + front.length) t)), sh (14 + front.length) t o1⟩,
      mono_of _ _ ?_, Or.inl ⟨?_, ?_, ?_⟩⟩
    · intro g hgm
      rcases List.mem_append.1 hgm with h | h
      · exact hm1 g (hfm g h)
      · obtain ⟨g1, hg1, rfl⟩ := List.mem_map.1 h
        have h1 := hm1 g1 (htm g1 hg1)
        refine ⟨h1.1, ?_⟩
        show (g1.inputs.map (sh (14 + front.length) t)).length ≤ 2
        rw [List.length_map]
        exact h1.2
    · have e1 : (front ++ tail.map (rn (sh (14 + front.length) t))).length
          = front.length + tail.length := by
        rw [List.length_append, List.length_map]
      show (front ++ tail.map (rn (sh (14 + front.length) t))).length + 2 ≤ C.gates.length
      omega
    · intro x hx
      have hx' : (x 0 && x 7) = false := by
        rcases hx with h | h
        · rw [h, Bool.false_and]
        · rw [h, Bool.and_false]
      constructor
      · intro h
        exact F1 x ((hEq x).1 h)
      · intro hF
        exact (hEq x).2 (F2 x hx' hF)
    · exact Bool.eq_false_iff.2 (fun h => hD ((hEq (ind 0 7)).1 h))

theorem core (C : Circuit) (rest : List Gate) (a b : ℕ)
    (hg : C.gates = { op := GateOp.and, inputs := [a, b] : Gate } :: rest)
    (hedge : (a, b) ∈ E ∨ (b, a) ∈ E) (hm : Monotone2 C)
    (hC : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ F x) :
    ∃ D : Circuit, Monotone2 D ∧
      ((D.size + 2 ≤ C.size ∧
          ((∀ x : Fin 14 → Bool, x 0 = false ∨ x 7 = false →
              (D.eval (List.ofFn x) = true ↔ F x)) ∧
            D.eval (List.ofFn (ind 0 7)) = false)) ∨
       (D.size + 1 ≤ C.size ∧ ∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = true ↔ F x)) := by
  obtain ⟨C', rest', hg', hm', hs', hC'⟩ := relabel C rest a b hg hedge hm hC
  have h := core07 C' rest' hg' hm' hC'
  rw [hs'] at h
  exact h

theorem main_aux : have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; have x2 : (Fin (14 : ℕ) → Bool) → Prop := fun (x2 : Fin (14 : ℕ) → Bool) => ∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ x1 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x4 : Fin (14 : ℕ) → Bool), x4 (0 : Fin (14 : ℕ)) = Bool.false ∨ x4 (7 : Fin (14 : ℕ)) = Bool.false → (x3.eval (List.ofFn x4) = Bool.true ↔ x2 x4)) ∧ x3.eval (List.ofFn fun (x4 : Fin (14 : ℕ)) => Decidable.decide (x4 = (0 : Fin (14 : ℕ)) ∨ x4 = (7 : Fin (14 : ℕ)))) = Bool.false; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : List PEqualNP.CircuitLowerBounds.Gate) (x6 x7 : ℕ), x4.gates = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x6, x7] : PEqualNP.CircuitLowerBounds.Gate } :: x5 → (x6, x7) ∈ x1 ∨ (x7, x6) ∈ x1 → PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x11 : Fin (14 : ℕ) → Bool), x4.eval (List.ofFn x11) = Bool.true ↔ x2 x11) → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x12 ∧ (x12.size + (2 : ℕ) ≤ x4.size ∧ x3 x12 ∨ x12.size + (1 : ℕ) ≤ x4.size ∧ ∀ (x13 : Fin (14 : ℕ) → Bool), x12.eval (List.ofFn x13) = Bool.true ↔ x2 x13) := by
  intro x1 x2 x3 x4 x5 x6 x7 h1 h2 h3 h4
  exact core x4 x5 x6 x7 h1 h2 h3 h4

end PEqualNP.Outside.L_meta_2652

theorem PEqualNP.Outside.L_meta_2652 : have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; have x2 : (Fin (14 : ℕ) → Bool) → Prop := fun (x2 : Fin (14 : ℕ) → Bool) => ∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ x1 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x4 : Fin (14 : ℕ) → Bool), x4 (0 : Fin (14 : ℕ)) = Bool.false ∨ x4 (7 : Fin (14 : ℕ)) = Bool.false → (x3.eval (List.ofFn x4) = Bool.true ↔ x2 x4)) ∧ x3.eval (List.ofFn fun (x4 : Fin (14 : ℕ)) => Decidable.decide (x4 = (0 : Fin (14 : ℕ)) ∨ x4 = (7 : Fin (14 : ℕ)))) = Bool.false; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : List PEqualNP.CircuitLowerBounds.Gate) (x6 x7 : ℕ), x4.gates = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x6, x7] : PEqualNP.CircuitLowerBounds.Gate } :: x5 → (x6, x7) ∈ x1 ∨ (x7, x6) ∈ x1 → PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x11 : Fin (14 : ℕ) → Bool), x4.eval (List.ofFn x11) = Bool.true ↔ x2 x11) → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x12 ∧ (x12.size + (2 : ℕ) ≤ x4.size ∧ x3 x12 ∨ x12.size + (1 : ℕ) ≤ x4.size ∧ ∀ (x13 : Fin (14 : ℕ) → Bool), x12.eval (List.ofFn x13) = Bool.true ↔ x2 x13) :=
  PEqualNP.Outside.L_meta_2652.main_aux
