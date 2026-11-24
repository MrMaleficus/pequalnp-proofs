import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2654

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def val (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [val g w]) w

theorem run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w = run gs (w ++ [val g w]) := rfl

theorem eval_run (C : Circuit) (y : List Bool) :
    C.eval y = (run C.gates y).getD C.output false := rfl

def rn (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

def g0 (a b : ℕ) : Gate := ⟨GateOp.and, [a, b]⟩

def rr (t : ℕ) (i : ℕ) : ℕ := if i < 14 then i else if i = 14 then t else i - 1

def ind (u v : Fin 14) : Fin 14 → Bool := fun i => decide (i = u ∨ i = v)

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

theorem getD_last (y : List Bool) (v : Bool) : (y ++ [v]).getD y.length false = v := by
  simp

theorem ofFn_getD (x : Fin 14 → Bool) (i : ℕ) (hi : i < 14) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  have h1 : i < (List.ofFn x).length := by rw [List.length_ofFn]; exact hi
  rw [List.getD_eq_getElem _ _ h1, List.getElem_ofFn]

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

theorem down (y : List Bool) (hy : y.length = 14) (rest : List Gate) (a b t : ℕ)
    (hops : ∀ g ∈ rest, g.op = GateOp.and ∨ g.op = GateOp.or)
    (ht : t < 14 ∨ t = 14 + rest.length)
    (h14 : y.getD t false = true → (y.getD a false && y.getD b false) = true) (o : ℕ)
    (h : (run (rest.map (rn (rr t))) y).getD (rr t o) false = true) :
    (run (g0 a b :: rest) y).getD o false = true := by
  rw [run_cons]
  have key : (run (rest.map (rn id)) (y ++ [val (g0 a b) y])).getD (id o) false = true := by
    refine flow (rr t) id rest y (y ++ [val (g0 a b) y]) hops ?_ ?_ o h
    · intro i k hk hi
      rw [List.length_append, List.length_singleton, hy]
      rw [hy] at hi
      show i = 14 + 1 + k
      unfold rr at hi
      split_ifs at hi <;> omega
    · intro i hi
      show (y ++ [val (g0 a b) y]).getD i false = true
      by_cases h1 : i < 14
      · have e0 : rr t i = i := by unfold rr; rw [if_pos h1]
        have h1' : i < y.length := by omega
        rw [List.getD_append _ _ _ _ h1']
        rw [e0] at hi
        exact hi
      · by_cases h2 : i = 14
        · have e1 : rr t i = t := by unfold rr; rw [if_neg h1, if_pos h2]
          rw [e1] at hi
          have e2 := getD_last y (val (g0 a b) y)
          rw [hy] at e2
          rw [h2, e2, val_and]
          exact h14 hi
        · have e3 : rr t i = i - 1 := by unfold rr; rw [if_neg h1, if_neg h2]
          have h6 : y.length ≤ i - 1 := by omega
          rw [e3, List.getD_eq_default _ _ h6] at hi
          exact absurd hi Bool.false_ne_true
  rw [rn_id] at key
  exact key

theorem up (y z : List Bool) (hy : y.length = 14) (hz : z.length = 14) (rest : List Gate)
    (a b t : ℕ)
    (hops : ∀ g ∈ rest, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hle : ∀ i, i < 14 → y.getD i false = true → z.getD i false = true)
    (h14 : (y.getD a false && y.getD b false) = true → z.getD t false = true) (o : ℕ)
    (h : (run (g0 a b :: rest) y).getD o false = true) :
    (run (rest.map (rn (rr t))) z).getD (rr t o) false = true := by
  rw [run_cons] at h
  have h' : (run (rest.map (rn id)) (y ++ [val (g0 a b) y])).getD (id o) false = true := by
    rw [rn_id]
    exact h
  refine flow id (rr t) rest (y ++ [val (g0 a b) y]) z hops ?_ ?_ o h'
  · intro i k hk hi
    rw [List.length_append, List.length_singleton, hy] at hi
    rw [hz]
    have hi' : i = 14 + 1 + k := hi
    unfold rr
    split_ifs <;> omega
  · intro i hi
    have hi' : (y ++ [val (g0 a b) y]).getD i false = true := hi
    by_cases h1 : i < 14
    · have e0 : rr t i = i := by unfold rr; rw [if_pos h1]
      have h1' : i < y.length := by omega
      rw [List.getD_append _ _ _ _ h1'] at hi'
      rw [e0]
      exact hle i h1 hi'
    · by_cases h2 : i = 14
      · have e1 : rr t i = t := by unfold rr; rw [if_neg h1, if_pos h2]
        have e2 := getD_last y (val (g0 a b) y)
        rw [hy] at e2
        rw [h2, e2, val_and] at hi'
        rw [e1]
        exact h14 hi'
      · have h6 : (y ++ [val (g0 a b) y]).length ≤ i := by
          rw [List.length_append, List.length_singleton]
          omega
        rw [List.getD_eq_default _ _ h6] at hi'
        exact absurd hi' Bool.false_ne_true

theorem core (E : List (ℕ × ℕ)) (C : Circuit) (rest : List Gate) (a b : ℕ)
    (hg : C.gates = { op := GateOp.and, inputs := [a, b] : Gate } :: rest)
    (ha : a < 14) (hb : b < 14)
    (hne : ¬((a, b) ∈ E ∨ (b, a) ∈ E)) (hm : Monotone2 C)
    (hC : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ (u : Fin 14) (v : Fin 14), ((u : ℕ), (v : ℕ)) ∈ E ∧ x u = true ∧ x v = true) :
    ∃ D : Circuit, Monotone2 D ∧ D.size + 1 ≤ C.size ∧
      ∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = true ↔
        ∃ (u : Fin 14) (v : Fin 14), ((u : ℕ), (v : ℕ)) ∈ E ∧ x u = true ∧ x v = true := by
  have hg' : C.gates = g0 a b :: rest := hg
  have hops : ∀ g ∈ rest, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hgm
    have h0 := (hm g (by rw [hg']; exact List.mem_cons_of_mem _ hgm)).1
    simpa using h0
  obtain ⟨t, ht1, ht2, ht3⟩ : ∃ t : ℕ, (t < 14 ∨ t = 14 + rest.length) ∧ (a = b → t = a) ∧
      (a ≠ b → t = 14 + rest.length) := by
    by_cases hab : a = b
    · exact ⟨a, Or.inl ha, fun _ => rfl, fun h => absurd hab h⟩
    · exact ⟨14 + rest.length, Or.inr rfl, fun h => absurd h hab, fun _ => rfl⟩
  refine ⟨⟨rest.map (rn (rr t)), rr t C.output⟩, ?_, ?_, ?_⟩
  · intro g hgm
    obtain ⟨g1, hg1, rfl⟩ := List.mem_map.1 hgm
    have h1 := hm g1 (by rw [hg']; exact List.mem_cons_of_mem _ hg1)
    refine ⟨h1.1, ?_⟩
    show (g1.inputs.map (rr t)).length ≤ 2
    rw [List.length_map]
    exact h1.2
  · have h0 : (rest.map (rn (rr t))).length + 1 = C.gates.length := by
      rw [List.length_map, hg', List.length_cons]
    exact le_of_eq h0
  · intro x
    have hy : (List.ofFn x).length = 14 := List.length_ofFn
    constructor
    · intro h
      have h' : (run (rest.map (rn (rr t))) (List.ofFn x)).getD (rr t C.output) false = true := h
      apply (hC x).1
      show (run C.gates (List.ofFn x)).getD C.output false = true
      rw [hg']
      refine down (List.ofFn x) hy rest a b t hops ht1 ?_ C.output h'
      intro h14
      by_cases hab : a = b
      · rw [ht2 hab] at h14
        have hb' : (List.ofFn x).getD b false = true := by rw [← hab]; exact h14
        simp only [Bool.and_eq_true]
        exact ⟨h14, hb'⟩
      · have h6 : (List.ofFn x).length ≤ t := by rw [hy, ht3 hab]; omega
        rw [List.getD_eq_default _ _ h6] at h14
        exact absurd h14 Bool.false_ne_true
    · rintro ⟨u, v, huv, hu, hv⟩
      have hCe := (hC (ind u v)).2 ⟨u, v, huv, ind_l u v, ind_r u v⟩
      have hCe' : (run (g0 a b :: rest) (List.ofFn (ind u v))).getD C.output false = true := by
        rw [← hg']
        exact hCe
      show (run (rest.map (rn (rr t))) (List.ofFn x)).getD (rr t C.output) false = true
      refine up (List.ofFn (ind u v)) (List.ofFn x) List.length_ofFn hy rest a b t hops ?_ ?_
        C.output hCe'
      · intro i hi h
        rw [ofFn_getD (ind u v) i hi] at h
        rw [ofFn_getD x i hi]
        rcases ind_of u v _ h with h0 | h0
        · rw [h0]; exact hu
        · rw [h0]; exact hv
      · intro h
        simp only [Bool.and_eq_true] at h
        obtain ⟨h1, h2⟩ := h
        rw [ofFn_getD (ind u v) a ha] at h1
        rw [ofFn_getD (ind u v) b hb] at h2
        have h1' : a = (u : ℕ) ∨ a = (v : ℕ) :=
          (ind_of u v _ h1).imp (fun e => congrArg Fin.val e) (fun e => congrArg Fin.val e)
        have h2' : b = (u : ℕ) ∨ b = (v : ℕ) :=
          (ind_of u v _ h2).imp (fun e => congrArg Fin.val e) (fun e => congrArg Fin.val e)
        by_cases hab : a = b
        · rw [ht2 hab, ofFn_getD x a ha]
          rcases ind_of u v _ h1 with h0 | h0
          · rw [h0]; exact hu
          · rw [h0]; exact hv
        · exfalso
          rcases h1' with e1 | e1
          · rcases h2' with e2 | e2
            · exact hab (e1.trans e2.symm)
            · exact hne (Or.inl (by rw [e1, e2]; exact huv))
          · rcases h2' with e2 | e2
            · exact hne (Or.inr (by rw [e1, e2]; exact huv))
            · exact hab (e1.trans e2.symm)

theorem main_aux : have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; have x2 : (Fin (14 : ℕ) → Bool) → Prop := fun (x2 : Fin (14 : ℕ) → Bool) => ∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ x1 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : List PEqualNP.CircuitLowerBounds.Gate) (x5 x6 : ℕ), x3.gates = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } :: x4 → x5 < (14 : ℕ) → x6 < (14 : ℕ) → ¬((x5, x6) ∈ x1 ∨ (x6, x5) ∈ x1) → PEqualNP.MetaComplexity.Monotone2 x3 → (∀ (x12 : Fin (14 : ℕ) → Bool), x3.eval (List.ofFn x12) = Bool.true ↔ x2 x12) → ∃ (x13 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x13 ∧ x13.size + (1 : ℕ) ≤ x3.size ∧ ∀ (x14 : Fin (14 : ℕ) → Bool), x13.eval (List.ofFn x14) = Bool.true ↔ x2 x14 := by
  intro x1 x2 x3 x4 x5 x6 h1 h2 h3 h4 h5 h6
  exact core x1 x3 x4 x5 x6 h1 h2 h3 h4 h5 h6

end PEqualNP.Outside.L_meta_2654

theorem PEqualNP.Outside.L_meta_2654 : have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; have x2 : (Fin (14 : ℕ) → Bool) → Prop := fun (x2 : Fin (14 : ℕ) → Bool) => ∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ x1 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : List PEqualNP.CircuitLowerBounds.Gate) (x5 x6 : ℕ), x3.gates = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } :: x4 → x5 < (14 : ℕ) → x6 < (14 : ℕ) → ¬((x5, x6) ∈ x1 ∨ (x6, x5) ∈ x1) → PEqualNP.MetaComplexity.Monotone2 x3 → (∀ (x12 : Fin (14 : ℕ) → Bool), x3.eval (List.ofFn x12) = Bool.true ↔ x2 x12) → ∃ (x13 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x13 ∧ x13.size + (1 : ℕ) ≤ x3.size ∧ ∀ (x14 : Fin (14 : ℕ) → Bool), x13.eval (List.ofFn x14) = Bool.true ↔ x2 x14 :=
  PEqualNP.Outside.L_meta_2654.main_aux
