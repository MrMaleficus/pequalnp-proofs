import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2826

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotBracket

/-- One step of the binary circuit fold. -/
def bf (w : List Bool) (g : BinaryGate) : List Bool :=
  w ++ [g.op (w.getD g.left false) (w.getD g.right false)]

/-- One step of the root circuit fold. -/
def ostep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def mk (a b : Bool) (p q : ℕ) : BinaryGate := ⟨fun y z => y == a && z == b, p, q⟩

/-- value of a wire with a polarity -/
def val (W : List Bool) (p : ℕ × Bool) : Bool := (W.getD p.1 false != p.2)

def rp (r : List (ℕ × Bool)) (n : ℕ) (o : Option ℕ) (nb : Bool) : ℕ × Bool :=
  match o with
  | none => (n, nb)
  | some i => r.getD i (n, false)

def tstep (n : ℕ) (s : List BinaryGate × List (ℕ × Bool)) (g : Gate) :
    List BinaryGate × List (ℕ × Bool) :=
  match g.op with
  | GateOp.not =>
      (s.1, s.2 ++ [((rp s.2 n g.inputs.head? false).1, !(rp s.2 n g.inputs.head? false).2)])
  | GateOp.or =>
      (s.1 ++ [mk (rp s.2 n g.inputs.head? false).2 (rp s.2 n g.inputs.tail.head? false).2
        (rp s.2 n g.inputs.head? false).1 (rp s.2 n g.inputs.tail.head? false).1],
        s.2 ++ [(n + 1 + s.1.length, true)])
  | _ =>
      (s.1 ++ [mk (!(rp s.2 n g.inputs.head? true).2) (!(rp s.2 n g.inputs.tail.head? true).2)
        (rp s.2 n g.inputs.head? true).1 (rp s.2 n g.inputs.tail.head? true).1],
        s.2 ++ [(n + 1 + s.1.length, false)])

def Inv (W : List Bool) (r : List (ℕ × Bool)) (V : List Bool) : Prop :=
  r.length = V.length ∧ ∀ i (h : i < r.length), r[i].1 < W.length ∧ val W r[i] = V.getD i false

theorem getD_app_left (W L : List Bool) (k : ℕ) (hk : k < W.length) :
    (W ++ L).getD k false = W.getD k false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

theorem getD_app_last (W : List Bool) (c : Bool) : (W ++ [c]).getD W.length false = c := by
  simp [List.getD_eq_getElem?_getD]

theorem bW_len (gs : List BinaryGate) (y : List Bool) :
    (gs.foldl bf y).length = y.length + gs.length := by
  induction gs generalizing y with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [bf]
    omega

theorem bW_pre (gs : List BinaryGate) (y : List Bool) (k : ℕ) (hk : k < y.length) :
    (gs.foldl bf y).getD k false = y.getD k false := by
  induction gs generalizing y with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih (bf y g) (by simp [bf]; omega)]
    exact getD_app_left _ _ _ hk

theorem bW_snoc (gs : List BinaryGate) (b : BinaryGate) (y : List Bool) :
    (gs ++ [b]).foldl bf y = bf (gs.foldl bf y) b := by
  simp [List.foldl_append]

theorem rp_val {W : List Bool} {r : List (ℕ × Bool)} {V : List Bool} {n : ℕ}
    (hI : Inv W r V) (hn : W.getD n false = false) (hnl : n < W.length)
    (o : Option ℕ) (nb : Bool) :
    (rp r n o nb).1 < W.length ∧ val W (rp r n o nb) = o.elim nb (fun i => V.getD i false) := by
  cases o with
  | none =>
    simp only [rp, Option.elim]
    refine ⟨hnl, ?_⟩
    show (W.getD n false != nb) = nb
    rw [hn]
    cases nb <;> rfl
  | some i =>
    simp only [rp, Option.elim]
    by_cases h : i < r.length
    · have e : r.getD i (n, false) = r[i] := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
      rw [e]
      exact hI.2 i h
    · have e : r.getD i (n, false) = (n, false) := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : r.length ≤ i)]
      have e2 : V.getD i false = false := by
        simp [List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by rw [← hI.1]; omega : V.length ≤ i)]
      rw [e, e2]
      refine ⟨hnl, ?_⟩
      show (W.getD n false != false) = false
      rw [hn]
      rfl

theorem inv_snoc {W W' : List Bool} {r : List (ℕ × Bool)} {V : List Bool} {p : ℕ × Bool}
    {b : Bool} (hI : Inv W r V) (hpre : ∀ k < W.length, W'.getD k false = W.getD k false)
    (hle : W.length ≤ W'.length) (hp : p.1 < W'.length) (hv : val W' p = b) :
    Inv W' (r ++ [p]) (V ++ [b]) := by
  refine ⟨by simp [hI.1], fun i hi => ?_⟩
  simp only [List.length_append, List.length_singleton] at hi
  by_cases h : i < r.length
  · rw [List.getElem_append_left h]
    obtain ⟨h1, h2⟩ := hI.2 i h
    refine ⟨by omega, ?_⟩
    rw [getD_app_left V [b] i (by rw [← hI.1]; exact h)]
    simp only [val] at h2 ⊢
    rw [hpre _ h1]
    exact h2
  · have hi' : i = r.length := by omega
    subst hi'
    have e1 : (r ++ [p])[r.length] = p := by simp
    rw [e1, hI.1, getD_app_last]
    exact ⟨hp, hv⟩

theorem eval_and (l : List ℕ) (f : ℕ → Bool) (hl : l.length ≤ 2) :
    GateOp.eval GateOp.and (l.map f) = (l.head?.elim true f && l.tail.head?.elim true f) := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · simp [GateOp.eval]
  · simp [GateOp.eval]
  · simp [GateOp.eval]
  · simp at hl

theorem eval_or (l : List ℕ) (f : ℕ → Bool) (hl : l.length ≤ 2) :
    GateOp.eval GateOp.or (l.map f) = (l.head?.elim false f || l.tail.head?.elim false f) := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · simp [GateOp.eval]
  · simp [GateOp.eval]
  · simp [GateOp.eval]
  · simp at hl

theorem eval_not (l : List ℕ) (f : ℕ → Bool) :
    GateOp.eval GateOp.not (l.map f) = !(l.head?.elim false f) := by
  rcases l with _ | ⟨a, l⟩
  · simp [GateOp.eval]
  · simp [GateOp.eval]

theorem and_gate_val (W : List Bool) (u v : ℕ × Bool) :
    val (bf W (mk (!u.2) (!v.2) u.1 v.1)) (W.length, false) = (val W u && val W v) := by
  obtain ⟨a, s⟩ := u
  obtain ⟨b, t⟩ := v
  simp only [val, bf, mk]
  rw [getD_app_last]
  generalize W.getD a false = p
  generalize W.getD b false = q
  cases p <;> cases q <;> cases s <;> cases t <;> rfl

theorem or_gate_val (W : List Bool) (u v : ℕ × Bool) :
    val (bf W (mk u.2 v.2 u.1 v.1)) (W.length, true) = (val W u || val W v) := by
  obtain ⟨a, s⟩ := u
  obtain ⟨b, t⟩ := v
  simp only [val, bf, mk]
  rw [getD_app_last]
  generalize W.getD a false = p
  generalize W.getD b false = q
  cases p <;> cases q <;> cases s <;> cases t <;> rfl

theorem step_inv (n : ℕ) (y : List Bool) (hyn : y.getD n false = false)
    (hyl : y.length = n + 1) (gs : List BinaryGate) (r : List (ℕ × Bool)) (V : List Bool)
    (hI : Inv (gs.foldl bf y) r V) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    Inv ((tstep n (gs, r) g).1.foldl bf y) (tstep n (gs, r) g).2 (ostep V g) := by
  have hWn : (gs.foldl bf y).getD n false = false := by
    rw [bW_pre _ _ _ (by omega)]
    exact hyn
  have hWl : n < (gs.foldl bf y).length := by
    rw [bW_len]
    omega
  have hWk : (gs.foldl bf y).length = n + 1 + gs.length := by
    rw [bW_len, hyl]
  obtain ⟨op, l⟩ := g
  obtain ⟨hop, hl⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · -- and
    obtain ⟨hu1, hu2⟩ := rp_val hI hWn hWl l.head? true
    obtain ⟨hv1, hv2⟩ := rp_val hI hWn hWl l.tail.head? true
    simp only [tstep, ostep]
    rw [bW_snoc]
    apply inv_snoc hI
    · intro k hk
      exact getD_app_left _ _ _ hk
    · simp [bf]
    · simp [bf]
      omega
    · rw [← hWk, and_gate_val, hu2, hv2, eval_and _ _ hl]
  · -- or
    obtain ⟨hu1, hu2⟩ := rp_val hI hWn hWl l.head? false
    obtain ⟨hv1, hv2⟩ := rp_val hI hWn hWl l.tail.head? false
    simp only [tstep, ostep]
    rw [bW_snoc]
    apply inv_snoc hI
    · intro k hk
      exact getD_app_left _ _ _ hk
    · simp [bf]
    · simp [bf]
      omega
    · rw [← hWk, or_gate_val, hu2, hv2, eval_or _ _ hl]
  · -- not
    obtain ⟨hu1, hu2⟩ := rp_val hI hWn hWl l.head? false
    simp only [tstep, ostep]
    apply inv_snoc hI
    · intro k _
      rfl
    · exact le_refl _
    · exact hu1
    · rw [eval_not, ← hu2]
      simp only [val]
      generalize (gs.foldl bf y).getD (rp r n l.head? false).1 false = p
      generalize (rp r n l.head? false).2 = s
      cases p <;> cases s <;> rfl

theorem trans_inv (n : ℕ) (y : List Bool) (hyn : y.getD n false = false)
    (hyl : y.length = n + 1) (L : List Gate)
    (hL : ∀ g ∈ L, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2) :
    ∀ (gs : List BinaryGate) (r : List (ℕ × Bool)) (V : List Bool),
      Inv (gs.foldl bf y) r V →
      Inv ((L.foldl (tstep n) (gs, r)).1.foldl bf y) (L.foldl (tstep n) (gs, r)).2
        (L.foldl ostep V) := by
  induction L with
  | nil => intro gs r V h; exact h
  | cons g L ih =>
    intro gs r V h
    rw [List.foldl_cons, List.foldl_cons]
    exact ih (fun g' hg' => hL g' (List.mem_cons_of_mem _ hg')) (tstep n (gs, r) g).1
      (tstep n (gs, r) g).2 (ostep V g)
      (step_inv n y hyn hyl gs r V h g (hL g (List.mem_cons_self ..)))

theorem size_count (n : ℕ) (L : List Gate) :
    ∀ (s : List BinaryGate × List (ℕ × Bool)),
      (L.foldl (tstep n) s).1.length + notCount ⟨L, 0⟩ = s.1.length + L.length := by
  induction L with
  | nil => intro s; simp [notCount]
  | cons g L ih =>
    intro s
    rw [List.foldl_cons]
    have h1 := ih (tstep n s g)
    obtain ⟨op, l⟩ := g
    cases op <;> simp [tstep, notCount, List.filter_cons] at h1 ⊢ <;> omega

theorem gates_form (n : ℕ) (L : List Gate) :
    ∀ (s : List BinaryGate × List (ℕ × Bool)),
      (∀ g ∈ s.1, ∃ (a b : Bool), g.op = fun (y z : Bool) => y == a && z == b) →
      ∀ g ∈ (L.foldl (tstep n) s).1, ∃ (a b : Bool), g.op = fun (y z : Bool) => y == a && z == b := by
  induction L with
  | nil => intro s h; exact h
  | cons g L ih =>
    intro s h
    rw [List.foldl_cons]
    apply ih
    obtain ⟨op, l⟩ := g
    cases op <;> simp only [tstep] <;>
      first
      | exact h
      | (intro g' hg'
         rcases List.mem_append.mp hg' with hg' | hg'
         · exact h g' hg'
         · rw [List.mem_singleton] at hg'
           subst hg'
           exact ⟨_, _, rfl⟩)

def r0 : List (ℕ × Bool) := (List.range 10).map fun i => (i, false)

theorem init_inv (x : List Bool) (hx : x.length = 10) : Inv (x ++ [false]) r0 x := by
  refine ⟨by simp [r0, hx], fun i hi => ?_⟩
  have hi' : i < 10 := by simpa [r0] using hi
  have e : ∀ h : i < r0.length, r0[i]'h = (i, false) := by
    intro h
    have h2 : r0[i]? = some (i, false) := by simp [r0, hi']
    rw [List.getElem?_eq_getElem h] at h2
    exact Option.some.inj h2
  simp only [e]
  refine ⟨(by simp [hx]; omega : i < (x ++ [false]).length), ?_⟩
  show ((x ++ [false]).getD i false != false) = x.getD i false
  rw [getD_app_left _ _ _ (by omega)]
  simp

theorem main_aux : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → ∃ (x3 : PEqualNP.MetaComplexity.BinaryCircuit) (x4 : Bool), (∀ x5 ∈ x3.gates, ∃ (x7 : Bool) (x8 : Bool), x5.op = fun (x9 x10 : Bool) => x9 == x7 && x10 == x8) ∧ x3.size + PEqualNP.NotBracket.notCount x1 ≤ x1.size ∧ ∀ (x5 : List Bool), x5.length = (10 : ℕ) → (x3.eval (x5 ++ [Bool.false]) != x4) = x1.eval x5 := by
  intro C hC
  refine ⟨⟨(C.gates.foldl (tstep 10) ([], r0)).1,
    (rp (C.gates.foldl (tstep 10) ([], r0)).2 10 (some C.output) false).1⟩,
    (rp (C.gates.foldl (tstep 10) ([], r0)).2 10 (some C.output) false).2, ?_, ?_, ?_⟩
  · exact gates_form 10 C.gates ([], r0) (by simp)
  · have h := size_count 10 C.gates ([], r0)
    have e : notCount C = notCount ⟨C.gates, 0⟩ := rfl
    show (C.gates.foldl (tstep 10) ([], r0)).1.length + notCount C ≤ C.gates.length
    rw [e]
    simp only [List.length_nil, Nat.zero_add] at h
    omega
  · intro x hx
    have hyn : (x ++ [false]).getD 10 false = false := by
      rw [← hx, getD_app_last]
    have hyl : (x ++ [false]).length = 10 + 1 := by simp [hx]
    have hT := trans_inv 10 (x ++ [false]) hyn hyl C.gates hC [] r0 x (init_inv x hx)
    have hWn : ((C.gates.foldl (tstep 10) ([], r0)).1.foldl bf (x ++ [false])).getD 10 false
        = false := by
      rw [bW_pre _ _ _ (by omega)]
      exact hyn
    have hWl : 10 < ((C.gates.foldl (tstep 10) ([], r0)).1.foldl bf (x ++ [false])).length := by
      rw [bW_len]
      omega
    exact (rp_val hT hWn hWl (some C.output) false).2

end PEqualNP.Outside.L_meta_2826

theorem PEqualNP.Outside.L_meta_2826 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → ∃ (x3 : PEqualNP.MetaComplexity.BinaryCircuit) (x4 : Bool), (∀ x5 ∈ x3.gates, ∃ (x7 : Bool) (x8 : Bool), x5.op = fun (x9 x10 : Bool) => x9 == x7 && x10 == x8) ∧ x3.size + PEqualNP.NotBracket.notCount x1 ≤ x1.size ∧ ∀ (x5 : List Bool), x5.length = (10 : ℕ) → (x3.eval (x5 ++ [Bool.false]) != x4) = x1.eval x5 :=
  PEqualNP.Outside.L_meta_2826.main_aux
