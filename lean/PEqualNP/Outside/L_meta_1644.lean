import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1644

open PEqualNP.CircuitLowerBounds

def x44brun (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma x44bruncons (g : Gate) (gs : List Gate) (x : List Bool) :
    x44brun (g :: gs) x = x44brun gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma x44brunlength (gs : List Gate) (x : List Bool) :
    (x44brun gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [x44brun]
  | cons g gs ih => rw [x44bruncons, ih]; simp; omega

lemma x44brungetD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (x44brun gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [x44bruncons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma x44brunsplit (gs : List Gate) (x : List Bool) (j : ℕ) :
    x44brun gs x = x44brun (gs.drop j) (x44brun (gs.take j) x) := by
  simpa only [x44brun, List.foldl_append] using
    congrArg (fun l : List Gate => x44brun l x) (List.take_append_drop j gs).symm

def x44bvalue {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma x44binputvalue {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    x44bvalue C x p = x p := by
  change (x44brun C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [x44brungetD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma x44bmissingvalue {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : x44bvalue C x w = false := by
  change (x44brun C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [x44brunlength, Circuit.size] using hw)

lemma x44bgatevalue {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    x44bvalue C x w = g.op.eval (g.inputs.map fun r => if r < w then x44bvalue C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := x44brun (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, x44brunlength, Nat.min_eq_left hj.le, j]; omega
  have split : x44brun C.gates (List.ofFn x) = x44brun (g :: C.gates.drop (j + 1)) earlier := by
    rw [x44brunsplit C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then x44bvalue C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (x44brun C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (x44brungetD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (x44brun C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then x44bvalue C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [x44bruncons]
  rw [x44brungetD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma x44bgatemono {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or)
    (x y : Fin n → Bool)
    (h : ∀ r ∈ C.gates[k].inputs, r < n + k → x44bvalue C x r = true → x44bvalue C y r = true) :
    x44bvalue C x (n + k) = true → x44bvalue C y (n + k) = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := x44bgatevalue C x (n + k) (by omega) hw
  have hy := x44bgatevalue C y (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx hy
  rw [hx, hy]
  have hr (r : ℕ) (hm : r ∈ C.gates[k].inputs) :
      (if r < n + k then x44bvalue C x r else false) = true →
      (if r < n + k then x44bvalue C y r else false) = true := by
    by_cases h' : r < n + k
    · simpa [h'] using h r hm h'
    · simp [h']
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_eq_true, id_eq]
    intro hx b hb
    obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
    exact hr r hm (hx _ (List.mem_map.mpr ⟨r, hm, rfl⟩))
  · simp only [hop, GateOp.eval, List.any_eq_true, id_eq]
    intro hx
    obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨r, hm, hv⟩ := List.mem_map.mp hb
    exact ⟨_, List.mem_map.mpr ⟨r, hm, rfl⟩, hr r hm hv⟩

lemma x44borvalue {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.or) (x : Fin n → Bool) :
    x44bvalue C x (n + k) = true ↔ ∃ r ∈ C.gates[k].inputs, r < n + k ∧ x44bvalue C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := x44bgatevalue C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx
  rw [hx, hop]
  simp [GateOp.eval]

lemma x44bandvalue {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and) (x : Fin n → Bool) :
    x44bvalue C x (n + k) = true ↔ ∀ r ∈ C.gates[k].inputs, r < n + k ∧ x44bvalue C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := x44bgatevalue C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx
  rw [hx, hop]
  simp [GateOp.eval]

lemma x44bmono {n : ℕ} (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (h : ∀ v, x v = true → y v = true) (w : ℕ) :
    x44bvalue C x w = true → x44bvalue C y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change x44bvalue C x p = true → x44bvalue C y p = true
      simpa only [x44binputvalue] using h p
    by_cases hw : w < n + C.gates.length
    · have hk : w - n < C.gates.length := by omega
      have hwk : w = n + (w - n) := by omega
      rw [hwk]
      exact x44bgatemono C (w - n) hk (hC _ (List.getElem_mem hk)).1 x y fun r _ hlt => ih r (by omega)
    · simp [x44bmissingvalue C x w (by unfold Circuit.size; omega)]

lemma x44hmono (N : ℕ) (gates : List Gate) (j : Fin gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hone : ∀ i : Fin gates.length, (gates.get i).op = GateOp.not → i = j)
    (x y : Fin N → Bool) (hxy : ∀ v, x v = true → y v = true) (w : ℕ) (hw : w < N + (j : ℕ)) :
    x44bvalue ⟨gates, 0⟩ x w = true → x44bvalue ⟨gates, 0⟩ y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < N
    · let p : Fin N := ⟨w, hn⟩
      change x44bvalue ⟨gates, 0⟩ x p = true → x44bvalue ⟨gates, 0⟩ y p = true
      simpa only [x44binputvalue] using hxy p
    · have hk : w - N < gates.length := by
        have := j.isLt
        omega
      have hwk : w = N + (w - N) := by omega
      rw [hwk]
      have hop : gates[w - N].op = GateOp.and ∨ gates[w - N].op = GateOp.or := by
        rcases (hg _ (List.getElem_mem hk)).1 with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · have h1 := hone ⟨w - N, hk⟩ h
          have h2 : w - N = (j : ℕ) := congrArg Fin.val h1
          omega
      exact x44bgatemono (n := N) ⟨gates, 0⟩ (w - N) hk hop x y fun r _ hlt => ih r (by omega) (by omega)

def x44drun (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma x44druncons (g : Gate) (gs : List Gate) (x : List Bool) :
    x44drun (g :: gs) x = x44drun gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma x44drunappend (A B : List Gate) (x : List Bool) : x44drun (A ++ B) x = x44drun B (x44drun A x) := by
  simp [x44drun, List.foldl_append]

lemma x44drunlength (gs : List Gate) (x : List Bool) :
    (x44drun gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [x44drun]
  | cons g gs ih => rw [x44druncons, ih]; simp; omega

lemma x44drungetD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (x44drun gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [x44druncons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma x44drunsplit (gs : List Gate) (x : List Bool) (j : ℕ) :
    x44drun gs x = x44drun (gs.drop j) (x44drun (gs.take j) x) := by
  simpa only [x44drun, List.foldl_append] using
    congrArg (fun l : List Gate => x44drun l x) (List.take_append_drop j gs).symm

def x44dvalue {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma x44dmissingvalue {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : x44dvalue C x w = false := by
  change (x44drun C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [x44drunlength, Circuit.size] using hw)

lemma x44dgatevalue {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    x44dvalue C x w = g.op.eval (g.inputs.map fun r => if r < w then x44dvalue C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := x44drun (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, x44drunlength, Nat.min_eq_left hj.le, j]; omega
  have split : x44drun C.gates (List.ofFn x) = x44drun (g :: C.gates.drop (j + 1)) earlier := by
    rw [x44drunsplit C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then x44dvalue C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (x44drun C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (x44drungetD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (x44drun C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then x44dvalue C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [x44druncons]
  rw [x44drungetD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma x44dgatevalueP {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (k : ℕ) (hk : k < gs.length) :
    x44dvalue ⟨gs, 0⟩ x (n + k) =
      gs[k].op.eval (gs[k].inputs.map fun r => if r < n + k then x44dvalue ⟨gs, 0⟩ x r else false) := by
  have h := x44dgatevalue ⟨gs, 0⟩ x (n + k) (by omega) (by change n + k < n + gs.length; omega)
  simpa only [Nat.add_sub_cancel_left] using h

def x44isOr : GateOp → Bool
  | GateOp.or => true
  | _ => false

def x44isNot : GateOp → Bool
  | GateOp.not => true
  | _ => false

lemma x44eval_ao (op : GateOp) (l : List Bool) (h : op = GateOp.and ∨ op = GateOp.or) :
    op.eval l = if x44isOr op ∈ l then x44isOr op else !x44isOr op := by
  rcases h with rfl | rfl
  · simp only [GateOp.eval, x44isOr]
    induction l with
    | nil => rfl
    | cons b t ih => cases b <;> simp_all
  · simp only [GateOp.eval, x44isOr]
    induction l with
    | nil => rfl
    | cons b t ih => cases b <;> simp_all

def x44fin3 (a : Bool) (op : GateOp) (N : ℕ) : List ℕ → (Bool ⊕ ℕ) × List Gate
  | [] => (Sum.inl (!a), [])
  | [w] => (Sum.inr w, [])
  | w :: w2 :: t => (Sum.inr N, [⟨op, w :: w2 :: t⟩])

def x44gen (ρ : List (Bool ⊕ ℕ)) (N : ℕ) (g : Gate) : (Bool ⊕ ℕ) × List Gate :=
  if Sum.inl (x44isOr g.op) ∈ g.inputs.map (fun r => ρ.getD r (Sum.inl false)) then
    (Sum.inl (x44isOr g.op), [])
  else x44fin3 (x44isOr g.op) g.op N
    ((g.inputs.map (fun r => ρ.getD r (Sum.inl false))).filterMap Sum.getRight?)

def x44stp (n h k : ℕ) (g : Gate) (s : List (Bool ⊕ ℕ) × List Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  if k < h then (s.1 ++ [Sum.inr (n + s.2.length)], s.2 ++ [g])
  else if k = h then (s.1 ++ [Sum.inl true], s.2)
  else if x44isNot g.op = true then (s.1 ++ [Sum.inl false], s.2)
  else (s.1 ++ [(x44gen s.1 (n + s.2.length) g).1], s.2 ++ (x44gen s.1 (n + s.2.length) g).2)

def x44S (n h : ℕ) (gs : List Gate) : ℕ → List (Bool ⊕ ℕ) × List Gate
  | 0 => ((List.range n).map Sum.inr, [])
  | k + 1 => match gs[k]? with
    | none => x44S n h gs k
    | some g => x44stp n h k g (x44S n h gs k)

lemma x44S_succ (n h : ℕ) (gs : List Gate) (k : ℕ) (hk : k < gs.length) :
    x44S n h gs (k + 1) = x44stp n h k gs[k] (x44S n h gs k) := by
  rw [x44S]
  simp [hk]

lemma x44fin3_len (a : Bool) (op : GateOp) (N : ℕ) (l : List ℕ) : (x44fin3 a op N l).2.length ≤ 1 := by
  rcases l with _ | ⟨w, _ | ⟨w2, t⟩⟩ <;> simp [x44fin3]

lemma x44fin3_mem (a : Bool) (op : GateOp) (N : ℕ) (l : List ℕ) :
    ∀ g' ∈ (x44fin3 a op N l).2, g'.op = op ∧ g'.inputs = l := by
  rcases l with _ | ⟨w, _ | ⟨w2, t⟩⟩ <;> simp [x44fin3]

lemma x44fin3_short (a : Bool) (op : GateOp) (N : ℕ) (l : List ℕ) (h : l.length ≤ 1) :
    (x44fin3 a op N l).2 = [] := by
  rcases l with _ | ⟨w, _ | ⟨w2, t⟩⟩
  · rfl
  · rfl
  · simp at h

lemma x44gen_len (ρ : List (Bool ⊕ ℕ)) (N : ℕ) (g : Gate) : (x44gen ρ N g).2.length ≤ 1 := by
  unfold x44gen
  split_ifs
  · simp
  · exact x44fin3_len _ _ _ _

lemma x44gen_mem (ρ : List (Bool ⊕ ℕ)) (N : ℕ) (g : Gate) :
    ∀ g' ∈ (x44gen ρ N g).2, g'.op = g.op ∧ g'.inputs.length ≤ g.inputs.length := by
  unfold x44gen
  split_ifs
  · simp
  · intro g' hg'
    obtain ⟨h1, h2⟩ := x44fin3_mem _ _ _ _ g' hg'
    refine ⟨h1, ?_⟩
    rw [h2]
    exact (List.length_filterMap_le _ _).trans (by simp)

lemma x44filterMap_lt (l : List (Bool ⊕ ℕ)) (b : Bool) (h : Sum.inl b ∈ l) :
    (l.filterMap Sum.getRight?).length + 1 ≤ l.length := by
  induction l with
  | nil => simp at h
  | cons c t ih =>
    rcases List.mem_cons.mp h with h | h
    · subst h
      have := List.length_filterMap_le Sum.getRight? t
      change (t.filterMap Sum.getRight?).length + 1 ≤ t.length + 1
      omega
    · have := ih h
      rcases c with c | c
      · change (t.filterMap Sum.getRight?).length + 1 ≤ t.length + 1
        omega
      · change (t.filterMap Sum.getRight?).length + 1 + 1 ≤ t.length + 1
        omega

lemma x44gen_reader (ρ : List (Bool ⊕ ℕ)) (N : ℕ) (g : Gate) (hlen : g.inputs.length ≤ 2)
    (r : ℕ) (hr : r ∈ g.inputs) (hρ : ρ.getD r (Sum.inl false) = Sum.inl false) :
    (x44gen ρ N g).2 = [] := by
  unfold x44gen
  split_ifs
  · rfl
  · apply x44fin3_short
    have hm : Sum.inl false ∈ g.inputs.map (fun r => ρ.getD r (Sum.inl false)) :=
      List.mem_map.mpr ⟨r, hr, hρ⟩
    have := x44filterMap_lt _ false hm
    simp only [List.length_map] at this
    omega

lemma x44stp_fst (n h k : ℕ) (g : Gate) (s : List (Bool ⊕ ℕ) × List Gate) :
    ∃ d, (x44stp n h k g s).1 = s.1 ++ [d] := by
  unfold x44stp
  split_ifs <;> exact ⟨_, rfl⟩

lemma x44stp_snd (n h k : ℕ) (g : Gate) (s : List (Bool ⊕ ℕ) × List Gate) :
    ∃ e, (x44stp n h k g s).2 = s.2 ++ e ∧ e.length ≤ 1 := by
  unfold x44stp
  split_ifs
  · exact ⟨[g], rfl, by simp⟩
  · exact ⟨[], by simp, by simp⟩
  · exact ⟨[], by simp, by simp⟩
  · exact ⟨_, rfl, x44gen_len _ _ _⟩

lemma x44S_len (n h : ℕ) (gs : List Gate) : ∀ k, k ≤ gs.length → (x44S n h gs k).1.length = n + k := by
  intro k
  induction k with
  | zero => intro _; simp [x44S]
  | succ k ih =>
    intro hk
    rw [x44S_succ n h gs k (by omega)]
    obtain ⟨d, hd⟩ := x44stp_fst n h k gs[k] (x44S n h gs k)
    rw [hd, List.length_append, ih (by omega)]
    simp
    omega

lemma x44S_low (n h : ℕ) (gs : List Gate) : ∀ k, k ≤ gs.length → k ≤ h →
    (x44S n h gs k).2 = gs.take k ∧ (x44S n h gs k).1 = (List.range (n + k)).map Sum.inr := by
  intro k
  induction k with
  | zero => intro _ _; simp [x44S]
  | succ k ih =>
    intro hk hkh
    obtain ⟨h1, h2⟩ := ih (by omega) (by omega)
    rw [x44S_succ n h gs k (by omega)]
    have hlt : k < h := by omega
    unfold x44stp
    simp only [hlt, ↓reduceIte]
    rw [h1, h2]
    refine ⟨(List.take_succ_eq_append_getElem (by omega)).symm, ?_⟩
    have : (List.take k gs).length = k := by simp; omega
    rw [this, ← Nat.add_assoc, List.range_succ, List.map_append]
    rfl

lemma x44S_prefix (n h : ℕ) (gs : List Gate) : ∀ k, k ≤ gs.length → h ≤ k →
    gs.take h <+: (x44S n h gs k).2 := by
  intro k
  induction k with
  | zero =>
    intro _ hh
    have : h = 0 := by omega
    subst this
    simp
  | succ k ih =>
    intro hk hh
    by_cases he : h = k + 1
    · rw [he, (x44S_low n (k + 1) gs (k + 1) hk le_rfl).1]
    · rw [x44S_succ n h gs k (by omega)]
      obtain ⟨e, he2, _⟩ := x44stp_snd n h k gs[k] (x44S n h gs k)
      rw [he2]
      exact (ih (by omega) (by omega)).trans (List.prefix_append _ _)

lemma x44S_ops (n h j : ℕ) (gs : List Gate) (hhj : h < j)
    (hops : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (huniq : ∀ i (hi : i < gs.length), gs[i].op = GateOp.not → i = j) :
    ∀ k, k ≤ gs.length → ∀ g' ∈ (x44S n h gs k).2,
      (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2 := by
  intro k
  induction k with
  | zero => intro _ g' hg'; simp [x44S] at hg'
  | succ k ih =>
    intro hk g' hg'
    have hkl : k < gs.length := by omega
    rw [x44S_succ n h gs k hkl] at hg'
    have hg := hops gs[k] (List.getElem_mem hkl)
    unfold x44stp at hg'
    split_ifs at hg' with h1 h2 h3
    · rcases List.mem_append.mp hg' with hm | hm
      · exact ih (by omega) g' hm
      · rw [List.mem_singleton.mp hm]
        refine ⟨?_, hg.2⟩
        rcases hg.1 with ho | ho | ho
        · exact Or.inl ho
        · exact Or.inr ho
        · have := huniq k hkl ho
          omega
    · exact ih (by omega) g' hg'
    · exact ih (by omega) g' hg'
    · rcases List.mem_append.mp hg' with hm | hm
      · exact ih (by omega) g' hm
      · obtain ⟨e1, e2⟩ := x44gen_mem _ _ _ g' hm
        refine ⟨?_, e2.trans hg.2⟩
        rw [e1]
        rcases hg.1 with ho | ho | ho
        · exact Or.inl ho
        · exact Or.inr ho
        · rw [ho] at h3
          exact absurd rfl h3

lemma x44S_j (n h j : ℕ) (gs : List Gate) (hhj : h < j) (hj : j < gs.length)
    (hjn : gs[j].op = GateOp.not) :
    ∀ k, k ≤ gs.length → j < k → (x44S n h gs k).1.getD (n + j) (Sum.inl false) = Sum.inl false := by
  intro k
  induction k with
  | zero => intro _ h0; omega
  | succ k ih =>
    intro hk hjk
    have hkl : k < gs.length := by omega
    have hl := x44S_len n h gs k (by omega)
    by_cases he : k = j
    · subst he
      rw [x44S_succ n h gs k hkl]
      unfold x44stp
      have h1 : ¬ k < h := by omega
      have h2 : ¬ k = h := by omega
      have h3 : x44isNot gs[k].op = true := by rw [hjn]; rfl
      simp only [h1, h2, h3, ↓reduceIte]
      rw [List.getD_append_right _ _ _ _ (by omega)]
      simp [hl]
    · rw [x44S_succ n h gs k hkl]
      obtain ⟨d, hd⟩ := x44stp_fst n h k gs[k] (x44S n h gs k)
      rw [hd, List.getD_append _ _ _ _ (by omega)]
      exact ih (by omega) (by omega)

def x44bad (n h j : ℕ) (gs : List Gate) (i : ℕ) : Bool :=
  decide (i = h ∨ i = j ∨ (j < i ∧ n + j ∈ (gs.getD i ⟨GateOp.and, []⟩).inputs))

lemma x44S_bad (n h j : ℕ) (gs : List Gate) (hhj : h < j) (hj : j < gs.length)
    (hjn : gs[j].op = GateOp.not) (hlen : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (k : ℕ) (hk : k < gs.length) (hb : x44bad n h j gs k = true) :
    (x44S n h gs (k + 1)).2 = (x44S n h gs k).2 := by
  rw [x44S_succ n h gs k hk]
  unfold x44bad at hb
  simp only [decide_eq_true_eq] at hb
  unfold x44stp
  rcases hb with hb | hb | ⟨hb1, hb2⟩
  · subst hb
    simp only [lt_irrefl, ↓reduceIte]
  · have h1 : ¬ k < h := by omega
    have h2 : ¬ k = h := by omega
    have h3 : x44isNot gs[k].op = true := by subst hb; rw [hjn]; rfl
    simp only [h1, h2, h3, ↓reduceIte]
  · have h1 : ¬ k < h := by omega
    have h2 : ¬ k = h := by omega
    simp only [h1, h2, ↓reduceIte]
    split_ifs
    · rfl
    · rw [List.getD_eq_getElem _ _ hk] at hb2
      rw [x44gen_reader _ _ gs[k] (hlen _ (List.getElem_mem hk)) (n + j) hb2
        (x44S_j n h j gs hhj hj hjn k (by omega) hb1)]
      simp

lemma x44S_count (n h j : ℕ) (gs : List Gate) (hhj : h < j) (hj : j < gs.length)
    (hjn : gs[j].op = GateOp.not) (hlen : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∀ k, k ≤ gs.length →
      (x44S n h gs k).2.length + ((Finset.range k).filter (fun i => x44bad n h j gs i = true)).card ≤ k := by
  intro k
  induction k with
  | zero => intro _; simp [x44S]
  | succ k ih =>
    intro hk
    have hkl : k < gs.length := by omega
    have ih' := ih (by omega)
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases hb : x44bad n h j gs k = true
    · rw [x44S_bad n h j gs hhj hj hjn hlen k hkl hb]
      simp only [hb, ↓reduceIte]
      rw [Finset.card_insert_of_notMem (by simp)]
      omega
    · simp only [hb]
      rw [x44S_succ n h gs k hkl]
      obtain ⟨e, he, hel⟩ := x44stp_snd n h k gs[k] (x44S n h gs k)
      rw [he, List.length_append]
      have : (false = true) = False := by simp
      simp only [this, ↓reduceIte]
      omega

def x44Rp (W' : List Bool) (v : Bool) : Bool ⊕ ℕ → Prop
  | Sum.inl b => v = b
  | Sum.inr w => w < W'.length ∧ W'.getD w false = v

lemma x44Rp_mono (W' : List Bool) (e : List Gate) (v : Bool) (r : Bool ⊕ ℕ) (hr : x44Rp W' v r) :
    x44Rp (x44drun e W') v r := by
  rcases r with b | w
  · exact hr
  · exact ⟨by rw [x44drunlength]; exact Nat.lt_add_right _ hr.1, by rw [x44drungetD _ _ _ hr.1]; exact hr.2⟩

lemma x44ext (ρ : List (Bool ⊕ ℕ)) (W' : List Bool) (e : List Gate) (d : Bool ⊕ ℕ) (V : ℕ → Bool)
    (N : ℕ) (hlen : ρ.length = N)
    (ih : ∀ i, x44Rp W' (if i < N then V i else false) (ρ.getD i (Sum.inl false)))
    (hd : x44Rp (x44drun e W') (V N) d) (i : ℕ) :
    x44Rp (x44drun e W') (if i < N + 1 then V i else false) ((ρ ++ [d]).getD i (Sum.inl false)) := by
  rcases lt_trichotomy i N with hi | hi | hi
  · rw [List.getD_append _ _ _ _ (by omega)]
    have := x44Rp_mono W' e _ _ (ih i)
    have h1 : i < N + 1 := by omega
    simpa only [hi, h1, ↓reduceIte] using this
  · subst hi
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simpa [hlen] using hd
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    have h1 : ¬ i < N + 1 := by omega
    simp only [h1, ↓reduceIte]
    exact rfl

lemma x44gen_sem (ρ : List (Bool ⊕ ℕ)) (W' : List Bool) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (vals : ℕ → Bool)
    (hr : ∀ r ∈ g.inputs, x44Rp W' (vals r) (ρ.getD r (Sum.inl false))) :
    x44Rp (x44drun (x44gen ρ W'.length g).2 W') (g.op.eval (g.inputs.map vals)) (x44gen ρ W'.length g).1 := by
  rw [x44eval_ao g.op _ hop]
  unfold x44gen
  by_cases hin : Sum.inl (x44isOr g.op) ∈ g.inputs.map (fun r => ρ.getD r (Sum.inl false))
  · simp only [hin, ↓reduceIte]
    obtain ⟨r, hrm, hre⟩ := List.mem_map.mp hin
    have h1 := hr r hrm
    rw [hre] at h1
    have h2 : vals r = x44isOr g.op := h1
    have hmem : x44isOr g.op ∈ g.inputs.map vals := List.mem_map.mpr ⟨r, hrm, h2⟩
    simp only [hmem, ↓reduceIte]
    exact rfl
  · simp only [hin, ↓reduceIte]
    have key1 : ∀ w ∈ (g.inputs.map (fun r => ρ.getD r (Sum.inl false))).filterMap Sum.getRight?,
        w < W'.length ∧ ∃ r ∈ g.inputs, W'.getD w false = vals r := by
      intro w hw
      obtain ⟨c, hc, hcw⟩ := List.mem_filterMap.mp hw
      obtain ⟨r, hrm, hre⟩ := List.mem_map.mp hc
      have hc' : c = Sum.inr w := Sum.getRight?_eq_some_iff.mp hcw
      have h1 := hr r hrm
      rw [hre, hc'] at h1
      exact ⟨h1.1, r, hrm, h1.2⟩
    have key2 : x44isOr g.op ∈ g.inputs.map vals ↔ x44isOr g.op ∈
        ((g.inputs.map (fun r => ρ.getD r (Sum.inl false))).filterMap Sum.getRight?).map
          (fun w => W'.getD w false) := by
      constructor
      · intro hm
        obtain ⟨r, hrm, hre⟩ := List.mem_map.mp hm
        have h1 := hr r hrm
        rcases hc : ρ.getD r (Sum.inl false) with b | w
        · rw [hc] at h1
          have h2 : vals r = b := h1
          exact absurd (List.mem_map.mpr ⟨r, hrm, by rw [hc, ← h2, hre]⟩) hin
        · rw [hc] at h1
          refine List.mem_map.mpr ⟨w, List.mem_filterMap.mpr ⟨Sum.inr w, List.mem_map.mpr ⟨r, hrm, hc⟩, rfl⟩, ?_⟩
          rw [h1.2, hre]
      · intro hm
        obtain ⟨w, hw, hwe⟩ := List.mem_map.mp hm
        obtain ⟨_, r, hrm, hre⟩ := key1 w hw
        exact List.mem_map.mpr ⟨r, hrm, by rw [← hre, hwe]⟩
    simp only [key2]
    generalize (g.inputs.map (fun r => ρ.getD r (Sum.inl false))).filterMap Sum.getRight? = l at key1
    rcases l with _ | ⟨w, _ | ⟨w2, t⟩⟩
    · simp [x44fin3, x44Rp]
    · have hw := (key1 w (by simp)).1
      refine ⟨hw, ?_⟩
      change W'.getD w false = _
      simp only [List.map_cons, List.map_nil, List.mem_singleton]
      generalize W'.getD w false = c
      cases x44isOr g.op <;> cases c <;> simp
    · refine ⟨by simp [x44fin3, x44drun], ?_⟩
      simp only [x44fin3, x44drun, List.foldl_cons, List.foldl_nil]
      rw [List.getD_append_right _ _ _ _ (by omega)]
      simp only [Nat.sub_self, List.getD_cons_zero]
      exact x44eval_ao g.op _ hop

lemma x44sem (n h j : ℕ) (gs : List Gate) (x : Fin n → Bool)
    (hops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (huniq : ∀ i (hi : i < gs.length), gs[i].op = GateOp.not → i = j)
    (hh : x44dvalue ⟨gs, 0⟩ x (n + h) = true) (hjv : x44dvalue ⟨gs, 0⟩ x (n + j) = false) :
    ∀ k, k ≤ gs.length → ∀ i, x44Rp (x44drun (x44S n h gs k).2 (List.ofFn x))
      (if i < n + k then x44dvalue ⟨gs, 0⟩ x i else false)
      ((x44S n h gs k).1.getD i (Sum.inl false)) := by
  intro k
  induction k with
  | zero =>
    intro _ i
    change x44Rp (List.ofFn x) (if i < n + 0 then x44dvalue ⟨gs, 0⟩ x i else false)
      (((List.range n).map Sum.inr).getD i (Sum.inl false))
    by_cases hi : i < n
    · have e1 : ((List.range n).map (Sum.inr : ℕ → Bool ⊕ ℕ)).getD i (Sum.inl false) = Sum.inr i := by
        rw [List.getD_eq_getElem _ _ (by simpa using hi)]
        simp
      rw [e1]
      simp only [Nat.add_zero, hi, ↓reduceIte]
      refine ⟨by simpa using hi, ?_⟩
      exact (x44drungetD gs _ i (by simpa using hi)).symm
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      simp only [Nat.add_zero, hi, ↓reduceIte]
      exact rfl
  | succ k ih =>
    intro hk
    have hkl : k < gs.length := by omega
    have ih' := ih (by omega)
    have hl := x44S_len n h gs k (by omega)
    have hWl : (x44drun (x44S n h gs k).2 (List.ofFn x)).length = n + (x44S n h gs k).2.length := by
      rw [x44drunlength]; simp
    have hgv := x44dgatevalueP gs x k hkl
    rw [x44S_succ n h gs k hkl]
    unfold x44stp
    split_ifs with h1 h2 h3
    · simp only [x44drunappend, ← Nat.add_assoc]
      apply x44ext _ _ _ _ (fun i => x44dvalue ⟨gs, 0⟩ x i) (n + k) hl ih'
      obtain ⟨l1, l2⟩ := x44S_low n h gs k (by omega) (by omega)
      have hk2 : (x44S n h gs k).2.length = k := by rw [l1]; simp; omega
      refine ⟨by rw [x44drunlength, hWl]; simp, ?_⟩
      change ((x44drun (x44S n h gs k).2 (List.ofFn x)) ++ [_]).getD _ false = _
      rw [List.getD_append_right _ _ _ _ (by omega), hWl, Nat.sub_self, List.getD_cons_zero, hgv]
      congr 1
      apply List.map_congr_left
      intro r _
      by_cases hr : r < n + k
      · have h4 := ih' r
        have e1 : (x44S n h gs k).1.getD r (Sum.inl false) = Sum.inr r := by
          rw [l2, List.getD_eq_getElem _ _ (by simpa using hr)]
          simp
        rw [e1] at h4
        simp only [hr, ↓reduceIte] at h4 ⊢
        exact h4.2
      · simp only [hr, ↓reduceIte]
        exact List.getD_eq_default _ _ (by omega)
    · simp only [← Nat.add_assoc]
      have := x44ext _ _ [] (Sum.inl true) (fun i => x44dvalue ⟨gs, 0⟩ x i) (n + k) hl ih'
        (by subst h2; exact hh)
      exact this
    · simp only [← Nat.add_assoc]
      have hkj : k = j := by
        apply huniq k hkl
        rcases hops gs[k] (List.getElem_mem hkl) with ho | ho | ho
        · rw [ho] at h3; exact absurd h3 (by simp [x44isNot])
        · rw [ho] at h3; exact absurd h3 (by simp [x44isNot])
        · exact ho
      have := x44ext _ _ [] (Sum.inl false) (fun i => x44dvalue ⟨gs, 0⟩ x i) (n + k) hl ih'
        (by subst hkj; exact hjv)
      exact this
    · simp only [x44drunappend, ← Nat.add_assoc]
      apply x44ext _ _ _ _ (fun i => x44dvalue ⟨gs, 0⟩ x i) (n + k) hl ih'
      have hop : gs[k].op = GateOp.and ∨ gs[k].op = GateOp.or := by
        rcases hops gs[k] (List.getElem_mem hkl) with ho | ho | ho
        · exact Or.inl ho
        · exact Or.inr ho
        · rw [ho] at h3; exact absurd rfl h3
      change x44Rp _ (x44dvalue ⟨gs, 0⟩ x (n + k)) _
      rw [hgv, ← hWl]
      exact x44gen_sem _ _ gs[k] hop _ (fun r _ => ih' r)


lemma x44topo_append (n : ℕ) (G e : List Gate)
    (hG : ∀ (i : ℕ) (g : Gate), G[i]? = some g → ∀ w ∈ g.inputs, w < n + i)
    (he : ∀ g' ∈ e, ∀ w ∈ g'.inputs, w < n + G.length) :
    ∀ (i : ℕ) (g : Gate), (G ++ e)[i]? = some g → ∀ w ∈ g.inputs, w < n + i := by
  intro i g hgi w hw
  by_cases hlt : i < G.length
  · rw [List.getElem?_append_left hlt] at hgi
    exact hG i g hgi w hw
  · rw [List.getElem?_append_right (by omega)] at hgi
    have hmem : g ∈ e := by
      obtain ⟨hh, hgg⟩ := List.getElem?_eq_some_iff.mp hgi
      rw [← hgg]
      exact List.getElem_mem hh
    have := he g hmem w hw
    omega

lemma x44fin3_topo (a : Bool) (op : GateOp) (M : ℕ) (l : List ℕ) (hl : ∀ w ∈ l, w < M) :
    (∀ w, (x44fin3 a op M l).1 = Sum.inr w → w < M + (x44fin3 a op M l).2.length) ∧
    (∀ g' ∈ (x44fin3 a op M l).2, ∀ w ∈ g'.inputs, w < M) := by
  rcases l with _ | ⟨w, _ | ⟨w2, t⟩⟩
  · refine ⟨fun w' hw => ?_, fun g' hg' => ?_⟩
    · change (Sum.inl (!a) : Bool ⊕ ℕ) = Sum.inr w' at hw
      cases hw
    · change g' ∈ ([] : List Gate) at hg'
      cases hg'
  · refine ⟨fun w' hw => ?_, fun g' hg' => ?_⟩
    · change (Sum.inr w : Bool ⊕ ℕ) = Sum.inr w' at hw
      have e : w = w' := Sum.inr.inj hw
      have h1 := hl w (List.mem_singleton.mpr rfl)
      change w' < M + 0
      omega
    · change g' ∈ ([] : List Gate) at hg'
      cases hg'
  · refine ⟨fun w' hw => ?_, fun g' hg' => ?_⟩
    · change (Sum.inr M : Bool ⊕ ℕ) = Sum.inr w' at hw
      have e : M = w' := Sum.inr.inj hw
      change w' < M + 1
      omega
    · change g' ∈ [(⟨op, w :: w2 :: t⟩ : Gate)] at hg'
      have e : g' = ⟨op, w :: w2 :: t⟩ := List.mem_singleton.mp hg'
      rw [e]
      exact hl

lemma x44gen_topo (ρ : List (Bool ⊕ ℕ)) (M : ℕ) (g : Gate) (hρ : ∀ w, Sum.inr w ∈ ρ → w < M) :
    (∀ w, (x44gen ρ M g).1 = Sum.inr w → w < M + (x44gen ρ M g).2.length) ∧
    (∀ g' ∈ (x44gen ρ M g).2, ∀ w ∈ g'.inputs, w < M) := by
  unfold x44gen
  split_ifs
  · refine ⟨fun w hw => ?_, fun g' hg' => ?_⟩
    · exact absurd hw (by simp)
    · change g' ∈ ([] : List Gate) at hg'
      cases hg'
  · apply x44fin3_topo
    intro w hw
    obtain ⟨c, hc, hcw⟩ := List.mem_filterMap.mp hw
    obtain ⟨r, _, hr⟩ := List.mem_map.mp hc
    have hr' : ρ.getD r (Sum.inl false) = c := hr
    have hc2 : c = Sum.inr w := by
      rcases c with b | w'
      · simp at hcw
      · have e : some w' = some w := hcw
        rw [Option.some.inj e]
    apply hρ
    by_cases hrl : r < ρ.length
    · rw [List.getD_eq_getElem _ _ hrl] at hr'
      rw [← hc2, ← hr']
      exact List.getElem_mem hrl
    · rw [List.getD_eq_default _ _ (by omega)] at hr'
      rw [hc2] at hr'
      cases hr'

lemma x44S_topo (n h : ℕ) (gs : List Gate)
    (htop : ∀ (i : Fin gs.length), ∀ w ∈ (gs.get i).inputs, w < n + (i : ℕ)) :
    ∀ k, k ≤ gs.length →
      (∀ w, Sum.inr w ∈ (x44S n h gs k).1 → w < n + (x44S n h gs k).2.length) ∧
      (∀ (i : ℕ) (g : Gate), (x44S n h gs k).2[i]? = some g → ∀ w ∈ g.inputs, w < n + i) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨fun w hw => ?_, fun i g hgi => ?_⟩
    · have hw' : Sum.inr w ∈ (List.range n).map (Sum.inr : ℕ → Bool ⊕ ℕ) := hw
      obtain ⟨a, ha, e⟩ := List.mem_map.mp hw'
      have h1 := List.mem_range.mp ha
      have e' : a = w := Sum.inr.inj e
      omega
    · have hgi' : ([] : List Gate)[i]? = some g := hgi
      simp at hgi'
  | succ k ih =>
    intro hk
    have hkl : k < gs.length := by omega
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    rw [x44S_succ n h gs k hkl]
    unfold x44stp
    split_ifs with h1 h2 h3
    · have hlow := (x44S_low n h gs k (by omega) (by omega)).1
      have hlen : (x44S n h gs k).2.length = k := by
        rw [hlow, List.length_take]
        omega
      refine ⟨fun w hw => ?_, x44topo_append n _ _ ih2 ?_⟩
      · have hw' : Sum.inr w ∈ (x44S n h gs k).1 ++ [(Sum.inr (n + (x44S n h gs k).2.length) : Bool ⊕ ℕ)] := hw
        change w < n + ((x44S n h gs k).2 ++ [gs[k]]).length
        rw [List.length_append, List.length_singleton]
        rcases List.mem_append.mp hw' with hm | hm
        · have := ih1 w hm
          omega
        · have e : (Sum.inr w : Bool ⊕ ℕ) = Sum.inr (n + (x44S n h gs k).2.length) :=
            List.mem_singleton.mp hm
          have e' := Sum.inr.inj e
          omega
      · intro g' hg' w hw
        rw [List.mem_singleton.mp hg'] at hw
        have := htop ⟨k, hkl⟩ w hw
        have hk' : ((⟨k, hkl⟩ : Fin gs.length) : ℕ) = k := rfl
        omega
    · refine ⟨fun w hw => ?_, ih2⟩
      have hw' : Sum.inr w ∈ (x44S n h gs k).1 ++ [(Sum.inl true : Bool ⊕ ℕ)] := hw
      rcases List.mem_append.mp hw' with hm | hm
      · exact ih1 w hm
      · have e : (Sum.inr w : Bool ⊕ ℕ) = Sum.inl true := List.mem_singleton.mp hm
        cases e
    · refine ⟨fun w hw => ?_, ih2⟩
      have hw' : Sum.inr w ∈ (x44S n h gs k).1 ++ [(Sum.inl false : Bool ⊕ ℕ)] := hw
      rcases List.mem_append.mp hw' with hm | hm
      · exact ih1 w hm
      · have e : (Sum.inr w : Bool ⊕ ℕ) = Sum.inl false := List.mem_singleton.mp hm
        cases e
    · obtain ⟨g1, g2⟩ := x44gen_topo (x44S n h gs k).1 (n + (x44S n h gs k).2.length) gs[k] ih1
      refine ⟨fun w hw => ?_, x44topo_append n _ _ ih2 g2⟩
      have hw' : Sum.inr w ∈ (x44S n h gs k).1 ++ [(x44gen (x44S n h gs k).1 (n + (x44S n h gs k).2.length) gs[k]).1] := hw
      change w < n + ((x44S n h gs k).2 ++ (x44gen (x44S n h gs k).1 (n + (x44S n h gs k).2.length) gs[k]).2).length
      rw [List.length_append]
      rcases List.mem_append.mp hw' with hm | hm
      · have := ih1 w hm
        omega
      · have e := List.mem_singleton.mp hm
        have := g1 w e.symm
        omega

lemma x44dmain : ∀ (n m : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (j h : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < n + (i : ℕ)) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (n + (h : ℕ)) :: r) →
    (∀ w : Fin m, ∃ x y : Fin n → Bool,
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (h : ℕ)⟩ (List.ofFn x) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (h : ℕ)⟩ (List.ofFn y) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn y) = false) →
    ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (out' : Fin m → ℕ),
      (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      (∀ (i : ℕ) (g : Gate), gates'[i]? = some g → ∀ w ∈ g.inputs, w < n + i) ∧
      gates.take (h : ℕ) <+: gates' ∧
      gates'.length + (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)).card + 2
        ≤ gates.length ∧
      ∀ (w : Fin m) (x : Fin n → Bool),
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (h : ℕ)⟩ (List.ofFn x) = true →
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', out' w⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) := by
  intro n m gates out j h hops htop hj huniq hhj hin hsep
  have hjl : (j : ℕ) < gates.length := j.2
  have hhj' : (h : ℕ) < (j : ℕ) := hhj
  have hjn : gates[(j : ℕ)].op = GateOp.not := hj
  have huniq' : ∀ i (hi : i < gates.length), gates[i].op = GateOp.not → i = (j : ℕ) :=
    fun i hi ho => congrArg Fin.val (huniq ⟨i, hi⟩ ho)
  have hops1 : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not :=
    fun g hg => (hops g hg).1
  have hlen : ∀ g ∈ gates, g.inputs.length ≤ 2 := fun g hg => (hops g hg).2
  have hjv : ∀ x : Fin n → Bool, x44dvalue ⟨gates, 0⟩ x (n + (h : ℕ)) = true →
      x44dvalue ⟨gates, 0⟩ x (n + (j : ℕ)) = false := by
    intro x hx
    obtain ⟨r, hr⟩ := hin
    have hr' : gates[(j : ℕ)].inputs = (n + (h : ℕ)) :: r := hr
    rw [x44dgatevalueP gates x j hjl, hjn, hr']
    have : n + (h : ℕ) < n + (j : ℕ) := by omega
    simp [GateOp.eval, this, hx]
  have hsem := fun (x : Fin n → Bool) (hx : x44dvalue ⟨gates, 0⟩ x (n + (h : ℕ)) = true) =>
    x44sem n h j gates x hops1 huniq' hx (hjv x hx) gates.length le_rfl
  have hSl := x44S_len n h gates gates.length le_rfl
  refine ⟨(x44S n h gates gates.length).2,
    fun w => ((x44S n h gates gates.length).1.getD (out w) (Sum.inl false)).elim (fun _ => 0) id,
    x44S_ops n h j gates hhj' hops huniq' gates.length le_rfl,
    (x44S_topo n h gates htop gates.length le_rfl).2,
    x44S_prefix n h gates gates.length le_rfl (by omega), ?_, ?_⟩
  · have hc := x44S_count n h j gates hhj' hjl hjn hlen gates.length le_rfl
    have hsub : insert (h : ℕ) (insert (j : ℕ)
        ((Finset.univ.filter (fun i : Fin gates.length =>
          j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)).image (fun i : Fin gates.length => (i : ℕ)))) ⊆
        (Finset.range gates.length).filter (fun i => x44bad n h j gates i = true) := by
      intro i hi
      rw [Finset.mem_filter, Finset.mem_range]
      unfold x44bad
      simp only [decide_eq_true_eq]
      rcases Finset.mem_insert.mp hi with hi | hi
      · exact ⟨by omega, Or.inl hi⟩
      rcases Finset.mem_insert.mp hi with hi | hi
      · exact ⟨by omega, Or.inr (Or.inl hi)⟩
      obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨_, a, b⟩ := Finset.mem_filter.mp hi'
      refine ⟨i'.2, Or.inr (Or.inr ⟨a, ?_⟩)⟩
      rw [List.getD_eq_getElem _ _ i'.2]
      exact b
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_image_of_injective _ Fin.val_injective] at hcard
    · omega
    · intro hm
      obtain ⟨i', hi', he⟩ := Finset.mem_image.mp hm
      have := (Finset.mem_filter.mp hi').2.1
      have : (j : ℕ) < (i' : ℕ) := this
      omega
    · intro hm
      rcases Finset.mem_insert.mp hm with hm | hm
      · omega
      · obtain ⟨i', hi', he⟩ := Finset.mem_image.mp hm
        have := (Finset.mem_filter.mp hi').2.1
        have : (j : ℕ) < (i' : ℕ) := this
        omega
  · intro w x hx
    have hx' : x44dvalue ⟨gates, 0⟩ x (n + (h : ℕ)) = true := hx
    obtain ⟨x0, y0, hx0, hy0, ox, oy⟩ := hsep w
    have ox' : x44dvalue ⟨gates, 0⟩ x0 (out w) = true := ox
    have oy' : x44dvalue ⟨gates, 0⟩ y0 (out w) = false := oy
    have a1 := hsem x0 hx0 (out w)
    have a2 := hsem y0 hy0 (out w)
    have a3 := hsem x hx' (out w)
    change (x44drun (x44S n h gates gates.length).2 (List.ofFn x)).getD (Sum.elim (fun _ => 0) id ((x44S n h gates gates.length).1.getD (out w) (Sum.inl false))) false = x44dvalue ⟨gates, 0⟩ x (out w)
    rcases hc : (x44S n h gates gates.length).1.getD (out w) (Sum.inl false) with b | w'
    · rw [hc] at a1 a2
      exfalso
      by_cases hlt : out w < n + gates.length
      · simp only [hlt, ↓reduceIte] at a1 a2
        have e1 : x44dvalue ⟨gates, 0⟩ x0 (out w) = b := a1
        have e2 : x44dvalue ⟨gates, 0⟩ y0 (out w) = b := a2
        rw [ox'] at e1
        rw [oy'] at e2
        rw [← e1] at e2
        exact Bool.noConfusion e2
      · rw [x44dmissingvalue _ x0 (out w) (by change n + gates.length ≤ _; omega)] at ox'
        exact Bool.noConfusion ox'
    · rw [hc] at a3
      by_cases hlt : out w < n + gates.length
      · simp only [hlt, ↓reduceIte] at a3
        exact a3.2
      · simp only [hlt, ↓reduceIte] at a3
        rw [x44dmissingvalue _ x (out w) (by change n + gates.length ≤ _; omega)]
        exact a3.2




open PEqualNP.CircuitLowerBounds

def b_run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma b_run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    b_run (g :: gs) x = b_run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma b_run_length (gs : List Gate) (x : List Bool) :
    (b_run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [b_run]
  | cons g gs ih => rw [b_run_cons, ih]; simp; omega

lemma b_run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (b_run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [b_run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma b_run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    b_run gs x = b_run (gs.drop j) (b_run (gs.take j) x) := by
  simpa only [b_run, List.foldl_append] using
    congrArg (fun l : List Gate => b_run l x) (List.take_append_drop j gs).symm

def b_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma b_input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    b_value C x p = x p := by
  change (b_run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [b_run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma b_missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : b_value C x w = false := by
  change (b_run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [b_run_length, Circuit.size] using hw)

lemma b_gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    b_value C x w = g.op.eval (g.inputs.map fun r => if r < w then b_value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := b_run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, b_run_length, Nat.min_eq_left hj.le, j]; omega
  have split : b_run C.gates (List.ofFn x) = b_run (g :: C.gates.drop (j + 1)) earlier := by
    rw [b_run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then b_value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (b_run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (b_run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (b_run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then b_value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [b_run_cons]
  rw [b_run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma b_gate_mono {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or)
    (x y : Fin n → Bool)
    (h : ∀ r ∈ C.gates[k].inputs, r < n + k → b_value C x r = true → b_value C y r = true) :
    b_value C x (n + k) = true → b_value C y (n + k) = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := b_gate_value C x (n + k) (by omega) hw
  have hy := b_gate_value C y (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx hy
  rw [hx, hy]
  have hr (r : ℕ) (hm : r ∈ C.gates[k].inputs) :
      (if r < n + k then b_value C x r else false) = true →
      (if r < n + k then b_value C y r else false) = true := by
    by_cases h' : r < n + k
    · simpa [h'] using h r hm h'
    · simp [h']
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_eq_true, id_eq]
    intro hx b hb
    obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
    exact hr r hm (hx _ (List.mem_map.mpr ⟨r, hm, rfl⟩))
  · simp only [hop, GateOp.eval, List.any_eq_true, id_eq]
    intro hx
    obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨r, hm, hv⟩ := List.mem_map.mp hb
    exact ⟨_, List.mem_map.mpr ⟨r, hm, rfl⟩, hr r hm hv⟩

lemma b_or_value {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.or) (x : Fin n → Bool) :
    b_value C x (n + k) = true ↔ ∃ r ∈ C.gates[k].inputs, r < n + k ∧ b_value C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := b_gate_value C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx
  rw [hx, hop]
  simp [GateOp.eval]

lemma b_and_value {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and) (x : Fin n → Bool) :
    b_value C x (n + k) = true ↔ ∀ r ∈ C.gates[k].inputs, r < n + k ∧ b_value C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := b_gate_value C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx
  rw [hx, hop]
  simp [GateOp.eval]

lemma b_mono {n : ℕ} (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (h : ∀ v, x v = true → y v = true) (w : ℕ) :
    b_value C x w = true → b_value C y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change b_value C x p = true → b_value C y p = true
      simpa only [b_input_value] using h p
    by_cases hw : w < n + C.gates.length
    · have hk : w - n < C.gates.length := by omega
      have hwk : w = n + (w - n) := by omega
      rw [hwk]
      exact b_gate_mono C (w - n) hk (hC _ (List.getElem_mem hk)).1 x y fun r _ hlt => ih r (by omega)
    · simp [b_missing_value C x w (by unfold Circuit.size; omega)]

lemma b_count {N m q : ℕ} (K : Fin m → Finset (Fin N)) (hq : ∀ i, q ≤ (K i).card)
    (hd : ∀ i j, i ≠ j → Disjoint (K i) (K j)) : m * q ≤ (Finset.univ.biUnion K).card := by
  rw [Finset.card_biUnion (fun i _ j _ hij => hd i j hij)]
  have h2 : ∑ _i : Fin m, q ≤ ∑ i : Fin m, (K i).card := Finset.sum_le_sum fun i _ => hq i
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h2
  exact h2

def r_step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma r_step_len (w : List Bool) (g : Gate) : (r_step w g).length = w.length + 1 := by
  simp [r_step]

lemma r_step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (r_step w g).getD i false = w.getD i false := by
  simp [r_step, List.getD, List.getElem?_append_left hi]

lemma r_step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (r_step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp [r_step, List.getD]

def r_W {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl r_step (List.ofFn x)

lemma r_W_len {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    (r_W gs x).length = n + gs.length := by
  have h : ∀ (gs : List Gate) (w : List Bool), (gs.foldl r_step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih, r_step_len, List.length_cons]
      omega
  rw [r_W, h]
  simp

lemma r_W_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    r_W (gs ++ [g]) x = r_step (r_W gs x) g := by
  simp [r_W, List.foldl_append]

lemma r_W_val {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (t : ℕ) :
    (r_W (gs ++ [g]) x).getD t false =
      if t = n + gs.length then g.op.eval (g.inputs.map fun i => (r_W gs x).getD i false)
      else (r_W gs x).getD t false := by
  rw [r_W_snoc]
  by_cases ht : t = n + gs.length
  · rw [if_pos ht, r_step_last _ _ _ (by rw [r_W_len]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < n + gs.length
    · exact r_step_lt _ _ _ (by rw [r_W_len]; exact hlt)
    · rw [List.getD_eq_default _ _ (by rw [r_step_len, r_W_len]; omega),
        List.getD_eq_default _ _ (by rw [r_W_len]; omega)]

def r_Rep {n : ℕ} (new : List Gate) (f : (Fin n → Bool) → Bool) : Prop :=
  (∃ c : Bool, ∀ x : Fin n → Bool, f x = c) ∨
    (∃ j : ℕ, j < n + new.length ∧ ∀ x : Fin n → Bool, (r_W new x).getD j false = f x)

def r_Fan (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

def r_Ext (n : ℕ) (new new' : List Gate) : Prop :=
  new' = new ∨ ∃ h : Gate, new' = new ++ [h] ∧ r_Fan h ∧ ∀ i ∈ h.inputs, i < n + new.length

lemma r_rep_congr {n : ℕ} {new : List Gate} {f g : (Fin n → Bool) → Bool}
    (h : ∀ x, f x = g x) (hf : r_Rep new f) : r_Rep new g := by
  obtain rfl : f = g := funext h
  exact hf

lemma r_rep_mono {n : ℕ} {new new' : List Gate} (he : r_Ext n new new')
    (f : (Fin n → Bool) → Bool) (h : r_Rep new f) : r_Rep new' f := by
  rcases he with rfl | ⟨k, rfl, _⟩
  · exact h
  · rcases h with hc | ⟨j, hj, hv⟩
    · exact Or.inl hc
    · have hne : ¬ j = n + new.length := by omega
      refine Or.inr ⟨j, by rw [List.length_append, List.length_singleton]; omega, fun x => ?_⟩
      rw [r_W_val, if_neg hne]
      exact hv x

lemma r_rep_and {n : ℕ} (new : List Gate) (f g : (Fin n → Bool) → Bool) (hf : r_Rep new f)
    (hg : r_Rep new g) : ∃ new', r_Ext n new new' ∧ r_Rep new' (fun x => f x && g x) := by
  rcases hf with ⟨c1, h1⟩ | ⟨j, hj, hjv⟩
  · cases c1 with
    | false =>
      exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by
        show (f x && g x) = false
        simp [h1 x]⟩⟩
    | true =>
      exact ⟨new, Or.inl rfl, r_rep_congr (fun x => by
        show g x = (f x && g x)
        simp [h1 x]) hg⟩
  · rcases hg with ⟨c2, h2⟩ | ⟨k, hk, hkv⟩
    · cases c2 with
      | false =>
        exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by
          show (f x && g x) = false
          simp [h2 x]⟩⟩
      | true =>
        exact ⟨new, Or.inl rfl, Or.inr ⟨j, hj, fun x => by
          show (r_W new x).getD j false = (f x && g x)
          rw [hjv x]
          simp [h2 x]⟩⟩
    · refine ⟨new ++ [⟨GateOp.and, [j, k]⟩], Or.inr ⟨_, rfl, ⟨Or.inl rfl, rfl⟩, (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)⟩,
        Or.inr ⟨n + new.length, by rw [List.length_append, List.length_singleton]; omega,
          fun x => ?_⟩⟩
      show (r_W (new ++ [⟨GateOp.and, [j, k]⟩]) x).getD (n + new.length) false = (f x && g x)
      rw [r_W_val, if_pos rfl]
      show GateOp.and.eval [(r_W new x).getD j false, (r_W new x).getD k false] = _
      rw [hjv x, hkv x]
      simp [GateOp.eval]

lemma r_rep_or {n : ℕ} (new : List Gate) (f g : (Fin n → Bool) → Bool) (hf : r_Rep new f)
    (hg : r_Rep new g) : ∃ new', r_Ext n new new' ∧ r_Rep new' (fun x => f x || g x) := by
  rcases hf with ⟨c1, h1⟩ | ⟨j, hj, hjv⟩
  · cases c1 with
    | true =>
      exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by
        show (f x || g x) = true
        simp [h1 x]⟩⟩
    | false =>
      exact ⟨new, Or.inl rfl, r_rep_congr (fun x => by
        show g x = (f x || g x)
        simp [h1 x]) hg⟩
  · rcases hg with ⟨c2, h2⟩ | ⟨k, hk, hkv⟩
    · cases c2 with
      | true =>
        exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by
          show (f x || g x) = true
          simp [h2 x]⟩⟩
      | false =>
        exact ⟨new, Or.inl rfl, Or.inr ⟨j, hj, fun x => by
          show (r_W new x).getD j false = (f x || g x)
          rw [hjv x]
          simp [h2 x]⟩⟩
    · refine ⟨new ++ [⟨GateOp.or, [j, k]⟩], Or.inr ⟨_, rfl, ⟨Or.inr rfl, rfl⟩, (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)⟩,
        Or.inr ⟨n + new.length, by rw [List.length_append, List.length_singleton]; omega,
          fun x => ?_⟩⟩
      show (r_W (new ++ [⟨GateOp.or, [j, k]⟩]) x).getD (n + new.length) false = (f x || g x)
      rw [r_W_val, if_pos rfl]
      show GateOp.or.eval [(r_W new x).getD j false, (r_W new x).getD k false] = _
      rw [hjv x, hkv x]
      simp [GateOp.eval]

lemma r_rep_input {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool)
    (hρ : ∀ i : Fin n, (∃ c : Bool, ∀ x : Fin n → Bool, ρ x i = c) ∨
      (∀ x : Fin n → Bool, ρ x i = x i)) (t : ℕ) :
    r_Rep ([] : List Gate) (fun x => (r_W [] (ρ x)).getD t false) := by
  by_cases ht : t < n
  · have hval : ∀ y : Fin n → Bool, (r_W [] y).getD t false = y ⟨t, ht⟩ := by
      intro y
      show (List.ofFn y).getD t false = _
      rw [List.getD_eq_getElem _ _ (by simpa using ht)]
      simp
    rcases hρ ⟨t, ht⟩ with ⟨c, hc⟩ | hid
    · exact Or.inl ⟨c, fun x => by
        show (r_W [] (ρ x)).getD t false = c
        rw [hval, hc x]⟩
    · exact Or.inr ⟨t, by simpa using ht, fun x => by
        show (r_W [] x).getD t false = (r_W [] (ρ x)).getD t false
        rw [hval, hval, hid x]⟩
  · exact Or.inl ⟨false, fun x =>
      List.getD_eq_default _ _ (by rw [r_W_len, List.length_nil]; omega)⟩

lemma r_gate_rep {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old new : List Gate)
    (op : GateOp) (l : List ℕ) (hop : op = GateOp.and ∨ op = GateOp.or) (hlen : l.length ≤ 2)
    (h : ∀ t : ℕ, r_Rep new (fun x => (r_W old (ρ x)).getD t false)) :
    ∃ new', r_Ext n new new' ∧
      r_Rep new' (fun x => op.eval (l.map fun i => (r_W old (ρ x)).getD i false)) := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c3, rest⟩⟩⟩
  · rcases hop with rfl | rfl
    · exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by simp [GateOp.eval]⟩⟩
    · exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by simp [GateOp.eval]⟩⟩
  · rcases hop with rfl | rfl
    · exact ⟨new, Or.inl rfl, r_rep_congr (fun x => by simp [GateOp.eval]) (h a)⟩
    · exact ⟨new, Or.inl rfl, r_rep_congr (fun x => by simp [GateOp.eval]) (h a)⟩
  · rcases hop with rfl | rfl
    · obtain ⟨new', he, hr⟩ := r_rep_and new _ _ (h a) (h b)
      exact ⟨new', he, r_rep_congr (fun x => by simp [GateOp.eval]) hr⟩
    · obtain ⟨new', he, hr⟩ := r_rep_or new _ _ (h a) (h b)
      exact ⟨new', he, r_rep_congr (fun x => by simp [GateOp.eval]) hr⟩
  · simp only [List.length_cons] at hlen
    omega

def r_RB (n : ℕ) (new : List Gate) : Prop :=
  ∀ j < new.length, ∀ i ∈ (new.getD j ⟨GateOp.or, []⟩).inputs, i < n + j

lemma r_rb_snoc {n : ℕ} {new : List Gate} {h : Gate} (hrb : r_RB n new)
    (hh : ∀ i ∈ h.inputs, i < n + new.length) : r_RB n (new ++ [h]) := by
  intro j hj i hi
  rw [List.length_append, List.length_singleton] at hj
  by_cases hlt : j < new.length
  · have e : (new ++ [h]).getD j ⟨GateOp.or, []⟩ = new.getD j ⟨GateOp.or, []⟩ := by
      simp [List.getD, List.getElem?_append_left hlt]
    rw [e] at hi
    exact hrb j hlt i hi
  · have hj' : j = new.length := by omega
    subst hj'
    have e : (new ++ [h]).getD new.length ⟨GateOp.or, []⟩ = h := by simp [List.getD]
    rw [e] at hi
    exact hh i hi

def r_Inv {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old : List Gate) : Prop :=
  ∃ new : List Gate, (∀ g ∈ new, r_Fan g) ∧ r_RB n new ∧ new.length ≤ old.length ∧
    ∀ t : ℕ, r_Rep new (fun x => (r_W old (ρ x)).getD t false)

lemma r_inv_step {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old : List Gate) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length ≤ 2)
    (h : r_Inv ρ old) : r_Inv ρ (old ++ [g]) := by
  obtain ⟨new, hfan, hrb, hl, hrep⟩ := h
  obtain ⟨new', he, hr⟩ := r_gate_rep ρ old new g.op g.inputs hop hlen hrep
  refine ⟨new', ?_, ?_, ?_, ?_⟩
  · rcases he with rfl | ⟨k, rfl, hk, _⟩
    · exact hfan
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hfan q hq
      · rw [List.mem_singleton] at hq
        rw [hq]
        exact hk
  · rcases he with rfl | ⟨k, rfl, _, hkb⟩
    · exact hrb
    · exact r_rb_snoc hrb hkb
  · rcases he with rfl | ⟨k, rfl, hk, _⟩
    · rw [List.length_append, List.length_singleton]
      omega
    · rw [List.length_append, List.length_append, List.length_singleton, List.length_singleton]
      omega
  · intro t
    by_cases ht : t = n + old.length
    · exact r_rep_congr (fun x => by
        show _ = (r_W (old ++ [g]) (ρ x)).getD t false
        rw [r_W_val, if_pos ht]) hr
    · exact r_rep_congr (fun x => by
        show _ = (r_W (old ++ [g]) (ρ x)).getD t false
        rw [r_W_val, if_neg ht]) (r_rep_mono he _ (hrep t))

lemma r_inv_all {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool)
    (hρ : ∀ i : Fin n, (∃ c : Bool, ∀ x : Fin n → Bool, ρ x i = c) ∨
      (∀ x : Fin n → Bool, ρ x i = x i)) (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    r_Inv ρ gates := by
  have hall : ∀ (post pre : List Gate), pre ++ post = gates → r_Inv ρ pre → r_Inv ρ gates := by
    intro post
    induction post with
    | nil =>
      intro pre h hinv
      rw [List.append_nil] at h
      rw [← h]
      exact hinv
    | cons g post ih =>
      intro pre h hinv
      have hmem : g ∈ gates := by
        rw [← h]
        simp
      exact ih (pre ++ [g]) (by rw [List.append_assoc]; exact h)
        (r_inv_step ρ pre g (hg g hmem).1 (hg g hmem).2 hinv)
  exact hall gates [] (List.nil_append _)
    ⟨[], by simp, (by intro j hj; simp at hj), le_refl _, r_rep_input ρ hρ⟩

lemma r_eval_eq {n : ℕ} (gs : List Gate) (o : ℕ) (x : Fin n → Bool) :
    Circuit.eval ⟨gs, o⟩ (List.ofFn x) = (r_W gs x).getD o false := rfl

theorem p33_main_aux : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ T : Fin N → Fin N → Fin N → Bool,
    (∀ (t p v : Fin N), T t p v = true ↔ (v = p ∨ (p0 ∉ L t ∧ p ≠ p1 ∧ v = p0) ∨ (p0 ∈ L t ∧ p1 ∉ L t ∧ p ≠ p0 ∧ v = p1) ∨
      (p0 ∈ L t ∧ p1 ∈ L t ∧ p ≠ p0 ∧ p ≠ p1 ∧ v ∉ L t))) →
    ∀ t u : Fin N, t ≠ i0 → u ≠ i0 → t ≠ u →
      ((∃ p ∈ L t \ L u, ∃ v ∈ L u, T t p v = true) ∧ (∃ p ∈ L u \ L t, ∃ v ∈ L t, T u p v = true) ↔ ((p0 ∈ L t ∧ p1 ∉ L t) ∧ (p1 ∈ L u ∧ p0 ∉ L u)) ∨ ((p1 ∈ L t ∧ p0 ∉ L t) ∧ (p0 ∈ L u ∧ p1 ∉ L u))) := by
  intro q N L i0 p0 p1 hq hN hcard hint hjoin h01 h0 h1 T hT t u ht hu htu
  have key : ∀ a : Fin N, a ≠ i0 → ¬ (p0 ∈ L a ∧ p1 ∈ L a) := by
    intro a ha hh
    have h := hint a i0 ha
    have hsub : ({p0, p1} : Finset (Fin N)) ⊆ L a ∩ L i0 := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_inter]
      rcases hx with hx | hx
      · rw [hx]; exact ⟨hh.1, h0⟩
      · rw [hx]; exact ⟨hh.2, h1⟩
    have h2 := Finset.card_le_card hsub
    rw [Finset.card_pair h01, h] at h2
    omega
  have ex : ∀ a b : Fin N, a ≠ b → ∀ x : Fin N, ∃ p ∈ L a \ L b, p ≠ x := by
    intro a b hab x
    have h3 := Finset.card_sdiff_add_card_inter (L a) (L b)
    rw [hint a b hab, hcard a] at h3
    exact Finset.exists_mem_ne (by omega) x
  have kt := key t ht
  have ku := key u hu
  constructor
  · rintro ⟨⟨p, hp, v, hv, hTt⟩, ⟨p', hp', v', hv', hTu⟩⟩
    rw [hT] at hTt hTu
    rw [Finset.mem_sdiff] at hp hp'
    have A : (p0 ∉ L t ∧ p0 ∈ L u) ∨ (p0 ∈ L t ∧ p1 ∉ L t ∧ p1 ∈ L u) := by
      rcases hTt with h | ⟨a, b, h⟩ | ⟨a, b, c, h⟩ | ⟨a, b, _⟩
      · rw [h] at hv; exact absurd hv hp.2
      · rw [h] at hv; exact Or.inl ⟨a, hv⟩
      · rw [h] at hv; exact Or.inr ⟨a, b, hv⟩
      · exact absurd ⟨a, b⟩ kt
    have B : (p0 ∉ L u ∧ p0 ∈ L t) ∨ (p0 ∈ L u ∧ p1 ∉ L u ∧ p1 ∈ L t) := by
      rcases hTu with h | ⟨a, b, h⟩ | ⟨a, b, c, h⟩ | ⟨a, b, _⟩
      · rw [h] at hv'; exact absurd hv' hp'.2
      · rw [h] at hv'; exact Or.inl ⟨a, hv'⟩
      · rw [h] at hv'; exact Or.inr ⟨a, b, hv'⟩
      · exact absurd ⟨a, b⟩ ku
    rcases A with ⟨a1, a2⟩ | ⟨a1, a2, a3⟩
    · rcases B with ⟨b1, b2⟩ | ⟨b1, b2, b3⟩
      · exact absurd b2 a1
      · exact Or.inr ⟨⟨b3, a1⟩, ⟨b1, b2⟩⟩
    · rcases B with ⟨b1, b2⟩ | ⟨b1, b2, b3⟩
      · exact Or.inl ⟨⟨a1, a2⟩, ⟨a3, b1⟩⟩
      · exact absurd a3 b2
  · rintro (⟨⟨a, b⟩, ⟨c, d⟩⟩ | ⟨⟨a, b⟩, ⟨c, d⟩⟩)
    · obtain ⟨p, hp, hpn⟩ := ex t u htu p0
      obtain ⟨p', hp', hpn'⟩ := ex u t (Ne.symm htu) p1
      refine ⟨⟨p, hp, p1, c, ?_⟩, ⟨p', hp', p0, a, ?_⟩⟩
      · rw [hT]; exact Or.inr (Or.inr (Or.inl ⟨a, b, hpn, rfl⟩))
      · rw [hT]; exact Or.inr (Or.inl ⟨d, hpn', rfl⟩)
    · obtain ⟨p, hp, hpn⟩ := ex t u htu p1
      obtain ⟨p', hp', hpn'⟩ := ex u t (Ne.symm htu) p0
      refine ⟨⟨p, hp, p0, c, ?_⟩, ⟨p', hp', p1, a, ?_⟩⟩
      · rw [hT]; exact Or.inr (Or.inl ⟨b, hpn, rfl⟩)
      · rw [hT]; exact Or.inr (Or.inr (Or.inl ⟨c, d, hpn', rfl⟩))

def p34_step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma p34_step_len (w : List Bool) (g : Gate) : (p34_step w g).length = w.length + 1 := by
  simp [p34_step]

lemma p34_step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (p34_step w g).getD i false = w.getD i false := by
  simp [p34_step, List.getD, List.getElem?_append_left hi]

lemma p34_step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (p34_step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp [p34_step, List.getD]

def p34_W {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl p34_step (List.ofFn x)

lemma p34_W_len {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    (p34_W gs x).length = n + gs.length := by
  have h : ∀ (gs : List Gate) (w : List Bool), (gs.foldl p34_step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih, p34_step_len, List.length_cons]
      omega
  rw [p34_W, h]
  simp

lemma p34_W_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    p34_W (gs ++ [g]) x = p34_step (p34_W gs x) g := by
  simp [p34_W, List.foldl_append]

lemma p34_W_val {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (t : ℕ) :
    (p34_W (gs ++ [g]) x).getD t false =
      if t = n + gs.length then g.op.eval (g.inputs.map fun i => (p34_W gs x).getD i false)
      else (p34_W gs x).getD t false := by
  rw [p34_W_snoc]
  by_cases ht : t = n + gs.length
  · rw [if_pos ht, p34_step_last _ _ _ (by rw [p34_W_len]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < n + gs.length
    · exact p34_step_lt _ _ _ (by rw [p34_W_len]; exact hlt)
    · rw [List.getD_eq_default _ _ (by rw [p34_step_len, p34_W_len]; omega),
        List.getD_eq_default _ _ (by rw [p34_W_len]; omega)]

lemma p34_all_true (l : List ℕ) (f : ℕ → Bool) :
    (l.map f).all id = true ↔ ∀ i ∈ l, f i = true := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

lemma p34_any_true (l : List ℕ) (f : ℕ → Bool) :
    (l.map f).any id = true ↔ ∃ i ∈ l, f i = true := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

lemma p34_ofFn_getD_true {n : ℕ} (x : Fin n → Bool) (t : ℕ)
    (h : (List.ofFn x).getD t false = true) : ∃ ht : t < n, x ⟨t, ht⟩ = true := by
  by_cases ht : t < n
  · refine ⟨ht, ?_⟩
    rw [List.getD_eq_getElem _ _ (by simpa using ht)] at h
    simpa using h
  · rw [List.getD_eq_default _ _ (by simpa using ht)] at h
    exact Bool.noConfusion h

lemma p34_ofFn_getD_val {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

def p34_Mono {n : ℕ} (gs : List Gate) : Prop :=
  ∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) →
    ∀ t, (p34_W gs x).getD t false = true → (p34_W gs y).getD t false = true

lemma p34_mono_nil {n : ℕ} : p34_Mono (n := n) [] := by
  intro x y hxy t ht
  obtain ⟨hlt, hx⟩ := p34_ofFn_getD_true x t ht
  exact (p34_ofFn_getD_val y ⟨t, hlt⟩).trans (hxy _ hx)

lemma p34_mono_step {n : ℕ} (gs : List Gate) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (h : p34_Mono (n := n) gs) :
    p34_Mono (n := n) (gs ++ [g]) := by
  intro x y hxy t ht
  rw [p34_W_val] at ht ⊢
  by_cases htt : t = n + gs.length
  · rw [if_pos htt] at ht ⊢
    rcases hop with hand | hor
    · rw [hand] at ht ⊢
      exact (p34_all_true _ _).mpr (fun i hi => h x y hxy i ((p34_all_true _ _).mp ht i hi))
    · rw [hor] at ht ⊢
      obtain ⟨i, hi, hti⟩ := (p34_any_true _ _).mp ht
      exact (p34_any_true _ _).mpr ⟨i, hi, h x y hxy i hti⟩
  · rw [if_neg htt] at ht ⊢
    exact h x y hxy t ht

lemma p34_mono_all {n : ℕ} (gs : List Gate) :
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) → p34_Mono (n := n) gs := by
  induction gs using List.reverseRecOn with
  | nil => intro _; exact p34_mono_nil
  | append_singleton l a ih =>
    intro h
    exact p34_mono_step l a (h a (by simp)) (ih (fun g hg => h g (by simp [hg])))

lemma p34_eval_mono {n : ℕ} (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true)
    (hx : Circuit.eval ⟨gs, o⟩ (List.ofFn x) = true) :
    Circuit.eval ⟨gs, o⟩ (List.ofFn y) = true :=
  p34_mono_all gs h x y hxy o hx

lemma p34_key {N : ℕ} (L : Fin N → Finset (Fin N))
    (T : Fin N → Fin N → Fin N → Bool) (gates : List Gate)
    (ev : ℕ → (Fin N → Bool) → Bool)
    (hev : ∀ (w : ℕ) (x : Fin N → Bool), ev w x = Circuit.eval ⟨gates, w⟩ (List.ofFn x))
    (w : ℕ) (a b : Fin N)
    (hg : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hcap : (L a ∩ L b).card = 1)
    (hcb : ev w (fun v : Fin N => decide (v ∉ L b)) = false)
    (hw : 2 ≤ ((L a).filter (fun p => ev w (T a p) = true)).card) :
    ∃ p ∈ L a \ L b, ∃ v ∈ L b, T a p v = true := by
  rw [hev] at hcb
  have hwit : ∀ p : Fin N, ev w (T a p) = true → ∃ v ∈ L b, T a p v = true := by
    intro p hp
    rw [hev] at hp
    by_contra hno
    have h2 := p34_eval_mono gates w hg (T a p) (fun v : Fin N => decide (v ∉ L b))
      (fun i hi => by
        rw [decide_eq_true_eq]
        intro hib
        exact hno ⟨i, hib, hi⟩) hp
    exact Bool.noConfusion (h2.symm.trans hcb)
  obtain ⟨p, hp, r, hr, hpr⟩ := Finset.one_lt_card.mp (Nat.lt_of_lt_of_le Nat.one_lt_two hw)
  rw [Finset.mem_filter] at hp hr
  by_cases hpb : p ∈ L b
  · have hrb : r ∉ L b := by
      intro hrb
      exact hpr (Finset.card_le_one.mp (le_of_eq hcap) p (Finset.mem_inter.mpr ⟨hp.1, hpb⟩) r
        (Finset.mem_inter.mpr ⟨hr.1, hrb⟩))
    exact ⟨r, Finset.mem_sdiff.mpr ⟨hr.1, hrb⟩, hwit r hr.2⟩
  · exact ⟨p, Finset.mem_sdiff.mpr ⟨hp.1, hpb⟩, hwit p hp.2⟩

theorem p34_main_aux : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ T : Fin N → Fin N → Fin N → Bool,
    (∀ (t p v : Fin N), T t p v = true ↔ (v = p ∨ (p0 ∉ L t ∧ p ≠ p1 ∧ v = p0) ∨ (p0 ∈ L t ∧ p1 ∉ L t ∧ p ≠ p0 ∧ v = p1) ∨
      (p0 ∈ L t ∧ p1 ∈ L t ∧ p ≠ p0 ∧ p ≠ p1 ∧ v ∉ L t))) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
    (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ∀ (w : ℕ) (t u : Fin N), t ≠ u → ev w (fun v : Fin N => decide (v ∉ L t)) = false → ev w (fun v : Fin N => decide (v ∉ L u)) = false →
      2 ≤ ((L t).filter (fun p => ev w (T t p) = true)).card → 2 ≤ ((L u).filter (fun p => ev w (T u p) = true)).card →
      (∃ p ∈ L t \ L u, ∃ v ∈ L u, T t p v = true) ∧ (∃ p ∈ L u \ L t, ∃ v ∈ L t, T u p v = true) := by
  intro q N L i0 p0 p1 hq hN hcard hcap hjoin h01 h0 h1 T hT gates hg hin hwire ev hev w t u htu hct hcu hwt hwu
  exact ⟨p34_key L T gates ev hev w t u (fun g hgm => (hg g hgm).1) (hcap t u htu) hcu hwt,
    p34_key L T gates ev hev w u t (fun g hgm => (hg g hgm).1) (hcap u t (Ne.symm htu)) hct hwu⟩

def p35_wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem p35_eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (p35_wf gs x).getD o false := rfl

theorem p35_wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    p35_wf (gs ++ [g]) w = p35_wf gs w ++ [g.op.eval (g.inputs.map fun i => (p35_wf gs w).getD i false)] := by
  simp [p35_wf, List.foldl_append]

theorem p35_wf_len (gs : List Gate) : ∀ w : List Bool, (p35_wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [p35_wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [p35_wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem p35_wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (p35_wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [p35_wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem p35_wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (p35_wf (pre ++ post) w).getD i false = (p35_wf pre w).getD i false := by
  have : p35_wf (pre ++ post) w = p35_wf post (p35_wf pre w) := by simp [p35_wf, List.foldl_append]
  rw [this]
  exact p35_wf_keep post _ i (by rw [p35_wf_len]; exact hi)

theorem p35_getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem p35_getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem p35_getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega


theorem p35_wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (p35_wf gates X).getD i false = (p35_wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact p35_wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem p35_gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (p35_wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (p35_wf (gates.take k) X).getD i false) := by
  rw [p35_wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, p35_wf_snoc]
  have := p35_getD_snoc_eq (p35_wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (p35_wf (gates.take k) X).getD i false))
  rw [p35_wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

def p35_val (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (p35_wf gates (List.ofFn x)).getD w false

theorem p35_iv_eq (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gates.length)
    (i : ℕ) : (p35_wf (gates.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ p35_val gates i x = true := by
  by_cases hi : i < n + k
  · rw [p35_val, p35_wire_take gates (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [p35_wf_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

theorem p35_val_and (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.and) :
    p35_val gates (n + k) x = true ↔ ∀ i ∈ gates[k].inputs, i < n + k ∧ p35_val gates i x = true := by
  have := p35_gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [p35_val, this, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (p35_iv_eq gates x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (p35_iv_eq gates x k (Nat.le_of_lt hk) i).2 (h i hi)

theorem p35_val_or (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.or) :
    p35_val gates (n + k) x = true ↔ ∃ i ∈ gates[k].inputs, i < n + k ∧ p35_val gates i x = true := by
  have := p35_gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [p35_val, this, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (p35_iv_eq gates x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (p35_iv_eq gates x k (Nat.le_of_lt hk) i).2 h⟩

theorem p35_val_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    p35_val gates w x = x ⟨w, hw⟩ := by
  rw [p35_val, p35_wf_keep gates _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem p35_val_big (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : p35_val gates w x = false := by
  rw [p35_val, List.getD_eq_default _ _ (by rw [p35_wf_len]; simpa using hw)]

def p35_Cl {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool) (τ : Fin n → Fin n → Bool)
    (i : Fin gates.length) (X : Finset (Fin n)) : Prop :=
  (gates.get i).op = GateOp.or → p35_val gates (n + (i : ℕ)) c = false →
    ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ M, ∀ y' ∈ M,
      (p35_val gates a (τ y) = true ∨ p35_val gates b (τ y) = true) →
      (p35_val gates a (τ y') = true ∨ p35_val gates b (τ y') = true) → (y ∈ X ↔ y' ∈ X)

def p35_Con {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool) (τ : Fin n → Fin n → Bool)
    (k : ℕ) (X : Finset (Fin n)) : Prop :=
  ∀ i : Fin gates.length, (i : ℕ) < k → p35_Cl gates M c τ i X

def p35_Mrg {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool) (τ : Fin n → Fin n → Bool)
    (g : Fin gates.length) : Prop :=
  (gates.get g).op = GateOp.or ∧ p35_val gates (n + (g : ℕ)) c = false ∧
    ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ M, ∃ r' ∈ M,
      p35_val gates w1 (τ r) = true ∧ p35_val gates w2 (τ r') = true ∧
      ∃ X : Finset (Fin n), r ∈ X ∧ r' ∉ X ∧ p35_Con gates M c τ (g : ℕ) X

theorem p35_single {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool)
    (hc : ∀ v, c v = false → v ∈ M)
    (hτ : ∀ p ∈ M, ∀ v ∈ M, τ p v = true ↔ v = p)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧
      ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (k : ℕ) (hk : k ≤ gates.length) (X : Finset (Fin n)) (hX : p35_Con gates M c τ k X) :
    ∀ w, w < n + k → p35_val gates w c = false → ∀ y ∈ M, ∀ y' ∈ M,
      p35_val gates w (τ y) = true → p35_val gates w (τ y') = true → (y ∈ X ↔ y' ∈ X) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hwc y hy y' hy' h1 h2
    by_cases hwn : w < n
    · rw [p35_val_input gates _ w hwn] at hwc h1 h2
      have hm := hc _ hwc
      have e1 := (hτ y hy _ hm).1 h1
      have e2 := (hτ y' hy' _ hm).1 h2
      rw [← e1, ← e2]
    · have hi : w - n < gates.length := by omega
      have he : n + (w - n) = w := by omega
      rw [← he] at hwc h1 h2
      have hinp : 1 ≤ gates[w - n].inputs.length ∧ ∀ a ∈ gates[w - n].inputs, a < n + (w - n) :=
        hin ⟨w - n, hi⟩
      have hlen := (legal gates[w - n] (List.getElem_mem hi)).2
      rcases (legal gates[w - n] (List.getElem_mem hi)).1 with ha | ho
      · have hex : ∃ j ∈ gates[w - n].inputs, p35_val gates j c = false := by
          by_contra hne
          have hall : p35_val gates (n + (w - n)) c = true := by
            apply (p35_val_and gates c (w - n) hi ha).2
            intro j hj
            refine ⟨hinp.2 j hj, ?_⟩
            cases hv : p35_val gates j c with
            | true => rfl
            | false => exact absurd ⟨j, hj, hv⟩ hne
          rw [hall] at hwc
          exact Bool.noConfusion hwc
        obtain ⟨j, hj, hjc⟩ := hex
        have hjlt := hinp.2 j hj
        exact ih j (by omega) (by omega) hjc y hy y' hy'
          ((p35_val_and gates (τ y) (w - n) hi ha).1 h1 j hj).2
          ((p35_val_and gates (τ y') (w - n) hi ha).1 h2 j hj).2
      · have hall : ∀ j ∈ gates[w - n].inputs, p35_val gates j c = false := by
          intro j hj
          cases hv : p35_val gates j c with
          | false => rfl
          | true =>
            have ht : p35_val gates (n + (w - n)) c = true :=
              (p35_val_or gates c (w - n) hi ho).2 ⟨j, hj, hinp.2 j hj, hv⟩
            rw [ht] at hwc
            exact Bool.noConfusion hwc
        obtain ⟨j1, hj1, _, hv1⟩ := (p35_val_or gates (τ y) (w - n) hi ho).1 h1
        obtain ⟨j2, hj2, _, hv2⟩ := (p35_val_or gates (τ y') (w - n) hi ho).1 h2
        rcases hinpe : gates[w - n].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
        · rw [hinpe] at hj1
          simp at hj1
        · rw [hinpe] at hj1 hj2
          have e1 : j1 = a := by simpa using hj1
          have e2 : j2 = a := by simpa using hj2
          rw [e1] at hv1
          rw [e2] at hv2
          have hjlt := hinp.2 a (by rw [hinpe]; simp)
          exact ih a (by omega) (by omega) (hall a (by rw [hinpe]; simp)) y hy y' hy' hv1 hv2
        · rw [hinpe] at hj1 hj2
          have d1 : p35_val gates a (τ y) = true ∨ p35_val gates b (τ y) = true := by
            rcases List.mem_pair.1 hj1 with e | e
            · subst e; exact Or.inl hv1
            · subst e; exact Or.inr hv1
          have d2 : p35_val gates a (τ y') = true ∨ p35_val gates b (τ y') = true := by
            rcases List.mem_pair.1 hj2 with e | e
            · subst e; exact Or.inl hv2
            · subst e; exact Or.inr hv2
          exact hX ⟨w - n, hi⟩ (by simp; omega) ho hwc a b hinpe y hy y' hy' d1 d2
        · rw [hinpe] at hlen
          simp at hlen

theorem p35_con_succ {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (hk : k < gates.length) (X : Finset (Fin n)) :
    p35_Con gates M c τ (k + 1) X ↔ p35_Con gates M c τ k X ∧ p35_Cl gates M c τ ⟨k, hk⟩ X := by
  constructor
  · intro h
    exact ⟨fun i hi => h i (by omega), h ⟨k, hk⟩ (by simp)⟩
  · rintro ⟨h1, h2⟩ i hi
    by_cases e : (i : ℕ) = k
    · have e' : i = ⟨k, hk⟩ := Fin.ext e
      rw [e']
      exact h2
    · exact h1 i (by omega)

theorem p35_con_compl {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (X : Finset (Fin n)) (h : p35_Con gates M c τ k X) :
    p35_Con gates M c τ k Xᶜ := by
  intro i hi ho hc' a b hab y hy y' hy' h1 h2
  rw [Finset.mem_compl, Finset.mem_compl, not_iff_not]
  exact h i hi ho hc' a b hab y hy y' hy' h1 h2

theorem p35_con_symm {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (X Y : Finset (Fin n)) (hX : p35_Con gates M c τ k X)
    (hY : p35_Con gates M c τ k Y) : p35_Con gates M c τ k (symmDiff X Y) := by
  intro i hi ho hc' a b hab y hy y' hy' h1 h2
  have e1 := hX i hi ho hc' a b hab y hy y' hy' h1 h2
  have e2 := hY i hi ho hc' a b hab y hy y' hy' h1 h2
  rw [Finset.mem_symmDiff, Finset.mem_symmDiff, e1, e2]

theorem p35_con_inter {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (X : Finset (Fin n)) (hX : p35_Con gates M c τ k X) :
    p35_Con gates M c τ k (X ∩ M) := by
  intro i hi ho hc' a b hab y hy y' hy' h1 h2
  have e1 := hX i hi ho hc' a b hab y hy y' hy' h1 h2
  rw [Finset.mem_inter, Finset.mem_inter, e1]
  exact ⟨fun h => ⟨h.1, hy'⟩, fun h => ⟨h.1, hy⟩⟩

theorem p35_cl_of {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (g : Fin gates.length) (X : Finset (Fin n)) (a b : ℕ)
    (hab : (gates.get g).inputs = [a, b])
    (sA : ∀ y ∈ M, ∀ y' ∈ M, p35_val gates a (τ y) = true → p35_val gates a (τ y') = true →
      (y ∈ X ↔ y' ∈ X))
    (sB : ∀ y ∈ M, ∀ y' ∈ M, p35_val gates b (τ y) = true → p35_val gates b (τ y') = true →
      (y ∈ X ↔ y' ∈ X))
    (Q : ∀ y ∈ M, ∀ y' ∈ M, p35_val gates a (τ y) = true → p35_val gates b (τ y') = true →
      (y ∈ X ↔ y' ∈ X)) : p35_Cl gates M c τ g X := by
  intro _ _ a' b' hab' y hy y' hy' h1 h2
  rw [hab] at hab'
  obtain ⟨e1, e2⟩ : a = a' ∧ b = b' := by simpa using hab'
  subst e1
  subst e2
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact sA y hy y' hy' h1 h2
  · exact Q y hy y' hy' h1 h2
  · exact (Q y' hy' y hy h2 h1).symm
  · exact sB y hy y' hy' h1 h2

theorem p35_symm_flip {n : ℕ} (X Y : Finset (Fin n)) (r r' : Fin n) (hr : r ∈ Y) (hr' : r' ∉ Y) :
    (r ∈ symmDiff X Y ↔ r' ∈ symmDiff X Y) ↔ ¬ (r ∈ X ↔ r' ∈ X) := by
  by_cases h1 : r ∈ X <;> by_cases h2 : r' ∈ X <;> simp [Finset.mem_symmDiff, h1, h2, hr, hr']

open Classical in
noncomputable def p35_P {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) : Finset (Finset (Fin n)) :=
  M.powerset.filter (fun X => p35_Con gates M c τ k X)

open Classical in
theorem p35_symm_mem {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (X Y : Finset (Fin n)) (hX : X ∈ p35_P gates M c τ k)
    (hY : Y ⊆ M) (hYc : p35_Con gates M c τ k Y) : symmDiff X Y ∈ p35_P gates M c τ k := by
  rw [p35_P, Finset.mem_filter, Finset.mem_powerset] at hX ⊢
  refine ⟨?_, p35_con_symm gates M c τ k X Y hX.2 hYc⟩
  intro v hv
  rw [Finset.mem_symmDiff] at hv
  rcases hv with hv | hv
  · exact hX.1 hv.1
  · exact hY hv.1

open Classical in
theorem p35_step {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool)
    (hc : ∀ v, c v = false → v ∈ M)
    (hτ : ∀ p ∈ M, ∀ v ∈ M, τ p v = true ↔ v = p)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧
      ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (g : Fin gates.length) :
    (p35_P gates M c τ ((g : ℕ) + 1)).card * (if p35_Mrg gates M c τ g then 2 else 1)
      = (p35_P gates M c τ (g : ℕ)).card := by
  by_cases hal : (gates.get g).op = GateOp.or ∧ p35_val gates (n + (g : ℕ)) c = false ∧
      ∃ a b : ℕ, (gates.get g).inputs = [a, b]
  swap
  · have hnm : ¬ p35_Mrg gates M c τ g := by
      rintro ⟨h1, h2, w1, w2, h3, _⟩
      exact hal ⟨h1, h2, w1, w2, h3⟩
    have hP : p35_P gates M c τ ((g : ℕ) + 1) = p35_P gates M c τ (g : ℕ) := by
      unfold p35_P
      apply Finset.filter_congr
      intro X _
      rw [p35_con_succ gates M c τ g g.2 X]
      constructor
      · exact fun h => h.1
      · intro h
        refine ⟨h, ?_⟩
        intro ho hc' a b hab
        exact absurd ⟨ho, hc', a, b, hab⟩ hal
    rw [hP, if_neg hnm, Nat.mul_one]
  · obtain ⟨ho, hgc, a, b, hab⟩ := hal
    have hma : a ∈ (gates.get g).inputs := by rw [hab]; simp
    have hmb : b ∈ (gates.get g).inputs := by rw [hab]; simp
    have ha : a < n + (g : ℕ) := (hin g).2 a hma
    have hb : b < n + (g : ℕ) := (hin g).2 b hmb
    have hac : p35_val gates a c = false := by
      cases hv : p35_val gates a c with
      | false => rfl
      | true =>
        have ht : p35_val gates (n + (g : ℕ)) c = true :=
          (p35_val_or gates c g g.2 ho).2 ⟨a, hma, ha, hv⟩
        rw [ht] at hgc
        exact Bool.noConfusion hgc
    have hbc : p35_val gates b c = false := by
      cases hv : p35_val gates b c with
      | false => rfl
      | true =>
        have ht : p35_val gates (n + (g : ℕ)) c = true :=
          (p35_val_or gates c g g.2 ho).2 ⟨b, hmb, hb, hv⟩
        rw [ht] at hgc
        exact Bool.noConfusion hgc
    have sA : ∀ X, p35_Con gates M c τ g X → ∀ y ∈ M, ∀ y' ∈ M, p35_val gates a (τ y) = true →
        p35_val gates a (τ y') = true → (y ∈ X ↔ y' ∈ X) := fun X hX =>
      p35_single gates M c τ hc hτ legal hin g (le_of_lt g.2) X hX a ha hac
    have sB : ∀ X, p35_Con gates M c τ g X → ∀ y ∈ M, ∀ y' ∈ M, p35_val gates b (τ y) = true →
        p35_val gates b (τ y') = true → (y ∈ X ↔ y' ∈ X) := fun X hX =>
      p35_single gates M c τ hc hτ legal hin g (le_of_lt g.2) X hX b hb hbc
    by_cases hm : ∃ r ∈ M, ∃ r' ∈ M, p35_val gates a (τ r) = true ∧ p35_val gates b (τ r') = true ∧
        ∃ X : Finset (Fin n), r ∈ X ∧ r' ∉ X ∧ p35_Con gates M c τ (g : ℕ) X
    · have hmrg : p35_Mrg gates M c τ g := ⟨ho, hgc, a, b, hab, hm⟩
      obtain ⟨r, hr, r', hr', hra, hrb, X0, hrX, hr'X, hX0⟩ := hm
      rw [if_pos hmrg]
      have hP : p35_P gates M c τ ((g : ℕ) + 1)
          = (p35_P gates M c τ (g : ℕ)).filter (fun X => r ∈ X ↔ r' ∈ X) := by
        unfold p35_P
        rw [Finset.filter_filter]
        apply Finset.filter_congr
        intro X _
        rw [p35_con_succ gates M c τ g g.2 X]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, h2 ho hgc a b hab r hr r' hr' (Or.inl hra) (Or.inr hrb)⟩
        · rintro ⟨h1, h2⟩
          refine ⟨h1, p35_cl_of gates M c τ g X a b hab (sA X h1) (sB X h1) ?_⟩
          intro y hy y' hy' hya hyb
          exact ((sA X h1 y hy r hr hya hra).trans h2).trans (sB X h1 r' hr' y' hy' hrb hyb)
      rw [hP]
      have hsplit := Finset.card_filter_add_card_filter_not (s := p35_P gates M c τ (g : ℕ))
        (fun X => r ∈ X ↔ r' ∈ X)
      have hY0 : X0 ∩ M ⊆ M := Finset.inter_subset_right
      have hY0c := p35_con_inter gates M c τ g X0 hX0
      have hrY : r ∈ X0 ∩ M := Finset.mem_inter.2 ⟨hrX, hr⟩
      have hr'Y : r' ∉ X0 ∩ M := fun h => hr'X (Finset.mem_inter.1 h).1
      have hbij : ((p35_P gates M c τ (g : ℕ)).filter (fun X => ¬ (r ∈ X ↔ r' ∈ X))).card
          = ((p35_P gates M c τ (g : ℕ)).filter (fun X => r ∈ X ↔ r' ∈ X)).card := by
        refine Finset.card_bij' (fun X _ => symmDiff X (X0 ∩ M)) (fun X _ => symmDiff X (X0 ∩ M))
          ?_ ?_ ?_ ?_
        · intro X hX
          rw [Finset.mem_filter] at hX ⊢
          refine ⟨p35_symm_mem gates M c τ g X _ hX.1 hY0 hY0c, ?_⟩
          exact (p35_symm_flip X (X0 ∩ M) r r' hrY hr'Y).2 hX.2
        · intro X hX
          rw [Finset.mem_filter] at hX ⊢
          refine ⟨p35_symm_mem gates M c τ g X _ hX.1 hY0 hY0c, ?_⟩
          intro hcon
          exact (p35_symm_flip X (X0 ∩ M) r r' hrY hr'Y).1 hcon hX.2
        · intro X _
          exact symmDiff_symmDiff_cancel_right _ _
        · intro X _
          exact symmDiff_symmDiff_cancel_right _ _
      omega
    · have hnm : ¬ p35_Mrg gates M c τ g := by
        rintro ⟨_, _, w1, w2, h3, r, hr, r', hr', h4, h5, h6⟩
        rw [hab] at h3
        obtain ⟨e1, e2⟩ : a = w1 ∧ b = w2 := by simpa using h3
        subst e1
        subst e2
        exact hm ⟨r, hr, r', hr', h4, h5, h6⟩
      rw [if_neg hnm, Nat.mul_one]
      congr 1
      unfold p35_P
      apply Finset.filter_congr
      intro X _
      rw [p35_con_succ gates M c τ g g.2 X]
      constructor
      · exact fun h => h.1
      · intro h
        refine ⟨h, p35_cl_of gates M c τ g X a b hab (sA X h) (sB X h) ?_⟩
        intro y hy y' hy' hya hyb
        constructor
        · intro hyX
          by_contra hn
          exact hm ⟨y, hy, y', hy', hya, hyb, X, hyX, hn, h⟩
        · intro hyX
          by_contra hn
          exact hm ⟨y, hy, y', hy', hya, hyb, Xᶜ, Finset.mem_compl.2 hn,
            fun h' => Finset.mem_compl.1 h' hyX, p35_con_compl gates M c τ g X h⟩

open Classical in
theorem p35_count {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool)
    (hc : ∀ v, c v = false → v ∈ M)
    (hτ : ∀ p ∈ M, ∀ v ∈ M, τ p v = true ↔ v = p)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧
      ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (k : ℕ) (hk : k ≤ gates.length) :
    (p35_P gates M c τ k).card *
      2 ^ (∑ g : Fin gates.length, if (g : ℕ) < k ∧ p35_Mrg gates M c τ g then 1 else 0)
      = 2 ^ M.card := by
  induction k with
  | zero =>
    have h0 : p35_P gates M c τ 0 = M.powerset := by
      unfold p35_P
      apply Finset.filter_true_of_mem
      intro X _ i hi
      exact absurd hi (Nat.not_lt_zero _)
    rw [h0, Finset.card_powerset]
    simp
  | succ k ih =>
    have hk' : k < gates.length := hk
    have hs : (p35_P gates M c τ (k + 1)).card * (if p35_Mrg gates M c τ ⟨k, hk'⟩ then 2 else 1)
        = (p35_P gates M c τ k).card := p35_step gates M c τ hc hτ legal hin ⟨k, hk'⟩
    have hsum : (∑ g : Fin gates.length, if (g : ℕ) < k + 1 ∧ p35_Mrg gates M c τ g then 1 else 0)
        = (∑ g : Fin gates.length, if (g : ℕ) < k ∧ p35_Mrg gates M c τ g then 1 else 0)
          + (if p35_Mrg gates M c τ ⟨k, hk'⟩ then 1 else 0) := by
      have hpt : ∀ g : Fin gates.length,
          (if (g : ℕ) < k + 1 ∧ p35_Mrg gates M c τ g then 1 else 0)
          = (if (g : ℕ) < k ∧ p35_Mrg gates M c τ g then 1 else 0)
            + (if g = ⟨k, hk'⟩ then (if p35_Mrg gates M c τ ⟨k, hk'⟩ then 1 else 0) else 0) := by
        intro g
        by_cases e : g = ⟨k, hk'⟩
        · subst e
          simp
        · have hne : (g : ℕ) ≠ k := fun h => e (Fin.ext h)
          have h2 : ((g : ℕ) < k + 1) ↔ ((g : ℕ) < k) := by omega
          simp [e, h2]
      rw [Finset.sum_congr rfl (fun g _ => hpt g), Finset.sum_add_distrib]
      simp
    rw [hsum, pow_add, ← ih (le_of_lt hk'), ← hs]
    split_ifs <;> ring

open Classical in
theorem p35_qcount {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool)
    (hc : ∀ v, c v = false → v ∈ M)
    (hτ : ∀ p ∈ M, ∀ v ∈ M, τ p v = true ↔ v = p)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧
      ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (q : ℕ) (hM : M.card = q + 1) (o : ℕ) (hoc : p35_val gates o c = false)
    (hot : ∀ p ∈ M, p35_val gates o (τ p) = true)
    (I : Finset (Fin gates.length)) (hI : ∀ g : Fin gates.length, g ∈ I ↔ p35_Mrg gates M c τ g) :
    I.card = q := by
  have hne : M.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨p0, hp0⟩ := hne
  have holt : o < n + gates.length := by
    by_contra h
    have hb := p35_val_big gates (τ p0) o (by omega)
    rw [hot p0 hp0] at hb
    exact Bool.noConfusion hb
  have hfin : p35_P gates M c τ gates.length = {∅, M} := by
    ext X
    rw [p35_P, Finset.mem_filter, Finset.mem_powerset, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hsub, hX⟩
      have hs := p35_single gates M c τ hc hτ legal hin gates.length le_rfl X hX o holt hoc
      by_cases hex : ∃ y ∈ M, y ∈ X
      · obtain ⟨y, hy, hyX⟩ := hex
        right
        apply Finset.Subset.antisymm hsub
        intro z hz
        exact (hs y hy z hz (hot y hy) (hot z hz)).1 hyX
      · left
        apply Finset.eq_empty_of_forall_notMem
        intro z hz
        exact hex ⟨z, hsub hz, hz⟩
    · rintro (e | e)
      · subst e
        refine ⟨Finset.empty_subset _, ?_⟩
        intro i _ _ _ a b _ y _ y' _ _ _
        simp
      · subst e
        refine ⟨Finset.Subset.refl _, ?_⟩
        intro i _ _ _ a b _ y hy y' hy' _ _
        exact ⟨fun _ => hy', fun _ => hy⟩
  have hcnt := p35_count gates M c τ hc hτ legal hin gates.length le_rfl
  have hpair : ({∅, M} : Finset (Finset (Fin n))).card = 2 := by
    apply Finset.card_pair
    intro h
    rw [← h] at hp0
    simp at hp0
  rw [hfin, hM, hpair] at hcnt
  have hsum : (∑ g : Fin gates.length, if (g : ℕ) < gates.length ∧ p35_Mrg gates M c τ g then 1 else 0)
      = ∑ g : Fin gates.length, if p35_Mrg gates M c τ g then 1 else 0 :=
    Finset.sum_congr rfl (fun g _ => by simp [g.2])
  rw [hsum] at hcnt
  have h8 : 2 ^ (∑ g : Fin gates.length, if p35_Mrg gates M c τ g then 1 else 0) = 2 ^ q :=
    Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) (hcnt.trans (by ring))
  have h9 : (∑ g : Fin gates.length, if p35_Mrg gates M c τ g then 1 else 0) = q :=
    Nat.pow_right_injective (le_refl 2) h8
  have hIe : I = Finset.univ.filter (fun g => p35_Mrg gates M c τ g) := by
    ext g
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    exact hI g
  rw [hIe, Finset.card_filter]
  exact h9

theorem p35_main_aux : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ T : Fin N → Fin N → Fin N → Bool,
    (∀ (t p v : Fin N), T t p v = true ↔ (v = p ∨ (p0 ∉ L t ∧ p ≠ p1 ∧ v = p0) ∨ (p0 ∈ L t ∧ p1 ∉ L t ∧ p ≠ p0 ∧ v = p1) ∨
      (p0 ∈ L t ∧ p1 ∈ L t ∧ p ≠ p0 ∧ p ≠ p1 ∧ v ∉ L t))) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
    (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ∀ o : Fin N → ℕ, (∀ (t : Fin N) (x : Fin N → Bool), (x p0 = true ∨ x p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → x u = true) →
      ev (o t) x = decide (∃ v ∈ L t, x v = true)) →
    ∀ Mg : Fin N → Fin gates.length → Prop,
    (∀ (t : Fin N) (g : Fin gates.length), Mg t g ↔ ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ev (N + (g : ℕ)) (fun v : Fin N => decide (v ∉ L t)) = false ∧
        ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ L t, ∃ r' ∈ L t, ev w1 (T t r) = true ∧ ev w2 (T t r') = true ∧
        ∃ X : Finset (Fin N), r ∈ X ∧ r' ∉ X ∧ (∀ i : Fin gates.length, i < g → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ev (N + (i : ℕ)) (fun v : Fin N => decide (v ∉ L t)) = false →
          ∀ c1 c2 : ℕ, (gates.get i).inputs = [c1, c2] → ∀ s ∈ L t, ∀ s' ∈ L t,
          (ev c1 (T t s) = true ∨ ev c2 (T t s) = true) → (ev c1 (T t s') = true ∨ ev c2 (T t s') = true) → (s ∈ X ↔ s' ∈ X)))) →
    ∀ t : Fin N,
      (∀ g : Fin gates.length, ev (N + (g : ℕ)) (fun v : Fin N => decide (v ∉ L t)) = false → ∀ a ∈ L t, ∀ b ∈ L t, ev (N + (g : ℕ)) (T t a) = true → ev (N + (g : ℕ)) (T t b) = true →
        ∀ X : Finset (Fin N), (∀ i : Fin gates.length, i ≤ g → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ev (N + (i : ℕ)) (fun v : Fin N => decide (v ∉ L t)) = false →
          ∀ c1 c2 : ℕ, (gates.get i).inputs = [c1, c2] → ∀ s ∈ L t, ∀ s' ∈ L t,
          (ev c1 (T t s) = true ∨ ev c2 (T t s) = true) → (ev c1 (T t s') = true ∨ ev c2 (T t s') = true) → (s ∈ X ↔ s' ∈ X)) → (a ∈ X ↔ b ∈ X)) ∧
      ∀ I : Finset (Fin gates.length), (∀ g : Fin gates.length, g ∈ I ↔ Mg t g) → I.card = q := by
  intro q N L i0 p0 p1 _ _ hcard hint _ hp01 hp0 hp1 T hT gates legal hlen hwire ev hE o hout Mg hMg t
  have hev : ∀ (w : ℕ) (x : Fin N → Bool), ev w x = p35_val gates w x := fun w x => hE w x
  have hin : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧
      ∀ a ∈ (gates.get i).inputs, a < N + (i : ℕ) := fun i => ⟨hlen i, hwire i⟩
  have hc : ∀ v : Fin N, decide (v ∉ L t) = false → v ∈ L t := by
    intro v hv
    simpa using hv
  have hτ : ∀ p ∈ L t, ∀ v ∈ L t, T t p v = true ↔ v = p := by
    intro p hp v hv
    rw [hT]
    constructor
    · rintro (h | ⟨h, _, e⟩ | ⟨_, h, _, e⟩ | ⟨_, _, _, _, h⟩)
      · exact h
      · rw [e] at hv
        exact absurd hv h
      · rw [e] at hv
        exact absurd hv h
      · exact absurd hv h
    · exact fun h => Or.inl h
  have hline : p0 ∈ L t → p1 ∈ L t → t = i0 := by
    intro h0 h1
    by_contra hne
    have h := hint t i0 hne
    have hsub : ({p0, p1} : Finset (Fin N)) ⊆ L t ∩ L i0 := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with e | e
      · rw [e]
        exact Finset.mem_inter.2 ⟨h0, hp0⟩
      · rw [e]
        exact Finset.mem_inter.2 ⟨h1, hp1⟩
    have h2 := Finset.card_le_card hsub
    rw [Finset.card_pair hp01, h] at h2
    omega
  have hdomc : p35_val gates (o t) (fun v : Fin N => decide (v ∉ L t)) = false := by
    have hd : decide (p0 ∉ L t) = true ∨ decide (p1 ∉ L t) = true ∨
        ∀ u : Fin N, u ∉ L i0 → decide (u ∉ L t) = true := by
      by_cases h0 : p0 ∈ L t
      · by_cases h1 : p1 ∈ L t
        · right
          right
          intro u hu
          have e := hline h0 h1
          rw [e]
          simpa using hu
        · right
          left
          simpa using h1
      · left
        simpa using h0
    have h := hout t (fun v : Fin N => decide (v ∉ L t)) hd
    rw [hev] at h
    rw [h]
    simp
  have hdomt : ∀ p ∈ L t, p35_val gates (o t) (T t p) = true := by
    intro p hp
    have hd : T t p p0 = true ∨ T t p p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → T t p u = true := by
      by_cases h0 : p0 ∈ L t
      · by_cases h1 : p1 ∈ L t
        · by_cases e0 : p = p0
          · left
            rw [hT]
            exact Or.inl e0.symm
          · by_cases e1 : p = p1
            · right
              left
              rw [hT]
              exact Or.inl e1.symm
            · right
              right
              intro u hu
              have e := hline h0 h1
              rw [hT]
              right
              right
              right
              refine ⟨h0, h1, e0, e1, ?_⟩
              rw [e]
              exact hu
        · by_cases e0 : p = p0
          · left
            rw [hT]
            exact Or.inl e0.symm
          · right
            left
            rw [hT]
            exact Or.inr (Or.inr (Or.inl ⟨h0, h1, e0, rfl⟩))
      · by_cases e1 : p = p1
        · right
          left
          rw [hT]
          exact Or.inl e1.symm
        · left
          rw [hT]
          exact Or.inr (Or.inl ⟨h0, e1, rfl⟩)
    have h := hout t (T t p) hd
    rw [hev] at h
    rw [h]
    exact decide_eq_true ⟨p, hp, (hτ p hp p hp).2 rfl⟩
  simp only [hev] at hMg ⊢
  refine ⟨?_, ?_⟩
  · intro g hg a ha b hb h1 h2 X hX
    exact p35_single gates (L t) (fun v : Fin N => decide (v ∉ L t)) (T t) hc hτ legal hin
      ((g : ℕ) + 1) g.2 X (fun i hi => hX i (show i ≤ g from Nat.lt_succ_iff.1 hi))
      (N + (g : ℕ)) (by omega) hg a ha b hb h1 h2
  · intro I hI
    exact p35_qcount gates (L t) (fun v : Fin N => decide (v ∉ L t)) (T t) hc hτ legal hin q
      (hcard t) (o t) hdomc hdomt I (fun g => (hI g).trans (hMg t g))

private def p36_step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma p36_step_len (w : List Bool) (g : Gate) : (p36_step w g).length = w.length + 1 := by
  simp [p36_step]

private lemma p36_step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (p36_step w g).getD i false = w.getD i false := by
  simp [p36_step, List.getD, List.getElem?_append_left hi]

private lemma p36_step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (p36_step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp [p36_step, List.getD]

private def p36_W {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl p36_step (List.ofFn x)

private lemma p36_W_len {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    (p36_W gs x).length = n + gs.length := by
  have h : ∀ (gs : List Gate) (w : List Bool), (gs.foldl p36_step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih, p36_step_len, List.length_cons]
      omega
  rw [p36_W, h]
  simp

private lemma p36_W_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    p36_W (gs ++ [g]) x = p36_step (p36_W gs x) g := by
  simp [p36_W, List.foldl_append]

private lemma p36_W_val {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (t : ℕ) :
    (p36_W (gs ++ [g]) x).getD t false =
      if t = n + gs.length then g.op.eval (g.inputs.map fun i => (p36_W gs x).getD i false)
      else (p36_W gs x).getD t false := by
  rw [p36_W_snoc]
  by_cases ht : t = n + gs.length
  · rw [if_pos ht, p36_step_last _ _ _ (by rw [p36_W_len]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < n + gs.length
    · exact p36_step_lt _ _ _ (by rw [p36_W_len]; exact hlt)
    · rw [List.getD_eq_default _ _ (by rw [p36_step_len, p36_W_len]; omega),
        List.getD_eq_default _ _ (by rw [p36_W_len]; omega)]

private lemma p36_all_true (l : List ℕ) (f : ℕ → Bool) :
    (l.map f).all id = true ↔ ∀ i ∈ l, f i = true := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

private lemma p36_any_true (l : List ℕ) (f : ℕ → Bool) :
    (l.map f).any id = true ↔ ∃ i ∈ l, f i = true := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

private lemma p36_ofFn_getD_true {n : ℕ} (x : Fin n → Bool) (t : ℕ)
    (h : (List.ofFn x).getD t false = true) : ∃ ht : t < n, x ⟨t, ht⟩ = true := by
  by_cases ht : t < n
  · refine ⟨ht, ?_⟩
    rw [List.getD_eq_getElem _ _ (by simpa using ht)] at h
    simpa using h
  · rw [List.getD_eq_default _ _ (by simpa using ht)] at h
    exact Bool.noConfusion h

private lemma p36_ofFn_getD_val {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

private def p36_Mono {n : ℕ} (gs : List Gate) : Prop :=
  ∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) →
    ∀ t, (p36_W gs x).getD t false = true → (p36_W gs y).getD t false = true

private lemma p36_mono_nil {n : ℕ} : p36_Mono (n := n) [] := by
  intro x y hxy t ht
  obtain ⟨hlt, hx⟩ := p36_ofFn_getD_true x t ht
  exact (p36_ofFn_getD_val y ⟨t, hlt⟩).trans (hxy _ hx)

private lemma p36_mono_step {n : ℕ} (gs : List Gate) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (h : p36_Mono (n := n) gs) :
    p36_Mono (n := n) (gs ++ [g]) := by
  intro x y hxy t ht
  rw [p36_W_val] at ht ⊢
  by_cases htt : t = n + gs.length
  · rw [if_pos htt] at ht ⊢
    rcases hop with hand | hor
    · rw [hand] at ht ⊢
      exact (p36_all_true _ _).mpr (fun i hi => h x y hxy i ((p36_all_true _ _).mp ht i hi))
    · rw [hor] at ht ⊢
      obtain ⟨i, hi, hti⟩ := (p36_any_true _ _).mp ht
      exact (p36_any_true _ _).mpr ⟨i, hi, h x y hxy i hti⟩
  · rw [if_neg htt] at ht ⊢
    exact h x y hxy t ht

private lemma p36_mono_all {n : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) : p36_Mono (n := n) gs := by
  induction gs using List.reverseRecOn with
  | nil => exact p36_mono_nil
  | append_singleton gs g ih =>
    exact p36_mono_step gs g (hg g (by simp)) (ih (fun g' hg' => hg g' (by simp [hg'])))

private lemma p36_eval_W {n : ℕ} (gs : List Gate) (o : ℕ) (x : Fin n → Bool) :
    Circuit.eval ⟨gs, o⟩ (List.ofFn x) = (p36_W gs x).getD o false := rfl

private lemma p36_eval_mono {n : ℕ} (gs : List Gate) (o : ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true)
    (h : Circuit.eval ⟨gs, o⟩ (List.ofFn x) = true) :
    Circuit.eval ⟨gs, o⟩ (List.ofFn y) = true := by
  rw [p36_eval_W] at h ⊢
  exact p36_mono_all gs (fun g hgm => (hg g hgm).1) x y hxy o h

theorem p36_main_aux : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ T : Fin N → Fin N → Fin N → Bool,
    (∀ (t p v : Fin N), T t p v = true ↔ (v = p ∨ (p0 ∉ L t ∧ p ≠ p1 ∧ v = p0) ∨ (p0 ∈ L t ∧ p1 ∉ L t ∧ p ≠ p0 ∧ v = p1) ∨
      (p0 ∈ L t ∧ p1 ∈ L t ∧ p ≠ p0 ∧ p ≠ p1 ∧ v ∉ L t))) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
    (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ∀ w : ℕ,
    (∀ m l : Fin N, (p1 ∈ L m ∧ p0 ∉ L m) → (p0 ∈ L l ∧ p1 ∉ L l) → ev w (fun v : Fin N => decide (v ∉ L m)) = false → (∃ p ∈ L l, ev w (T l p) = true) →
      ∀ l' : Fin N, (p0 ∈ L l' ∧ p1 ∉ L l') → l' ≠ l → ev w (fun v : Fin N => decide (v ∉ L l')) = true) ∧
    (∀ l m : Fin N, (p0 ∈ L l ∧ p1 ∉ L l) → (p1 ∈ L m ∧ p0 ∉ L m) → ev w (fun v : Fin N => decide (v ∉ L l)) = false → (∃ p ∈ L m, ev w (T m p) = true) →
      ∀ m' : Fin N, (p1 ∈ L m' ∧ p0 ∉ L m') → m' ≠ m → ev w (fun v : Fin N => decide (v ∉ L m')) = true) ∧
    (∀ m M : Fin N, (p1 ∈ L m ∧ p0 ∉ L m) → ev w (fun v : Fin N => decide (v ∉ L m)) = false → (p0 ∉ L M ∧ p1 ∉ L M) → ((L M).filter (fun p => ev w (T M p) = true)).card ≤ 1) := by
  intro q N L i0 p0 p1 hq hN hcard hint hjoin hne h0 h1 T hT gates hg hin hord ev hev w
  have mono : ∀ x y : Fin N → Bool, (∀ i, x i = true → y i = true) →
      ev w x = true → ev w y = true := by
    intro x y hxy h
    rw [hev] at h ⊢
    exact p36_eval_mono gates w hg x y hxy h
  have two : ∀ a b : Fin N, a ≠ b → ∀ p p' : Fin N, p ∈ L a → p ∈ L b → p' ∈ L a → p' ∈ L b →
      p = p' := by
    intro a b hab p p' ha hb ha' hb'
    have hc := hint a b hab
    rw [Finset.card_eq_one] at hc
    obtain ⟨c, hc⟩ := hc
    have e1 : p ∈ L a ∩ L b := Finset.mem_inter.mpr ⟨ha, hb⟩
    have e2 : p' ∈ L a ∩ L b := Finset.mem_inter.mpr ⟨ha', hb'⟩
    rw [hc] at e1 e2
    rw [Finset.mem_singleton] at e1 e2
    rw [e1, e2]
  refine ⟨?_, ?_, ?_⟩
  · intro m l hm hl hfalse hex l2 hl2 hne2
    obtain ⟨p, hp, htrue⟩ := hex
    by_cases hpp : p = p0
    · exfalso
      have hc : ev w (fun v : Fin N => decide (v ∉ L m)) = true := by
        refine mono _ _ (fun v hv => ?_) htrue
        rcases (hT l p v).mp hv with h | ⟨h, _, _⟩ | ⟨_, _, h, _⟩ | ⟨_, h, _⟩
        · exact decide_eq_true (by rw [h, hpp]; exact hm.2)
        · exact absurd hl.1 h
        · exact absurd hpp h
        · exact absurd h hl.2
      exact Bool.noConfusion (hfalse.symm.trans hc)
    · refine mono _ _ (fun v hv => ?_) htrue
      rcases (hT l p v).mp hv with h | ⟨h, _, _⟩ | ⟨_, _, _, h⟩ | ⟨_, h, _⟩
      · exact decide_eq_true (by
          rw [h]
          intro hin2
          exact hpp (two l l2 (Ne.symm hne2) p p0 hp hin2 hl.1 hl2.1))
      · exact absurd hl.1 h
      · exact decide_eq_true (by rw [h]; exact hl2.2)
      · exact absurd h hl.2
  · intro l m hl hm hfalse hex m2 hm2 hne2
    obtain ⟨p, hp, htrue⟩ := hex
    by_cases hpp : p = p1
    · exfalso
      have hc : ev w (fun v : Fin N => decide (v ∉ L l)) = true := by
        refine mono _ _ (fun v hv => ?_) htrue
        rcases (hT m p v).mp hv with h | ⟨_, h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
        · exact decide_eq_true (by rw [h, hpp]; exact hl.2)
        · exact absurd hpp h
        · exact absurd h hm.2
        · exact absurd h hm.2
      exact Bool.noConfusion (hfalse.symm.trans hc)
    · refine mono _ _ (fun v hv => ?_) htrue
      rcases (hT m p v).mp hv with h | ⟨_, _, h⟩ | ⟨h, _⟩ | ⟨h, _⟩
      · exact decide_eq_true (by
          rw [h]
          intro hin2
          exact hpp (two m m2 (Ne.symm hne2) p p1 hp hin2 hm.1 hm2.1))
      · exact decide_eq_true (by rw [h]; exact hm2.2)
      · exact absurd h hm.2
      · exact absurd h hm.2
  · intro m M hm hfalse hM
    have hMm : M ≠ m := by
      intro h
      rw [h] at hM
      exact hM.2 hm.1
    have hsub : (L M).filter (fun p => ev w (T M p) = true) ⊆ L M ∩ L m := by
      intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hpM, htrue⟩ := hp
      rw [Finset.mem_inter]
      refine ⟨hpM, ?_⟩
      by_contra hpm
      have hc : ev w (fun v : Fin N => decide (v ∉ L m)) = true := by
        refine mono _ _ (fun v hv => ?_) htrue
        rcases (hT M p v).mp hv with h | ⟨_, _, h⟩ | ⟨h, _⟩ | ⟨h, _⟩
        · exact decide_eq_true (by rw [h]; exact hpm)
        · exact decide_eq_true (by rw [h]; exact hm.2)
        · exact absurd h hM.1
        · exact absurd h hM.1
      exact Bool.noConfusion (hfalse.symm.trans hc)
    calc ((L M).filter (fun p => ev w (T M p) = true)).card ≤ (L M ∩ L m).card :=
          Finset.card_le_card hsub
      _ = 1 := hint M m hMm

def p39_step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma p39_step_len (w : List Bool) (g : Gate) : (p39_step w g).length = w.length + 1 := by
  simp [p39_step]

lemma p39_step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (p39_step w g).getD i false = w.getD i false := by
  simp [p39_step, List.getD, List.getElem?_append_left hi]

lemma p39_step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (p39_step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp [p39_step, List.getD]

def p39_W {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl p39_step (List.ofFn x)

lemma p39_W_len {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    (p39_W gs x).length = n + gs.length := by
  have h : ∀ (gs : List Gate) (w : List Bool), (gs.foldl p39_step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih, p39_step_len, List.length_cons]
      omega
  rw [p39_W, h]
  simp

lemma p39_W_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    p39_W (gs ++ [g]) x = p39_step (p39_W gs x) g := by
  simp [p39_W, List.foldl_append]

lemma p39_W_val {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (t : ℕ) :
    (p39_W (gs ++ [g]) x).getD t false =
      if t = n + gs.length then g.op.eval (g.inputs.map fun i => (p39_W gs x).getD i false)
      else (p39_W gs x).getD t false := by
  rw [p39_W_snoc]
  by_cases ht : t = n + gs.length
  · rw [if_pos ht, p39_step_last _ _ _ (by rw [p39_W_len]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < n + gs.length
    · exact p39_step_lt _ _ _ (by rw [p39_W_len]; exact hlt)
    · rw [List.getD_eq_default _ _ (by rw [p39_step_len, p39_W_len]; omega),
        List.getD_eq_default _ _ (by rw [p39_W_len]; omega)]

lemma p39_all_true (l : List ℕ) (f : ℕ → Bool) :
    (l.map f).all id = true ↔ ∀ i ∈ l, f i = true := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

lemma p39_any_true (l : List ℕ) (f : ℕ → Bool) :
    (l.map f).any id = true ↔ ∃ i ∈ l, f i = true := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

lemma p39_ofFn_getD_true {n : ℕ} (x : Fin n → Bool) (t : ℕ)
    (h : (List.ofFn x).getD t false = true) : ∃ ht : t < n, x ⟨t, ht⟩ = true := by
  by_cases ht : t < n
  · refine ⟨ht, ?_⟩
    rw [List.getD_eq_getElem _ _ (by simpa using ht)] at h
    simpa using h
  · rw [List.getD_eq_default _ _ (by simpa using ht)] at h
    exact Bool.noConfusion h

lemma p39_ofFn_getD_val {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

def p39_Mono {n : ℕ} (gs : List Gate) : Prop :=
  ∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) →
    ∀ t, (p39_W gs x).getD t false = true → (p39_W gs y).getD t false = true

lemma p39_mono_nil {n : ℕ} : p39_Mono (n := n) [] := by
  intro x y hxy t ht
  obtain ⟨hlt, hx⟩ := p39_ofFn_getD_true x t ht
  exact (p39_ofFn_getD_val y ⟨t, hlt⟩).trans (hxy _ hx)

lemma p39_mono_step {n : ℕ} (gs : List Gate) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (h : p39_Mono (n := n) gs) :
    p39_Mono (n := n) (gs ++ [g]) := by
  intro x y hxy t ht
  rw [p39_W_val] at ht ⊢
  by_cases htt : t = n + gs.length
  · rw [if_pos htt] at ht ⊢
    rcases hop with hand | hor
    · rw [hand] at ht ⊢
      exact (p39_all_true _ _).mpr (fun i hi => h x y hxy i ((p39_all_true _ _).mp ht i hi))
    · rw [hor] at ht ⊢
      obtain ⟨i, hi, hti⟩ := (p39_any_true _ _).mp ht
      exact (p39_any_true _ _).mpr ⟨i, hi, h x y hxy i hti⟩
  · rw [if_neg htt] at ht ⊢
    exact h x y hxy t ht

lemma p39_mono_all {n : ℕ} (gs : List Gate)
    (h : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) : p39_Mono (n := n) gs := by
  induction gs using List.reverseRecOn with
  | nil => exact p39_mono_nil
  | append_singleton gs g ih =>
    exact p39_mono_step gs g (h g (by simp)) (ih (fun g' hg' => h g' (by simp [hg'])))

lemma p39_W_app_lt {n : ℕ} (pre : List Gate) (x : Fin n → Bool) (t : ℕ)
    (ht : t < n + pre.length) (post : List Gate) :
    (p39_W (pre ++ post) x).getD t false = (p39_W pre x).getD t false := by
  induction post using List.reverseRecOn with
  | nil => simp
  | append_singleton post g ih =>
    rw [← List.append_assoc, p39_W_val, if_neg (by rw [List.length_append]; omega)]
    exact ih

lemma p39_wire_input {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (p : Fin n) :
    (p39_W gs x).getD p.val false = x p := by
  have h := p39_W_app_lt [] x p.val (by simpa using p.isLt) gs
  rw [List.nil_append] at h
  rw [h]
  exact p39_ofFn_getD_val x p

lemma p39_or_up_split {n : ℕ} (pre post : List Gate) (g : Gate) (x : Fin n → Bool)
    (hor : g.op = GateOp.or) (a : ℕ) (ha : a ∈ g.inputs) (hlt : a < n + pre.length)
    (hv : (p39_W (pre ++ g :: post) x).getD a false = true) :
    (p39_W (pre ++ g :: post) x).getD (n + pre.length) false = true := by
  have e : pre ++ g :: post = (pre ++ [g]) ++ post := by simp
  rw [e] at hv ⊢
  rw [p39_W_app_lt (pre ++ [g]) x _ (by rw [List.length_append, List.length_singleton]; omega)] at hv ⊢
  rw [p39_W_val] at hv ⊢
  rw [if_pos rfl, hor]
  rw [if_neg (by omega)] at hv
  exact (p39_any_true _ _).mpr ⟨a, ha, hv⟩

lemma p39_or_up {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : Fin gs.length)
    (hor : (gs.get i).op = GateOp.or) (a : ℕ) (ha : a ∈ (gs.get i).inputs)
    (hlt : a < n + i.val) (hv : (p39_W gs x).getD a false = true) :
    (p39_W gs x).getD (n + i.val) false = true := by
  have hsplit : gs.take i.val ++ gs.get i :: gs.drop (i.val + 1) = gs := by
    rw [List.get_eq_getElem, ← List.drop_eq_getElem_cons i.isLt, List.take_append_drop]
  have hlen : (gs.take i.val).length = i.val := by
    rw [List.length_take]
    exact min_eq_left (le_of_lt i.isLt)
  have h := p39_or_up_split (gs.take i.val) (gs.drop (i.val + 1)) (gs.get i) x hor a ha
    (by rw [hlen]; exact hlt) (by rw [hsplit]; exact hv)
  rw [hsplit, hlen] at h
  exact h

theorem p39_main_aux : ∀ (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → 1 ≤ m → m ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = m →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (u : ℕ),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) → (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
    ∀ (t : Fin N) (y : Fin N), t ≠ i0 → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L t))) = false → L t ∩ L i0 = {y} →
      (∀ p : Fin N, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ e ∈ (gates.get i).inputs, e ∈ S) → (p : ℕ) ∈ S) → p = y) ∧ (y ∉ T0 → ∀ x ∈ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin N => decide (v = x))) = false) := by
  intro q m N L i0 T0 _ _ _ _ _ _ _ hT0 _ gates u hops _ hwf h0 t y _ ht hy
  have h0w : (p39_W gates (fun v : Fin N => decide (v ∉ L i0))).getD u false = false := h0
  have htw : (p39_W gates (fun v : Fin N => decide (v ∉ L t))).getD u false = false := ht
  refine ⟨?_, ?_⟩
  · intro p hp
    have hpS := hp {w | ((p39_W gates (fun v : Fin N => decide (v ∉ L i0))).getD w false = true →
        (p39_W gates (fun v : Fin N => decide (v ∉ L i0))).getD u false = true) ∧
      ((p39_W gates (fun v : Fin N => decide (v ∉ L t))).getD w false = true →
        (p39_W gates (fun v : Fin N => decide (v ∉ L t))).getD u false = true)} ⟨id, id⟩ ?_
    · have hpS2 : ((p39_W gates (fun v : Fin N => decide (v ∉ L i0))).getD p.val false = true →
          (p39_W gates (fun v : Fin N => decide (v ∉ L i0))).getD u false = true) ∧
        ((p39_W gates (fun v : Fin N => decide (v ∉ L t))).getD p.val false = true →
          (p39_W gates (fun v : Fin N => decide (v ∉ L t))).getD u false = true) := hpS
      obtain ⟨h1, h2⟩ := hpS2
      have hp0 : p ∈ L i0 := by
        by_contra hc
        have hw : (p39_W gates (fun v : Fin N => decide (v ∉ L i0))).getD p.val false = true := by
          rw [p39_wire_input]
          simpa using hc
        rw [h1 hw] at h0w
        exact Bool.noConfusion h0w
      have hpt : p ∈ L t := by
        by_contra hc
        have hw : (p39_W gates (fun v : Fin N => decide (v ∉ L t))).getD p.val false = true := by
          rw [p39_wire_input]
          simpa using hc
        rw [h2 hw] at htw
        exact Bool.noConfusion htw
      have hmem : p ∈ L t ∩ L i0 := Finset.mem_inter.mpr ⟨hpt, hp0⟩
      rw [hy] at hmem
      exact Finset.mem_singleton.mp hmem
    · intro i hi hor a ha
      have hi2 : ((p39_W gates (fun v : Fin N => decide (v ∉ L i0))).getD (N + i.val) false = true →
          (p39_W gates (fun v : Fin N => decide (v ∉ L i0))).getD u false = true) ∧
        ((p39_W gates (fun v : Fin N => decide (v ∉ L t))).getD (N + i.val) false = true →
          (p39_W gates (fun v : Fin N => decide (v ∉ L t))).getD u false = true) := hi
      exact ⟨fun hv => hi2.1 (p39_or_up gates _ i hor a ha (hwf i a ha) hv),
        fun hv => hi2.2 (p39_or_up gates _ i hor a ha (hwf i a ha) hv)⟩
  · intro hyT x hx
    have hxt : x ∉ L t := by
      intro hxt
      have hmem : x ∈ L t ∩ L i0 := Finset.mem_inter.mpr ⟨hxt, hT0 hx⟩
      rw [hy] at hmem
      have hxy : x = y := Finset.mem_singleton.mp hmem
      exact hyT (hxy ▸ hx)
    show (p39_W gates (fun v : Fin N => decide (v = x))).getD u false = false
    by_contra hc
    have hc2 : (p39_W gates (fun v : Fin N => decide (v = x))).getD u false = true := by
      simpa using hc
    have hm := p39_mono_all (n := N) gates (fun g hg => (hops g hg).1)
      (fun v => decide (v = x)) (fun v => decide (v ∉ L t))
      (by
        intro v hv
        have hvx : v = x := by simpa using hv
        rw [hvx]
        simpa using hxt) u hc2
    rw [hm] at htw
    exact Bool.noConfusion htw

def p42_Good {P : Type*} [DecidableEq P] (R D : Finset P) (sens pure : P → Prop) (core : Prop) : Prop :=
  (∀ r ∈ R, r ∉ D → sens r → pure r ∧ ¬ core) ∧
  (∀ r ∈ R, r ∉ D → sens r → ∀ s ∈ R, s ∉ D → sens s → r = s)

lemma p42_Good.mono {P : Type*} [DecidableEq P] {R D E : Finset P} {s p : P → Prop} {c : Prop}
    (h : p42_Good R D s p c) (hDE : D ⊆ E) : p42_Good R E s p c :=
  ⟨fun r hr hd hs => h.1 r hr (fun h => hd (hDE h)) hs,
   fun r hr hd hs t ht he hs' => h.2 r hr (fun h => hd (hDE h)) hs t ht (fun h => he (hDE h)) hs'⟩

abbrev p42_V {N : ℕ} (gs : List Gate) (w : ℕ) (x : Fin N → Bool) : Bool := Circuit.eval ⟨gs,w⟩ (List.ofFn x)
abbrev p42_base {N : ℕ} (M : Finset (Fin N)) : Fin N → Bool := fun v => decide (v ∉ M)
abbrev p42_single {N : ℕ} (r : Fin N) : Fin N → Bool := fun v => decide (v = r)
abbrev p42_rimInput {N : ℕ} (M : Finset (Fin N)) (r : Fin N) : Fin N → Bool := fun v => decide (v ∉ M ∨ v = r)
abbrev p42_S {N : ℕ} (gs : List Gate) (M : Finset (Fin N)) (w : ℕ) (r : Fin N) : Prop := p42_V gs w (p42_rimInput M r) = true
abbrev p42_U {N : ℕ} (gs : List Gate) (w : ℕ) (r : Fin N) : Prop := p42_V gs w (p42_single r) = true
abbrev p42_C {N : ℕ} (gs : List Gate) (T : Finset (Fin N)) (w : ℕ) : Prop := ∃ x ∈ T, p42_U gs w x

namespace p42_CoWire

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (p42_C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (p42_C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (p42_C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value p42_C x p = x p := by
  change (run p42_C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (p42_C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + p42_C.size ≤ w) : value p42_C x w = false := by
  change (run p42_C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (p42_C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + p42_C.size) :
    let g := p42_C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value p42_C x w = g.op.eval (g.inputs.map fun r => if r < w then value p42_C x r else false) := by
  let j := w - n
  have hj : j < p42_C.gates.length := by unfold j Circuit.size at *; omega
  let g := p42_C.gates[j]
  let earlier := run (p42_C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run p42_C.gates (List.ofFn x) = run (g :: p42_C.gates.drop (j + 1)) earlier := by
    rw [run_split p42_C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value p42_C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run p42_C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run p42_C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value p42_C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma gate_mono {n : ℕ} (p42_C : Circuit) (k : ℕ) (hk : k < p42_C.gates.length)
    (hop : p42_C.gates[k].op = GateOp.and ∨ p42_C.gates[k].op = GateOp.or)
    (x y : Fin n → Bool)
    (h : ∀ r ∈ p42_C.gates[k].inputs, r < n + k → value p42_C x r = true → value p42_C y r = true) :
    value p42_C x (n + k) = true → value p42_C y (n + k) = true := by
  have hw : n + k < n + p42_C.size := by unfold Circuit.size; omega
  have hx := gate_value p42_C x (n + k) (by omega) hw
  have hy := gate_value p42_C y (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx hy
  rw [hx, hy]
  have hr (r : ℕ) (hm : r ∈ p42_C.gates[k].inputs) :
      (if r < n + k then value p42_C x r else false) = true →
      (if r < n + k then value p42_C y r else false) = true := by
    by_cases h' : r < n + k
    · simpa [h'] using h r hm h'
    · simp [h']
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_eq_true, id_eq]
    intro hx b hb
    obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
    exact hr r hm (hx _ (List.mem_map.mpr ⟨r, hm, rfl⟩))
  · simp only [hop, GateOp.eval, List.any_eq_true, id_eq]
    intro hx
    obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨r, hm, hv⟩ := List.mem_map.mp hb
    exact ⟨_, List.mem_map.mpr ⟨r, hm, rfl⟩, hr r hm hv⟩

lemma mono {n : ℕ} (p42_C : Circuit)
    (hC : ∀ g ∈ p42_C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (h : ∀ v, x v = true → y v = true) (w : ℕ) :
    value p42_C x w = true → value p42_C y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value p42_C x p = true → value p42_C y p = true
      simpa only [input_value] using h p
    by_cases hw : w < n + p42_C.gates.length
    · have hk : w - n < p42_C.gates.length := by omega
      have hwk : w = n + (w - n) := by omega
      rw [hwk]
      exact gate_mono p42_C (w - n) hk (hC _ (List.getElem_mem hk)).1 x y fun r _ hlt => ih r (by omega)
    · simp [missing_value p42_C x w (by unfold Circuit.size; omega)]

end p42_CoWire

lemma p42_twoPoints {N : ℕ} (L : Fin N → Finset (Fin N)) {i t r s : Fin N}
    (hinter : ∀ i j, i ≠ j → (L i ∩ L j).card = 1)
    (ht : t ≠ i) (hr : r ∈ L i) (hs : s ∈ L i) (hrs : r ≠ s) :
    r ∉ L t ∨ s ∉ L t := by
  by_contra! h
  have hsub : ({r,s} : Finset (Fin N)) ⊆ L i ∩ L t := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨hr, h.1⟩
    · exact Finset.mem_inter.mpr ⟨hs, h.2⟩
  have hle := Finset.card_le_card hsub
  simp [hrs, hinter i t ht.symm] at hle

lemma p42_offOther {N : ℕ} (gates : List Gate) (w : ℕ) (L : Fin N → Finset (Fin N))
    {i r s : Fin N} (hC : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hinter : ∀ i j, i ≠ j → (L i ∩ L j).card = 1)
    (hr : r ∈ L i) (hs : s ∈ L i) (hrs : r ≠ s)
    (h1 : Circuit.eval ⟨gates,w⟩ (List.ofFn fun v : Fin N => decide (v = r)) = true)
    (h2 : Circuit.eval ⟨gates,w⟩ (List.ofFn fun v : Fin N => decide (v = s)) = true)
    (t : Fin N) (ht : t ≠ i) :
    Circuit.eval ⟨gates,w⟩ (List.ofFn fun v : Fin N => decide (v ∉ L t)) = true := by
  have lift (p : Fin N) (hp : p ∉ L t)
      (hv : Circuit.eval ⟨gates,w⟩ (List.ofFn fun v : Fin N => decide (v = p)) = true) :
      Circuit.eval ⟨gates,w⟩ (List.ofFn fun v : Fin N => decide (v ∉ L t)) = true := by
    apply p42_CoWire.mono ⟨gates,w⟩ hC (fun v : Fin N => decide (v = p)) (fun v => decide (v ∉ L t)) _ w hv
    intro v h
    simp only [decide_eq_true_eq] at h ⊢
    simpa only [h] using hp
  rcases p42_twoPoints L hinter ht hr hs hrs with h | h
  · exact lift r h h1
  · exact lift s h h2

theorem p42_orUpdate {P : Type*} [DecidableEq P] (R D : Finset P) (s₁ s₂ p₁ p₂ : P → Prop)
    (c₁ c₂ Q : Prop) [Decidable Q] (g₁ : p42_Good R D s₁ p₁ c₁) (g₂ : p42_Good R D s₂ p₂ c₂)
    (charge : ((∃ r ∈ R, r ∉ D ∧ s₁ r ∧ c₂) ∨ (∃ r ∈ R, r ∉ D ∧ s₂ r ∧ c₁) ∨
        (∃ r ∈ R, ∃ t ∈ R, r ∉ D ∧ t ∉ D ∧ s₁ r ∧ s₂ t ∧ r ≠ t)) → Q) :
    ∃ E : Finset P, D ⊆ E ∧ E.card ≤ D.card + (if Q then 1 else 0) ∧
      p42_Good R E (fun r => s₁ r ∨ s₂ r) (fun r => p₁ r ∨ p₂ r) (c₁ ∨ c₂) := by
  classical
  let Bad := (∃ r ∈ R, r ∉ D ∧ s₁ r ∧ c₂) ∨ (∃ r ∈ R, r ∉ D ∧ s₂ r ∧ c₁) ∨
             (∃ r ∈ R, ∃ t ∈ R, r ∉ D ∧ t ∉ D ∧ s₁ r ∧ s₂ t ∧ r ≠ t)
  have drop {s p : P → Prop} {c : Prop} (g : p42_Good R D s p c) {a : P}
      (ha : a ∈ R) (hd : a ∉ D) (hs : s a) :
      ∀ z ∈ R, z ∉ insert a D → ¬ s z := by
    intro z hz he hsz
    have eq := g.2 z hz (fun h => he (Finset.mem_insert_of_mem h)) hsz a ha hd hs
    exact he (Finset.mem_insert.mpr (Or.inl eq))
  have vac (E : Finset P) (h : ∀ z ∈ R, z ∉ E → ¬ (s₁ z ∨ s₂ z)) :
      p42_Good R E (fun z => s₁ z ∨ s₂ z) (fun z => p₁ z ∨ p₂ z) (c₁ ∨ c₂) := by
    exact ⟨fun r hr he hs => (h r hr he hs).elim, fun r hr he hs => (h r hr he hs).elim⟩
  by_cases bad : Bad
  · have q : Q := charge bad
    have budget (a : P) : (insert a D).card ≤ D.card + (if Q then 1 else 0) := by
      rw [ite_eq_left q]
      exact Finset.card_insert_le a D
    rcases bad with ⟨a,ha,hd,hs,hc⟩ | ⟨a,ha,hd,hs,hc⟩ | ⟨a,ha,b,hb,hd,_,hs,_,_⟩
    · refine ⟨insert a D, Finset.subset_insert _ _, budget a, vac _ ?_⟩
      intro z hz he h
      rcases h with l | r
      · exact drop g₁ ha hd hs z hz he l
      · exact (g₂.1 z hz (fun h => he (Finset.mem_insert_of_mem h)) r).2 hc
    · refine ⟨insert a D, Finset.subset_insert _ _, budget a, vac _ ?_⟩
      intro z hz he h
      rcases h with l | r
      · exact (g₁.1 z hz (fun h => he (Finset.mem_insert_of_mem h)) l).2 hc
      · exact drop g₂ ha hd hs z hz he r
    · refine ⟨insert a D, Finset.subset_insert _ _, budget a, ?_⟩
      have right : ∀ z ∈ R, z ∉ insert a D → s₁ z ∨ s₂ z → s₂ z :=
        fun z hz he h => h.resolve_left (drop g₁ ha hd hs z hz he)
      have g₂' := g₂.mono (Finset.subset_insert a D)
      constructor
      · intro z hz he h
        have v := g₂'.1 z hz he (right z hz he h)
        exact ⟨Or.inr v.1, fun hC => hC.elim (g₁.1 a ha hd hs).2 v.2⟩
      · intro z hz he h t ht hte hts
        exact g₂'.2 z hz he (right z hz he h) t ht hte (right t ht hte hts)
  · refine ⟨D, Finset.Subset.rfl, Nat.le_add_right _ _, ?_⟩
    have cross {a b : P} (ha : a ∈ R) (hb : b ∈ R) (da : a ∉ D) (db : b ∉ D)
        (sa : s₁ a) (sb : s₂ b) : a = b := by
      by_contra hn
      exact bad (Or.inr (Or.inr ⟨a,ha,b,hb,da,db,sa,sb,hn⟩))
    constructor
    · intro r hr hd hs
      rcases hs with l | r'
      · have v := g₁.1 r hr hd l
        exact ⟨Or.inl v.1, fun c => c.elim v.2 (fun rc => bad (Or.inl ⟨r,hr,hd,l,rc⟩))⟩
      · have v := g₂.1 r hr hd r'
        exact ⟨Or.inr v.1, fun c => c.elim (fun lc => bad (Or.inr (Or.inl ⟨r,hr,hd,r',lc⟩))) v.2⟩
    · intro a ha da hsa b hb db hsb
      rcases hsa with l | r <;> rcases hsb with l' | r'
      · exact g₁.2 a ha da l b hb db l'
      · exact cross ha hb da db l r'
      · exact (cross hb ha db da l' r).symm
      · exact g₂.2 a ha da r b hb db r'

lemma p42_Good.imp {P : Type*} [DecidableEq P] {R D : Finset P} {s p s' p' : P → Prop} {c c' : Prop}
    (h : p42_Good R D s p c) (hs : ∀ r, s' r → s r) (hp : ∀ r, p r → p' r) (hc : c' → c) :
    p42_Good R D s' p' c' :=
  ⟨fun r hr hd h' => ⟨hp r (h.1 r hr hd (hs r h')).1, fun k => (h.1 r hr hd (hs r h')).2 (hc k)⟩,
   fun r hr hd h' t ht hd' h'' => h.2 r hr hd (hs r h') t ht hd' (hs t h'')⟩

lemma p42_Good.vac {P : Type*} [DecidableEq P] {R D : Finset P} {s p : P → Prop} {c : Prop}
    (h : ∀ r ∈ R, r ∉ D → ¬ s r) : p42_Good R D s p c :=
  ⟨fun r hr hd hs => (h r hr hd hs).elim, fun r hr hd hs => (h r hr hd hs).elim⟩

theorem p42_realOrUpdate {N : ℕ} {L : Fin N → Finset (Fin N)} {i0 : Fin N}
    {T : Finset (Fin N)} {gs : List Gate} {Xs : Finset (Fin gs.length)} {D : Finset (Fin N)}
    (St : ℕ → Fin N → Prop)
    (hG : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hinter : ∀ i j, i ≠ j → (L i ∩ L j).card = 1) (hTsub : T ⊆ L i0)
    (hXs : ∀ g : Fin gs.length, ((gs.get g).op = GateOp.or ∧ p42_V gs (N + g.val) (p42_base (L i0)) = false ∧
      (∀ t : Fin N, t ≠ i0 → p42_V gs (N + g.val) (p42_base (L t)) = true) ∧
      ¬ ∀ e ∈ (gs.get g).inputs, p42_C gs T e) → g ∈ Xs)
    (i : Fin gs.length) (a b : ℕ) (hop : (gs.get i).op = GateOp.or)
    (hinputs : (gs.get i).inputs = [a,b]) (hcold : p42_V gs (N + i.val) (p42_base (L i0)) = false)
    (hor : ∀ x : Fin N → Bool, p42_V gs (N + i.val) x = (p42_V gs a x || p42_V gs b x))
    (stA : ∀ r, St a r → St (N + i.val) r) (stB : ∀ r, St b r → St (N + i.val) r)
    (ga : p42_Good (L i0 \ T) D (p42_S gs (L i0) a) (fun r => p42_U gs a r ∧ St a r) (p42_C gs T a))
    (gb : p42_Good (L i0 \ T) D (p42_S gs (L i0) b) (fun r => p42_U gs b r ∧ St b r) (p42_C gs T b)) :
    ∃ E : Finset (Fin N), D ⊆ E ∧ E.card ≤ D.card + (if i ∈ Xs then 1 else 0) ∧
      p42_Good (L i0 \ T) E (p42_S gs (L i0) (N + i.val))
        (fun r => p42_U gs (N + i.val) r ∧ St (N + i.val) r) (p42_C gs T (N + i.val)) := by
  classical
  have us (r : Fin N) : p42_U gs (N + i.val) r ↔ p42_U gs a r ∨ p42_U gs b r := by
    change p42_V gs (N + i.val) (p42_single r) = true ↔ _
    rw [hor]
    simp only [Bool.or_eq_true, p42_U]
  have ss (r : Fin N) : p42_S gs (L i0) (N + i.val) r ↔ p42_S gs (L i0) a r ∨ p42_S gs (L i0) b r := by
    change p42_V gs (N + i.val) (p42_rimInput (L i0) r) = true ↔ _
    rw [hor]
    simp only [Bool.or_eq_true, p42_S]
  have cs : p42_C gs T (N + i.val) ↔ p42_C gs T a ∨ p42_C gs T b := by
    constructor
    · rintro ⟨x,hx,ux⟩
      rcases (us x).1 ux with ua | ub
      · exact Or.inl ⟨x,hx,ua⟩
      · exact Or.inr ⟨x,hx,ub⟩
    · rintro (⟨x,hx,ua⟩ | ⟨x,hx,ub⟩)
      · exact ⟨x,hx,(us x).2 (Or.inl ua)⟩
      · exact ⟨x,hx,(us x).2 (Or.inr ub)⟩
  have pay {r t : Fin N} (hr : r ∈ L i0) (ht : t ∈ L i0) (hrt : r ≠ t)
      (u₁ : p42_U gs a r) (u₂ : p42_U gs b t) (empty : ¬ p42_C gs T a ∨ ¬ p42_C gs T b) : i ∈ Xs := by
    have every := p42_offOther gs (N + i.val) L hG hinter hr ht hrt
      ((us r).2 (Or.inl u₁)) ((us t).2 (Or.inr u₂))
    refine hXs i ⟨hop, hcold, every, fun hall => ?_⟩
    rcases empty with ha | hb
    · exact ha (hall a (by rw [hinputs]; simp))
    · exact hb (hall b (by rw [hinputs]; simp))
  obtain ⟨E,hDE,hcard,hGood⟩ := p42_orUpdate (L i0 \ T) D _ _ _ _ _ _ (i ∈ Xs) ga gb (by
    rintro (⟨r,hr,hd,sa,t,ht,ub⟩ | ⟨t,ht,hd,sb,r,hr,ua⟩ | ⟨r,hr,t,ht,dr,dt,sa,sb,hrt⟩)
    · obtain ⟨ua,ha⟩ := ga.1 r hr hd sa
      have h := Finset.mem_sdiff.mp hr
      exact pay h.1 (hTsub ht) (fun e => h.2 (e ▸ ht)) ua.1 ub (Or.inl ha)
    · obtain ⟨ub,hb⟩ := gb.1 t ht hd sb
      have h := Finset.mem_sdiff.mp ht
      exact pay (hTsub hr) h.1 (fun e => h.2 (e ▸ hr)) ua ub.1 (Or.inr hb)
    · obtain ⟨ua,ha⟩ := ga.1 r hr dr sa
      obtain ⟨ub,_⟩ := gb.1 t ht dt sb
      exact pay (Finset.mem_sdiff.mp hr).1 (Finset.mem_sdiff.mp ht).1 hrt ua.1 ub.1 (Or.inl ha))
  refine ⟨E,hDE,hcard,?_,?_⟩
  · intro r hr hd sr
    obtain ⟨u,c⟩ := hGood.1 r hr hd ((ss r).1 sr)
    refine ⟨?_, fun h => c (cs.1 h)⟩
    rcases u with u | u
    · exact ⟨(us r).2 (Or.inl u.1), stA r u.2⟩
    · exact ⟨(us r).2 (Or.inr u.1), stB r u.2⟩
  · intro r hr hd sr t ht hdt st
    exact hGood.2 r hr hd ((ss r).1 sr) t ht hdt ((ss t).1 st)

theorem p42_prefixBudget {P : Type*} [DecidableEq P] (N k : ℕ)
    (A Xs : Finset (Fin k)) (G : ℕ → Finset P → Prop)
    (mono : ∀ w D E, D ⊆ E → G w D → G w E)
    (init : ∀ w < N, G w ∅)
    (step : ∀ (i : Fin k) (D : Finset P), (∀ w < N + i.val, G w D) →
      ∃ E, D ⊆ E ∧ E.card ≤ D.card + (if i ∈ A then 1 else 0) +
        (if i ∈ Xs then 1 else 0) ∧ G (N + i.val) E) :
    ∃ D, D.card ≤ A.card + Xs.card ∧ ∀ w < N + k, G w D := by
  let count (p42_S : Finset (Fin k)) (j : ℕ) := (p42_S.filter fun v => v.val < j).card
  have next (p42_S : Finset (Fin k)) (i : Fin k) :
      count p42_S (i.val + 1) = count p42_S i.val + (if i ∈ p42_S then 1 else 0) := by
    have hlt (v : Fin k) : v.val < i.val + 1 ↔ v = i ∨ v.val < i.val := by
      rw [Fin.ext_iff]
      omega
    by_cases hi : i ∈ p42_S
    · have heq : p42_S.filter (fun v => v.val < i.val + 1) =
          insert i (p42_S.filter fun v => v.val < i.val) := by
        ext v
        by_cases hv : v = i
        · subst v
          simp [hi]
        · simp [hlt, hv]
      have hnot : i ∉ p42_S.filter (fun v => v.val < i.val) := by simp
      simp only [count, heq, Finset.card_insert_of_notMem hnot, ite_eq_left hi]
    · have heq : p42_S.filter (fun v => v.val < i.val + 1) =
          p42_S.filter (fun v => v.val < i.val) := by
        ext v
        by_cases hv : v = i
        · subst v
          simp [hi]
        · simp [hlt, hv]
      simp only [count, heq, ite_eq_right hi, Nat.add_zero]
  have prefixBound (j : ℕ) (hj : j ≤ k) :
      ∃ D, D.card ≤ count A j + count Xs j ∧ ∀ w < N + j, G w D := by
    induction j with
    | zero =>
      exact ⟨∅, by simp [count], by simpa using init⟩
    | succ j ih =>
      let i : Fin k := ⟨j, by omega⟩
      obtain ⟨D, hD, hG⟩ := ih (by omega)
      obtain ⟨E, hDE, hE, hGE⟩ := step i D hG
      refine ⟨E, ?_, ?_⟩
      · change E.card ≤ count A (i.val + 1) + count Xs (i.val + 1)
        rw [next A i, next Xs i]
        change D.card ≤ count A i.val + count Xs i.val at hD
        omega
      · intro w hw
        by_cases hprev : w < N + j
        · exact mono w D E hDE (hG w hprev)
        · have hw' : w = N + i.val := by change w = N + j; omega
          exact hw' ▸ hGE
  have last (p42_S : Finset (Fin k)) : count p42_S k = p42_S.card := by
    have heq : p42_S.filter (fun v => v.val < k) = p42_S := by
      ext v
      simp
    simp only [count, heq]
  simpa only [last] using prefixBound k (le_refl k)

lemma p42_primaryGood {N : ℕ} (gs : List Gate) (M T : Finset (Fin N)) (w : ℕ) (hw : w < N)
    (hc : p42_V gs w (p42_base M) = false) : p42_Good (M \ T) ∅ (p42_S gs M w) (p42_U gs w) (p42_C gs T w) := by
  let p : Fin N := ⟨w, hw⟩
  have eval (x : Fin N → Bool) : p42_V gs w x = x p := p42_CoWire.input_value ⟨gs,w⟩ x p
  rw [eval] at hc
  have hp : p ∈ M := by simpa [p42_base] using hc
  have sens (r : Fin N) : p42_S gs M w r ↔ p = r := by
    change p42_V gs w (p42_rimInput M r) = true ↔ _
    rw [eval]
    simp [p42_rimInput, hp]
  have purePt (r : Fin N) : p42_U gs w r ↔ p = r := by
    change p42_V gs w (p42_single r) = true ↔ _
    rw [eval]
    simp [p42_single]
  constructor
  · intro r hr _ hs
    refine ⟨(purePt r).mpr ((sens r).mp hs), ?_⟩
    rintro ⟨x, hx, hux⟩
    have heq : r = x := ((sens r).mp hs).symm.trans ((purePt x).mp hux)
    exact (Finset.mem_sdiff.mp hr).2 (heq ▸ hx)
  · intro r _ _ hr s _ _ hs
    exact ((sens r).mp hr).symm.trans ((sens s).mp hs)

lemma p42_missingV {N : ℕ} (gs : List Gate) (w : ℕ) (hw : N + gs.length ≤ w)
    (x : Fin N → Bool) : p42_V gs w x = false :=
  p42_CoWire.missing_value ⟨gs,w⟩ x w hw

lemma p42_primaryGood2 {N : ℕ} (gs : List Gate) (M T : Finset (Fin N)) (St : ℕ → Fin N → Prop)
    (stIn : ∀ r : Fin N, St r.val r) (w : ℕ) (hw : w < N)
    (hc : p42_V gs w (p42_base M) = false) :
    p42_Good (M \ T) ∅ (p42_S gs M w) (fun r => p42_U gs w r ∧ St w r) (p42_C gs T w) := by
  refine (p42_primaryGood gs M T w hw hc).imp (fun _ h => h) ?_ (fun h => h)
  intro r hu
  refine ⟨hu, ?_⟩
  have eval : p42_V gs w (p42_single r) = p42_single r ⟨w, hw⟩ :=
    p42_CoWire.input_value ⟨gs,w⟩ (p42_single r) ⟨w, hw⟩
  have hu' : p42_V gs w (p42_single r) = true := hu
  rw [eval] at hu'
  have heq : (⟨w, hw⟩ : Fin N) = r := by simpa [p42_single] using hu'
  subst heq
  exact stIn ⟨w, hw⟩

lemma p42_gateCases {N : ℕ} (gs : List Gate)
    (hG : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (htop : ∀ i : Fin gs.length, 1 ≤ (gs.get i).inputs.length ∧
      ∀ a ∈ (gs.get i).inputs, a < N + i.val) (i : Fin gs.length) :
    (∃ a < N + i.val, (gs.get i).inputs = [a] ∧
      ∀ x : Fin N → Bool, p42_V gs (N + i.val) x = p42_V gs a x) ∨
    (∃ a < N + i.val, ∃ b < N + i.val, (gs.get i).op = GateOp.and ∧
      (gs.get i).inputs = [a, b] ∧
      ∀ x : Fin N → Bool, p42_V gs (N + i.val) x = (p42_V gs a x && p42_V gs b x)) ∨
    (∃ a < N + i.val, ∃ b < N + i.val, (gs.get i).op = GateOp.or ∧
      (gs.get i).inputs = [a, b] ∧
      ∀ x : Fin N → Bool, p42_V gs (N + i.val) x = (p42_V gs a x || p42_V gs b x)) := by
  obtain ⟨hop, hlen⟩ := hG (gs.get i) (List.get_mem gs i)
  obtain ⟨hnon, earlier⟩ := htop i
  have val (x : Fin N → Bool) :
      p42_V gs (N + i.val) x = (gs.get i).op.eval
        ((gs.get i).inputs.map fun r => if r < N + i.val then p42_V gs r x else false) := by
    let D : Circuit := ⟨gs,0⟩
    have hw : N + i.val < N + D.size := Nat.add_lt_add_left i.isLt N
    have h := p42_CoWire.gate_value D x (N + i.val) (by omega) hw
    simpa [D, p42_CoWire.value, p42_V, Circuit.eval, Circuit.wires] using h
  generalize eqg : gs.get i = g at hop hlen hnon earlier val ⊢
  cases ins : g.inputs with
  | nil => simp [ins] at hnon
  | cons a rest =>
    have ha : a < N + i.val := earlier a (by simp [ins])
    cases rest with
    | nil =>
      refine Or.inl ⟨a, ha, rfl, ?_⟩
      intro x
      rcases hop with hop | hop <;> simpa [ins, hop, GateOp.eval, ha] using val x
    | cons b rest =>
      cases rest with
      | nil =>
        have hb : b < N + i.val := earlier b (by simp [ins])
        rcases hop with hop | hop
        · refine Or.inr (Or.inl ⟨a, ha, b, hb, hop, rfl, ?_⟩)
          intro x
          simpa [ins, hop, GateOp.eval, ha, hb] using val x
        · refine Or.inr (Or.inr ⟨a, ha, b, hb, hop, rfl, ?_⟩)
          intro x
          simpa [ins, hop, GateOp.eval, ha, hb] using val x
      | cons c rest => simp [ins] at hlen

lemma p42_andInputs {N : ℕ} (gs : List Gate)
    (hG : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (htop : ∀ i : Fin gs.length, 1 ≤ (gs.get i).inputs.length ∧
      ∀ a ∈ (gs.get i).inputs, a < N + i.val) (i : Fin gs.length)
    (hand : (gs.get i).op = GateOp.and) (e : ℕ) (he : e ∈ (gs.get i).inputs)
    (x : Fin N → Bool) (hx : p42_V gs (N + i.val) x = true) : p42_V gs e x = true := by
  rcases p42_gateCases gs hG htop i with
    ⟨a, _, hin, heq⟩ | ⟨a, _, b, _, _, hin, heq⟩ | ⟨a, _, b, _, hop, _, _⟩
  · rw [hin] at he
    have hea : e = a := by simpa using he
    subst hea
    exact (heq x).symm.trans hx
  · rw [hin] at he
    have hab := Bool.and_eq_true_iff.mp ((heq x).symm.trans hx)
    have hea : e = a ∨ e = b := by simpa using he
    rcases hea with h | h
    · rw [h]; exact hab.1
    · rw [h]; exact hab.2
  · rw [hand] at hop
    cases hop

theorem p42_main_aux : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
    (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ∀ o0 : ℕ, ev o0 (fun v : Fin N => decide (v ∉ L i0)) = false → ev o0 (fun v : Fin N => decide (v = p0)) = true → ev o0 (fun v : Fin N => decide (v = p1)) = true →
    (∀ r ∈ L i0, r ≠ p0 → r ≠ p1 → ev o0 (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true) →
    ∀ St : ℕ → Fin N → Prop,
    (∀ (w : ℕ) (p : Fin N), St w p ↔ ∀ Zs : Set ℕ, w ∈ Zs → (∀ k : Fin gates.length, N + (k : ℕ) ∈ Zs → (gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ e ∈ (gates.get k).inputs, e ∈ Zs) → (p : ℕ) ∈ Zs) →
    ∀ ch : Fin gates.length → ℕ, (∀ a : Fin gates.length, ((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ev (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false ∧ ∃ r ∈ L i0, r ≠ p0 ∧ r ≠ p1 ∧ ev (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true) → ch a ∈ (gates.get a).inputs ∧ ev (ch a) (fun v : Fin N => decide (v ∉ L i0)) = false) →
    ∀ Au Xs : Finset (Fin gates.length), (∀ a : Fin gates.length, (((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ev (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false ∧ ∃ r ∈ L i0, r ≠ p0 ∧ r ≠ p1 ∧ ev (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true) ∧ ∃ r ∈ L i0, r ≠ p0 ∧ r ≠ p1 ∧ ev (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true ∧ St (ch a) r) → a ∈ Au) →
      (∀ g : Fin gates.length, ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ev (N + (g : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false ∧ (∀ t : Fin N, t ≠ i0 → ev (N + (g : ℕ)) (fun v : Fin N => decide (v ∉ L t)) = true) ∧
        ¬ ∀ e ∈ (gates.get g).inputs, (ev e (fun v : Fin N => decide (v = p0)) = true ∨ ev e (fun v : Fin N => decide (v = p1)) = true)) → g ∈ Xs) → q - 1 ≤ Au.card + Xs.card := by
  classical
  intro q N L i0 p0 p1 _hq _hN hsize hinter _hpair hne hp0 hp1 gs hG hlen hlt ev hev o0 hbase
    h0 _h1 hrim St hSt ch hch Au Xs hAu hXs
  have htop : ∀ i : Fin gs.length, 1 ≤ (gs.get i).inputs.length ∧
      ∀ a ∈ (gs.get i).inputs, a < N + i.val := fun i => ⟨hlen i, hlt i⟩
  have m0 : p0 ∈ ({p0, p1} : Finset (Fin N)) := Finset.mem_insert_self _ _
  have m1 : p1 ∈ ({p0, p1} : Finset (Fin N)) :=
    Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hTsub : ({p0, p1} : Finset (Fin N)) ⊆ L i0 := by
    intro x hx
    rcases Finset.mem_insert.mp hx with h | h
    · rw [h]; exact hp0
    · rw [Finset.mem_singleton.mp h]; exact hp1
  have offT : ∀ r ∈ L i0 \ ({p0, p1} : Finset (Fin N)), r ∈ L i0 ∧ r ≠ p0 ∧ r ≠ p1 := by
    intro r hr
    have h := Finset.mem_sdiff.mp hr
    exact ⟨h.1, fun e => h.2 (by rw [e]; exact m0), fun e => h.2 (by rw [e]; exact m1)⟩
  have stIn : ∀ r : Fin N, St r.val r := by
    intro r
    rw [hSt]
    intro Zs hz _
    exact hz
  have stOr : ∀ (i : Fin gs.length), (gs.get i).op = GateOp.or →
      ∀ e ∈ (gs.get i).inputs, ∀ r, St e r → St (N + i.val) r := by
    intro i hor e he r h
    rw [hSt] at h ⊢
    intro Zs hz hcl
    exact h Zs (hcl i hz hor e he) hcl
  have hXs' : ∀ g : Fin gs.length, ((gs.get g).op = GateOp.or ∧
      p42_V gs (N + g.val) (p42_base (L i0)) = false ∧
      (∀ t : Fin N, t ≠ i0 → p42_V gs (N + g.val) (p42_base (L t)) = true) ∧
      ¬ ∀ e ∈ (gs.get g).inputs, p42_C gs ({p0, p1} : Finset (Fin N)) e) → g ∈ Xs := by
    rintro g ⟨k1, k2, k3, k4⟩
    refine hXs g ⟨k1, (hev _ _).trans k2, fun t ht => (hev _ _).trans (k3 t ht),
      fun hall => k4 fun e he => ?_⟩
    rcases hall e he with h | h
    · exact ⟨p0, m0, (hev _ _).symm.trans h⟩
    · exact ⟨p1, m1, (hev _ _).symm.trans h⟩
  let Inv (w : ℕ) (D : Finset (Fin N)) : Prop :=
    p42_V gs w (p42_base (L i0)) = false →
      p42_Good (L i0 \ {p0, p1}) D (p42_S gs (L i0) w) (fun r => p42_U gs w r ∧ St w r) (p42_C gs {p0, p1} w)
  have grow : ∀ w D E, D ⊆ E → Inv w D → Inv w E := by
    intro w D E hDE hw hc
    exact (hw hc).mono hDE
  have init : ∀ w < N, Inv w ∅ := by
    intro w hw hc
    exact p42_primaryGood2 gs (L i0) {p0, p1} St stIn w hw hc
  have step (i : Fin gs.length) (D : Finset (Fin N))
      (prev : ∀ w < N + i.val, Inv w D) :
      ∃ E, D ⊆ E ∧ E.card ≤ D.card + (if i ∈ Au then 1 else 0) + (if i ∈ Xs then 1 else 0) ∧
        Inv (N + i.val) E := by
    by_cases hc : p42_V gs (N + i.val) (p42_base (L i0)) = false
    · rcases (hG (gs.get i) (List.get_mem gs i)).1 with hand | hor
      · by_cases unpaid : ∃ r ∈ L i0 \ ({p0, p1} : Finset (Fin N)),
            r ∉ D ∧ p42_S gs (L i0) (N + i.val) r
        · obtain ⟨r, hr, hd, hs⟩ := unpaid
          obtain ⟨hrM, ne0, ne1⟩ := offT r hr
          have hs' : ev (N + i.val) (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true :=
            (hev _ _).trans hs
          have carry : (gs.get i).op = GateOp.and ∧
              ev (N + i.val) (fun v : Fin N => decide (v ∉ L i0)) = false ∧
              ∃ r ∈ L i0, r ≠ p0 ∧ r ≠ p1 ∧
                ev (N + i.val) (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true :=
            ⟨hand, (hev _ _).trans hc, r, hrM, ne0, ne1, hs'⟩
          obtain ⟨hmem, hcold⟩ := hch i carry
          have hcold' : p42_V gs (ch i) (p42_base (L i0)) = false := (hev _ _).symm.trans hcold
          have sub : ∀ x : Fin N → Bool, p42_V gs (N + i.val) x = true → p42_V gs (ch i) x = true :=
            fun x hx => p42_andInputs gs hG htop i hand (ch i) hmem x hx
          have gch : p42_Good (L i0 \ {p0, p1}) D (p42_S gs (L i0) (ch i))
              (fun r => p42_U gs (ch i) r ∧ St (ch i) r) (p42_C gs {p0, p1} (ch i)) :=
            prev (ch i) (hlt i _ hmem) hcold'
          have hst : St (ch i) r := (gch.1 r hr hd (sub _ hs)).1.2
          have hin : i ∈ Au := hAu i ⟨carry, r, hrM, ne0, ne1, hs', hst⟩
          have no : ∀ t ∈ L i0 \ ({p0, p1} : Finset (Fin N)), t ∉ insert r D →
              ¬ p42_S gs (L i0) (N + i.val) t := by
            intro t ht he hts
            have htd : t ∉ D := fun hm => he (Finset.mem_insert_of_mem hm)
            exact he (Finset.mem_insert.mpr
              (Or.inl (gch.2 t ht htd (sub _ hts) r hr hd (sub _ hs))))
          refine ⟨insert r D, Finset.subset_insert _ _, ?_, fun _ => p42_Good.vac no⟩
          rw [Finset.card_insert_of_notMem hd, ite_eq_left hin]
          omega
        · exact ⟨D, Finset.Subset.rfl, by omega,
            fun _ => p42_Good.vac (fun r hr hd hs => unpaid ⟨r, hr, hd, hs⟩)⟩
      · rcases p42_gateCases gs hG htop i with
          ⟨a, ha, hin, heq⟩ | ⟨a, _, b, _, hop, _, _⟩ | ⟨a, ha, b, hb, hop, hin, heq⟩
        · refine ⟨D, Finset.Subset.rfl, by omega, fun _ => ?_⟩
          have ca : p42_V gs a (p42_base (L i0)) = false := (heq _).symm.trans hc
          have hmem : a ∈ (gs.get i).inputs := by rw [hin]; simp
          have ga : p42_Good (L i0 \ {p0, p1}) D (p42_S gs (L i0) a)
              (fun r => p42_U gs a r ∧ St a r) (p42_C gs {p0, p1} a) := prev a ha ca
          show p42_Good (L i0 \ {p0, p1}) D (p42_S gs (L i0) (N + i.val))
            (fun r => p42_U gs (N + i.val) r ∧ St (N + i.val) r) (p42_C gs {p0, p1} (N + i.val))
          refine ga.imp (fun r h => (heq _).symm.trans h)
            (fun r h => ⟨(heq _).trans h.1, stOr i hor a hmem r h.2⟩) ?_
          rintro ⟨x, hx, ux⟩
          exact ⟨x, hx, (heq _).symm.trans ux⟩
        · rw [hor] at hop
          cases hop
        · have ab : p42_V gs a (p42_base (L i0)) = false ∧ p42_V gs b (p42_base (L i0)) = false := by
            simpa only [Bool.or_eq_false_iff] using (heq (p42_base (L i0))).symm.trans hc
          obtain ⟨E, hDE, hcard, hg⟩ := p42_realOrUpdate St hG hinter hTsub hXs' i a b hop hin hc heq
            (stOr i hor a (by rw [hin]; simp)) (stOr i hor b (by rw [hin]; simp))
            (prev a ha ab.1) (prev b hb ab.2)
          exact ⟨E, hDE, by omega, fun _ => hg⟩
    · exact ⟨D, fun _ h => h, by omega, fun h => (hc h).elim⟩
  obtain ⟨D, hd, hgood⟩ := p42_prefixBudget N gs.length Au Xs Inv grow init step
  have s0 : p42_V gs o0 (p42_single p0) = true := (hev _ _).symm.trans h0
  have bounded : o0 < N + gs.length := by
    by_contra! he
    exact Bool.false_ne_true ((p42_missingV gs o0 he (p42_single p0)).symm.trans s0)
  have core : p42_C gs ({p0, p1} : Finset (Fin N)) o0 := ⟨p0, m0, s0⟩
  have cold : p42_V gs o0 (p42_base (L i0)) = false := (hev _ _).symm.trans hbase
  have gout : p42_Good (L i0 \ {p0, p1}) D (p42_S gs (L i0) o0)
      (fun r => p42_U gs o0 r ∧ St o0 r) (p42_C gs {p0, p1} o0) := hgood o0 bounded cold
  have covered : L i0 \ ({p0, p1} : Finset (Fin N)) ⊆ D := by
    intro r hr
    by_contra hd'
    obtain ⟨hrM, ne0, ne1⟩ := offT r hr
    have sens : p42_S gs (L i0) o0 r := (hev _ _).symm.trans (hrim r hrM ne0 ne1)
    exact (gout.1 r hr hd' sens).2 core
  have count := (Finset.card_le_card covered).trans hd
  rw [Finset.card_sdiff_of_subset hTsub, hsize, Finset.card_pair hne] at count
  omega

def EV {N : ℕ} (gates : List Gate) (w : ℕ) (x : Fin N → Bool) : Bool :=
  Circuit.eval ⟨gates, w⟩ (List.ofFn x)

lemma EV_val {N : ℕ} (gates : List Gate) (w : ℕ) (x : Fin N → Bool) :
    EV gates w x = b_value ⟨gates, 0⟩ x w := rfl

lemma EV_in {N : ℕ} (gates : List Gate) (p : Fin N) (x : Fin N → Bool) :
    EV gates (p : ℕ) x = x p := by
  rw [EV_val]
  exact b_input_value _ x p

lemma EV_miss {N : ℕ} (gates : List Gate) (w : ℕ) (x : Fin N → Bool)
    (hw : N + gates.length ≤ w) : EV gates w x = false := by
  rw [EV_val]
  exact b_missing_value _ x w hw

lemma EV_or {N : ℕ} (gates : List Gate)
    (htopo : ∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ))
    (g : Fin gates.length) (hop : (gates.get g).op = GateOp.or) (x : Fin N → Bool) :
    EV gates (N + (g : ℕ)) x = true ↔ ∃ e ∈ (gates.get g).inputs, EV gates e x = true := by
  show b_value ⟨gates, 0⟩ x (N + (g : ℕ)) = true ↔ _
  refine (b_or_value (n := N) ⟨gates, 0⟩ (g : ℕ) g.2 hop x).trans ⟨?_, ?_⟩
  · rintro ⟨r, hr, _, hv⟩
    exact ⟨r, hr, hv⟩
  · rintro ⟨r, hr, hv⟩
    exact ⟨r, hr, htopo g r hr, hv⟩

lemma EV_and {N : ℕ} (gates : List Gate)
    (htopo : ∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ))
    (g : Fin gates.length) (hop : (gates.get g).op = GateOp.and) (x : Fin N → Bool) :
    EV gates (N + (g : ℕ)) x = true ↔ ∀ e ∈ (gates.get g).inputs, EV gates e x = true := by
  show b_value ⟨gates, 0⟩ x (N + (g : ℕ)) = true ↔ _
  refine (b_and_value (n := N) ⟨gates, 0⟩ (g : ℕ) g.2 hop x).trans ⟨?_, ?_⟩
  · intro h r hr
    exact (h r hr).2
  · intro h r hr
    exact ⟨htopo g r hr, h r hr⟩

lemma EV_mono {N : ℕ} (gates : List Gate)
    (hg : ∀ gt ∈ gates, (gt.op = GateOp.and ∨ gt.op = GateOp.or) ∧ gt.inputs.length ≤ 2)
    (x y : Fin N → Bool) (h : ∀ v, x v = true → y v = true) (w : ℕ) :
    EV gates w x = true → EV gates w y = true :=
  b_mono ⟨gates, 0⟩ hg x y h w

lemma EV_or_false {N : ℕ} (gates : List Gate)
    (htopo : ∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ))
    (g : Fin gates.length) (hop : (gates.get g).op = GateOp.or) (x : Fin N → Bool)
    (h : EV gates (N + (g : ℕ)) x = false) : ∀ e ∈ (gates.get g).inputs, EV gates e x = false := by
  intro e he
  by_contra hne
  have ht : EV gates e x = true := by simpa using hne
  have h2 := (EV_or gates htopo g hop x).mpr ⟨e, he, ht⟩
  exact Bool.false_ne_true (h.symm.trans h2)

lemma EV_and_false {N : ℕ} (gates : List Gate)
    (htopo : ∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ))
    (g : Fin gates.length) (hop : (gates.get g).op = GateOp.and) (x : Fin N → Bool)
    (h : EV gates (N + (g : ℕ)) x = false) : ∃ e ∈ (gates.get g).inputs, EV gates e x = false := by
  by_contra hne
  have h2 : EV gates (N + (g : ℕ)) x = true := (EV_and gates htopo g hop x).mpr (fun e he => by
    by_contra h3
    exact hne ⟨e, he, by simpa using h3⟩)
  exact Bool.false_ne_true (h.symm.trans h2)

lemma three_in_two (l : List ℕ) (hl : l.length ≤ 2) (a b c : ℕ) (ha : a ∈ l) (hb : b ∈ l)
    (hc : c ∈ l) (hab : a ≠ b) (hac : a ≠ c) : b = c := by
  match l, hl, ha, hb, hc with
  | [], _, ha, _, _ => simp at ha
  | [x], _, ha, hb, hc =>
    simp only [List.mem_singleton] at ha hb hc
    omega
  | [x, y], _, ha, hb, hc =>
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha hb hc
    omega
  | _ :: _ :: _ :: _, hl, _, _, _ =>
    simp only [List.length_cons] at hl
    omega

def TT {N : ℕ} (L : Fin N → Finset (Fin N)) (p0 p1 t p v : Fin N) : Bool :=
  decide (v = p ∨ (p0 ∉ L t ∧ p ≠ p1 ∧ v = p0) ∨ (p0 ∈ L t ∧ p1 ∉ L t ∧ p ≠ p0 ∧ v = p1) ∨
      (p0 ∈ L t ∧ p1 ∈ L t ∧ p ≠ p0 ∧ p ≠ p1 ∧ v ∉ L t))

lemma TT_iff {N : ℕ} (L : Fin N → Finset (Fin N)) (p0 p1 t p v : Fin N) :
    TT L p0 p1 t p v = true ↔ (v = p ∨ (p0 ∉ L t ∧ p ≠ p1 ∧ v = p0) ∨ (p0 ∈ L t ∧ p1 ∉ L t ∧ p ≠ p0 ∧ v = p1) ∨
      (p0 ∈ L t ∧ p1 ∈ L t ∧ p ≠ p0 ∧ p ≠ p1 ∧ v ∉ L t)) := by
  unfold TT
  exact decide_eq_true_iff

lemma TT_on {N : ℕ} (L : Fin N → Finset (Fin N)) (p0 p1 t a v : Fin N) (hv : v ∈ L t)
    (h : TT L p0 p1 t a v = true) : v = a := by
  rcases (TT_iff L p0 p1 t a v).mp h with h | ⟨h1, _, h3⟩ | ⟨_, h2, _, h4⟩ | ⟨_, _, _, _, h5⟩
  · exact h
  · exact absurd (h3 ▸ hv) h1
  · exact absurd (h4 ▸ hv) h2
  · exact absurd hv h5

def Plane (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N) : Prop :=
  3 ≤ q ∧ N = q ^ 2 + q + 1 ∧ (∀ i : Fin N, (L i).card = q + 1) ∧
    (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) ∧
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) ∧ p0 ≠ p1 ∧ p0 ∈ L i0 ∧ p1 ∈ L i0

def Ckt (N : ℕ) (gates : List Gate) : Prop :=
  (∀ gt ∈ gates, (gt.op = GateOp.and ∨ gt.op = GateOp.or) ∧ gt.inputs.length ≤ 2) ∧
    (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) ∧
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ))

def Good {N : ℕ} (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N) (gates : List Gate)
    (o : Fin N → ℕ) : Prop :=
  ∀ (t : Fin N) (x : Fin N → Bool), (x p0 = true ∨ x p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → x u = true) →
    EV gates (o t) x = decide (∃ v ∈ L t, x v = true)

def Cl {N : ℕ} (L : Fin N → Finset (Fin N)) (T : Fin N → Fin N → Fin N → Bool) (gates : List Gate)
    (t : Fin N) (j : ℕ) (X : Finset (Fin N)) : Prop :=
  ∀ i : Fin gates.length, (i : ℕ) < j → (gates.get i).op = GateOp.or →
    EV gates (N + (i : ℕ)) (fun v : Fin N => decide (v ∉ L t)) = false →
    ∀ c1 c2 : ℕ, (gates.get i).inputs = [c1, c2] → ∀ s ∈ L t, ∀ s' ∈ L t,
    (EV gates c1 (T t s) = true ∨ EV gates c2 (T t s) = true) →
    (EV gates c1 (T t s') = true ∨ EV gates c2 (T t s') = true) → (s ∈ X ↔ s' ∈ X)

def Eqv {N : ℕ} (L : Fin N → Finset (Fin N)) (T : Fin N → Fin N → Fin N → Bool) (gates : List Gate)
    (t : Fin N) (j : ℕ) (a b : Fin N) : Prop :=
  ∀ X : Finset (Fin N), Cl L T gates t j X → (a ∈ X ↔ b ∈ X)

def Mg {N : ℕ} (L : Fin N → Finset (Fin N)) (T : Fin N → Fin N → Fin N → Bool) (gates : List Gate)
    (t : Fin N) (g : Fin gates.length) : Prop :=
  (gates.get g).op = GateOp.or ∧ EV gates (N + (g : ℕ)) (fun v : Fin N => decide (v ∉ L t)) = false ∧
        ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ L t, ∃ r' ∈ L t, EV gates w1 (T t r) = true ∧ EV gates w2 (T t r') = true ∧
        ∃ X : Finset (Fin N), r ∈ X ∧ r' ∉ X ∧ (∀ i : Fin gates.length, i < g → (gates.get i).op = GateOp.or → EV gates (N + (i : ℕ)) (fun v : Fin N => decide (v ∉ L t)) = false →
          ∀ c1 c2 : ℕ, (gates.get i).inputs = [c1, c2] → ∀ s ∈ L t, ∀ s' ∈ L t,
          (EV gates c1 (T t s) = true ∨ EV gates c2 (T t s) = true) → (EV gates c1 (T t s') = true ∨ EV gates c2 (T t s') = true) → (s ∈ X ↔ s' ∈ X))

def TS {N : ℕ} (L : Fin N → Finset (Fin N)) (T : Fin N → Fin N → Fin N → Bool) (gates : List Gate)
    (l m : Fin N) (w : ℕ) : Prop :=
  EV gates w (fun v : Fin N => decide (v ∉ L l)) = false ∧
    EV gates w (fun v : Fin N => decide (v ∉ L m)) = false ∧
    (∃ p ∈ L l, EV gates w (T l p) = true) ∧ ∃ p ∈ L m, EV gates w (T m p) = true

def SH {N : ℕ} (L : Fin N → Finset (Fin N)) (T : Fin N → Fin N → Fin N → Bool) (gates : List Gate)
    (l m : Fin N) (h : Fin gates.length) : Prop :=
  TS L T gates l m (N + (h : ℕ)) ∧ ∀ e ∈ (gates.get h).inputs, ¬ TS L T gates l m e

def Node {N : ℕ} (L : Fin N → Finset (Fin N)) (T : Fin N → Fin N → Fin N → Bool) (gates : List Gate)
    (l m : Fin N) (ν : ℕ) : Prop :=
  (∃ c : Fin N, c ∈ L l ∧ c ∈ L m ∧ ν = (c : ℕ)) ∨
    ∃ h : Fin gates.length, ν = N + (h : ℕ) ∧ SH L T gates l m h

def Rt {N : ℕ} (L : Fin N → Finset (Fin N)) (T : Fin N → Fin N → Fin N → Bool) (gates : List Gate)
    (l m : Fin N) (j : ℕ) (s : Fin N) (ν : ℕ) : Prop :=
  Node L T gates l m ν ∧ ν < N + j ∧ ∃ u ∈ L l, EV gates ν (T l u) = true ∧ Eqv L T gates l j u s

def Pk {N : ℕ} (L : Fin N → Finset (Fin N)) (T : Fin N → Fin N → Fin N → Bool) (gates : List Gate)
    (l m : Fin N) (g h : Fin gates.length) : Prop :=
  SH L T gates l m h ∧ (h : ℕ) < (g : ℕ) ∧
    (∃ s : Fin N, Rt L T gates l m (g : ℕ) s (N + (h : ℕ)) ∧
      ∀ ν : ℕ, Rt L T gates l m (g : ℕ) s ν → N + (h : ℕ) ≤ ν) ∧
    ∃ ν' : ℕ, Node L T gates l m ν' ∧ ν' < N + (h : ℕ) ∧ ∃ u' ∈ L l, EV gates ν' (T l u') = true ∧
      ∃ u0 ∈ L l, EV gates (N + (h : ℕ)) (T l u0) = true ∧ Eqv L T gates l ((g : ℕ) + 1) u' u0

def St {N : ℕ} (gates : List Gate) (w : ℕ) (p : Fin N) : Prop :=
  ∀ Zs : Set ℕ, w ∈ Zs → (∀ k : Fin gates.length, N + (k : ℕ) ∈ Zs → (gates.get k).op = GateOp.or → ∀ e ∈ (gates.get k).inputs, e ∈ Zs) → (p : ℕ) ∈ Zs

def Dl {N : ℕ} (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N) (gates : List Gate)
    (ch : Fin gates.length → ℕ) (a : Fin gates.length) : Prop :=
  ((gates.get a).op = GateOp.and ∧ EV gates (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false ∧ ∃ r ∈ L i0, r ≠ p0 ∧ r ≠ p1 ∧ EV gates (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true) ∧ ∃ r ∈ L i0, r ≠ p0 ∧ r ≠ p1 ∧ EV gates (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true ∧ St gates (ch a) r

def Xst {N : ℕ} (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N) (gates : List Gate)
    (g : Fin gates.length) : Prop :=
  (gates.get g).op = GateOp.or ∧ EV gates (N + (g : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false ∧ (∀ t : Fin N, t ≠ i0 → EV gates (N + (g : ℕ)) (fun v : Fin N => decide (v ∉ L t)) = true) ∧
        ¬ ∀ e ∈ (gates.get g).inputs, (EV gates e (fun v : Fin N => decide (v = p0)) = true ∨ EV gates e (fun v : Fin N => decide (v = p1)) = true)

def KindM {N : ℕ} (L : Fin N → Finset (Fin N)) (T : Fin N → Fin N → Fin N → Bool) (gates : List Gate)
    (p0 p1 t : Fin N) (e : Fin gates.length) : Prop :=
  Mg L T gates t e ∧
    ((p1 ∈ L t ∧ p0 ∉ L t) → ∀ l : Fin N, (p0 ∈ L l ∧ p1 ∉ L l) → ¬ Mg L T gates l e)

def KindS {N : ℕ} (L : Fin N → Finset (Fin N)) (T : Fin N → Fin N → Fin N → Bool) (gates : List Gate)
    (p0 p1 t : Fin N) (e : Fin gates.length) : Prop :=
  (p1 ∈ L t ∧ p0 ∉ L t) ∧ ∃ l : Fin N, (p0 ∈ L l ∧ p1 ∉ L l) ∧ SH L T gates l t e

lemma Eqv_refl {N : ℕ} {L : Fin N → Finset (Fin N)} {T : Fin N → Fin N → Fin N → Bool}
    {gates : List Gate} {t : Fin N} {j : ℕ} {a : Fin N} : Eqv L T gates t j a a :=
  fun _ _ => Iff.rfl

lemma Eqv_symm {N : ℕ} {L : Fin N → Finset (Fin N)} {T : Fin N → Fin N → Fin N → Bool}
    {gates : List Gate} {t : Fin N} {j : ℕ} {a b : Fin N} (h : Eqv L T gates t j a b) :
    Eqv L T gates t j b a :=
  fun X hX => (h X hX).symm

lemma Eqv_trans {N : ℕ} {L : Fin N → Finset (Fin N)} {T : Fin N → Fin N → Fin N → Bool}
    {gates : List Gate} {t : Fin N} {j : ℕ} {a b c : Fin N} (h1 : Eqv L T gates t j a b)
    (h2 : Eqv L T gates t j b c) : Eqv L T gates t j a c :=
  fun X hX => (h1 X hX).trans (h2 X hX)

lemma Eqv_mono {N : ℕ} {L : Fin N → Finset (Fin N)} {T : Fin N → Fin N → Fin N → Bool}
    {gates : List Gate} {t : Fin N} {j j' : ℕ} {a b : Fin N} (hjj : j ≤ j')
    (h : Eqv L T gates t j a b) : Eqv L T gates t j' a b :=
  fun X hX => h X (fun i hi => hX i (lt_of_lt_of_le hi hjj))

lemma Pk_sh {N : ℕ} {L : Fin N → Finset (Fin N)} {T : Fin N → Fin N → Fin N → Bool}
    {gates : List Gate} {l m : Fin N} {g h : Fin gates.length} (hp : Pk L T gates l m g h) :
    SH L T gates l m h := by
  obtain ⟨h1, _⟩ := hp
  exact h1

lemma Mg_live {N : ℕ} {L : Fin N → Finset (Fin N)} {T : Fin N → Fin N → Fin N → Bool}
    {gates : List Gate} {t : Fin N} {g : Fin gates.length} (hM : Mg L T gates t g) :
    EV gates (N + (g : ℕ)) (fun v : Fin N => decide (v ∉ L t)) = false := by
  obtain ⟨_, h, _⟩ := hM
  exact h

lemma Mg_or {N : ℕ} {L : Fin N → Finset (Fin N)} {T : Fin N → Fin N → Fin N → Bool}
    {gates : List Gate} {t : Fin N} {g : Fin gates.length} (hM : Mg L T gates t g) :
    (gates.get g).op = GateOp.or := by
  obtain ⟨h, _⟩ := hM
  exact h


variable {q N : ℕ} {L : Fin N → Finset (Fin N)} {i0 p0 p1 : Fin N} {gates : List Gate}

lemma W33 (hP : Plane q N L i0 p0 p1) (t u : Fin N) (ht : t ≠ i0) (hu : u ≠ i0) (htu : t ≠ u) :
    ((∃ p ∈ L t \ L u, ∃ v ∈ L u, TT L p0 p1 t p v = true) ∧ (∃ p ∈ L u \ L t, ∃ v ∈ L t, TT L p0 p1 u p v = true)) ↔
      (((p0 ∈ L t ∧ p1 ∉ L t) ∧ (p1 ∈ L u ∧ p0 ∉ L u)) ∨ ((p1 ∈ L t ∧ p0 ∉ L t) ∧ (p0 ∈ L u ∧ p1 ∉ L u))) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hP
  exact p33_main_aux q N L i0 p0 p1 a1 a2 a3 a4 a5 a6 a7 a8 (TT L p0 p1)
    (fun t p v => TT_iff L p0 p1 t p v) t u ht hu htu

lemma W34 (hP : Plane q N L i0 p0 p1) (hC : Ckt N gates) (w : ℕ) (t u : Fin N) (htu : t ≠ u)
    (hzt : EV gates w (fun v : Fin N => decide (v ∉ L t)) = false)
    (hzu : EV gates w (fun v : Fin N => decide (v ∉ L u)) = false)
    (h2t : 2 ≤ ((L t).filter (fun p => EV gates w (TT L p0 p1 t p) = true)).card)
    (h2u : 2 ≤ ((L u).filter (fun p => EV gates w (TT L p0 p1 u p) = true)).card) :
    (∃ p ∈ L t \ L u, ∃ v ∈ L u, TT L p0 p1 t p v = true) ∧ (∃ p ∈ L u \ L t, ∃ v ∈ L t, TT L p0 p1 u p v = true) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hP
  obtain ⟨c1, c2, c3⟩ := hC
  exact p34_main_aux q N L i0 p0 p1 a1 a2 a3 a4 a5 a6 a7 a8 (TT L p0 p1)
    (fun t p v => TT_iff L p0 p1 t p v) gates c1 c2 c3 (EV gates) (fun _ _ => rfl) w t u htu hzt hzu h2t h2u

lemma W35a (hP : Plane q N L i0 p0 p1) (hC : Ckt N gates) (o : Fin N → ℕ)
    (hgood : Good L i0 p0 p1 gates o) (t : Fin N) (g : Fin gates.length)
    (hz : EV gates (N + (g : ℕ)) (fun v : Fin N => decide (v ∉ L t)) = false) (a b : Fin N)
    (ha : a ∈ L t) (hb : b ∈ L t) (hta : EV gates (N + (g : ℕ)) (TT L p0 p1 t a) = true)
    (htb : EV gates (N + (g : ℕ)) (TT L p0 p1 t b) = true) :
    Eqv L (TT L p0 p1) gates t ((g : ℕ) + 1) a b := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hP
  obtain ⟨c1, c2, c3⟩ := hC
  intro X hX
  exact (p35_main_aux q N L i0 p0 p1 a1 a2 a3 a4 a5 a6 a7 a8 (TT L p0 p1)
    (fun t p v => TT_iff L p0 p1 t p v) gates c1 c2 c3 (EV gates) (fun _ _ => rfl) o hgood
    (Mg L (TT L p0 p1) gates) (fun _ _ => Iff.rfl) t).1 g hz a ha b hb hta htb X
    (fun i hi => hX i (Nat.lt_succ_of_le (Fin.le_def.mp hi)))

lemma W35b (hP : Plane q N L i0 p0 p1) (hC : Ckt N gates) (o : Fin N → ℕ)
    (hgood : Good L i0 p0 p1 gates o) (t : Fin N) (I : Finset (Fin gates.length))
    (hI : ∀ g : Fin gates.length, g ∈ I ↔ Mg L (TT L p0 p1) gates t g) : I.card = q := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hP
  obtain ⟨c1, c2, c3⟩ := hC
  exact (p35_main_aux q N L i0 p0 p1 a1 a2 a3 a4 a5 a6 a7 a8 (TT L p0 p1)
    (fun t p v => TT_iff L p0 p1 t p v) gates c1 c2 c3 (EV gates) (fun _ _ => rfl) o hgood
    (Mg L (TT L p0 p1) gates) (fun _ _ => Iff.rfl) t).2 I hI

lemma W36a (hP : Plane q N L i0 p0 p1) (hC : Ckt N gates) (w : ℕ) (m l : Fin N)
    (hm : p1 ∈ L m ∧ p0 ∉ L m) (hl : p0 ∈ L l ∧ p1 ∉ L l)
    (hz : EV gates w (fun v : Fin N => decide (v ∉ L m)) = false)
    (hex : ∃ p ∈ L l, EV gates w (TT L p0 p1 l p) = true) (l' : Fin N)
    (hl' : p0 ∈ L l' ∧ p1 ∉ L l') (hne : l' ≠ l) :
    EV gates w (fun v : Fin N => decide (v ∉ L l')) = true := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hP
  obtain ⟨c1, c2, c3⟩ := hC
  exact (p36_main_aux q N L i0 p0 p1 a1 a2 a3 a4 a5 a6 a7 a8 (TT L p0 p1)
    (fun t p v => TT_iff L p0 p1 t p v) gates c1 c2 c3 (EV gates) (fun _ _ => rfl) w).1
    m l hm hl hz hex l' hl' hne

lemma W36b (hP : Plane q N L i0 p0 p1) (hC : Ckt N gates) (w : ℕ) (l m : Fin N)
    (hl : p0 ∈ L l ∧ p1 ∉ L l) (hm : p1 ∈ L m ∧ p0 ∉ L m)
    (hz : EV gates w (fun v : Fin N => decide (v ∉ L l)) = false)
    (hex : ∃ p ∈ L m, EV gates w (TT L p0 p1 m p) = true) (m' : Fin N)
    (hm' : p1 ∈ L m' ∧ p0 ∉ L m') (hne : m' ≠ m) :
    EV gates w (fun v : Fin N => decide (v ∉ L m')) = true := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hP
  obtain ⟨c1, c2, c3⟩ := hC
  exact (p36_main_aux q N L i0 p0 p1 a1 a2 a3 a4 a5 a6 a7 a8 (TT L p0 p1)
    (fun t p v => TT_iff L p0 p1 t p v) gates c1 c2 c3 (EV gates) (fun _ _ => rfl) w).2.1
    l m hl hm hz hex m' hm' hne

lemma W36c (hP : Plane q N L i0 p0 p1) (hC : Ckt N gates) (w : ℕ) (m M : Fin N)
    (hm : p1 ∈ L m ∧ p0 ∉ L m)
    (hz : EV gates w (fun v : Fin N => decide (v ∉ L m)) = false)
    (hM : p0 ∉ L M ∧ p1 ∉ L M) :
    ((L M).filter (fun p => EV gates w (TT L p0 p1 M p) = true)).card ≤ 1 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hP
  obtain ⟨c1, c2, c3⟩ := hC
  exact (p36_main_aux q N L i0 p0 p1 a1 a2 a3 a4 a5 a6 a7 a8 (TT L p0 p1)
    (fun t p v => TT_iff L p0 p1 t p v) gates c1 c2 c3 (EV gates) (fun _ _ => rfl) w).2.2
    m M hm hz hM

lemma W39 (hP : Plane q N L i0 p0 p1) (hC : Ckt N gates) (u : ℕ)
    (hz : EV gates u (fun v : Fin N => decide (v ∉ L i0)) = false) (t y : Fin N) (ht : t ≠ i0)
    (hzt : EV gates u (fun v : Fin N => decide (v ∉ L t)) = false) (hmeet : L t ∩ L i0 = {y})
    (p : Fin N) (hst : St gates u p) : p = y := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hP
  obtain ⟨c1, c2, c3⟩ := hC
  have hsub : ({p0, p1} : Finset (Fin N)) ⊆ L i0 := by
    intro x hx
    rcases Finset.mem_insert.mp hx with hx | hx
    · rw [hx]
      exact a7
    · rw [Finset.mem_singleton.mp hx]
      exact a8
  exact (p39_main_aux q 2 N L i0 {p0, p1} a1 (by norm_num) (by omega) a2 a3 a4 a5 hsub
    (Finset.card_pair a6) gates u c1 c2 c3 hz t y ht hzt hmeet).1 p hst

lemma W42 (hP : Plane q N L i0 p0 p1) (hC : Ckt N gates) (o0 : ℕ)
    (hz : EV gates o0 (fun v : Fin N => decide (v ∉ L i0)) = false)
    (h0 : EV gates o0 (fun v : Fin N => decide (v = p0)) = true)
    (h1 : EV gates o0 (fun v : Fin N => decide (v = p1)) = true)
    (hrim : ∀ r ∈ L i0, r ≠ p0 → r ≠ p1 → EV gates o0 (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true)
    (ch : Fin gates.length → ℕ)
    (hch : ∀ a : Fin gates.length, ((gates.get a).op = GateOp.and ∧ EV gates (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false ∧ ∃ r ∈ L i0, r ≠ p0 ∧ r ≠ p1 ∧ EV gates (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true) → ch a ∈ (gates.get a).inputs ∧ EV gates (ch a) (fun v : Fin N => decide (v ∉ L i0)) = false)
    (Au Xs : Finset (Fin gates.length))
    (hAu : ∀ a : Fin gates.length, Dl L i0 p0 p1 gates ch a → a ∈ Au)
    (hXs : ∀ g : Fin gates.length, Xst L i0 p0 p1 gates g → g ∈ Xs) :
    q - 1 ≤ Au.card + Xs.card := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hP
  obtain ⟨c1, c2, c3⟩ := hC
  exact p42_main_aux q N L i0 p0 p1 a1 a2 a3 a4 a5 a6 a7 a8 gates c1 c2 c3 (EV gates)
    (fun _ _ => rfl) o0 hz h0 h1 hrim (St gates) (fun _ _ => Iff.rfl) ch hch Au Xs hAu hXs

lemma two_pts (hP : Plane q N L i0 p0 p1) (t u : Fin N) (htu : t ≠ u) (a b : Fin N)
    (hat : a ∈ L t) (hau : a ∈ L u) (hbt : b ∈ L t) (hbu : b ∈ L u) : a = b :=
  Finset.card_le_one.mp (le_of_eq (hP.2.2.2.1 t u htu)) a (Finset.mem_inter.mpr ⟨hat, hau⟩) b
    (Finset.mem_inter.mpr ⟨hbt, hbu⟩)

lemma not_both (hP : Plane q N L i0 p0 p1) (t : Fin N) (ht : t ≠ i0) :
    ¬ (p0 ∈ L t ∧ p1 ∈ L t) := fun h =>
  hP.2.2.2.2.2.1 (two_pts hP t i0 ht p0 p1 h.1 hP.2.2.2.2.2.2.1 h.2 hP.2.2.2.2.2.2.2)

lemma meet_eq (hP : Plane q N L i0 p0 p1) (t u : Fin N) (htu : t ≠ u) (y : Fin N)
    (hyt : y ∈ L t) (hyu : y ∈ L u) : L t ∩ L u = {y} := by
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp (hP.2.2.2.1 t u htu)
  have h : y ∈ L t ∩ L u := Finset.mem_inter.mpr ⟨hyt, hyu⟩
  rw [hc] at h ⊢
  rw [Finset.mem_singleton.mp h]

lemma C1 (hP : Plane q N L i0 p0 p1) (hC : Ckt N gates) (o : Fin N → ℕ)
    (hgood : Good L i0 p0 p1 gates o) (t : Fin N) (j w : ℕ) (hw : w < N + j)
    (hz : EV gates w (fun v : Fin N => decide (v ∉ L t)) = false) (a b : Fin N)
    (ha : a ∈ L t) (hb : b ∈ L t) (hta : EV gates w (TT L p0 p1 t a) = true)
    (htb : EV gates w (TT L p0 p1 t b) = true) : Eqv L (TT L p0 p1) gates t j a b := by
  by_cases hin : w < N
  · have hz' : decide ((⟨w, hin⟩ : Fin N) ∉ L t) = false :=
      (EV_in gates (⟨w, hin⟩ : Fin N) _).symm.trans hz
    have hp : (⟨w, hin⟩ : Fin N) ∈ L t := by simpa using hz'
    have h1 : (⟨w, hin⟩ : Fin N) = a :=
      TT_on L p0 p1 t a _ hp ((EV_in gates (⟨w, hin⟩ : Fin N) _).symm.trans hta)
    have h2 : (⟨w, hin⟩ : Fin N) = b :=
      TT_on L p0 p1 t b _ hp ((EV_in gates (⟨w, hin⟩ : Fin N) _).symm.trans htb)
    have hab : a = b := h1.symm.trans h2
    rw [hab]
    exact Eqv_refl
  · by_cases hlen : w < N + gates.length
    · obtain ⟨k, rfl⟩ : ∃ k, w = N + k := ⟨w - N, by omega⟩
      have hk : k < gates.length := by omega
      exact Eqv_mono (show k + 1 ≤ j by omega)
        (W35a hP hC o hgood t ⟨k, hk⟩ hz a b ha hb hta htb)
    · rw [EV_miss gates w _ (by omega)] at hta
      exact absurd hta (by decide)

lemma Node_live {l m : Fin N} {ν : ℕ} (h : Node L (TT L p0 p1) gates l m ν) :
    EV gates ν (fun v : Fin N => decide (v ∉ L l)) = false := by
  rcases h with ⟨c, hcl, _, hν⟩ | ⟨h, hν, hs⟩
  · rw [hν, EV_in]
    simpa using hcl
  · rw [hν]
    exact hs.1.1

lemma descent (hP : Plane q N L i0 p0 p1) (hC : Ckt N gates) (o : Fin N → ℕ)
    (hgood : Good L i0 p0 p1 gates o) (l m : Fin N) (j : ℕ) :
    ∀ w : ℕ, TS L (TT L p0 p1) gates l m w → w < N + j →
      ∃ ν : ℕ, Node L (TT L p0 p1) gates l m ν ∧ ν ≤ w ∧ ∃ s ∈ L l,
        EV gates ν (TT L p0 p1 l s) = true ∧ ∃ s' ∈ L l, EV gates w (TT L p0 p1 l s') = true ∧
          Eqv L (TT L p0 p1) gates l j s s' := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hts hw
    obtain ⟨hzl, hzm, ⟨s0, hs0, hs0t⟩, hWm⟩ := hts
    by_cases hin : w < N
    · have hzl' : decide ((⟨w, hin⟩ : Fin N) ∉ L l) = false :=
        (EV_in gates (⟨w, hin⟩ : Fin N) _).symm.trans hzl
      have hzm' : decide ((⟨w, hin⟩ : Fin N) ∉ L m) = false :=
        (EV_in gates (⟨w, hin⟩ : Fin N) _).symm.trans hzm
      have hpl : (⟨w, hin⟩ : Fin N) ∈ L l := by simpa using hzl'
      have hpm : (⟨w, hin⟩ : Fin N) ∈ L m := by simpa using hzm'
      exact ⟨w, Or.inl ⟨⟨w, hin⟩, hpl, hpm, rfl⟩, le_refl _, s0, hs0, hs0t, s0, hs0, hs0t,
        Eqv_refl⟩
    · by_cases hlen : w < N + gates.length
      · obtain ⟨k, rfl⟩ : ∃ k, w = N + k := ⟨w - N, by omega⟩
        have hk : k < gates.length := by omega
        by_cases hno : ∀ e ∈ (gates.get ⟨k, hk⟩).inputs, ¬ TS L (TT L p0 p1) gates l m e
        · exact ⟨N + k, Or.inr ⟨⟨k, hk⟩, rfl, ⟨hzl, hzm, ⟨s0, hs0, hs0t⟩, hWm⟩, hno⟩, le_refl _,
            s0, hs0, hs0t, s0, hs0, hs0t, Eqv_refl⟩
        · push_neg at hno
          obtain ⟨e, he, hte⟩ := hno
          have helt : e < N + k := hC.2.2 ⟨k, hk⟩ e he
          obtain ⟨ν, hν, hνe, s, hs, hsν, s2, hs2, hs2e, heq⟩ := ih e helt hte (by omega)
          rcases (hC.1 _ (List.getElem_mem hk)).1 with hand | hor
          · have hs0e : EV gates e (TT L p0 p1 l s0) = true :=
              (EV_and gates hC.2.2 ⟨k, hk⟩ hand _).mp hs0t e he
            have hc := C1 hP hC o hgood l j e (by omega) hte.1 s2 s0 hs2 hs0 hs2e hs0e
            exact ⟨ν, hν, by omega, s, hs, hsν, s0, hs0, hs0t, Eqv_trans heq hc⟩
          · have hv : EV gates (N + k) (TT L p0 p1 l s2) = true :=
              (EV_or gates hC.2.2 ⟨k, hk⟩ hor _).mpr ⟨e, he, hs2e⟩
            exact ⟨ν, hν, by omega, s, hs, hsν, s2, hs2, hv, heq⟩
      · rw [EV_miss gates w _ (by omega)] at hs0t
        exact absurd hs0t (by decide)

lemma Pk_inj (hP : Plane q N L i0 p0 p1) (hC : Ckt N gates) (o : Fin N → ℕ)
    (hgood : Good L i0 p0 p1 gates o) (l m : Fin N) (g g' h : Fin gates.length)
    (hlt : (g : ℕ) < (g' : ℕ)) (h1 : Pk L (TT L p0 p1) gates l m g h)
    (h2 : Pk L (TT L p0 p1) gates l m g' h) : False := by
  obtain ⟨⟨⟨hzl, _, _, _⟩, _⟩, hhg, _, ν', hν', hν'h, u', hu', hu'ν, u0, hu0, hu0h, hequ⟩ := h1
  obtain ⟨_, hhg', ⟨s, ⟨_, _, u, hu, huh, hus⟩, hmin⟩, _⟩ := h2
  have e1 : Eqv L (TT L p0 p1) gates l (g' : ℕ) u' u0 := Eqv_mono (by omega) hequ
  have e2 : Eqv L (TT L p0 p1) gates l (g' : ℕ) u0 u :=
    C1 hP hC o hgood l (g' : ℕ) (N + (h : ℕ)) (by omega) hzl u0 u hu0 hu hu0h huh
  have h3 := hmin ν' ⟨hν', by omega, u', hu', hu'ν, Eqv_trans e1 (Eqv_trans e2 hus)⟩
  omega

lemma pick (hP : Plane q N L i0 p0 p1) (l m : Fin N) (hlm : l ≠ m) (g : Fin gates.length)
    (a b : Fin N) (ρa ρb : ℕ) (hRa : Rt L (TT L p0 p1) gates l m (g : ℕ) a ρa)
    (hRb : Rt L (TT L p0 p1) gates l m (g : ℕ) b ρb) (hlt : ρa < ρb)
    (hminb : ∀ ν : ℕ, Rt L (TT L p0 p1) gates l m (g : ℕ) b ν → ρb ≤ ν)
    (hab : Eqv L (TT L p0 p1) gates l ((g : ℕ) + 1) a b) :
    ∃ h : Fin gates.length, Pk L (TT L p0 p1) gates l m g h := by
  obtain ⟨hNa, hag, ua, hua, huaρ, ea⟩ := hRa
  have hRb' := hRb
  obtain ⟨hNb, hbg, ub, hub, hubρ, eb⟩ := hRb
  rcases hNb with ⟨c, hcl, hcm, hρb⟩ | ⟨h, hρb, hSH⟩
  · exfalso
    rcases hNa with ⟨c', hcl', hcm', hρa⟩ | ⟨h', hρa, _⟩
    · have hcc : c' = c := two_pts hP l m hlm c' c hcl' hcm' hcl hcm
      rw [hρa, hρb, hcc] at hlt
      exact lt_irrefl _ hlt
    · have hc2 := c.2
      omega
  · rw [hρb] at hRb' hminb hlt hubρ hbg
    refine ⟨h, hSH, by omega, ⟨b, hRb', hminb⟩, ρa, hNa, hlt, ua, hua, huaρ, ub, hub, hubρ, ?_⟩
    exact Eqv_trans (Eqv_mono (Nat.le_succ _) ea)
      (Eqv_trans hab (Eqv_symm (Eqv_mono (Nat.le_succ _) eb)))

lemma shared_exists (hP : Plane q N L i0 p0 p1) (hC : Ckt N gates) (o : Fin N → ℕ)
    (hgood : Good L i0 p0 p1 gates o) (l m : Fin N) (hl : p0 ∈ L l ∧ p1 ∉ L l)
    (hm : p1 ∈ L m ∧ p0 ∉ L m) (g : Fin gates.length) (hgl : Mg L (TT L p0 p1) gates l g)
    (hgm : Mg L (TT L p0 p1) gates m g) :
    ∃ h : Fin gates.length, Pk L (TT L p0 p1) gates l m g h := by
  classical
  have hlm : l ≠ m := fun e => hm.2 (e ▸ hl.1)
  obtain ⟨hop, hzl, w1, w2, hin, r, hr, r', hr', h1, h2, X, hX, hX', hcl⟩ := hgl
  obtain ⟨_, hzm, v1, v2, hin', ρ, hρ, ρ', hρ', k1, k2, _⟩ := hgm
  have hvv : w1 = v1 ∧ w2 = v2 := by
    have h3 := hin.symm.trans hin'
    simpa using h3
  rw [← hvv.1] at k1
  rw [← hvv.2] at k2
  have hw1 : w1 ∈ (gates.get g).inputs := by rw [hin]; simp
  have hw2 : w2 ∈ (gates.get g).inputs := by rw [hin]; simp
  have hfl := EV_or_false gates hC.2.2 g hop _ hzl
  have hfm := EV_or_false gates hC.2.2 g hop _ hzm
  have ts1 : TS L (TT L p0 p1) gates l m w1 := ⟨hfl w1 hw1, hfm w1 hw1, ⟨r, hr, h1⟩, ⟨ρ, hρ, k1⟩⟩
  have ts2 : TS L (TT L p0 p1) gates l m w2 :=
    ⟨hfl w2 hw2, hfm w2 hw2, ⟨r', hr', h2⟩, ⟨ρ', hρ', k2⟩⟩
  have lt1 := hC.2.2 g w1 hw1
  have lt2 := hC.2.2 g w2 hw2
  obtain ⟨ν1, hν1, hν1w, s1, hs1, hs1ν, t1, ht1, ht1w, e1⟩ :=
    descent hP hC o hgood l m (g : ℕ) w1 ts1 lt1
  obtain ⟨ν2, hν2, hν2w, s2, hs2, hs2ν, t2, ht2, ht2w, e2⟩ :=
    descent hP hC o hgood l m (g : ℕ) w2 ts2 lt2
  have c1 := C1 hP hC o hgood l (g : ℕ) w1 lt1 (hfl w1 hw1) t1 r ht1 hr ht1w h1
  have c2 := C1 hP hC o hgood l (g : ℕ) w2 lt2 (hfl w2 hw2) t2 r' ht2 hr' ht2w h2
  have exa : ∃ ν : ℕ, Rt L (TT L p0 p1) gates l m (g : ℕ) r ν :=
    ⟨ν1, hν1, by omega, s1, hs1, hs1ν, Eqv_trans e1 c1⟩
  have exb : ∃ ν : ℕ, Rt L (TT L p0 p1) gates l m (g : ℕ) r' ν :=
    ⟨ν2, hν2, by omega, s2, hs2, hs2ν, Eqv_trans e2 c2⟩
  have hnot : ¬ Eqv L (TT L p0 p1) gates l (g : ℕ) r r' := fun h =>
    hX' ((h X (fun i hi => hcl i (Fin.lt_def.mpr hi))).mp hX)
  have hg1 : EV gates (N + (g : ℕ)) (TT L p0 p1 l r) = true :=
    (EV_or gates hC.2.2 g hop _).mpr ⟨w1, hw1, h1⟩
  have hg2 : EV gates (N + (g : ℕ)) (TT L p0 p1 l r') = true :=
    (EV_or gates hC.2.2 g hop _).mpr ⟨w2, hw2, h2⟩
  have hyes : Eqv L (TT L p0 p1) gates l ((g : ℕ) + 1) r r' :=
    C1 hP hC o hgood l ((g : ℕ) + 1) (N + (g : ℕ)) (by omega) hzl r r' hr hr' hg1 hg2
  have sa := Nat.find_spec exa
  have ma : ∀ ν : ℕ, Rt L (TT L p0 p1) gates l m (g : ℕ) r ν → Nat.find exa ≤ ν :=
    fun ν hν => Nat.find_min' exa hν
  have sb := Nat.find_spec exb
  have mb : ∀ ν : ℕ, Rt L (TT L p0 p1) gates l m (g : ℕ) r' ν → Nat.find exb ≤ ν :=
    fun ν hν => Nat.find_min' exb hν
  have hne : Nat.find exa ≠ Nat.find exb := by
    intro heq
    obtain ⟨hNa, hag, ua, hua, huaρ, ea⟩ := sa
    obtain ⟨_, _, ub, hub, hubρ, eb⟩ := sb
    rw [← heq] at hubρ
    have h3 := C1 hP hC o hgood l (g : ℕ) (Nat.find exa) hag (Node_live hNa) ua ub hua hub
      huaρ hubρ
    exact hnot (Eqv_trans (Eqv_symm ea) (Eqv_trans h3 eb))
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact pick hP l m hlm g r r' _ _ sa sb hlt mb hyes
  · exact pick hP l m hlm g r' r _ _ sb sa hlt ma (Eqv_symm hyes)

lemma forest (hP : Plane q N L i0 p0 p1) (hC : Ckt N gates) (o : Fin N → ℕ)
    (hgood : Good L i0 p0 p1 gates o) (l m : Fin N) (hl : p0 ∈ L l ∧ p1 ∉ L l)
    (hm : p1 ∈ L m ∧ p0 ∉ L m) (S SHs : Finset (Fin gates.length))
    (hS : ∀ g ∈ S, Mg L (TT L p0 p1) gates l g ∧ Mg L (TT L p0 p1) gates m g)
    (hH : ∀ h : Fin gates.length, SH L (TT L p0 p1) gates l m h → h ∈ SHs) :
    S.card ≤ SHs.card := by
  classical
  have ex : ∀ g : Fin gates.length, ∃ h : Fin gates.length,
      g ∈ S → Pk L (TT L p0 p1) gates l m g h := by
    intro g
    by_cases hg : g ∈ S
    · obtain ⟨h, hh⟩ := shared_exists hP hC o hgood l m hl hm g (hS g hg).1 (hS g hg).2
      exact ⟨h, fun _ => hh⟩
    · exact ⟨g, fun h => absurd h hg⟩
  choose f hf using ex
  refine Finset.card_le_card_of_injOn f
    (fun g hg => Finset.mem_coe.mpr (hH _ (Pk_sh (hf g (Finset.mem_coe.mp hg))))) ?_
  intro g1 hg1 g2 hg2 heq
  by_contra hne
  have h1 := hf g1 (Finset.mem_coe.mp hg1)
  have h2 := hf g2 (Finset.mem_coe.mp hg2)
  rw [← heq] at h2
  rcases lt_or_gt_of_ne (fun e => hne (Fin.ext e)) with hlt | hlt
  · exact Pk_inj hP hC o hgood l m g1 g2 (f g1) hlt h1 h2
  · exact Pk_inj hP hC o hgood l m g2 g1 (f g1) hlt h2 h1

lemma Mg_two (hC : Ckt N gates) (t : Fin N) (g : Fin gates.length)
    (hM : Mg L (TT L p0 p1) gates t g) :
    2 ≤ ((L t).filter (fun p => EV gates (N + (g : ℕ)) (TT L p0 p1 t p) = true)).card := by
  obtain ⟨hop, hz, w1, w2, hin, r, hr, r', hr', h1, h2, X, hX, hX', _⟩ := hM
  have hw1 : w1 ∈ (gates.get g).inputs := by rw [hin]; simp
  have hw2 : w2 ∈ (gates.get g).inputs := by rw [hin]; simp
  have hne : r ≠ r' := fun e => hX' (e ▸ hX)
  exact Finset.one_lt_card.mpr ⟨r, Finset.mem_filter.mpr ⟨hr, (EV_or gates hC.2.2 g hop _).mpr
    ⟨w1, hw1, h1⟩⟩, r', Finset.mem_filter.mpr ⟨hr', (EV_or gates hC.2.2 g hop _).mpr
    ⟨w2, hw2, h2⟩⟩, hne⟩

lemma Mg_pair (hP : Plane q N L i0 p0 p1) (hC : Ckt N gates) (t u : Fin N)
    (e : Fin gates.length) (htu : t ≠ u) (ht : t ≠ i0) (hu : u ≠ i0)
    (m1 : Mg L (TT L p0 p1) gates t e) (m2 : Mg L (TT L p0 p1) gates u e) :
    ((p0 ∈ L t ∧ p1 ∉ L t) ∧ (p1 ∈ L u ∧ p0 ∉ L u)) ∨ ((p1 ∈ L t ∧ p0 ∉ L t) ∧ (p0 ∈ L u ∧ p1 ∉ L u)) :=
  (W33 hP t u ht hu htu).mp (W34 hP hC (N + (e : ℕ)) t u htu (Mg_live m1) (Mg_live m2)
    (Mg_two hC t e m1) (Mg_two hC u e m2))

lemma merge_ts (hC : Ckt N gates) (t u : Fin N) (h : Fin gates.length)
    (hM : Mg L (TT L p0 p1) gates t h)
    (hzu : EV gates (N + (h : ℕ)) (fun v : Fin N => decide (v ∉ L u)) = false)
    (s : Fin N) (hs : s ∈ L u) (hst : EV gates (N + (h : ℕ)) (TT L p0 p1 u s) = true) :
    ∃ e ∈ (gates.get h).inputs, EV gates e (fun v : Fin N => decide (v ∉ L t)) = false ∧
      EV gates e (fun v : Fin N => decide (v ∉ L u)) = false ∧
      (∃ p ∈ L t, EV gates e (TT L p0 p1 t p) = true) ∧ ∃ p ∈ L u, EV gates e (TT L p0 p1 u p) = true := by
  obtain ⟨hop, hzt, w1, w2, hin, r, hr, r', hr', h1, h2, _⟩ := hM
  obtain ⟨e, he, hes⟩ := (EV_or gates hC.2.2 h hop _).mp hst
  refine ⟨e, he, EV_or_false gates hC.2.2 h hop _ hzt e he,
    EV_or_false gates hC.2.2 h hop _ hzu e he, ?_, s, hs, hes⟩
  have he' : e = w1 ∨ e = w2 := by
    rw [hin] at he
    simpa using he
  rcases he' with he' | he'
  · rw [he']
    exact ⟨r, hr, h1⟩
  · rw [he']
    exact ⟨r', hr', h2⟩

lemma hinge_not_merge (hP : Plane q N L i0 p0 p1) (hC : Ckt N gates) (l m : Fin N)
    (hl : p0 ∈ L l ∧ p1 ∉ L l) (hm : p1 ∈ L m ∧ p0 ∉ L m) (h : Fin gates.length)
    (hS : SH L (TT L p0 p1) gates l m h) (t : Fin N) (ht : t ≠ i0)
    (hM : Mg L (TT L p0 p1) gates t h) : False := by
  obtain ⟨⟨hzl, hzm, ⟨s, hs, hst⟩, ⟨s', hs', hst'⟩⟩, hno⟩ := hS
  by_cases htl : t = l
  · rw [htl] at hM
    obtain ⟨e, he, b1, b2, b3, b4⟩ := merge_ts hC l m h hM hzm s' hs' hst'
    exact hno e he ⟨b1, b2, b3, b4⟩
  by_cases htm : t = m
  · rw [htm] at hM
    obtain ⟨e, he, b1, b2, b3, b4⟩ := merge_ts hC m l h hM hzl s hs hst
    exact hno e he ⟨b2, b1, b4, b3⟩
  have hzt := Mg_live hM
  by_cases h0 : p0 ∈ L t
  · have h1 : p1 ∉ L t := fun h1 => not_both hP t ht ⟨h0, h1⟩
    have h3 := W36a hP hC (N + (h : ℕ)) m l hm hl hzm ⟨s, hs, hst⟩ t ⟨h0, h1⟩ htl
    exact Bool.false_ne_true (hzt.symm.trans h3)
  · by_cases h1 : p1 ∈ L t
    · have h3 := W36b hP hC (N + (h : ℕ)) l m hl hm hzl ⟨s', hs', hst'⟩ t ⟨h1, h0⟩ htm
      exact Bool.false_ne_true (hzt.symm.trans h3)
    · have c1 := W36c hP hC (N + (h : ℕ)) m t hm hzm ⟨h0, h1⟩
      have c2 := Mg_two hC t h hM
      omega

lemma hinge_not_deliver (hP : Plane q N L i0 p0 p1) (hC : Ckt N gates) (l m : Fin N)
    (hl : p0 ∈ L l ∧ p1 ∉ L l) (hm : p1 ∈ L m ∧ p0 ∉ L m) (h : Fin gates.length)
    (hS : SH L (TT L p0 p1) gates l m h) (hand : (gates.get h).op = GateOp.and) (c : ℕ)
    (hc : c ∈ (gates.get h).inputs)
    (hcz : EV gates c (fun v : Fin N => decide (v ∉ L i0)) = false) (r : Fin N) (hr0 : r ≠ p0)
    (hr1 : r ≠ p1) (hst : St gates c r) : False := by
  obtain ⟨⟨hzl, hzm, ⟨s, hs, hsv⟩, ⟨s', hs', hsv'⟩⟩, hno⟩ := hS
  have hli : l ≠ i0 := fun e => hl.2 (e ▸ hP.2.2.2.2.2.2.2)
  have hmi : m ≠ i0 := fun e => hm.2 (e ▸ hP.2.2.2.2.2.2.1)
  by_cases hcl : EV gates c (fun v : Fin N => decide (v ∉ L l)) = false
  · exact hr0 (W39 hP hC c hcz l p0 hli hcl (meet_eq hP l i0 hli p0 hl.1 hP.2.2.2.2.2.2.1) r hst)
  by_cases hcm : EV gates c (fun v : Fin N => decide (v ∉ L m)) = false
  · exact hr1 (W39 hP hC c hcz m p1 hmi hcm (meet_eq hP m i0 hmi p1 hm.1 hP.2.2.2.2.2.2.2) r hst)
  obtain ⟨e1, he1, he1z⟩ := EV_and_false gates hC.2.2 h hand _ hzl
  obtain ⟨e2, he2, he2z⟩ := EV_and_false gates hC.2.2 h hand _ hzm
  have hce1 : c ≠ e1 := fun e => hcl (e ▸ he1z)
  have hce2 : c ≠ e2 := fun e => hcm (e ▸ he2z)
  have he12 : e1 = e2 :=
    three_in_two _ (hC.1 _ (List.getElem_mem h.2)).2 c e1 e2 hc he1 he2 hce1 hce2
  rw [← he12] at he2z
  exact hno e1 he1 ⟨he1z, he2z, ⟨s, hs, (EV_and gates hC.2.2 h hand _).mp hsv e1 he1⟩,
    ⟨s', hs', (EV_and gates hC.2.2 h hand _).mp hsv' e1 he1⟩⟩

lemma dis2 (hP : Plane q N L i0 p0 p1) (hC : Ckt N gates) (t u : Fin N) (htu : t ≠ u)
    (ht : t ≠ i0) (hu : u ≠ i0) (e : Fin gates.length)
    (h1 : KindM L (TT L p0 p1) gates p0 p1 t e ∨ KindS L (TT L p0 p1) gates p0 p1 t e)
    (h2 : KindM L (TT L p0 p1) gates p0 p1 u e ∨ KindS L (TT L p0 p1) gates p0 p1 u e) :
    False := by
  rcases h1 with ⟨m1, n1⟩ | ⟨ms1, l1, hl1, s1⟩
  · rcases h2 with ⟨m2, n2⟩ | ⟨ms2, l2, hl2, s2⟩
    · rcases Mg_pair hP hC t u e htu ht hu m1 m2 with ⟨a, b⟩ | ⟨a, b⟩
      · exact n2 b t a m1
      · exact n1 a u b m2
    · exact hinge_not_merge hP hC l2 u hl2 ms2 e s2 t ht m1
  · rcases h2 with ⟨m2, n2⟩ | ⟨ms2, l2, hl2, s2⟩
    · exact hinge_not_merge hP hC l1 t hl1 ms1 e s1 u hu m2
    · obtain ⟨⟨b1, _, _, b4⟩, _⟩ := s1
      obtain ⟨⟨_, d2, _, _⟩, _⟩ := s2
      have h3 := W36b hP hC (N + (e : ℕ)) l1 t hl1 ms1 b1 b4 u ms2 (Ne.symm htu)
      exact Bool.false_ne_true (d2.symm.trans h3)

lemma dis1 (hP : Plane q N L i0 p0 p1) (hC : Ckt N gates) (u : Fin N) (hu : u ≠ i0)
    (e : Fin gates.length) (ch : Fin gates.length → ℕ)
    (hch : ∀ a : Fin gates.length, ((gates.get a).op = GateOp.and ∧ EV gates (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false ∧ ∃ r ∈ L i0, r ≠ p0 ∧ r ≠ p1 ∧ EV gates (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true) → ch a ∈ (gates.get a).inputs ∧ EV gates (ch a) (fun v : Fin N => decide (v ∉ L i0)) = false)
    (h1 : Dl L i0 p0 p1 gates ch e ∨ ((gates.get e).op = GateOp.or ∧
      EV gates (N + (e : ℕ)) (fun v : Fin N => decide (v ∉ L u)) = true))
    (h2 : KindM L (TT L p0 p1) gates p0 p1 u e ∨ KindS L (TT L p0 p1) gates p0 p1 u e) :
    False := by
  rcases h1 with hd | ⟨hor, htrue⟩
  · obtain ⟨hA, r, hr, hr0, hr1, hrv, hst⟩ := hd
    obtain ⟨hcin, hcz⟩ := hch e hA
    rcases h2 with ⟨m2, _⟩ | ⟨ms, l, hl, s⟩
    · cases hA.1.symm.trans (Mg_or m2)
    · exact hinge_not_deliver hP hC l u hl ms e s hA.1 (ch e) hcin hcz r hr0 hr1 hst
  · rcases h2 with ⟨m2, _⟩ | ⟨ms, l, hl, s⟩
    · exact Bool.false_ne_true ((Mg_live m2).symm.trans htrue)
    · obtain ⟨⟨_, d2, _, _⟩, _⟩ := s
      exact Bool.false_ne_true (d2.symm.trans htrue)

lemma gstar (hP : Plane q N L i0 p0 p1) (hC : Ckt N gates) (o0 : ℕ)
    (hz : EV gates o0 (fun v : Fin N => decide (v ∉ L i0)) = false)
    (h0 : EV gates o0 (fun v : Fin N => decide (v = p0)) = true)
    (h1 : EV gates o0 (fun v : Fin N => decide (v = p1)) = true) :
    ∃ a : Fin gates.length, (gates.get a).op = GateOp.or ∧
      (∀ t : Fin N, t ≠ i0 → EV gates (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L t)) = true) ∧
      ∀ e ∈ (gates.get a).inputs, (EV gates e (fun v : Fin N => decide (v = p0)) = true ∨ EV gates e (fun v : Fin N => decide (v = p1)) = true) := by
  classical
  have ex : ∃ w : ℕ, EV gates w (fun v : Fin N => decide (v ∉ L i0)) = false ∧
      EV gates w (fun v : Fin N => decide (v = p0)) = true ∧
      EV gates w (fun v : Fin N => decide (v = p1)) = true := ⟨o0, hz, h0, h1⟩
  obtain ⟨hwz, hw0, hw1⟩ := Nat.find_spec ex
  have hmin : ∀ w' : ℕ, w' < Nat.find ex →
      ¬ (EV gates w' (fun v : Fin N => decide (v ∉ L i0)) = false ∧
      EV gates w' (fun v : Fin N => decide (v = p0)) = true ∧
      EV gates w' (fun v : Fin N => decide (v = p1)) = true) := fun w' hw' => Nat.find_min ex hw'
  generalize Nat.find ex = w at hwz hw0 hw1 hmin
  have hN : N ≤ w := by
    by_contra hlt
    have hlt' : w < N := Nat.lt_of_not_le hlt
    have b0 : decide ((⟨w, hlt'⟩ : Fin N) = p0) = true :=
      (EV_in gates (⟨w, hlt'⟩ : Fin N) _).symm.trans hw0
    have b1 : decide ((⟨w, hlt'⟩ : Fin N) = p1) = true :=
      (EV_in gates (⟨w, hlt'⟩ : Fin N) _).symm.trans hw1
    exact hP.2.2.2.2.2.1 ((of_decide_eq_true b0).symm.trans (of_decide_eq_true b1))
  have hlen : w < N + gates.length := by
    by_contra hge
    rw [EV_miss gates w _ (by omega)] at hw0
    exact absurd hw0 (by decide)
  obtain ⟨k, rfl⟩ : ∃ k, w = N + k := ⟨w - N, by omega⟩
  have hk : k < gates.length := by omega
  rcases (hC.1 _ (List.getElem_mem hk)).1 with hand | hor
  · exfalso
    obtain ⟨e, he, hez⟩ := EV_and_false gates hC.2.2 ⟨k, hk⟩ hand _ hwz
    exact hmin e (hC.2.2 ⟨k, hk⟩ e he) ⟨hez, (EV_and gates hC.2.2 ⟨k, hk⟩ hand _).mp hw0 e he,
      (EV_and gates hC.2.2 ⟨k, hk⟩ hand _).mp hw1 e he⟩
  · refine ⟨⟨k, hk⟩, hor, ?_, ?_⟩
    · intro t ht
      by_cases hp0 : p0 ∈ L t
      · have hp1 : p1 ∉ L t := fun h => not_both hP t ht ⟨hp0, h⟩
        refine EV_mono gates hC.1 (fun v : Fin N => decide (v = p1)) _ (fun v hv => ?_) _ hw1
        have hv' : v = p1 := of_decide_eq_true hv
        show decide (v ∉ L t) = true
        rw [hv']
        exact decide_eq_true hp1
      · refine EV_mono gates hC.1 (fun v : Fin N => decide (v = p0)) _ (fun v hv => ?_) _ hw0
        have hv' : v = p0 := of_decide_eq_true hv
        show decide (v ∉ L t) = true
        rw [hv']
        exact decide_eq_true hp0
    · intro e he
      have hez := EV_or_false gates hC.2.2 ⟨k, hk⟩ hor _ hwz
      obtain ⟨e0, he0, h0'⟩ := (EV_or gates hC.2.2 ⟨k, hk⟩ hor _).mp hw0
      obtain ⟨e1, he1, h1'⟩ := (EV_or gates hC.2.2 ⟨k, hk⟩ hor _).mp hw1
      by_contra hcon
      have hcon' := not_or.mp hcon
      have hne0 : e ≠ e0 := fun h => hcon'.1 (h ▸ h0')
      have hne1 : e ≠ e1 := fun h => hcon'.2 (h ▸ h1')
      have h01 : e0 = e1 :=
        three_in_two _ (hC.1 _ (List.getElem_mem hk)).2 e e0 e1 he he0 he1 hne0 hne1
      rw [← h01] at h1'
      exact hmin e0 (hC.2.2 ⟨k, hk⟩ e0 he0) ⟨hez e0 he0, h0', h1'⟩

theorem core (hP : Plane q N L i0 p0 p1) (hC : Ckt N gates) (o : Fin N → ℕ)
    (hgood : Good L i0 p0 p1 gates o) : N * q ≤ gates.length := by
  classical
  have hoz : EV gates (o i0) (fun v : Fin N => decide (v ∉ L i0)) = false :=
    (hgood i0 (fun v : Fin N => decide (v ∉ L i0))
      (Or.inr (Or.inr (fun u hu => decide_eq_true hu)))).trans (by simp)
  have ho0 : EV gates (o i0) (fun v : Fin N => decide (v = p0)) = true :=
    (hgood i0 (fun v : Fin N => decide (v = p0)) (Or.inl (by simp))).trans
      (decide_eq_true ⟨p0, hP.2.2.2.2.2.2.1, by simp⟩)
  have ho1 : EV gates (o i0) (fun v : Fin N => decide (v = p1)) = true :=
    (hgood i0 (fun v : Fin N => decide (v = p1)) (Or.inr (Or.inl (by simp)))).trans
      (decide_eq_true ⟨p1, hP.2.2.2.2.2.2.2, by simp⟩)
  have horim : ∀ r ∈ L i0, r ≠ p0 → r ≠ p1 →
      EV gates (o i0) (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true :=
    fun r hr _ _ => (hgood i0 (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))
      (Or.inr (Or.inr (fun u hu => decide_eq_true (Or.inl hu))))).trans
      (decide_eq_true ⟨r, hr, by simp⟩)
  have hchex : ∀ a : Fin gates.length, ∃ c : ℕ, ((gates.get a).op = GateOp.and ∧ EV gates (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false ∧ ∃ r ∈ L i0, r ≠ p0 ∧ r ≠ p1 ∧ EV gates (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true) → c ∈ (gates.get a).inputs ∧ EV gates c (fun v : Fin N => decide (v ∉ L i0)) = false := by
    intro a
    by_cases h : (gates.get a).op = GateOp.and ∧
        EV gates (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false
    · obtain ⟨c, hc, hcz⟩ := EV_and_false gates hC.2.2 a h.1 _ h.2
      exact ⟨c, fun _ => ⟨hc, hcz⟩⟩
    · exact ⟨0, fun h' => absurd ⟨h'.1, h'.2.1⟩ h⟩
  choose ch hch using hchex
  obtain ⟨D, hDmem⟩ : ∃ D : Finset (Fin gates.length), ∀ a, a ∈ D ↔ Dl L i0 p0 p1 gates ch a :=
    ⟨Finset.univ.filter (fun a => Dl L i0 p0 p1 gates ch a), fun a => by simp⟩
  obtain ⟨Xs, hXmem⟩ : ∃ Xs : Finset (Fin gates.length), ∀ a, a ∈ Xs ↔ Xst L i0 p0 p1 gates a :=
    ⟨Finset.univ.filter (fun a => Xst L i0 p0 p1 gates a), fun a => by simp⟩
  have h42 : q - 1 ≤ D.card + Xs.card :=
    W42 hP hC (o i0) hoz ho0 ho1 horim ch hch D Xs (fun a ha => (hDmem a).mpr ha)
      (fun g hg => (hXmem g).mpr hg)
  obtain ⟨ag, hag_or, hag_true, hag_in⟩ := gstar hP hC (o i0) hoz ho0 ho1
  obtain ⟨I, hImem⟩ : ∃ I : Fin N → Finset (Fin gates.length),
      ∀ t g, g ∈ I t ↔ Mg L (TT L p0 p1) gates t g :=
    ⟨fun t => Finset.univ.filter (fun g => Mg L (TT L p0 p1) gates t g), fun t g => by simp⟩
  have hIcard : ∀ t, (I t).card = q := fun t => W35b hP hC o hgood t (I t) (hImem t)
  obtain ⟨H, hHmem⟩ : ∃ H : Fin N → Fin N → Finset (Fin gates.length),
      ∀ l m h, h ∈ H l m ↔ SH L (TT L p0 p1) gates l m h :=
    ⟨fun l m => Finset.univ.filter (fun h => SH L (TT L p0 p1) gates l m h),
      fun l m h => by simp⟩
  obtain ⟨LSs, hLS⟩ : ∃ LSs : Finset (Fin N), ∀ l, l ∈ LSs ↔ (p0 ∈ L l ∧ p1 ∉ L l) :=
    ⟨Finset.univ.filter (fun l => p0 ∈ L l ∧ p1 ∉ L l), fun l => by simp⟩
  obtain ⟨K, hK0, hKms, hKo⟩ : ∃ K : Fin N → Finset (Fin gates.length),
      K i0 = D ∪ Xs ∪ {ag} ∧
      (∀ t, t ≠ i0 → (p1 ∈ L t ∧ p0 ∉ L t) →
        K t = (I t \ LSs.biUnion I) ∪ LSs.biUnion (fun l => H l t)) ∧
      (∀ t, t ≠ i0 → ¬ (p1 ∈ L t ∧ p0 ∉ L t) → K t = I t) := by
    refine ⟨fun t => if t = i0 then D ∪ Xs ∪ {ag}
      else if p1 ∈ L t ∧ p0 ∉ L t then (I t \ LSs.biUnion I) ∪ LSs.biUnion (fun l => H l t)
      else I t, ?_, ?_, ?_⟩
    · exact if_pos rfl
    · intro t ht hm
      show (if t = i0 then _ else _) = _
      rw [if_neg ht, if_pos hm]
    · intro t ht hm
      show (if t = i0 then _ else _) = _
      rw [if_neg ht, if_neg hm]
  have hkind : ∀ t, t ≠ i0 → ∀ e, e ∈ K t →
      (KindM L (TT L p0 p1) gates p0 p1 t e ∨ KindS L (TT L p0 p1) gates p0 p1 t e) := by
    intro t ht e he
    by_cases hm : p1 ∈ L t ∧ p0 ∉ L t
    · rw [hKms t ht hm] at he
      rcases Finset.mem_union.mp he with he | he
      · obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp he
        refine Or.inl ⟨(hImem t e).mp h1, fun _ l hl hMl => h2 ?_⟩
        exact Finset.mem_biUnion.mpr ⟨l, (hLS l).mpr hl, (hImem l e).mpr hMl⟩
      · obtain ⟨l, hl, hel⟩ := Finset.mem_biUnion.mp he
        exact Or.inr ⟨hm, l, (hLS l).mp hl, (hHmem l t e).mp hel⟩
    · rw [hKo t ht hm] at he
      exact Or.inl ⟨(hImem t e).mp he, fun h => absurd h hm⟩
  have hkind0 : ∀ e, e ∈ K i0 → ∀ u, u ≠ i0 → (Dl L i0 p0 p1 gates ch e ∨
      ((gates.get e).op = GateOp.or ∧
        EV gates (N + (e : ℕ)) (fun v : Fin N => decide (v ∉ L u)) = true)) := by
    intro e he u hu
    rw [hK0] at he
    rcases Finset.mem_union.mp he with he | he
    · rcases Finset.mem_union.mp he with he | he
      · exact Or.inl ((hDmem e).mp he)
      · obtain ⟨x1, _, x3, _⟩ := (hXmem e).mp he
        exact Or.inr ⟨x1, x3 u hu⟩
    · rw [Finset.mem_singleton.mp he]
      exact Or.inr ⟨hag_or, hag_true u hu⟩
  have hdisj : ∀ t u, t ≠ u → Disjoint (K t) (K u) := by
    intro t u htu
    refine Finset.disjoint_left.mpr (fun e het heu => ?_)
    by_cases ht : t = i0
    · have hu : u ≠ i0 := fun h => htu (ht.trans h.symm)
      rw [ht] at het
      exact dis1 hP hC u hu e ch hch (hkind0 e het u hu) (hkind u hu e heu)
    · by_cases hu : u = i0
      · rw [hu] at heu
        exact dis1 hP hC t ht e ch hch (hkind0 e heu t ht) (hkind t ht e het)
      · exact dis2 hP hC t u htu ht hu e (hkind t ht e het) (hkind u hu e heu)
  have hcard : ∀ t, q ≤ (K t).card := by
    intro t
    by_cases ht : t = i0
    · rw [ht, hK0]
      have hd1 : Disjoint D Xs := Finset.disjoint_left.mpr (fun e h1 h2 => by
        obtain ⟨⟨y1, _⟩, _⟩ := (hDmem e).mp h1
        obtain ⟨y2, _⟩ := (hXmem e).mp h2
        cases y1.symm.trans y2)
      have hnotin : ag ∉ D ∪ Xs := by
        intro h
        rcases Finset.mem_union.mp h with h | h
        · obtain ⟨⟨y1, _⟩, _⟩ := (hDmem ag).mp h
          cases y1.symm.trans hag_or
        · obtain ⟨_, _, _, y4⟩ := (hXmem ag).mp h
          exact y4 hag_in
      have c1 : (D ∪ Xs ∪ {ag}).card = (D ∪ Xs).card + 1 := by
        rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr hnotin),
          Finset.card_singleton]
      have c2 : (D ∪ Xs).card = D.card + Xs.card := Finset.card_union_of_disjoint hd1
      omega
    · by_cases hm : p1 ∈ L t ∧ p0 ∉ L t
      · rw [hKms t ht hm]
        have hd : Disjoint (I t \ LSs.biUnion I) (LSs.biUnion (fun l => H l t)) :=
          Finset.disjoint_left.mpr (fun e h1 h2 => by
            obtain ⟨l, hl, hel⟩ := Finset.mem_biUnion.mp h2
            exact hinge_not_merge hP hC l t ((hLS l).mp hl) hm e ((hHmem l t e).mp hel) t ht
              ((hImem t e).mp (Finset.mem_sdiff.mp h1).1))
        have hpd : ∀ l ∈ LSs, ∀ l' ∈ LSs, l ≠ l' → Disjoint (H l t) (H l' t) := by
          intro l hl l' hl' hne
          refine Finset.disjoint_left.mpr (fun e h1 h2 => ?_)
          obtain ⟨⟨_, y2, y3, _⟩, _⟩ := (hHmem l t e).mp h1
          obtain ⟨⟨z1, _⟩, _⟩ := (hHmem l' t e).mp h2
          have h3 := W36a hP hC (N + (e : ℕ)) t l hm ((hLS l).mp hl) y2 y3 l' ((hLS l').mp hl')
            (Ne.symm hne)
          exact Bool.false_ne_true (z1.symm.trans h3)
        have c1 : ((I t \ LSs.biUnion I) ∪ LSs.biUnion (fun l => H l t)).card =
            (I t \ LSs.biUnion I).card + (LSs.biUnion (fun l => H l t)).card :=
          Finset.card_union_of_disjoint hd
        have c2 : (LSs.biUnion (fun l => H l t)).card = ∑ l ∈ LSs, (H l t).card :=
          Finset.card_biUnion (fun l hl l' hl' hne => hpd l hl l' hl' hne)
        have c3 : (I t \ LSs.biUnion I).card + (I t ∩ LSs.biUnion I).card = (I t).card :=
          Finset.card_sdiff_add_card_inter _ _
        have c4 : (I t ∩ LSs.biUnion I).card ≤ ∑ l ∈ LSs, (I t ∩ I l).card := by
          rw [Finset.inter_biUnion]
          exact Finset.card_biUnion_le
        have c5 : ∑ l ∈ LSs, (I t ∩ I l).card ≤ ∑ l ∈ LSs, (H l t).card :=
          Finset.sum_le_sum (fun l hl =>
            forest hP hC o hgood l t ((hLS l).mp hl) hm (I t ∩ I l) (H l t)
              (fun g hg => ⟨(hImem l g).mp (Finset.mem_inter.mp hg).2,
                (hImem t g).mp (Finset.mem_inter.mp hg).1⟩)
              (fun h hh => (hHmem l t h).mpr hh))
        have c6 := hIcard t
        omega
      · rw [hKo t ht hm, hIcard t]
  have hfin := b_count K hcard hdisj
  have hle := Finset.card_le_univ (Finset.univ.biUnion K)
  rw [Fintype.card_fin] at hle
  exact le_trans hfin hle


theorem lower_bound : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ),
      (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
      (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
      (∀ (t : Fin N) (x : Fin N → Bool), (x p0 = true ∨ x p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → x u = true) →
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
      N * q ≤ gates.length := by
  intro q N L i0 p0 p1 hq hN hcard hinter hline h01 h0 h1 gates o legal _ hout
  have hP : Plane q N L i0 p0 p1 := ⟨hq, hN, hcard, hinter, hline, h01, h0, h1⟩
  obtain ⟨new, hfan, hrb, hl, hrep⟩ :=
    r_inv_all (fun (x : Fin N → Bool) => x) (fun i => Or.inr (fun x => rfl)) gates legal
  have hsel : ∀ t : Fin N, ∃ j : ℕ, ∀ x : Fin N → Bool,
      Circuit.eval ⟨new, j⟩ (List.ofFn x) = Circuit.eval ⟨gates, o t⟩ (List.ofFn x) := by
    intro t
    rcases hrep (o t) with ⟨c, hc⟩ | ⟨j, _, hj⟩
    · exfalso
      have hF : ((fun v : Fin N => decide (v ∉ L t)) p0 = true ∨ (fun v : Fin N => decide (v ∉ L t)) p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → (fun v : Fin N => decide (v ∉ L t)) u = true) := by
        by_cases ht : t = i0
        · refine Or.inr (Or.inr (fun u hu => ?_))
          rw [ht]
          exact decide_eq_true hu
        · by_cases hp0 : p0 ∈ L t
          · exact Or.inr (Or.inl (decide_eq_true (fun hp1 => not_both hP t ht ⟨hp0, hp1⟩)))
          · exact Or.inl (decide_eq_true hp0)
      have e1 := hout t (fun _ => true) (Or.inl rfl)
      have e2 := hout t (fun v : Fin N => decide (v ∉ L t)) hF
      have a1 : Circuit.eval ⟨gates, o t⟩ (List.ofFn (fun _ : Fin N => true)) = c := hc _
      have a2 : Circuit.eval ⟨gates, o t⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L t))) = c :=
        hc _
      rw [a1] at e1
      rw [a2] at e2
      have hne : (L t).Nonempty := Finset.card_pos.mp (by rw [hcard t]; omega)
      obtain ⟨v0, hv0⟩ := hne
      have l1 : decide (∃ v ∈ L t, (fun _ : Fin N => true) v = true) = true :=
        decide_eq_true ⟨v0, hv0, rfl⟩
      have l2 : decide (∃ v ∈ L t, (fun v : Fin N => decide (v ∉ L t)) v = true) = false := by
        simp
      rw [l1] at e1
      rw [l2] at e2
      rw [e1] at e2
      exact Bool.noConfusion e2
    · exact ⟨j, fun x => hj x⟩
  choose o' ho' using hsel
  have hC : Ckt N new := by
    refine ⟨fun g hg => ⟨(hfan g hg).1, le_of_eq (hfan g hg).2⟩, ?_, ?_⟩
    · intro i
      have hf := (hfan new[(i : ℕ)] (List.getElem_mem i.2)).2
      show 1 ≤ new[(i : ℕ)].inputs.length
      rw [hf]
      norm_num
    · intro i a ha
      exact hrb i i.2 a (by rw [List.getD_eq_getElem _ _ i.2]; exact ha)
  have hlen : N * q ≤ new.length :=
    core hP hC o' (fun t x hx => (ho' t x).trans (hout t x hx))
  exact le_trans hlen hl


lemma upper_core {q N : ℕ} (L : Fin N → Finset (Fin N)) (hq : 1 ≤ q) (pt : ℕ → ℕ → ℕ)
    (hpt1 : ∀ t i : ℕ, t < N → i < q + 1 → pt t i < N)
    (hpt2 : ∀ (t v : Fin N), v ∈ L t ↔ ∃ i : ℕ, i < q + 1 ∧ pt (t : ℕ) i = (v : ℕ)) :
    ∃ (gates : List Gate) (o : Fin N → ℕ),
      (∀ gt ∈ gates, (gt.op = GateOp.and ∨ gt.op = GateOp.or) ∧ gt.inputs.length ≤ 2) ∧
      (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) ∧
      (∀ (t : Fin N) (x : Fin N → Bool), Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) ∧
      gates.length = N * q := by
  obtain ⟨Gf, hGf⟩ : ∃ Gf : ℕ → Gate, ∀ j, Gf j = ⟨GateOp.or, if j % q = 0 then [pt (j / q) 0, pt (j / q) 1] else [N + (j - 1), pt (j / q) (j % q + 1)]⟩ :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨gates, hgdef⟩ : ∃ gates : List Gate, gates = (List.range (N * q)).map Gf := ⟨_, rfl⟩
  have hlen : gates.length = N * q := by
    rw [hgdef]
    simp
  have hget : ∀ i : Fin gates.length, gates.get i = Gf (i : ℕ) := by
    intro i
    subst hgdef
    simp
  have hop : ∀ j, (Gf j).op = GateOp.or := fun j => by rw [hGf]
  have hin0 : ∀ j, j % q = 0 → (Gf j).inputs = [pt (j / q) 0, pt (j / q) 1] := fun j h => by
    rw [hGf]
    exact if_pos h
  have hin1 : ∀ j, j % q ≠ 0 → (Gf j).inputs = [N + (j - 1), pt (j / q) (j % q + 1)] :=
    fun j h => by
      rw [hGf]
      exact if_neg h
  have hqpos : 0 < q := hq
  have hNq : ∀ j, j < N * q → j / q < N := fun j hj =>
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hj)
  have hlegal : ∀ gt ∈ gates, (gt.op = GateOp.and ∨ gt.op = GateOp.or) ∧ gt.inputs.length ≤ 2 := by
    intro gt hgt
    rw [hgdef] at hgt
    obtain ⟨j, _, hj⟩ := List.mem_map.mp hgt
    rw [← hj]
    refine ⟨Or.inr (hop j), ?_⟩
    by_cases h : j % q = 0
    · rw [hin0 j h]
      simp
    · rw [hin1 j h]
      simp
  have htopo : ∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ) := by
    intro i w hw
    rw [hget i] at hw
    have hi : (i : ℕ) < N * q := by
      rw [← hlen]
      exact i.2
    have hdiv := hNq _ hi
    by_cases h : (i : ℕ) % q = 0
    · rw [hin0 _ h] at hw
      have hw' : w = pt ((i : ℕ) / q) 0 ∨ w = pt ((i : ℕ) / q) 1 := by simpa using hw
      rcases hw' with hw' | hw'
      · have h3 := hpt1 _ 0 hdiv (by omega)
        omega
      · have h3 := hpt1 _ 1 hdiv (by omega)
        omega
    · rw [hin1 _ h] at hw
      have hw' : w = N + ((i : ℕ) - 1) ∨ w = pt ((i : ℕ) / q) ((i : ℕ) % q + 1) := by
        simpa using hw
      have hi0 : (i : ℕ) ≠ 0 := by
        intro h0
        rw [h0] at h
        exact h (Nat.zero_mod q)
      rcases hw' with hw' | hw'
      · omega
      · have hm := Nat.mod_lt (i : ℕ) hqpos
        have h3 := hpt1 _ ((i : ℕ) % q + 1) hdiv (by omega)
        omega
  have hjlt : ∀ (t : Fin N) (k : ℕ), k < q → q * (t : ℕ) + k < gates.length := by
    intro t k hk
    rw [hlen]
    have h1 : q * ((t : ℕ) + 1) ≤ q * N := Nat.mul_le_mul_left q (Nat.succ_le_of_lt t.2)
    have h2 : q * ((t : ℕ) + 1) = q * (t : ℕ) + q := Nat.mul_succ q t
    have h3 : q * N = N * q := Nat.mul_comm q N
    omega
  have hdivk : ∀ (t k : ℕ), k < q → (q * t + k) / q = t := fun t k hk => by
    rw [Nat.mul_add_div hqpos, Nat.div_eq_of_lt hk, Nat.add_zero]
  have hmodk : ∀ (t k : ℕ), k < q → (q * t + k) % q = k := fun t k hk => by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hk]
  have hval : ∀ (t : Fin N) (k : ℕ), k < q → ∀ x : Fin N → Bool,
      (EV gates (N + (q * (t : ℕ) + k)) x = true ↔
        ∃ e ∈ (Gf (q * (t : ℕ) + k)).inputs, EV gates e x = true) := by
    intro t k hk x
    have h := EV_or gates htopo ⟨q * (t : ℕ) + k, hjlt t k hk⟩ (by rw [hget]; exact hop _) x
    rw [hget] at h
    exact h
  have hchain : ∀ (t : Fin N) (x : Fin N → Bool) (k : ℕ), k < q →
      (EV gates (N + (q * (t : ℕ) + k)) x = true ↔
        ∃ i : ℕ, i ≤ k + 1 ∧ EV gates (pt (t : ℕ) i) x = true) := by
    intro t x k
    induction k with
    | zero =>
      intro hk
      have hv := hval t 0 hk x
      rw [hin0 (q * (t : ℕ) + 0) (hmodk (t : ℕ) 0 hk), hdivk (t : ℕ) 0 hk] at hv
      refine hv.trans ⟨?_, ?_⟩
      · rintro ⟨e, he, hev⟩
        have he' : e = pt (t : ℕ) 0 ∨ e = pt (t : ℕ) 1 := by simpa using he
        rcases he' with he' | he'
        · exact ⟨0, by omega, he' ▸ hev⟩
        · exact ⟨1, by omega, he' ▸ hev⟩
      · rintro ⟨i, hi, hev⟩
        have hi' : i = 0 ∨ i = 1 := by omega
        rcases hi' with hi' | hi'
        · exact ⟨pt (t : ℕ) 0, by simp, hi' ▸ hev⟩
        · exact ⟨pt (t : ℕ) 1, by simp, hi' ▸ hev⟩
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      have hv := hval t (k + 1) hk x
      rw [hin1 (q * (t : ℕ) + (k + 1)) (by rw [hmodk (t : ℕ) (k + 1) hk]; omega),
        hdivk (t : ℕ) (k + 1) hk, hmodk (t : ℕ) (k + 1) hk] at hv
      have hidx : N + (q * (t : ℕ) + (k + 1) - 1) = N + (q * (t : ℕ) + k) := by omega
      rw [hidx] at hv
      refine hv.trans ⟨?_, ?_⟩
      · rintro ⟨e, he, hev⟩
        have he' : e = N + (q * (t : ℕ) + k) ∨ e = pt (t : ℕ) (k + 1 + 1) := by simpa using he
        rcases he' with he' | he'
        · rw [he'] at hev
          obtain ⟨i, hi, hiv⟩ := ih'.mp hev
          exact ⟨i, by omega, hiv⟩
        · exact ⟨k + 1 + 1, le_refl _, he' ▸ hev⟩
      · rintro ⟨i, hi, hev⟩
        by_cases hik : i ≤ k + 1
        · exact ⟨N + (q * (t : ℕ) + k), by simp, ih'.mpr ⟨i, hik, hev⟩⟩
        · have hi' : i = k + 1 + 1 := by omega
          exact ⟨pt (t : ℕ) (k + 1 + 1), by simp, hi' ▸ hev⟩
  refine ⟨gates, fun t => N + (q * (t : ℕ) + (q - 1)), hlegal, htopo, ?_, hlen⟩
  intro t x
  show EV gates (N + (q * (t : ℕ) + (q - 1))) x = decide (∃ v ∈ L t, x v = true)
  have hc := hchain t x (q - 1) (by omega)
  have hiff : EV gates (N + (q * (t : ℕ) + (q - 1))) x = true ↔ ∃ v ∈ L t, x v = true := by
    refine hc.trans ⟨?_, ?_⟩
    · rintro ⟨i, hi, hev⟩
      have hlt : pt (t : ℕ) i < N := hpt1 _ i t.2 (by omega)
      refine ⟨⟨pt (t : ℕ) i, hlt⟩, (hpt2 t _).mpr ⟨i, by omega, rfl⟩, ?_⟩
      exact (EV_in gates (⟨pt (t : ℕ) i, hlt⟩ : Fin N) x).symm.trans hev
    · rintro ⟨v, hv, hxv⟩
      obtain ⟨i, hi, hiv⟩ := (hpt2 t v).mp hv
      refine ⟨i, by omega, ?_⟩
      rw [hiv]
      exact (EV_in gates v x).trans hxv
  by_cases hd : ∃ v ∈ L t, x v = true
  · rw [decide_eq_true hd]
    exact hiff.mpr hd
  · rw [decide_eq_false hd]
    by_contra hne
    exact hd (hiff.mp (by simpa using hne))

theorem x43main_aux : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ),
      (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
      (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
      (∀ (t : Fin N) (x : Fin N → Bool), (x p0 = true ∨ x p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → x u = true) →
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
      N * q ≤ gates.length) ∧
    ∃ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ),
      (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) ∧
      (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) ∧
      (∀ (t : Fin N) (x : Fin N → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) ∧
      gates.length = N * q := by
  intro q N L i0 p0 p1 hq hN hcard hinter hline h01 h0 h1
  refine ⟨fun gates o legal htopo hout => lower_bound q N L i0 p0 p1 hq hN hcard hinter hline
    h01 h0 h1 gates o legal htopo hout, ?_⟩
  have hex : ∀ t : Fin N, ∃ f : ℕ → ℕ, (∀ i, i < q + 1 → f i < N) ∧
      ∀ v : Fin N, v ∈ L t ↔ ∃ i, i < q + 1 ∧ f i = (v : ℕ) := by
    intro t
    refine ⟨fun i => if h : i < q + 1 then
      (((L t).orderEmbOfFin (hcard t) ⟨i, h⟩ : Fin N) : ℕ) else 0, ?_, ?_⟩
    · intro i hi
      simp only [dif_pos hi]
      exact Fin.is_lt _
    · intro v
      constructor
      · intro hv
        have hr : v ∈ Set.range ((L t).orderEmbOfFin (hcard t)) := by
          rw [Finset.range_orderEmbOfFin]
          exact Finset.mem_coe.mpr hv
        obtain ⟨k, hk⟩ := hr
        refine ⟨(k : ℕ), k.2, ?_⟩
        simp only [dif_pos k.2]
        rw [← hk]
      · rintro ⟨i, hi, hfi⟩
        simp only [dif_pos hi] at hfi
        have he : (L t).orderEmbOfFin (hcard t) ⟨i, hi⟩ = v := Fin.ext hfi
        rw [← he]
        exact Finset.orderEmbOfFin_mem _ _ _
  choose F hF1 hF2 using hex
  exact upper_core L (by omega) (fun t' i => if h : t' < N then F ⟨t', h⟩ i else 0)
    (fun t i ht hi => by simp only [dif_pos ht]; exact hF1 ⟨t, ht⟩ i hi)
    (fun t v => by simp only [dif_pos t.2]; exact hF2 t v)

lemma x44core : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ),
      (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
      (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
      (∀ (t : Fin N) (x : Fin N → Bool), (x p0 = true ∨ x p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → x u = true) →
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
      N * q ≤ gates.length :=
  fun q N L i0 p0 p1 a1 a2 a3 a4 a5 a6 a7 a8 =>
    (x43main_aux q N L i0 p0 p1 a1 a2 a3 a4 a5 a6 a7 a8).1

theorem main_aux : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ) (j h : Fin gates.length),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ gt.inputs.length ≤ 2) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (N + (h : ℕ)) :: r) →
    (∀ (t : Fin N) (x : Fin N → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (h : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v = p0))) = true → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (h : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v = p1))) = true →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (h : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = true →
    N * q + (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ N + (j : ℕ) ∈ (gates.get i).inputs)).card + 2 ≤ gates.length := by
  intro q N L i0 p0 p1 hq3 hN hcard hint hjoin h01 h0 h1 gates o j h hg htop hjop hone hhj hjin hout hp0 hp1 hco
  classical
  have key : ∀ t : Fin N, p0 ∈ L t → p1 ∈ L t → t = i0 := by
    intro t ht0 ht1
    by_contra hne
    have hc := hint t i0 hne
    have hsub : ({p0, p1} : Finset (Fin N)) ⊆ L t ∩ L i0 := by
      intro v hv
      rw [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact Finset.mem_inter.2 ⟨ht0, h0⟩
      · exact Finset.mem_inter.2 ⟨ht1, h1⟩
    have h2 := Finset.card_le_card hsub
    rw [hc, Finset.card_pair h01] at h2
    omega
  have hlt : N + (h : ℕ) < N + (j : ℕ) := by
    have : (h : ℕ) < (j : ℕ) := hhj
    omega
  have hF : ∀ x : Fin N → Bool, (x p0 = true ∨ x p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → x u = true) →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (h : ℕ)⟩ (List.ofFn x) = true := by
    intro x hx
    rcases hx with hx | hx | hx
    · refine x44hmono N gates j hg hone (fun v : Fin N => decide (v = p0)) x (fun v hv => ?_) _ hlt hp0
      rw [of_decide_eq_true hv]
      exact hx
    · refine x44hmono N gates j hg hone (fun v : Fin N => decide (v = p1)) x (fun v hv => ?_) _ hlt hp1
      rw [of_decide_eq_true hv]
      exact hx
    · refine x44hmono N gates j hg hone (fun v : Fin N => decide (v ∉ L i0)) x (fun v hv => ?_) _ hlt hco
      exact hx v (of_decide_eq_true hv)
  have htrue : PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (h : ℕ)⟩ (List.ofFn (fun _ : Fin N => true)) = true :=
    hF (fun _ : Fin N => true) (Or.inl rfl)
  have hy : ∀ t : Fin N,
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (h : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L t))) = true := by
    intro t
    apply hF
    by_cases ht0 : p0 ∈ L t
    · by_cases ht1 : p1 ∈ L t
      · right
        right
        intro u hu
        have ht := key t ht0 ht1
        rw [ht]
        exact decide_eq_true hu
      · right
        left
        exact decide_eq_true ht1
    · left
      exact decide_eq_true ht0
  obtain ⟨gates', out', hg', htop', hpre, hlen, hagree⟩ := x44dmain N N gates o j h hg htop hjop hone hhj hjin (by
    intro w
    refine ⟨fun _ : Fin N => true, fun v : Fin N => decide (v ∉ L w), htrue, hy w, ?_, ?_⟩
    · rw [hout]
      obtain ⟨u, hu⟩ : (L w).Nonempty := Finset.card_pos.mp (by
        rw [hcard]
        omega)
      exact decide_eq_true ⟨u, hu, rfl⟩
    · rw [hout]
      refine decide_eq_false ?_
      rintro ⟨v, hv, hh⟩
      exact (of_decide_eq_true hh) hv)
  have key2 := x44core q N L i0 p0 p1 hq3 hN hcard hint hjoin h01 h0 h1 gates' out' hg'
    (fun i w hw => htop' i.1 (gates'.get i) (List.getElem?_eq_getElem i.2) w hw)
    (fun t x hx => (hagree t x (hF x hx)).trans (hout t x))
  omega

end PEqualNP.Outside.L_meta_1644

theorem PEqualNP.Outside.L_meta_1644 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ) (j h : Fin gates.length),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ gt.inputs.length ≤ 2) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (N + (h : ℕ)) :: r) →
    (∀ (t : Fin N) (x : Fin N → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (h : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v = p0))) = true → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (h : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v = p1))) = true →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (h : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = true →
    N * q + (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ N + (j : ℕ) ∈ (gates.get i).inputs)).card + 2 ≤ gates.length :=
  PEqualNP.Outside.L_meta_1644.main_aux
