import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2350

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_foldl, foldl_stepWire_length, List.length_ofFn]

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]


def W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, foldl_stepWire_length, hpre_len]
  have hCj : W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + k) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge_length w0 i (by omega)

lemma W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    W n C x u = x ⟨u, hu⟩ := by
  simp only [W]
  rw [wires_eq_foldl, foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

open PEqualNP.CleanedNonEdge in
lemma orFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

open PEqualNP.CleanedNonEdge in
lemma orStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
    x ∈ (orStep n cs g).getD cs.length [] ↔ x = cs.length ∨ (g.op = GateOp.or ∧
      ∃ w ∈ g.inputs, n ≤ w ∧ w < n + cs.length ∧ x ∈ cs.getD (w - n) []) := by
  by_cases h : g.op = GateOp.or
  · simp only [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, h,
      ↓reduceIte, true_and, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
      List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro (h1 | ⟨w, ⟨hw, hn, hlt⟩, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, hw, hn, hlt, hx⟩
    · rintro (h1 | ⟨w, hw, hn, hlt, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, ⟨hw, hn, hlt⟩, hx⟩
  · simp [orStep, List.getD_eq_getElem?_getD, h]

open PEqualNP.CleanedNonEdge in
lemma orStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.CleanedNonEdge in
lemma orFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact orStep_getD_lt n cs g k hk

open PEqualNP.CleanedNonEdge in
lemma orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ x ∈ (orSets n C).getD (w - n) []) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [orFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : (orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k [] := by
    rw [hc, orFold_getD_lt n post _ k (by omega)]
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, orFold_getD_lt n post _ m (by omega)]
    exact orStep_getD_lt n _ gk m (by omega)
  have h3 := orStep_mem_last n (pre.foldl (orStep n) []) gk x
  rw [hl0] at h3
  rw [h1, h3]
  constructor
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [h2 (w - n) (by omega)]; exact hx⟩
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [← h2 (w - n) (by omega)]; exact hx⟩

open PEqualNP.CleanedNonEdge PEqualNP.ReadK PEqualNP.TopForm

lemma orReaches_self (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    OrReaches n C (n + j) j := by
  unfold OrReaches
  refine ⟨Nat.le_add_right n j, ?_⟩
  rw [Nat.add_sub_cancel_left, orSets_mem_iff n C j j hj]
  exact Or.inl rfl

lemma orReaches_step (n : ℕ) (C : Circuit) (j i g : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : OrReaches n C i g) : OrReaches n C (n + j) g := by
  unfold OrReaches at h ⊢
  refine ⟨Nat.le_add_right n j, ?_⟩
  rw [Nat.add_sub_cancel_left, orSets_mem_iff n C j g hj]
  exact Or.inr ⟨hop, i, hi, h.1, hlt, h.2⟩

lemma mem_filter_iff_gen {α : Type} (p : α → Prop) (d : DecidablePred p) (s : Finset α) (a : α) :
    a ∈ @Finset.filter α p d s ↔ a ∈ s ∧ p a :=
  @Finset.mem_filter α p d s a

lemma mem_orIn (n : ℕ) (C : Circuit) (w : ℕ) (i : Fin n) :
    i ∈ orIn n C w ↔ ((i : ℕ) = w ∨ ∃ k < C.gates.length,
      OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧ (i : ℕ) ∈ (gateAt C k).inputs) := by
  unfold orIn
  exact ⟨fun h => ((mem_filter_iff_gen _ _ _ _).1 h).2,
    fun h => (mem_filter_iff_gen _ _ _ _).2 ⟨Finset.mem_univ _, h⟩⟩

lemma orIn_up (n : ℕ) (C : Circuit) (j i : ℕ) (a : Fin n) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : a ∈ orIn n C i) : a ∈ orIn n C (n + j) := by
  rw [mem_orIn] at h ⊢
  right
  rcases h with h | ⟨k, hk, hr, hopk, hin⟩
  · exact ⟨j, hj, orReaches_self n C j hj, hop, by rw [h]; exact hi⟩
  · exact ⟨k, hk, orReaches_step n C j i k hj hop hi hlt hr, hopk, hin⟩

def FR (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) : List (List ℕ) :=
  match g.op with
  | GateOp.or => (g.inputs.map fun i => R.getD i []).foldl (fun acc A => A.foldl insertNew acc) []
  | GateOp.and => (g.inputs.map fun i => R.getD i []).foldl (andStep k) [S.map fun _ => 0]
  | _ => []

def stepR (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) : List (List (List ℕ)) :=
  R ++ [FR S k R g]

lemma readVectors_eq (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) :
    readVectors C n S k = C.gates.foldl (stepR S k) ((List.range n).map (leafVectors S k)) := by
  first
    | rfl
    | (unfold readVectors; congr 1; funext R g; rcases g with ⟨op, ins⟩; cases op <;> rfl)

lemma FR_or (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) (h : g.op = GateOp.or) :
    FR S k R g =
      (g.inputs.map fun i => R.getD i []).foldl (fun acc A => A.foldl insertNew acc) [] := by
  obtain ⟨op, ins⟩ := g
  have h2 : op = GateOp.or := h
  subst h2
  rfl

lemma FR_and (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate)
    (h : g.op = GateOp.and) :
    FR S k R g = (g.inputs.map fun i => R.getD i []).foldl (andStep k) [S.map fun _ => 0] := by
  obtain ⟨op, ins⟩ := g
  have h2 : op = GateOp.and := h
  subst h2
  rfl

lemma foldR_length (S : List ℕ) (k : ℕ) (gs : List Gate) (R : List (List (List ℕ))) :
    (gs.foldl (stepR S k) R).length = R.length + gs.length := by
  induction gs generalizing R with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepR]
    omega

lemma foldR_getD_lt (S : List ℕ) (k : ℕ) (gs : List Gate) (R : List (List (List ℕ))) (i : ℕ)
    (hi : i < R.length) : (gs.foldl (stepR S k) R).getD i [] = R.getD i [] := by
  induction gs generalizing R with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepR S k R g).length := by simp [stepR]; omega
    rw [ih (stepR S k R g) hlt]
    simp [stepR, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

def RV (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (w : ℕ) : List (List ℕ) :=
  (readVectors C n S k).getD w []

lemma RV_input (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (w : ℕ) (hw : w < n) :
    RV C n S k w = leafVectors S k w := by
  simp only [RV]
  rw [readVectors_eq, foldR_getD_lt S k C.gates ((List.range n).map (leafVectors S k)) w
    (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

lemma RV_gate (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (j : ℕ) (hj : j < C.gates.length) :
    ∃ Rp : List (List (List ℕ)),
      (∀ i, i < n + j → Rp.getD i [] = RV C n S k i) ∧
      RV C n S k (n + j) = FR S k Rp (gateAt C j) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates C.gates j hj
  have hga : gateAt C j = gj := by rw [gateAt_eq C j hj]; exact hgj
  rw [hga]
  obtain ⟨Rp, hRp⟩ : ∃ Rp, Rp = pre.foldl (stepR S k) ((List.range n).map (leafVectors S k)) :=
    ⟨_, rfl⟩
  have hlen : Rp.length = n + j := by
    rw [hRp, foldR_length]
    simp only [List.length_map, List.length_range, hpre_len]
  have hall : readVectors C n S k = post.foldl (stepR S k) (stepR S k Rp gj) := by
    rw [readVectors_eq, hgs, List.foldl_append, List.foldl_cons, hRp]
  have hlen1 : (stepR S k Rp gj).length = n + j + 1 := by
    simp [stepR, hlen]
  refine ⟨Rp, ?_, ?_⟩
  · intro i hi
    simp only [RV]
    rw [hall, foldR_getD_lt S k post (stepR S k Rp gj) i (by omega)]
    simp [stepR, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (show i < Rp.length by omega)]
  · simp only [RV]
    rw [hall, foldR_getD_lt S k post (stepR S k Rp gj) (n + j) (by omega)]
    simp [stepR, List.getD_eq_getElem?_getD, hlen]

lemma mem_foldl_insertNew (L : List (List ℕ)) (acc : List (List ℕ)) (v : List ℕ)
    (h : v ∈ L.foldl insertNew acc) : v ∈ acc ∨ v ∈ L := by
  induction L generalizing acc with
  | nil => exact Or.inl h
  | cons x L ih =>
    rw [List.foldl_cons] at h
    rcases ih _ h with h1 | h1
    · unfold insertNew at h1
      split_ifs at h1
      · exact Or.inl h1
      · rcases List.mem_append.1 h1 with h2 | h2
        · exact Or.inl h2
        · have h3 : v = x := by simpa using h2
          exact Or.inr (by simp [h3])
    · exact Or.inr (List.mem_cons_of_mem _ h1)

lemma mem_andStep (k : ℕ) (A B : List (List ℕ)) (v : List ℕ) (h : v ∈ andStep k A B) :
    ∃ u ∈ A, ∃ u2 ∈ B, v = capAdd k u u2 := by
  unfold andStep at h
  rcases mem_foldl_insertNew _ _ _ h with h1 | h1
  · simp at h1
  · simp only [List.mem_flatMap, List.mem_map] at h1
    obtain ⟨u, hu, u2, hu2, rfl⟩ := h1
    exact ⟨u, hu, u2, hu2, rfl⟩

lemma capAdd_pair (k x1 y1 x2 y2 : ℕ) :
    capAdd k [x1, y1] [x2, y2] = [min (x1 + x2) (k + 1), min (y1 + y2) (k + 1)] := by
  first
    | rfl
    | simp [capAdd]

lemma leaf_eq2 (a b t : ℕ) :
    leafVectors [a, b] 2 t =
      if t ∈ [a, b] then [[if a = t then 1 else 0, if b = t then 1 else 0]] else [] := by
  first
    | rfl
    | (unfold leafVectors; simp)

lemma mem_foldl_insertNew_of (L : List (List ℕ)) (acc : List (List ℕ)) (v : List ℕ)
    (h : v ∈ acc ∨ v ∈ L) : v ∈ L.foldl insertNew acc := by
  induction L generalizing acc with
  | nil =>
    rcases h with h | h
    · exact h
    · simp at h
  | cons x L ih =>
    rw [List.foldl_cons]
    apply ih
    rcases h with h | h
    · left
      unfold insertNew
      split_ifs
      · exact h
      · exact List.mem_append_left _ h
    · rcases List.mem_cons.1 h with h3 | h3
      · left
        unfold insertNew
        split_ifs with hx
        · rw [h3]
          exact hx
        · rw [h3]
          simp
      · right
        exact h3

lemma andStep_mem (k : ℕ) (A B : List (List ℕ)) (u u2 : List ℕ) (hu : u ∈ A) (hu2 : u2 ∈ B) :
    capAdd k u u2 ∈ andStep k A B := by
  unfold andStep
  apply mem_foldl_insertNew_of
  right
  simp only [List.mem_flatMap, List.mem_map]
  exact ⟨u, hu, u2, hu2, rfl⟩

lemma mem_union_fold (Ls : List (List (List ℕ))) (acc : List (List ℕ)) (v : List ℕ)
    (h : v ∈ acc ∨ ∃ A ∈ Ls, v ∈ A) :
    v ∈ Ls.foldl (fun acc A => A.foldl insertNew acc) acc := by
  induction Ls generalizing acc with
  | nil =>
    rcases h with h | ⟨A, hA, _⟩
    · exact h
    · simp at hA
  | cons B Ls ih =>
    rw [List.foldl_cons]
    apply ih
    rcases h with h | ⟨A, hA, hvA⟩
    · exact Or.inl (mem_foldl_insertNew_of _ _ _ (Or.inl h))
    · rcases List.mem_cons.1 hA with h3 | h3
      · exact Or.inl (mem_foldl_insertNew_of _ _ _ (Or.inr (by rw [← h3]; exact hvA)))
      · exact Or.inr ⟨A, h3, hvA⟩

lemma RV_or_mem (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (j i : ℕ) (v : List ℕ)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or)
    (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j) (hv : v ∈ RV C n S k i) :
    v ∈ RV C n S k (n + j) := by
  obtain ⟨Rp, hRp, hRV⟩ := RV_gate C n S k j hj
  rw [hRV, FR_or _ _ _ _ hop]
  apply mem_union_fold
  right
  exact ⟨Rp.getD i [], List.mem_map.2 ⟨i, hi, rfl⟩, by rw [hRp i hlt]; exact hv⟩

lemma RV_and_mem (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (j i1 i2 : ℕ)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (hinp : (gateAt C j).inputs = [i1, i2]) (h1 : i1 < n + j) (h2 : i2 < n + j)
    (u1 u2 : List ℕ) (m1 : u1 ∈ RV C n S k i1) (m2 : u2 ∈ RV C n S k i2) :
    capAdd k (capAdd k (S.map fun _ => 0) u1) u2 ∈ RV C n S k (n + j) := by
  obtain ⟨Rp, hRp, hRV⟩ := RV_gate C n S k j hj
  rw [hRV, FR_and _ _ _ _ hop, hinp]
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
    hRp i1 h1, hRp i2 h2]
  exact andStep_mem k _ _ _ _ (andStep_mem k _ _ _ _ (List.mem_singleton.2 rfl) m1) m2

theorem RV_ind (n : ℕ) (C : Circuit) (S : List ℕ) (k : ℕ) (hC : IsAO2 n C)
    (P : ℕ → List ℕ → Prop)
    (hleaf : ∀ t, t < n → ∀ v ∈ leafVectors S k t, P t v)
    (hor : ∀ j i, j < C.gates.length → (gateAt C j).op = GateOp.or →
      i ∈ (gateAt C j).inputs → i < n + j → ∀ v, P i v → P (n + j) v)
    (hand : ∀ j i1 i2, j < C.gates.length → (gateAt C j).op = GateOp.and →
      (gateAt C j).inputs = [i1, i2] → i1 < n + j → i2 < n + j → ∀ u1 u2, P i1 u1 → P i2 u2 →
      P (n + j) (capAdd k (capAdd k (S.map fun _ => 0) u1) u2)) :
    ∀ t, ∀ v ∈ RV C n S k t, P t v := by
  obtain ⟨hAnd, hBack, hTwo⟩ := hC
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro v hv
    by_cases htn : t < n
    · rw [RV_input C n S k t htn] at hv
      exact hleaf t htn v hv
    · obtain ⟨j, rfl⟩ : ∃ j, t = n + j := ⟨t - n, by omega⟩
      by_cases hj : j < C.gates.length
      · have hmem : gateAt C j ∈ C.gates := by
          rw [gateAt_eq C j hj]
          exact List.getElem_mem hj
        have hlen2 := hTwo _ hmem
        have hback := hBack j hj
        obtain ⟨Rp, hRp, hRV⟩ := RV_gate C n S k j hj
        rcases hinp : (gateAt C j).inputs with _ | ⟨i1, _ | ⟨i2, _ | ⟨i3, rest⟩⟩⟩
        · exfalso
          rw [hinp] at hlen2
          simp at hlen2
        · exfalso
          rw [hinp] at hlen2
          simp at hlen2
        · have hm1 : i1 ∈ (gateAt C j).inputs := by rw [hinp]; simp
          have hm2 : i2 ∈ (gateAt C j).inputs := by rw [hinp]; simp
          have hi1 : i1 < n + j := hback i1 hm1
          have hi2 : i2 < n + j := hback i2 hm2
          rcases hAnd _ hmem with hop | hop
          · rw [hRV, FR_and _ _ _ _ hop, hinp] at hv
            simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
              hRp i1 hi1, hRp i2 hi2] at hv
            obtain ⟨t2, ht2, u2, hu2, rfl⟩ := mem_andStep _ _ _ _ hv
            obtain ⟨z, hz, u1, hu1, rfl⟩ := mem_andStep _ _ _ _ ht2
            have hz2 : z = S.map fun _ => 0 := List.mem_singleton.1 hz
            subst hz2
            exact hand j i1 i2 hj hop hinp hi1 hi2 u1 u2 (ih i1 hi1 u1 hu1) (ih i2 hi2 u2 hu2)
          · rw [hRV, FR_or _ _ _ _ hop, hinp] at hv
            simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
              hRp i1 hi1, hRp i2 hi2] at hv
            rcases mem_foldl_insertNew _ _ _ hv with h | h
            · rcases mem_foldl_insertNew _ _ _ h with h3 | h3
              · simp at h3
              · exact hor j i1 hj hop hm1 hi1 v (ih i1 hi1 v h3)
            · exact hor j i2 hj hop hm2 hi2 v (ih i2 hi2 v h)
        · exfalso
          rw [hinp] at hlen2
          simp at hlen2
      · exfalso
        have hnil : RV C n S k (n + j) = [] := by
          simp only [RV]
          rw [readVectors_eq]
          exact List.getD_eq_default _ _ (by
            rw [foldR_length]
            simp only [List.length_map, List.length_range]
            omega)
        rw [hnil] at hv
        simp at hv

def Sw (n : ℕ) (C : Circuit) (u w : ℕ) (t : ℕ) (v : List ℕ) : Prop :=
  ∃ x y, v = [x, y] ∧ [y, x] ∈ RV C n [w, u] 2 t

theorem sw_mem (n : ℕ) (C : Circuit) (u w : ℕ) (hC : IsAO2 n C) :
    ∀ t, ∀ v ∈ RV C n [u, w] 2 t, Sw n C u w t v := by
  apply RV_ind n C [u, w] 2 hC (Sw n C u w)
  · intro t ht v hv
    unfold Sw
    rw [leaf_eq2] at hv
    rw [RV_input C n _ 2 t ht, leaf_eq2]
    by_cases hm : t ∈ [u, w]
    · have hm2 : t ∈ [w, u] := by
        rcases List.mem_cons.1 hm with h | h
        · exact List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl h)))
        · exact List.mem_cons.2 (Or.inl (List.mem_singleton.1 h))
      rw [if_pos hm] at hv
      rw [if_pos hm2]
      exact ⟨_, _, List.mem_singleton.1 hv, List.mem_singleton.2 rfl⟩
    · rw [if_neg hm] at hv
      simp at hv
  · intro j i hj hop hi hlt v hS
    obtain ⟨x, y, hv, hmem⟩ := hS
    exact ⟨x, y, hv, RV_or_mem C n _ 2 j i _ hj hop hi hlt hmem⟩
  · intro j i1 i2 hj hop hinp hi1 hi2 u1 u2 h1 h2
    obtain ⟨x1, y1, rfl, m1⟩ := h1
    obtain ⟨x2, y2, rfl, m2⟩ := h2
    refine ⟨min (min (0 + x1) (2 + 1) + x2) (2 + 1),
      min (min (0 + y1) (2 + 1) + y2) (2 + 1), ?_, ?_⟩
    · show capAdd 2 (capAdd 2 [0, 0] [x1, y1]) [x2, y2] = _
      rw [capAdd_pair, capAdd_pair]
    · have h3 := RV_and_mem C n [w, u] 2 j i1 i2 hj hop hinp hi1 hi2 _ _ m1 m2
      have h4 : capAdd 2 (capAdd 2 [0, 0] [y1, x1]) [y2, x2] ∈ RV C n [w, u] 2 (n + j) := h3
      rw [capAdd_pair, capAdd_pair] at h4
      exact h4

lemma reads_swap (n : ℕ) (C : Circuit) (u w : ℕ) (hC : IsAO2 n C)
    (h : readsAtMost C n [u, w] 2 = true) : readsAtMost C n [w, u] 2 = true := by
  unfold readsAtMost at h ⊢
  rw [List.any_eq_true] at h ⊢
  obtain ⟨v, hv, hall⟩ := h
  obtain ⟨x, y, rfl, hm⟩ := sw_mem n C u w hC C.output v hv
  refine ⟨[y, x], hm, ?_⟩
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq] at hall ⊢
  exact ⟨hall.2, hall.1⟩

def Rr (n : ℕ) (C : Circuit) (a b : ℕ) : Prop :=
  Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧
    (gateAt C rj).op = GateOp.or ∧ ra ∈ (gateAt C rj).inputs) a b

def Tr (n : ℕ) (C : Circuit) (tt : ℕ) (tL : List (ℕ × ℕ)) : Prop :=
  ∀ Q : ℕ → List (ℕ × ℕ) → Prop,
    (∀ (qv qt : ℕ), qv < n → Rr n C qv qt → Q qt [(qt, qv)]) →
    (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length →
      (gateAt C qj).op = GateOp.and → Rr n C (n + qj) qt →
      Q ((gateAt C qj).inputs.getD 0 0) qL1 → Q ((gateAt C qj).inputs.getD 1 0) qL2 →
      Q qt (qL1 ++ qL2)) → Q tt tL

lemma Rr_refl (n : ℕ) (C : Circuit) (t : ℕ) : Rr n C t t := by
  unfold Rr
  exact Relation.ReflTransGen.refl

lemma Rr_step (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j) :
    Rr n C i (n + j) := by
  unfold Rr
  exact Relation.ReflTransGen.single ⟨hlt, j, rfl, hj, hop, hi⟩

lemma Rr_trans (n : ℕ) (C : Circuit) (a b c : ℕ) (h1 : Rr n C a b) (h2 : Rr n C b c) :
    Rr n C a c := by
  unfold Rr at h1 h2 ⊢
  exact Relation.ReflTransGen.trans h1 h2

lemma W_or_up (n : ℕ) (C : Circuit) (z : Fin n → Bool) (j i : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (hz : W n C z i = true) : W n C z (n + j) = true := by
  rw [W_gate n C z j hj, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
  exact ⟨i, hi, by simp only [hlt, ite_true]; exact hz⟩

lemma W_and_up (n : ℕ) (C : Circuit) (z : Fin n → Bool) (j i1 i2 : ℕ)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (hinp : (gateAt C j).inputs = [i1, i2]) (h1 : i1 < n + j) (h2 : i2 < n + j)
    (hz1 : W n C z i1 = true) (hz2 : W n C z i2 = true) : W n C z (n + j) = true := by
  rw [W_gate n C z j hj, hop, hinp]
  simp [GateOp.eval, h1, h2, hz1, hz2]

lemma Rr_W (n : ℕ) (C : Circuit) (z : Fin n → Bool) (a t : ℕ) (h : Rr n C a t)
    (ha : W n C z a = true) : W n C z t = true := by
  unfold Rr at h
  induction h with
  | refl => exact ha
  | tail _ hstep ih =>
    obtain ⟨hlt, rj, rfl, hrj, hop, hin⟩ := hstep
    exact W_or_up n C z rj _ hrj hop hin hlt ih

lemma Tr_leaf (n : ℕ) (C : Circuit) (qv qt : ℕ) (h : qv < n) (hr : Rr n C qv qt) :
    Tr n C qt [(qt, qv)] := by
  intro Q hl ha
  exact hl qv qt h hr

lemma Tr_and (n : ℕ) (C : Circuit) (qj qt : ℕ) (L1 L2 : List (ℕ × ℕ))
    (hj : qj < C.gates.length) (hop : (gateAt C qj).op = GateOp.and)
    (hr : Rr n C (n + qj) qt) (t1 : Tr n C ((gateAt C qj).inputs.getD 0 0) L1)
    (t2 : Tr n C ((gateAt C qj).inputs.getD 1 0) L2) : Tr n C qt (L1 ++ L2) := by
  intro Q hl ha
  exact ha qj qt L1 L2 hj hop hr (t1 Q hl ha) (t2 Q hl ha)

lemma Tr_W (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (q : ℕ) (hq : q < n) (t : ℕ)
    (L : List (ℕ × ℕ)) (hT : Tr n C t L) (hall : ∀ e ∈ L, e.2 = q) :
    W n C (fun k : Fin n => decide (k.val = q)) t = true := by
  obtain ⟨hAnd, hBack, hTwo⟩ := hC
  revert hall
  refine hT (fun t L => (∀ e ∈ L, e.2 = q) →
    W n C (fun k : Fin n => decide (k.val = q)) t = true) ?_ ?_
  · intro qv qt hqv hr hall
    have hqq : qv = q := hall (qt, qv) (List.mem_singleton.2 rfl)
    rw [hqq] at hr
    exact Rr_W n C _ q qt hr (by rw [W_input n C _ q hq]; exact decide_eq_true rfl)
  · intro qj qt L1 L2 hj hop hr h1 h2 hall
    have hmem : gateAt C qj ∈ C.gates := by
      rw [gateAt_eq C qj hj]
      exact List.getElem_mem hj
    have hlen2 := hTwo _ hmem
    have hback := hBack qj hj
    rcases hinp : (gateAt C qj).inputs with _ | ⟨i1, _ | ⟨i2, _ | ⟨i3, rest⟩⟩⟩
    · exfalso
      rw [hinp] at hlen2
      simp at hlen2
    · exfalso
      rw [hinp] at hlen2
      simp at hlen2
    · rw [hinp] at h1 h2
      have h1b : W n C (fun k : Fin n => decide (k.val = q)) i1 = true :=
        h1 (fun e he => hall e (List.mem_append_left _ he))
      have h2b : W n C (fun k : Fin n => decide (k.val = q)) i2 = true :=
        h2 (fun e he => hall e (List.mem_append_right _ he))
      exact Rr_W n C _ _ qt hr (W_and_up n C _ qj i1 i2 hj hop hinp
        (hback i1 (by rw [hinp]; simp)) (hback i2 (by rw [hinp]; simp)) h1b h2b)
    · exfalso
      rw [hinp] at hlen2
      simp at hlen2

def cnt (q : ℕ) (L : List (ℕ × ℕ)) : ℕ := (L.filter (fun e => decide (e.2 = q))).length

lemma cnt_append (q : ℕ) (L1 L2 : List (ℕ × ℕ)) :
    cnt q (L1 ++ L2) = cnt q L1 + cnt q L2 := by
  simp [cnt]

lemma cnt_single_eq (q s : ℕ) : cnt q [(s, q)] = 1 := by
  simp [cnt]

lemma cnt_single_ne (q s p : ℕ) (h : p ≠ q) : cnt q [(s, p)] = 0 := by
  simp [cnt, h]

lemma cnt_zero (q : ℕ) (L : List (ℕ × ℕ)) (h : cnt q L = 0) (e : ℕ × ℕ) (he : e ∈ L) :
    e.2 ≠ q := by
  intro heq
  have h3 : e ∈ L.filter (fun e => decide (e.2 = q)) :=
    List.mem_filter.2 ⟨he, decide_eq_true heq⟩
  unfold cnt at h
  rw [List.eq_nil_of_length_eq_zero h] at h3
  simp at h3

def Good (n : ℕ) (C : Circuit) (u w : ℕ) (s : ℕ) (v : List ℕ) : Prop :=
  ∃ x y, v = [x, y] ∧
    ((∃ qv, qv < n ∧ Rr n C qv s ∧ ((qv = u ∧ x = 1 ∧ y = 0) ∨ (qv = w ∧ x = 0 ∧ y = 1))) ∨
      (∃ j0 L1 L2, j0 < C.gates.length ∧ (gateAt C j0).op = GateOp.and ∧ Rr n C (n + j0) s ∧
        Tr n C ((gateAt C j0).inputs.getD 0 0) L1 ∧ Tr n C ((gateAt C j0).inputs.getD 1 0) L2 ∧
        (∀ e ∈ L1 ++ L2, e.2 = u ∨ e.2 = w) ∧ x = min (cnt u (L1 ++ L2)) 3 ∧
        y = min (cnt w (L1 ++ L2)) 3))

lemma Good_T (n : ℕ) (C : Circuit) (u w : ℕ) (huw : u ≠ w) (s : ℕ) (v : List ℕ)
    (h : Good n C u w s v) :
    ∃ x y L, v = [x, y] ∧ Tr n C s L ∧ (∀ e ∈ L, e.2 = u ∨ e.2 = w) ∧
      x = min (cnt u L) 3 ∧ y = min (cnt w L) 3 := by
  obtain ⟨x, y, hv, h | h⟩ := h
  · obtain ⟨qv, hqv, hr, h | h⟩ := h
    · obtain ⟨hq, hx, hy⟩ := h
      refine ⟨x, y, [(s, qv)], hv, Tr_leaf n C qv s hqv hr, ?_, ?_, ?_⟩
      · intro e he
        rw [List.mem_singleton.1 he]
        exact Or.inl hq
      · rw [hq, cnt_single_eq]
        omega
      · rw [hq, cnt_single_ne w s u huw]
        omega
    · obtain ⟨hq, hx, hy⟩ := h
      refine ⟨x, y, [(s, qv)], hv, Tr_leaf n C qv s hqv hr, ?_, ?_, ?_⟩
      · intro e he
        rw [List.mem_singleton.1 he]
        exact Or.inr hq
      · rw [hq, cnt_single_ne u s w (Ne.symm huw)]
        omega
      · rw [hq, cnt_single_eq]
        omega
  · obtain ⟨j0, L1, L2, hj0, hop, hr, t1, t2, hall, hx, hy⟩ := h
    exact ⟨x, y, L1 ++ L2, hv, Tr_and n C j0 s L1 L2 hj0 hop hr t1 t2, hall, hx, hy⟩

theorem good_all (n : ℕ) (C : Circuit) (u w : ℕ) (hC : IsAO2 n C) (huw : u ≠ w) :
    ∀ t, ∀ v ∈ RV C n [u, w] 2 t, Good n C u w t v := by
  apply RV_ind n C [u, w] 2 hC (Good n C u w)
  · intro t ht v hv
    rw [leaf_eq2] at hv
    by_cases htu : u = t
    · have htw : ¬ w = t := by omega
      rw [if_pos (List.mem_cons.2 (Or.inl htu.symm)), if_pos htu, if_neg htw] at hv
      have hv2 : v = [1, 0] := List.mem_singleton.1 hv
      exact ⟨1, 0, hv2, Or.inl ⟨t, ht, Rr_refl n C t, Or.inl ⟨htu.symm, rfl, rfl⟩⟩⟩
    · by_cases htw : w = t
      · rw [if_pos (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl htw.symm)))),
          if_neg htu, if_pos htw] at hv
        have hv2 : v = [0, 1] := List.mem_singleton.1 hv
        exact ⟨0, 1, hv2, Or.inl ⟨t, ht, Rr_refl n C t, Or.inr ⟨htw.symm, rfl, rfl⟩⟩⟩
      · exfalso
        have hm : ¬ t ∈ [u, w] := by
          intro hm
          rcases List.mem_cons.1 hm with h | h
          · exact htu h.symm
          · exact htw (List.mem_singleton.1 h).symm
        rw [if_neg hm] at hv
        simp at hv
  · intro j i hj hop hi hlt v hG
    obtain ⟨x, y, hv, h | h⟩ := hG
    · obtain ⟨qv, hqv, hr, hc⟩ := h
      exact ⟨x, y, hv, Or.inl ⟨qv, hqv,
        Rr_trans n C _ _ _ hr (Rr_step n C j i hj hop hi hlt), hc⟩⟩
    · obtain ⟨j0, L1, L2, hj0, hop0, hr, t1, t2, hall, hx, hy⟩ := h
      exact ⟨x, y, hv, Or.inr ⟨j0, L1, L2, hj0, hop0,
        Rr_trans n C _ _ _ hr (Rr_step n C j i hj hop hi hlt), t1, t2, hall, hx, hy⟩⟩
  · intro j i1 i2 hj hop hinp hi1 hi2 u1 u2 hG1 hG2
    obtain ⟨x1, y1, L1, rfl, t1, hall1, hx1, hy1⟩ := Good_T n C u w huw i1 u1 hG1
    obtain ⟨x2, y2, L2, rfl, t2, hall2, hx2, hy2⟩ := Good_T n C u w huw i2 u2 hG2
    refine ⟨min (min (0 + x1) (2 + 1) + x2) (2 + 1),
      min (min (0 + y1) (2 + 1) + y2) (2 + 1), ?_,
      Or.inr ⟨j, L1, L2, hj, hop, Rr_refl n C (n + j), ?_, ?_, ?_, ?_, ?_⟩⟩
    · show capAdd 2 (capAdd 2 [0, 0] [x1, y1]) [x2, y2] = _
      rw [capAdd_pair, capAdd_pair]
    · rw [hinp]
      exact t1
    · rw [hinp]
      exact t2
    · intro e he
      rcases List.mem_append.1 he with h | h
      · exact hall1 e h
      · exact hall2 e h
    · rw [cnt_append]
      omega
    · rw [cnt_append]
      omega

theorem part2 (n : ℕ) (C : Circuit) (u w : ℕ) (hC : IsAO2 n C) (hu : u < n) (hw : w < n)
    (huw : u ≠ w)
    (h1 : circuitFun n C (fun k1 : Fin n => decide (k1.val = u)) = false)
    (h2 : circuitFun n C (fun k2 : Fin n => decide (k2.val = w)) = false)
    (hread : readsAtMost C n [u, w] 2 = true) :
    ∃ L : List (ℕ × ℕ), (∃ (j0 : ℕ) (L1 L2 : List (ℕ × ℕ)), j0 < C.gates.length ∧
      (gateAt C j0).op = GateOp.and ∧ Rr n C (n + j0) C.output ∧
      Tr n C ((gateAt C j0).inputs.getD 0 0) L1 ∧ Tr n C ((gateAt C j0).inputs.getD 1 0) L2 ∧
      L = L1 ++ L2) ∧ (∀ gv ∈ L, gv.2 = u ∨ gv.2 = w) ∧
      cnt u L ∈ ({1, 2} : Finset ℕ) ∧ cnt w L ∈ ({1, 2} : Finset ℕ) := by
  unfold readsAtMost at hread
  rw [List.any_eq_true] at hread
  obtain ⟨v, hv, hall⟩ := hread
  obtain ⟨x, y, hveq, h | h⟩ := good_all n C u w hC huw C.output v hv
  · exfalso
    obtain ⟨qv, hqv, hr, hc | hc⟩ := h
    · have h3 : circuitFun n C (fun k1 : Fin n => decide (k1.val = u)) = true :=
        Rr_W n C (fun k1 : Fin n => decide (k1.val = u)) qv C.output hr
          (by rw [W_input n C _ qv hqv]; exact decide_eq_true hc.1)
      rw [h1] at h3
      exact Bool.false_ne_true h3
    · have h3 : circuitFun n C (fun k2 : Fin n => decide (k2.val = w)) = true :=
        Rr_W n C (fun k2 : Fin n => decide (k2.val = w)) qv C.output hr
          (by rw [W_input n C _ qv hqv]; exact decide_eq_true hc.1)
      rw [h2] at h3
      exact Bool.false_ne_true h3
  · obtain ⟨j0, L1, L2, hj0, hop, hr, t1, t2, hLall, hx, hy⟩ := h
    subst hveq
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
      decide_eq_true_eq] at hall
    obtain ⟨hx2, hy2⟩ := hall
    have hT : Tr n C C.output (L1 ++ L2) := Tr_and n C j0 C.output L1 L2 hj0 hop hr t1 t2
    have hcu : cnt u (L1 ++ L2) ≠ 0 := by
      intro h0
      have hallw : ∀ e ∈ L1 ++ L2, e.2 = w := by
        intro e he
        rcases hLall e he with h | h
        · exact absurd h (cnt_zero u _ h0 e he)
        · exact h
      have h3 : circuitFun n C (fun k2 : Fin n => decide (k2.val = w)) = true :=
        Tr_W n C hC w hw C.output _ hT hallw
      rw [h2] at h3
      exact Bool.false_ne_true h3
    have hcw : cnt w (L1 ++ L2) ≠ 0 := by
      intro h0
      have hallu : ∀ e ∈ L1 ++ L2, e.2 = u := by
        intro e he
        rcases hLall e he with h | h
        · exact h
        · exact absurd h (cnt_zero w _ h0 e he)
      have h3 : circuitFun n C (fun k1 : Fin n => decide (k1.val = u)) = true :=
        Tr_W n C hC u hu C.output _ hT hallu
      rw [h1] at h3
      exact Bool.false_ne_true h3
    refine ⟨L1 ++ L2, ⟨j0, L1, L2, hj0, hop, hr, t1, t2, rfl⟩, hLall, ?_, ?_⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      omega

theorem main_aux : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (u w : ℕ), PEqualNP.TopForm.IsAO2 n C → u < n → w < n → u ≠ w → PEqualNP.MetaComplexity.circuitFun n C (fun k1 : Fin n => decide (k1.val = u)) = false → PEqualNP.MetaComplexity.circuitFun n C (fun k2 : Fin n => decide (k2.val = w)) = false → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → ∀ T : ℕ → List (ℕ × ℕ) → Prop, T = (fun tt tL => ∀ Q : ℕ → List (ℕ × ℕ) → Prop, (∀ (qv qt : ℕ), qv < n → R qv qt → Q qt [(qt, qv)]) → (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C qj).op = PEqualNP.CircuitLowerBounds.GateOp.and → R (n + qj) qt → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 0 0) qL1 → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 1 0) qL2 → Q qt (qL1 ++ qL2)) → Q tt tL) → (PEqualNP.ReadK.readsAtMost C n [u, w] 2 = PEqualNP.ReadK.readsAtMost C n [w, u] 2) ∧ (PEqualNP.ReadK.readsAtMost C n [u, w] 2 = true → ∃ L : List (ℕ × ℕ), (∃ (j0 : ℕ) (L1 L2 : List (ℕ × ℕ)), j0 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j0).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ R (n + j0) C.output ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j0).inputs.getD 0 0) L1 ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j0).inputs.getD 1 0) L2 ∧ L = L1 ++ L2) ∧ (∀ gv ∈ L, gv.2 = u ∨ gv.2 = w) ∧ (L.filter (fun e1 => decide (e1.2 = u))).length ∈ ({1, 2} : Finset ℕ) ∧ (L.filter (fun e2 => decide (e2.2 = w))).length ∈ ({1, 2} : Finset ℕ)) := by
  intro n C u w hC hu hw huw h1 h2 R hR T hT
  subst hR
  subst hT
  refine ⟨?_, fun hread => ?_⟩
  · rcases hA : readsAtMost C n [u, w] 2 with _ | _
    · rcases hB : readsAtMost C n [w, u] 2 with _ | _
      · rfl
      · have h3 := reads_swap n C w u hC hB
        rw [hA] at h3
        exact absurd h3 Bool.false_ne_true
    · exact (reads_swap n C u w hC hA).symm
  · exact part2 n C u w hC hu hw huw h1 h2 hread

end PEqualNP.Outside.L_meta_2350

theorem PEqualNP.Outside.L_meta_2350 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (u w : ℕ), PEqualNP.TopForm.IsAO2 n C → u < n → w < n → u ≠ w → PEqualNP.MetaComplexity.circuitFun n C (fun k1 : Fin n => decide (k1.val = u)) = false → PEqualNP.MetaComplexity.circuitFun n C (fun k2 : Fin n => decide (k2.val = w)) = false → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → ∀ T : ℕ → List (ℕ × ℕ) → Prop, T = (fun tt tL => ∀ Q : ℕ → List (ℕ × ℕ) → Prop, (∀ (qv qt : ℕ), qv < n → R qv qt → Q qt [(qt, qv)]) → (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C qj).op = PEqualNP.CircuitLowerBounds.GateOp.and → R (n + qj) qt → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 0 0) qL1 → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 1 0) qL2 → Q qt (qL1 ++ qL2)) → Q tt tL) → (PEqualNP.ReadK.readsAtMost C n [u, w] 2 = PEqualNP.ReadK.readsAtMost C n [w, u] 2) ∧ (PEqualNP.ReadK.readsAtMost C n [u, w] 2 = true → ∃ L : List (ℕ × ℕ), (∃ (j0 : ℕ) (L1 L2 : List (ℕ × ℕ)), j0 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j0).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ R (n + j0) C.output ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j0).inputs.getD 0 0) L1 ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j0).inputs.getD 1 0) L2 ∧ L = L1 ++ L2) ∧ (∀ gv ∈ L, gv.2 = u ∨ gv.2 = w) ∧ (L.filter (fun e1 => decide (e1.2 = u))).length ∈ ({1, 2} : Finset ℕ) ∧ (L.filter (fun e2 => decide (e2.2 = w))).length ∈ ({1, 2} : Finset ℕ)) :=
  PEqualNP.Outside.L_meta_2350.main_aux
