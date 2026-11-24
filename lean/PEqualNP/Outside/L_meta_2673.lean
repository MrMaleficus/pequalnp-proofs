import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2673

section


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def a50_stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma a50_wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl a50_stepWire x := rfl

lemma a50_foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl a50_stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [a50_stepWire]
    omega

lemma a50_foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl a50_stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (a50_stepWire w g).length := by simp [a50_stepWire]; omega
    rw [ih (a50_stepWire w g) hlt]
    simp [a50_stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma a50_getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma a50_wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [a50_wires_eq_foldl, a50_foldl_stepWire_length, List.length_ofFn]

lemma a50_split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]


def a50_W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma a50_gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma a50_W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    a50_W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then a50_W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := a50_split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [a50_gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl a50_stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, a50_foldl_stepWire_length, hpre_len]
  have hCj : a50_W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [a50_W]
    rw [a50_wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [a50_foldl_stepWire_getD_lt post (a50_stepWire w0 gj) (n + k) (by simp [a50_stepWire]; omega)]
    simp [a50_stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [a50_W]
    rw [a50_wires_eq_foldl, hgs, List.foldl_append]
    exact (a50_foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact a50_getD_ge_length w0 i (by omega)

lemma a50_W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    a50_W n C x u = x ⟨u, hu⟩ := by
  simp only [a50_W]
  rw [a50_wires_eq_foldl, a50_foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

open PEqualNP.CleanedNonEdge in
lemma a50_orFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

open PEqualNP.CleanedNonEdge in
lemma a50_orStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
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
lemma a50_orStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.CleanedNonEdge in
lemma a50_orFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact a50_orStep_getD_lt n cs g k hk

open PEqualNP.CleanedNonEdge in
lemma a50_orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ x ∈ (orSets n C).getD (w - n) []) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := a50_split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [a50_gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [a50_orFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : (orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k [] := by
    rw [hc, a50_orFold_getD_lt n post _ k (by omega)]
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, a50_orFold_getD_lt n post _ m (by omega)]
    exact a50_orStep_getD_lt n _ gk m (by omega)
  have h3 := a50_orStep_mem_last n (pre.foldl (orStep n) []) gk x
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

lemma a50_orReaches_self (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    OrReaches n C (n + j) j := by
  unfold OrReaches
  refine ⟨Nat.le_add_right n j, ?_⟩
  rw [Nat.add_sub_cancel_left, a50_orSets_mem_iff n C j j hj]
  exact Or.inl rfl

lemma a50_orReaches_step (n : ℕ) (C : Circuit) (j i g : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : OrReaches n C i g) : OrReaches n C (n + j) g := by
  unfold OrReaches at h ⊢
  refine ⟨Nat.le_add_right n j, ?_⟩
  rw [Nat.add_sub_cancel_left, a50_orSets_mem_iff n C j g hj]
  exact Or.inr ⟨hop, i, hi, h.1, hlt, h.2⟩

lemma a50_mem_filter_iff_gen {α : Type} (p : α → Prop) (d : DecidablePred p) (s : Finset α) (a : α) :
    a ∈ @Finset.filter α p d s ↔ a ∈ s ∧ p a :=
  @Finset.mem_filter α p d s a

lemma a50_mem_orIn (n : ℕ) (C : Circuit) (w : ℕ) (i : Fin n) :
    i ∈ orIn n C w ↔ ((i : ℕ) = w ∨ ∃ k < C.gates.length,
      OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧ (i : ℕ) ∈ (gateAt C k).inputs) := by
  unfold orIn
  exact ⟨fun h => ((a50_mem_filter_iff_gen _ _ _ _).1 h).2,
    fun h => (a50_mem_filter_iff_gen _ _ _ _).2 ⟨Finset.mem_univ _, h⟩⟩

lemma a50_orIn_up (n : ℕ) (C : Circuit) (j i : ℕ) (a : Fin n) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : a ∈ orIn n C i) : a ∈ orIn n C (n + j) := by
  rw [a50_mem_orIn] at h ⊢
  right
  rcases h with h | ⟨k, hk, hr, hopk, hin⟩
  · exact ⟨j, hj, a50_orReaches_self n C j hj, hop, by rw [h]; exact hi⟩
  · exact ⟨k, hk, a50_orReaches_step n C j i k hj hop hi hlt hr, hopk, hin⟩

def a50_FR (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) : List (List ℕ) :=
  match g.op with
  | GateOp.or => (g.inputs.map fun i => R.getD i []).foldl (fun acc A => A.foldl insertNew acc) []
  | GateOp.and => (g.inputs.map fun i => R.getD i []).foldl (andStep k) [S.map fun _ => 0]
  | _ => []

def a50_stepR (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) : List (List (List ℕ)) :=
  R ++ [a50_FR S k R g]

lemma a50_readVectors_eq (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) :
    readVectors C n S k = C.gates.foldl (a50_stepR S k) ((List.range n).map (leafVectors S k)) := by
  first
    | rfl
    | (unfold readVectors; congr 1; funext R g; rcases g with ⟨op, ins⟩; cases op <;> rfl)

lemma a50_FR_or (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) (h : g.op = GateOp.or) :
    a50_FR S k R g =
      (g.inputs.map fun i => R.getD i []).foldl (fun acc A => A.foldl insertNew acc) [] := by
  obtain ⟨op, ins⟩ := g
  have h2 : op = GateOp.or := h
  subst h2
  rfl

lemma a50_FR_and (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate)
    (h : g.op = GateOp.and) :
    a50_FR S k R g = (g.inputs.map fun i => R.getD i []).foldl (andStep k) [S.map fun _ => 0] := by
  obtain ⟨op, ins⟩ := g
  have h2 : op = GateOp.and := h
  subst h2
  rfl

lemma a50_foldR_length (S : List ℕ) (k : ℕ) (gs : List Gate) (R : List (List (List ℕ))) :
    (gs.foldl (a50_stepR S k) R).length = R.length + gs.length := by
  induction gs generalizing R with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [a50_stepR]
    omega

lemma a50_foldR_getD_lt (S : List ℕ) (k : ℕ) (gs : List Gate) (R : List (List (List ℕ))) (i : ℕ)
    (hi : i < R.length) : (gs.foldl (a50_stepR S k) R).getD i [] = R.getD i [] := by
  induction gs generalizing R with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (a50_stepR S k R g).length := by simp [a50_stepR]; omega
    rw [ih (a50_stepR S k R g) hlt]
    simp [a50_stepR, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

def a50_RV (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (w : ℕ) : List (List ℕ) :=
  (readVectors C n S k).getD w []

lemma a50_RV_input (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (w : ℕ) (hw : w < n) :
    a50_RV C n S k w = leafVectors S k w := by
  simp only [a50_RV]
  rw [a50_readVectors_eq, a50_foldR_getD_lt S k C.gates ((List.range n).map (leafVectors S k)) w
    (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

lemma a50_RV_gate (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (j : ℕ) (hj : j < C.gates.length) :
    ∃ Rp : List (List (List ℕ)),
      (∀ i, i < n + j → Rp.getD i [] = a50_RV C n S k i) ∧
      a50_RV C n S k (n + j) = a50_FR S k Rp (gateAt C j) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := a50_split_gates C.gates j hj
  have hga : gateAt C j = gj := by rw [a50_gateAt_eq C j hj]; exact hgj
  rw [hga]
  obtain ⟨Rp, hRp⟩ : ∃ Rp, Rp = pre.foldl (a50_stepR S k) ((List.range n).map (leafVectors S k)) :=
    ⟨_, rfl⟩
  have hlen : Rp.length = n + j := by
    rw [hRp, a50_foldR_length]
    simp only [List.length_map, List.length_range, hpre_len]
  have hall : readVectors C n S k = post.foldl (a50_stepR S k) (a50_stepR S k Rp gj) := by
    rw [a50_readVectors_eq, hgs, List.foldl_append, List.foldl_cons, hRp]
  have hlen1 : (a50_stepR S k Rp gj).length = n + j + 1 := by
    simp [a50_stepR, hlen]
  refine ⟨Rp, ?_, ?_⟩
  · intro i hi
    simp only [a50_RV]
    rw [hall, a50_foldR_getD_lt S k post (a50_stepR S k Rp gj) i (by omega)]
    simp [a50_stepR, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (show i < Rp.length by omega)]
  · simp only [a50_RV]
    rw [hall, a50_foldR_getD_lt S k post (a50_stepR S k Rp gj) (n + j) (by omega)]
    simp [a50_stepR, List.getD_eq_getElem?_getD, hlen]

lemma a50_mem_foldl_insertNew (L : List (List ℕ)) (acc : List (List ℕ)) (v : List ℕ)
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

lemma a50_mem_andStep (k : ℕ) (A B : List (List ℕ)) (v : List ℕ) (h : v ∈ andStep k A B) :
    ∃ u ∈ A, ∃ u2 ∈ B, v = capAdd k u u2 := by
  unfold andStep at h
  rcases a50_mem_foldl_insertNew _ _ _ h with h1 | h1
  · simp at h1
  · simp only [List.mem_flatMap, List.mem_map] at h1
    obtain ⟨u, hu, u2, hu2, rfl⟩ := h1
    exact ⟨u, hu, u2, hu2, rfl⟩

lemma a50_capAdd_pair (k x1 y1 x2 y2 : ℕ) :
    capAdd k [x1, y1] [x2, y2] = [min (x1 + x2) (k + 1), min (y1 + y2) (k + 1)] := by
  first
    | rfl
    | simp [capAdd]

lemma a50_leaf_eq2 (a b t : ℕ) :
    leafVectors [a, b] 2 t =
      if t ∈ [a, b] then [[if a = t then 1 else 0, if b = t then 1 else 0]] else [] := by
  first
    | rfl
    | (unfold leafVectors; simp)

lemma a50_mem_foldl_insertNew_of (L : List (List ℕ)) (acc : List (List ℕ)) (v : List ℕ)
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

lemma a50_andStep_mem (k : ℕ) (A B : List (List ℕ)) (u u2 : List ℕ) (hu : u ∈ A) (hu2 : u2 ∈ B) :
    capAdd k u u2 ∈ andStep k A B := by
  unfold andStep
  apply a50_mem_foldl_insertNew_of
  right
  simp only [List.mem_flatMap, List.mem_map]
  exact ⟨u, hu, u2, hu2, rfl⟩

lemma a50_mem_union_fold (Ls : List (List (List ℕ))) (acc : List (List ℕ)) (v : List ℕ)
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
    · exact Or.inl (a50_mem_foldl_insertNew_of _ _ _ (Or.inl h))
    · rcases List.mem_cons.1 hA with h3 | h3
      · exact Or.inl (a50_mem_foldl_insertNew_of _ _ _ (Or.inr (by rw [← h3]; exact hvA)))
      · exact Or.inr ⟨A, h3, hvA⟩

lemma a50_RV_or_mem (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (j i : ℕ) (v : List ℕ)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or)
    (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j) (hv : v ∈ a50_RV C n S k i) :
    v ∈ a50_RV C n S k (n + j) := by
  obtain ⟨Rp, hRp, hRV⟩ := a50_RV_gate C n S k j hj
  rw [hRV, a50_FR_or _ _ _ _ hop]
  apply a50_mem_union_fold
  right
  exact ⟨Rp.getD i [], List.mem_map.2 ⟨i, hi, rfl⟩, by rw [hRp i hlt]; exact hv⟩

lemma a50_RV_and_mem (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (j i1 i2 : ℕ)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (hinp : (gateAt C j).inputs = [i1, i2]) (h1 : i1 < n + j) (h2 : i2 < n + j)
    (u1 u2 : List ℕ) (m1 : u1 ∈ a50_RV C n S k i1) (m2 : u2 ∈ a50_RV C n S k i2) :
    capAdd k (capAdd k (S.map fun _ => 0) u1) u2 ∈ a50_RV C n S k (n + j) := by
  obtain ⟨Rp, hRp, hRV⟩ := a50_RV_gate C n S k j hj
  rw [hRV, a50_FR_and _ _ _ _ hop, hinp]
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
    hRp i1 h1, hRp i2 h2]
  exact a50_andStep_mem k _ _ _ _ (a50_andStep_mem k _ _ _ _ (List.mem_singleton.2 rfl) m1) m2

theorem a50_RV_ind (n : ℕ) (C : Circuit) (S : List ℕ) (k : ℕ) (hC : IsAO2 n C)
    (P : ℕ → List ℕ → Prop)
    (hleaf : ∀ t, t < n → ∀ v ∈ leafVectors S k t, P t v)
    (hor : ∀ j i, j < C.gates.length → (gateAt C j).op = GateOp.or →
      i ∈ (gateAt C j).inputs → i < n + j → ∀ v, P i v → P (n + j) v)
    (hand : ∀ j i1 i2, j < C.gates.length → (gateAt C j).op = GateOp.and →
      (gateAt C j).inputs = [i1, i2] → i1 < n + j → i2 < n + j → ∀ u1 u2, P i1 u1 → P i2 u2 →
      P (n + j) (capAdd k (capAdd k (S.map fun _ => 0) u1) u2)) :
    ∀ t, ∀ v ∈ a50_RV C n S k t, P t v := by
  obtain ⟨hAnd, hBack, hTwo⟩ := hC
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro v hv
    by_cases htn : t < n
    · rw [a50_RV_input C n S k t htn] at hv
      exact hleaf t htn v hv
    · obtain ⟨j, rfl⟩ : ∃ j, t = n + j := ⟨t - n, by omega⟩
      by_cases hj : j < C.gates.length
      · have hmem : gateAt C j ∈ C.gates := by
          rw [a50_gateAt_eq C j hj]
          exact List.getElem_mem hj
        have hlen2 := hTwo _ hmem
        have hback := hBack j hj
        obtain ⟨Rp, hRp, hRV⟩ := a50_RV_gate C n S k j hj
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
          · rw [hRV, a50_FR_and _ _ _ _ hop, hinp] at hv
            simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
              hRp i1 hi1, hRp i2 hi2] at hv
            obtain ⟨t2, ht2, u2, hu2, rfl⟩ := a50_mem_andStep _ _ _ _ hv
            obtain ⟨z, hz, u1, hu1, rfl⟩ := a50_mem_andStep _ _ _ _ ht2
            have hz2 : z = S.map fun _ => 0 := List.mem_singleton.1 hz
            subst hz2
            exact hand j i1 i2 hj hop hinp hi1 hi2 u1 u2 (ih i1 hi1 u1 hu1) (ih i2 hi2 u2 hu2)
          · rw [hRV, a50_FR_or _ _ _ _ hop, hinp] at hv
            simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
              hRp i1 hi1, hRp i2 hi2] at hv
            rcases a50_mem_foldl_insertNew _ _ _ hv with h | h
            · rcases a50_mem_foldl_insertNew _ _ _ h with h3 | h3
              · simp at h3
              · exact hor j i1 hj hop hm1 hi1 v (ih i1 hi1 v h3)
            · exact hor j i2 hj hop hm2 hi2 v (ih i2 hi2 v h)
        · exfalso
          rw [hinp] at hlen2
          simp at hlen2
      · exfalso
        have hnil : a50_RV C n S k (n + j) = [] := by
          simp only [a50_RV]
          rw [a50_readVectors_eq]
          exact List.getD_eq_default _ _ (by
            rw [a50_foldR_length]
            simp only [List.length_map, List.length_range]
            omega)
        rw [hnil] at hv
        simp at hv

def a50_Sw (n : ℕ) (C : Circuit) (u w : ℕ) (t : ℕ) (v : List ℕ) : Prop :=
  ∃ x y, v = [x, y] ∧ [y, x] ∈ a50_RV C n [w, u] 2 t

theorem a50_sw_mem (n : ℕ) (C : Circuit) (u w : ℕ) (hC : IsAO2 n C) :
    ∀ t, ∀ v ∈ a50_RV C n [u, w] 2 t, a50_Sw n C u w t v := by
  apply a50_RV_ind n C [u, w] 2 hC (a50_Sw n C u w)
  · intro t ht v hv
    unfold a50_Sw
    rw [a50_leaf_eq2] at hv
    rw [a50_RV_input C n _ 2 t ht, a50_leaf_eq2]
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
    exact ⟨x, y, hv, a50_RV_or_mem C n _ 2 j i _ hj hop hi hlt hmem⟩
  · intro j i1 i2 hj hop hinp hi1 hi2 u1 u2 h1 h2
    obtain ⟨x1, y1, rfl, m1⟩ := h1
    obtain ⟨x2, y2, rfl, m2⟩ := h2
    refine ⟨min (min (0 + x1) (2 + 1) + x2) (2 + 1),
      min (min (0 + y1) (2 + 1) + y2) (2 + 1), ?_, ?_⟩
    · show capAdd 2 (capAdd 2 [0, 0] [x1, y1]) [x2, y2] = _
      rw [a50_capAdd_pair, a50_capAdd_pair]
    · have h3 := a50_RV_and_mem C n [w, u] 2 j i1 i2 hj hop hinp hi1 hi2 _ _ m1 m2
      have h4 : capAdd 2 (capAdd 2 [0, 0] [y1, x1]) [y2, x2] ∈ a50_RV C n [w, u] 2 (n + j) := h3
      rw [a50_capAdd_pair, a50_capAdd_pair] at h4
      exact h4

lemma a50_reads_swap (n : ℕ) (C : Circuit) (u w : ℕ) (hC : IsAO2 n C)
    (h : readsAtMost C n [u, w] 2 = true) : readsAtMost C n [w, u] 2 = true := by
  unfold readsAtMost at h ⊢
  rw [List.any_eq_true] at h ⊢
  obtain ⟨v, hv, hall⟩ := h
  obtain ⟨x, y, rfl, hm⟩ := a50_sw_mem n C u w hC C.output v hv
  refine ⟨[y, x], hm, ?_⟩
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq] at hall ⊢
  exact ⟨hall.2, hall.1⟩

def a50_Rr (n : ℕ) (C : Circuit) (a b : ℕ) : Prop :=
  Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧
    (gateAt C rj).op = GateOp.or ∧ ra ∈ (gateAt C rj).inputs) a b

def a50_Tr (n : ℕ) (C : Circuit) (tt : ℕ) (tL : List (ℕ × ℕ)) : Prop :=
  ∀ Q : ℕ → List (ℕ × ℕ) → Prop,
    (∀ (qv qt : ℕ), qv < n → a50_Rr n C qv qt → Q qt [(qt, qv)]) →
    (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length →
      (gateAt C qj).op = GateOp.and → a50_Rr n C (n + qj) qt →
      Q ((gateAt C qj).inputs.getD 0 0) qL1 → Q ((gateAt C qj).inputs.getD 1 0) qL2 →
      Q qt (qL1 ++ qL2)) → Q tt tL

lemma a50_Rr_refl (n : ℕ) (C : Circuit) (t : ℕ) : a50_Rr n C t t := by
  unfold a50_Rr
  exact Relation.ReflTransGen.refl

lemma a50_Rr_step (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j) :
    a50_Rr n C i (n + j) := by
  unfold a50_Rr
  exact Relation.ReflTransGen.single ⟨hlt, j, rfl, hj, hop, hi⟩

lemma a50_Rr_trans (n : ℕ) (C : Circuit) (a b c : ℕ) (h1 : a50_Rr n C a b) (h2 : a50_Rr n C b c) :
    a50_Rr n C a c := by
  unfold a50_Rr at h1 h2 ⊢
  exact Relation.ReflTransGen.trans h1 h2

lemma a50_W_or_up (n : ℕ) (C : Circuit) (z : Fin n → Bool) (j i : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (hz : a50_W n C z i = true) : a50_W n C z (n + j) = true := by
  rw [a50_W_gate n C z j hj, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
  exact ⟨i, hi, by simp only [hlt, ite_true]; exact hz⟩

lemma a50_W_and_up (n : ℕ) (C : Circuit) (z : Fin n → Bool) (j i1 i2 : ℕ)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (hinp : (gateAt C j).inputs = [i1, i2]) (h1 : i1 < n + j) (h2 : i2 < n + j)
    (hz1 : a50_W n C z i1 = true) (hz2 : a50_W n C z i2 = true) : a50_W n C z (n + j) = true := by
  rw [a50_W_gate n C z j hj, hop, hinp]
  simp [GateOp.eval, h1, h2, hz1, hz2]

lemma a50_Rr_W (n : ℕ) (C : Circuit) (z : Fin n → Bool) (a t : ℕ) (h : a50_Rr n C a t)
    (ha : a50_W n C z a = true) : a50_W n C z t = true := by
  unfold a50_Rr at h
  induction h with
  | refl => exact ha
  | tail _ hstep ih =>
    obtain ⟨hlt, rj, rfl, hrj, hop, hin⟩ := hstep
    exact a50_W_or_up n C z rj _ hrj hop hin hlt ih

lemma a50_Tr_leaf (n : ℕ) (C : Circuit) (qv qt : ℕ) (h : qv < n) (hr : a50_Rr n C qv qt) :
    a50_Tr n C qt [(qt, qv)] := by
  intro Q hl ha
  exact hl qv qt h hr

lemma a50_Tr_and (n : ℕ) (C : Circuit) (qj qt : ℕ) (L1 L2 : List (ℕ × ℕ))
    (hj : qj < C.gates.length) (hop : (gateAt C qj).op = GateOp.and)
    (hr : a50_Rr n C (n + qj) qt) (t1 : a50_Tr n C ((gateAt C qj).inputs.getD 0 0) L1)
    (t2 : a50_Tr n C ((gateAt C qj).inputs.getD 1 0) L2) : a50_Tr n C qt (L1 ++ L2) := by
  intro Q hl ha
  exact ha qj qt L1 L2 hj hop hr (t1 Q hl ha) (t2 Q hl ha)

lemma a50_Tr_W (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (q : ℕ) (hq : q < n) (t : ℕ)
    (L : List (ℕ × ℕ)) (hT : a50_Tr n C t L) (hall : ∀ e ∈ L, e.2 = q) :
    a50_W n C (fun k : Fin n => decide (k.val = q)) t = true := by
  obtain ⟨hAnd, hBack, hTwo⟩ := hC
  revert hall
  refine hT (fun t L => (∀ e ∈ L, e.2 = q) →
    a50_W n C (fun k : Fin n => decide (k.val = q)) t = true) ?_ ?_
  · intro qv qt hqv hr hall
    have hqq : qv = q := hall (qt, qv) (List.mem_singleton.2 rfl)
    rw [hqq] at hr
    exact a50_Rr_W n C _ q qt hr (by rw [a50_W_input n C _ q hq]; exact decide_eq_true rfl)
  · intro qj qt L1 L2 hj hop hr h1 h2 hall
    have hmem : gateAt C qj ∈ C.gates := by
      rw [a50_gateAt_eq C qj hj]
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
      have h1b : a50_W n C (fun k : Fin n => decide (k.val = q)) i1 = true :=
        h1 (fun e he => hall e (List.mem_append_left _ he))
      have h2b : a50_W n C (fun k : Fin n => decide (k.val = q)) i2 = true :=
        h2 (fun e he => hall e (List.mem_append_right _ he))
      exact a50_Rr_W n C _ _ qt hr (a50_W_and_up n C _ qj i1 i2 hj hop hinp
        (hback i1 (by rw [hinp]; simp)) (hback i2 (by rw [hinp]; simp)) h1b h2b)
    · exfalso
      rw [hinp] at hlen2
      simp at hlen2

def a50_cnt (q : ℕ) (L : List (ℕ × ℕ)) : ℕ := (L.filter (fun e => decide (e.2 = q))).length

lemma a50_cnt_append (q : ℕ) (L1 L2 : List (ℕ × ℕ)) :
    a50_cnt q (L1 ++ L2) = a50_cnt q L1 + a50_cnt q L2 := by
  simp [a50_cnt]

lemma a50_cnt_single_eq (q s : ℕ) : a50_cnt q [(s, q)] = 1 := by
  simp [a50_cnt]

lemma a50_cnt_single_ne (q s p : ℕ) (h : p ≠ q) : a50_cnt q [(s, p)] = 0 := by
  simp [a50_cnt, h]

lemma a50_cnt_zero (q : ℕ) (L : List (ℕ × ℕ)) (h : a50_cnt q L = 0) (e : ℕ × ℕ) (he : e ∈ L) :
    e.2 ≠ q := by
  intro heq
  have h3 : e ∈ L.filter (fun e => decide (e.2 = q)) :=
    List.mem_filter.2 ⟨he, decide_eq_true heq⟩
  unfold a50_cnt at h
  rw [List.eq_nil_of_length_eq_zero h] at h3
  simp at h3

def a50_Good (n : ℕ) (C : Circuit) (u w : ℕ) (s : ℕ) (v : List ℕ) : Prop :=
  ∃ x y, v = [x, y] ∧
    ((∃ qv, qv < n ∧ a50_Rr n C qv s ∧ ((qv = u ∧ x = 1 ∧ y = 0) ∨ (qv = w ∧ x = 0 ∧ y = 1))) ∨
      (∃ j0 L1 L2, j0 < C.gates.length ∧ (gateAt C j0).op = GateOp.and ∧ a50_Rr n C (n + j0) s ∧
        a50_Tr n C ((gateAt C j0).inputs.getD 0 0) L1 ∧ a50_Tr n C ((gateAt C j0).inputs.getD 1 0) L2 ∧
        (∀ e ∈ L1 ++ L2, e.2 = u ∨ e.2 = w) ∧ x = min (a50_cnt u (L1 ++ L2)) 3 ∧
        y = min (a50_cnt w (L1 ++ L2)) 3))

lemma a50_Good_T (n : ℕ) (C : Circuit) (u w : ℕ) (huw : u ≠ w) (s : ℕ) (v : List ℕ)
    (h : a50_Good n C u w s v) :
    ∃ x y L, v = [x, y] ∧ a50_Tr n C s L ∧ (∀ e ∈ L, e.2 = u ∨ e.2 = w) ∧
      x = min (a50_cnt u L) 3 ∧ y = min (a50_cnt w L) 3 := by
  obtain ⟨x, y, hv, h | h⟩ := h
  · obtain ⟨qv, hqv, hr, h | h⟩ := h
    · obtain ⟨hq, hx, hy⟩ := h
      refine ⟨x, y, [(s, qv)], hv, a50_Tr_leaf n C qv s hqv hr, ?_, ?_, ?_⟩
      · intro e he
        rw [List.mem_singleton.1 he]
        exact Or.inl hq
      · rw [hq, a50_cnt_single_eq]
        omega
      · rw [hq, a50_cnt_single_ne w s u huw]
        omega
    · obtain ⟨hq, hx, hy⟩ := h
      refine ⟨x, y, [(s, qv)], hv, a50_Tr_leaf n C qv s hqv hr, ?_, ?_, ?_⟩
      · intro e he
        rw [List.mem_singleton.1 he]
        exact Or.inr hq
      · rw [hq, a50_cnt_single_ne u s w (Ne.symm huw)]
        omega
      · rw [hq, a50_cnt_single_eq]
        omega
  · obtain ⟨j0, L1, L2, hj0, hop, hr, t1, t2, hall, hx, hy⟩ := h
    exact ⟨x, y, L1 ++ L2, hv, a50_Tr_and n C j0 s L1 L2 hj0 hop hr t1 t2, hall, hx, hy⟩

theorem a50_good_all (n : ℕ) (C : Circuit) (u w : ℕ) (hC : IsAO2 n C) (huw : u ≠ w) :
    ∀ t, ∀ v ∈ a50_RV C n [u, w] 2 t, a50_Good n C u w t v := by
  apply a50_RV_ind n C [u, w] 2 hC (a50_Good n C u w)
  · intro t ht v hv
    rw [a50_leaf_eq2] at hv
    by_cases htu : u = t
    · have htw : ¬ w = t := by omega
      rw [if_pos (List.mem_cons.2 (Or.inl htu.symm)), if_pos htu, if_neg htw] at hv
      have hv2 : v = [1, 0] := List.mem_singleton.1 hv
      exact ⟨1, 0, hv2, Or.inl ⟨t, ht, a50_Rr_refl n C t, Or.inl ⟨htu.symm, rfl, rfl⟩⟩⟩
    · by_cases htw : w = t
      · rw [if_pos (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl htw.symm)))),
          if_neg htu, if_pos htw] at hv
        have hv2 : v = [0, 1] := List.mem_singleton.1 hv
        exact ⟨0, 1, hv2, Or.inl ⟨t, ht, a50_Rr_refl n C t, Or.inr ⟨htw.symm, rfl, rfl⟩⟩⟩
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
        a50_Rr_trans n C _ _ _ hr (a50_Rr_step n C j i hj hop hi hlt), hc⟩⟩
    · obtain ⟨j0, L1, L2, hj0, hop0, hr, t1, t2, hall, hx, hy⟩ := h
      exact ⟨x, y, hv, Or.inr ⟨j0, L1, L2, hj0, hop0,
        a50_Rr_trans n C _ _ _ hr (a50_Rr_step n C j i hj hop hi hlt), t1, t2, hall, hx, hy⟩⟩
  · intro j i1 i2 hj hop hinp hi1 hi2 u1 u2 hG1 hG2
    obtain ⟨x1, y1, L1, rfl, t1, hall1, hx1, hy1⟩ := a50_Good_T n C u w huw i1 u1 hG1
    obtain ⟨x2, y2, L2, rfl, t2, hall2, hx2, hy2⟩ := a50_Good_T n C u w huw i2 u2 hG2
    refine ⟨min (min (0 + x1) (2 + 1) + x2) (2 + 1),
      min (min (0 + y1) (2 + 1) + y2) (2 + 1), ?_,
      Or.inr ⟨j, L1, L2, hj, hop, a50_Rr_refl n C (n + j), ?_, ?_, ?_, ?_, ?_⟩⟩
    · show capAdd 2 (capAdd 2 [0, 0] [x1, y1]) [x2, y2] = _
      rw [a50_capAdd_pair, a50_capAdd_pair]
    · rw [hinp]
      exact t1
    · rw [hinp]
      exact t2
    · intro e he
      rcases List.mem_append.1 he with h | h
      · exact hall1 e h
      · exact hall2 e h
    · rw [a50_cnt_append]
      omega
    · rw [a50_cnt_append]
      omega

theorem a50_part2 (n : ℕ) (C : Circuit) (u w : ℕ) (hC : IsAO2 n C) (hu : u < n) (hw : w < n)
    (huw : u ≠ w)
    (h1 : circuitFun n C (fun k1 : Fin n => decide (k1.val = u)) = false)
    (h2 : circuitFun n C (fun k2 : Fin n => decide (k2.val = w)) = false)
    (hread : readsAtMost C n [u, w] 2 = true) :
    ∃ L : List (ℕ × ℕ), (∃ (j0 : ℕ) (L1 L2 : List (ℕ × ℕ)), j0 < C.gates.length ∧
      (gateAt C j0).op = GateOp.and ∧ a50_Rr n C (n + j0) C.output ∧
      a50_Tr n C ((gateAt C j0).inputs.getD 0 0) L1 ∧ a50_Tr n C ((gateAt C j0).inputs.getD 1 0) L2 ∧
      L = L1 ++ L2) ∧ (∀ gv ∈ L, gv.2 = u ∨ gv.2 = w) ∧
      a50_cnt u L ∈ ({1, 2} : Finset ℕ) ∧ a50_cnt w L ∈ ({1, 2} : Finset ℕ) := by
  unfold readsAtMost at hread
  rw [List.any_eq_true] at hread
  obtain ⟨v, hv, hall⟩ := hread
  obtain ⟨x, y, hveq, h | h⟩ := a50_good_all n C u w hC huw C.output v hv
  · exfalso
    obtain ⟨qv, hqv, hr, hc | hc⟩ := h
    · have h3 : circuitFun n C (fun k1 : Fin n => decide (k1.val = u)) = true :=
        a50_Rr_W n C (fun k1 : Fin n => decide (k1.val = u)) qv C.output hr
          (by rw [a50_W_input n C _ qv hqv]; exact decide_eq_true hc.1)
      rw [h1] at h3
      exact Bool.false_ne_true h3
    · have h3 : circuitFun n C (fun k2 : Fin n => decide (k2.val = w)) = true :=
        a50_Rr_W n C (fun k2 : Fin n => decide (k2.val = w)) qv C.output hr
          (by rw [a50_W_input n C _ qv hqv]; exact decide_eq_true hc.1)
      rw [h2] at h3
      exact Bool.false_ne_true h3
  · obtain ⟨j0, L1, L2, hj0, hop, hr, t1, t2, hLall, hx, hy⟩ := h
    subst hveq
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
      decide_eq_true_eq] at hall
    obtain ⟨hx2, hy2⟩ := hall
    have hT : a50_Tr n C C.output (L1 ++ L2) := a50_Tr_and n C j0 C.output L1 L2 hj0 hop hr t1 t2
    have hcu : a50_cnt u (L1 ++ L2) ≠ 0 := by
      intro h0
      have hallw : ∀ e ∈ L1 ++ L2, e.2 = w := by
        intro e he
        rcases hLall e he with h | h
        · exact absurd h (a50_cnt_zero u _ h0 e he)
        · exact h
      have h3 : circuitFun n C (fun k2 : Fin n => decide (k2.val = w)) = true :=
        a50_Tr_W n C hC w hw C.output _ hT hallw
      rw [h2] at h3
      exact Bool.false_ne_true h3
    have hcw : a50_cnt w (L1 ++ L2) ≠ 0 := by
      intro h0
      have hallu : ∀ e ∈ L1 ++ L2, e.2 = u := by
        intro e he
        rcases hLall e he with h | h
        · exact h
        · exact absurd h (a50_cnt_zero w _ h0 e he)
      have h3 : circuitFun n C (fun k1 : Fin n => decide (k1.val = u)) = true :=
        a50_Tr_W n C hC u hu C.output _ hT hallu
      rw [h1] at h3
      exact Bool.false_ne_true h3
    refine ⟨L1 ++ L2, ⟨j0, L1, L2, hj0, hop, hr, t1, t2, rfl⟩, hLall, ?_, ?_⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      omega

theorem l2350 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (u w : ℕ), PEqualNP.TopForm.IsAO2 n C → u < n → w < n → u ≠ w → PEqualNP.MetaComplexity.circuitFun n C (fun k1 : Fin n => decide (k1.val = u)) = false → PEqualNP.MetaComplexity.circuitFun n C (fun k2 : Fin n => decide (k2.val = w)) = false → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → ∀ T : ℕ → List (ℕ × ℕ) → Prop, T = (fun tt tL => ∀ Q : ℕ → List (ℕ × ℕ) → Prop, (∀ (qv qt : ℕ), qv < n → R qv qt → Q qt [(qt, qv)]) → (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C qj).op = PEqualNP.CircuitLowerBounds.GateOp.and → R (n + qj) qt → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 0 0) qL1 → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 1 0) qL2 → Q qt (qL1 ++ qL2)) → Q tt tL) → (PEqualNP.ReadK.readsAtMost C n [u, w] 2 = PEqualNP.ReadK.readsAtMost C n [w, u] 2) ∧ (PEqualNP.ReadK.readsAtMost C n [u, w] 2 = true → ∃ L : List (ℕ × ℕ), (∃ (j0 : ℕ) (L1 L2 : List (ℕ × ℕ)), j0 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j0).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ R (n + j0) C.output ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j0).inputs.getD 0 0) L1 ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j0).inputs.getD 1 0) L2 ∧ L = L1 ++ L2) ∧ (∀ gv ∈ L, gv.2 = u ∨ gv.2 = w) ∧ (L.filter (fun e1 => decide (e1.2 = u))).length ∈ ({1, 2} : Finset ℕ) ∧ (L.filter (fun e2 => decide (e2.2 = w))).length ∈ ({1, 2} : Finset ℕ)) := by
  intro n C u w hC hu hw huw h1 h2 R hR T hT
  subst hR
  subst hT
  refine ⟨?_, fun hread => ?_⟩
  · rcases hA : readsAtMost C n [u, w] 2 with _ | _
    · rcases hB : readsAtMost C n [w, u] 2 with _ | _
      · rfl
      · have h3 := a50_reads_swap n C w u hC hB
        rw [hA] at h3
        exact absurd h3 Bool.false_ne_true
    · exact (a50_reads_swap n C u w hC hA).symm
  · exact a50_part2 n C u w hC hu hw huw h1 h2 hread


end


section


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- fragment f00_basic
def a24_stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma a24_wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl a24_stepWire x := rfl

lemma a24_foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl a24_stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [a24_stepWire]
    omega

lemma a24_foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl a24_stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (a24_stepWire w g).length := by simp [a24_stepWire]; omega
    rw [ih (a24_stepWire w g) hlt]
    simp [a24_stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma a24_getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma a24_wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [a24_wires_eq_foldl, a24_foldl_stepWire_length, List.length_ofFn]

lemma a24_split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]


def a24_W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma a24_gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma a24_W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    a24_W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then a24_W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := a24_split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [a24_gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl a24_stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, a24_foldl_stepWire_length, hpre_len]
  have hCj : a24_W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [a24_W]
    rw [a24_wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [a24_foldl_stepWire_getD_lt post (a24_stepWire w0 gj) (n + k) (by simp [a24_stepWire]; omega)]
    simp [a24_stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [a24_W]
    rw [a24_wires_eq_foldl, hgs, List.foldl_append]
    exact (a24_foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact a24_getD_ge_length w0 i (by omega)

lemma a24_W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    a24_W n C x u = x ⟨u, hu⟩ := by
  simp only [a24_W]
  rw [a24_wires_eq_foldl, a24_foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

lemma a24_gateAt_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [a24_gateAt_eq C j hj]; exact List.getElem_mem hj

lemma a24_or_up (n : ℕ) (C : Circuit) (z : Fin n → Bool) (a b : ℕ)
    (h : a < b ∧ ∃ rj, b = n + rj ∧ rj < C.gates.length ∧
      (gateAt C rj).op = GateOp.or ∧ a ∈ (gateAt C rj).inputs)
    (ha : a24_W n C z a = true) : a24_W n C z b = true := by
  obtain ⟨hlt, rj, rfl, hj, hop, hin⟩ := h
  rw [a24_W_gate n C z rj hj, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
  exact ⟨a, hin, by simp only [hlt, ite_true]; exact ha⟩

lemma a24_path_up (n : ℕ) (C : Circuit) (z : Fin n → Bool) (a b : ℕ)
    (h : Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧
      (gateAt C rj).op = GateOp.or ∧ ra ∈ (gateAt C rj).inputs) a b)
    (ha : a24_W n C z a = true) : a24_W n C z b = true := by
  induction h with
  | refl => exact ha
  | tail _ hstep ih => exact a24_or_up n C z _ _ hstep ih

lemma a24_and_up (n : ℕ) (C : Circuit) (z : Fin n → Bool) (hC : PEqualNP.TopForm.IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (h0 : a24_W n C z ((gateAt C j).inputs.getD 0 0) = true)
    (h1 : a24_W n C z ((gateAt C j).inputs.getD 1 0) = true) : a24_W n C z (n + j) = true := by
  obtain ⟨_, hRB, h2⟩ := hC
  have hlen : (gateAt C j).inputs.length = 2 := h2 _ (a24_gateAt_mem C j hj)
  have hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j := hRB j hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  rw [a24_W_gate n C z j hj, hop]
  rw [hab] at h0 h1 hrb ⊢
  have ha : a < n + j := hrb a (by simp)
  have hb : b < n + j := hrb b (by simp)
  have h0' : a24_W n C z a = true := by simpa using h0
  have h1' : a24_W n C z b = true := by simpa using h1
  simp [GateOp.eval, ha, hb, h0', h1']

-- fragment f01_tools
def a24_stp (n : ℕ) (C : Circuit) : ℕ → ℕ → Prop :=
  fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧
    (gateAt C rj).op = GateOp.or ∧ ra ∈ (gateAt C rj).inputs

def a24_Rr (n : ℕ) (C : Circuit) : ℕ → ℕ → Prop := Relation.ReflTransGen (a24_stp n C)

def a24_inp (C : Circuit) (j : ℕ) (b : Bool) : ℕ := (gateAt C j).inputs.getD (if b then 1 else 0) 0

def a24_AndG (C : Circuit) (j : ℕ) : Prop := j < C.gates.length ∧ (gateAt C j).op = GateOp.and

def a24_OrG (C : Circuit) (j : ℕ) : Prop := j < C.gates.length ∧ (gateAt C j).op = GateOp.or

theorem a24_inp_false (C : Circuit) (j : ℕ) : a24_inp C j false = (gateAt C j).inputs.getD 0 0 := by
  simp [a24_inp]

theorem a24_inp_true (C : Circuit) (j : ℕ) : a24_inp C j true = (gateAt C j).inputs.getD 1 0 := by
  simp [a24_inp]

theorem a24_Rr_refl (n : ℕ) (C : Circuit) (a : ℕ) : a24_Rr n C a a := Relation.ReflTransGen.refl

theorem a24_Rr_trans {n : ℕ} {C : Circuit} {a b c : ℕ} (h1 : a24_Rr n C a b) (h2 : a24_Rr n C b c) : a24_Rr n C a c :=
  Relation.ReflTransGen.trans h1 h2

theorem a24_inp_cases {n : ℕ} {C : Circuit} (hC : PEqualNP.TopForm.IsAO2 n C) (j : ℕ)
    (hj : j < C.gates.length) (u : ℕ) (hu : u ∈ (gateAt C j).inputs) : ∃ b, u = a24_inp C j b := by
  have hlen : (gateAt C j).inputs.length = 2 := hC.2.2 _ (a24_gateAt_mem C j hj)
  obtain ⟨x, y, hxy⟩ := List.length_eq_two.mp hlen
  rw [hxy] at hu
  rcases List.mem_pair.mp hu with h | h
  · exact ⟨false, by rw [a24_inp_false, hxy, h]; rfl⟩
  · exact ⟨true, by rw [a24_inp_true, hxy, h]; rfl⟩

theorem a24_inp_mem {n : ℕ} {C : Circuit} (hC : PEqualNP.TopForm.IsAO2 n C) (j : ℕ)
    (hj : j < C.gates.length) (b : Bool) :
    a24_inp C j b ∈ (gateAt C j).inputs ∧ a24_inp C j b < n + j := by
  have hlen : (gateAt C j).inputs.length = 2 := hC.2.2 _ (a24_gateAt_mem C j hj)
  obtain ⟨x, y, hxy⟩ := List.length_eq_two.mp hlen
  have hm : a24_inp C j b ∈ (gateAt C j).inputs := by
    cases b
    · rw [a24_inp_false, hxy]; simp
    · rw [a24_inp_true, hxy]; simp
  exact ⟨hm, hC.2.1 j hj _ hm⟩

theorem a24_Rr_inp {n : ℕ} {C : Circuit} (hC : PEqualNP.TopForm.IsAO2 n C) (j : ℕ) (hj : a24_OrG C j)
    (b : Bool) : a24_Rr n C (a24_inp C j b) (n + j) := by
  obtain ⟨hm, hlt⟩ := a24_inp_mem hC j hj.1 b
  exact Relation.ReflTransGen.single ⟨hlt, j, rfl, hj.1, hj.2, hm⟩

theorem a24_Rr_tail {n : ℕ} {C : Circuit} (hC : PEqualNP.TopForm.IsAO2 n C) (x w : ℕ)
    (h : a24_Rr n C x w) : x = w ∨ ∃ j b, a24_OrG C j ∧ w = n + j ∧ a24_Rr n C x (a24_inp C j b) := by
  rcases Relation.ReflTransGen.cases_tail h with h1 | ⟨u, hu, _, rj, hw, hrj, hop, hmem⟩
  · exact Or.inl h1.symm
  · obtain ⟨b, hb⟩ := a24_inp_cases hC rj hrj u hmem
    exact Or.inr ⟨rj, b, ⟨hrj, hop⟩, hw, by rw [← hb]; exact hu⟩

theorem a24_Rr_and {n : ℕ} {C : Circuit} (hC : PEqualNP.TopForm.IsAO2 n C) (j : ℕ) (hj : a24_AndG C j)
    (x : ℕ) (h : a24_Rr n C x (n + j)) : x = n + j := by
  rcases a24_Rr_tail hC x (n + j) h with h1 | ⟨j', b, hj', hw, _⟩
  · exact h1
  · exfalso
    have e : j = j' := by omega
    subst e
    have h2 := hj'.2
    rw [hj.2] at h2
    exact GateOp.noConfusion h2

theorem a24_Rr_input {n : ℕ} {C : Circuit} (hC : PEqualNP.TopForm.IsAO2 n C) (w : ℕ) (hw : w < n)
    (x : ℕ) (h : a24_Rr n C x w) : x = w := by
  rcases a24_Rr_tail hC x w h with h1 | ⟨j', b, _, hw', _⟩
  · exact h1
  · omega

theorem a24_FMG {n : ℕ} {C : Circuit} (hC : PEqualNP.TopForm.IsAO2 n C) (Good : ℕ → Prop)
    (w0 w : ℕ) (h : a24_Rr n C w0 w) (h0 : Good w0) (h1 : ¬ Good w) :
    ∃ jo b, a24_OrG C jo ∧ a24_Rr n C (n + jo) w ∧ a24_Rr n C w0 (a24_inp C jo b) ∧ Good (a24_inp C jo b) ∧
      ¬ Good (n + jo) := by
  unfold a24_Rr at h
  revert h1
  induction h with
  | refl => intro h1; exact absurd h0 h1
  | @tail b c hab hbc ih =>
    intro h1
    by_cases hb : Good b
    · obtain ⟨_, rj, hc, hrj, hop, hmem⟩ := hbc
      subst hc
      obtain ⟨bb, hbb⟩ := a24_inp_cases hC rj hrj b hmem
      refine ⟨rj, bb, ⟨hrj, hop⟩, a24_Rr_refl n C _, ?_, ?_, h1⟩
      · rw [← hbb]; exact hab
      · rw [← hbb]; exact hb
    · obtain ⟨jo, bo, h2, h3, h4, h5, h6⟩ := ih hb
      exact ⟨jo, bo, h2, Relation.ReflTransGen.tail h3 hbc, h4, h5, h6⟩

def a24_Bd {X : Type} (P : X → Prop) (k : ℕ) : Prop :=
  ∀ S : Finset X, (∀ e ∈ S, P e) → S.card ≤ k

theorem a24_Bd_mono {X : Type} {P Q : X → Prop} {k : ℕ} (h : ∀ e, P e → Q e) (hQ : a24_Bd Q k) :
    a24_Bd P k :=
  fun S hS => hQ S (fun e he => h e (hS e he))

theorem a24_Bd_le {X : Type} {P : X → Prop} {k k' : ℕ} (h : k ≤ k') (hP : a24_Bd P k) : a24_Bd P k' :=
  fun S hS => (hP S hS).trans h

theorem a24_Bd_or {X : Type} {P Q : X → Prop} {b c : ℕ} (hP : a24_Bd P b) (hQ : a24_Bd Q c) :
    a24_Bd (fun e => P e ∨ Q e) (b + c) := by
  classical
  intro S hS
  have h1 := hP (S.filter (fun e => P e)) (fun e he => (Finset.mem_filter.mp he).2)
  have h2 := hQ (S.filter (fun e => ¬ P e)) (fun e he => by
    have h := Finset.mem_filter.mp he
    rcases hS e h.1 with h' | h'
    · exact absurd h' h.2
    · exact h')
  have h3 := Finset.card_filter_add_card_filter_not (s := S) (fun e => P e)
  omega

theorem a24_Bd_charge {X κ : Type} (K : Finset κ) (Ch : κ → X → Prop) (k : ℕ)
    (hf : ∀ key ∈ K, a24_Bd (Ch key) k) : a24_Bd (fun e => ∃ key ∈ K, Ch key e) (k * K.card) := by
  classical
  intro S hS
  have hsub : S ⊆ K.biUnion (fun key => S.filter (fun e => Ch key e)) := by
    intro e he
    obtain ⟨key, hk, hc⟩ := hS e he
    exact Finset.mem_biUnion.mpr ⟨key, hk, Finset.mem_filter.mpr ⟨he, hc⟩⟩
  calc S.card ≤ (K.biUnion (fun key => S.filter (fun e => Ch key e))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ key ∈ K, (S.filter (fun e => Ch key e)).card := Finset.card_biUnion_le
    _ ≤ ∑ _key ∈ K, k := Finset.sum_le_sum (fun key hk =>
        hf key hk _ (fun e he => (Finset.mem_filter.mp he).2))
    _ = k * K.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

def a24_ChU {α β : Type} (PA : α → Prop) (PB : β → Prop) (a : α) (b : β) : Prop :=
  PA a ∧ (∀ a', PA a' → a' = a) ∧ PB b ∧ (∀ b', PB b' → b' = b)

theorem a24_Bd_U {α β : Type} (PA : α → Prop) (PB : β → Prop) :
    a24_Bd (fun e : α × β => a24_ChU PA PB e.1 e.2) 1 := by
  intro S hS
  refine Finset.card_le_one.mpr ?_
  intro e he e' he'
  obtain ⟨h1, _, h3, _⟩ := hS e he
  obtain ⟨_, h2', _, h4'⟩ := hS e' he'
  exact Prod.ext (h2' _ h1) (h4' _ h3)

def a24_ChM {α β : Type} (Cmp : α → β → Prop) (L0 L1 : β → Prop) (a : α) (b : β) : Prop :=
  L0 b ∧ (∀ y, L0 y → y = b) ∧ L1 b ∧ (∃ y, L1 y ∧ y ≠ b) ∧ ∀ y, L1 y → Cmp a y

def a24_No4 {α β : Type} (Cmp : α → β → Prop) : Prop :=
  ∀ a a' b b', a ≠ a' → b ≠ b' → ¬ (Cmp a b ∧ Cmp a' b ∧ Cmp a b' ∧ Cmp a' b')

theorem a24_No4_swap {α β : Type} {Cmp : α → β → Prop} (h : a24_No4 Cmp) : a24_No4 (fun b a => Cmp a b) := by
  intro b b' a a' hb ha hh
  exact h a a' b b' ha hb ⟨hh.1, hh.2.2.1, hh.2.1, hh.2.2.2⟩

theorem a24_Bd_M {X α β : Type} (fa : X → α) (fb : X → β)
    (hinj : ∀ e e' : X, fa e = fa e' → fb e = fb e' → e = e') (Cmp : α → β → Prop)
    (h4 : a24_No4 Cmp) (L0 L1 : β → Prop) :
    a24_Bd (fun e : X => a24_ChM Cmp L0 L1 (fa e) (fb e)) 1 := by
  intro S hS
  refine Finset.card_le_one.mpr ?_
  intro e he e' he'
  obtain ⟨h1, _, h3, ⟨y, hy, hne⟩, h5⟩ := hS e he
  obtain ⟨_, h2', h3', _, h5'⟩ := hS e' he'
  have hb : fb e = fb e' := h2' _ h1
  refine hinj e e' ?_ hb
  by_contra hne2
  refine h4 (fa e) (fa e') (fb e) y hne2 (Ne.symm hne) ⟨h5 _ h3, ?_, h5 _ hy, h5' _ hy⟩
  rw [hb]
  exact h5' _ h3'

theorem a24_card_le_of_maps {X Y : Type} (S : Finset X) (f : X → Y)
    (hinj : ∀ e ∈ S, ∀ e' ∈ S, f e = f e' → e = e') (T : Set Y) (hfin : T.Finite) (k : ℕ)
    (hT : T.ncard ≤ k) (hmem : ∀ e ∈ S, f e ∈ T) : S.card ≤ k := by
  classical
  have h1 : (S.image f).card = S.card :=
    Finset.card_image_of_injOn (fun e he e' he' h => hinj e he e' he' h)
  have h2 : ((S.image f : Finset Y) : Set Y) ⊆ T := by
    intro y hy
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
    exact hmem e he
  have h3 := Set.ncard_le_ncard h2 hfin
  rw [Set.ncard_coe_finset] at h3
  omega

theorem a24_card_le_two_of_bool {X : Type} (S : Finset X) (f : X → Bool)
    (hinj : ∀ e ∈ S, ∀ e' ∈ S, f e = f e' → e = e') : S.card ≤ 2 := by
  classical
  have h1 : (S.image f).card = S.card :=
    Finset.card_image_of_injOn (fun e he e' he' h => hinj e he e' he' h)
  have h2 : (S.image f).card ≤ (Finset.univ : Finset Bool).card :=
    Finset.card_le_card (Finset.subset_univ _)
  have h3 : (Finset.univ : Finset Bool).card = 2 := by simp
  omega

theorem a24_card_le_prod {X Y : Type} (S : Finset X) (f : X → Y) (a b : ℕ)
    (himg : ∀ T : Finset Y, (∀ y ∈ T, ∃ e ∈ S, f e = y) → T.card ≤ a)
    (hfib : ∀ y, ∀ T : Finset X, (∀ e ∈ T, e ∈ S ∧ f e = y) → T.card ≤ b) : S.card ≤ b * a := by
  classical
  have h1 : (S.image f).card ≤ a := himg _ (fun y hy => by
    obtain ⟨e, he, h⟩ := Finset.mem_image.mp hy
    exact ⟨e, he, h⟩)
  have h2 := Finset.card_le_mul_card_image (f := f) S b (fun y _ =>
    hfib y _ (fun e he => by
      have h := Finset.mem_filter.mp he
      exact ⟨h.1, h.2⟩))
  calc S.card ≤ b * (S.image f).card := h2
    _ ≤ b * a := Nat.mul_le_mul_left b h1

def a24_Lb (n : ℕ) (C : Circuit) {β : Type} (φ : ℕ → β → Prop) (w : ℕ) (y : β) : Prop :=
  ∃ j, a24_Rr n C (n + j) w ∧ φ j y

theorem a24_Lb_mono {n : ℕ} {C : Circuit} {β : Type} {φ : ℕ → β → Prop} {a b : ℕ} {y : β}
    (h : a24_Rr n C a b) (hl : a24_Lb n C φ a y) : a24_Lb n C φ b y := by
  obtain ⟨j, hj, hp⟩ := hl
  exact ⟨j, a24_Rr_trans hj h, hp⟩

theorem a24_Lb_self {n : ℕ} {C : Circuit} {β : Type} {φ : ℕ → β → Prop} {j : ℕ} {y : β}
    (h : φ j y) : a24_Lb n C φ (n + j) y :=
  ⟨j, a24_Rr_refl n C _, h⟩

theorem a24_Lb_and {n : ℕ} {C : Circuit} (hC : PEqualNP.TopForm.IsAO2 n C) {β : Type}
    {φ : ℕ → β → Prop} {j : ℕ} (hj : a24_AndG C j) {y : β} (h : a24_Lb n C φ (n + j) y) : φ j y := by
  obtain ⟨j', hj', hp⟩ := h
  have e := a24_Rr_and hC j hj _ hj'
  have e2 : j' = j := by omega
  rw [← e2]
  exact hp

theorem a24_FM3 {n : ℕ} {C : Circuit} (hC : PEqualNP.TopForm.IsAO2 n C) {β : Type}
    (φ : ℕ → β → Prop) (w0 w : ℕ) (h : a24_Rr n C w0 w) (y0 : β) :
    (∀ y, a24_Lb n C φ w y → y = y0) ∨ (∃ y, a24_Lb n C φ w0 y ∧ y ≠ y0) ∨
    ∃ jo b, a24_OrG C jo ∧ a24_Rr n C (n + jo) w ∧ a24_Rr n C w0 (a24_inp C jo b) ∧
      (∀ y, a24_Lb n C φ (a24_inp C jo b) y → y = y0) ∧ ∃ y, a24_Lb n C φ (n + jo) y ∧ y ≠ y0 := by
  by_cases ha : ∀ y, a24_Lb n C φ w y → y = y0
  · exact Or.inl ha
  by_cases hb : ∃ y, a24_Lb n C φ w0 y ∧ y ≠ y0
  · exact Or.inr (Or.inl hb)
  refine Or.inr (Or.inr ?_)
  have h0 : ∀ y, a24_Lb n C φ w0 y → y = y0 := by
    intro y hy
    by_contra hne
    exact hb ⟨y, hy, hne⟩
  obtain ⟨jo, b, h2, h3, h4, h5, h6⟩ := a24_FMG hC (fun v => ∀ y, a24_Lb n C φ v y → y = y0) w0 w h h0 ha
  refine ⟨jo, b, h2, h3, h4, h5, ?_⟩
  by_contra hne
  apply h6
  intro y hy
  by_contra hne2
  exact hne ⟨y, hy, hne2⟩

-- fragment f02_sib
section


theorem a24_a07_key (N M : ℕ) (I : Fin N → Fin M → Prop) (L : Set (Fin M))
    (H : ∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 →
      ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5))
    (p q z : Fin N) (hpq : p ≠ q)
    (h3 : 3 ≤ {l : Fin M | l ∈ L ∧ I p l}.ncard)
    (hsub : L ⊆ {l2 : Fin M | I q l2 ∨ I z l2}) : p = z := by
  by_contra hpz
  have h3' : 2 < {l : Fin M | l ∈ L ∧ I p l}.ncard := h3
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ :=
    (Set.two_lt_ncard_iff (Set.toFinite _)).mp h3'
  obtain ⟨haL, hpa⟩ := ha
  obtain ⟨hbL, hpb⟩ := hb
  obtain ⟨hcL, hpc⟩ := hc
  rcases hsub haL with qa | za <;> rcases hsub hbL with qb | zb <;>
    rcases hsub hcL with qc | zc
  all_goals first
    | exact H p q a b hpq hab ⟨hpa, qa, hpb, qb⟩
    | exact H p q a c hpq hac ⟨hpa, qa, hpc, qc⟩
    | exact H p q b c hpq hbc ⟨hpb, qb, hpc, qc⟩
    | exact H p z a b hpz hab ⟨hpa, za, hpb, zb⟩
    | exact H p z a c hpz hac ⟨hpa, za, hpc, zc⟩
    | exact H p z b c hpz hbc ⟨hpb, zb, hpc, zc⟩

theorem a24_a07_card_aux {α : Type} [Finite α] (S : Set α)
    (h : ∀ q ∈ S, ∃ z, ∀ p ∈ S, p ≠ q → p = z) : S.ncard ≤ 2 := by
  rcases Set.eq_empty_or_nonempty S with hE | ⟨q, hq⟩
  · rw [hE, Set.ncard_empty]
    exact Nat.zero_le 2
  · obtain ⟨z, hz⟩ := h q hq
    have hS : S ⊆ ({q, z} : Set α) := by
      intro p hp
      by_cases hpq : p = q
      · exact Or.inl hpq
      · exact Or.inr (hz p hp hpq)
    have h2 : ({q, z} : Set α).ncard ≤ 2 := by
      have h1 := Set.ncard_insert_le q ({z} : Set α)
      rw [Set.ncard_singleton] at h1
      exact h1
    exact le_trans (Set.ncard_le_ncard hS (Set.toFinite _)) h2

theorem a24_l2407 : ∀ (N M : ℕ) (I : Fin N → Fin M → Prop) (L : Set (Fin M)), (∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 → ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5)) → {p : Fin N | 3 ≤ {l : Fin M | l ∈ L ∧ I p l}.ncard ∧ ∃ z : Fin N, L ⊆ {l2 : Fin M | I p l2 ∨ I z l2}}.ncard ≤ 2 := by
  intro N M I L H
  apply a24_a07_card_aux
  intro q hq
  obtain ⟨-, z, hz⟩ := hq
  refine ⟨z, ?_⟩
  intro p hp hpq
  obtain ⟨hp3, -⟩ := hp
  exact a24_a07_key N M I L H p q z hpq hp3 hz


end

section


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

/-- One upward step along an OR gate. -/
def a24_a10_stp (n : ℕ) (C : Circuit) : ℕ → ℕ → Prop :=
  fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧
    (gateAt C rj).op = GateOp.or ∧ ra ∈ (gateAt C rj).inputs

/-- The pairs having a wire above the point whose shadow has two points, all on the line. -/
def a24_a10_Bp (N M : ℕ) (pw : Fin N → ℕ) (I : Fin N → Fin M → Prop) (R : ℕ → ℕ → Prop)
    (ex : Fin N × Fin M) : Prop :=
  ∃ w, R (pw ex.1) w ∧ (∀ q : Fin N, R (pw q) w → I q ex.2) ∧
    2 ≤ {r : Fin N | R (pw r) w}.ncard

theorem a24_a10_gate_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  have h : gateAt C j = C.gates[j] := by
    unfold gateAt
    simp [List.getD_eq_getElem?_getD, hj]
  rw [h]
  exact List.getElem_mem hj

theorem a24_a10_two_inputs (l : List ℕ) (hl : l.length = 2) (b : ℕ) (hb : b ∈ l) :
    b = l.getD 0 0 ∨ b = l.getD 1 0 := by
  rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, t⟩⟩⟩
  · simp at hl
  · simp at hl
  · simpa using hb
  · simp at hl

theorem a24_a10_base (n N : ℕ) (C : Circuit) (pw : Fin N → ℕ) (hpw : Function.Injective pw)
    (hpn : ∀ p2 : Fin N, pw p2 < n) (r p : Fin N)
    (h : Relation.ReflTransGen (a24_a10_stp n C) (pw r) (pw p)) : r = p := by
  rcases Relation.ReflTransGen.cases_tail h with h1 | ⟨b, _, hs⟩
  · exact (hpw h1).symm
  · obtain ⟨_, rj, hrj, _⟩ := hs
    have := hpn p
    omega

theorem a24_a10_key (n N : ℕ) (C : Circuit) (pw : Fin N → ℕ)
    (hlen : ∀ g ∈ C.gates, g.inputs.length = 2)
    (hpw : Function.Injective pw) (hpn : ∀ p2 : Fin N, pw p2 < n)
    (R : ℕ → ℕ → Prop) (hR : R = Relation.ReflTransGen (a24_a10_stp n C))
    (p : Fin N) (w : ℕ) (hw : R (pw p) w) (h2 : 2 ≤ {r : Fin N | R (pw r) w}.ncard) :
    ∃ jo, jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or ∧ (∀ x, R x (n + jo) → R x w) ∧
      2 ≤ {r : Fin N | R (pw r) (n + jo)}.ncard ∧
      ∃ i : Fin 2, R (pw p) ((gateAt C jo).inputs.getD i.val 0) ∧
        ∀ q : Fin N, R (pw q) ((gateAt C jo).inputs.getD i.val 0) → q = p := by
  subst hR
  revert h2
  induction hw with
  | refl =>
    intro h2
    exfalso
    obtain ⟨a, b, ha, hb, hab⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).mp h2
    have e1 : a = p := a24_a10_base n N C pw hpw hpn a p ha
    have e2 : b = p := a24_a10_base n N C pw hpw hpn b p hb
    exact hab (e1.trans e2.symm)
  | @tail b c hab hbc ih =>
    intro h2
    by_cases hb : 2 ≤ {r : Fin N | Relation.ReflTransGen (a24_a10_stp n C) (pw r) b}.ncard
    · obtain ⟨jo, h1, h3, h4, h5, h6⟩ := ih hb
      exact ⟨jo, h1, h3, fun x hx => (h4 x hx).tail hbc, h5, h6⟩
    · have hbc2 := hbc
      obtain ⟨_, rj, hc, hrj, hop, hmem⟩ := hbc2
      subst hc
      have hm : gateAt C rj ∈ C.gates := a24_a10_gate_mem C rj hrj
      have hl : (gateAt C rj).inputs.length = 2 := hlen _ hm
      have huniq : ∀ q : Fin N, Relation.ReflTransGen (a24_a10_stp n C) (pw q) b → q = p := by
        intro q hq
        by_contra hne
        apply hb
        have hsub : ({q, p} : Set (Fin N)) ⊆
            {r : Fin N | Relation.ReflTransGen (a24_a10_stp n C) (pw r) b} := by
          intro r hr
          rcases Set.mem_insert_iff.mp hr with h | h
          · rw [h]; exact hq
          · rw [Set.mem_singleton_iff.mp h]; exact hab
        calc 2 = ({q, p} : Set (Fin N)).ncard := (Set.ncard_pair hne).symm
          _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
      have hcase : b = (gateAt C rj).inputs.getD 0 0 ∨ b = (gateAt C rj).inputs.getD 1 0 :=
        a24_a10_two_inputs _ hl b hmem
      refine ⟨rj, hrj, hop, fun x hx => hx, h2, ?_⟩
      rcases hcase with h0 | h1
      · refine ⟨⟨0, by omega⟩, ?_, ?_⟩
        · show Relation.ReflTransGen (a24_a10_stp n C) (pw p) ((gateAt C rj).inputs.getD 0 0)
          rw [← h0]; exact hab
        · intro q hq
          apply huniq q
          rw [h0]; exact hq
      · refine ⟨⟨1, by omega⟩, ?_, ?_⟩
        · show Relation.ReflTransGen (a24_a10_stp n C) (pw p) ((gateAt C rj).inputs.getD 1 0)
          rw [← h1]; exact hab
        · intro q hq
          apply huniq q
          rw [h1]; exact hq

theorem a24_a10_leafR (n : ℕ) (C : Circuit) (R : ℕ → ℕ → Prop) (t : ℕ) (L : List (ℕ × ℕ))
    (hT : ∀ Q : ℕ → List (ℕ × ℕ) → Prop,
      (∀ (qv qt : ℕ), qv < n → R qv qt → Q qt [(qt, qv)]) →
      (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length →
        (gateAt C qj).op = GateOp.and → R (n + qj) qt →
        Q ((gateAt C qj).inputs.getD 0 0) qL1 → Q ((gateAt C qj).inputs.getD 1 0) qL2 →
        Q qt (qL1 ++ qL2)) → Q t L) :
    ∀ g ∈ L, R g.2 g.1 := by
  refine hT (fun t L => ∀ g ∈ L, R g.2 g.1) ?_ ?_
  · intro qv qt _ hR g hg
    rw [List.mem_singleton] at hg
    rw [hg]
    exact hR
  · intro qj qt L1 L2 _ _ _ h1 h2 g hg
    rcases List.mem_append.mp hg with h | h
    · exact h1 g h
    · exact h2 g h

theorem a24_a10_final {α : Type} [Finite α] (PA PX : α → Prop) (k : ℕ) (B : Set α) (hB : B.ncard ≤ k)
    (h : ∀ a, PA a → PX a → a ∈ B) :
    {a | PA a}.ncard ≤ k + {a | PA a ∧ ¬ PX a}.ncard := by
  have hsub : {a | PA a} ⊆ B ∪ {a | PA a ∧ ¬ PX a} := by
    intro a ha
    by_cases hx : PX a
    · exact Or.inl (h a ha hx)
    · exact Or.inr ⟨ha, hx⟩
  calc {a | PA a}.ncard ≤ (B ∪ {a | PA a ∧ ¬ PX a}).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ B.ncard + {a | PA a ∧ ¬ PX a}.ncard := Set.ncard_union_le _ _
    _ ≤ k + {a | PA a ∧ ¬ PX a}.ncard := by omega

theorem a24_a10_sib_main_aux : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → Function.Injective pw → Function.Injective lw → (∀ (p1 : Fin N) (l1 : Fin M), pw p1 ≠ lw l1) → (∀ p2 : Fin N, pw p2 < n) → (∀ l2 : Fin M, lw l2 < n) → (∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 → ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5)) → (∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2 → (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) → PEqualNP.MetaComplexity.circuitFun n C (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)) = false) → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → ∀ T : ℕ → List (ℕ × ℕ) → Prop, T = (fun tt tL => ∀ Q : ℕ → List (ℕ × ℕ) → Prop, (∀ (qv qt : ℕ), qv < n → R qv qt → Q qt [(qt, qv)]) → (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C qj).op = PEqualNP.CircuitLowerBounds.GateOp.and → R (n + qj) qt → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 0 0) qL1 → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 1 0) qL2 → Q qt (qL1 ++ qL2)) → Q tt tL) → (∀ (p6 : Fin N) (l6 : Fin M), I p6 l6 → ∃ L6 : List (ℕ × ℕ), (∃ (j6 : ℕ) (La6 Lb6 : List (ℕ × ℕ)), j6 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ R (n + j6) C.output ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j6).inputs.getD 0 0) La6 ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j6).inputs.getD 1 0) Lb6 ∧ L6 = La6 ++ Lb6) ∧ (∀ g6 ∈ L6, g6.2 = pw p6 ∨ g6.2 = lw l6) ∧ (L6.filter (fun e6 => decide (e6.2 = pw p6))).length ∈ ({1, 2} : Finset ℕ) ∧ (L6.filter (fun f6 => decide (f6.2 = lw l6))).length ∈ ({1, 2} : Finset ℕ)) → {ei : Fin N × Fin M | I ei.1 ei.2}.ncard ≤ 2 * {jo : ℕ | jo < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C jo).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard + {ex : Fin N × Fin M | I ex.1 ex.2 ∧ ¬ ∃ L7 : List (ℕ × ℕ), (∃ (j7 : ℕ) (La7 Lb7 : List (ℕ × ℕ)), j7 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j7).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ R (n + j7) C.output ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j7).inputs.getD 0 0) La7 ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j7).inputs.getD 1 0) Lb7 ∧ L7 = La7 ++ Lb7) ∧ (∀ g7 ∈ L7, g7.2 = pw ex.1 ∨ g7.2 = lw ex.2) ∧ (L7.filter (fun e7 => decide (e7.2 = pw ex.1))).length ∈ ({1, 2} : Finset ℕ) ∧ (L7.filter (fun f7 => decide (f7.2 = lw ex.2))).length ∈ ({1, 2} : Finset ℕ) ∧ ∃ g8 ∈ L7, g8.2 = pw ex.1 ∧ (∀ q8 : Fin N, R (pw q8) g8.1 → I q8 ex.2) ∧ 2 ≤ {r8 : Fin N | R (pw r8) g8.1}.ncard}.ncard := by
  intro n N M pw lw I C hAO hpw hlw hne hpn hln hK hsound R hR T hT hread
  subst hT
  have hlen := hAO.2.2
  have hBex : ∀ ex : Fin N × Fin M, a24_a10_Bp N M pw I R ex → ∃ y : ℕ × Fin 2,
      (y.1 < C.gates.length ∧ (gateAt C y.1).op = GateOp.or) ∧
      2 ≤ {r : Fin N | R (pw r) (n + y.1)}.ncard ∧
      (∀ q : Fin N, R (pw q) (n + y.1) → I q ex.2) ∧
      R (pw ex.1) ((gateAt C y.1).inputs.getD y.2.val 0) ∧
      ∀ q : Fin N, R (pw q) ((gateAt C y.1).inputs.getD y.2.val 0) → q = ex.1 := by
    rintro ex ⟨w, hw, hsh, h2⟩
    obtain ⟨jo, h1, h3, h4, h5, i, h6, h7⟩ := a24_a10_key n N C pw hlen hpw hpn R hR ex.1 w hw h2
    exact ⟨(jo, i), ⟨h1, h3⟩, h5, fun q hq => hsh q (h4 _ hq), h6, h7⟩
  choose! f hf using hBex
  have hO : {jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or}.Finite :=
    (Set.finite_lt_nat C.gates.length).subset (fun jo h => h.1)
  have hBcard : {ex : Fin N × Fin M | a24_a10_Bp N M pw I R ex}.ncard ≤
      2 * {jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or}.ncard := by
    have h1 : {ex : Fin N × Fin M | a24_a10_Bp N M pw I R ex}.ncard ≤
        ({jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or} ×ˢ
          (Set.univ : Set (Fin 2))).ncard := by
      refine Set.ncard_le_ncard_of_injOn f ?_ ?_ (hO.prod Set.finite_univ)
      · intro ex hex
        exact ⟨(hf ex hex).1, Set.mem_univ _⟩
      · intro ex hex ex2 hex2 heq
        have P1 := hf ex hex
        have P2 := hf ex2 hex2
        rw [← heq] at P2
        obtain ⟨_, h2a, hla, hra, hua⟩ := P1
        obtain ⟨_, _, hlb, hrb, hub⟩ := P2
        have e1 : ex2.1 = ex.1 := hua ex2.1 hrb
        obtain ⟨q1, q2, hq1, hq2, hq12⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).mp h2a
        have e2 : ex.2 = ex2.2 := by
          by_contra hl
          exact hK q1 q2 ex.2 ex2.2 hq12 hl ⟨hla q1 hq1, hla q2 hq2, hlb q1 hq1, hlb q2 hq2⟩
        exact Prod.ext e1.symm e2
    rw [Set.ncard_prod, Set.ncard_univ, Nat.card_fin] at h1
    omega
  refine a24_a10_final _ _ _ {ex : Fin N × Fin M | a24_a10_Bp N M pw I R ex} hBcard ?_
  intro a ha hx
  obtain ⟨L7, ⟨j7, La7, Lb7, hj7, hop7, hR7, hTa, hTb, hL⟩, hvars, hcp, hcl, g8, hg8, hg8p,
    hsh, h2⟩ := hx
  subst hL
  have hRg : R g8.2 g8.1 := by
    rcases List.mem_append.mp hg8 with h | h
    · exact a24_a10_leafR n C R _ La7 hTa g8 h
    · exact a24_a10_leafR n C R _ Lb7 hTb g8 h
  rw [hg8p] at hRg
  exact ⟨g8.1, hRg, hsh, h2⟩

theorem a24_a10_l2409 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → Function.Injective pw → Function.Injective lw → (∀ (p1 : Fin N) (l1 : Fin M), pw p1 ≠ lw l1) → (∀ p2 : Fin N, pw p2 < n) → (∀ l2 : Fin M, lw l2 < n) → (∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 → ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5)) → (∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2 → (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) → PEqualNP.MetaComplexity.circuitFun n C (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)) = false) → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → ∀ T : ℕ → List (ℕ × ℕ) → Prop, T = (fun tt tL => ∀ Q : ℕ → List (ℕ × ℕ) → Prop, (∀ (qv qt : ℕ), qv < n → R qv qt → Q qt [(qt, qv)]) → (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C qj).op = PEqualNP.CircuitLowerBounds.GateOp.and → R (n + qj) qt → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 0 0) qL1 → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 1 0) qL2 → Q qt (qL1 ++ qL2)) → Q tt tL) → (∀ (p6 : Fin N) (l6 : Fin M), I p6 l6 → ∃ L6 : List (ℕ × ℕ), (∃ (j6 : ℕ) (La6 Lb6 : List (ℕ × ℕ)), j6 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ R (n + j6) C.output ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j6).inputs.getD 0 0) La6 ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j6).inputs.getD 1 0) Lb6 ∧ L6 = La6 ++ Lb6) ∧ (∀ g6 ∈ L6, g6.2 = pw p6 ∨ g6.2 = lw l6) ∧ (L6.filter (fun e6 => decide (e6.2 = pw p6))).length ∈ ({1, 2} : Finset ℕ) ∧ (L6.filter (fun f6 => decide (f6.2 = lw l6))).length ∈ ({1, 2} : Finset ℕ)) → {ei : Fin N × Fin M | I ei.1 ei.2}.ncard ≤ 2 * {jo : ℕ | jo < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C jo).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard + {ex : Fin N × Fin M | I ex.1 ex.2 ∧ ¬ ∃ L7 : List (ℕ × ℕ), (∃ (j7 : ℕ) (La7 Lb7 : List (ℕ × ℕ)), j7 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j7).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ R (n + j7) C.output ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j7).inputs.getD 0 0) La7 ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j7).inputs.getD 1 0) Lb7 ∧ L7 = La7 ++ Lb7) ∧ (∀ g7 ∈ L7, g7.2 = pw ex.1 ∨ g7.2 = lw ex.2) ∧ (L7.filter (fun e7 => decide (e7.2 = pw ex.1))).length ∈ ({1, 2} : Finset ℕ) ∧ (L7.filter (fun f7 => decide (f7.2 = lw ex.2))).length ∈ ({1, 2} : Finset ℕ) ∧ ∃ g8 ∈ L7, g8.2 = pw ex.1 ∧ (∀ q8 : Fin N, R (pw q8) g8.1 → I q8 ex.2) ∧ 2 ≤ {r8 : Fin N | R (pw r8) g8.1}.ncard}.ncard :=
  a24_a10_sib_main_aux

theorem a24_a10_two_sided_swap_card {α β : Type} (P : α × β → Prop) (P' : β × α → Prop)
    (h : ∀ a b, P' (b, a) ↔ P (a, b)) :
    {e : β × α | P' e}.ncard = {e : α × β | P e}.ncard := by
  have himg : Prod.swap '' {e : α × β | P e} = {e : β × α | P' e} := by
    ext ⟨b, a⟩
    constructor
    · intro hm
      obtain ⟨⟨x, y⟩, hx, hxy⟩ := (Set.mem_image _ _ _).mp hm
      have h3 : y = b ∧ x = a := Prod.mk.inj hxy
      rw [← h3.1, ← h3.2]
      show P' (y, x)
      exact (h x y).mpr hx
    · intro hm
      exact (Set.mem_image _ _ _).mpr ⟨(a, b), (h a b).mp hm, rfl⟩
  rw [← himg]
  exact Set.ncard_image_of_injective _ Prod.swap_injective

theorem a24_a10_two_sided_combine {α β : Type} [Finite α] [Finite β] (S A B : α × β → Prop)
    (S' A' : β × α → Prop) (k : ℕ)
    (hS : ∀ a b, S' (b, a) ↔ S (a, b))
    (hB : ∀ a b, S (a, b) → (A' (b, a) ↔ B (a, b)))
    (h1 : {e : α × β | S e}.ncard ≤ 2 * k + {e : α × β | S e ∧ ¬ A e}.ncard)
    (h2 : {e : β × α | S' e}.ncard ≤ 2 * k + {e : β × α | S' e ∧ ¬ A' e}.ncard) :
    {e : α × β | S e}.ncard ≤ 4 * k + {e : α × β | S e ∧ ¬ A e ∧ ¬ B e}.ncard := by
  have e1 : {e : β × α | S' e}.ncard = {e : α × β | S e}.ncard := a24_a10_two_sided_swap_card S S' hS
  have e2 : {e : β × α | S' e ∧ ¬ A' e}.ncard = {e : α × β | S e ∧ ¬ B e}.ncard := by
    refine a24_a10_two_sided_swap_card (fun e => S e ∧ ¬ B e) (fun e => S' e ∧ ¬ A' e) ?_
    intro a b
    constructor
    · intro hh
      exact ⟨(hS a b).mp hh.1, fun hb => hh.2 ((hB a b ((hS a b).mp hh.1)).mpr hb)⟩
    · intro hh
      exact ⟨(hS a b).mpr hh.1, fun ha => hh.2 ((hB a b hh.1).mp ha)⟩
  have hU := Set.ncard_union_add_ncard_inter {e : α × β | S e ∧ ¬ A e} {e : α × β | S e ∧ ¬ B e}
  have hsub1 : ({e : α × β | S e ∧ ¬ A e} ∪ {e : α × β | S e ∧ ¬ B e}).ncard
      ≤ {e : α × β | S e}.ncard := by
    apply Set.ncard_le_ncard
    · intro e he
      rcases he with hh | hh
      · exact hh.1
      · exact hh.1
    · exact Set.toFinite _
  have hsub2 : ({e : α × β | S e ∧ ¬ A e} ∩ {e : α × β | S e ∧ ¬ B e}).ncard
      ≤ {e : α × β | S e ∧ ¬ A e ∧ ¬ B e}.ncard := by
    apply Set.ncard_le_ncard
    · intro e he
      exact ⟨he.1.1, he.1.2, he.2.2⟩
    · exact Set.toFinite _
  rw [e1, e2] at h2
  omega

theorem a24_l2410 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → Function.Injective pw → Function.Injective lw → (∀ (p1 : Fin N) (l1 : Fin M), pw p1 ≠ lw l1) → (∀ p2 : Fin N, pw p2 < n) → (∀ l2 : Fin M, lw l2 < n) → (∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 → ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5)) → (∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2 → (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) → PEqualNP.MetaComplexity.circuitFun n C (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)) = false) → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → ∀ T : ℕ → List (ℕ × ℕ) → Prop, T = (fun tt tL => ∀ Q : ℕ → List (ℕ × ℕ) → Prop, (∀ (qv qt : ℕ), qv < n → R qv qt → Q qt [(qt, qv)]) → (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C qj).op = PEqualNP.CircuitLowerBounds.GateOp.and → R (n + qj) qt → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 0 0) qL1 → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 1 0) qL2 → Q qt (qL1 ++ qL2)) → Q tt tL) → (∀ (p6 : Fin N) (l6 : Fin M), I p6 l6 → ∃ L6 : List (ℕ × ℕ), (∃ (j6 : ℕ) (La6 Lb6 : List (ℕ × ℕ)), j6 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ R (n + j6) C.output ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j6).inputs.getD 0 0) La6 ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j6).inputs.getD 1 0) Lb6 ∧ L6 = La6 ++ Lb6) ∧ (∀ g6 ∈ L6, g6.2 = pw p6 ∨ g6.2 = lw l6) ∧ (L6.filter (fun e6 => decide (e6.2 = pw p6))).length ∈ ({1, 2} : Finset ℕ) ∧ (L6.filter (fun f6 => decide (f6.2 = lw l6))).length ∈ ({1, 2} : Finset ℕ)) → {ei : Fin N × Fin M | I ei.1 ei.2}.ncard ≤ 4 * {jo : ℕ | jo < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C jo).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard + {ey : Fin N × Fin M | I ey.1 ey.2 ∧ (¬ ∃ L7 : List (ℕ × ℕ), (∃ (j7 : ℕ) (La7 Lb7 : List (ℕ × ℕ)), j7 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j7).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ R (n + j7) C.output ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j7).inputs.getD 0 0) La7 ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j7).inputs.getD 1 0) Lb7 ∧ L7 = La7 ++ Lb7) ∧ (∀ g7 ∈ L7, g7.2 = pw ey.1 ∨ g7.2 = lw ey.2) ∧ (L7.filter (fun e7 => decide (e7.2 = pw ey.1))).length ∈ ({1, 2} : Finset ℕ) ∧ (L7.filter (fun f7 => decide (f7.2 = lw ey.2))).length ∈ ({1, 2} : Finset ℕ) ∧ ∃ g8 ∈ L7, g8.2 = pw ey.1 ∧ (∀ q8 : Fin N, R (pw q8) g8.1 → I q8 ey.2) ∧ 2 ≤ {r8 : Fin N | R (pw r8) g8.1}.ncard) ∧ ¬ ∃ L9 : List (ℕ × ℕ), (∃ (j9 : ℕ) (La9 Lb9 : List (ℕ × ℕ)), j9 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j9).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ R (n + j9) C.output ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j9).inputs.getD 0 0) La9 ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j9).inputs.getD 1 0) Lb9 ∧ L9 = La9 ++ Lb9) ∧ (∀ g9 ∈ L9, g9.2 = pw ey.1 ∨ g9.2 = lw ey.2) ∧ (L9.filter (fun e9 => decide (e9.2 = pw ey.1))).length ∈ ({1, 2} : Finset ℕ) ∧ (L9.filter (fun f9 => decide (f9.2 = lw ey.2))).length ∈ ({1, 2} : Finset ℕ) ∧ ∃ g10 ∈ L9, g10.2 = lw ey.2 ∧ (∀ q10 : Fin M, R (lw q10) g10.1 → I ey.1 q10) ∧ 2 ≤ {r10 : Fin M | R (lw r10) g10.1}.ncard}.ncard := by
  intro n N M pw lw I C hAO hpi hli hne hpn hln hK hS R hR T hT hTree
  have h1 := a24_a10_l2409 n N M pw lw I C hAO hpi hli hne hpn hln hK hS R hR T hT hTree
  have h2 := a24_a10_l2409 n M N lw pw (fun l p => I p l) C hAO hli hpi
    (fun p l => (hne l p).symm) hln hpn
    (fun p4 p5 l4 l5 hp hl h => hK l4 l5 p4 p5 hl hp ⟨h.1, h.2.2.1, h.2.1, h.2.2.2⟩)
    (fun P Y hP hY hno => by
      have e : (P.image lw ∪ Y.image pw) = (Y.image pw ∪ P.image lw) := Finset.union_comm _ _
      rw [e]
      exact hS Y P hY hP (fun p hp l hl => hno l hl p hp))
    R hR T hT
    (fun p6 l6 h => by
      obtain ⟨L, ht, hall, hf1, hf2⟩ := hTree l6 p6 h
      exact ⟨L, ht, fun g hg => (hall g hg).symm, hf2, hf1⟩)
  refine a24_a10_two_sided_combine _ _ _ _ _ _ ?_ ?_ h1 h2
  · intro a b
    exact Iff.rfl
  · intro a b _
    constructor
    · intro hh
      obtain ⟨L, ht, hall, hf1, hf2, hg⟩ := hh
      exact ⟨L, ht, fun g hg' => (hall g hg').symm, hf2, hf1, hg⟩
    · intro hh
      obtain ⟨L, ht, hall, hf1, hf2, hg⟩ := hh
      exact ⟨L, ht, fun g hg' => (hall g hg').symm, hf2, hf1, hg⟩


end

-- fragment f03_f3
def a24_ChF3 (n : ℕ) (C : Circuit) {K1 K2 : ℕ} (yw : Fin K2 → ℕ) (Cmp : Fin K1 → Fin K2 → Prop)
    (key : ℕ × Bool) (a : Fin K1) (y : Fin K2) : Prop :=
  a24_Rr n C (yw y) (a24_inp C key.1 key.2) ∧ Cmp a y ∧
  {t : Fin K2 | a24_Rr n C (yw t) (a24_inp C key.1 key.2) ∧ Cmp a t}.ncard ≤ 2 ∧
  3 ≤ {t : Fin K2 | a24_Rr n C (yw t) (n + key.1) ∧ Cmp a t}.ncard ∧
  ∃ z : Fin K1, ∀ t, a24_Rr n C (yw t) (n + key.1) → Cmp a t ∨ Cmp z t

theorem a24_F3_exists {n : ℕ} {C : Circuit} (hC : PEqualNP.TopForm.IsAO2 n C) {K1 K2 : ℕ}
    (yw : Fin K2 → ℕ) (hinj : Function.Injective yw) (hlt : ∀ y, yw y < n)
    (Cmp : Fin K1 → Fin K2 → Prop) (d : ℕ) (a : Fin K1) (y : Fin K2)
    (h : a24_Rr n C (yw y) d) (hc : Cmp a y)
    (h3 : 3 ≤ {t : Fin K2 | a24_Rr n C (yw t) d ∧ Cmp a t}.ncard)
    (z : Fin K1) (hz : ∀ t, a24_Rr n C (yw t) d → Cmp a t ∨ Cmp z t) :
    ∃ jo b, a24_OrG C jo ∧ a24_ChF3 n C yw Cmp (jo, b) a y := by
  have h0 : {t : Fin K2 | a24_Rr n C (yw t) (yw y) ∧ Cmp a t}.ncard ≤ 2 := by
    have hsub : {t : Fin K2 | a24_Rr n C (yw t) (yw y) ∧ Cmp a t} ⊆ {y} := by
      intro t ht
      exact hinj (a24_Rr_input hC _ (hlt y) _ ht.1)
    have h := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_singleton] at h
    omega
  obtain ⟨jo, b, h2, h3', h4, h5, h6⟩ := a24_FMG hC
    (fun v => {t : Fin K2 | a24_Rr n C (yw t) v ∧ Cmp a t}.ncard ≤ 2) (yw y) d h h0
    (not_le.mpr (by omega))
  have h6' := not_le.mp h6
  refine ⟨jo, b, h2, h4, hc, h5, ?_, z, fun t ht => hz t (a24_Rr_trans ht h3')⟩
  show 3 ≤ {t : Fin K2 | a24_Rr n C (yw t) (n + jo) ∧ Cmp a t}.ncard
  omega

theorem a24_F3_fiber {n : ℕ} {C : Circuit} {X : Type} {K1 K2 : ℕ} (fa : X → Fin K1) (fb : X → Fin K2)
    (hinj : ∀ e e' : X, fa e = fa e' → fb e = fb e' → e = e')
    (yw : Fin K2 → ℕ) (Cmp : Fin K1 → Fin K2 → Prop) (h4 : a24_No4 Cmp) (key : ℕ × Bool) :
    a24_Bd (fun e : X => a24_ChF3 n C yw Cmp key (fa e) (fb e)) 4 := by
  intro S hS
  have hm2 := a24_l2407 K1 K2 Cmp {t : Fin K2 | a24_Rr n C (yw t) (n + key.1)} h4
  have hh : S.card ≤ 2 * 2 := by
    refine a24_card_le_prod S fa 2 2 ?_ ?_
    · intro T hT
      refine a24_card_le_of_maps T id (fun e _ e' _ h => h) _ (Set.toFinite _) 2 hm2 ?_
      intro a ha
      obtain ⟨e, he, rfl⟩ := hT a ha
      obtain ⟨_, _, _, h3, z, hz⟩ := hS e he
      exact ⟨h3, z, fun t ht => hz t ht⟩
    · intro a T hT
      rcases T.eq_empty_or_nonempty with h | ⟨e0, he0⟩
      · simp [h]
      · obtain ⟨he0S, hae0⟩ := hT e0 he0
        have hk := (hS e0 he0S).2.2.1
        rw [hae0] at hk
        refine a24_card_le_of_maps T fb (fun e he e' he' h =>
          hinj e e' ((hT e he).2.trans (hT e' he').2.symm) h) _ (Set.toFinite _) 2 hk ?_
        intro e he
        obtain ⟨heS, hae⟩ := hT e he
        obtain ⟨h1, h2, _⟩ := hS e heS
        rw [hae] at h2
        exact ⟨h1, h2⟩
  omega

-- fragment f04_tree
def a24_Tt (n : ℕ) (C : Circuit) (tt : ℕ) (tL : List (ℕ × ℕ)) : Prop :=
  ∀ Q : ℕ → List (ℕ × ℕ) → Prop, (∀ (qv qt : ℕ), qv < n → a24_Rr n C qv qt → Q qt [(qt, qv)]) → (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length → (gateAt C qj).op = GateOp.and → a24_Rr n C (n + qj) qt → Q ((gateAt C qj).inputs.getD 0 0) qL1 → Q ((gateAt C qj).inputs.getD 1 0) qL2 → Q qt (qL1 ++ qL2)) → Q tt tL

theorem a24_Tt_inv {n : ℕ} {C : Circuit} {t : ℕ} {L : List (ℕ × ℕ)} (h : a24_Tt n C t L) :
    (∃ v, v < n ∧ a24_Rr n C v t ∧ L = [(t, v)]) ∨
    (∃ j L1 L2, a24_AndG C j ∧ a24_Rr n C (n + j) t ∧ a24_Tt n C (a24_inp C j false) L1 ∧
      a24_Tt n C (a24_inp C j true) L2 ∧ L = L1 ++ L2) := by
  refine (h (fun t L => a24_Tt n C t L ∧ ((∃ v, v < n ∧ a24_Rr n C v t ∧ L = [(t, v)]) ∨
    (∃ j L1 L2, a24_AndG C j ∧ a24_Rr n C (n + j) t ∧ a24_Tt n C (a24_inp C j false) L1 ∧
      a24_Tt n C (a24_inp C j true) L2 ∧ L = L1 ++ L2))) ?_ ?_).2
  · intro qv qt hv hR
    exact ⟨fun Q h1 _ => h1 qv qt hv hR, Or.inl ⟨qv, hv, hR, rfl⟩⟩
  · intro qj qt L1 L2 hj hop hR h1 h2
    refine ⟨fun Q a b => b qj qt L1 L2 hj hop hR (h1.1 Q a b) (h2.1 Q a b),
      Or.inr ⟨qj, L1, L2, ⟨hj, hop⟩, hR, ?_, ?_, rfl⟩⟩
    · rw [a24_inp_false]; exact h1.1
    · rw [a24_inp_true]; exact h2.1

theorem a24_Tt_pos {n : ℕ} {C : Circuit} {t : ℕ} {L : List (ℕ × ℕ)} (h : a24_Tt n C t L) :
    1 ≤ L.length := by
  refine h (fun _ L => 1 ≤ L.length) ?_ ?_
  · intro qv qt _ _
    simp
  · intro qj qt L1 L2 _ _ _ h1 h2
    simp only [List.length_append]
    omega

theorem a24_Tt_leafR {n : ℕ} {C : Circuit} {t : ℕ} {L : List (ℕ × ℕ)} (h : a24_Tt n C t L) :
    ∀ g ∈ L, a24_Rr n C g.2 g.1 := by
  refine h (fun _ L => ∀ g ∈ L, a24_Rr n C g.2 g.1) ?_ ?_
  · intro qv qt _ hR g hg
    rw [List.mem_singleton] at hg
    rw [hg]
    exact hR
  · intro qj qt L1 L2 _ _ _ h1 h2 g hg
    rcases List.mem_append.mp hg with h | h
    · exact h1 g h
    · exact h2 g h

def a24_cnt (q : ℕ) (L : List (ℕ × ℕ)) : ℕ := (L.filter (fun e => decide (e.2 = q))).length

theorem a24_cnt_append (q : ℕ) (L1 L2 : List (ℕ × ℕ)) : a24_cnt q (L1 ++ L2) = a24_cnt q L1 + a24_cnt q L2 := by
  simp [a24_cnt]

theorem a24_cnt_single_eq (q s : ℕ) : a24_cnt q [(s, q)] = 1 := by
  simp [a24_cnt]

theorem a24_cnt_single_ne (q s p : ℕ) (h : p ≠ q) : a24_cnt q [(s, p)] = 0 := by
  simp [a24_cnt, h]

def a24_LOK (wp wl : ℕ) (X Y : ℕ → Prop) (L : List (ℕ × ℕ)) : Prop :=
  ∀ g ∈ L, (g.2 = wp ∧ X g.1) ∨ (g.2 = wl ∧ Y g.1)

theorem a24_LOK_left {wp wl : ℕ} {X Y : ℕ → Prop} {L1 L2 : List (ℕ × ℕ)}
    (h : a24_LOK wp wl X Y (L1 ++ L2)) : a24_LOK wp wl X Y L1 :=
  fun g hg => h g (List.mem_append.mpr (Or.inl hg))

theorem a24_LOK_right {wp wl : ℕ} {X Y : ℕ → Prop} {L1 L2 : List (ℕ × ℕ)}
    (h : a24_LOK wp wl X Y (L1 ++ L2)) : a24_LOK wp wl X Y L2 :=
  fun g hg => h g (List.mem_append.mpr (Or.inr hg))

theorem a24_cnt_total {wp wl : ℕ} {X Y : ℕ → Prop} (hne : wp ≠ wl) (L : List (ℕ × ℕ))
    (h : a24_LOK wp wl X Y L) : a24_cnt wp L + a24_cnt wl L = L.length := by
  induction L with
  | nil => simp [a24_cnt]
  | cons g L ih =>
    have ih' := ih (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))
    have e1 : a24_cnt wp (g :: L) = a24_cnt wp [g] + a24_cnt wp L := a24_cnt_append wp [g] L
    have e2 : a24_cnt wl (g :: L) = a24_cnt wl [g] + a24_cnt wl L := a24_cnt_append wl [g] L
    have hg := h g (List.mem_cons_self)
    have e3 : a24_cnt wp [g] + a24_cnt wl [g] = 1 := by
      obtain ⟨g1, g2⟩ := g
      rcases hg with ⟨hh, _⟩ | ⟨hh, _⟩
      · simp only at hh
        subst hh
        rw [a24_cnt_single_eq, a24_cnt_single_ne _ _ _ hne]
      · simp only at hh
        subst hh
        rw [a24_cnt_single_eq, a24_cnt_single_ne _ _ _ (Ne.symm hne)]
    simp only [List.length_cons]
    omega

theorem a24_D1 {n : ℕ} {C : Circuit} {wp wl : ℕ} {X Y : ℕ → Prop} (hne : wp ≠ wl) {t : ℕ}
    {L : List (ℕ × ℕ)} (h : a24_Tt n C t L) (hl : L.length = 1) (hk : a24_LOK wp wl X Y L) :
    (X t ∧ a24_cnt wp L = 1 ∧ a24_cnt wl L = 0) ∨ (Y t ∧ a24_cnt wp L = 0 ∧ a24_cnt wl L = 1) := by
  rcases a24_Tt_inv h with ⟨v, _, _, hL⟩ | ⟨j, L1, L2, _, _, h1, h2, hL⟩
  · subst hL
    rcases hk (t, v) (by simp) with ⟨hh, hx⟩ | ⟨hh, hy⟩
    · simp only at hh hx
      subst hh
      exact Or.inl ⟨hx, a24_cnt_single_eq _ _, a24_cnt_single_ne _ _ _ hne⟩
    · simp only at hh hy
      subst hh
      exact Or.inr ⟨hy, a24_cnt_single_ne _ _ _ (Ne.symm hne), a24_cnt_single_eq _ _⟩
  · exfalso
    have p1 := a24_Tt_pos h1
    have p2 := a24_Tt_pos h2
    rw [hL, List.length_append] at hl
    omega

theorem a24_D2 {n : ℕ} {C : Circuit} {wp wl : ℕ} {X Y : ℕ → Prop} (hne : wp ≠ wl) {t : ℕ}
    {L : List (ℕ × ℕ)} (h : a24_Tt n C t L) (hl : L.length = 2) (hk : a24_LOK wp wl X Y L) :
    ∃ j c, a24_AndG C j ∧ a24_Rr n C (n + j) t ∧
      ((X (a24_inp C j c) ∧ X (a24_inp C j (!c)) ∧ a24_cnt wp L = 2 ∧ a24_cnt wl L = 0) ∨
       (X (a24_inp C j c) ∧ Y (a24_inp C j (!c)) ∧ a24_cnt wp L = 1 ∧ a24_cnt wl L = 1) ∨
       (Y (a24_inp C j c) ∧ Y (a24_inp C j (!c)) ∧ a24_cnt wp L = 0 ∧ a24_cnt wl L = 2)) := by
  rcases a24_Tt_inv h with ⟨v, _, _, hL⟩ | ⟨j, L1, L2, hj, hR, h1, h2, hL⟩
  · exfalso
    rw [hL] at hl
    simp at hl
  · subst hL
    have p1 := a24_Tt_pos h1
    have p2 := a24_Tt_pos h2
    rw [List.length_append] at hl
    have e1 := a24_cnt_append wp L1 L2
    have e2 := a24_cnt_append wl L1 L2
    rcases a24_D1 hne h1 (by omega) (a24_LOK_left hk) with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
    · rcases a24_D1 hne h2 (by omega) (a24_LOK_right hk) with ⟨b1, b2, b3⟩ | ⟨b1, b2, b3⟩
      · exact ⟨j, false, hj, hR, Or.inl ⟨a1, b1, by omega, by omega⟩⟩
      · exact ⟨j, false, hj, hR, Or.inr (Or.inl ⟨a1, b1, by omega, by omega⟩)⟩
    · rcases a24_D1 hne h2 (by omega) (a24_LOK_right hk) with ⟨b1, b2, b3⟩ | ⟨b1, b2, b3⟩
      · exact ⟨j, true, hj, hR, Or.inr (Or.inl ⟨b1, a1, by omega, by omega⟩)⟩
      · exact ⟨j, false, hj, hR, Or.inr (Or.inr ⟨a1, b1, by omega, by omega⟩)⟩

theorem a24_D3 {n : ℕ} {C : Circuit} {wp wl : ℕ} {X Y : ℕ → Prop} {t : ℕ}
    {L : List (ℕ × ℕ)} (h : a24_Tt n C t L) (hl : L.length = 3) (hk : a24_LOK wp wl X Y L) :
    ∃ j c L1 L2, a24_AndG C j ∧ a24_Rr n C (n + j) t ∧ a24_Tt n C (a24_inp C j c) L1 ∧ a24_Tt n C (a24_inp C j (!c)) L2 ∧
      L1.length = 1 ∧ L2.length = 2 ∧ a24_LOK wp wl X Y L1 ∧ a24_LOK wp wl X Y L2 ∧
      a24_cnt wp L = a24_cnt wp L1 + a24_cnt wp L2 ∧ a24_cnt wl L = a24_cnt wl L1 + a24_cnt wl L2 := by
  rcases a24_Tt_inv h with ⟨v, _, _, hL⟩ | ⟨j, L1, L2, hj, hR, h1, h2, hL⟩
  · exfalso
    rw [hL] at hl
    simp at hl
  · subst hL
    have p1 := a24_Tt_pos h1
    have p2 := a24_Tt_pos h2
    rw [List.length_append] at hl
    have e1 := a24_cnt_append wp L1 L2
    have e2 := a24_cnt_append wl L1 L2
    by_cases h11 : L1.length = 1
    · exact ⟨j, false, L1, L2, hj, hR, h1, h2, h11, by omega, a24_LOK_left hk, a24_LOK_right hk, e1, e2⟩
    · exact ⟨j, true, L2, L1, hj, hR, h2, h1, by omega, by omega, a24_LOK_right hk, a24_LOK_left hk,
        by omega, by omega⟩

def a24_Sh2 (n : ℕ) (C : Circuit) (X Y : ℕ → Prop) : Prop :=
  ∃ jr b, a24_AndG C jr ∧ a24_Rr n C (n + jr) C.output ∧ X (a24_inp C jr b) ∧ Y (a24_inp C jr (!b))

def a24_Sh3 (n : ℕ) (C : Circuit) (X Y Z : ℕ → Prop) : Prop :=
  ∃ jr b j c, a24_AndG C jr ∧ a24_Rr n C (n + jr) C.output ∧ X (a24_inp C jr b) ∧ a24_AndG C j ∧
    a24_Rr n C (n + j) (a24_inp C jr (!b)) ∧ Y (a24_inp C j c) ∧ Z (a24_inp C j (!c))

def a24_ShBal (n : ℕ) (C : Circuit) (X Y Z a24_W : ℕ → Prop) : Prop :=
  ∃ jr b j1 c1 j2 c2, a24_AndG C jr ∧ a24_Rr n C (n + jr) C.output ∧ a24_AndG C j1 ∧
    a24_Rr n C (n + j1) (a24_inp C jr b) ∧ X (a24_inp C j1 c1) ∧ Y (a24_inp C j1 (!c1)) ∧ a24_AndG C j2 ∧
    a24_Rr n C (n + j2) (a24_inp C jr (!b)) ∧ Z (a24_inp C j2 c2) ∧ a24_W (a24_inp C j2 (!c2))

def a24_ShCat (n : ℕ) (C : Circuit) (X Y Z a24_W : ℕ → Prop) : Prop :=
  ∃ jr b j c j' c', a24_AndG C jr ∧ a24_Rr n C (n + jr) C.output ∧ X (a24_inp C jr b) ∧ a24_AndG C j ∧
    a24_Rr n C (n + j) (a24_inp C jr (!b)) ∧ Y (a24_inp C j c) ∧ a24_AndG C j' ∧
    a24_Rr n C (n + j') (a24_inp C j (!c)) ∧ Z (a24_inp C j' c') ∧ a24_W (a24_inp C j' (!c'))

def a24_Prim (n : ℕ) (C : Circuit) (X Y : ℕ → Prop) : Prop :=
  a24_Sh2 n C X Y ∨ a24_Sh3 n C X X Y ∨ a24_Sh3 n C X Y Y ∨ a24_ShBal n C X X Y Y ∨ a24_ShBal n C X Y X Y ∨
    a24_ShCat n C X X Y Y ∨ a24_ShCat n C X Y X Y

theorem a24_rootcase {n : ℕ} {C : Circuit} {wp wl : ℕ} {X Y : ℕ → Prop} (hne : wp ≠ wl) (jr : ℕ)
    (b : Bool) (hjr : a24_AndG C jr) (hout : a24_Rr n C (n + jr) C.output) (L1 L2 : List (ℕ × ℕ))
    (h1 : a24_Tt n C (a24_inp C jr b) L1) (h2 : a24_Tt n C (a24_inp C jr (!b)) L2)
    (hk1 : a24_LOK wp wl X Y L1) (hk2 : a24_LOK wp wl X Y L2)
    (hc : 1 ≤ a24_cnt wp L1 + a24_cnt wp L2 ∧ a24_cnt wp L1 + a24_cnt wp L2 ≤ 2)
    (hc' : 1 ≤ a24_cnt wl L1 + a24_cnt wl L2 ∧ a24_cnt wl L1 + a24_cnt wl L2 ≤ 2)
    (hlen : (L1.length = 1 ∧ L2.length = 1) ∨ (L1.length = 1 ∧ L2.length = 2) ∨
      (L1.length = 1 ∧ L2.length = 3) ∨ (L1.length = 2 ∧ L2.length = 2)) :
    a24_Prim n C X Y ∨ a24_Prim n C Y X := by
  rcases hlen with ⟨l1, l2⟩ | ⟨l1, l2⟩ | ⟨l1, l2⟩ | ⟨l1, l2⟩
  · rcases a24_D1 hne h1 l1 hk1 with ⟨hx, a2, a3⟩ | ⟨hx, a2, a3⟩
    · rcases a24_D1 hne h2 l2 hk2 with ⟨hy, b2, b3⟩ | ⟨hy, b2, b3⟩
      · exfalso; omega
      · exact Or.inl (Or.inl ⟨jr, b, hjr, hout, hx, hy⟩)
    · rcases a24_D1 hne h2 l2 hk2 with ⟨hy, b2, b3⟩ | ⟨hy, b2, b3⟩
      · exact Or.inr (Or.inl ⟨jr, b, hjr, hout, hx, hy⟩)
      · exfalso; omega
  · obtain ⟨j, c, hj, hRj, hkind⟩ := a24_D2 hne h2 l2 hk2
    rcases a24_D1 hne h1 l1 hk1 with ⟨hx, a2, a3⟩ | ⟨hx, a2, a3⟩
    · rcases hkind with ⟨ha, hb, b2, b3⟩ | ⟨ha, hb, b2, b3⟩ | ⟨ha, hb, b2, b3⟩
      · exfalso; omega
      · exact Or.inl (Or.inr (Or.inl ⟨jr, b, j, c, hjr, hout, hx, hj, hRj, ha, hb⟩))
      · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨jr, b, j, c, hjr, hout, hx, hj, hRj, ha, hb⟩)))
    · rcases hkind with ⟨ha, hb, b2, b3⟩ | ⟨ha, hb, b2, b3⟩ | ⟨ha, hb, b2, b3⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨jr, b, j, c, hjr, hout, hx, hj, hRj, ha, hb⟩)))
      · exact Or.inr (Or.inr (Or.inl ⟨jr, b, j, !c, hjr, hout, hx, hj, hRj, hb,
          by rw [Bool.not_not]; exact ha⟩))
      · exfalso; omega
  · obtain ⟨j, c, L3, L4, hj, hRj, h3, h4, l3, l4, hk3, hk4, e1, e2⟩ := a24_D3 h2 l2 hk2
    obtain ⟨j', c', hj', hRj', hkind⟩ := a24_D2 hne h4 l4 hk4
    rcases a24_D1 hne h1 l1 hk1 with ⟨hx, a2, a3⟩ | ⟨hx, a2, a3⟩
    · rcases a24_D1 hne h3 l3 hk3 with ⟨hy, d2, d3⟩ | ⟨hy, d2, d3⟩
      · rcases hkind with ⟨ha, hb, b2, b3⟩ | ⟨ha, hb, b2, b3⟩ | ⟨ha, hb, b2, b3⟩
        · exfalso; omega
        · exfalso; omega
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨jr, b, j, c, j', c', hjr, hout, hx, hj, hRj, hy, hj', hRj', ha, hb⟩))))))
      · rcases hkind with ⟨ha, hb, b2, b3⟩ | ⟨ha, hb, b2, b3⟩ | ⟨ha, hb, b2, b3⟩
        · exfalso; omega
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨jr, b, j, c, j', c', hjr, hout, hx, hj, hRj, hy, hj', hRj', ha, hb⟩))))))
        · exfalso; omega
    · rcases a24_D1 hne h3 l3 hk3 with ⟨hy, d2, d3⟩ | ⟨hy, d2, d3⟩
      · rcases hkind with ⟨ha, hb, b2, b3⟩ | ⟨ha, hb, b2, b3⟩ | ⟨ha, hb, b2, b3⟩
        · exfalso; omega
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨jr, b, j, c, j', !c', hjr, hout, hx, hj, hRj, hy, hj', hRj', hb,
              by rw [Bool.not_not]; exact ha⟩))))))
        · exfalso; omega
      · rcases hkind with ⟨ha, hb, b2, b3⟩ | ⟨ha, hb, b2, b3⟩ | ⟨ha, hb, b2, b3⟩
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨jr, b, j, c, j', c', hjr, hout, hx, hj, hRj, hy, hj', hRj', ha, hb⟩))))))
        · exfalso; omega
        · exfalso; omega
  · obtain ⟨j1, c1, hj1, hRj1, hkind1⟩ := a24_D2 hne h1 l1 hk1
    obtain ⟨j2, c2, hj2, hRj2, hkind2⟩ := a24_D2 hne h2 l2 hk2
    rcases hkind1 with ⟨ha, hb, a2, a3⟩ | ⟨ha, hb, a2, a3⟩ | ⟨ha, hb, a2, a3⟩
    · rcases hkind2 with ⟨hc1, hd, b2, b3⟩ | ⟨hc1, hd, b2, b3⟩ | ⟨hc1, hd, b2, b3⟩
      · exfalso; omega
      · exfalso; omega
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨jr, b, j1, c1, j2, c2, hjr, hout, hj1, hRj1, ha, hb, hj2, hRj2, hc1, hd⟩))))
    · rcases hkind2 with ⟨hc1, hd, b2, b3⟩ | ⟨hc1, hd, b2, b3⟩ | ⟨hc1, hd, b2, b3⟩
      · exfalso; omega
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨jr, b, j1, c1, j2, c2, hjr, hout, hj1, hRj1, ha, hb, hj2, hRj2, hc1, hd⟩)))))
      · exfalso; omega
    · rcases hkind2 with ⟨hc1, hd, b2, b3⟩ | ⟨hc1, hd, b2, b3⟩ | ⟨hc1, hd, b2, b3⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨jr, b, j1, c1, j2, c2, hjr, hout, hj1, hRj1, ha, hb, hj2, hRj2, hc1, hd⟩))))
      · exfalso; omega
      · exfalso; omega

theorem a24_prim_of_tree {n : ℕ} {C : Circuit} {wp wl : ℕ} {X Y : ℕ → Prop} (hne : wp ≠ wl) (jr : ℕ)
    (hjr : a24_AndG C jr) (hout : a24_Rr n C (n + jr) C.output) (La a24_Lb : List (ℕ × ℕ))
    (h1 : a24_Tt n C (a24_inp C jr false) La) (h2 : a24_Tt n C (a24_inp C jr true) a24_Lb)
    (hk : a24_LOK wp wl X Y (La ++ a24_Lb))
    (hc : a24_cnt wp (La ++ a24_Lb) = 1 ∨ a24_cnt wp (La ++ a24_Lb) = 2)
    (hc' : a24_cnt wl (La ++ a24_Lb) = 1 ∨ a24_cnt wl (La ++ a24_Lb) = 2) :
    a24_Prim n C X Y ∨ a24_Prim n C Y X := by
  have p1 := a24_Tt_pos h1
  have p2 := a24_Tt_pos h2
  have e1 := a24_cnt_append wp La a24_Lb
  have e2 := a24_cnt_append wl La a24_Lb
  have e3 := a24_cnt_total hne (La ++ a24_Lb) hk
  rw [List.length_append] at e3
  have hcases : (La.length = 1 ∧ a24_Lb.length = 1) ∨ (La.length = 1 ∧ a24_Lb.length = 2) ∨
      (La.length = 1 ∧ a24_Lb.length = 3) ∨ (La.length = 2 ∧ a24_Lb.length = 2) ∨
      (a24_Lb.length = 1 ∧ La.length = 2) ∨ (a24_Lb.length = 1 ∧ La.length = 3) := by omega
  rcases hcases with h | h | h | h | h | h
  · exact a24_rootcase hne jr false hjr hout La a24_Lb h1 h2 (a24_LOK_left hk) (a24_LOK_right hk)
      (by omega) (by omega) (Or.inl h)
  · exact a24_rootcase hne jr false hjr hout La a24_Lb h1 h2 (a24_LOK_left hk) (a24_LOK_right hk)
      (by omega) (by omega) (Or.inr (Or.inl h))
  · exact a24_rootcase hne jr false hjr hout La a24_Lb h1 h2 (a24_LOK_left hk) (a24_LOK_right hk)
      (by omega) (by omega) (Or.inr (Or.inr (Or.inl h)))
  · exact a24_rootcase hne jr false hjr hout La a24_Lb h1 h2 (a24_LOK_left hk) (a24_LOK_right hk)
      (by omega) (by omega) (Or.inr (Or.inr (Or.inr h)))
  · exact a24_rootcase hne jr true hjr hout a24_Lb La h2 h1 (a24_LOK_right hk) (a24_LOK_left hk)
      (by omega) (by omega) (Or.inr (Or.inl h))
  · exact a24_rootcase hne jr true hjr hout a24_Lb La h2 h1 (a24_LOK_right hk) (a24_LOK_left hk)
      (by omega) (by omega) (Or.inr (Or.inr (Or.inl h)))

-- fragment f05_sys
def a24_Sys (n : ℕ) (C : Circuit) (N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) : Prop :=
  PEqualNP.TopForm.IsAO2 n C ∧ Function.Injective pw ∧ Function.Injective lw ∧
  (∀ p, pw p < n) ∧ (∀ l, lw l < n) ∧ a24_No4 I ∧
  (∀ P Y x, x ∈ P → Tr P Y (pw x)) ∧ (∀ P Y y, y ∈ Y → Tr P Y (lw y)) ∧
  (∀ P Y a b, a24_Rr n C a b → Tr P Y a → Tr P Y b) ∧
  (∀ P Y j, a24_AndG C j → Tr P Y (a24_inp C j false) → Tr P Y (a24_inp C j true) → Tr P Y (n + j)) ∧
  (∀ P Y, P.card ≤ 2 → Y.card ≤ 2 → Tr P Y C.output → ∃ x ∈ P, ∃ y ∈ Y, I x y)

theorem a24_Sys_swap {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : a24_Sys n C N M pw lw I Tr) :
    a24_Sys n C M N lw pw (fun y x => I x y) (fun Y P w => Tr P Y w) := by
  obtain ⟨hC, hpw, hlw, hpn, hln, h4, htp, htl, htR, htA, hsnd⟩ := id hS
  refine ⟨hC, hlw, hpw, hln, hpn, a24_No4_swap h4, fun Y P y hy => htl P Y y hy,
    fun Y P x hx => htp P Y x hx, fun Y P a b h => htR P Y a b h,
    fun Y P j hj => htA P Y j hj, ?_⟩
  intro Y P hY hP h
  obtain ⟨x, hx, y, hy, hI⟩ := hsnd P Y hP hY h
  exact ⟨y, hy, x, hx, hI⟩

theorem a24_tr_p {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : a24_Sys n C N M pw lw I Tr) {P : Finset (Fin N)} {Y : Finset (Fin M)} {x : Fin N} {w : ℕ}
    (hx : x ∈ P) (h : a24_Rr n C (pw x) w) : Tr P Y w := by
  obtain ⟨hC, hpw, hlw, hpn, hln, h4, htp, htl, htR, htA, hsnd⟩ := id hS
  exact htR P Y _ _ h (htp P Y x hx)

theorem a24_tr_l {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : a24_Sys n C N M pw lw I Tr) {P : Finset (Fin N)} {Y : Finset (Fin M)} {y : Fin M} {w : ℕ}
    (hy : y ∈ Y) (h : a24_Rr n C (lw y) w) : Tr P Y w := by
  obtain ⟨hC, hpw, hlw, hpn, hln, h4, htp, htl, htR, htA, hsnd⟩ := id hS
  exact htR P Y _ _ h (htl P Y y hy)

theorem a24_tr_R {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : a24_Sys n C N M pw lw I Tr) {P : Finset (Fin N)} {Y : Finset (Fin M)} {a b : ℕ}
    (h : a24_Rr n C a b) (ha : Tr P Y a) : Tr P Y b := by
  obtain ⟨hC, hpw, hlw, hpn, hln, h4, htp, htl, htR, htA, hsnd⟩ := id hS
  exact htR P Y _ _ h ha

theorem a24_tr_and {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : a24_Sys n C N M pw lw I Tr) {P : Finset (Fin N)} {Y : Finset (Fin M)} {j : ℕ} (hj : a24_AndG C j)
    (c : Bool) (h1 : Tr P Y (a24_inp C j c)) (h2 : Tr P Y (a24_inp C j (!c))) : Tr P Y (n + j) := by
  obtain ⟨hC, hpw, hlw, hpn, hln, h4, htp, htl, htR, htA, hsnd⟩ := id hS
  cases c
  · exact htA P Y j hj h1 h2
  · exact htA P Y j hj h2 h1

theorem a24_snd22 {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : a24_Sys n C N M pw lw I Tr) {x z : Fin N} {y t : Fin M} (h : Tr {x, z} {y, t} C.output) :
    I x y ∨ I x t ∨ I z y ∨ I z t := by
  obtain ⟨hC, hpw, hlw, hpn, hln, h4, htp, htl, htR, htA, hsnd⟩ := id hS
  obtain ⟨x', hx', y', hy', hI⟩ := hsnd {x, z} {y, t} Finset.card_le_two Finset.card_le_two h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx' hy'
  rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl <;> tauto

theorem a24_snd21 {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : a24_Sys n C N M pw lw I Tr) {x z : Fin N} {y : Fin M} (h : Tr {x, z} {y} C.output) :
    I x y ∨ I z y := by
  obtain ⟨hC, hpw, hlw, hpn, hln, h4, htp, htl, htR, htA, hsnd⟩ := id hS
  obtain ⟨x', hx', y', hy', hI⟩ := hsnd {x, z} {y} Finset.card_le_two (by simp) h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx' hy'
  rcases hx' with rfl | rfl <;> rcases hy' with rfl <;> tauto

theorem a24_snd12 {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : a24_Sys n C N M pw lw I Tr) {x : Fin N} {y t : Fin M} (h : Tr {x} {y, t} C.output) :
    I x y ∨ I x t := by
  obtain ⟨hC, hpw, hlw, hpn, hln, h4, htp, htl, htR, htA, hsnd⟩ := id hS
  obtain ⟨x', hx', y', hy', hI⟩ := hsnd {x} {y, t} (by simp) Finset.card_le_two h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx' hy'
  rcases hx' with rfl <;> rcases hy' with rfl | rfl <;> tauto

theorem a24_snd11 {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : a24_Sys n C N M pw lw I Tr) {x : Fin N} {y : Fin M} (h : Tr {x} {y} C.output) : I x y := by
  obtain ⟨hC, hpw, hlw, hpn, hln, h4, htp, htl, htR, htA, hsnd⟩ := id hS
  obtain ⟨x', hx', y', hy', hI⟩ := hsnd {x} {y} (by simp) (by simp) h
  simp only [Finset.mem_singleton] at hx' hy'
  rw [hx', hy'] at hI
  exact hI

noncomputable def a24_andS (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter (fun j => (gateAt C j).op = GateOp.and)

noncomputable def a24_orS (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter (fun j => (gateAt C j).op = GateOp.or)

theorem a24_mem_andS {C : Circuit} {j : ℕ} : j ∈ a24_andS C ↔ a24_AndG C j := by
  unfold a24_andS a24_AndG
  simp only [Finset.mem_filter, Finset.mem_range]

theorem a24_mem_orS {C : Circuit} {j : ℕ} : j ∈ a24_orS C ↔ a24_OrG C j := by
  unfold a24_orS a24_OrG
  simp only [Finset.mem_filter, Finset.mem_range]

theorem a24_and_or_card {n : ℕ} {C : Circuit} (hC : PEqualNP.TopForm.IsAO2 n C) :
    (a24_andS C).card + (a24_orS C).card = C.gates.length := by
  classical
  have hd : Disjoint (a24_andS C) (a24_orS C) := by
    rw [Finset.disjoint_left]
    intro j h1 h2
    have a1 := (a24_mem_andS.mp h1).2
    have a2 := (a24_mem_orS.mp h2).2
    rw [a1] at a2
    exact GateOp.noConfusion a2
  have hu : a24_andS C ∪ a24_orS C = Finset.range C.gates.length := by
    ext j
    rw [Finset.mem_union, a24_mem_andS, a24_mem_orS, Finset.mem_range]
    constructor
    · rintro (h | h)
      · exact h.1
      · exact h.1
    · intro hj
      rcases hC.1 _ (a24_gateAt_mem C j hj) with h | h
      · exact Or.inl ⟨hj, h⟩
      · exact Or.inr ⟨hj, h⟩
  have h := Finset.card_union_of_disjoint hd
  rw [hu, Finset.card_range] at h
  omega

noncomputable def a24_KA (C : Circuit) : Finset (ℕ × Bool) := (a24_andS C) ×ˢ (Finset.univ : Finset Bool)

noncomputable def a24_KO (C : Circuit) : Finset (ℕ × Bool) := (a24_orS C) ×ˢ (Finset.univ : Finset Bool)

theorem a24_mem_KA {C : Circuit} {key : ℕ × Bool} : key ∈ a24_KA C ↔ a24_AndG C key.1 := by
  unfold a24_KA
  rw [Finset.mem_product, a24_mem_andS]
  simp

theorem a24_mem_KO {C : Circuit} {key : ℕ × Bool} : key ∈ a24_KO C ↔ a24_OrG C key.1 := by
  unfold a24_KO
  rw [Finset.mem_product, a24_mem_orS]
  simp

theorem a24_card_KA (C : Circuit) : (a24_KA C).card = 2 * (a24_andS C).card := by
  unfold a24_KA
  rw [Finset.card_product]
  simp
  omega

theorem a24_card_KO (C : Circuit) : (a24_KO C).card = 2 * (a24_orS C).card := by
  unfold a24_KO
  rw [Finset.card_product]
  simp
  omega

def a24_PPr (n : ℕ) (C : Circuit) {K : ℕ} (xw : Fin K → ℕ) (a : ℕ) (x : Fin K) : Prop :=
  a24_Rr n C (xw x) a ∧ ∀ x', a24_Rr n C (xw x') a → x' = x

def a24_GPf (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (I : Fin N → Fin M → Prop)
    (p : Fin N) (l : Fin M) (w : ℕ) : Prop :=
  a24_Rr n C (pw p) w ∧ ((∀ x, a24_Rr n C (pw x) w → x = p) ∨ ∃ q, a24_Rr n C (pw q) w ∧ ¬ I q l)

def a24_GLf (n : ℕ) (C : Circuit) {N M : ℕ} (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop)
    (p : Fin N) (l : Fin M) (w : ℕ) : Prop :=
  a24_Rr n C (lw l) w ∧ ((∀ y, a24_Rr n C (lw y) w → y = l) ∨ ∃ y, a24_Rr n C (lw y) w ∧ ¬ I p y)

def a24_Junk (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (j : ℕ) (x : Fin N) (t : Fin M) : Prop :=
  a24_AndG C j ∧ ∃ c, a24_Rr n C (pw x) (a24_inp C j c) ∧ a24_Rr n C (lw t) (a24_inp C j (!c)) ∧ ¬ I x t

def a24_phi2 (n : ℕ) (C : Circuit) {K : ℕ} (xw : Fin K → ℕ) (j : ℕ) (x : Fin K) : Prop :=
  a24_AndG C j ∧ a24_Rr n C (xw x) (a24_inp C j false) ∧ a24_Rr n C (xw x) (a24_inp C j true)

def a24_phiS (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (j : ℕ) (x : Fin N) : Prop :=
  ∃ t, a24_Junk n C pw lw I j x t

def a24_phiB (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (j : ℕ) (y : Fin M) : Prop :=
  ∃ z, a24_Junk n C pw lw I j z y

theorem a24_junk_tr {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : a24_Sys n C N M pw lw I Tr) {P : Finset (Fin N)} {Y : Finset (Fin M)} {j : ℕ} {x : Fin N} {t : Fin M}
    (h : a24_Junk n C pw lw I j x t) (hx : x ∈ P) (ht : t ∈ Y) : Tr P Y (n + j) := by
  obtain ⟨hj, c, h1, h2, _⟩ := h
  exact a24_tr_and hS hj c (a24_tr_p hS hx h1) (a24_tr_l hS ht h2)

theorem a24_phi2p_tr {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : a24_Sys n C N M pw lw I Tr) {P : Finset (Fin N)} {Y : Finset (Fin M)} {j : ℕ} {x : Fin N}
    (h : a24_phi2 n C pw j x) (hx : x ∈ P) : Tr P Y (n + j) := by
  obtain ⟨hj, h1, h2⟩ := h
  exact a24_tr_and hS hj false (a24_tr_p hS hx h1) (a24_tr_p hS hx h2)

theorem a24_phi2l_tr {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : a24_Sys n C N M pw lw I Tr) {P : Finset (Fin N)} {Y : Finset (Fin M)} {j : ℕ} {y : Fin M}
    (h : a24_phi2 n C lw j y) (hy : y ∈ Y) : Tr P Y (n + j) := by
  obtain ⟨hj, h1, h2⟩ := h
  exact a24_tr_and hS hj false (a24_tr_l hS hy h1) (a24_tr_l hS hy h2)

def a24_QU {N M : ℕ} (K : Finset (ℕ × Bool)) (PA : ℕ × Bool → Fin N → Prop)
    (PB : ℕ × Bool → Fin M → Prop) (e : Fin N × Fin M) : Prop :=
  ∃ key ∈ K, a24_ChU (PA key) (PB key) e.1 e.2

theorem a24_bd_QU {N M : ℕ} (K : Finset (ℕ × Bool)) (PA : ℕ × Bool → Fin N → Prop)
    (PB : ℕ × Bool → Fin M → Prop) : a24_Bd (a24_QU K PA PB) K.card := by
  have h := a24_Bd_charge K (fun key (e : Fin N × Fin M) => a24_ChU (PA key) (PB key) e.1 e.2) 1
    (fun key _ => a24_Bd_U _ _)
  rw [one_mul] at h
  exact h

def a24_QM {N M : ℕ} (I : Fin N → Fin M → Prop) (K : Finset (ℕ × Bool))
    (L0 L1 : ℕ × Bool → Fin M → Prop) (e : Fin N × Fin M) : Prop :=
  ∃ key ∈ K, a24_ChM I (L0 key) (L1 key) e.1 e.2

theorem a24_bd_QM {N M : ℕ} {I : Fin N → Fin M → Prop} (h4 : a24_No4 I) (K : Finset (ℕ × Bool))
    (L0 L1 : ℕ × Bool → Fin M → Prop) : a24_Bd (a24_QM I K L0 L1) K.card := by
  have h := a24_Bd_charge K (fun key (e : Fin N × Fin M) => a24_ChM I (L0 key) (L1 key) e.1 e.2) 1
    (fun key _ => a24_Bd_M Prod.fst Prod.snd (fun e e' h1 h2 => Prod.ext h1 h2) I h4 _ _)
  rw [one_mul] at h
  exact h

def a24_QMP {N M : ℕ} (I : Fin N → Fin M → Prop) (K : Finset (ℕ × Bool))
    (L0 L1 : ℕ × Bool → Fin N → Prop) (e : Fin N × Fin M) : Prop :=
  ∃ key ∈ K, a24_ChM (fun (l : Fin M) (p : Fin N) => I p l) (L0 key) (L1 key) e.2 e.1

theorem a24_bd_QMP {N M : ℕ} {I : Fin N → Fin M → Prop} (h4 : a24_No4 I) (K : Finset (ℕ × Bool))
    (L0 L1 : ℕ × Bool → Fin N → Prop) : a24_Bd (a24_QMP I K L0 L1) K.card := by
  have h := a24_Bd_charge K (fun key (e : Fin N × Fin M) =>
      a24_ChM (fun (l : Fin M) (p : Fin N) => I p l) (L0 key) (L1 key) e.2 e.1) 1
    (fun key _ => a24_Bd_M Prod.snd Prod.fst (fun e e' h1 h2 => Prod.ext h2 h1) _ (a24_No4_swap h4) _ _)
  rw [one_mul] at h
  exact h

def a24_QF (n : ℕ) (C : Circuit) {N M : ℕ} (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop)
    (e : Fin N × Fin M) : Prop :=
  ∃ key ∈ a24_KO C, a24_ChF3 n C lw I key e.1 e.2

theorem a24_bd_QF (n : ℕ) (C : Circuit) {N M : ℕ} (lw : Fin M → ℕ) {I : Fin N → Fin M → Prop}
    (h4 : a24_No4 I) : a24_Bd (a24_QF n C lw I) (4 * (a24_KO C).card) :=
  a24_Bd_charge (a24_KO C) (fun key (e : Fin N × Fin M) => a24_ChF3 n C lw I key e.1 e.2) 4
    (fun key _ => a24_F3_fiber Prod.fst Prod.snd (fun e e' h1 h2 => Prod.ext h1 h2) lw I h4 key)

def a24_QFP (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (I : Fin N → Fin M → Prop)
    (e : Fin N × Fin M) : Prop :=
  ∃ key ∈ a24_KO C, a24_ChF3 n C pw (fun (l : Fin M) (p : Fin N) => I p l) key e.2 e.1

theorem a24_bd_QFP (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) {I : Fin N → Fin M → Prop}
    (h4 : a24_No4 I) : a24_Bd (a24_QFP n C pw I) (4 * (a24_KO C).card) :=
  a24_Bd_charge (a24_KO C) (fun key (e : Fin N × Fin M) =>
      a24_ChF3 n C pw (fun (l : Fin M) (p : Fin N) => I p l) key e.2 e.1) 4
    (fun key _ => a24_F3_fiber Prod.snd Prod.fst (fun e e' h1 h2 => Prod.ext h2 h1) pw _
      (a24_No4_swap h4) key)

theorem a24_fm_line {n : ℕ} {C : Circuit} (hC : PEqualNP.TopForm.IsAO2 n C) {N M : ℕ}
    {I : Fin N → Fin M → Prop} (φ : ℕ → Fin M → Prop) (p : Fin N) (l : Fin M) (j0 w : ℕ)
    (hR : a24_Rr n C (n + j0) w) (h0 : φ j0 l) (hrig : ∀ y, a24_Lb n C φ w y → I p y) :
    (∀ y, a24_Lb n C φ w y → y = l) ∨ (∃ y, a24_Lb n C φ (n + j0) y ∧ y ≠ l) ∨
    a24_QM I (a24_KO C) (fun key y => a24_Lb n C φ (a24_inp C key.1 key.2) y)
      (fun key y => a24_Lb n C φ (n + key.1) y) (p, l) := by
  rcases a24_FM3 hC φ (n + j0) w hR l with h | h | ⟨jo, b, hjo, h3, h4, h5, y, hy, hne⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr ⟨(jo, b), a24_mem_KO.mpr hjo, a24_Lb_mono h4 (a24_Lb_self h0), h5,
      a24_Lb_mono (a24_Rr_trans h4 (a24_Rr_inp hC jo hjo b)) (a24_Lb_self h0), ⟨y, hy, hne⟩,
      fun y' hy' => hrig y' (a24_Lb_mono h3 hy')⟩)

theorem a24_fm_pt {n : ℕ} {C : Circuit} (hC : PEqualNP.TopForm.IsAO2 n C) {N M : ℕ}
    {I : Fin N → Fin M → Prop} (ψ : ℕ → Fin N → Prop) (p : Fin N) (l : Fin M) (j0 w : ℕ)
    (hR : a24_Rr n C (n + j0) w) (h0 : ψ j0 p) (hrig : ∀ x, a24_Lb n C ψ w x → I x l) :
    (∀ x, a24_Lb n C ψ w x → x = p) ∨ (∃ x, a24_Lb n C ψ (n + j0) x ∧ x ≠ p) ∨
    a24_QMP I (a24_KO C) (fun key x => a24_Lb n C ψ (a24_inp C key.1 key.2) x)
      (fun key x => a24_Lb n C ψ (n + key.1) x) (p, l) := by
  rcases a24_FM3 hC ψ (n + j0) w hR p with h | h | ⟨jo, b, hjo, h3, h4, h5, y, hy, hne⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr ⟨(jo, b), a24_mem_KO.mpr hjo, a24_Lb_mono h4 (a24_Lb_self h0), h5,
      a24_Lb_mono (a24_Rr_trans h4 (a24_Rr_inp hC jo hjo b)) (a24_Lb_self h0), ⟨y, hy, hne⟩,
      fun y' hy' => hrig y' (a24_Lb_mono h3 hy')⟩)

-- fragment f06_cover
def a24_Acc (C : Circuit) {N M : ℕ} (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (p : Fin N)
    (m : ℕ) : Prop :=
  ∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), p ∈ P → Tr P Y m → Tr P Y C.output

def a24_DT (n : ℕ) {N M : ℕ} (I : Fin N → Fin M → Prop)
    (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (j : ℕ) (y : Fin M) : Prop :=
  ∀ p' : Fin N, ¬ I p' y → ∃ P : Finset (Fin N), P.card ≤ 1 ∧ (∀ x ∈ P, ¬ I x y) ∧
    Tr (insert p' P) {y} (n + j)

def a24_D0 (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (p : Fin N)
    (l : Fin M) : Prop :=
  ∃ j b, a24_AndG C j ∧ a24_PPr n C pw (a24_inp C j b) p ∧ a24_PPr n C lw (a24_inp C j (!b)) l

def a24_C15 (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (p : Fin N)
    (l : Fin M) : Prop :=
  ∃ rd b β, a24_AndG C rd ∧ a24_PPr n C pw (a24_inp C rd b) p ∧ a24_Acc C Tr p (a24_inp C rd (!b)) ∧ a24_AndG C β ∧
    a24_Rr n C (n + β) (a24_inp C rd (!b)) ∧ (∃ c, a24_PPr n C lw (a24_inp C β c) l) ∧ a24_DT n I Tr β l

def a24_C14 (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (p : Fin N) (l : Fin M) : Prop :=
  ∃ jr b j c j' c', a24_AndG C jr ∧ a24_Rr n C (n + jr) C.output ∧ a24_PPr n C pw (a24_inp C jr b) p ∧
    a24_AndG C j ∧ a24_Rr n C (n + j) (a24_inp C jr (!b)) ∧ a24_Rr n C (pw p) (a24_inp C j c) ∧
    (∃ q, a24_Rr n C (pw q) (a24_inp C j c) ∧ ¬ I q l) ∧ a24_AndG C j' ∧ a24_Rr n C (n + j') (a24_inp C j (!c)) ∧
    a24_PPr n C lw (a24_inp C j' c') l ∧ a24_Rr n C (lw l) (a24_inp C j' (!c'))

def a24_C1 (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (p : Fin N)
    (l : Fin M) : Prop :=
  ∃ g bg α bα β bβ, a24_AndG C g ∧ a24_Rr n C (n + g) C.output ∧ a24_AndG C α ∧
    a24_Rr n C (n + α) (a24_inp C g bg) ∧ a24_PPr n C pw (a24_inp C α bα) p ∧ a24_Rr n C (pw p) (a24_inp C α (!bα)) ∧
    a24_AndG C β ∧ a24_Rr n C (n + β) (a24_inp C g (!bg)) ∧ a24_PPr n C lw (a24_inp C β bβ) l ∧
    a24_Rr n C (lw l) (a24_inp C β (!bβ))

def a24_C2h (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (p : Fin N) (l : Fin M) : Prop :=
  ∃ g bg α bα β bβ, a24_AndG C g ∧ a24_Rr n C (n + g) C.output ∧ a24_AndG C α ∧
    a24_Rr n C (n + α) (a24_inp C g bg) ∧ a24_PPr n C pw (a24_inp C α bα) p ∧ a24_Rr n C (lw l) (a24_inp C α (!bα)) ∧
    (∃ y, a24_Rr n C (lw y) (a24_inp C α (!bα)) ∧ ¬ I p y) ∧
    a24_AndG C β ∧ a24_Rr n C (n + β) (a24_inp C g (!bg)) ∧ a24_PPr n C lw (a24_inp C β bβ) l ∧
    a24_Rr n C (pw p) (a24_inp C β (!bβ)) ∧ (∃ q, a24_Rr n C (pw q) (a24_inp C β (!bβ)) ∧ ¬ I q l)

def a24_C4a (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (p : Fin N) (l : Fin M) : Prop :=
  ∃ ρ bρ β bβ α bα, a24_AndG C ρ ∧ a24_Rr n C (n + ρ) C.output ∧ a24_Rr n C (pw p) (a24_inp C ρ bρ) ∧
    a24_AndG C β ∧ a24_Rr n C (n + β) (a24_inp C ρ (!bρ)) ∧ a24_PPr n C lw (a24_inp C β bβ) l ∧
    a24_AndG C α ∧ a24_Rr n C (n + α) (a24_inp C β (!bβ)) ∧ a24_PPr n C pw (a24_inp C α bα) p ∧
    a24_Rr n C (lw l) (a24_inp C α (!bα)) ∧ ∃ y, a24_Rr n C (lw y) (a24_inp C α (!bα)) ∧ ¬ I p y

def a24_C4b (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (p : Fin N) (l : Fin M) : Prop :=
  ∃ ρ bρ s bs β bβ, a24_AndG C ρ ∧ a24_Rr n C (n + ρ) C.output ∧ a24_PPr n C pw (a24_inp C ρ bρ) p ∧
    a24_AndG C s ∧ a24_Rr n C (n + s) (a24_inp C ρ (!bρ)) ∧ a24_Rr n C (lw l) (a24_inp C s bs) ∧
    a24_AndG C β ∧ a24_Rr n C (n + β) (a24_inp C s (!bs)) ∧ a24_PPr n C lw (a24_inp C β bβ) l ∧
    a24_Rr n C (pw p) (a24_inp C β (!bβ)) ∧ ∃ q, a24_Rr n C (pw q) (a24_inp C β (!bβ)) ∧ ¬ I q l

def a24_HalfC (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (p : Fin N)
    (l : Fin M) : Prop :=
  a24_D0 n C pw lw p l ∨ a24_C15 n C pw lw I Tr p l ∨ a24_C14 n C pw lw I p l ∨ a24_C1 n C pw lw p l ∨
    a24_C2h n C pw lw I p l ∨ a24_C4a n C pw lw I p l ∨ a24_C4b n C pw lw I p l

theorem a24_cov_A {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : a24_Sys n C N M pw lw I Tr) (p : Fin N) (l : Fin M)
    (h : a24_Sh2 n C (a24_GPf n C pw I p l) (a24_GLf n C lw I p l)) : a24_D0 n C pw lw p l := by
  obtain ⟨jr, b, hjr, hout, ⟨hx, hxk⟩, ⟨hy, hyk⟩⟩ := h
  have htrue : ∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), Tr P Y (a24_inp C jr b) →
      Tr P Y (a24_inp C jr (!b)) → Tr P Y C.output :=
    fun P Y h1 h2 => a24_tr_R hS hout (a24_tr_and hS hjr b h1 h2)
  have px : ∀ x', a24_Rr n C (pw x') (a24_inp C jr b) → x' = p := by
    rcases hxk with h | ⟨q, hq, hnq⟩
    · exact h
    · exfalso
      exact hnq (a24_snd11 hS (htrue {q} {l} (a24_tr_p hS (by simp) hq) (a24_tr_l hS (by simp) hy)))
  have py : ∀ y', a24_Rr n C (lw y') (a24_inp C jr (!b)) → y' = l := by
    rcases hyk with h | ⟨y', hy', hn⟩
    · exact h
    · exfalso
      exact hn (a24_snd11 hS (htrue {p} {y'} (a24_tr_p hS (by simp) hx) (a24_tr_l hS (by simp) hy')))
  exact ⟨jr, b, hjr, ⟨hx, px⟩, ⟨hy, py⟩⟩

theorem a24_cov_B1 {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : a24_Sys n C N M pw lw I Tr) (p : Fin N) (l : Fin M)
    (h : a24_Sh3 n C (a24_GPf n C pw I p l) (a24_GPf n C pw I p l) (a24_GLf n C lw I p l)) :
    a24_D0 n C pw lw p l ∨ a24_C15 n C pw lw I Tr p l := by
  obtain ⟨jr, b, j, c, hjr, hout, ⟨hx, hxk⟩, hj, hRj, ⟨ha, hak⟩, ⟨hb, hbk⟩⟩ := h
  have htrue : ∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), Tr P Y (a24_inp C jr b) →
      Tr P Y (a24_inp C j c) → Tr P Y (a24_inp C j (!c)) → Tr P Y C.output :=
    fun P Y h1 h2 h3 => a24_tr_R hS hout (a24_tr_and hS hjr b h1 (a24_tr_R hS hRj (a24_tr_and hS hj c h2 h3)))
  have hbu : ∀ y', a24_Rr n C (lw y') (a24_inp C j (!c)) → y' = l := by
    rcases hbk with h | ⟨y', hy', hn⟩
    · exact h
    · exfalso
      exact hn (a24_snd11 hS (htrue {p} {y'} (a24_tr_p hS (by simp) hx) (a24_tr_p hS (by simp) ha)
        (a24_tr_l hS (by simp) hy')))
  rcases hak with hau | ⟨q, hq, hnq⟩
  · exact Or.inl ⟨j, c, hj, ⟨ha, hau⟩, ⟨hb, hbu⟩⟩
  · have hxu : ∀ x', a24_Rr n C (pw x') (a24_inp C jr b) → x' = p := by
      rcases hxk with h | ⟨q', hq', hnq'⟩
      · exact h
      · exfalso
        rcases a24_snd21 hS (htrue {q', q} {l} (a24_tr_p hS (by simp) hq') (a24_tr_p hS (by simp) hq)
          (a24_tr_l hS (by simp) hb)) with h | h
        · exact hnq' h
        · exact hnq h
    refine Or.inr ⟨jr, b, j, hjr, ⟨hx, hxu⟩, ?_, hj, hRj, ⟨!c, hb, hbu⟩, ?_⟩
    · intro P Y hp hm
      exact a24_tr_R hS hout (a24_tr_and hS hjr b (a24_tr_p hS hp hx) hm)
    · intro p' _
      refine ⟨{q}, by simp, ?_, a24_tr_and hS hj c (a24_tr_p hS (by simp) hq) (a24_tr_l hS (by simp) hb)⟩
      intro x hx'
      rw [Finset.mem_singleton.mp hx']
      exact hnq

theorem a24_cov_B2 {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : a24_Sys n C N M pw lw I Tr) (p : Fin N) (l : Fin M)
    (h : a24_Sh3 n C (a24_GPf n C pw I p l) (a24_GLf n C lw I p l) (a24_GLf n C lw I p l)) :
    a24_C15 n C pw lw I Tr p l := by
  obtain ⟨jr, b, j, c, hjr, hout, ⟨hx, hxk⟩, hj, hRj, ⟨ha, hak⟩, ⟨hb, hbk⟩⟩ := h
  have htrue : ∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), Tr P Y (a24_inp C jr b) →
      Tr P Y (a24_inp C j c) → Tr P Y (a24_inp C j (!c)) → Tr P Y C.output :=
    fun P Y h1 h2 h3 => a24_tr_R hS hout (a24_tr_and hS hjr b h1 (a24_tr_R hS hRj (a24_tr_and hS hj c h2 h3)))
  have hxu : ∀ x', a24_Rr n C (pw x') (a24_inp C jr b) → x' = p := by
    rcases hxk with h | ⟨q, hq, hnq⟩
    · exact h
    · exfalso
      exact hnq (a24_snd11 hS (htrue {q} {l} (a24_tr_p hS (by simp) hq) (a24_tr_l hS (by simp) ha)
        (a24_tr_l hS (by simp) hb)))
  have hacc : a24_Acc C Tr p (a24_inp C jr (!b)) := by
    intro P Y hp hm
    exact a24_tr_R hS hout (a24_tr_and hS hjr b (a24_tr_p hS hp hx) hm)
  have hdt : a24_DT n I Tr j l := by
    intro p' _
    exact ⟨∅, by simp, by simp, a24_tr_and hS hj c (a24_tr_l hS (by simp) ha) (a24_tr_l hS (by simp) hb)⟩
  rcases hak with hau | ⟨y1, h1, n1⟩
  · exact ⟨jr, b, j, hjr, ⟨hx, hxu⟩, hacc, hj, hRj, ⟨c, ha, hau⟩, hdt⟩
  · rcases hbk with hbu | ⟨y2, h2, n2⟩
    · exact ⟨jr, b, j, hjr, ⟨hx, hxu⟩, hacc, hj, hRj, ⟨!c, hb, hbu⟩, hdt⟩
    · exfalso
      rcases a24_snd12 hS (htrue {p} {y1, y2} (a24_tr_p hS (by simp) hx) (a24_tr_l hS (by simp) h1)
        (a24_tr_l hS (by simp) h2)) with h | h
      · exact n1 h
      · exact n2 h

theorem a24_cov_C1 {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : a24_Sys n C N M pw lw I Tr) (p : Fin N) (l : Fin M)
    (h : a24_ShBal n C (a24_GPf n C pw I p l) (a24_GPf n C pw I p l) (a24_GLf n C lw I p l) (a24_GLf n C lw I p l)) :
    a24_C1 n C pw lw p l := by
  obtain ⟨jr, b, j1, c1, j2, c2, hjr, hout, hj1, hR1, ⟨ha, hak⟩, ⟨hb, hbk⟩, hj2, hR2,
    ⟨hc, hck⟩, ⟨hd, hdk⟩⟩ := h
  have htrue : ∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), Tr P Y (a24_inp C j1 c1) →
      Tr P Y (a24_inp C j1 (!c1)) → Tr P Y (a24_inp C j2 c2) → Tr P Y (a24_inp C j2 (!c2)) →
      Tr P Y C.output :=
    fun P Y h1 h2 h3 h4 => a24_tr_R hS hout (a24_tr_and hS hjr b (a24_tr_R hS hR1 (a24_tr_and hS hj1 c1 h1 h2))
      (a24_tr_R hS hR2 (a24_tr_and hS hj2 c2 h3 h4)))
  have hP : ∃ e, a24_PPr n C pw (a24_inp C j1 e) p ∧ a24_Rr n C (pw p) (a24_inp C j1 (!e)) := by
    rcases hak with hau | ⟨q1, hq1, n1⟩
    · exact ⟨c1, ⟨ha, hau⟩, hb⟩
    · rcases hbk with hbu | ⟨q2, hq2, n2⟩
      · exact ⟨!c1, ⟨hb, hbu⟩, by rw [Bool.not_not]; exact ha⟩
      · exfalso
        rcases a24_snd21 hS (htrue {q1, q2} {l} (a24_tr_p hS (by simp) hq1) (a24_tr_p hS (by simp) hq2)
          (a24_tr_l hS (by simp) hc) (a24_tr_l hS (by simp) hd)) with h | h
        · exact n1 h
        · exact n2 h
  have hL : ∃ e, a24_PPr n C lw (a24_inp C j2 e) l ∧ a24_Rr n C (lw l) (a24_inp C j2 (!e)) := by
    rcases hck with hcu | ⟨y1, hy1, n1⟩
    · exact ⟨c2, ⟨hc, hcu⟩, hd⟩
    · rcases hdk with hdu | ⟨y2, hy2, n2⟩
      · exact ⟨!c2, ⟨hd, hdu⟩, by rw [Bool.not_not]; exact hc⟩
      · exfalso
        rcases a24_snd12 hS (htrue {p} {y1, y2} (a24_tr_p hS (by simp) ha) (a24_tr_p hS (by simp) hb)
          (a24_tr_l hS (by simp) hy1) (a24_tr_l hS (by simp) hy2)) with h | h
        · exact n1 h
        · exact n2 h
  obtain ⟨e1, hp1, hp2⟩ := hP
  obtain ⟨e2, hl1, hl2⟩ := hL
  exact ⟨jr, b, j1, e1, j2, e2, hjr, hout, hj1, hR1, hp1, hp2, hj2, hR2, hl1, hl2⟩

theorem a24_cov_C2 {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : a24_Sys n C N M pw lw I Tr) (p : Fin N) (l : Fin M)
    (h : a24_ShBal n C (a24_GPf n C pw I p l) (a24_GLf n C lw I p l) (a24_GPf n C pw I p l) (a24_GLf n C lw I p l)) :
    a24_D0 n C pw lw p l ∨ a24_C2h n C pw lw I p l := by
  obtain ⟨jr, b, j1, c1, j2, c2, hjr, hout, hj1, hR1, ⟨ha, hak⟩, ⟨hb, hbk⟩, hj2, hR2,
    ⟨hc, hck⟩, ⟨hd, hdk⟩⟩ := h
  have htrue : ∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), Tr P Y (a24_inp C j1 c1) →
      Tr P Y (a24_inp C j1 (!c1)) → Tr P Y (a24_inp C j2 c2) → Tr P Y (a24_inp C j2 (!c2)) →
      Tr P Y C.output :=
    fun P Y h1 h2 h3 h4 => a24_tr_R hS hout (a24_tr_and hS hjr b (a24_tr_R hS hR1 (a24_tr_and hS hj1 c1 h1 h2))
      (a24_tr_R hS hR2 (a24_tr_and hS hj2 c2 h3 h4)))
  rcases hak with hau | ⟨qa, hqa, nqa⟩
  · rcases hbk with hbu | ⟨yb, hyb, nyb⟩
    · exact Or.inl ⟨j1, c1, hj1, ⟨ha, hau⟩, ⟨hb, hbu⟩⟩
    · have hdu : ∀ y', a24_Rr n C (lw y') (a24_inp C j2 (!c2)) → y' = l := by
        rcases hdk with h | ⟨yd, hyd, nyd⟩
        · exact h
        · exfalso
          rcases a24_snd12 hS (htrue {p} {yb, yd} (a24_tr_p hS (by simp) ha) (a24_tr_l hS (by simp) hyb)
            (a24_tr_p hS (by simp) hc) (a24_tr_l hS (by simp) hyd)) with h | h
          · exact nyb h
          · exact nyd h
      rcases hck with hcu | ⟨qc, hqc, nqc⟩
      · exact Or.inl ⟨j2, c2, hj2, ⟨hc, hcu⟩, ⟨hd, hdu⟩⟩
      · exact Or.inr ⟨jr, b, j1, c1, j2, !c2, hjr, hout, hj1, hR1, ⟨ha, hau⟩, hb,
          ⟨yb, hyb, nyb⟩, hj2, hR2, ⟨hd, hdu⟩, by rw [Bool.not_not]; exact hc,
          ⟨qc, by rw [Bool.not_not]; exact hqc, nqc⟩⟩
  · have hcu : ∀ x', a24_Rr n C (pw x') (a24_inp C j2 c2) → x' = p := by
      rcases hck with h | ⟨qc, hqc, nqc⟩
      · exact h
      · exfalso
        rcases a24_snd21 hS (htrue {qa, qc} {l} (a24_tr_p hS (by simp) hqa) (a24_tr_l hS (by simp) hb)
          (a24_tr_p hS (by simp) hqc) (a24_tr_l hS (by simp) hd)) with h | h
        · exact nqa h
        · exact nqc h
    rcases hdk with hdu | ⟨yd, hyd, nyd⟩
    · exact Or.inl ⟨j2, c2, hj2, ⟨hc, hcu⟩, ⟨hd, hdu⟩⟩
    · have hbu : ∀ y', a24_Rr n C (lw y') (a24_inp C j1 (!c1)) → y' = l := by
        rcases hbk with h | ⟨yb, hyb, nyb⟩
        · exact h
        · exfalso
          rcases a24_snd12 hS (htrue {p} {yb, yd} (a24_tr_p hS (by simp) ha) (a24_tr_l hS (by simp) hyb)
            (a24_tr_p hS (by simp) hc) (a24_tr_l hS (by simp) hyd)) with h | h
          · exact nyb h
          · exact nyd h
      exact Or.inr ⟨jr, !b, j2, c2, j1, !c1, hjr, hout, hj2, hR2, ⟨hc, hcu⟩, hd,
        ⟨yd, hyd, nyd⟩, hj1, by rw [Bool.not_not]; exact hR1, ⟨hb, hbu⟩,
        by rw [Bool.not_not]; exact ha, ⟨qa, by rw [Bool.not_not]; exact hqa, nqa⟩⟩

theorem a24_cov_C3 {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : a24_Sys n C N M pw lw I Tr) (p : Fin N) (l : Fin M)
    (h : a24_ShCat n C (a24_GPf n C pw I p l) (a24_GPf n C pw I p l) (a24_GLf n C lw I p l) (a24_GLf n C lw I p l)) :
    a24_C15 n C pw lw I Tr p l ∨ a24_C14 n C pw lw I p l := by
  obtain ⟨jr, b, j, c, j', c', hjr, hout, ⟨hx, hxk⟩, hj, hRj, ⟨ha, hak⟩, hj', hRj',
    ⟨hc, hck⟩, ⟨hd, hdk⟩⟩ := h
  have htrue : ∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), Tr P Y (a24_inp C jr b) →
      Tr P Y (a24_inp C j c) → Tr P Y (a24_inp C j' c') → Tr P Y (a24_inp C j' (!c')) → Tr P Y C.output :=
    fun P Y h1 h2 h3 h4 => a24_tr_R hS hout (a24_tr_and hS hjr b h1 (a24_tr_R hS hRj (a24_tr_and hS hj c h2
      (a24_tr_R hS hRj' (a24_tr_and hS hj' c' h3 h4)))))
  have hL : ∃ e, a24_PPr n C lw (a24_inp C j' e) l ∧ a24_Rr n C (lw l) (a24_inp C j' (!e)) := by
    rcases hck with hcu | ⟨y1, hy1, n1⟩
    · exact ⟨c', ⟨hc, hcu⟩, hd⟩
    · rcases hdk with hdu | ⟨y2, hy2, n2⟩
      · exact ⟨!c', ⟨hd, hdu⟩, by rw [Bool.not_not]; exact hc⟩
      · exfalso
        rcases a24_snd12 hS (htrue {p} {y1, y2} (a24_tr_p hS (by simp) hx) (a24_tr_p hS (by simp) ha)
          (a24_tr_l hS (by simp) hy1) (a24_tr_l hS (by simp) hy2)) with h | h
        · exact n1 h
        · exact n2 h
  obtain ⟨e, hl1, hl2⟩ := hL
  rcases hak with hau | ⟨q, hq, nq⟩
  · refine Or.inl ⟨j, c, j', hj, ⟨ha, hau⟩, ?_, hj', hRj', ⟨e, hl1⟩, ?_⟩
    · intro P Y hp hm
      exact a24_tr_R hS hout (a24_tr_and hS hjr b (a24_tr_p hS hp hx) (a24_tr_R hS hRj
        (a24_tr_and hS hj c (a24_tr_p hS hp ha) hm)))
    · intro p' _
      exact ⟨∅, by simp, by simp, a24_tr_and hS hj' c' (a24_tr_l hS (by simp) hc)
        (a24_tr_l hS (by simp) hd)⟩
  · have hxu : ∀ x', a24_Rr n C (pw x') (a24_inp C jr b) → x' = p := by
      rcases hxk with h | ⟨q', hq', nq'⟩
      · exact h
      · exfalso
        rcases a24_snd21 hS (htrue {q', q} {l} (a24_tr_p hS (by simp) hq') (a24_tr_p hS (by simp) hq)
          (a24_tr_l hS (by simp) hc) (a24_tr_l hS (by simp) hd)) with h | h
        · exact nq' h
        · exact nq h
    exact Or.inr ⟨jr, b, j, c, j', e, hjr, hout, ⟨hx, hxu⟩, hj, hRj, ha, ⟨q, hq, nq⟩, hj',
      hRj', hl1, hl2⟩

theorem a24_cov_C4 {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : a24_Sys n C N M pw lw I Tr) (p : Fin N) (l : Fin M)
    (h : a24_ShCat n C (a24_GPf n C pw I p l) (a24_GLf n C lw I p l) (a24_GPf n C pw I p l) (a24_GLf n C lw I p l)) :
    a24_D0 n C pw lw p l ∨ a24_C15 n C pw lw I Tr p l ∨ a24_C4a n C pw lw I p l ∨ a24_C4b n C pw lw I p l := by
  obtain ⟨jr, b, j, c, j', c', hjr, hout, ⟨hx, hxk⟩, hj, hRj, ⟨ha, hak⟩, hj', hRj',
    ⟨hc, hck⟩, ⟨hd, hdk⟩⟩ := h
  have htrue : ∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), Tr P Y (a24_inp C jr b) →
      Tr P Y (a24_inp C j c) → Tr P Y (a24_inp C j' c') → Tr P Y (a24_inp C j' (!c')) → Tr P Y C.output :=
    fun P Y h1 h2 h3 h4 => a24_tr_R hS hout (a24_tr_and hS hjr b h1 (a24_tr_R hS hRj (a24_tr_and hS hj c h2
      (a24_tr_R hS hRj' (a24_tr_and hS hj' c' h3 h4)))))
  rcases hck with hcu | ⟨qc, hqc, nqc⟩
  · rcases hdk with hdu | ⟨yd, hyd, nyd⟩
    · exact Or.inl ⟨j', c', hj', ⟨hc, hcu⟩, ⟨hd, hdu⟩⟩
    · have hau : ∀ y', a24_Rr n C (lw y') (a24_inp C j c) → y' = l := by
        rcases hak with h | ⟨ya, hya, nya⟩
        · exact h
        · exfalso
          rcases a24_snd12 hS (htrue {p} {ya, yd} (a24_tr_p hS (by simp) hx) (a24_tr_l hS (by simp) hya)
            (a24_tr_p hS (by simp) hc) (a24_tr_l hS (by simp) hyd)) with h | h
          · exact nya h
          · exact nyd h
      exact Or.inr (Or.inr (Or.inl ⟨jr, b, j, c, j', c', hjr, hout, hx, hj, hRj, ⟨ha, hau⟩,
        hj', hRj', ⟨hc, hcu⟩, hd, yd, hyd, nyd⟩))
  · have hxu : ∀ x', a24_Rr n C (pw x') (a24_inp C jr b) → x' = p := by
      rcases hxk with h | ⟨qx, hqx, nqx⟩
      · exact h
      · exfalso
        rcases a24_snd21 hS (htrue {qx, qc} {l} (a24_tr_p hS (by simp) hqx) (a24_tr_l hS (by simp) ha)
          (a24_tr_p hS (by simp) hqc) (a24_tr_l hS (by simp) hd)) with h | h
        · exact nqx h
        · exact nqc h
    rcases hak with hau | ⟨ya, hya, nya⟩
    · refine Or.inr (Or.inl ⟨jr, b, j, hjr, ⟨hx, hxu⟩, ?_, hj, hRj, ⟨c, ha, hau⟩, ?_⟩)
      · intro P Y hp hm
        exact a24_tr_R hS hout (a24_tr_and hS hjr b (a24_tr_p hS hp hx) hm)
      · intro p' _
        refine ⟨{qc}, by simp, ?_, a24_tr_and hS hj c (a24_tr_l hS (by simp) ha)
          (a24_tr_R hS hRj' (a24_tr_and hS hj' c' (a24_tr_p hS (by simp) hqc) (a24_tr_l hS (by simp) hd)))⟩
        intro x hx'
        rw [Finset.mem_singleton.mp hx']
        exact nqc
    · have hdu : ∀ y', a24_Rr n C (lw y') (a24_inp C j' (!c')) → y' = l := by
        rcases hdk with h | ⟨yd, hyd, nyd⟩
        · exact h
        · exfalso
          rcases a24_snd12 hS (htrue {p} {ya, yd} (a24_tr_p hS (by simp) hx) (a24_tr_l hS (by simp) hya)
            (a24_tr_p hS (by simp) hc) (a24_tr_l hS (by simp) hyd)) with h | h
          · exact nya h
          · exact nyd h
      exact Or.inr (Or.inr (Or.inr ⟨jr, b, j, c, j', !c', hjr, hout, ⟨hx, hxu⟩, hj, hRj, ha,
        hj', hRj', ⟨hd, hdu⟩, by rw [Bool.not_not]; exact hc,
        ⟨qc, by rw [Bool.not_not]; exact hqc, nqc⟩⟩))

theorem a24_cover_prim {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : a24_Sys n C N M pw lw I Tr) (p : Fin N) (l : Fin M)
    (h : a24_Prim n C (a24_GPf n C pw I p l) (a24_GLf n C lw I p l)) : a24_HalfC n C pw lw I Tr p l := by
  rcases h with h | h | h | h | h | h | h
  · exact Or.inl (a24_cov_A hS p l h)
  · rcases a24_cov_B1 hS p l h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inl (a24_cov_B2 hS p l h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (a24_cov_C1 hS p l h))))
  · rcases a24_cov_C2 hS p l h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h'))))
  · rcases a24_cov_C3 hS p l h with h' | h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (Or.inl h'))
  · rcases a24_cov_C4 hS p l h with h' | h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h')))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h')))))

-- fragment f07_special
def a24_phi15 (n : ℕ) (C : Circuit) {N M : ℕ} (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop)
    (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (j : ℕ) (y : Fin M) : Prop :=
  a24_AndG C j ∧ (∃ c, a24_Rr n C (lw y) (a24_inp C j c)) ∧ a24_DT n I Tr j y

def a24_phi14 (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (j : ℕ) (y : Fin M) : Prop :=
  a24_AndG C j ∧ ∃ c, (∃ z, a24_Rr n C (pw z) (a24_inp C j c) ∧ ¬ I z y) ∧
    a24_Lb n C (a24_phi2 n C lw) (a24_inp C j (!c)) y

def a24_phi1 (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (j : ℕ) (y : Fin M) : Prop :=
  a24_AndG C j ∧ ∃ c, a24_Rr n C (lw y) (a24_inp C j c) ∧ a24_Lb n C (a24_phiB n C pw lw I) (a24_inp C j (!c)) y

def a24_phiNP (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (j : ℕ) (yt : Fin M × Fin M) : Prop :=
  a24_AndG C j ∧ ∃ c, a24_Rr n C (lw yt.1) (a24_inp C j c) ∧
    ∃ x, a24_Lb n C (fun j' x' => a24_Junk n C pw lw I j' x' yt.2) (a24_inp C j (!c)) x ∧ ¬ I x yt.1

theorem a24_pts_le_two {N M : ℕ} {I : Fin N → Fin M → Prop} (h4 : a24_No4 I) {X : Type} (T : Finset X)
    (f : X → Fin N) (hinj : ∀ e ∈ T, ∀ e' ∈ T, f e = f e' → e = e') (l y t : Fin M)
    (hy : y ≠ l) (ht : t ≠ l) (h : ∀ e ∈ T, I (f e) l ∧ (I (f e) y ∨ I (f e) t)) :
    T.card ≤ 2 := by
  classical
  refine a24_card_le_two_of_bool T (fun e => decide (I (f e) y)) ?_
  intro e he e' he' hdec
  have hiff : I (f e) y ↔ I (f e') y := decide_eq_decide.mp hdec
  apply hinj e he e' he'
  by_contra hne
  obtain ⟨hI, ho⟩ := h e he
  obtain ⟨hI', ho'⟩ := h e' he'
  by_cases h1 : I (f e) y
  · exact h4 (f e) (f e') l y hne (Ne.symm hy) ⟨hI, hI', h1, hiff.mp h1⟩
  · have h1' : ¬ I (f e') y := fun hh => h1 (hiff.mpr hh)
    exact h4 (f e) (f e') l t hne (Ne.symm ht)
      ⟨hI, hI', ho.resolve_left h1, ho'.resolve_left h1'⟩

theorem a24_lines_le_two {M : ℕ} (T : Finset (Fin M)) (yt0 : Fin M × Fin M)
    (h : ∀ y ∈ T, yt0.1 = y ∨ yt0.2 = y) : T.card ≤ 2 := by
  classical
  refine a24_card_le_two_of_bool T (fun y => decide (yt0.1 = y)) ?_
  intro y hy y' hy' hdec
  have hiff : yt0.1 = y ↔ yt0.1 = y' := decide_eq_decide.mp hdec
  by_cases h1 : yt0.1 = y
  · exact h1.symm.trans (hiff.mp h1)
  · have h1' : ¬ yt0.1 = y' := fun hh => h1 (hiff.mpr hh)
    exact ((h y hy).resolve_left h1).symm.trans ((h y' hy').resolve_left h1')

def a24_SmallL (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (key : ℕ × Bool) (p : Fin N) (l : Fin M) : Prop :=
  a24_PPr n C pw (a24_inp C key.1 key.2) p ∧ a24_Rr n C (lw l) (a24_inp C key.1 (!key.2)) ∧ I p l ∧
    {t : Fin M | a24_Rr n C (lw t) (a24_inp C key.1 (!key.2)) ∧ I p t}.ncard ≤ 2

theorem a24_fib_SL (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (key : ℕ × Bool) :
    a24_Bd (fun e : Fin N × Fin M => a24_SmallL n C pw lw I key e.1 e.2) 2 := by
  intro S hS
  rcases S.eq_empty_or_nonempty with h | ⟨e0, he0⟩
  · simp [h]
  · obtain ⟨⟨_, hu0⟩, _, _, hk0⟩ := hS e0 he0
    have hp : ∀ e ∈ S, e.1 = e0.1 := fun e he => hu0 _ (hS e he).1.1
    refine a24_card_le_of_maps S Prod.snd (fun e he e' he' h =>
      Prod.ext ((hp e he).trans (hp e' he').symm) h) _ (Set.toFinite _) 2 hk0 ?_
    intro e he
    obtain ⟨_, h2, h3, _⟩ := hS e he
    rw [hp e he] at h3
    exact ⟨h2, h3⟩

def a24_SmallP (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (key : ℕ × Bool) (p : Fin N) (l : Fin M) : Prop :=
  a24_PPr n C lw (a24_inp C key.1 key.2) l ∧ a24_Rr n C (pw p) (a24_inp C key.1 (!key.2)) ∧ I p l ∧
    {z : Fin N | a24_Rr n C (pw z) (a24_inp C key.1 (!key.2)) ∧ I z l}.ncard ≤ 2

theorem a24_fib_SP (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (key : ℕ × Bool) :
    a24_Bd (fun e : Fin N × Fin M => a24_SmallP n C pw lw I key e.1 e.2) 2 := by
  intro S hS
  rcases S.eq_empty_or_nonempty with h | ⟨e0, he0⟩
  · simp [h]
  · obtain ⟨⟨_, hu0⟩, _, _, hk0⟩ := hS e0 he0
    have hp : ∀ e ∈ S, e.2 = e0.2 := fun e he => hu0 _ (hS e he).1.1
    refine a24_card_le_of_maps S Prod.fst (fun e he e' he' h =>
      Prod.ext h ((hp e he).trans (hp e' he').symm)) _ (Set.toFinite _) 2 hk0 ?_
    intro e he
    obtain ⟨_, h2, h3, _⟩ := hS e he
    rw [hp e he] at h3
    exact ⟨h2, h3⟩

def a24_SbCh (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (key : ℕ × Bool) (p : Fin N) (l : Fin M) : Prop :=
  (∃ y1 y2, y1 ≠ y2 ∧ a24_Lb n C (a24_phi1 n C pw lw I) (n + key.1) y1 ∧
    a24_Lb n C (a24_phi1 n C pw lw I) (n + key.1) y2) ∧
  (∀ y, a24_Lb n C (a24_phi1 n C pw lw I) (n + key.1) y → I p y) ∧
  a24_Rr n C (lw l) (a24_inp C key.1 key.2) ∧ I p l ∧
  {t : Fin M | a24_Rr n C (lw t) (a24_inp C key.1 key.2) ∧ I p t}.ncard ≤ 2

theorem a24_fib_Sb (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    {I : Fin N → Fin M → Prop} (h4 : a24_No4 I) (key : ℕ × Bool) :
    a24_Bd (fun e : Fin N × Fin M => a24_SbCh n C pw lw I key e.1 e.2) 2 := by
  intro S hS
  rcases S.eq_empty_or_nonempty with h | ⟨e0, he0⟩
  · simp [h]
  · obtain ⟨⟨y1, y2, hne, h1, h2⟩, ha0, _, _, hk0⟩ := hS e0 he0
    have hp : ∀ e ∈ S, e.1 = e0.1 := by
      intro e he
      by_contra hne2
      have ha := (hS e he).2.1
      exact h4 e.1 e0.1 y1 y2 hne2 hne ⟨ha _ h1, ha0 _ h1, ha _ h2, ha0 _ h2⟩
    refine a24_card_le_of_maps S Prod.snd (fun e he e' he' h =>
      Prod.ext ((hp e he).trans (hp e' he').symm) h) _ (Set.toFinite _) 2 hk0 ?_
    intro e he
    obtain ⟨_, _, h2', h3, _⟩ := hS e he
    rw [hp e he] at h3
    exact ⟨h2', h3⟩

def a24_NbCh (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (key : ℕ × Bool) (p : Fin N) (l : Fin M) : Prop :=
  a24_PPr n C lw (a24_inp C key.1 key.2) l ∧ I p l ∧
  (∃ yt : Fin M × Fin M, a24_Lb n C (a24_phiNP n C pw lw I) (n + key.1) yt ∧ yt.1 ≠ l ∧ yt.2 ≠ l) ∧
  ∀ yt : Fin M × Fin M, a24_Lb n C (a24_phiNP n C pw lw I) (n + key.1) yt → I p yt.1 ∨ I p yt.2

theorem a24_fib_Nb (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    {I : Fin N → Fin M → Prop} (h4 : a24_No4 I) (key : ℕ × Bool) :
    a24_Bd (fun e : Fin N × Fin M => a24_NbCh n C pw lw I key e.1 e.2) 2 := by
  intro S hS
  rcases S.eq_empty_or_nonempty with h | ⟨e0, he0⟩
  · simp [h]
  · obtain ⟨⟨_, hu0⟩, _, ⟨yt, hyt, hn1, hn2⟩, _⟩ := hS e0 he0
    have hl : ∀ e ∈ S, e.2 = e0.2 := fun e he => hu0 _ (hS e he).1.1
    refine a24_pts_le_two h4 S Prod.fst (fun e he e' he' h =>
      Prod.ext h ((hl e he).trans (hl e' he').symm)) e0.2 yt.1 yt.2 hn1 hn2 ?_
    intro e he
    obtain ⟨_, hI, _, ho⟩ := hS e he
    rw [hl e he] at hI
    exact ⟨hI, ho yt hyt⟩

def a24_NcCh (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (key : ℕ × Bool) (p : Fin N) (l : Fin M) : Prop :=
  I p l ∧
  (∀ yt : Fin M × Fin M, a24_Lb n C (a24_phiNP n C pw lw I) (a24_inp C key.1 key.2) yt →
    yt.1 = l ∨ yt.2 = l) ∧
  (∃ yt : Fin M × Fin M, a24_Lb n C (a24_phiNP n C pw lw I) (a24_inp C key.1 key.2) yt) ∧
  (∃ yt : Fin M × Fin M, a24_Lb n C (a24_phiNP n C pw lw I) (n + key.1) yt ∧ yt.1 ≠ l ∧ yt.2 ≠ l) ∧
  ∀ yt : Fin M × Fin M, a24_Lb n C (a24_phiNP n C pw lw I) (n + key.1) yt → I p yt.1 ∨ I p yt.2

theorem a24_fib_Nc (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    {I : Fin N → Fin M → Prop} (h4 : a24_No4 I) (key : ℕ × Bool) :
    a24_Bd (fun e : Fin N × Fin M => a24_NcCh n C pw lw I key e.1 e.2) 4 := by
  intro S hS
  rcases S.eq_empty_or_nonempty with h | ⟨e0, he0⟩
  · simp [h]
  · obtain ⟨_, _, ⟨yt0, hyt0⟩, _, _⟩ := hS e0 he0
    have hh : S.card ≤ 2 * 2 := by
      refine a24_card_le_prod S Prod.snd 2 2 ?_ ?_
      · intro T hT
        refine a24_lines_le_two T yt0 ?_
        intro y hy
        obtain ⟨e, he, hey⟩ := hT y hy
        rw [← hey]
        exact (hS e he).2.1 yt0 hyt0
      · intro y T hT
        rcases T.eq_empty_or_nonempty with h | ⟨e1, he1⟩
        · simp [h]
        · obtain ⟨he1S, hy1⟩ := hT e1 he1
          obtain ⟨_, _, _, ⟨yt, hyt, hn1, hn2⟩, _⟩ := hS e1 he1S
          rw [hy1] at hn1 hn2
          refine a24_pts_le_two h4 T Prod.fst (fun e he e' he' h =>
            Prod.ext h ((hT e he).2.trans (hT e' he').2.symm)) y yt.1 yt.2 hn1 hn2 ?_
          intro e he
          obtain ⟨heS, hye⟩ := hT e he
          obtain ⟨hI, _, _, _, ho⟩ := hS e heS
          rw [hye] at hI
          exact ⟨hI, ho yt hyt⟩
    omega

def a24_NaCh (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (key : ℕ × Bool) (p : Fin N) (l : Fin M) : Prop :=
  a24_Rr n C (pw p) (a24_inp C key.1 key.2) ∧ I p l ∧
  (∀ yt : Fin M × Fin M, a24_Lb n C (a24_phiNP n C pw lw I) (a24_inp C key.1 (!key.2)) yt →
    yt.1 = l ∨ yt.2 = l) ∧
  (∃ yt : Fin M × Fin M, a24_Lb n C (a24_phiNP n C pw lw I) (a24_inp C key.1 (!key.2)) yt) ∧
  {z : Fin N | a24_Rr n C (pw z) (a24_inp C key.1 key.2) ∧ I z l}.ncard ≤ 2

theorem a24_fib_Na (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (key : ℕ × Bool) :
    a24_Bd (fun e : Fin N × Fin M => a24_NaCh n C pw lw I key e.1 e.2) 4 := by
  intro S hS
  rcases S.eq_empty_or_nonempty with h | ⟨e0, he0⟩
  · simp [h]
  · obtain ⟨_, _, _, ⟨yt0, hyt0⟩, _⟩ := hS e0 he0
    have hh : S.card ≤ 2 * 2 := by
      refine a24_card_le_prod S Prod.snd 2 2 ?_ ?_
      · intro T hT
        refine a24_lines_le_two T yt0 ?_
        intro y hy
        obtain ⟨e, he, hey⟩ := hT y hy
        rw [← hey]
        exact (hS e he).2.2.1 yt0 hyt0
      · intro y T hT
        rcases T.eq_empty_or_nonempty with h | ⟨e1, he1⟩
        · simp [h]
        · obtain ⟨he1S, hy1⟩ := hT e1 he1
          have hk := (hS e1 he1S).2.2.2.2
          rw [hy1] at hk
          refine a24_card_le_of_maps T Prod.fst (fun e he e' he' h =>
            Prod.ext h ((hT e he).2.trans (hT e' he').2.symm)) _ (Set.toFinite _) 2 hk ?_
          intro e he
          obtain ⟨heS, hye⟩ := hT e he
          obtain ⟨h1, hI, _⟩ := hS e heS
          rw [hye] at hI
          exact ⟨h1, hI⟩
    omega

-- fragment f08_fam
def a24_F_D0 (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  a24_QU (a24_KA C) (fun key x => a24_Rr n C (pw x) (a24_inp C key.1 key.2)) (fun key y => a24_Rr n C (lw y) (a24_inp C key.1 (!key.2))) e

def a24_F_15a (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  a24_QU (a24_KA C) (fun key x => a24_Rr n C (pw x) (a24_inp C key.1 key.2)) (fun key y => a24_Lb n C (a24_phi15 n C lw I Tr) (a24_inp C key.1 (!key.2)) y) e

def a24_F_15b (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  a24_QM I (a24_KA C) (fun key y => a24_Rr n C (lw y) (a24_inp C key.1 key.2)) (fun key y => a24_Lb n C (a24_phi15 n C lw I Tr) (n + key.1) y) e

def a24_F_15c (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  a24_QM I (a24_KO C) (fun key y => a24_Lb n C (a24_phi15 n C lw I Tr) (a24_inp C key.1 key.2) y) (fun key y => a24_Lb n C (a24_phi15 n C lw I Tr) (n + key.1) y) e

def a24_F_LL (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  a24_QM I (a24_KO C) (fun key y => a24_Lb n C (a24_phi2 n C lw) (a24_inp C key.1 key.2) y) (fun key y => a24_Lb n C (a24_phi2 n C lw) (n + key.1) y) e

def a24_F_14a (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  a24_QU (a24_KA C) (fun key x => a24_Rr n C (pw x) (a24_inp C key.1 key.2)) (fun key y => a24_Lb n C (a24_phi14 n C pw lw I) (a24_inp C key.1 (!key.2)) y) e

def a24_F_14b (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  a24_QM I (a24_KA C) (fun key y => a24_Lb n C (a24_phi2 n C lw) (a24_inp C key.1 (!key.2)) y) (fun key y => a24_Lb n C (a24_phi14 n C pw lw I) (n + key.1) y) e

def a24_F_14c (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  a24_QM I (a24_KO C) (fun key y => a24_Lb n C (a24_phi14 n C pw lw I) (a24_inp C key.1 key.2) y) (fun key y => a24_Lb n C (a24_phi14 n C pw lw I) (n + key.1) y) e

def a24_F_C1g (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  a24_QU (a24_KA C) (fun key y => a24_Lb n C (a24_phi2 n C pw) (a24_inp C key.1 key.2) y) (fun key y => a24_Lb n C (a24_phi2 n C lw) (a24_inp C key.1 (!key.2)) y) e

def a24_F_PP (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  a24_QMP I (a24_KO C) (fun key y => a24_Lb n C (a24_phi2 n C pw) (a24_inp C key.1 key.2) y) (fun key y => a24_Lb n C (a24_phi2 n C pw) (n + key.1) y) e

def a24_F_SL (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  ∃ key ∈ a24_KA C, a24_SmallL n C pw lw I key e.1 e.2

def a24_F_SP (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  ∃ key ∈ a24_KA C, a24_SmallP n C pw lw I key e.1 e.2

def a24_F_Sb (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  a24_QMP I (a24_KA C) (fun key x => a24_Rr n C (pw x) (a24_inp C key.1 key.2)) (fun key y => a24_Lb n C (a24_phiS n C pw lw I) (n + key.1) y) e

def a24_F_Sc (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  a24_QMP I (a24_KO C) (fun key y => a24_Lb n C (a24_phiS n C pw lw I) (a24_inp C key.1 key.2) y) (fun key y => a24_Lb n C (a24_phiS n C pw lw I) (n + key.1) y) e

def a24_F_C2g (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  a24_QU (a24_KA C) (fun key y => a24_Lb n C (a24_phiS n C pw lw I) (a24_inp C key.1 key.2) y) (fun key y => a24_Lb n C (a24_phiB n C pw lw I) (a24_inp C key.1 (!key.2)) y) e

def a24_F_Bb (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  a24_QM I (a24_KA C) (fun key y => a24_Rr n C (lw y) (a24_inp C key.1 key.2)) (fun key y => a24_Lb n C (a24_phiB n C pw lw I) (n + key.1) y) e

def a24_F_Bc (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  a24_QM I (a24_KO C) (fun key y => a24_Lb n C (a24_phiB n C pw lw I) (a24_inp C key.1 key.2) y) (fun key y => a24_Lb n C (a24_phiB n C pw lw I) (n + key.1) y) e

def a24_F_4aE (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  a24_QU (a24_KA C) (fun key y => a24_Lb n C (a24_phiS n C pw lw I) (a24_inp C key.1 (!key.2)) y) (fun key y => a24_Rr n C (lw y) (a24_inp C key.1 key.2)) e

def a24_F_Nb (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  ∃ key ∈ a24_KA C, a24_NbCh n C pw lw I key e.1 e.2

def a24_F_Nc (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  ∃ key ∈ a24_KO C, a24_NcCh n C pw lw I key e.1 e.2

def a24_F_Na (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  ∃ key ∈ a24_KA C, a24_NaCh n C pw lw I key e.1 e.2

def a24_F_4ba (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  a24_QU (a24_KA C) (fun key x => a24_Rr n C (pw x) (a24_inp C key.1 key.2)) (fun key y => a24_Lb n C (a24_phi1 n C pw lw I) (a24_inp C key.1 (!key.2)) y) e

def a24_F_4bc (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  a24_QM I (a24_KO C) (fun key y => a24_Lb n C (a24_phi1 n C pw lw I) (a24_inp C key.1 key.2) y) (fun key y => a24_Lb n C (a24_phi1 n C pw lw I) (n + key.1) y) e

def a24_F_Sbb (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  ∃ key ∈ a24_KA C, a24_SbCh n C pw lw I key e.1 e.2

def a24_F_4b2 (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  a24_QM I (a24_KA C) (fun key y => a24_Lb n C (a24_phiB n C pw lw I) (a24_inp C key.1 (!key.2)) y) (fun key y => a24_Lb n C (a24_phi1 n C pw lw I) (n + key.1) y) e

def a24_F_QF (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  a24_QF n C lw I e

def a24_F_QFP (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  a24_QFP n C pw I e

def a24_HQ (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  a24_F_D0 n C pw lw I Tr e ∨ a24_F_15a n C pw lw I Tr e ∨ a24_F_15b n C pw lw I Tr e ∨ a24_F_15c n C pw lw I Tr e ∨ a24_F_LL n C pw lw I Tr e ∨ a24_F_14a n C pw lw I Tr e ∨ a24_F_14b n C pw lw I Tr e ∨ a24_F_14c n C pw lw I Tr e ∨ a24_F_C1g n C pw lw I Tr e ∨ a24_F_PP n C pw lw I Tr e ∨ a24_F_SL n C pw lw I Tr e ∨ a24_F_SP n C pw lw I Tr e ∨ a24_F_Sb n C pw lw I Tr e ∨ a24_F_Sc n C pw lw I Tr e ∨ a24_F_C2g n C pw lw I Tr e ∨ a24_F_Bb n C pw lw I Tr e ∨ a24_F_Bc n C pw lw I Tr e ∨ a24_F_4aE n C pw lw I Tr e ∨ a24_F_Nb n C pw lw I Tr e ∨ a24_F_Nc n C pw lw I Tr e ∨ a24_F_Na n C pw lw I Tr e ∨ a24_F_4ba n C pw lw I Tr e ∨ a24_F_4bc n C pw lw I Tr e ∨ a24_F_Sbb n C pw lw I Tr e ∨ a24_F_4b2 n C pw lw I Tr e ∨ a24_F_QF n C pw lw I Tr e ∨ a24_F_QFP n C pw lw I Tr e

theorem a24_hq_D0 {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : a24_F_D0 n C pw lw I Tr e) : a24_HQ n C pw lw I Tr e :=
  Or.inl h

theorem a24_hq_15a {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : a24_F_15a n C pw lw I Tr e) : a24_HQ n C pw lw I Tr e :=
  Or.inr (Or.inl h)

theorem a24_hq_15b {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : a24_F_15b n C pw lw I Tr e) : a24_HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inl h))

theorem a24_hq_15c {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : a24_F_15c n C pw lw I Tr e) : a24_HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem a24_hq_LL {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : a24_F_LL n C pw lw I Tr e) : a24_HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem a24_hq_14a {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : a24_F_14a n C pw lw I Tr e) : a24_HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

theorem a24_hq_14b {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : a24_F_14b n C pw lw I Tr e) : a24_HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))

theorem a24_hq_14c {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : a24_F_14c n C pw lw I Tr e) : a24_HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))

theorem a24_hq_C1g {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : a24_F_C1g n C pw lw I Tr e) : a24_HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))

theorem a24_hq_PP {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : a24_F_PP n C pw lw I Tr e) : a24_HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))

theorem a24_hq_SL {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : a24_F_SL n C pw lw I Tr e) : a24_HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))

theorem a24_hq_SP {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : a24_F_SP n C pw lw I Tr e) : a24_HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))

theorem a24_hq_Sb {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : a24_F_Sb n C pw lw I Tr e) : a24_HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))

theorem a24_hq_Sc {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : a24_F_Sc n C pw lw I Tr e) : a24_HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))

theorem a24_hq_C2g {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : a24_F_C2g n C pw lw I Tr e) : a24_HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))

theorem a24_hq_Bb {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : a24_F_Bb n C pw lw I Tr e) : a24_HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))

theorem a24_hq_Bc {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : a24_F_Bc n C pw lw I Tr e) : a24_HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))

theorem a24_hq_4aE {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : a24_F_4aE n C pw lw I Tr e) : a24_HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))

theorem a24_hq_Nb {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : a24_F_Nb n C pw lw I Tr e) : a24_HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))

theorem a24_hq_Nc {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : a24_F_Nc n C pw lw I Tr e) : a24_HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))

theorem a24_hq_Na {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : a24_F_Na n C pw lw I Tr e) : a24_HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))

theorem a24_hq_4ba {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : a24_F_4ba n C pw lw I Tr e) : a24_HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))

theorem a24_hq_4bc {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : a24_F_4bc n C pw lw I Tr e) : a24_HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))

theorem a24_hq_Sbb {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : a24_F_Sbb n C pw lw I Tr e) : a24_HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))

theorem a24_hq_4b2 {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : a24_F_4b2 n C pw lw I Tr e) : a24_HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))

theorem a24_hq_QF {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : a24_F_QF n C pw lw I Tr e) : a24_HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))

theorem a24_hq_QFP {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : a24_F_QFP n C pw lw I Tr e) : a24_HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))))))))))))))))))))))

theorem a24_bd_HQ {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : a24_Sys n C N M pw lw I Tr) :
    a24_Bd (a24_HQ n C pw lw I Tr) (24 * (a24_KA C).card + 19 * (a24_KO C).card) := by
  have h4 : a24_No4 I := hS.2.2.2.2.2.1
  have b_D0 : a24_Bd (a24_F_D0 n C pw lw I Tr) ((a24_KA C).card) := a24_bd_QU _ _ _
  have b_15a : a24_Bd (a24_F_15a n C pw lw I Tr) ((a24_KA C).card) := a24_bd_QU _ _ _
  have b_15b : a24_Bd (a24_F_15b n C pw lw I Tr) ((a24_KA C).card) := a24_bd_QM h4 _ _ _
  have b_15c : a24_Bd (a24_F_15c n C pw lw I Tr) ((a24_KO C).card) := a24_bd_QM h4 _ _ _
  have b_LL : a24_Bd (a24_F_LL n C pw lw I Tr) ((a24_KO C).card) := a24_bd_QM h4 _ _ _
  have b_14a : a24_Bd (a24_F_14a n C pw lw I Tr) ((a24_KA C).card) := a24_bd_QU _ _ _
  have b_14b : a24_Bd (a24_F_14b n C pw lw I Tr) ((a24_KA C).card) := a24_bd_QM h4 _ _ _
  have b_14c : a24_Bd (a24_F_14c n C pw lw I Tr) ((a24_KO C).card) := a24_bd_QM h4 _ _ _
  have b_C1g : a24_Bd (a24_F_C1g n C pw lw I Tr) ((a24_KA C).card) := a24_bd_QU _ _ _
  have b_PP : a24_Bd (a24_F_PP n C pw lw I Tr) ((a24_KO C).card) := a24_bd_QMP h4 _ _ _
  have b_SL : a24_Bd (a24_F_SL n C pw lw I Tr) (2 * (a24_KA C).card) := a24_Bd_charge (a24_KA C) _ 2 (fun key _ => a24_fib_SL n C pw lw I key)
  have b_SP : a24_Bd (a24_F_SP n C pw lw I Tr) (2 * (a24_KA C).card) := a24_Bd_charge (a24_KA C) _ 2 (fun key _ => a24_fib_SP n C pw lw I key)
  have b_Sb : a24_Bd (a24_F_Sb n C pw lw I Tr) ((a24_KA C).card) := a24_bd_QMP h4 _ _ _
  have b_Sc : a24_Bd (a24_F_Sc n C pw lw I Tr) ((a24_KO C).card) := a24_bd_QMP h4 _ _ _
  have b_C2g : a24_Bd (a24_F_C2g n C pw lw I Tr) ((a24_KA C).card) := a24_bd_QU _ _ _
  have b_Bb : a24_Bd (a24_F_Bb n C pw lw I Tr) ((a24_KA C).card) := a24_bd_QM h4 _ _ _
  have b_Bc : a24_Bd (a24_F_Bc n C pw lw I Tr) ((a24_KO C).card) := a24_bd_QM h4 _ _ _
  have b_4aE : a24_Bd (a24_F_4aE n C pw lw I Tr) ((a24_KA C).card) := a24_bd_QU _ _ _
  have b_Nb : a24_Bd (a24_F_Nb n C pw lw I Tr) (2 * (a24_KA C).card) := a24_Bd_charge (a24_KA C) _ 2 (fun key _ => a24_fib_Nb n C pw lw h4 key)
  have b_Nc : a24_Bd (a24_F_Nc n C pw lw I Tr) (4 * (a24_KO C).card) := a24_Bd_charge (a24_KO C) _ 4 (fun key _ => a24_fib_Nc n C pw lw h4 key)
  have b_Na : a24_Bd (a24_F_Na n C pw lw I Tr) (4 * (a24_KA C).card) := a24_Bd_charge (a24_KA C) _ 4 (fun key _ => a24_fib_Na n C pw lw I key)
  have b_4ba : a24_Bd (a24_F_4ba n C pw lw I Tr) ((a24_KA C).card) := a24_bd_QU _ _ _
  have b_4bc : a24_Bd (a24_F_4bc n C pw lw I Tr) ((a24_KO C).card) := a24_bd_QM h4 _ _ _
  have b_Sbb : a24_Bd (a24_F_Sbb n C pw lw I Tr) (2 * (a24_KA C).card) := a24_Bd_charge (a24_KA C) _ 2 (fun key _ => a24_fib_Sb n C pw lw h4 key)
  have b_4b2 : a24_Bd (a24_F_4b2 n C pw lw I Tr) ((a24_KA C).card) := a24_bd_QM h4 _ _ _
  have b_QF : a24_Bd (a24_F_QF n C pw lw I Tr) (4 * (a24_KO C).card) := a24_bd_QF n C lw h4
  have b_QFP : a24_Bd (a24_F_QFP n C pw lw I Tr) (4 * (a24_KO C).card) := a24_bd_QFP n C pw h4
  refine a24_Bd_le ?_ (a24_Bd_or (b_D0) (a24_Bd_or (b_15a) (a24_Bd_or (b_15b) (a24_Bd_or (b_15c) (a24_Bd_or (b_LL) (a24_Bd_or (b_14a) (a24_Bd_or (b_14b) (a24_Bd_or (b_14c) (a24_Bd_or (b_C1g) (a24_Bd_or (b_PP) (a24_Bd_or (b_SL) (a24_Bd_or (b_SP) (a24_Bd_or (b_Sb) (a24_Bd_or (b_Sc) (a24_Bd_or (b_C2g) (a24_Bd_or (b_Bb) (a24_Bd_or (b_Bc) (a24_Bd_or (b_4aE) (a24_Bd_or (b_Nb) (a24_Bd_or (b_Nc) (a24_Bd_or (b_Na) (a24_Bd_or (b_4ba) (a24_Bd_or (b_4bc) (a24_Bd_or (b_Sbb) (a24_Bd_or (b_4b2) (a24_Bd_or (b_QF) (b_QFP)))))))))))))))))))))))))))
  omega

-- fragment f09_classes
theorem a24_junk_not {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {j : ℕ} {x : Fin N} {t : Fin M} (h : a24_Junk n C pw lw I j x t) :
    ¬ I x t := by
  obtain ⟨_, _, _, _, hn⟩ := h
  exact hn

theorem a24_phi2_of {n : ℕ} {C : Circuit} {K : ℕ} {xw : Fin K → ℕ} {j : ℕ} (hj : a24_AndG C j) (c : Bool)
    {x : Fin K} (h1 : a24_Rr n C (xw x) (a24_inp C j c)) (h2 : a24_Rr n C (xw x) (a24_inp C j (!c))) :
    a24_phi2 n C xw j x := by
  cases c
  · exact ⟨hj, h1, h2⟩
  · exact ⟨hj, h2, h1⟩

theorem a24_phi2_at {n : ℕ} {C : Circuit} {K : ℕ} {xw : Fin K → ℕ} {j : ℕ} {x : Fin K}
    (h : a24_phi2 n C xw j x) (c : Bool) : a24_Rr n C (xw x) (a24_inp C j c) := by
  cases c
  · exact h.2.1
  · exact h.2.2

theorem a24_hq_of_D0 {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : a24_Sys n C N M pw lw I Tr) (p : Fin N) (l : Fin M) (h : a24_D0 n C pw lw p l) :
    a24_HQ n C pw lw I Tr (p, l) := by
  obtain ⟨j, b, hj, ⟨h1, h2⟩, ⟨h3, h4⟩⟩ := h
  exact a24_hq_D0 ⟨(j, b), a24_mem_KA.mpr hj, h1, h2, h3, h4⟩

theorem a24_rig15 {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : a24_Sys n C N M pw lw I Tr) {p : Fin N} {m : ℕ} {y : Fin M} (hacc : a24_Acc C Tr p m)
    (hl : a24_Lb n C (a24_phi15 n C lw I Tr) m y) : I p y := by
  obtain ⟨hC, hpw, hlw, hpn, hln, h4, htp, htl, htR, htA, hsnd⟩ := id hS
  by_contra hn
  obtain ⟨j, hR, _, _, hdt⟩ := hl
  obtain ⟨P, hP1, hPn, htr⟩ := hdt p hn
  have hout := hacc (insert p P) {y} (Finset.mem_insert_self p P) (htR _ _ _ _ hR htr)
  obtain ⟨x, hx, y', hy', hI'⟩ := hsnd (insert p P) {y}
    ((Finset.card_insert_le p P).trans (by omega)) (by simp) hout
  rw [Finset.mem_singleton] at hy'
  rw [hy'] at hI'
  rcases Finset.mem_insert.mp hx with h | h
  · rw [h] at hI'
    exact hn hI'
  · exact hPn x h hI'

theorem a24_hq_of_C15 {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : a24_Sys n C N M pw lw I Tr) (p : Fin N) (l : Fin M) (h : a24_C15 n C pw lw I Tr p l) :
    a24_HQ n C pw lw I Tr (p, l) := by
  obtain ⟨rd, b, β, hrd, ⟨hp1, hp2⟩, hacc, hβ, hRβ, ⟨c, hl1, hl2⟩, hdt⟩ := h
  have hC := hS.1
  have h0 : a24_phi15 n C lw I Tr β l := ⟨hβ, ⟨c, hl1⟩, hdt⟩
  have hrig : ∀ y, a24_Lb n C (a24_phi15 n C lw I Tr) (a24_inp C rd (!b)) y → I p y :=
    fun y hy => a24_rig15 hS hacc hy
  rcases a24_fm_line hC (a24_phi15 n C lw I Tr) p l β (a24_inp C rd (!b)) hRβ h0 hrig with
    h | ⟨y, hy, hne⟩ | h
  · exact a24_hq_15a ⟨(rd, b), a24_mem_KA.mpr hrd, hp1, hp2, a24_Lb_mono hRβ (a24_Lb_self h0), h⟩
  · exact a24_hq_15b ⟨(β, c), a24_mem_KA.mpr hβ, hl1, hl2, a24_Lb_self h0, ⟨y, hy, hne⟩,
      fun y' hy' => hrig y' (a24_Lb_mono hRβ hy')⟩
  · exact a24_hq_15c h

theorem a24_hq_of_C14 {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : a24_Sys n C N M pw lw I Tr) (p : Fin N) (l : Fin M) (h : a24_C14 n C pw lw I p l) :
    a24_HQ n C pw lw I Tr (p, l) := by
  obtain ⟨jr, b, j, c, j', c', hjr, hout, ⟨hp1, hp2⟩, hj, hRj, ha, ⟨q, hq, nq⟩, hj', hRj',
    ⟨hl1, hl2⟩, hl3⟩ := h
  have hC := hS.1
  have h2 : a24_phi2 n C lw j' l := a24_phi2_of hj' c' hl1 hl3
  have hrig2 : ∀ y, a24_Lb n C (a24_phi2 n C lw) (a24_inp C j (!c)) y → I p y := by
    intro y hy
    obtain ⟨j2, hR2, hphi⟩ := hy
    exact a24_snd11 hS (x := p) (y := y) (a24_tr_R hS hout (a24_tr_and hS hjr b (a24_tr_p hS (by simp) hp1)
      (a24_tr_R hS hRj (a24_tr_and hS hj c (a24_tr_p hS (by simp) ha)
        (a24_tr_R hS hR2 (a24_phi2l_tr hS hphi (by simp)))))))
  rcases a24_fm_line hC (a24_phi2 n C lw) p l j' (a24_inp C j (!c)) hRj' h2 hrig2 with
    ha2 | ⟨y, hy, hne⟩ | hc2
  · have h14 : a24_phi14 n C pw lw I j l := ⟨hj, c, ⟨q, hq, nq⟩, a24_Lb_mono hRj' (a24_Lb_self h2)⟩
    have hrig1 : ∀ y, a24_Lb n C (a24_phi14 n C pw lw I) (a24_inp C jr (!b)) y → I p y := by
      intro y hy
      obtain ⟨j1, hR1, hj1, c1, ⟨z, hz, nz⟩, ⟨j2, hR2, hphi⟩⟩ := hy
      rcases a24_snd21 hS (x := p) (z := z) (y := y) (a24_tr_R hS hout (a24_tr_and hS hjr b
        (a24_tr_p hS (by simp) hp1) (a24_tr_R hS hR1 (a24_tr_and hS hj1 c1 (a24_tr_p hS (by simp) hz)
          (a24_tr_R hS hR2 (a24_phi2l_tr hS hphi (by simp))))))) with h | h
      · exact h
      · exact absurd h nz
    rcases a24_fm_line hC (a24_phi14 n C pw lw I) p l j (a24_inp C jr (!b)) hRj h14 hrig1 with
      ha1 | ⟨y, hy, hne⟩ | hc1
    · exact a24_hq_14a ⟨(jr, b), a24_mem_KA.mpr hjr, hp1, hp2, a24_Lb_mono hRj (a24_Lb_self h14), ha1⟩
    · exact a24_hq_14b ⟨(j, c), a24_mem_KA.mpr hj, a24_Lb_mono hRj' (a24_Lb_self h2), ha2, a24_Lb_self h14,
        ⟨y, hy, hne⟩, fun y' hy' => hrig1 y' (a24_Lb_mono hRj hy')⟩
    · exact a24_hq_14c hc1
  · exfalso
    exact hne (hl2 _ (a24_phi2_at (a24_Lb_and hC hj' hy) c'))
  · exact a24_hq_LL hc2

theorem a24_hq_of_C1 {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : a24_Sys n C N M pw lw I Tr) (p : Fin N) (l : Fin M) (h : a24_C1 n C pw lw p l) :
    a24_HQ n C pw lw I Tr (p, l) := by
  obtain ⟨g, bg, α, bα, β, bβ, hg, hout, hα, hRα, ⟨hp1, hp2⟩, hp3, hβ, hRβ, ⟨hl1, hl2⟩,
    hl3⟩ := h
  have hC := hS.1
  have hψ : a24_phi2 n C pw α p := a24_phi2_of hα bα hp1 hp3
  have hφ : a24_phi2 n C lw β l := a24_phi2_of hβ bβ hl1 hl3
  have rig : ∀ x y, a24_Lb n C (a24_phi2 n C pw) (a24_inp C g bg) x →
      a24_Lb n C (a24_phi2 n C lw) (a24_inp C g (!bg)) y → I x y := by
    intro x y hx hy
    obtain ⟨j1, hR1, h1⟩ := hx
    obtain ⟨j2, hR2, h2⟩ := hy
    exact a24_snd11 hS (x := x) (y := y) (a24_tr_R hS hout (a24_tr_and hS hg bg
      (a24_tr_R hS hR1 (a24_phi2p_tr hS h1 (by simp))) (a24_tr_R hS hR2 (a24_phi2l_tr hS h2 (by simp)))))
  have hLp : a24_Lb n C (a24_phi2 n C pw) (a24_inp C g bg) p := a24_Lb_mono hRα (a24_Lb_self hψ)
  have hLl : a24_Lb n C (a24_phi2 n C lw) (a24_inp C g (!bg)) l := a24_Lb_mono hRβ (a24_Lb_self hφ)
  rcases a24_fm_line hC (a24_phi2 n C lw) p l β (a24_inp C g (!bg)) hRβ hφ (fun y hy => rig p y hLp hy) with
    ha | ⟨y, hy, hne⟩ | hc
  · rcases a24_fm_pt hC (a24_phi2 n C pw) p l α (a24_inp C g bg) hRα hψ (fun x hx => rig x l hx hLl) with
      ha' | ⟨x, hx, hne⟩ | hc'
    · exact a24_hq_C1g ⟨(g, bg), a24_mem_KA.mpr hg, hLp, ha', hLl, ha⟩
    · exfalso
      exact hne (hp2 _ (a24_phi2_at (a24_Lb_and hC hα hx) bα))
    · exact a24_hq_PP hc'
  · exfalso
    exact hne (hl2 _ (a24_phi2_at (a24_Lb_and hC hβ hy) bβ))
  · exact a24_hq_LL hc

theorem a24_hq_of_C2h {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : a24_Sys n C N M pw lw I Tr) (p : Fin N) (l : Fin M) (hI : I p l) (h : a24_C2h n C pw lw I p l) :
    a24_HQ n C pw lw I Tr (p, l) := by
  obtain ⟨g, bg, α, bα, β, bβ, hg, hout, hα, hRα, ⟨hp1, hp2⟩, hla, ⟨y0, hy0, n0⟩, hβ, hRβ,
    ⟨hl1, hl2⟩, hpb, ⟨q0, hq0, nq0⟩⟩ := h
  obtain ⟨hC, hpw, hlw, hpn, hln, h4, htp, htl, htR, htA, hsnd⟩ := id hS
  have hJa : ∀ t, a24_Rr n C (lw t) (a24_inp C α (!bα)) → ¬ I p t → a24_Junk n C pw lw I α p t :=
    fun t ht hn => ⟨hα, bα, hp1, ht, hn⟩
  have hJb : ∀ z, a24_Rr n C (pw z) (a24_inp C β (!bβ)) → ¬ I z l → a24_Junk n C pw lw I β z l :=
    fun z hz hn => ⟨hβ, !bβ, hz, by rw [Bool.not_not]; exact hl1, hn⟩
  have hψ0 : a24_phiS n C pw lw I α p := ⟨y0, hJa y0 hy0 n0⟩
  have hφ0 : a24_phiB n C pw lw I β l := ⟨q0, hJb q0 hq0 nq0⟩
  have JS : ∀ j1 x t j2 z y, a24_Rr n C (n + j1) (a24_inp C g bg) → a24_Junk n C pw lw I j1 x t →
      a24_Rr n C (n + j2) (a24_inp C g (!bg)) → a24_Junk n C pw lw I j2 z y → I x y ∨ I z t := by
    intro j1 x t j2 z y h1 J1 h2 J2
    rcases a24_snd22 hS (x := x) (z := z) (y := t) (t := y) (a24_tr_R hS hout (a24_tr_and hS hg bg
      (a24_tr_R hS h1 (a24_junk_tr hS J1 (by simp) (by simp)))
      (a24_tr_R hS h2 (a24_junk_tr hS J2 (by simp) (by simp))))) with h | h | h | h
    · exact absurd h (a24_junk_not J1)
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h (a24_junk_not J2)
  by_cases hY : ∃ y', a24_Lb n C (a24_phiB n C pw lw I) (a24_inp C g (!bg)) y' ∧ ¬ I p y'
  · obtain ⟨y', ⟨j2, hR2, z', J2⟩, ny'⟩ := hY
    have hz : ∀ t, a24_Rr n C (lw t) (a24_inp C α (!bα)) → I p t ∨ I z' t := by
      intro t ht
      by_cases hpt : I p t
      · exact Or.inl hpt
      · rcases JS α p t j2 z' y' hRα (hJa t ht hpt) hR2 J2 with h | h
        · exact absurd h ny'
        · exact Or.inr h
    by_cases h3 : 3 ≤ {t : Fin M | a24_Rr n C (lw t) (a24_inp C α (!bα)) ∧ I p t}.ncard
    · obtain ⟨jo, b', hjo, hch⟩ := a24_F3_exists hC lw hlw hln I (a24_inp C α (!bα)) p l hla hI h3 z' hz
      exact a24_hq_QF ⟨(jo, b'), a24_mem_KO.mpr hjo, hch⟩
    · exact a24_hq_SL ⟨(α, bα), a24_mem_KA.mpr hα, ⟨hp1, hp2⟩, hla, hI,
        Nat.le_of_lt_succ (not_le.mp h3)⟩
  by_cases hX : ∃ x', a24_Lb n C (a24_phiS n C pw lw I) (a24_inp C g bg) x' ∧ ¬ I x' l
  · obtain ⟨x', ⟨j1, hR1, t', J1⟩, nx'⟩ := hX
    have hz : ∀ z, a24_Rr n C (pw z) (a24_inp C β (!bβ)) → I z l ∨ I z t' := by
      intro z hzz
      by_cases hzl : I z l
      · exact Or.inl hzl
      · rcases JS j1 x' t' β z l hR1 J1 hRβ (hJb z hzz hzl) with h | h
        · exact absurd h nx'
        · exact Or.inr h
    by_cases h3 : 3 ≤ {z : Fin N | a24_Rr n C (pw z) (a24_inp C β (!bβ)) ∧ I z l}.ncard
    · obtain ⟨jo, b', hjo, hch⟩ := a24_F3_exists hC pw hpw hpn
        (fun (l : Fin M) (p : Fin N) => I p l) (a24_inp C β (!bβ)) l p hpb hI h3 t' hz
      exact a24_hq_QFP ⟨(jo, b'), a24_mem_KO.mpr hjo, hch⟩
    · exact a24_hq_SP ⟨(β, bβ), a24_mem_KA.mpr hβ, ⟨hl1, hl2⟩, hpb, hI,
        Nat.le_of_lt_succ (not_le.mp h3)⟩
  have hnX : ∀ x, a24_Lb n C (a24_phiS n C pw lw I) (a24_inp C g bg) x → I x l := by
    intro x hx
    by_contra hn
    exact hX ⟨x, hx, hn⟩
  have hnY : ∀ y, a24_Lb n C (a24_phiB n C pw lw I) (a24_inp C g (!bg)) y → I p y := by
    intro y hy
    by_contra hn
    exact hY ⟨y, hy, hn⟩
  have hLp : a24_Lb n C (a24_phiS n C pw lw I) (a24_inp C g bg) p := a24_Lb_mono hRα (a24_Lb_self hψ0)
  have hLl : a24_Lb n C (a24_phiB n C pw lw I) (a24_inp C g (!bg)) l := a24_Lb_mono hRβ (a24_Lb_self hφ0)
  rcases a24_fm_pt hC (a24_phiS n C pw lw I) p l α (a24_inp C g bg) hRα hψ0 hnX with
    ha | ⟨x, hx, hne⟩ | hc
  · rcases a24_fm_line hC (a24_phiB n C pw lw I) p l β (a24_inp C g (!bg)) hRβ hφ0 hnY with
      ha' | ⟨y, hy, hne⟩ | hc'
    · exact a24_hq_C2g ⟨(g, bg), a24_mem_KA.mpr hg, hLp, ha, hLl, ha'⟩
    · exact a24_hq_Bb ⟨(β, bβ), a24_mem_KA.mpr hβ, hl1, hl2, a24_Lb_self hφ0, ⟨y, hy, hne⟩,
        fun y' hy' => hnY y' (a24_Lb_mono hRβ hy')⟩
    · exact a24_hq_Bc hc'
  · exact a24_hq_Sb ⟨(α, bα), a24_mem_KA.mpr hα, hp1, hp2, a24_Lb_self hψ0, ⟨x, hx, hne⟩,
      fun x' hx' => hnX x' (a24_Lb_mono hRα hx')⟩
  · exact a24_hq_Sc hc

theorem a24_hq_of_C4a {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : a24_Sys n C N M pw lw I Tr) (p : Fin N) (l : Fin M) (hI : I p l) (h : a24_C4a n C pw lw I p l) :
    a24_HQ n C pw lw I Tr (p, l) := by
  obtain ⟨ρ, bρ, β, bβ, α, bα, hρ, hout, hpx, hβ, hRβ, ⟨hl1, hl2⟩, hα, hRα, ⟨hp1, hp2⟩, hla,
    y0, hy0, n0⟩ := h
  obtain ⟨hC, hpw, hlw, hpn, hln, h4, htp, htl, htR, htA, hsnd⟩ := id hS
  have hψ0 : a24_phiS n C pw lw I α p := ⟨y0, hα, bα, hp1, hy0, n0⟩
  by_cases hE : ∀ x, a24_Lb n C (a24_phiS n C pw lw I) (a24_inp C β (!bβ)) x → I x l
  · rcases a24_fm_pt hC (a24_phiS n C pw lw I) p l α (a24_inp C β (!bβ)) hRα hψ0 hE with
      ha | ⟨x, hx, hne⟩ | hc
    · exact a24_hq_4aE ⟨(β, bβ), a24_mem_KA.mpr hβ, a24_Lb_mono hRα (a24_Lb_self hψ0), ha, hl1, hl2⟩
    · exact a24_hq_Sb ⟨(α, bα), a24_mem_KA.mpr hα, hp1, hp2, a24_Lb_self hψ0, ⟨x, hx, hne⟩,
        fun x' hx' => hE x' (a24_Lb_mono hRα hx')⟩
    · exact a24_hq_Sc hc
  · have hN : ∃ p', a24_Lb n C (a24_phiS n C pw lw I) (a24_inp C β (!bβ)) p' ∧ ¬ I p' l := by
      by_contra hh
      apply hE
      intro x hx
      by_contra hn
      exact hh ⟨x, hx, hn⟩
    obtain ⟨p', ⟨α', hR', t', J'⟩, np'⟩ := hN
    have own : a24_phiNP n C pw lw I β (l, t') := ⟨hβ, bβ, hl1, p', ⟨α', hR', J'⟩, np'⟩
    have CP : ∀ yt : Fin M × Fin M, a24_Lb n C (a24_phiNP n C pw lw I) (a24_inp C ρ (!bρ)) yt →
        ∀ x, a24_Rr n C (pw x) (a24_inp C ρ bρ) → I x yt.1 ∨ I x yt.2 := by
      intro yt hyt x hx
      obtain ⟨j, hRj, hj, c, hy, x'', ⟨j', hRj', J⟩, hn⟩ := hyt
      rcases a24_snd22 hS (x := x) (z := x'') (y := yt.1) (t := yt.2) (a24_tr_R hS hout
        (a24_tr_and hS hρ bρ (a24_tr_p hS (by simp) hx) (a24_tr_R hS hRj (a24_tr_and hS hj c
          (a24_tr_l hS (by simp) hy) (a24_tr_R hS hRj' (a24_junk_tr hS J (by simp) (by simp))))))) with
        h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h hn
      · exact absurd h (a24_junk_not J)
    have hown : a24_Lb n C (a24_phiNP n C pw lw I) (a24_inp C ρ (!bρ)) (l, t') := a24_Lb_mono hRβ (a24_Lb_self own)
    by_cases ha : ∀ yt : Fin M × Fin M, a24_Lb n C (a24_phiNP n C pw lw I) (a24_inp C ρ (!bρ)) yt →
        yt.1 = l ∨ yt.2 = l
    · by_cases hQ : 3 ≤ {z : Fin N | a24_Rr n C (pw z) (a24_inp C ρ bρ) ∧ I z l}.ncard
      · obtain ⟨jo, b', hjo, hch⟩ := a24_F3_exists hC pw hpw hpn
          (fun (l : Fin M) (p : Fin N) => I p l) (a24_inp C ρ bρ) l p hpx hI hQ t'
          (fun z hz => CP (l, t') hown z hz)
        exact a24_hq_QFP ⟨(jo, b'), a24_mem_KO.mpr hjo, hch⟩
      · exact a24_hq_Na ⟨(ρ, bρ), a24_mem_KA.mpr hρ, hpx, hI, ha, ⟨(l, t'), hown⟩,
          Nat.le_of_lt_succ (not_le.mp hQ)⟩
    · by_cases hb : ∀ yt : Fin M × Fin M, a24_Lb n C (a24_phiNP n C pw lw I) (n + β) yt →
          yt.1 = l ∨ yt.2 = l
      · obtain ⟨jo, b', hjo, h3, h4', h5, h6⟩ := a24_FMG hC
          (fun v => ∀ yt : Fin M × Fin M, a24_Lb n C (a24_phiNP n C pw lw I) v yt → yt.1 = l ∨ yt.2 = l)
          (n + β) (a24_inp C ρ (!bρ)) hRβ hb ha
        have h6' : ∃ yt : Fin M × Fin M, a24_Lb n C (a24_phiNP n C pw lw I) (n + jo) yt ∧
            yt.1 ≠ l ∧ yt.2 ≠ l := by
          by_contra hh
          apply h6
          intro yt hyt
          by_contra hn
          exact hh ⟨yt, hyt, fun h => hn (Or.inl h), fun h => hn (Or.inr h)⟩
        exact a24_hq_Nc ⟨(jo, b'), a24_mem_KO.mpr hjo, hI, h5, ⟨(l, t'), a24_Lb_mono h4' (a24_Lb_self own)⟩,
          h6', fun yt hyt => CP yt (a24_Lb_mono h3 hyt) p hpx⟩
      · have hb' : ∃ yt : Fin M × Fin M, a24_Lb n C (a24_phiNP n C pw lw I) (n + β) yt ∧
            yt.1 ≠ l ∧ yt.2 ≠ l := by
          by_contra hh
          apply hb
          intro yt hyt
          by_contra hn
          exact hh ⟨yt, hyt, fun h => hn (Or.inl h), fun h => hn (Or.inr h)⟩
        exact a24_hq_Nb ⟨(β, bβ), a24_mem_KA.mpr hβ, ⟨hl1, hl2⟩, hI, hb',
          fun yt hyt => CP yt (a24_Lb_mono hRβ hyt) p hpx⟩

theorem a24_hq_of_C4b {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : a24_Sys n C N M pw lw I Tr) (p : Fin N) (l : Fin M) (hI : I p l) (h : a24_C4b n C pw lw I p l) :
    a24_HQ n C pw lw I Tr (p, l) := by
  obtain ⟨ρ, bρ, s, bs, β, bβ, hρ, hout, ⟨hp1, hp2⟩, hs, hRs, hls, hβ, hRβ, ⟨hl1, hl2⟩, hpb,
    q0, hq0, nq0⟩ := h
  obtain ⟨hC, hpw, hlw, hpn, hln, h4, htp, htl, htR, htA, hsnd⟩ := id hS
  have hB0 : a24_phiB n C pw lw I β l :=
    ⟨q0, hβ, !bβ, hq0, by rw [Bool.not_not]; exact hl1, nq0⟩
  have h10 : a24_phi1 n C pw lw I s l := ⟨hs, bs, hls, a24_Lb_mono hRβ (a24_Lb_self hB0)⟩
  have R1 : ∀ y, a24_Lb n C (a24_phi1 n C pw lw I) (a24_inp C ρ (!bρ)) y → I p y := by
    intro y hy
    obtain ⟨j, hRj, hj, c, hyc, j', hRj', z, J⟩ := hy
    rcases a24_snd21 hS (x := p) (z := z) (y := y) (a24_tr_R hS hout (a24_tr_and hS hρ bρ
      (a24_tr_p hS (by simp) hp1) (a24_tr_R hS hRj (a24_tr_and hS hj c (a24_tr_l hS (by simp) hyc)
        (a24_tr_R hS hRj' (a24_junk_tr hS J (by simp) (by simp))))))) with h | h
    · exact h
    · exact absurd h (a24_junk_not J)
  rcases a24_fm_line hC (a24_phi1 n C pw lw I) p l s (a24_inp C ρ (!bρ)) hRs h10 R1 with
    ha | ⟨y2, hy2, hne2⟩ | hc
  · exact a24_hq_4ba ⟨(ρ, bρ), a24_mem_KA.mpr hρ, hp1, hp2, a24_Lb_mono hRs (a24_Lb_self h10), ha⟩
  · have Hs1 : ∀ y, a24_Lb n C (a24_phi1 n C pw lw I) (n + s) y → I p y :=
      fun y hy => R1 y (a24_Lb_mono hRs hy)
    by_cases hY : ∃ y'', a24_Lb n C (a24_phiB n C pw lw I) (a24_inp C s (!bs)) y'' ∧ ¬ I p y''
    · obtain ⟨y'', ⟨j'', hR'', z'', J''⟩, ny''⟩ := hY
      have hz : ∀ t, a24_Rr n C (lw t) (a24_inp C s bs) → I p t ∨ I z'' t := by
        intro t ht
        rcases a24_snd22 hS (x := p) (z := z'') (y := t) (t := y'') (a24_tr_R hS hout
          (a24_tr_and hS hρ bρ (a24_tr_p hS (by simp) hp1) (a24_tr_R hS hRs (a24_tr_and hS hs bs
            (a24_tr_l hS (by simp) ht) (a24_tr_R hS hR'' (a24_junk_tr hS J'' (by simp) (by simp))))))) with
          h | h | h | h
        · exact Or.inl h
        · exact absurd h ny''
        · exact Or.inr h
        · exact absurd h (a24_junk_not J'')
      by_cases h3 : 3 ≤ {t : Fin M | a24_Rr n C (lw t) (a24_inp C s bs) ∧ I p t}.ncard
      · obtain ⟨jo, b', hjo, hch⟩ := a24_F3_exists hC lw hlw hln I (a24_inp C s bs) p l hls hI h3 z'' hz
        exact a24_hq_QF ⟨(jo, b'), a24_mem_KO.mpr hjo, hch⟩
      · exact a24_hq_Sbb ⟨(s, bs), a24_mem_KA.mpr hs, ⟨y2, l, hne2, hy2, a24_Lb_self h10⟩, Hs1, hls, hI,
          Nat.le_of_lt_succ (not_le.mp h3)⟩
    · have hnY : ∀ y, a24_Lb n C (a24_phiB n C pw lw I) (a24_inp C s (!bs)) y → I p y := by
        intro y hy
        by_contra hn
        exact hY ⟨y, hy, hn⟩
      rcases a24_fm_line hC (a24_phiB n C pw lw I) p l β (a24_inp C s (!bs)) hRβ hB0 hnY with
        ha2 | ⟨y, hy, hne⟩ | hc2
      · exact a24_hq_4b2 ⟨(s, bs), a24_mem_KA.mpr hs, a24_Lb_mono hRβ (a24_Lb_self hB0), ha2, a24_Lb_self h10,
          ⟨y2, hy2, hne2⟩, Hs1⟩
      · exact a24_hq_Bb ⟨(β, bβ), a24_mem_KA.mpr hβ, hl1, hl2, a24_Lb_self hB0, ⟨y, hy, hne⟩,
          fun y' hy' => hnY y' (a24_Lb_mono hRβ hy')⟩
      · exact a24_hq_Bc hc2
  · exact a24_hq_4bc hc

theorem a24_hq_of_half {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : a24_Sys n C N M pw lw I Tr) (p : Fin N) (l : Fin M) (hI : I p l)
    (h : a24_HalfC n C pw lw I Tr p l) : a24_HQ n C pw lw I Tr (p, l) := by
  rcases h with h | h | h | h | h | h | h
  · exact a24_hq_of_D0 hS p l h
  · exact a24_hq_of_C15 hS p l h
  · exact a24_hq_of_C14 hS p l h
  · exact a24_hq_of_C1 hS p l h
  · exact a24_hq_of_C2h hS p l hI h
  · exact a24_hq_of_C4a hS p l hI h
  · exact a24_hq_of_C4b hS p l hI h

theorem a24_half {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : a24_Sys n C N M pw lw I Tr) :
    a24_Bd (fun e : Fin N × Fin M => I e.1 e.2 ∧
      a24_Prim n C (a24_GPf n C pw I e.1 e.2) (a24_GLf n C lw I e.1 e.2))
      (24 * (a24_KA C).card + 19 * (a24_KO C).card) :=
  a24_Bd_mono (fun e he => a24_hq_of_half hS e.1 e.2 he.1 (a24_cover_prim hS e.1 e.2 he.2)) (a24_bd_HQ hS)

-- fragment f10_main
theorem a24_Bd_ncard {X : Type} [Finite X] {P : X → Prop} {k : ℕ} (h : a24_Bd P k) :
    {e | P e}.ncard ≤ k := by
  classical
  have hfin : {e | P e}.Finite := Set.toFinite _
  rw [Set.ncard_eq_toFinset_card _ hfin]
  refine h _ ?_
  intro e he
  exact (Set.Finite.mem_toFinset hfin).mp he

theorem a24_Bd_swap {α β : Type} {P : β × α → Prop} {k : ℕ} (h : a24_Bd P k) :
    a24_Bd (fun e : α × β => P e.swap) k := by
  classical
  intro S hS
  have h1 : (S.image Prod.swap).card = S.card :=
    Finset.card_image_of_injective S Prod.swap_injective
  have h2 := h (S.image Prod.swap) (fun e he => by
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
    exact hS e' he')
  omega

theorem a24_core (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hpw : Function.Injective pw) (hlw : Function.Injective lw)
    (hne : ∀ (p1 : Fin N) (l1 : Fin M), pw p1 ≠ lw l1) (hpn : ∀ p2 : Fin N, pw p2 < n)
    (hln : ∀ l2 : Fin M, lw l2 < n)
    (h4 : ∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 → ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5))
    (hsound : (∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2 → (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) → PEqualNP.MetaComplexity.circuitFun n C (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)) = false))
    (hread : (∀ (p6 : Fin N) (l6 : Fin M), I p6 l6 → ∃ L6 : List (ℕ × ℕ), (∃ (j6 : ℕ) (La6 Lb6 : List (ℕ × ℕ)), j6 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ a24_Rr n C (n + j6) C.output ∧ a24_Tt n C ((PEqualNP.MetaComplexity.NestedCover.gateAt C j6).inputs.getD 0 0) La6 ∧ a24_Tt n C ((PEqualNP.MetaComplexity.NestedCover.gateAt C j6).inputs.getD 1 0) Lb6 ∧ L6 = La6 ++ Lb6) ∧ (∀ g6 ∈ L6, g6.2 = pw p6 ∨ g6.2 = lw l6) ∧ (L6.filter (fun e6 => decide (e6.2 = pw p6))).length ∈ ({1, 2} : Finset ℕ) ∧ (L6.filter (fun f6 => decide (f6.2 = lw l6))).length ∈ ({1, 2} : Finset ℕ))) :
    {ei : Fin N × Fin M | I ei.1 ei.2}.ncard ≤ 96 * C.gates.length := by
  have hS : a24_Sys n C N M pw lw I (fun P Y w =>
      a24_W n C (fun k : Fin n => decide (k.val ∈ P.image pw ∪ Y.image lw)) w = true) := by
    refine ⟨hAO, hpw, hlw, hpn, hln, h4, ?_, ?_, ?_, ?_, ?_⟩
    · intro P Y x hx
      show a24_W n C _ (pw x) = true
      rw [a24_W_input n C _ (pw x) (hpn x)]
      exact decide_eq_true (Finset.mem_union_left _ (Finset.mem_image_of_mem pw hx))
    · intro P Y y hy
      show a24_W n C _ (lw y) = true
      rw [a24_W_input n C _ (lw y) (hln y)]
      exact decide_eq_true (Finset.mem_union_right _ (Finset.mem_image_of_mem lw hy))
    · intro P Y a b h ha
      exact a24_path_up n C _ a b h ha
    · intro P Y j hj h0 h1
      rw [a24_inp_false] at h0
      rw [a24_inp_true] at h1
      exact a24_and_up n C _ hAO j hj.1 hj.2 h0 h1
    · intro P Y hP hY h
      by_contra hcon
      have hno : ∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3 :=
        fun p3 hp3 l3 hl3 hI => hcon ⟨p3, hp3, l3, hl3, hI⟩
      have h2 := hsound P Y hP hY hno
      have h1 : PEqualNP.MetaComplexity.circuitFun n C
          (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)) = true := h
      rw [h1] at h2
      exact Bool.noConfusion h2
  have hbA := a24_half hS
  have hbB := a24_half (a24_Sys_swap hS)
  have hE1 : {e : Fin N × Fin M | I e.1 e.2 ∧
      a24_Prim n C (a24_GPf n C pw I e.1 e.2) (a24_GLf n C lw I e.1 e.2)}.ncard ≤
      24 * (a24_KA C).card + 19 * (a24_KO C).card := a24_Bd_ncard hbA
  have conv : ∀ e : Fin N × Fin M,
      (I e.1 e.2 ∧ a24_Prim n C (a24_GLf n C lw I e.1 e.2) (a24_GPf n C pw I e.1 e.2)) →
      ((fun (y : Fin M) (x : Fin N) => I x y) e.swap.1 e.swap.2 ∧
        a24_Prim n C (a24_GPf n C lw (fun (y : Fin M) (x : Fin N) => I x y) e.swap.1 e.swap.2)
          (a24_GLf n C pw (fun (y : Fin M) (x : Fin N) => I x y) e.swap.1 e.swap.2)) :=
    fun e he => he
  have hE2 : {e : Fin N × Fin M | I e.1 e.2 ∧
      a24_Prim n C (a24_GLf n C lw I e.1 e.2) (a24_GPf n C pw I e.1 e.2)}.ncard ≤
      24 * (a24_KA C).card + 19 * (a24_KO C).card := a24_Bd_ncard (a24_Bd_mono conv (a24_Bd_swap hbB))
  have key : ∀ S : Set (Fin N × Fin M), (∀ e ∈ S,
      e ∈ {e : Fin N × Fin M | I e.1 e.2 ∧
        a24_Prim n C (a24_GPf n C pw I e.1 e.2) (a24_GLf n C lw I e.1 e.2)} ∪
      {e : Fin N × Fin M | I e.1 e.2 ∧
        a24_Prim n C (a24_GLf n C lw I e.1 e.2) (a24_GPf n C pw I e.1 e.2)}) →
      S.ncard ≤ 2 * (24 * (a24_KA C).card + 19 * (a24_KO C).card) := by
    intro S hsub
    have h1 := Set.ncard_le_ncard (fun e he => hsub e he) (Set.toFinite _)
    have h2 := Set.ncard_union_le {e : Fin N × Fin M | I e.1 e.2 ∧
        a24_Prim n C (a24_GPf n C pw I e.1 e.2) (a24_GLf n C lw I e.1 e.2)}
      {e : Fin N × Fin M | I e.1 e.2 ∧
        a24_Prim n C (a24_GLf n C lw I e.1 e.2) (a24_GPf n C pw I e.1 e.2)}
    omega
  have hOR : {jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or}.ncard =
      (a24_orS C).card := by
    have hset : {jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or} =
        ((a24_orS C : Finset ℕ) : Set ℕ) := by
      ext j
      simp only [Set.mem_setOf_eq, Finset.mem_coe, a24_mem_orS, a24_OrG]
    rw [hset, Set.ncard_coe_finset]
  have h10 := a24_l2410 n N M pw lw I C hAO hpw hlw hne hpn hln h4 hsound (a24_Rr n C) rfl (a24_Tt n C) rfl
    hread
  have hfin : 4 * {jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or}.ncard +
      2 * (24 * (a24_KA C).card + 19 * (a24_KO C).card) ≤ 96 * C.gates.length := by
    have a := a24_card_KA C
    have b := a24_card_KO C
    have c := a24_and_or_card hAO
    rw [hOR]
    omega
  refine le_trans h10 (le_trans (Nat.add_le_add_left (key _ ?_) _) hfin)
  intro e he
  obtain ⟨hI, hn7, hn9⟩ := he
  obtain ⟨L6, ⟨j6, La, a24_Lb, hj6, hop6, hR6, hTa, hTb, hL⟩, hvars, hcp, hcl⟩ := hread e.1 e.2 hI
  subst hL
  have hleaf : ∀ g ∈ La ++ a24_Lb, a24_Rr n C g.2 g.1 := by
    intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact a24_Tt_leafR hTa g h
    · exact a24_Tt_leafR hTb g h
  have hk : a24_LOK (pw e.1) (lw e.2) (a24_GPf n C pw I e.1 e.2) (a24_GLf n C lw I e.1 e.2) (La ++ a24_Lb) := by
    intro g hg
    have hRg := hleaf g hg
    rcases hvars g hg with h | h
    · left
      refine ⟨h, ?_, ?_⟩
      · rw [← h]
        exact hRg
      · by_cases hd : ∃ q, a24_Rr n C (pw q) g.1 ∧ ¬ I q e.2
        · exact Or.inr hd
        · left
          intro x hx
          by_contra hxp
          apply hn7
          refine ⟨La ++ a24_Lb, ⟨j6, La, a24_Lb, hj6, hop6, hR6, hTa, hTb, rfl⟩, hvars, hcp, hcl, g, hg,
            h, ?_, ?_⟩
          · intro q8 hq8
            by_contra hnI
            exact hd ⟨q8, hq8, hnI⟩
          · have hsub : ({x, e.1} : Set (Fin N)) ⊆ {r8 : Fin N | a24_Rr n C (pw r8) g.1} := by
              intro r hr
              rcases Set.mem_insert_iff.mp hr with h' | h'
              · rw [h']
                exact hx
              · rw [Set.mem_singleton_iff.mp h']
                show a24_Rr n C (pw e.1) g.1
                rw [← h]
                exact hRg
            calc 2 = ({x, e.1} : Set (Fin N)).ncard := (Set.ncard_pair hxp).symm
              _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
    · right
      refine ⟨h, ?_, ?_⟩
      · rw [← h]
        exact hRg
      · by_cases hd : ∃ y, a24_Rr n C (lw y) g.1 ∧ ¬ I e.1 y
        · exact Or.inr hd
        · left
          intro x hx
          by_contra hxp
          apply hn9
          refine ⟨La ++ a24_Lb, ⟨j6, La, a24_Lb, hj6, hop6, hR6, hTa, hTb, rfl⟩, hvars, hcp, hcl, g, hg,
            h, ?_, ?_⟩
          · intro q8 hq8
            by_contra hnI
            exact hd ⟨q8, hq8, hnI⟩
          · have hsub : ({x, e.2} : Set (Fin M)) ⊆ {r8 : Fin M | a24_Rr n C (lw r8) g.1} := by
              intro r hr
              rcases Set.mem_insert_iff.mp hr with h' | h'
              · rw [h']
                exact hx
              · rw [Set.mem_singleton_iff.mp h']
                show a24_Rr n C (lw e.2) g.1
                rw [← h]
                exact hRg
            calc 2 = ({x, e.2} : Set (Fin M)).ncard := (Set.ncard_pair hxp).symm
              _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hcp' : a24_cnt (pw e.1) (La ++ a24_Lb) = 1 ∨ a24_cnt (pw e.1) (La ++ a24_Lb) = 2 := by
    have h := hcp
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    exact h
  have hcl' : a24_cnt (lw e.2) (La ++ a24_Lb) = 1 ∨ a24_cnt (lw e.2) (La ++ a24_Lb) = 2 := by
    have h := hcl
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    exact h
  have hprim := a24_prim_of_tree (hne e.1 e.2) j6 ⟨hj6, hop6⟩ hR6 La a24_Lb
    (by rw [a24_inp_false]; exact hTa) (by rw [a24_inp_true]; exact hTb) hk hcp' hcl'
  rcases hprim with h | h
  · exact Or.inl ⟨hI, h⟩
  · exact Or.inr ⟨hI, h⟩

theorem l2424 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → Function.Injective pw → Function.Injective lw → (∀ (p1 : Fin N) (l1 : Fin M), pw p1 ≠ lw l1) → (∀ p2 : Fin N, pw p2 < n) → (∀ l2 : Fin M, lw l2 < n) → (∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 → ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5)) → (∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2 → (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) → PEqualNP.MetaComplexity.circuitFun n C (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)) = false) → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → ∀ T : ℕ → List (ℕ × ℕ) → Prop, T = (fun tt tL => ∀ Q : ℕ → List (ℕ × ℕ) → Prop, (∀ (qv qt : ℕ), qv < n → R qv qt → Q qt [(qt, qv)]) → (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C qj).op = PEqualNP.CircuitLowerBounds.GateOp.and → R (n + qj) qt → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 0 0) qL1 → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 1 0) qL2 → Q qt (qL1 ++ qL2)) → Q tt tL) → (∀ (p6 : Fin N) (l6 : Fin M), I p6 l6 → ∃ L6 : List (ℕ × ℕ), (∃ (j6 : ℕ) (La6 Lb6 : List (ℕ × ℕ)), j6 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ R (n + j6) C.output ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j6).inputs.getD 0 0) La6 ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j6).inputs.getD 1 0) Lb6 ∧ L6 = La6 ++ Lb6) ∧ (∀ g6 ∈ L6, g6.2 = pw p6 ∨ g6.2 = lw l6) ∧ (L6.filter (fun e6 => decide (e6.2 = pw p6))).length ∈ ({1, 2} : Finset ℕ) ∧ (L6.filter (fun f6 => decide (f6.2 = lw l6))).length ∈ ({1, 2} : Finset ℕ)) → {ei : Fin N × Fin M | I ei.1 ei.2}.ncard ≤ 112 * C.size := by
  intro n N M pw lw I C hAO hpw hlw hne hpn hln h4 hsound R hR T hT hread
  subst hR
  subst hT
  have h := a24_core n N M pw lw I C hAO hpw hlw hne hpn hln h4 hsound hread
  show _ ≤ 112 * C.gates.length
  omega


end



theorem main_aux : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ p1 l1 : Fin N, I p1 l1 → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k1 => decide (k1 = Fin.castAdd N p1 ∨ k1 = Fin.natAdd N l1)) = true) → (∀ z : Fin (N + N) → Bool, (Finset.univ.filter (fun p2 : Fin N => z (Fin.castAdd N p2) = true)).card ≤ 2 → (Finset.univ.filter (fun l2 : Fin N => z (Fin.natAdd N l2) = true)).card ≤ 2 → (¬ ∃ p3 l3 : Fin N, I p3 l3 ∧ z (Fin.castAdd N p3) = true ∧ z (Fin.natAdd N l3) = true) → PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) → (∀ p4 l4 : Fin N, I p4 l4 → PEqualNP.ReadK.readsAtMost C (N + N) [p4.val, N + l4.val] 2 = true) → N * q ≤ 100 * C.size := by
  intro q N I instI C hq hN hline huniq hAO htrue hsound hread
  have hzP : ∀ (P : Finset (Fin N)) (Y : Finset (Fin N)) (p : Fin N),
      decide ((Fin.castAdd N p).val ∈ P.image (fun pv : Fin N => pv.val) ∪
        Y.image (fun lv : Fin N => N + lv.val)) = true → p ∈ P := by
    intro P Y p hp
    have hpm := of_decide_eq_true hp
    rcases Finset.mem_union.mp hpm with h | h
    · obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp h
      have h1 : x.val = p.val := hxe
      have h2 : x = p := Fin.ext h1
      rw [← h2]
      exact hx
    · obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp h
      exfalso
      have h1 : N + x.val = p.val := hxe
      have h2 := p.isLt
      omega
  have hzL : ∀ (P : Finset (Fin N)) (Y : Finset (Fin N)) (l : Fin N),
      decide ((Fin.natAdd N l).val ∈ P.image (fun pv : Fin N => pv.val) ∪
        Y.image (fun lv : Fin N => N + lv.val)) = true → l ∈ Y := by
    intro P Y l hl
    have hlm := of_decide_eq_true hl
    rcases Finset.mem_union.mp hlm with h | h
    · obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp h
      exfalso
      have h1 : x.val = N + l.val := hxe
      have h2 := x.isLt
      omega
    · obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp h
      have h1 : N + x.val = N + l.val := hxe
      have h2 : x = l := Fin.ext (by omega)
      rw [← h2]
      exact hx
  have hsnd : ∀ (P : Finset (Fin N)) (Y : Finset (Fin N)), P.card ≤ 2 → Y.card ≤ 2 →
      (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) →
      PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k3 : Fin (N + N) =>
        decide (k3.val ∈ P.image (fun pv : Fin N => pv.val) ∪
          Y.image (fun lv : Fin N => N + lv.val))) = false := by
    intro P Y hP hY hno
    refine hsound _ ?_ ?_ ?_
    · refine le_trans (Finset.card_le_card ?_) hP
      intro p hp
      exact hzP P Y p (Finset.mem_filter.mp hp).2
    · refine le_trans (Finset.card_le_card ?_) hY
      intro l hl
      exact hzL P Y l (Finset.mem_filter.mp hl).2
    · rintro ⟨p3, l3, hI, h1, h2⟩
      exact hno p3 (hzP P Y p3 h1) l3 (hzL P Y l3 h2) hI
  have h4 : ∀ (p4 p5 : Fin N) (l4 l5 : Fin N), p4 ≠ p5 → l4 ≠ l5 →
      ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5) := by
    intro p4 p5 l4 l5 hp hl hh
    exact hl ((huniq p4 p5 hp).unique ⟨hh.1, hh.2.1⟩ ⟨hh.2.2.1, hh.2.2.2⟩)
  have hinj1 : Function.Injective (fun pv : Fin N => pv.val) := Fin.val_injective
  have hinj2 : Function.Injective (fun lv : Fin N => N + lv.val) := by
    intro a b h
    apply Fin.ext
    have h' : N + a.val = N + b.val := h
    omega
  have hz1 : ∀ p : Fin N, PEqualNP.MetaComplexity.circuitFun (N + N) C
      (fun k1 : Fin (N + N) => decide (k1.val = p.val)) = false := by
    intro p
    refine hsound _ ?_ ?_ ?_
    · refine le_trans (Finset.card_le_card (t := {p}) ?_) (by simp)
      intro p2 hp2
      have h := of_decide_eq_true (Finset.mem_filter.mp hp2).2
      have h1 : p2.val = p.val := h
      exact Finset.mem_singleton.mpr (Fin.ext h1)
    · refine le_trans (Finset.card_le_card (t := ∅) ?_) (by simp)
      intro l2 hl2
      exfalso
      have h := of_decide_eq_true (Finset.mem_filter.mp hl2).2
      have h1 : N + l2.val = p.val := h
      have h2 := p.isLt
      omega
    · rintro ⟨p3, l3, _, _, h2⟩
      have h := of_decide_eq_true h2
      have h1 : N + l3.val = p.val := h
      have h3 := p.isLt
      omega
  have hz2 : ∀ l : Fin N, PEqualNP.MetaComplexity.circuitFun (N + N) C
      (fun k2 : Fin (N + N) => decide (k2.val = N + l.val)) = false := by
    intro l
    refine hsound _ ?_ ?_ ?_
    · refine le_trans (Finset.card_le_card (t := ∅) ?_) (by simp)
      intro p2 hp2
      exfalso
      have h := of_decide_eq_true (Finset.mem_filter.mp hp2).2
      have h1 : p2.val = N + l.val := h
      have h2 := p2.isLt
      omega
    · refine le_trans (Finset.card_le_card (t := {l}) ?_) (by simp)
      intro l2 hl2
      have h := of_decide_eq_true (Finset.mem_filter.mp hl2).2
      have h1 : N + l2.val = N + l.val := h
      exact Finset.mem_singleton.mpr (Fin.ext (by omega))
    · rintro ⟨p3, l3, _, h2, _⟩
      have h := of_decide_eq_true h2
      have h1 : p3.val = N + l.val := h
      have h3 := p3.isLt
      omega
  have hcore := a24_core (N + N) N N (fun pv : Fin N => pv.val) (fun lv : Fin N => N + lv.val) I C
    hAO hinj1 hinj2
    (fun p1 l1 => by
      have h1 := p1.isLt
      show p1.val ≠ N + l1.val
      omega)
    (fun p2 => by
      have h1 := p2.isLt
      show p2.val < N + N
      omega)
    (fun l2 => by
      have h1 := l2.isLt
      show N + l2.val < N + N
      omega)
    h4 hsnd
    (fun p6 l6 hI => (l2350 (N + N) C p6.val (N + l6.val) hAO
      (by have h1 := p6.isLt; omega) (by have h1 := l6.isLt; omega)
      (by have h1 := p6.isLt; omega) (hz1 p6) (hz2 l6)
      (a24_Rr (N + N) C) rfl (a24_Tt (N + N) C) rfl).2 (hread p6 l6 hI))
  have hcount : N * (q + 1) ≤ {ei : Fin N × Fin N | I ei.1 ei.2}.ncard := by
    have hfin : {ei : Fin N × Fin N | I ei.1 ei.2}.Finite := Set.toFinite _
    rw [Set.ncard_eq_toFinset_card _ hfin]
    have hs : ((Finset.univ : Finset (Fin N)).sigma
        (fun l => Finset.univ.filter (fun p => I p l))).card = N * (q + 1) := by
      rw [Finset.card_sigma]
      simp only [hline]
      simp
    rw [← hs]
    refine Finset.card_le_card_of_injOn (fun x => (x.2, x.1)) ?_ ?_
    · intro x hx
      have h := (Finset.mem_sigma.mp hx).2
      exact (Set.Finite.mem_toFinset hfin).mpr (Finset.mem_filter.mp h).2
    · intro x _ y _ hxy
      have h1 : x.2 = y.2 := congrArg Prod.fst hxy
      have h2 : x.1 = y.1 := congrArg Prod.snd hxy
      exact Sigma.ext h2 (heq_of_eq h1)
  show N * q ≤ 100 * C.gates.length
  have h5 : N * q ≤ N * (q + 1) := Nat.mul_le_mul_left N (by omega)
  omega

end PEqualNP.Outside.L_meta_2673

theorem PEqualNP.Outside.L_meta_2673 : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ p1 l1 : Fin N, I p1 l1 → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k1 => decide (k1 = Fin.castAdd N p1 ∨ k1 = Fin.natAdd N l1)) = true) → (∀ z : Fin (N + N) → Bool, (Finset.univ.filter (fun p2 : Fin N => z (Fin.castAdd N p2) = true)).card ≤ 2 → (Finset.univ.filter (fun l2 : Fin N => z (Fin.natAdd N l2) = true)).card ≤ 2 → (¬ ∃ p3 l3 : Fin N, I p3 l3 ∧ z (Fin.castAdd N p3) = true ∧ z (Fin.natAdd N l3) = true) → PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) → (∀ p4 l4 : Fin N, I p4 l4 → PEqualNP.ReadK.readsAtMost C (N + N) [p4.val, N + l4.val] 2 = true) → N * q ≤ 100 * C.size :=
  PEqualNP.Outside.L_meta_2673.main_aux
