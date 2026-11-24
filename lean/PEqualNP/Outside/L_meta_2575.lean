import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2575


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def s2230_stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma s2230_wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl s2230_stepWire x := rfl

lemma s2230_foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl s2230_stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [s2230_stepWire]
    omega

lemma s2230_foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl s2230_stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (s2230_stepWire w g).length := by simp [s2230_stepWire]; omega
    rw [ih (s2230_stepWire w g) hlt]
    simp [s2230_stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma s2230_getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma s2230_wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [s2230_wires_eq_foldl, s2230_foldl_stepWire_length, List.length_ofFn]

lemma s2230_split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]


def s2230_W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma s2230_gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma s2230_W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    s2230_W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then s2230_W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := s2230_split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [s2230_gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl s2230_stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, s2230_foldl_stepWire_length, hpre_len]
  have hCj : s2230_W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [s2230_W]
    rw [s2230_wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [s2230_foldl_stepWire_getD_lt post (s2230_stepWire w0 gj) (n + k) (by simp [s2230_stepWire]; omega)]
    simp [s2230_stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [s2230_W]
    rw [s2230_wires_eq_foldl, hgs, List.foldl_append]
    exact (s2230_foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact s2230_getD_ge_length w0 i (by omega)

lemma s2230_W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    s2230_W n C x u = x ⟨u, hu⟩ := by
  simp only [s2230_W]
  rw [s2230_wires_eq_foldl, s2230_foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

open PEqualNP.CleanedNonEdge in
lemma s2230_orFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

open PEqualNP.CleanedNonEdge in
lemma s2230_orStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
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
lemma s2230_orStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.CleanedNonEdge in
lemma s2230_orFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact s2230_orStep_getD_lt n cs g k hk

open PEqualNP.CleanedNonEdge in
lemma s2230_orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ x ∈ (orSets n C).getD (w - n) []) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := s2230_split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [s2230_gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [s2230_orFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : (orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k [] := by
    rw [hc, s2230_orFold_getD_lt n post _ k (by omega)]
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, s2230_orFold_getD_lt n post _ m (by omega)]
    exact s2230_orStep_getD_lt n _ gk m (by omega)
  have h3 := s2230_orStep_mem_last n (pre.foldl (orStep n) []) gk x
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

lemma s2230_orReaches_self (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    OrReaches n C (n + j) j := by
  unfold OrReaches
  refine ⟨Nat.le_add_right n j, ?_⟩
  rw [Nat.add_sub_cancel_left, s2230_orSets_mem_iff n C j j hj]
  exact Or.inl rfl

lemma s2230_orReaches_step (n : ℕ) (C : Circuit) (j i g : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : OrReaches n C i g) : OrReaches n C (n + j) g := by
  unfold OrReaches at h ⊢
  refine ⟨Nat.le_add_right n j, ?_⟩
  rw [Nat.add_sub_cancel_left, s2230_orSets_mem_iff n C j g hj]
  exact Or.inr ⟨hop, i, hi, h.1, hlt, h.2⟩

lemma s2230_mem_filter_iff_gen {α : Type} (p : α → Prop) (d : DecidablePred p) (s : Finset α) (a : α) :
    a ∈ @Finset.filter α p d s ↔ a ∈ s ∧ p a :=
  @Finset.mem_filter α p d s a

lemma s2230_mem_orIn (n : ℕ) (C : Circuit) (w : ℕ) (i : Fin n) :
    i ∈ orIn n C w ↔ ((i : ℕ) = w ∨ ∃ k < C.gates.length,
      OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧ (i : ℕ) ∈ (gateAt C k).inputs) := by
  unfold orIn
  exact ⟨fun h => ((s2230_mem_filter_iff_gen _ _ _ _).1 h).2,
    fun h => (s2230_mem_filter_iff_gen _ _ _ _).2 ⟨Finset.mem_univ _, h⟩⟩

lemma s2230_orIn_up (n : ℕ) (C : Circuit) (j i : ℕ) (a : Fin n) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : a ∈ orIn n C i) : a ∈ orIn n C (n + j) := by
  rw [s2230_mem_orIn] at h ⊢
  right
  rcases h with h | ⟨k, hk, hr, hopk, hin⟩
  · exact ⟨j, hj, s2230_orReaches_self n C j hj, hop, by rw [h]; exact hi⟩
  · exact ⟨k, hk, s2230_orReaches_step n C j i k hj hop hi hlt hr, hopk, hin⟩

def s2230_FR (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) : List (List ℕ) :=
  match g.op with
  | GateOp.or => (g.inputs.map fun i => R.getD i []).foldl (fun acc A => A.foldl insertNew acc) []
  | GateOp.and => (g.inputs.map fun i => R.getD i []).foldl (andStep k) [S.map fun _ => 0]
  | _ => []

def s2230_stepR (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) : List (List (List ℕ)) :=
  R ++ [s2230_FR S k R g]

lemma s2230_readVectors_eq (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) :
    readVectors C n S k = C.gates.foldl (s2230_stepR S k) ((List.range n).map (leafVectors S k)) := by
  first
    | rfl
    | (unfold readVectors; congr 1; funext R g; rcases g with ⟨op, ins⟩; cases op <;> rfl)

lemma s2230_FR_or (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) (h : g.op = GateOp.or) :
    s2230_FR S k R g =
      (g.inputs.map fun i => R.getD i []).foldl (fun acc A => A.foldl insertNew acc) [] := by
  obtain ⟨op, ins⟩ := g
  have h2 : op = GateOp.or := h
  subst h2
  rfl

lemma s2230_FR_and (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate)
    (h : g.op = GateOp.and) :
    s2230_FR S k R g = (g.inputs.map fun i => R.getD i []).foldl (andStep k) [S.map fun _ => 0] := by
  obtain ⟨op, ins⟩ := g
  have h2 : op = GateOp.and := h
  subst h2
  rfl

lemma s2230_foldR_length (S : List ℕ) (k : ℕ) (gs : List Gate) (R : List (List (List ℕ))) :
    (gs.foldl (s2230_stepR S k) R).length = R.length + gs.length := by
  induction gs generalizing R with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [s2230_stepR]
    omega

lemma s2230_foldR_getD_lt (S : List ℕ) (k : ℕ) (gs : List Gate) (R : List (List (List ℕ))) (i : ℕ)
    (hi : i < R.length) : (gs.foldl (s2230_stepR S k) R).getD i [] = R.getD i [] := by
  induction gs generalizing R with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (s2230_stepR S k R g).length := by simp [s2230_stepR]; omega
    rw [ih (s2230_stepR S k R g) hlt]
    simp [s2230_stepR, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

def s2230_RV (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (w : ℕ) : List (List ℕ) :=
  (readVectors C n S k).getD w []

lemma s2230_RV_input (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (w : ℕ) (hw : w < n) :
    s2230_RV C n S k w = leafVectors S k w := by
  simp only [s2230_RV]
  rw [s2230_readVectors_eq, s2230_foldR_getD_lt S k C.gates ((List.range n).map (leafVectors S k)) w
    (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

lemma s2230_RV_gate (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (j : ℕ) (hj : j < C.gates.length) :
    ∃ Rp : List (List (List ℕ)),
      (∀ i, i < n + j → Rp.getD i [] = s2230_RV C n S k i) ∧
      s2230_RV C n S k (n + j) = s2230_FR S k Rp (gateAt C j) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := s2230_split_gates C.gates j hj
  have hga : gateAt C j = gj := by rw [s2230_gateAt_eq C j hj]; exact hgj
  rw [hga]
  obtain ⟨Rp, hRp⟩ : ∃ Rp, Rp = pre.foldl (s2230_stepR S k) ((List.range n).map (leafVectors S k)) :=
    ⟨_, rfl⟩
  have hlen : Rp.length = n + j := by
    rw [hRp, s2230_foldR_length]
    simp only [List.length_map, List.length_range, hpre_len]
  have hall : readVectors C n S k = post.foldl (s2230_stepR S k) (s2230_stepR S k Rp gj) := by
    rw [s2230_readVectors_eq, hgs, List.foldl_append, List.foldl_cons, hRp]
  have hlen1 : (s2230_stepR S k Rp gj).length = n + j + 1 := by
    simp [s2230_stepR, hlen]
  refine ⟨Rp, ?_, ?_⟩
  · intro i hi
    simp only [s2230_RV]
    rw [hall, s2230_foldR_getD_lt S k post (s2230_stepR S k Rp gj) i (by omega)]
    simp [s2230_stepR, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (show i < Rp.length by omega)]
  · simp only [s2230_RV]
    rw [hall, s2230_foldR_getD_lt S k post (s2230_stepR S k Rp gj) (n + j) (by omega)]
    simp [s2230_stepR, List.getD_eq_getElem?_getD, hlen]

lemma s2230_mem_foldl_insertNew (L : List (List ℕ)) (acc : List (List ℕ)) (v : List ℕ)
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

lemma s2230_mem_andStep (k : ℕ) (A B : List (List ℕ)) (v : List ℕ) (h : v ∈ andStep k A B) :
    ∃ u ∈ A, ∃ u2 ∈ B, v = capAdd k u u2 := by
  unfold andStep at h
  rcases s2230_mem_foldl_insertNew _ _ _ h with h1 | h1
  · simp at h1
  · simp only [List.mem_flatMap, List.mem_map] at h1
    obtain ⟨u, hu, u2, hu2, rfl⟩ := h1
    exact ⟨u, hu, u2, hu2, rfl⟩

lemma s2230_capAdd_pair (k x1 y1 x2 y2 : ℕ) :
    capAdd k [x1, y1] [x2, y2] = [min (x1 + x2) (k + 1), min (y1 + y2) (k + 1)] := by
  first
    | rfl
    | simp [capAdd]

lemma s2230_leaf_eq (a b w : ℕ) :
    leafVectors [a, b] 1 w =
      if w ∈ [a, b] then [[if a = w then 1 else 0, if b = w then 1 else 0]] else [] := by
  first
    | rfl
    | (unfold leafVectors; simp)

theorem cor_setList_pair {n : ℕ} (a b : Fin n) (hab : a < b) :
    PEqualNP.ReadK.setList ({a, b} : Finset (Fin n)) = [a.val, b.val] := by
  have key : ∀ x y : Fin n, x < y → y < x → x = y :=
    fun x y h1 h2 => absurd h1 (lt_asymm h2)
  have hp1 : List.Pairwise (fun x y : Fin n => x < y)
      ((List.finRange n).filter (fun i => decide (i ∈ ({a, b} : Finset (Fin n))))) :=
    List.Pairwise.filter _ (List.pairwise_lt_finRange n)
  have hp2 : List.Pairwise (fun x y : Fin n => x < y) [a, b] := by
    simp [hab]
  have hperm : List.Perm
      ((List.finRange n).filter (fun i => decide (i ∈ ({a, b} : Finset (Fin n))))) [a, b] := by
    apply List.perm_of_nodup_nodup_toFinset_eq
    · exact List.Nodup.filter _ (List.nodup_finRange n)
    · simp [ne_of_lt hab]
    · ext x
      simp
  have h : (List.finRange n).filter (fun i => decide (i ∈ ({a, b} : Finset (Fin n)))) = [a, b] :=
    List.Perm.eq_of_pairwise (fun x y _ _ => key x y) hp1 hp2 hperm
  unfold PEqualNP.ReadK.setList
  rw [h]
  rfl


lemma u_W_or2 (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k a b : ℕ) (hk : k < C.gates.length)
    (hg : gateAt C k = ⟨GateOp.or, [a, b]⟩) (ha : a < n + k) (hb : b < n + k) :
    s2230_W n C x (n + k) = (s2230_W n C x a || s2230_W n C x b) := by
  rw [s2230_W_gate n C x k hk, hg]
  simp [GateOp.eval, ha, hb]

lemma u_W_and2 (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k a b : ℕ) (hk : k < C.gates.length)
    (hg : gateAt C k = ⟨GateOp.and, [a, b]⟩) (ha : a < n + k) (hb : b < n + k) :
    s2230_W n C x (n + k) = (s2230_W n C x a && s2230_W n C x b) := by
  rw [s2230_W_gate n C x k hk, hg]
  simp [GateOp.eval, ha, hb]

lemma u_mem_foldl_insertNew (L acc : List (List ℕ)) (v : List ℕ) (h : v ∈ acc ∨ v ∈ L) :
    v ∈ L.foldl insertNew acc := by
  induction L generalizing acc with
  | nil =>
    rcases h with h | h
    · exact h
    · simp at h
  | cons y L ih =>
    rw [List.foldl_cons]
    apply ih
    rcases h with h | h
    · left
      unfold insertNew
      split_ifs
      · exact h
      · exact List.mem_append_left _ h
    · rcases List.mem_cons.mp h with h1 | h1
      · left
        unfold insertNew
        split_ifs with hc
        · rw [h1]
          exact hc
        · rw [h1]
          exact List.mem_append_right _ (List.mem_singleton_self y)
      · right
        exact h1

lemma u_mem_andStep (k : ℕ) (A B : List (List ℕ)) (u u2 : List ℕ) (hu : u ∈ A) (hu2 : u2 ∈ B) :
    capAdd k u u2 ∈ andStep k A B := by
  unfold andStep
  apply u_mem_foldl_insertNew
  right
  simp only [List.mem_flatMap, List.mem_map]
  exact ⟨u, hu, u2, hu2, rfl⟩

lemma u_RV_or2 (C : Circuit) (n : ℕ) (S : List ℕ) (k j a b : ℕ) (hj : j < C.gates.length)
    (hg : gateAt C j = ⟨GateOp.or, [a, b]⟩) (ha : a < n + j) (hb : b < n + j) (v : List ℕ)
    (hv : v ∈ s2230_RV C n S k a ∨ v ∈ s2230_RV C n S k b) :
    v ∈ s2230_RV C n S k (n + j) := by
  obtain ⟨Rp, hRp, hEq⟩ := s2230_RV_gate C n S k j hj
  have hop : (gateAt C j).op = GateOp.or := by simp [hg]
  rw [hEq, s2230_FR_or S k Rp (gateAt C j) hop, hg]
  show v ∈ ([a, b].map fun i => Rp.getD i []).foldl (fun acc A => A.foldl insertNew acc) []
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
  rw [hRp a ha, hRp b hb]
  apply u_mem_foldl_insertNew
  rcases hv with hv | hv
  · left
    exact u_mem_foldl_insertNew _ _ _ (Or.inr hv)
  · right
    exact hv

lemma u_RV_and2 (C : Circuit) (n : ℕ) (S : List ℕ) (k j a b : ℕ) (hj : j < C.gates.length)
    (hg : gateAt C j = ⟨GateOp.and, [a, b]⟩) (ha : a < n + j) (hb : b < n + j) (u u2 : List ℕ)
    (hu : u ∈ s2230_RV C n S k a) (hu2 : u2 ∈ s2230_RV C n S k b) :
    capAdd k (capAdd k (S.map fun _ => 0) u) u2 ∈ s2230_RV C n S k (n + j) := by
  obtain ⟨Rp, hRp, hEq⟩ := s2230_RV_gate C n S k j hj
  have hop : (gateAt C j).op = GateOp.and := by simp [hg]
  rw [hEq, s2230_FR_and S k Rp (gateAt C j) hop, hg]
  show capAdd k (capAdd k (S.map fun _ => 0) u) u2 ∈
    ([a, b].map fun i => Rp.getD i []).foldl (andStep k) [S.map fun _ => 0]
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
  rw [hRp a ha, hRp b hb]
  exact u_mem_andStep k _ _ _ _
    (u_mem_andStep k _ _ _ _ (List.mem_singleton_self _) hu) hu2

lemma u_leaf_a (a b : ℕ) (hab : a ≠ b) : leafVectors [a, b] 2 a = [[1, 0]] := by
  first
    | simp [leafVectors, hab.symm]
    | (unfold leafVectors; simp [hab.symm])

lemma u_leaf_b (a b : ℕ) (hab : a ≠ b) : leafVectors [a, b] 2 b = [[0, 1]] := by
  first
    | simp [leafVectors, hab]
    | (unfold leafVectors; simp [hab])

/-- The gate number j of the line star: for each line a block of q + 1 gates (q OR gates over its
points, then the AND with the line input), then N - 1 OR gates joining the line terms. -/
def u_Gf (q N : ℕ) (pt : ℕ → ℕ → ℕ) (j : ℕ) : Gate :=
  if j < N * (q + 1) then
    (if j % (q + 1) = 0 then ⟨GateOp.or, [pt (j / (q + 1)) 0, pt (j / (q + 1)) 1]⟩
     else if j % (q + 1) = q then ⟨GateOp.and, [N + N + (j - 1), N + j / (q + 1)]⟩
     else ⟨GateOp.or, [N + N + (j - 1), pt (j / (q + 1)) (j % (q + 1) + 1)]⟩)
  else
    (if j = N * (q + 1) then ⟨GateOp.or, [N + N + q, N + N + (q + 1 + q)]⟩
     else ⟨GateOp.or, [N + N + (j - 1), N + N + ((j - N * (q + 1) + 1) * (q + 1) + q)]⟩)

def u_D (q N : ℕ) (pt : ℕ → ℕ → ℕ) : Circuit :=
  ⟨(List.range (N * (q + 1) + (N - 1))).map (u_Gf q N pt), N + N + (N * (q + 1) + (N - 2))⟩

lemma u_len (q N : ℕ) (pt : ℕ → ℕ → ℕ) :
    (u_D q N pt).gates.length = N * (q + 1) + (N - 1) := by
  simp [u_D]

lemma u_gateAt (q N : ℕ) (pt : ℕ → ℕ → ℕ) (j : ℕ) (hj : j < N * (q + 1) + (N - 1)) :
    gateAt (u_D q N pt) j = u_Gf q N pt j := by
  have hk : j < (u_D q N pt).gates.length := by
    rw [u_len]
    exact hj
  first
    | simp [gateAt, u_D, List.getD_eq_getElem?_getD, hj]
    | (rw [s2230_gateAt_eq _ j hk]; simp [u_D])

lemma u_div (q l r : ℕ) (hr : r < q + 1) : (l * (q + 1) + r) / (q + 1) = l := by
  have hpos : 0 < q + 1 := by omega
  rw [Nat.add_comm (l * (q + 1)) r, Nat.add_mul_div_right r l hpos, Nat.div_eq_of_lt hr,
    Nat.zero_add]

lemma u_mod (q l r : ℕ) (hr : r < q + 1) : (l * (q + 1) + r) % (q + 1) = r := by
  rw [Nat.add_comm (l * (q + 1)) r, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]

lemma u_blk (q N l r : ℕ) (hl : l < N) (hr : r < q + 1) : l * (q + 1) + r < N * (q + 1) := by
  have h1 : (l + 1) * (q + 1) ≤ N * (q + 1) := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hl)
  have h2 : (l + 1) * (q + 1) = l * (q + 1) + (q + 1) := Nat.succ_mul l (q + 1)
  omega

lemma u_G0 (q N : ℕ) (pt : ℕ → ℕ → ℕ) (l : ℕ) (hl : l < N) :
    u_Gf q N pt (l * (q + 1)) = ⟨GateOp.or, [pt l 0, pt l 1]⟩ := by
  have h1 := u_blk q N l 0 hl (by omega)
  have h2 := u_div q l 0 (by omega)
  have h3 := u_mod q l 0 (by omega)
  rw [Nat.add_zero] at h1 h2 h3
  unfold u_Gf
  rw [if_pos h1, if_pos h3, h2]

lemma u_G1 (q N : ℕ) (pt : ℕ → ℕ → ℕ) (l r : ℕ) (hl : l < N) (hr0 : 0 < r) (hrq : r < q) :
    u_Gf q N pt (l * (q + 1) + r) =
      ⟨GateOp.or, [N + N + (l * (q + 1) + r - 1), pt l (r + 1)]⟩ := by
  have h1 := u_blk q N l r hl (by omega)
  have h2 := u_div q l r (by omega)
  have h3 := u_mod q l r (by omega)
  have h4 : ¬ ((l * (q + 1) + r) % (q + 1) = 0) := by
    rw [h3]
    omega
  have h5 : ¬ ((l * (q + 1) + r) % (q + 1) = q) := by
    rw [h3]
    omega
  unfold u_Gf
  rw [if_pos h1, if_neg h4, if_neg h5, h2, h3]

lemma u_Gq (q N : ℕ) (pt : ℕ → ℕ → ℕ) (l : ℕ) (hq : 1 ≤ q) (hl : l < N) :
    u_Gf q N pt (l * (q + 1) + q) =
      ⟨GateOp.and, [N + N + (l * (q + 1) + q - 1), N + l]⟩ := by
  have h1 := u_blk q N l q hl (by omega)
  have h2 := u_div q l q (by omega)
  have h3 := u_mod q l q (by omega)
  have h4 : ¬ ((l * (q + 1) + q) % (q + 1) = 0) := by
    rw [h3]
    omega
  unfold u_Gf
  rw [if_pos h1, if_neg h4, if_pos h3, h2]

lemma u_F0 (q N : ℕ) (pt : ℕ → ℕ → ℕ) :
    u_Gf q N pt (N * (q + 1)) = ⟨GateOp.or, [N + N + q, N + N + (q + 1 + q)]⟩ := by
  have h1 : ¬ (N * (q + 1) < N * (q + 1)) := lt_irrefl _
  unfold u_Gf
  rw [if_neg h1, if_pos rfl]

lemma u_Fi (q N : ℕ) (pt : ℕ → ℕ → ℕ) (i : ℕ) (hi : 0 < i) :
    u_Gf q N pt (N * (q + 1) + i) =
      ⟨GateOp.or, [N + N + (N * (q + 1) + i - 1), N + N + ((i + 1) * (q + 1) + q)]⟩ := by
  have h1 : ¬ (N * (q + 1) + i < N * (q + 1)) := by omega
  have h2 : ¬ (N * (q + 1) + i = N * (q + 1)) := by omega
  have h3 : N * (q + 1) + i - N * (q + 1) = i := by omega
  unfold u_Gf
  rw [if_neg h1, if_neg h2, h3]

lemma u_Gf_shape (q N : ℕ) (pt : ℕ → ℕ → ℕ) (j : ℕ) :
    ∃ a b, (u_Gf q N pt j = ⟨GateOp.or, [a, b]⟩ ∨ u_Gf q N pt j = ⟨GateOp.and, [a, b]⟩) := by
  unfold u_Gf
  split_ifs
  all_goals first
    | exact ⟨_, _, Or.inl rfl⟩
    | exact ⟨_, _, Or.inr rfl⟩

lemma u_cases (q N j : ℕ) (hj : j < N * (q + 1) + (N - 1)) :
    (∃ l r, l < N ∧ r < q + 1 ∧ j = l * (q + 1) + r) ∨
      (∃ i, i < N - 1 ∧ j = N * (q + 1) + i) := by
  by_cases h : j < N * (q + 1)
  · left
    refine ⟨j / (q + 1), j % (q + 1), ?_, Nat.mod_lt _ (by omega), ?_⟩
    · exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h)
    · have h2 := Nat.div_add_mod j (q + 1)
      rw [Nat.mul_comm] at h2
      exact h2.symm
  · right
    exact ⟨j - N * (q + 1), by omega, by omega⟩

lemma u_gate_blk (q N : ℕ) (pt : ℕ → ℕ → ℕ) (l r : ℕ) (hl : l < N) (hr : r < q + 1) :
    l * (q + 1) + r < (u_D q N pt).gates.length ∧
      gateAt (u_D q N pt) (l * (q + 1) + r) = u_Gf q N pt (l * (q + 1) + r) := by
  have hb := u_blk q N l r hl hr
  have hj : l * (q + 1) + r < N * (q + 1) + (N - 1) := by omega
  refine ⟨?_, u_gateAt q N pt _ hj⟩
  rw [u_len]
  exact hj

lemma u_gate_fin (q N : ℕ) (pt : ℕ → ℕ → ℕ) (i : ℕ) (hi : i < N - 1) :
    N * (q + 1) + i < (u_D q N pt).gates.length ∧
      gateAt (u_D q N pt) (N * (q + 1) + i) = u_Gf q N pt (N * (q + 1) + i) := by
  have hj : N * (q + 1) + i < N * (q + 1) + (N - 1) := by omega
  refine ⟨?_, u_gateAt q N pt _ hj⟩
  rw [u_len]
  exact hj

lemma u_andOr (q N : ℕ) (pt : ℕ → ℕ → ℕ) :
    ∀ g ∈ (u_D q N pt).gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
  intro g hg
  have hg2 : g ∈ (List.range (N * (q + 1) + (N - 1))).map (u_Gf q N pt) := hg
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hg2
  obtain ⟨a, b, h | h⟩ := u_Gf_shape q N pt j
  · rw [h]
    exact Or.inr rfl
  · rw [h]
    exact Or.inl rfl

lemma u_fanin (q N : ℕ) (pt : ℕ → ℕ → ℕ) :
    ∀ g ∈ (u_D q N pt).gates, g.inputs.length = 2 := by
  intro g hg
  have hg2 : g ∈ (List.range (N * (q + 1) + (N - 1))).map (u_Gf q N pt) := hg
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hg2
  obtain ⟨a, b, h | h⟩ := u_Gf_shape q N pt j
  · simp [h]
  · simp [h]

lemma u_readsBack (q N : ℕ) (pt : ℕ → ℕ → ℕ) (hq : 1 ≤ q) (hN : 2 ≤ N)
    (hpt : ∀ l i, l < N → i < q + 1 → pt l i < N) :
    ∀ j < (u_D q N pt).gates.length, ∀ i ∈ (gateAt (u_D q N pt) j).inputs, i < N + N + j := by
  intro j hj i hi
  rw [u_len] at hj
  rw [u_gateAt q N pt j hj] at hi
  rcases u_cases q N j hj with ⟨l, r, hl, hr, rfl⟩ | ⟨k, hk, rfl⟩
  · by_cases hr0 : r = 0
    · subst hr0
      rw [Nat.add_zero, u_G0 q N pt l hl] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      have h0 := hpt l 0 hl (by omega)
      have h1 := hpt l 1 hl (by omega)
      rcases hi with hi | hi <;> omega
    · by_cases hrq : r = q
      · rw [hrq, u_Gq q N pt l hq hl] at hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with hi | hi <;> omega
      · rw [u_G1 q N pt l r hl (by omega) (by omega)] at hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        have h1 := hpt l (r + 1) hl (by omega)
        rcases hi with hi | hi <;> omega
  · by_cases hk0 : k = 0
    · subst hk0
      rw [Nat.add_zero, u_F0] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      have h2 : 2 * (q + 1) ≤ N * (q + 1) := Nat.mul_le_mul_right _ hN
      rcases hi with hi | hi <;> omega
    · rw [u_Fi q N pt k (by omega)] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      have h2 : (k + 1 + 1) * (q + 1) ≤ N * (q + 1) := Nat.mul_le_mul_right _ (by omega)
      have h3 : (k + 1 + 1) * (q + 1) = (k + 1) * (q + 1) + (q + 1) := Nat.succ_mul _ _
      rcases hi with hi | hi <;> omega

lemma u_val_chain (q N : ℕ) (pt : ℕ → ℕ → ℕ)
    (hpt : ∀ l i, l < N → i < q + 1 → pt l i < N) (x : Fin (N + N) → Bool) (l : ℕ) (hl : l < N) :
    ∀ r, r < q → (s2230_W (N + N) (u_D q N pt) x (N + N + (l * (q + 1) + r)) = true ↔
      ∃ i, i ≤ r + 1 ∧ s2230_W (N + N) (u_D q N pt) x (pt l i) = true) := by
  intro r
  induction r with
  | zero =>
    intro hr
    obtain ⟨hk, hga⟩ := u_gate_blk q N pt l 0 hl (by omega)
    have hg : gateAt (u_D q N pt) (l * (q + 1) + 0) = ⟨GateOp.or, [pt l 0, pt l 1]⟩ := by
      rw [hga, Nat.add_zero, u_G0 q N pt l hl]
    have h0 := hpt l 0 hl (by omega)
    have h1 := hpt l 1 hl (by omega)
    rw [u_W_or2 (N + N) (u_D q N pt) x _ _ _ hk hg (by omega) (by omega), Bool.or_eq_true]
    constructor
    · rintro (h | h)
      · exact ⟨0, by omega, h⟩
      · exact ⟨1, by omega, h⟩
    · rintro ⟨i, hi, h⟩
      have hi2 : i = 0 ∨ i = 1 := by omega
      rcases hi2 with hi3 | hi3
      · rw [hi3] at h
        exact Or.inl h
      · rw [hi3] at h
        exact Or.inr h
  | succ r ih =>
    intro hr
    have ih2 := ih (by omega)
    obtain ⟨hk, hga⟩ := u_gate_blk q N pt l (r + 1) hl (by omega)
    have e : l * (q + 1) + (r + 1) - 1 = l * (q + 1) + r := by omega
    have hg : gateAt (u_D q N pt) (l * (q + 1) + (r + 1)) =
        ⟨GateOp.or, [N + N + (l * (q + 1) + r), pt l (r + 1 + 1)]⟩ := by
      rw [hga, u_G1 q N pt l (r + 1) hl (by omega) hr, e]
    have h1 := hpt l (r + 1 + 1) hl (by omega)
    rw [u_W_or2 (N + N) (u_D q N pt) x _ _ _ hk hg (by omega) (by omega), Bool.or_eq_true, ih2]
    constructor
    · rintro (⟨i, hi, h⟩ | h)
      · exact ⟨i, by omega, h⟩
      · exact ⟨r + 1 + 1, le_refl _, h⟩
    · rintro ⟨i, hi, h⟩
      by_cases hi2 : i ≤ r + 1
      · exact Or.inl ⟨i, hi2, h⟩
      · have hi3 : i = r + 1 + 1 := by omega
        rw [hi3] at h
        exact Or.inr h

lemma u_val_term (q N : ℕ) (pt : ℕ → ℕ → ℕ) (hq : 1 ≤ q)
    (hpt : ∀ l i, l < N → i < q + 1 → pt l i < N) (x : Fin (N + N) → Bool) (l : ℕ) (hl : l < N) :
    (s2230_W (N + N) (u_D q N pt) x (N + N + (l * (q + 1) + q)) = true ↔
      (∃ i, i ≤ q ∧ s2230_W (N + N) (u_D q N pt) x (pt l i) = true) ∧
        s2230_W (N + N) (u_D q N pt) x (N + l) = true) := by
  obtain ⟨hk, hga⟩ := u_gate_blk q N pt l q hl (by omega)
  have e : l * (q + 1) + q - 1 = l * (q + 1) + (q - 1) := by omega
  have hg : gateAt (u_D q N pt) (l * (q + 1) + q) =
      ⟨GateOp.and, [N + N + (l * (q + 1) + (q - 1)), N + l]⟩ := by
    rw [hga, u_Gq q N pt l hq hl, e]
  have hc := u_val_chain q N pt hpt x l hl (q - 1) (by omega)
  have e2 : q - 1 + 1 = q := Nat.sub_add_cancel hq
  rw [e2] at hc
  rw [u_W_and2 (N + N) (u_D q N pt) x _ _ _ hk hg (by omega) (by omega), Bool.and_eq_true, hc]

lemma u_val_final (q N : ℕ) (pt : ℕ → ℕ → ℕ) (hN : 2 ≤ N) (x : Fin (N + N) → Bool) :
    ∀ i, i < N - 1 → (s2230_W (N + N) (u_D q N pt) x (N + N + (N * (q + 1) + i)) = true ↔
      ∃ l, l ≤ i + 1 ∧
        s2230_W (N + N) (u_D q N pt) x (N + N + (l * (q + 1) + q)) = true) := by
  intro i
  induction i with
  | zero =>
    intro hi
    obtain ⟨hk, hga⟩ := u_gate_fin q N pt 0 hi
    have e0 : 0 * (q + 1) + q = q := by omega
    have e1 : 1 * (q + 1) + q = q + 1 + q := by omega
    have hg : gateAt (u_D q N pt) (N * (q + 1) + 0) =
        ⟨GateOp.or, [N + N + (0 * (q + 1) + q), N + N + (1 * (q + 1) + q)]⟩ := by
      rw [hga, Nat.add_zero, u_F0, e0, e1]
    have h2 : 2 * (q + 1) ≤ N * (q + 1) := Nat.mul_le_mul_right _ hN
    rw [u_W_or2 (N + N) (u_D q N pt) x _ _ _ hk hg (by omega) (by omega), Bool.or_eq_true]
    constructor
    · rintro (h | h)
      · exact ⟨0, by omega, h⟩
      · exact ⟨1, by omega, h⟩
    · rintro ⟨l, hl, h⟩
      have hl2 : l = 0 ∨ l = 1 := by omega
      rcases hl2 with hl3 | hl3
      · rw [hl3] at h
        exact Or.inl h
      · rw [hl3] at h
        exact Or.inr h
  | succ i ih =>
    intro hi
    have ih2 := ih (by omega)
    obtain ⟨hk, hga⟩ := u_gate_fin q N pt (i + 1) hi
    have e : N * (q + 1) + (i + 1) - 1 = N * (q + 1) + i := by omega
    have hg : gateAt (u_D q N pt) (N * (q + 1) + (i + 1)) =
        ⟨GateOp.or, [N + N + (N * (q + 1) + i), N + N + ((i + 1 + 1) * (q + 1) + q)]⟩ := by
      rw [hga, u_Fi q N pt (i + 1) (by omega), e]
    have h2 : (i + 1 + 1 + 1) * (q + 1) ≤ N * (q + 1) := Nat.mul_le_mul_right _ (by omega)
    have h3 : (i + 1 + 1 + 1) * (q + 1) = (i + 1 + 1) * (q + 1) + (q + 1) := Nat.succ_mul _ _
    rw [u_W_or2 (N + N) (u_D q N pt) x _ _ _ hk hg (by omega) (by omega), Bool.or_eq_true, ih2]
    constructor
    · rintro (⟨l, hl, h⟩ | h)
      · exact ⟨l, by omega, h⟩
      · exact ⟨i + 1 + 1, le_refl _, h⟩
    · rintro ⟨l, hl, h⟩
      by_cases hl2 : l ≤ i + 1
      · exact Or.inl ⟨l, hl2, h⟩
      · have hl3 : l = i + 1 + 1 := by omega
        rw [hl3] at h
        exact Or.inr h

lemma u_eval_iff (q N : ℕ) (pt : ℕ → ℕ → ℕ) (I : Fin N → Fin N → Prop) (hq : 1 ≤ q)
    (hN : 2 ≤ N) (hpt : ∀ l i, l < N → i < q + 1 → pt l i < N)
    (hpt2 : ∀ (l p : Fin N), I p l ↔ ∃ i, i < q + 1 ∧ pt l.val i = p.val)
    (x : Fin (N + N) → Bool) :
    circuitFun (N + N) (u_D q N pt) x = true ↔
      ∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true := by
  have hout : circuitFun (N + N) (u_D q N pt) x =
      s2230_W (N + N) (u_D q N pt) x (N + N + (N * (q + 1) + (N - 2))) := rfl
  rw [hout, u_val_final q N pt hN x (N - 2) (by omega)]
  constructor
  · rintro ⟨l, hl, h⟩
    have hlN : l < N := by omega
    obtain ⟨⟨i, hi, h1⟩, h2⟩ := (u_val_term q N pt hq hpt x l hlN).mp h
    have hp := hpt l i hlN (by omega)
    refine ⟨⟨pt l i, hp⟩, ⟨l, hlN⟩, (hpt2 ⟨l, hlN⟩ ⟨pt l i, hp⟩).mpr ⟨i, by omega, rfl⟩, ?_, ?_⟩
    · rw [s2230_W_input (N + N) (u_D q N pt) x (pt l i) (by omega)] at h1
      exact h1
    · rw [s2230_W_input (N + N) (u_D q N pt) x (N + l) (by omega)] at h2
      exact h2
  · rintro ⟨p, l, hI, hp, hl⟩
    obtain ⟨i, hi, hpi⟩ := (hpt2 l p).mp hI
    have hpN := p.isLt
    have hlN := l.isLt
    refine ⟨l.val, by omega,
      (u_val_term q N pt hq hpt x l.val hlN).mpr ⟨⟨i, by omega, ?_⟩, ?_⟩⟩
    · rw [hpi, s2230_W_input (N + N) (u_D q N pt) x p.val (by omega)]
      exact hp
    · rw [s2230_W_input (N + N) (u_D q N pt) x (N + l.val) (by omega)]
      exact hl

lemma u_rv_chain (q N : ℕ) (pt : ℕ → ℕ → ℕ)
    (hpt : ∀ l i, l < N → i < q + 1 → pt l i < N) (l : ℕ) (hl : l < N) (i0 : ℕ)
    (hi0 : i0 < q + 1) (b : ℕ) (hb : pt l i0 ≠ b) :
    ∀ r, r < q → i0 ≤ r + 1 →
      [1, 0] ∈ s2230_RV (u_D q N pt) (N + N) [pt l i0, b] 2 (N + N + (l * (q + 1) + r)) := by
  have hp0 := hpt l i0 hl hi0
  have hleaf : [1, 0] ∈ s2230_RV (u_D q N pt) (N + N) [pt l i0, b] 2 (pt l i0) := by
    rw [s2230_RV_input (u_D q N pt) (N + N) [pt l i0, b] 2 (pt l i0) (by omega), u_leaf_a _ _ hb]
    exact List.mem_singleton_self _
  intro r
  induction r with
  | zero =>
    intro hr hi
    obtain ⟨hk, hga⟩ := u_gate_blk q N pt l 0 hl (by omega)
    have hg : gateAt (u_D q N pt) (l * (q + 1) + 0) = ⟨GateOp.or, [pt l 0, pt l 1]⟩ := by
      rw [hga, Nat.add_zero, u_G0 q N pt l hl]
    have h0 := hpt l 0 hl (by omega)
    have h1 := hpt l 1 hl (by omega)
    apply u_RV_or2 (u_D q N pt) (N + N) [pt l i0, b] 2 _ _ _ hk hg (by omega) (by omega)
    have hi2 : i0 = 0 ∨ i0 = 1 := by omega
    rcases hi2 with h | h
    · left
      have e : pt l 0 = pt l i0 := by rw [h]
      rw [e]
      exact hleaf
    · right
      have e : pt l 1 = pt l i0 := by rw [h]
      rw [e]
      exact hleaf
  | succ r ih =>
    intro hr hi
    obtain ⟨hk, hga⟩ := u_gate_blk q N pt l (r + 1) hl (by omega)
    have e : l * (q + 1) + (r + 1) - 1 = l * (q + 1) + r := by omega
    have hg : gateAt (u_D q N pt) (l * (q + 1) + (r + 1)) =
        ⟨GateOp.or, [N + N + (l * (q + 1) + r), pt l (r + 1 + 1)]⟩ := by
      rw [hga, u_G1 q N pt l (r + 1) hl (by omega) hr, e]
    have h1 := hpt l (r + 1 + 1) hl (by omega)
    apply u_RV_or2 (u_D q N pt) (N + N) [pt l i0, b] 2 _ _ _ hk hg (by omega) (by omega)
    by_cases hi2 : i0 ≤ r + 1
    · left
      exact ih (by omega) hi2
    · right
      have e2 : pt l (r + 1 + 1) = pt l i0 := by
        have e3 : r + 1 + 1 = i0 := by omega
        rw [e3]
      rw [e2]
      exact hleaf

lemma u_rv_term (q N : ℕ) (pt : ℕ → ℕ → ℕ) (hq : 1 ≤ q)
    (hpt : ∀ l i, l < N → i < q + 1 → pt l i < N) (l : ℕ) (hl : l < N) (i0 : ℕ)
    (hi0 : i0 < q + 1) :
    [1, 1] ∈ s2230_RV (u_D q N pt) (N + N) [pt l i0, N + l] 2 (N + N + (l * (q + 1) + q)) := by
  have hp := hpt l i0 hl hi0
  have hne : pt l i0 ≠ N + l := by omega
  obtain ⟨hk, hga⟩ := u_gate_blk q N pt l q hl (by omega)
  have e : l * (q + 1) + q - 1 = l * (q + 1) + (q - 1) := by omega
  have hg : gateAt (u_D q N pt) (l * (q + 1) + q) =
      ⟨GateOp.and, [N + N + (l * (q + 1) + (q - 1)), N + l]⟩ := by
    rw [hga, u_Gq q N pt l hq hl, e]
  have hc := u_rv_chain q N pt hpt l hl i0 hi0 (N + l) hne (q - 1) (by omega) (by omega)
  have hb : [0, 1] ∈ s2230_RV (u_D q N pt) (N + N) [pt l i0, N + l] 2 (N + l) := by
    rw [s2230_RV_input (u_D q N pt) (N + N) [pt l i0, N + l] 2 (N + l) (by omega),
      u_leaf_b _ _ hne]
    exact List.mem_singleton_self _
  have h := u_RV_and2 (u_D q N pt) (N + N) [pt l i0, N + l] 2 _ _ _ hk hg (by omega) (by omega)
    _ _ hc hb
  have e3 : capAdd 2 (capAdd 2 ([pt l i0, N + l].map fun _ => 0) [1, 0]) [0, 1] = [1, 1] := by
    first
      | rfl
      | simp [capAdd]
  rw [e3] at h
  exact h

lemma u_rv_final (q N : ℕ) (pt : ℕ → ℕ → ℕ) (hN : 2 ≤ N) (S : List ℕ) (l0 : ℕ)
    (ht : [1, 1] ∈ s2230_RV (u_D q N pt) (N + N) S 2 (N + N + (l0 * (q + 1) + q))) :
    ∀ i, i < N - 1 → l0 ≤ i + 1 →
      [1, 1] ∈ s2230_RV (u_D q N pt) (N + N) S 2 (N + N + (N * (q + 1) + i)) := by
  intro i
  induction i with
  | zero =>
    intro hi hl
    obtain ⟨hk, hga⟩ := u_gate_fin q N pt 0 hi
    have e0 : 0 * (q + 1) + q = q := by omega
    have e1 : 1 * (q + 1) + q = q + 1 + q := by omega
    have hg : gateAt (u_D q N pt) (N * (q + 1) + 0) =
        ⟨GateOp.or, [N + N + (0 * (q + 1) + q), N + N + (1 * (q + 1) + q)]⟩ := by
      rw [hga, Nat.add_zero, u_F0, e0, e1]
    have h2 : 2 * (q + 1) ≤ N * (q + 1) := Nat.mul_le_mul_right _ hN
    apply u_RV_or2 (u_D q N pt) (N + N) S 2 _ _ _ hk hg (by omega) (by omega)
    have hl2 : l0 = 0 ∨ l0 = 1 := by omega
    rcases hl2 with h | h
    · left
      rw [h] at ht
      exact ht
    · right
      rw [h] at ht
      exact ht
  | succ i ih =>
    intro hi hl
    obtain ⟨hk, hga⟩ := u_gate_fin q N pt (i + 1) hi
    have e : N * (q + 1) + (i + 1) - 1 = N * (q + 1) + i := by omega
    have hg : gateAt (u_D q N pt) (N * (q + 1) + (i + 1)) =
        ⟨GateOp.or, [N + N + (N * (q + 1) + i), N + N + ((i + 1 + 1) * (q + 1) + q)]⟩ := by
      rw [hga, u_Fi q N pt (i + 1) (by omega), e]
    have h2 : (i + 1 + 1 + 1) * (q + 1) ≤ N * (q + 1) := Nat.mul_le_mul_right _ (by omega)
    have h3 : (i + 1 + 1 + 1) * (q + 1) = (i + 1 + 1) * (q + 1) + (q + 1) := Nat.succ_mul _ _
    apply u_RV_or2 (u_D q N pt) (N + N) S 2 _ _ _ hk hg (by omega) (by omega)
    by_cases hl2 : l0 ≤ i + 1
    · left
      exact ih (by omega) hl2
    · right
      have e2 : l0 = i + 1 + 1 := by omega
      rw [e2] at ht
      exact ht

lemma u_reads (q N : ℕ) (pt : ℕ → ℕ → ℕ) (hq : 1 ≤ q) (hN : 2 ≤ N)
    (hpt : ∀ l i, l < N → i < q + 1 → pt l i < N) (l : ℕ) (hl : l < N) (i0 : ℕ)
    (hi0 : i0 < q + 1) :
    readsAtMost (u_D q N pt) (N + N) [pt l i0, N + l] 2 = true := by
  have ht := u_rv_term q N pt hq hpt l hl i0 hi0
  have hf := u_rv_final q N pt hN _ l ht (N - 2) (by omega) (by omega)
  unfold readsAtMost
  rw [List.any_eq_true]
  refine ⟨[1, 1], hf, ?_⟩
  first
    | rfl
    | decide
    | simp

lemma u_readK (q N : ℕ) (pt : ℕ → ℕ → ℕ) (I : Fin N → Fin N → Prop) (hq : 1 ≤ q)
    (hN : 2 ≤ N) (hpt : ∀ l i, l < N → i < q + 1 → pt l i < N)
    (hpt2 : ∀ (l p : Fin N), I p l ↔ ∃ i, i < q + 1 ∧ pt l.val i = p.val)
    (hfun : ∀ x : Fin (N + N) → Bool, circuitFun (N + N) (u_D q N pt) x = true ↔
      ∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) :
    PEqualNP.ReadK.IsReadK (N + N) (u_D q N pt) 2 := by
  intro S hS
  obtain ⟨hS1, hS2⟩ := hS
  obtain ⟨p, l, hI, hp, hl⟩ := (hfun _).mp hS1
  have hpS : Fin.castAdd N p ∈ S := by simpa [PEqualNP.ReadK.setInput] using hp
  have hlS : Fin.natAdd N l ∈ S := by simpa [PEqualNP.ReadK.setInput] using hl
  have hpN := p.isLt
  have hlN := l.isLt
  have hlt : Fin.castAdd N p < Fin.natAdd N l := by
    rw [Fin.lt_def]
    show p.val < N + l.val
    omega
  have hSeq : S = {Fin.castAdd N p, Fin.natAdd N l} := by
    by_contra hne
    have hsub : ({Fin.castAdd N p, Fin.natAdd N l} : Finset (Fin (N + N))) ⊂ S := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, fun h => hne h.symm⟩
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with hy | hy
      · rw [hy]
        exact hpS
      · rw [hy]
        exact hlS
    have hfalse := hS2 _ (Finset.mem_ssubsets.mpr hsub)
    have htrue : circuitFun (N + N) (u_D q N pt) (PEqualNP.ReadK.setInput
        ({Fin.castAdd N p, Fin.natAdd N l} : Finset (Fin (N + N)))) = true :=
      (hfun _).mpr ⟨p, l, hI, by simp [PEqualNP.ReadK.setInput],
        by simp [PEqualNP.ReadK.setInput]⟩
    rw [htrue] at hfalse
    exact Bool.noConfusion hfalse
  rw [hSeq, cor_setList_pair _ _ hlt]
  obtain ⟨i0, hi0, hpi⟩ := (hpt2 l p).mp hI
  have h := u_reads q N pt hq hN hpt l.val hlN i0 hi0
  rw [hpi] at h
  exact h

lemma u_core (q N : ℕ) (I : Fin N → Fin N → Prop) (hq : 1 ≤ q) (hN : 2 ≤ N)
    (pt : ℕ → ℕ → ℕ) (hpt : ∀ l i, l < N → i < q + 1 → pt l i < N)
    (hpt2 : ∀ (l p : Fin N), I p l ↔ ∃ i, i < q + 1 ∧ pt l.val i = p.val) :
    ∃ D : Circuit, IsAO2 (N + N) D ∧
      (∀ x : Fin (N + N) → Bool, circuitFun (N + N) D x = true ↔
        ∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) ∧
      PEqualNP.ReadK.IsReadK (N + N) D 2 ∧ D.size + 1 = N * (q + 2) := by
  have hAO : IsAO2 (N + N) (u_D q N pt) :=
    And.intro (u_andOr q N pt) (And.intro (u_readsBack q N pt hq hN hpt) (u_fanin q N pt))
  refine ⟨u_D q N pt, hAO, fun x => u_eval_iff q N pt I hq hN hpt hpt2 x,
    u_readK q N pt I hq hN hpt hpt2 (fun x => u_eval_iff q N pt I hq hN hpt hpt2 x), ?_⟩
  have h1 : (u_D q N pt).size = N * (q + 1) + (N - 1) := u_len q N pt
  have hmul : N * (q + 2) = N * (q + 1) + N := Nat.mul_succ N (q + 1)
  omega

lemma u_upper (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (hq : 2 ≤ q)
    (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) :
    ∃ D : Circuit, IsAO2 (N + N) D ∧
      (∀ x : Fin (N + N) → Bool, circuitFun (N + N) D x = true ↔
        ∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) ∧
      PEqualNP.ReadK.IsReadK (N + N) D 2 ∧ D.size + 1 = N * (q + 2) := by
  have hN2 : 2 ≤ N := by omega
  have hex : ∀ t : Fin N, ∃ f : ℕ → ℕ, (∀ i, i < q + 1 → f i < N) ∧
      ∀ v : Fin N, I v t ↔ ∃ i, i < q + 1 ∧ f i = (v : ℕ) := by
    intro t
    refine ⟨fun i => if h : i < q + 1 then
      (((Finset.univ.filter (fun p => I p t)).orderEmbOfFin (hline t) ⟨i, h⟩ : Fin N) : ℕ)
      else 0, ?_, ?_⟩
    · intro i hi
      simp only [dif_pos hi]
      exact Fin.is_lt _
    · intro v
      constructor
      · intro hv
        have hv2 : v ∈ Finset.univ.filter (fun p => I p t) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
        have hr : v ∈ Set.range ((Finset.univ.filter (fun p => I p t)).orderEmbOfFin
            (hline t)) := by
          rw [Finset.range_orderEmbOfFin]
          exact Finset.mem_coe.mpr hv2
        obtain ⟨k, hk⟩ := hr
        refine ⟨(k : ℕ), k.2, ?_⟩
        simp only [dif_pos k.2]
        rw [← hk]
      · rintro ⟨i, hi, hfi⟩
        simp only [dif_pos hi] at hfi
        have he : (Finset.univ.filter (fun p => I p t)).orderEmbOfFin (hline t) ⟨i, hi⟩ = v :=
          Fin.ext hfi
        have hm := Finset.orderEmbOfFin_mem (Finset.univ.filter (fun p => I p t)) (hline t)
          ⟨i, hi⟩
        rw [he] at hm
        exact (Finset.mem_filter.mp hm).2
  choose F hF1 hF2 using hex
  exact u_core q N I (by omega) hN2 (fun t' i => if h : t' < N then F ⟨t', h⟩ i else 0)
    (fun t i ht hi => by simp only [dif_pos ht]; exact hF1 ⟨t, ht⟩ i hi)
    (fun t v => by simp only [dif_pos t.2]; exact hF2 t v)

theorem main_aux : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I], 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (N + N) C ∧ (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) ∧ PEqualNP.ReadK.IsReadK (N + N) C 2 ∧ C.size ≤ N * (q + 2) := by
  intro q N I _ hq hN hline _
  obtain ⟨D, hD1, hD2, hD3, hD4⟩ := u_upper q N I hq hN hline
  refine ⟨D, hD1, ?_, hD3, by omega⟩
  intro z2
  by_cases hd : ∃ p4 l4 : Fin N, I p4 l4 ∧ z2 (Fin.castAdd N p4) = true ∧
      z2 (Fin.natAdd N l4) = true
  · rw [decide_eq_true hd]
    exact (hD2 z2).mpr hd
  · rw [decide_eq_false hd]
    cases hc : PEqualNP.MetaComplexity.circuitFun (N + N) D z2
    · rfl
    · exact absurd ((hD2 z2).mp hc) hd

end PEqualNP.Outside.L_meta_2575

theorem PEqualNP.Outside.L_meta_2575 : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I], 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (N + N) C ∧ (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) ∧ PEqualNP.ReadK.IsReadK (N + N) C 2 ∧ C.size ≤ N * (q + 2) :=
  PEqualNP.Outside.L_meta_2575.main_aux
