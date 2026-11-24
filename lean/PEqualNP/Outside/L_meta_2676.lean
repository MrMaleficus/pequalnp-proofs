import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2676

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

theorem gapp_lt {α : Type} (l l2 : List α) (d : α) (i : ℕ) (h : i < l.length) :
    (l ++ l2).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left h]

theorem gapp_len {α : Type} (l : List α) (v d : α) : (l ++ [v]).getD l.length d = v := by
  simp [List.getD]

theorem gapp_gt {α : Type} (l : List α) (v d : α) (i : ℕ) (h : l.length < i) :
    (l ++ [v]).getD i d = d :=
  List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton]; omega)

theorem split_at (gs : List Gate) : ∀ (j : ℕ) (g g2 : Gate), gs[j]? = some g →
    ∃ pre post, pre.length = j ∧ gs = pre ++ g :: post ∧ gs.set j g2 = pre ++ g2 :: post := by
  induction gs with
  | nil => intro j g g2 h; simp at h
  | cons a gs ih =>
    intro j g g2 h
    cases j with
    | zero =>
      have ha : a = g := by simpa using h
      subst ha
      exact ⟨[], gs, rfl, rfl, rfl⟩
    | succ j =>
      have h2 : gs[j]? = some g := by simpa using h
      obtain ⟨pre, post, hl, e1, e2⟩ := ih j g g2 h2
      refine ⟨a :: pre, post, by rw [List.length_cons, hl], ?_, ?_⟩
      · exact congrArg (List.cons a) e1
      · exact congrArg (List.cons a) e2

theorem mem_insertNew (A : List (List ℕ)) (w v : List ℕ) :
    v ∈ insertNew A w ↔ v ∈ A ∨ v = w := by
  unfold insertNew
  split_ifs with h
  · constructor
    · intro hv
      exact Or.inl hv
    · rintro (hv | rfl)
      · exact hv
      · exact h
  · simp

theorem mem_foldl_insertNew (B : List (List ℕ)) :
    ∀ (acc : List (List ℕ)) (v : List ℕ), v ∈ B.foldl insertNew acc ↔ v ∈ acc ∨ v ∈ B := by
  induction B with
  | nil => intro acc v; simp
  | cons b B ih =>
    intro acc v
    rw [List.foldl_cons, ih, mem_insertNew, List.mem_cons]
    tauto

theorem mem_union (ins : List (List (List ℕ))) :
    ∀ (acc : List (List ℕ)) (v : List ℕ),
      v ∈ ins.foldl (fun acc A => A.foldl insertNew acc) acc ↔ v ∈ acc ∨ ∃ A ∈ ins, v ∈ A := by
  induction ins with
  | nil => intro acc v; simp
  | cons A ins ih =>
    intro acc v
    simp only [List.foldl_cons]
    rw [ih, mem_foldl_insertNew]
    constructor
    · rintro ((h | h) | ⟨X, hX, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨A, by simp, h⟩
      · exact Or.inr ⟨X, List.mem_cons_of_mem _ hX, h⟩
    · rintro (h | ⟨X, hX, h⟩)
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.1 hX with hXA | hX
        · rw [hXA] at h
          exact Or.inl (Or.inr h)
        · exact Or.inr ⟨X, hX, h⟩

theorem mem_andStep (k : ℕ) (A B : List (List ℕ)) (v : List ℕ) :
    v ∈ andStep k A B ↔ ∃ a ∈ A, ∃ b ∈ B, capAdd k a b = v := by
  unfold andStep
  rw [mem_foldl_insertNew]
  simp [List.mem_flatMap]

theorem capAdd_good (k : ℕ) : ∀ (a b : List ℕ), a.length = b.length →
    (capAdd k a b).all (fun x => decide (x ≤ k)) = true →
    a.all (fun x => decide (x ≤ k)) = true ∧ b.all (fun x => decide (x ≤ k)) = true := by
  intro a
  induction a with
  | nil =>
    intro b hl _
    cases b with
    | nil => simp
    | cons y b => simp at hl
  | cons x a ih =>
    intro b hl h
    cases b with
    | nil => simp at hl
    | cons y b =>
      simp only [capAdd, List.zipWith_cons_cons, List.all_cons, Bool.and_eq_true,
        decide_eq_true_eq] at h
      have hl2 : a.length = b.length := by simpa using hl
      have h3 := ih b hl2 h.2
      have h1 := h.1
      simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨by omega, h3.1⟩, ⟨by omega, h3.2⟩⟩

theorem capAdd_len (k : ℕ) (a b : List ℕ) (L : ℕ) (ha : a.length = L) (hb : b.length = L) :
    (capAdd k a b).length = L := by
  simp [capAdd, ha, hb]

abbrev Rel (L k : ℕ) (X Y : List (List ℕ)) : Prop :=
  ∀ v ∈ X, v.length = L ∧ (v.all (fun a => decide (a ≤ k)) = true → v ∈ Y)

abbrev WRel (S : List ℕ) (k : ℕ) (A B : List (List (List ℕ))) : Prop :=
  A.length = B.length ∧ ∀ i, Rel S.length k (A.getD i []) (B.getD i [])

theorem and_fold (L k : ℕ) (fA fB : ℕ → List (List ℕ))
    (hf : ∀ i, Rel L k (fA i) (fB i)) (is : List ℕ) :
    ∀ (accA accB : List (List ℕ)), Rel L k accA accB →
      Rel L k ((is.map fA).foldl (andStep k) accA) ((is.map fB).foldl (andStep k) accB) := by
  induction is with
  | nil => intro accA accB hacc; exact hacc
  | cons i is ih =>
    intro accA accB hacc
    simp only [List.map_cons, List.foldl_cons]
    apply ih
    intro v hv
    rw [mem_andStep] at hv
    obtain ⟨a, ha, b, hb, rfl⟩ := hv
    have h1 := hacc a ha
    have h2 := hf i b hb
    refine ⟨capAdd_len k a b L h1.1 h2.1, fun hg => ?_⟩
    have hg2 := capAdd_good k a b (by rw [h1.1, h2.1]) hg
    rw [mem_andStep]
    exact ⟨a, h1.2 hg2.1, b, h2.2 hg2.2, rfl⟩

theorem or_union (L k : ℕ) (fA fB : ℕ → List (List ℕ))
    (hf : ∀ i, Rel L k (fA i) (fB i)) (is : List ℕ) :
    Rel L k ((is.map fA).foldl (fun acc A => A.foldl insertNew acc) [])
      ((is.map fB).foldl (fun acc A => A.foldl insertNew acc) []) := by
  intro v hv
  rw [mem_union] at hv
  rcases hv with h | ⟨X, hX, hv⟩
  · exact absurd h List.not_mem_nil
  · rw [List.mem_map] at hX
    obtain ⟨i, hi, rfl⟩ := hX
    have h := hf i v hv
    refine ⟨h.1, fun hg => ?_⟩
    rw [mem_union]
    exact Or.inr ⟨fB i, List.mem_map.2 ⟨i, hi, rfl⟩, h.2 hg⟩

def gv (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) : List (List ℕ) :=
  match g.op with
  | GateOp.or => (g.inputs.map fun i => R.getD i []).foldl (fun acc A => A.foldl insertNew acc) []
  | GateOp.and => (g.inputs.map fun i => R.getD i []).foldl (andStep k) [S.map fun _ => 0]
  | _ => []

def RW (S : List ℕ) (k : ℕ) (gs : List Gate) (R : List (List (List ℕ))) :
    List (List (List ℕ)) :=
  gs.foldl (fun R g => R ++ [gv S k R g]) R

theorem RW_cons (S : List ℕ) (k : ℕ) (g : Gate) (gs : List Gate) (R : List (List (List ℕ))) :
    RW S k (g :: gs) R = RW S k gs (R ++ [gv S k R g]) := rfl

theorem RW_single (S : List ℕ) (k : ℕ) (g : Gate) (R : List (List (List ℕ))) :
    RW S k [g] R = R ++ [gv S k R g] := rfl

theorem RW_append (S : List ℕ) (k : ℕ) (a b : List Gate) (R : List (List (List ℕ))) :
    RW S k (a ++ b) R = RW S k b (RW S k a R) := by
  unfold RW
  rw [List.foldl_append]

theorem RW_length (S : List ℕ) (k : ℕ) (gs : List Gate) :
    ∀ R : List (List (List ℕ)), (RW S k gs R).length = R.length + gs.length := by
  induction gs with
  | nil => intro R; simp [RW]
  | cons g gs ih =>
    intro R
    rw [RW_cons, ih, List.length_append, List.length_singleton, List.length_cons]
    omega

theorem RW_prefix (S : List ℕ) (k : ℕ) (gs : List Gate) :
    ∀ (R : List (List (List ℕ))) (i : ℕ), i < R.length →
      (RW S k gs R).getD i [] = R.getD i [] := by
  induction gs with
  | nil => intro R i _; rfl
  | cons g gs ih =>
    intro R i hi
    rw [RW_cons, ih _ i (by rw [List.length_append, List.length_singleton]; omega)]
    exact gapp_lt R _ _ i hi

theorem gv_rel (S : List ℕ) (k : ℕ) (A B : List (List (List ℕ)))
    (h : ∀ i, Rel S.length k (A.getD i []) (B.getD i [])) (g : Gate) :
    Rel S.length k (gv S k A g) (gv S k B g) := by
  obtain ⟨op, inputs⟩ := g
  cases op with
  | or =>
    exact or_union S.length k (fun i => A.getD i []) (fun i => B.getD i []) h inputs
  | and =>
    refine and_fold S.length k (fun i => A.getD i []) (fun i => B.getD i []) h inputs
      [S.map fun _ => 0] [S.map fun _ => 0] ?_
    intro v hv
    rw [List.mem_singleton] at hv
    refine ⟨by rw [hv]; simp, fun _ => List.mem_singleton.2 hv⟩
  | not => intro v hv; exact absurd hv List.not_mem_nil
  | mod m => intro v hv; exact absurd hv List.not_mem_nil
  | maj => intro v hv; exact absurd hv List.not_mem_nil

theorem step_rel (S : List ℕ) (k : ℕ) (A B : List (List (List ℕ))) (X Y : List (List ℕ))
    (h : WRel S k A B) (hXY : Rel S.length k X Y) : WRel S k (A ++ [X]) (B ++ [Y]) := by
  refine ⟨by rw [List.length_append, List.length_append, h.1, List.length_singleton,
    List.length_singleton], fun i => ?_⟩
  rcases lt_trichotomy i A.length with hi | hi | hi
  · rw [gapp_lt A _ _ i hi, gapp_lt B _ _ i (by rw [← h.1]; exact hi)]
    exact h.2 i
  · rw [hi, gapp_len, h.1, gapp_len]
    exact hXY
  · rw [gapp_gt A _ _ i hi, gapp_gt B _ _ i (by rw [← h.1]; exact hi)]
    intro v hv
    exact absurd hv List.not_mem_nil

theorem RW_rel (S : List ℕ) (k : ℕ) (gs : List Gate) :
    ∀ (A B : List (List (List ℕ))), WRel S k A B → WRel S k (RW S k gs A) (RW S k gs B) := by
  induction gs with
  | nil => intro A B h; exact h
  | cons g gs ih =>
    intro A B h
    show WRel S k (RW S k gs (A ++ [gv S k A g])) (RW S k gs (B ++ [gv S k B g]))
    exact ih _ _ (step_rel S k A B _ _ h (gv_rel S k A B h.2 g))

theorem base_rel (S : List ℕ) (k n : ℕ) :
    WRel S k ((List.range n).map (leafVectors S k)) ((List.range n).map (leafVectors S k)) := by
  refine ⟨rfl, fun i v hv => ⟨?_, fun _ => hv⟩⟩
  by_cases hi : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hi)] at hv
    simp only [List.getElem_map, List.getElem_range] at hv
    unfold leafVectors at hv
    split_ifs at hv with h
    · rw [List.mem_singleton] at hv
      rw [hv]
      simp
    · exact absurd hv List.not_mem_nil
  · rw [List.getD_eq_default _ _ (by simpa using hi)] at hv
    exact absurd hv List.not_mem_nil

theorem mod_rel (S : List ℕ) (k : ℕ) (P : List (List (List ℕ))) (u t : ℕ)
    (hPP : WRel S k P P)
    (hnQ : ∀ w ∈ P.getD t [], w.all (fun a => decide (a ≤ k)) = true → False) :
    Rel S.length k (gv S k P ⟨GateOp.or, [u, t]⟩) (gv S k P ⟨GateOp.or, [u]⟩) := by
  intro v hv
  have hv2 : v ∈ ([u, t].map fun i => P.getD i []).foldl
      (fun acc A => A.foldl insertNew acc) [] := hv
  rw [mem_union] at hv2
  rcases hv2 with h | ⟨Y, hY, hvY⟩
  · exact absurd h List.not_mem_nil
  · rw [List.mem_map] at hY
    obtain ⟨i, hi, rfl⟩ := hY
    have hi2 : i = u ∨ i = t := by simpa using hi
    rcases hi2 with hiu | hit
    · rw [hiu] at hvY
      refine ⟨(hPP.2 u v hvY).1, fun _ => ?_⟩
      show v ∈ ([u].map fun i => P.getD i []).foldl (fun acc A => A.foldl insertNew acc) []
      rw [mem_union]
      exact Or.inr ⟨P.getD u [], List.mem_map.2 ⟨u, by simp, rfl⟩, hvY⟩
    · rw [hit] at hvY
      exact ⟨(hPP.2 t v hvY).1, fun hg => (hnQ v hvY hg).elim⟩

theorem top_or (S : List ℕ) (k : ℕ) (Rn : List (List (List ℕ))) (o t K : ℕ)
    (hK : K = Rn.length) (v : List ℕ) (hv : v ∈ Rn.getD o [] ∨ v ∈ Rn.getD t [])
    (hg : v.all (fun a => decide (a ≤ k)) = true) :
    ((Rn ++ [gv S k Rn ⟨GateOp.or, [o, t]⟩]).getD K []).any
      (fun v => v.all fun a => decide (a ≤ k)) = true := by
  subst hK
  rw [gapp_len, List.any_eq_true]
  refine ⟨v, ?_, hg⟩
  show v ∈ ([o, t].map fun i => Rn.getD i []).foldl (fun acc A => A.foldl insertNew acc) []
  rw [mem_union]
  rcases hv with h | h
  · exact Or.inr ⟨Rn.getD o [], List.mem_map.2 ⟨o, by simp, rfl⟩, h⟩
  · exact Or.inr ⟨Rn.getD t [], List.mem_map.2 ⟨t, by simp, rfl⟩, h⟩

theorem core (S : List ℕ) (k : ℕ) (P : List (List (List ℕ))) (post : List Gate)
    (u t o K : ℕ) (hPP : WRel S k P P) (ht : t < P.length)
    (hK : K = P.length + 1 + post.length)
    (h : ((RW S k post (P ++ [gv S k P ⟨GateOp.or, [u, t]⟩])).getD o []).any
      (fun v => v.all fun a => decide (a ≤ k)) = true) :
    ((RW S k post (P ++ [gv S k P ⟨GateOp.or, [u]⟩]) ++
      [gv S k (RW S k post (P ++ [gv S k P ⟨GateOp.or, [u]⟩])) ⟨GateOp.or, [o, t]⟩]).getD K
        []).any (fun v => v.all fun a => decide (a ≤ k)) = true := by
  rw [List.any_eq_true] at h
  obtain ⟨v, hv, hg⟩ := h
  have hKn : K = (RW S k post (P ++ [gv S k P ⟨GateOp.or, [u]⟩])).length := by
    rw [RW_length, List.length_append, List.length_singleton]
    exact hK
  have htn : (RW S k post (P ++ [gv S k P ⟨GateOp.or, [u]⟩])).getD t [] = P.getD t [] := by
    rw [RW_prefix _ _ _ _ _ (by rw [List.length_append, List.length_singleton]; omega)]
    exact gapp_lt P _ _ t ht
  by_cases hQ : ∃ w, w ∈ P.getD t [] ∧ w.all (fun a => decide (a ≤ k)) = true
  · obtain ⟨w, hw, hwg⟩ := hQ
    exact top_or S k _ o t K hKn w (Or.inr (by rw [htn]; exact hw)) hwg
  · have hrel : WRel S k (P ++ [gv S k P ⟨GateOp.or, [u, t]⟩])
        (P ++ [gv S k P ⟨GateOp.or, [u]⟩]) :=
      step_rel S k P P _ _ hPP (mod_rel S k P u t hPP (fun w hw hwg => hQ ⟨w, hw, hwg⟩))
    have hfin := RW_rel S k post _ _ hrel
    exact top_or S k _ o t K hKn v (Or.inl ((hfin.2 o v hv).2 hg)) hg

theorem main_aux : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (j u t : ℕ), PEqualNP.MetaComplexity.Monotone2 C → j < C.gates.length → C.gates[j]? = some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [u, t] } → t < n + j → (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true → PEqualNP.MetaComplexity.circuitFun n C x = true) → ∀ (S : List ℕ) (k : ℕ), PEqualNP.ReadK.readsAtMost C n S k = true → PEqualNP.ReadK.readsAtMost { gates := C.gates.set j { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [u] } ++ [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [C.output, t] }], output := n + C.gates.length } n S k = true := by
  intro n C j u t _ hj hg ht _ S k hread
  obtain ⟨pre, post, hlen, h1, h2⟩ :=
    split_at C.gates j ⟨GateOp.or, [u, t]⟩ ⟨GateOp.or, [u]⟩ hg
  have hP : (RW S k pre ((List.range n).map (leafVectors S k))).length = n + j := by
    rw [RW_length, List.length_map, List.length_range, hlen]
  have hPP : WRel S k (RW S k pre ((List.range n).map (leafVectors S k)))
      (RW S k pre ((List.range n).map (leafVectors S k))) :=
    RW_rel S k pre _ _ (base_rel S k n)
  have hlenC : C.gates.length = j + 1 + post.length := by
    have h3 := congrArg List.length h1
    rw [List.length_append, List.length_cons] at h3
    omega
  have hread2 : ((RW S k C.gates ((List.range n).map (leafVectors S k))).getD C.output []).any
      (fun v => v.all fun a => decide (a ≤ k)) = true := hread
  rw [h1, RW_append, RW_cons] at hread2
  show ((RW S k (C.gates.set j ⟨GateOp.or, [u]⟩ ++ [⟨GateOp.or, [C.output, t]⟩])
      ((List.range n).map (leafVectors S k))).getD (n + C.gates.length) []).any
      (fun v => v.all fun a => decide (a ≤ k)) = true
  rw [h2, RW_append, RW_single, RW_append, RW_cons]
  exact core S k (RW S k pre ((List.range n).map (leafVectors S k))) post u t C.output
    (n + C.gates.length) hPP (by rw [hP]; exact ht) (by rw [hP]; omega) hread2

end PEqualNP.Outside.L_meta_2676

theorem PEqualNP.Outside.L_meta_2676 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (j u t : ℕ), PEqualNP.MetaComplexity.Monotone2 C → j < C.gates.length → C.gates[j]? = some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [u, t] } → t < n + j → (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true → PEqualNP.MetaComplexity.circuitFun n C x = true) → ∀ (S : List ℕ) (k : ℕ), PEqualNP.ReadK.readsAtMost C n S k = true → PEqualNP.ReadK.readsAtMost { gates := C.gates.set j { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [u] } ++ [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [C.output, t] }], output := n + C.gates.length } n S k = true :=
  PEqualNP.Outside.L_meta_2676.main_aux
