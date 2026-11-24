import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2472

open PEqualNP.CircuitLowerBounds PEqualNP.ReadK

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

lemma FR_other (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate)
    (hor : g.op ≠ GateOp.or) (hand : g.op ≠ GateOp.and) : FR S k R g = [] := by
  obtain ⟨op, ins⟩ := g
  cases op
  · exact absurd rfl hand
  · exact absurd rfl hor
  · rfl
  · rfl
  · rfl

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

lemma mem_andStep (k : ℕ) (A B : List (List ℕ)) (v : List ℕ) (h : v ∈ andStep k A B) :
    ∃ u ∈ A, ∃ u2 ∈ B, v = capAdd k u u2 := by
  unfold andStep at h
  rcases mem_foldl_insertNew _ _ _ h with h1 | h1
  · simp at h1
  · simp only [List.mem_flatMap, List.mem_map] at h1
    obtain ⟨u, hu, u2, hu2, rfl⟩ := h1
    exact ⟨u, hu, u2, hu2, rfl⟩

lemma mem_andStep_of (k : ℕ) (A B : List (List ℕ)) (u u2 : List ℕ) (hu : u ∈ A) (hu2 : u2 ∈ B) :
    capAdd k u u2 ∈ andStep k A B := by
  unfold andStep
  apply mem_foldl_insertNew_of
  right
  simp only [List.mem_flatMap, List.mem_map]
  exact ⟨u, hu, u2, hu2, rfl⟩

lemma mem_orFold (Ls : List (List (List ℕ))) (acc : List (List ℕ)) (v : List ℕ) :
    v ∈ Ls.foldl (fun acc A => A.foldl insertNew acc) acc ↔ v ∈ acc ∨ ∃ A ∈ Ls, v ∈ A := by
  induction Ls generalizing acc with
  | nil => simp
  | cons A Ls ih =>
    rw [List.foldl_cons, ih]
    constructor
    · rintro (h | ⟨B, hB, hv⟩)
      · rcases mem_foldl_insertNew _ _ _ h with h1 | h1
        · exact Or.inl h1
        · exact Or.inr ⟨A, List.mem_cons_self, h1⟩
      · exact Or.inr ⟨B, List.mem_cons_of_mem _ hB, hv⟩
    · rintro (h | ⟨B, hB, hv⟩)
      · exact Or.inl (mem_foldl_insertNew_of _ _ _ (Or.inl h))
      · rcases List.mem_cons.1 hB with h1 | h1
        · subst h1
          exact Or.inl (mem_foldl_insertNew_of _ _ _ (Or.inr hv))
        · exact Or.inr ⟨B, h1, hv⟩

def cp (v : List ℕ) : List ℕ := v.map (fun a => min a 2)

def Rel (A B : List (List ℕ)) : Prop := ∀ v ∈ A, ∃ v2 ∈ B, v = cp v2

def RelR (R1 R2 : List (List (List ℕ))) : Prop :=
  R1.length = R2.length ∧ ∀ i, Rel (R1.getD i []) (R2.getD i [])

lemma cp_capAdd (a b : List ℕ) : capAdd 1 (cp a) (cp b) = cp (capAdd 2 a b) := by
  induction a generalizing b with
  | nil => simp [capAdd, cp]
  | cons x a ih =>
    cases b with
    | nil => simp [capAdd, cp]
    | cons y b =>
      have h := ih b
      simp only [capAdd, cp, List.map_cons, List.zipWith_cons_cons] at h ⊢
      rw [h]
      congr 1
      omega

lemma rel_andStep (A A2 B B2 : List (List ℕ)) (hA : Rel A A2) (hB : Rel B B2) :
    Rel (andStep 1 A B) (andStep 2 A2 B2) := by
  intro v hv
  obtain ⟨a, ha, b, hb, hveq⟩ := mem_andStep 1 A B v hv
  obtain ⟨a2, ha2, haeq⟩ := hA a ha
  obtain ⟨b2, hb2, hbeq⟩ := hB b hb
  refine ⟨capAdd 2 a2 b2, mem_andStep_of 2 A2 B2 a2 b2 ha2 hb2, ?_⟩
  rw [hveq, haeq, hbeq]
  exact cp_capAdd a2 b2

lemma rel_andFold (R1 R2 : List (List (List ℕ)))
    (h : ∀ i, Rel (R1.getD i []) (R2.getD i [])) (ins : List ℕ) (acc1 acc2 : List (List ℕ))
    (hacc : Rel acc1 acc2) :
    Rel ((ins.map fun i => R1.getD i []).foldl (andStep 1) acc1)
      ((ins.map fun i => R2.getD i []).foldl (andStep 2) acc2) := by
  induction ins generalizing acc1 acc2 with
  | nil => exact hacc
  | cons i ins ih =>
    exact ih (andStep 1 acc1 (R1.getD i [])) (andStep 2 acc2 (R2.getD i []))
      (rel_andStep _ _ _ _ hacc (h i))

lemma rel_orFold (R1 R2 : List (List (List ℕ)))
    (h : ∀ i, Rel (R1.getD i []) (R2.getD i [])) (ins : List ℕ) :
    Rel ((ins.map fun i => R1.getD i []).foldl (fun acc A => A.foldl insertNew acc) [])
      ((ins.map fun i => R2.getD i []).foldl (fun acc A => A.foldl insertNew acc) []) := by
  intro v hv
  rw [mem_orFold] at hv
  rcases hv with hv | ⟨A, hA, hv⟩
  · simp at hv
  · rw [List.mem_map] at hA
    obtain ⟨i, hi, hAeq⟩ := hA
    rw [← hAeq] at hv
    obtain ⟨v2, hv2, hveq⟩ := h i v hv
    refine ⟨v2, ?_, hveq⟩
    rw [mem_orFold]
    exact Or.inr ⟨R2.getD i [], List.mem_map.2 ⟨i, hi, rfl⟩, hv2⟩

lemma rel_zero (S : List ℕ) : Rel [S.map fun _ => 0] [S.map fun _ => 0] := by
  intro v hv
  have hv2 : v = S.map (fun _ => 0) := List.mem_singleton.1 hv
  refine ⟨S.map fun _ => 0, List.mem_singleton.2 rfl, ?_⟩
  rw [hv2]
  unfold cp
  rw [List.map_map]
  apply List.map_congr_left
  intro j _
  rfl

lemma rel_FR (S : List ℕ) (R1 R2 : List (List (List ℕ)))
    (h : ∀ i, Rel (R1.getD i []) (R2.getD i [])) (g : Gate) :
    Rel (FR S 1 R1 g) (FR S 2 R2 g) := by
  by_cases hor : g.op = GateOp.or
  · rw [FR_or S 1 R1 g hor, FR_or S 2 R2 g hor]
    exact rel_orFold R1 R2 h g.inputs
  · by_cases hand : g.op = GateOp.and
    · rw [FR_and S 1 R1 g hand, FR_and S 2 R2 g hand]
      exact rel_andFold R1 R2 h g.inputs _ _ (rel_zero S)
    · rw [FR_other S 1 R1 g hor hand, FR_other S 2 R2 g hor hand]
      intro v hv
      simp at hv

lemma getD_snoc (R : List (List (List ℕ))) (x : List (List ℕ)) (i : ℕ) :
    (R ++ [x]).getD i [] = if i < R.length then R.getD i [] else if i = R.length then x else [] := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2
    simp
  · rw [List.getElem?_eq_none (by simp only [List.length_append, List.length_singleton]; omega)]
    rfl

lemma rel_step (S : List ℕ) (R1 R2 : List (List (List ℕ))) (hR : RelR R1 R2) (g : Gate) :
    RelR (stepR S 1 R1 g) (stepR S 2 R2 g) := by
  obtain ⟨hl, h⟩ := hR
  have hF := rel_FR S R1 R2 h g
  refine ⟨by simp [stepR, hl], ?_⟩
  intro i
  unfold stepR
  rw [getD_snoc, getD_snoc, hl]
  split_ifs
  · exact h i
  · exact hF
  · intro v hv
    simp at hv

lemma rel_fold (S : List ℕ) (gs : List Gate) (R1 R2 : List (List (List ℕ))) (hR : RelR R1 R2) :
    RelR (gs.foldl (stepR S 1) R1) (gs.foldl (stepR S 2) R2) := by
  induction gs generalizing R1 R2 with
  | nil => exact hR
  | cons g gs ih =>
    rw [List.foldl_cons, List.foldl_cons]
    exact ih _ _ (rel_step S R1 R2 hR g)

lemma leaf_pos (S : List ℕ) (k i : ℕ) (hm : i ∈ S) :
    leafVectors S (k + 1) i = [S.map fun j => if j = i then 1 else 0] := by
  unfold leafVectors
  rw [if_pos hm]
  have e : min 1 (k + 1 + 1) = 1 := by omega
  rw [e]

lemma leaf_neg (S : List ℕ) (k i : ℕ) (hm : ¬ i ∈ S) : leafVectors S k i = [] := by
  unfold leafVectors
  rw [if_neg hm]

lemma rel_leaf (S : List ℕ) (i : ℕ) : Rel (leafVectors S 1 i) (leafVectors S 2 i) := by
  intro v hv
  by_cases hm : i ∈ S
  · rw [leaf_pos S 0 i hm] at hv
    rw [leaf_pos S 1 i hm]
    have hv2 := List.mem_singleton.1 hv
    refine ⟨S.map fun j => if j = i then 1 else 0, List.mem_singleton.2 rfl, ?_⟩
    rw [hv2]
    unfold cp
    rw [List.map_map]
    apply List.map_congr_left
    intro j _
    by_cases hj : j = i <;> simp [hj]
  · rw [leaf_neg S 1 i hm] at hv
    simp at hv

lemma rel_init (n : ℕ) (S : List ℕ) :
    RelR ((List.range n).map (leafVectors S 1)) ((List.range n).map (leafVectors S 2)) := by
  refine ⟨by simp, ?_⟩
  intro i
  by_cases hi : i < n
  · have e : ∀ k, ((List.range n).map (leafVectors S k)).getD i [] = leafVectors S k i := by
      intro k
      simp [List.getD_eq_getElem?_getD, hi]
    rw [e, e]
    exact rel_leaf S i
  · have e : ∀ k, ((List.range n).map (leafVectors S k)).getD i [] = [] := by
      intro k
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by simp only [List.length_map, List.length_range]; omega)]
      rfl
    rw [e]
    intro v hv
    simp at hv

lemma getD_le (v2 : List ℕ) (i : ℕ) (h : (cp v2).all (fun a => decide (a ≤ 1)) = true) :
    v2.getD i 0 ≤ 1 := by
  rw [List.all_eq_true] at h
  rw [List.getD_eq_getElem?_getD]
  by_cases hi : i < v2.length
  · rw [List.getElem?_eq_getElem hi]
    have h1 : min v2[i] 2 ∈ cp v2 := by
      unfold cp
      exact List.mem_map.2 ⟨v2[i], List.getElem_mem hi, rfl⟩
    have h2 := of_decide_eq_true (h _ h1)
    simp only [Option.getD_some]
    omega
  · rw [List.getElem?_eq_none (by omega)]
    simp

theorem main_aux : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (u w : ℕ), PEqualNP.ReadK.readsAtMost C n [u, w] 1 = true → ((PEqualNP.ReadK.readVectors C n [u, w] 2).getD C.output []).any (fun v_1 => decide (v_1.getD 0 0 ≤ 1 ∧ v_1.getD 1 0 ≤ 1)) = true := by
  intro n C u w h
  unfold readsAtMost at h
  rw [List.any_eq_true] at h
  obtain ⟨v, hv, hall⟩ := h
  have hrel : RelR (readVectors C n [u, w] 1) (readVectors C n [u, w] 2) := by
    rw [readVectors_eq, readVectors_eq]
    exact rel_fold _ _ _ _ (rel_init n _)
  obtain ⟨v2, hv2, hveq⟩ := hrel.2 C.output v hv
  rw [hveq] at hall
  rw [List.any_eq_true]
  exact ⟨v2, hv2, decide_eq_true ⟨getD_le v2 0 hall, getD_le v2 1 hall⟩⟩

end PEqualNP.Outside.L_meta_2472

theorem PEqualNP.Outside.L_meta_2472 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (u w : ℕ), PEqualNP.ReadK.readsAtMost C n [u, w] 1 = true → ((PEqualNP.ReadK.readVectors C n [u, w] 2).getD C.output []).any (fun v_1 => decide (v_1.getD 0 0 ≤ 1 ∧ v_1.getD 1 0 ≤ 1)) = true :=
  PEqualNP.Outside.L_meta_2472.main_aux
