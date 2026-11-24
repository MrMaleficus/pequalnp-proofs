import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2482

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


lemma W_or_up (n : ℕ) (C : Circuit) (z : Fin n → Bool) (j i : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (hz : W n C z i = true) : W n C z (n + j) = true := by
  rw [W_gate n C z j hj, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
  exact ⟨i, hi, by simp only [hlt, ite_true]; exact hz⟩

theorem gateAt_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq C j hj]; exact List.getElem_mem hj

/-- One upward step along an OR gate. -/
def stp (n : ℕ) (C : Circuit) : ℕ → ℕ → Prop :=
  fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧
    (gateAt C rj).op = GateOp.or ∧ ra ∈ (gateAt C rj).inputs

/-- The line set of a wire: the lines whose input alone makes it true. -/
def LS (n M : ℕ) (C : Circuit) (lw : Fin M → ℕ) (w : ℕ) : Set (Fin M) :=
  {m | W n C (fun k : Fin n => decide (k.val = lw m)) w = true}

theorem stp_mk (n : ℕ) (C : Circuit) (a k : ℕ) (hlt : a < n + k) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (hmem : a ∈ (gateAt C k).inputs) :
    stp n C a (n + k) := by
  unfold stp
  exact ⟨hlt, k, rfl, hk, hop, hmem⟩

theorem orSets_R (n : ℕ) (C : Circuit) : ∀ k, k < C.gates.length →
    ∀ x, x ∈ (orSets n C).getD k [] → Relation.ReflTransGen (stp n C) (n + x) (n + k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk x hx
    rw [orSets_mem_iff n C k x hk] at hx
    rcases hx with h | ⟨hop, w, hw, hn, hlt, hx⟩
    · rw [h]
    · have h1 := ih (w - n) (by omega) (by omega) x hx
      have e : n + (w - n) = w := by omega
      rw [e] at h1
      exact h1.tail (stp_mk n C w k hlt hk hop hw)

theorem orReaches_R (n : ℕ) (C : Circuit) (F j : ℕ) (h : OrReaches n C F j) :
    Relation.ReflTransGen (stp n C) (n + j) F := by
  obtain ⟨hn, hj⟩ := h
  have hk : F - n < C.gates.length := by
    by_contra hge
    have hlen : (orSets n C).length = C.gates.length := by
      unfold orSets
      rw [orFold_length]
      simp
    have hle : (orSets n C).length ≤ F - n := by omega
    have hnil : (orSets n C).getD (F - n) [] = [] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hle]
    rw [hnil] at hj
    simp at hj
  have h1 := orSets_R n C (F - n) hk j hj
  have e : n + (F - n) = F := by omega
  rw [e] at h1
  exact h1

theorem reach (n : ℕ) (C : Circuit) (a F : ℕ)
    (h : (∃ i : Fin n, i.val = a ∧ i ∈ orIn n C F) ∨
      (∃ j : ℕ, a = n + j ∧ OrReaches n C F j)) :
    Relation.ReflTransGen (stp n C) a F := by
  rcases h with ⟨i, hi, hin⟩ | ⟨j, hj, hr⟩
  · rw [mem_orIn] at hin
    rcases hin with h1 | ⟨k, hk, hr, hop, hmem⟩
    · have e : a = F := hi.symm.trans h1
      rw [e]
    · have h2 := orReaches_R n C F k hr
      have hlt : a < n + k := by
        have := i.isLt
        omega
      have hmem2 : a ∈ (gateAt C k).inputs := by
        rw [← hi]; exact hmem
      exact Relation.ReflTransGen.head (stp_mk n C a k hlt hk hop hmem2) h2
  · rw [hj]
    exact orReaches_R n C F j hr

theorem two_inputs (l : List ℕ) (hl : l.length = 2) (b : ℕ) (hb : b ∈ l) :
    b = l.getD 0 0 ∨ b = l.getD 1 0 := by
  rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, t⟩⟩⟩
  · simp at hl
  · simp at hl
  · simpa using hb
  · simp at hl

theorem key (n M : ℕ) (C : Circuit) (hlen : ∀ g ∈ C.gates, g.inputs.length = 2)
    (S : ℕ → Set (Fin M)) (hmono : ∀ a b, stp n C a b → S a ⊆ S b)
    (l : Fin M) (a : ℕ) (hla : l ∈ S a) (hua : ∀ m ∈ S a, m = l) (F : ℕ)
    (hF : Relation.ReflTransGen (stp n C) a F) :
    l ∈ S F ∧ (2 ≤ (S F).ncard →
      ∃ jo, jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or ∧ S (n + jo) ⊆ S F ∧
        2 ≤ (S (n + jo)).ncard ∧
        ∃ i : Fin 2, l ∈ S ((gateAt C jo).inputs.getD i.val 0) ∧
          ∀ m ∈ S ((gateAt C jo).inputs.getD i.val 0), m = l) := by
  induction hF with
  | refl =>
    refine ⟨hla, fun h2 => ?_⟩
    exfalso
    obtain ⟨x, y, hx, hy, hxy⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).mp h2
    exact hxy ((hua x hx).trans (hua y hy).symm)
  | @tail b c hab hbc ih =>
    obtain ⟨hlb, ih2⟩ := ih
    have hsub := hmono b c hbc
    refine ⟨hsub hlb, fun h2 => ?_⟩
    by_cases hb : 2 ≤ (S b).ncard
    · obtain ⟨jo, h1, h3, h4, h5, h6⟩ := ih2 hb
      exact ⟨jo, h1, h3, fun m hm => hsub (h4 hm), h5, h6⟩
    · have hbc2 := hbc
      obtain ⟨_, rj, hc, hrj, hop, hmem⟩ := hbc2
      subst hc
      have hl : (gateAt C rj).inputs.length = 2 := hlen _ (gateAt_mem C rj hrj)
      have huniq : ∀ m ∈ S b, m = l := by
        intro q hq
        by_contra hne
        apply hb
        have hs2 : ({q, l} : Set (Fin M)) ⊆ S b := by
          intro r hr
          rcases Set.mem_insert_iff.mp hr with h | h
          · rw [h]; exact hq
          · rw [Set.mem_singleton_iff.mp h]; exact hlb
        calc 2 = ({q, l} : Set (Fin M)).ncard := (Set.ncard_pair hne).symm
          _ ≤ _ := Set.ncard_le_ncard hs2 (Set.toFinite _)
      have hcase : b = (gateAt C rj).inputs.getD 0 0 ∨ b = (gateAt C rj).inputs.getD 1 0 :=
        two_inputs _ hl b hmem
      refine ⟨rj, hrj, hop, fun m hm => hm, h2, ?_⟩
      rcases hcase with h0 | h1
      · refine ⟨⟨0, by omega⟩, ?_, ?_⟩
        · show l ∈ S ((gateAt C rj).inputs.getD 0 0)
          rw [← h0]; exact hlb
        · intro m hm
          apply huniq m
          rw [h0]; exact hm
      · refine ⟨⟨1, by omega⟩, ?_, ?_⟩
        · show l ∈ S ((gateAt C rj).inputs.getD 1 0)
          rw [← h1]; exact hlb
        · intro m hm
          apply huniq m
          rw [h1]; exact hm

theorem main_aux : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit) (A : Finset (Fin N × Fin M)), PEqualNP.TopForm.IsAO2 n C → (Function.Injective pw ∧ Function.Injective lw ∧ (∀ p_1 l_1, pw p_1 ≠ lw l_1) ∧ (∀ p_2, pw p_2 < n) ∧ (∀ l_2, lw l_2 < n)) → (∀ p_3 p_4 l_3 l_4, p_3 ≠ p_4 → l_3 ≠ l_4 → ¬ (I p_3 l_3 ∧ I p_4 l_3 ∧ I p_3 l_4 ∧ I p_4 l_4)) → (∀ pl ∈ A, I pl.1 pl.2 ∧ (∃ a_1 F_1, ((∃ i_1 : Fin n, i_1.val = a_1 ∧ i_1 ∈ PEqualNP.TopForm.orIn n C (F_1)) ∨ (∃ j_1 : ℕ, a_1 = n + j_1 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (F_1) j_1)) ∧ {a_3 | PEqualNP.CleanedNonEdge.wireVal n C (a_1) (fun k_2 : Fin n => decide (k_2.val = lw a_3)) = true} = {pl.2} ∧ {a_2 | PEqualNP.CleanedNonEdge.wireVal n C (F_1) (fun k_1 : Fin n => decide (k_1.val = lw a_2)) = true} ⊆ {m_1 | I pl.1 m_1} ∧ 2 ≤ ({a_4 | PEqualNP.CleanedNonEdge.wireVal n C (F_1) (fun k_3 : Fin n => decide (k_3.val = lw a_4)) = true}).ncard)) → A.card ≤ 2 * {j_2 : ℕ | j_2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard := by
  intro n N M pw lw I C A hAO hinj hK hA
  have hlen := hAO.2.2
  have hmono : ∀ a b, stp n C a b → LS n M C lw a ⊆ LS n M C lw b := by
    intro a b hab m hm
    obtain ⟨hlt, rj, hb, hrj, hop, hin⟩ := hab
    subst hb
    exact W_or_up n C _ rj a hrj hop hin hlt hm
  have hex : ∀ pl ∈ A, ∃ y : ℕ × Fin 2,
      (y.1 < C.gates.length ∧ (gateAt C y.1).op = GateOp.or) ∧
      2 ≤ (LS n M C lw (n + y.1)).ncard ∧
      (∀ m ∈ LS n M C lw (n + y.1), I pl.1 m) ∧
      pl.2 ∈ LS n M C lw ((gateAt C y.1).inputs.getD y.2.val 0) ∧
      ∀ m ∈ LS n M C lw ((gateAt C y.1).inputs.getD y.2.val 0), m = pl.2 := by
    intro pl hpl
    obtain ⟨_, a, F, hreach, hLa, hLF, h2⟩ := hA pl hpl
    have hLa2 : LS n M C lw a = {pl.2} := hLa
    have hLF2 : LS n M C lw F ⊆ {m | I pl.1 m} := hLF
    have h22 : 2 ≤ (LS n M C lw F).ncard := h2
    have hR := reach n C a F hreach
    have hk := key n M C hlen (LS n M C lw) hmono pl.2 a
      (by rw [hLa2]; exact Set.mem_singleton _)
      (by intro m hm; rw [hLa2] at hm; exact Set.mem_singleton_iff.mp hm) F hR
    obtain ⟨jo, h1, h3, h4, h5, i, h6, h7⟩ := hk.2 h22
    exact ⟨(jo, i), ⟨h1, h3⟩, h5, fun m hm => hLF2 (h4 hm), h6, h7⟩
  choose! f hf using hex
  have hO : {j_2 : ℕ | j_2 < C.gates.length ∧ (gateAt C j_2).op = GateOp.or}.Finite :=
    (Set.finite_lt_nat C.gates.length).subset (fun jo h => h.1)
  have h1 : (↑A : Set (Fin N × Fin M)).ncard ≤
      ({j_2 : ℕ | j_2 < C.gates.length ∧ (gateAt C j_2).op = GateOp.or} ×ˢ
        (Set.univ : Set (Fin 2))).ncard := by
    refine Set.ncard_le_ncard_of_injOn f ?_ ?_ (hO.prod Set.finite_univ)
    · intro ex hex
      exact ⟨(hf ex (Finset.mem_coe.mp hex)).1, Set.mem_univ _⟩
    · intro ex hex ex2 hex2 heq
      have P1 := hf ex (Finset.mem_coe.mp hex)
      have P2 := hf ex2 (Finset.mem_coe.mp hex2)
      rw [← heq] at P2
      obtain ⟨_, h2a, hla, hra, hua⟩ := P1
      obtain ⟨_, _, hlb, hrb, hub⟩ := P2
      have e2 : ex2.2 = ex.2 := hua ex2.2 hrb
      obtain ⟨m1, m2, hm1, hm2, hm12⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).mp h2a
      have e1 : ex.1 = ex2.1 := by
        by_contra hp
        exact hK ex.1 ex2.1 m1 m2 hp hm12 ⟨hla m1 hm1, hlb m1 hm1, hla m2 hm2, hlb m2 hm2⟩
      exact Prod.ext e1 e2.symm
  rw [Set.ncard_prod, Set.ncard_univ, Nat.card_fin, Set.ncard_coe_finset] at h1
  omega

end PEqualNP.Outside.L_meta_2482

theorem PEqualNP.Outside.L_meta_2482 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit) (A : Finset (Fin N × Fin M)), PEqualNP.TopForm.IsAO2 n C → (Function.Injective pw ∧ Function.Injective lw ∧ (∀ p_1 l_1, pw p_1 ≠ lw l_1) ∧ (∀ p_2, pw p_2 < n) ∧ (∀ l_2, lw l_2 < n)) → (∀ p_3 p_4 l_3 l_4, p_3 ≠ p_4 → l_3 ≠ l_4 → ¬ (I p_3 l_3 ∧ I p_4 l_3 ∧ I p_3 l_4 ∧ I p_4 l_4)) → (∀ pl ∈ A, I pl.1 pl.2 ∧ (∃ a_1 F_1, ((∃ i_1 : Fin n, i_1.val = a_1 ∧ i_1 ∈ PEqualNP.TopForm.orIn n C (F_1)) ∨ (∃ j_1 : ℕ, a_1 = n + j_1 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (F_1) j_1)) ∧ {a_3 | PEqualNP.CleanedNonEdge.wireVal n C (a_1) (fun k_2 : Fin n => decide (k_2.val = lw a_3)) = true} = {pl.2} ∧ {a_2 | PEqualNP.CleanedNonEdge.wireVal n C (F_1) (fun k_1 : Fin n => decide (k_1.val = lw a_2)) = true} ⊆ {m_1 | I pl.1 m_1} ∧ 2 ≤ ({a_4 | PEqualNP.CleanedNonEdge.wireVal n C (F_1) (fun k_3 : Fin n => decide (k_3.val = lw a_4)) = true}).ncard)) → A.card ≤ 2 * {j_2 : ℕ | j_2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard :=
  PEqualNP.Outside.L_meta_2482.main_aux
