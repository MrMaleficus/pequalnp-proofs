import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2415

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

abbrev st (n : ℕ) (C : Circuit) (ra rb : ℕ) : Prop :=
  ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (gateAt C rj).op = GateOp.or ∧
    ra ∈ (gateAt C rj).inputs

abbrev RR (n : ℕ) (C : Circuit) : ℕ → ℕ → Prop := Relation.ReflTransGen (st n C)

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma rr_le (n : ℕ) (C : Circuit) (a b : ℕ) (h : RR n C a b) : a ≤ b := by
  induction h with
  | refl => exact le_rfl
  | tail _ hs ih => exact le_trans ih (le_of_lt hs.1)

lemma rr_cases (n : ℕ) (C : Circuit) (m w : ℕ) (h : RR n C m w) :
    m = w ∨ ∃ c, RR n C m c ∧ st n C c w := by
  rcases Relation.ReflTransGen.cases_tail h with h1 | ⟨c, hc, hs⟩
  · exact Or.inl h1.symm
  · exact Or.inr ⟨c, hc, hs⟩

lemma rr_step (n : ℕ) (C : Circuit) (k c i : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (hc : c ∈ (gateAt C k).inputs) (hlt : c < n + k)
    (h : RR n C i c) : RR n C i (n + k) := by
  have hs : st n C c (n + k) := ⟨hlt, k, rfl, hk, hop, hc⟩
  exact Relation.ReflTransGen.tail h hs

lemma rr_notor (n : ℕ) (C : Circuit) (m w : ℕ)
    (hw : ¬ ∃ k, w = n + k ∧ k < C.gates.length ∧ (gateAt C k).op = GateOp.or)
    (h : RR n C m w) : m = w := by
  rcases rr_cases n C m w h with h1 | ⟨c, _, hs⟩
  · exact h1
  · exfalso
    obtain ⟨_, rj, h1, h2, h3, _⟩ := hs
    exact hw ⟨rj, h1, h2, h3⟩

noncomputable def LL (n : ℕ) (C : Circuit) {α : Type} (labelled : Finset ℕ)
    (lab : ℕ → Finset α) (w : ℕ) : Finset α := by
  classical
  exact (labelled.filter (fun m => RR n C m w)).biUnion lab

lemma mem_LL (n : ℕ) (C : Circuit) {α : Type} (labelled : Finset ℕ)
    (lab : ℕ → Finset α) (w : ℕ) (x : α) :
    x ∈ LL n C labelled lab w ↔ ∃ m ∈ labelled, RR n C m w ∧ x ∈ lab m := by
  classical
  unfold LL
  simp only [Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨m, ⟨h1, h2⟩, h3⟩
    exact ⟨m, h1, h2, h3⟩
  · rintro ⟨m, h1, h2, h3⟩
    exact ⟨m, ⟨h1, h2⟩, h3⟩

lemma ncard_LL (n : ℕ) (C : Circuit) {α : Type} (labelled : Finset ℕ)
    (lab : ℕ → Finset α) (w : ℕ) :
    ({x3 : α | ∃ m3 ∈ labelled, RR n C m3 w ∧ x3 ∈ lab m3}).ncard =
      (LL n C labelled lab w).card := by
  have hE : {x3 : α | ∃ m3 ∈ labelled, RR n C m3 w ∧ x3 ∈ lab m3} =
      ((LL n C labelled lab w : Finset α) : Set α) := by
    ext x
    rw [Set.mem_ofPred_eq, Finset.mem_coe]
    exact (mem_LL n C labelled lab w x).symm
  rw [hE, Set.ncard_coe_finset]

lemma LL_small_notor (n : ℕ) (C : Circuit) {α : Type} (labelled : Finset ℕ)
    (lab : ℕ → Finset α) (hlab : ∀ m ∈ labelled, (lab m).card ≤ 2) (w : ℕ)
    (hw : ¬ ∃ k, w = n + k ∧ k < C.gates.length ∧ (gateAt C k).op = GateOp.or) :
    (LL n C labelled lab w).card ≤ 2 := by
  by_cases hwl : w ∈ labelled
  · refine le_trans (Finset.card_le_card ?_) (hlab w hwl)
    intro x hx
    obtain ⟨m, hm, hr, hxm⟩ := (mem_LL n C labelled lab w x).1 hx
    have hmw := rr_notor n C m w hw hr
    rw [← hmw]
    exact hxm
  · have hE : LL n C labelled lab w = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro x hx
      obtain ⟨m, hm, hr, hxm⟩ := (mem_LL n C labelled lab w x).1 hx
      have hmw := rr_notor n C m w hw hr
      rw [hmw] at hm
      exact hwl hm
    rw [hE, Finset.card_empty]
    exact Nat.zero_le _

lemma LL_or (n : ℕ) (C : Circuit) {α : Type} (labelled : Finset ℕ)
    (lab : ℕ → Finset α)
    (hnl : ∀ m ∈ labelled, m < n ∨ ∃ j, m = n + j ∧ j < C.gates.length ∧
      (gateAt C j).op = GateOp.and)
    (k a b : ℕ) (hop : (gateAt C k).op = GateOp.or)
    (hin : (gateAt C k).inputs = [a, b]) (x : α)
    (hx : x ∈ LL n C labelled lab (n + k)) :
    x ∈ LL n C labelled lab a ∨ x ∈ LL n C labelled lab b := by
  obtain ⟨m, hm, hr, hxm⟩ := (mem_LL n C labelled lab (n + k) x).1 hx
  rcases rr_cases n C m (n + k) hr with h1 | ⟨c, hc, hs⟩
  · exfalso
    rcases hnl m hm with h2 | ⟨j, h2, _, h4⟩
    · omega
    · have hjk : j = k := by omega
      rw [hjk, hop] at h4
      cases h4
  · obtain ⟨_, rj, h1, _, _, h4⟩ := hs
    have hjk : rj = k := by omega
    rw [hjk, hin, List.mem_cons, List.mem_singleton] at h4
    rcases h4 with h5 | h5
    · rw [h5] at hc
      exact Or.inl ((mem_LL n C labelled lab a x).2 ⟨m, hm, hc, hxm⟩)
    · rw [h5] at hc
      exact Or.inr ((mem_LL n C labelled lab b x).2 ⟨m, hm, hc, hxm⟩)

def bigP (n : ℕ) (C : Circuit) {α : Type} (labelled : Finset ℕ)
    (lab : ℕ → Finset α) (Q : Finset ℕ) (k : ℕ) : Prop :=
  (gateAt C k).op = GateOp.or ∧ (∃ w ∈ Q, RR n C (n + k) w) ∧
    3 ≤ (LL n C labelled lab (n + k)).card

noncomputable def big (n : ℕ) (C : Circuit) {α : Type} (labelled : Finset ℕ)
    (lab : ℕ → Finset α) (Q : Finset ℕ) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter (bigP n C labelled lab Q)

lemma mem_big (n : ℕ) (C : Circuit) {α : Type} (labelled : Finset ℕ)
    (lab : ℕ → Finset α) (Q : Finset ℕ) (k : ℕ) :
    k ∈ big n C labelled lab Q ↔ (k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧
      (∃ w ∈ Q, RR n C (n + k) w) ∧ 3 ≤ (LL n C labelled lab (n + k)).card) := by
  classical
  unfold big
  simp only [Finset.mem_filter, Finset.mem_range, bigP]

lemma big_mono (n : ℕ) (C : Circuit) {α : Type} (labelled : Finset ℕ)
    (lab : ℕ → Finset α) (Q Q' : Finset ℕ) (h : Q ⊆ Q') :
    big n C labelled lab Q ⊆ big n C labelled lab Q' := by
  intro i hi
  obtain ⟨h1, h2, ⟨w, hw, hr⟩, h3⟩ := (mem_big n C labelled lab Q i).1 hi
  exact (mem_big n C labelled lab Q' i).2 ⟨h1, h2, ⟨w, h hw, hr⟩, h3⟩

lemma count (n : ℕ) (C : Circuit) {α : Type} (labelled : Finset ℕ)
    (lab : ℕ → Finset α) (hRB : ReadsBack n C)
    (hlen2 : ∀ g ∈ C.gates, g.inputs.length = 2)
    (hnl : ∀ m ∈ labelled, m < n ∨ ∃ j, m = n + j ∧ j < C.gates.length ∧
      (gateAt C j).op = GateOp.and)
    (hlab : ∀ m ∈ labelled, (lab m).card ≤ 2) :
    ∀ (m : ℕ) (Q : Finset ℕ), (∀ w ∈ Q, w < m) → ∀ T : Finset α,
      (∀ x ∈ T, ∃ w ∈ Q, x ∈ LL n C labelled lab w) →
      T.card ≤ 2 * (Q.card + (big n C labelled lab Q).card) := by
  classical
  intro m
  induction m with
  | zero =>
    intro Q hQ T hT
    have hTe : T = ∅ := Finset.eq_empty_of_forall_notMem (fun x hx => by
      obtain ⟨w, hw, _⟩ := hT x hx
      have := hQ w hw
      omega)
    rw [hTe, Finset.card_empty]
    exact Nat.zero_le _
  | succ m ih =>
    intro Q hQ T hT
    by_cases hm : m ∈ Q
    · have hQ0 : ∀ w ∈ Q.erase m, w < m := by
        intro w hw
        have h1 := Finset.ne_of_mem_erase hw
        have h2 := hQ w (Finset.mem_of_mem_erase hw)
        omega
      have hcardQ : (Q.erase m).card + 1 = Q.card := Finset.card_erase_add_one hm
      by_cases hs : (∃ k, m = n + k ∧ k < C.gates.length ∧ (gateAt C k).op = GateOp.or) ∧
          3 ≤ (LL n C labelled lab m).card
      · obtain ⟨⟨k, rfl, hs2, hs3⟩, hs4⟩ := hs
        have hmem : gateAt C k ∈ C.gates := by
          rw [gateAt_eq C k hs2]
          exact List.getElem_mem hs2
        have hl := hlen2 _ hmem
        obtain ⟨a, b, hin⟩ : ∃ a b, (gateAt C k).inputs = [a, b] := List.length_eq_two.1 hl
        have hma : a ∈ (gateAt C k).inputs := by rw [hin]; simp
        have hmb : b ∈ (gateAt C k).inputs := by rw [hin]; simp
        have ha : a < n + k := hRB k hs2 a hma
        have hb : b < n + k := hRB k hs2 b hmb
        have hQ' : ∀ w ∈ insert a (insert b (Q.erase (n + k))), w < n + k := by
          intro w hw
          rw [Finset.mem_insert, Finset.mem_insert] at hw
          rcases hw with h | h | h
          · omega
          · omega
          · exact hQ0 w h
        have hT' : ∀ x ∈ T, ∃ w ∈ insert a (insert b (Q.erase (n + k))),
            x ∈ LL n C labelled lab w := by
          intro x hx
          obtain ⟨w, hw, hxw⟩ := hT x hx
          by_cases hwk : w = n + k
          · rw [hwk] at hxw
            rcases LL_or n C labelled lab hnl k a b hs3 hin x hxw with h | h
            · exact ⟨a, Finset.mem_insert_self _ _, h⟩
            · exact ⟨b, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), h⟩
          · exact ⟨w, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
              (Finset.mem_erase.2 ⟨hwk, hw⟩)), hxw⟩
        have hih := ih _ hQ' T hT'
        have hc' : (insert a (insert b (Q.erase (n + k)))).card ≤
            (Q.erase (n + k)).card + 2 := by
          have h1 := Finset.card_insert_le a (insert b (Q.erase (n + k)))
          have h2 := Finset.card_insert_le b (Q.erase (n + k))
          omega
        have hsub : big n C labelled lab (insert a (insert b (Q.erase (n + k)))) ⊆
            (big n C labelled lab Q).erase k := by
          intro i hi
          obtain ⟨h1, h2, ⟨w, hw, hr⟩, h3⟩ := (mem_big n C labelled lab _ i).1 hi
          have hle := rr_le n C (n + i) w hr
          have hwlt := hQ' w hw
          rw [Finset.mem_erase]
          refine ⟨by omega, (mem_big n C labelled lab Q i).2 ⟨h1, h2, ?_, h3⟩⟩
          rw [Finset.mem_insert, Finset.mem_insert] at hw
          rcases hw with h | h | h
          · rw [h] at hr
            exact ⟨n + k, hm, rr_step n C k a (n + i) hs2 hs3 hma ha hr⟩
          · rw [h] at hr
            exact ⟨n + k, hm, rr_step n C k b (n + i) hs2 hs3 hmb hb hr⟩
          · exact ⟨w, Finset.mem_of_mem_erase h, hr⟩
        have hkmem : k ∈ big n C labelled lab Q :=
          (mem_big n C labelled lab Q k).2
            ⟨hs2, hs3, ⟨n + k, hm, Relation.ReflTransGen.refl⟩, hs4⟩
        have hc2 : ((big n C labelled lab Q).erase k).card + 1 =
            (big n C labelled lab Q).card := Finset.card_erase_add_one hkmem
        have hc3 := Finset.card_le_card hsub
        omega
      · have hsmall : (LL n C labelled lab m).card ≤ 2 := by
          by_cases hs' : ∃ k, m = n + k ∧ k < C.gates.length ∧ (gateAt C k).op = GateOp.or
          · by_contra hc
            exact hs ⟨hs', by omega⟩
          · exact LL_small_notor n C labelled lab hlab m hs'
        obtain ⟨B, hB⟩ : ∃ B : Finset α, ∀ x, x ∈ B ↔ (x ∈ T ∧ ¬ x ∈ LL n C labelled lab m) :=
          ⟨T.filter (fun x => ¬ x ∈ LL n C labelled lab m), fun x => Finset.mem_filter⟩
        have hT2 : ∀ x ∈ B, ∃ w ∈ Q.erase m, x ∈ LL n C labelled lab w := by
          intro x hx
          obtain ⟨hxT, hxn⟩ := (hB x).1 hx
          obtain ⟨w, hw, hxw⟩ := hT x hxT
          refine ⟨w, Finset.mem_erase.2 ⟨?_, hw⟩, hxw⟩
          intro hwm
          rw [hwm] at hxw
          exact hxn hxw
        have hsubT : T ⊆ LL n C labelled lab m ∪ B := by
          intro x hx
          rw [Finset.mem_union]
          by_cases hxl : x ∈ LL n C labelled lab m
          · exact Or.inl hxl
          · exact Or.inr ((hB x).2 ⟨hx, hxl⟩)
        have hun := Finset.card_union_le (LL n C labelled lab m) B
        have hcT := Finset.card_le_card hsubT
        have hih := ih _ hQ0 B hT2
        have hmono := Finset.card_le_card
          (big_mono n C labelled lab _ _ (Finset.erase_subset m Q))
        omega
    · refine ih Q (fun w hw => ?_) T hT
      have h1 := hQ w hw
      have h2 : w ≠ m := fun h => hm (h ▸ hw)
      omega


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

lemma or_up (n : ℕ) (C : Circuit) (z : Fin n → Bool) (a b : ℕ)
    (h : a < b ∧ ∃ rj, b = n + rj ∧ rj < C.gates.length ∧
      (gateAt C rj).op = GateOp.or ∧ a ∈ (gateAt C rj).inputs)
    (ha : W n C z a = true) : W n C z b = true := by
  obtain ⟨hlt, rj, rfl, hj, hop, hin⟩ := h
  rw [W_gate n C z rj hj, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
  exact ⟨a, hin, by simp only [hlt, ite_true]; exact ha⟩

lemma path_up (n : ℕ) (C : Circuit) (z : Fin n → Bool) (a b : ℕ)
    (h : Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧
      (gateAt C rj).op = GateOp.or ∧ ra ∈ (gateAt C rj).inputs) a b)
    (ha : W n C z a = true) : W n C z b = true := by
  induction h with
  | refl => exact ha
  | tail _ hstep ih => exact or_up n C z _ _ hstep ih


private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

private lemma step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp [step, List.getD, List.getElem?_append_left hi]

private lemma step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp [step, List.getD]

private def Wg {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl step (List.ofFn x)

private lemma Wg_len {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    (Wg gs x).length = n + gs.length := by
  have h : ∀ (gs : List Gate) (w : List Bool), (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih, step_len, List.length_cons]
      omega
  rw [Wg, h]
  simp

private lemma Wg_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    Wg (gs ++ [g]) x = step (Wg gs x) g := by
  simp [Wg, List.foldl_append]

private lemma Wg_val {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (t : ℕ) :
    (Wg (gs ++ [g]) x).getD t false =
      if t = n + gs.length then g.op.eval (g.inputs.map fun i => (Wg gs x).getD i false)
      else (Wg gs x).getD t false := by
  rw [Wg_snoc]
  by_cases ht : t = n + gs.length
  · rw [if_pos ht, step_last _ _ _ (by rw [Wg_len]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < n + gs.length
    · exact step_lt _ _ _ (by rw [Wg_len]; exact hlt)
    · rw [List.getD_eq_default _ _ (by rw [step_len, Wg_len]; omega),
        List.getD_eq_default _ _ (by rw [Wg_len]; omega)]

private lemma all_true (l : List ℕ) (f : ℕ → Bool) :
    (l.map f).all id = true ↔ ∀ i ∈ l, f i = true := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

private lemma any_true (l : List ℕ) (f : ℕ → Bool) :
    (l.map f).any id = true ↔ ∃ i ∈ l, f i = true := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

private lemma ofFn_getD_true {n : ℕ} (x : Fin n → Bool) (t : ℕ)
    (h : (List.ofFn x).getD t false = true) : ∃ ht : t < n, x ⟨t, ht⟩ = true := by
  by_cases ht : t < n
  · refine ⟨ht, ?_⟩
    rw [List.getD_eq_getElem _ _ (by simpa using ht)] at h
    simpa using h
  · rw [List.getD_eq_default _ _ (by simpa using ht)] at h
    exact Bool.noConfusion h

private lemma ofFn_getD_val {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

private def Mono {n : ℕ} (gs : List Gate) : Prop :=
  ∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) →
    ∀ t, (Wg gs x).getD t false = true → (Wg gs y).getD t false = true

private lemma mono_nil {n : ℕ} : Mono (n := n) [] := by
  intro x y hxy t ht
  obtain ⟨hlt, hx⟩ := ofFn_getD_true x t ht
  exact (ofFn_getD_val y ⟨t, hlt⟩).trans (hxy _ hx)

private lemma mono_step {n : ℕ} (gs : List Gate) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (h : Mono (n := n) gs) :
    Mono (n := n) (gs ++ [g]) := by
  intro x y hxy t ht
  rw [Wg_val] at ht ⊢
  by_cases htt : t = n + gs.length
  · rw [if_pos htt] at ht ⊢
    rcases hop with hand | hor
    · rw [hand] at ht ⊢
      exact (all_true _ _).mpr (fun i hi => h x y hxy i ((all_true _ _).mp ht i hi))
    · rw [hor] at ht ⊢
      obtain ⟨i, hi, hti⟩ := (any_true _ _).mp ht
      exact (any_true _ _).mpr ⟨i, hi, h x y hxy i hti⟩
  · rw [if_neg htt] at ht ⊢
    exact h x y hxy t ht

private lemma mono_all {n : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) : Mono (n := n) gs := by
  induction gs using List.reverseRecOn with
  | nil => exact mono_nil
  | append_singleton gs g ih =>
    exact mono_step gs g (hg g (by simp)) (ih (fun g' hg' => hg g' (by simp [hg'])))

private lemma wires_mono (n : ℕ) (C : Circuit)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) (t : ℕ)
    (h : (C.wires (List.ofFn x)).getD t false = true) :
    (C.wires (List.ofFn y)).getD t false = true :=
  mono_all C.gates hC x y hxy t h


lemma starI (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : Circuit)
    (hC : PEqualNP.TopForm.IsAO2 n C) (hpn : ∀ p2 : Fin N, pw p2 < n)
    (hsound : ∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2 →
      (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) →
      circuitFun n C (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)) = false)
    (p' : Fin N) (l : Fin M) (s mm : ℕ)
    (hpath : RR n C s mm)
    (hout : ∀ z3 : Fin n → Bool, (∃ h3 : pw p' < n, z3 ⟨pw p', h3⟩ = true) →
      (C.wires (List.ofFn z3)).getD mm false = true → circuitFun n C z3 = true)
    (hdirty : ∀ pz6 : Fin N, ¬ I pz6 l → ∃ (P6 : Finset (Fin N)) (Y6 : Finset (Fin M)),
      P6.card ≤ 1 ∧ Y6.card ≤ 2 ∧ (∀ a6 ∈ insert pz6 P6, ∀ m6 ∈ Y6, ¬ I a6 m6) ∧
      (C.wires (List.ofFn (fun k6 : Fin n =>
        decide (k6.val ∈ P6.image pw ∪ Y6.image lw)))).getD s false = true) :
    I p' l := by
  by_contra hI
  obtain ⟨P6, Y6, hP, hY, hno, hw⟩ := hdirty p' hI
  have hcard : (insert p' P6).card ≤ 2 := (Finset.card_insert_le _ _).trans (by omega)
  have hs := hsound (insert p' P6) Y6 hcard hY hno
  have hw2 : (C.wires (List.ofFn (fun k3 : Fin n =>
      decide (k3.val ∈ (insert p' P6).image pw ∪ Y6.image lw)))).getD s false = true := by
    refine wires_mono n C hC.1 _ _ ?_ s hw
    intro i hi
    have hmem : i.val ∈ P6.image pw ∪ Y6.image lw := of_decide_eq_true hi
    refine decide_eq_true ?_
    rcases Finset.mem_union.mp hmem with h | h
    · exact Finset.mem_union_left _
        (Finset.image_subset_image (Finset.subset_insert _ _) h)
    · exact Finset.mem_union_right _ h
  have hw3 : (C.wires (List.ofFn (fun k3 : Fin n =>
      decide (k3.val ∈ (insert p' P6).image pw ∪ Y6.image lw)))).getD mm false = true :=
    path_up n C _ s mm hpath hw2
  have hpz : pw p' ∈ (insert p' P6).image pw ∪ Y6.image lw :=
    Finset.mem_union_left _ (Finset.mem_image_of_mem pw (Finset.mem_insert_self _ _))
  have ht := hout (fun k3 : Fin n =>
      decide (k3.val ∈ (insert p' P6).image pw ∪ Y6.image lw))
      ⟨hpn p', decide_eq_true hpz⟩ hw3
  exact Bool.false_ne_true (hs.symm.trans ht)

lemma readersB (n N M : ℕ) (pw : Fin N → ℕ) (C : Circuit) (A : Finset (Fin N × Fin M))
    (Rd G m : Fin N × Fin M → ℕ) (T : Finset ℕ)
    (hA : ∀ e ∈ A, Rd e ∈ T ∧
      ((((gateAt C (Rd e)).inputs.getD 0 0) = G e ∧ ((gateAt C (Rd e)).inputs.getD 1 0) = m e) ∨
       (((gateAt C (Rd e)).inputs.getD 0 0) = m e ∧ ((gateAt C (Rd e)).inputs.getD 1 0) = G e)))
    (hG : ∀ e ∈ A, {x1 : Fin N | RR n C (pw x1) (G e)} = {e.1}) :
    (A.image (fun e => (e.1, m e))).card ≤ 2 * T.card := by
  classical
  have key : ∀ t ∈ A.image (fun e => (e.1, m e)), ∃ q : ℕ × Bool, q.1 ∈ T ∧
      {x1 : Fin N | RR n C (pw x1) (cond q.2 ((gateAt C q.1).inputs.getD 0 0)
        ((gateAt C q.1).inputs.getD 1 0))} = {t.1} ∧
      cond q.2 ((gateAt C q.1).inputs.getD 1 0) ((gateAt C q.1).inputs.getD 0 0) = t.2 := by
    intro t ht
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hj, hab⟩ := hA e he
    have h1 := hG e he
    rcases hab with ⟨ha, hb⟩ | ⟨hb, ha⟩
    · refine ⟨(Rd e, true), hj, ?_, ?_⟩
      · show {x1 : Fin N | RR n C (pw x1) ((gateAt C (Rd e)).inputs.getD 0 0)} = {e.1}
        rw [ha]
        exact h1
      · exact hb
    · refine ⟨(Rd e, false), hj, ?_, ?_⟩
      · show {x1 : Fin N | RR n C (pw x1) ((gateAt C (Rd e)).inputs.getD 1 0)} = {e.1}
        rw [ha]
        exact h1
      · exact hb
  choose! g hg using key
  have hinj : Set.InjOn g (↑(A.image (fun e => (e.1, m e))) : Set (Fin N × ℕ)) := by
    intro t ht t2 ht2 hee
    obtain ⟨_, h1, h2⟩ := hg t (Finset.mem_coe.mp ht)
    obtain ⟨_, k1, k2⟩ := hg t2 (Finset.mem_coe.mp ht2)
    rw [hee] at h1 h2
    have q1 : ({t.1} : Set (Fin N)) = {t2.1} := h1.symm.trans k1
    exact Prod.ext (Set.singleton_eq_singleton_iff.mp q1) (h2.symm.trans k2)
  have hmaps : ∀ t ∈ A.image (fun e => (e.1, m e)),
      g t ∈ T ×ˢ (Finset.univ : Finset Bool) := by
    intro t ht
    exact Finset.mem_product.mpr ⟨(hg t ht).1, Finset.mem_univ _⟩
  have hcard : (A.image (fun e => (e.1, m e))).card ≤ (T ×ˢ (Finset.univ : Finset Bool)).card :=
    Finset.card_le_card_of_injOn g (fun e he => hmaps e he) hinj
  have h2 : (Finset.univ : Finset Bool).card = 2 := by simp
  rw [Finset.card_product, h2] at hcard
  omega

lemma lab_card (n N M : ℕ) (lw : Fin M → ℕ) (C : Circuit) (B : Finset (Fin N × Fin M))
    (S Sy : Fin N × Fin M → ℕ) (p : Fin N) (w : ℕ)
    (hp : ∀ e ∈ B, e.1 = p) (hw : ∀ e ∈ B, n + S e = w)
    (hSy : ∀ e ∈ B, Sy e = (gateAt C (S e)).inputs.getD 0 0 ∨
      Sy e = (gateAt C (S e)).inputs.getD 1 0)
    (hl : ∀ e ∈ B, {y2 : Fin M | RR n C (lw y2) (Sy e)} = {e.2}) :
    B.card ≤ 2 := by
  classical
  obtain ⟨f, hf⟩ : ∃ f : Fin N × Fin M → Bool, ∀ e, f e = true ↔
      Sy e = (gateAt C (S e)).inputs.getD 0 0 :=
    ⟨fun e => decide (Sy e = (gateAt C (S e)).inputs.getD 0 0), fun e => decide_eq_true_iff⟩
  have hinj : Set.InjOn f (↑B : Set (Fin N × Fin M)) := by
    intro e he e2 he2 hee
    have he' := Finset.mem_coe.mp he
    have he2' := Finset.mem_coe.mp he2
    have hS : S e = S e2 := by
      have h1 := hw e he'
      have h2 := hw e2 he2'
      omega
    have hSyeq : Sy e = Sy e2 := by
      by_cases h0 : Sy e = (gateAt C (S e)).inputs.getD 0 0
      · have h0' : Sy e2 = (gateAt C (S e2)).inputs.getD 0 0 :=
          (hf e2).mp (hee.symm.trans ((hf e).mpr h0))
        rw [h0, h0', hS]
      · have h0' : ¬ Sy e2 = (gateAt C (S e2)).inputs.getD 0 0 := by
          intro hc
          exact h0 ((hf e).mp (hee.trans ((hf e2).mpr hc)))
        rcases hSy e he' with h1 | h1
        · exact absurd h1 h0
        · rcases hSy e2 he2' with h2 | h2
          · exact absurd h2 h0'
          · rw [h1, h2, hS]
    have q2 : ({e.2} : Set (Fin M)) = {e2.2} := by
      have a1 := hl e he'
      have a2 := hl e2 he2'
      rw [hSyeq] at a1
      exact a1.symm.trans a2
    exact Prod.ext ((hp e he').trans (hp e2 he2').symm) (Set.singleton_eq_singleton_iff.mp q2)
  have hmaps : ∀ e ∈ B, f e ∈ (Finset.univ : Finset Bool) := fun e _ => Finset.mem_univ _
  have hcard : B.card ≤ (Finset.univ : Finset Bool).card :=
    Finset.card_le_card_of_injOn f (fun e he => hmaps e he) hinj
  have h2 : (Finset.univ : Finset Bool).card = 2 := by simp
  omega

lemma big_fin (n : ℕ) (C : Circuit) {α : Type} (S : Finset α) (roots labelled : Finset ℕ)
    (lab : ℕ → Finset α) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hlabd : ∀ m ∈ labelled, (m < n ∨ ∃ j, m = n + j ∧ j < C.gates.length ∧
      (gateAt C j).op = GateOp.and) ∧ (lab m).card ≤ 2)
    (hS : ∀ a ∈ S, ∃ r ∈ roots, ∃ m1 ∈ labelled, RR n C m1 r ∧ a ∈ lab m1) :
    S.card ≤ 2 * (roots.card + (big n C labelled lab roots).card) :=
  count n C labelled lab hAO.2.1 hAO.2.2
    (fun m hm => (hlabd m hm).1) (fun m hm => (hlabd m hm).2)
    (roots.sup id + 1) roots
    (fun w hw => Nat.lt_succ_of_le (Finset.le_sup (f := id) hw)) S
    (fun a ha => by
      obtain ⟨r, hr, m1, hm1, hR1, ha1⟩ := hS a ha
      exact ⟨r, hr, (mem_LL n C labelled lab r a).2 ⟨m1, hm1, hR1, ha1⟩⟩)

def Ap {N M : ℕ} (A : Finset (Fin N × Fin M)) (p : Fin N) : Finset (Fin N × Fin M) :=
  A.filter (fun e => e.1 = p)

lemma mem_Ap {N M : ℕ} (A : Finset (Fin N × Fin M)) (p : Fin N) (e : Fin N × Fin M) :
    e ∈ Ap A p ↔ e ∈ A ∧ e.1 = p := by
  unfold Ap
  exact Finset.mem_filter

def labp {N M : ℕ} (n : ℕ) (S : Fin N × Fin M → ℕ) (A : Finset (Fin N × Fin M)) (p : Fin N)
    (w : ℕ) : Finset (Fin N × Fin M) :=
  (Ap A p).filter (fun e => n + S e = w)

lemma mem_labp {N M : ℕ} (n : ℕ) (S : Fin N × Fin M → ℕ) (A : Finset (Fin N × Fin M))
    (p : Fin N) (w : ℕ) (e : Fin N × Fin M) :
    e ∈ labp n S A p w ↔ (e ∈ A ∧ e.1 = p) ∧ n + S e = w := by
  unfold labp
  rw [Finset.mem_filter, mem_Ap]

noncomputable def Bp {N M : ℕ} (n : ℕ) (C : Circuit) (m S : Fin N × Fin M → ℕ)
    (A : Finset (Fin N × Fin M)) (p : Fin N) : Finset ℕ :=
  big n C ((Ap A p).image (fun e => n + S e)) (labp n S A p) ((Ap A p).image m)

lemma mem_Bp {N M : ℕ} (n : ℕ) (C : Circuit) (m S : Fin N × Fin M → ℕ)
    (A : Finset (Fin N × Fin M)) (p : Fin N) (j : ℕ) (hj : j ∈ Bp n C m S A p) :
    j < C.gates.length ∧ (gateAt C j).op = GateOp.or ∧
      (∃ e0 ∈ A, e0.1 = p ∧ RR n C (n + j) (m e0)) ∧
      ∃ x ∈ A, ∃ x' ∈ A, x ≠ x' ∧ x.1 = p ∧ x'.1 = p ∧
        RR n C (n + S x) (n + j) ∧ RR n C (n + S x') (n + j) := by
  classical
  unfold Bp at hj
  obtain ⟨h1, h2, ⟨w, hw, hr⟩, h3⟩ := (mem_big n C _ _ _ j).1 hj
  obtain ⟨e0, he0, hw0⟩ := Finset.mem_image.mp hw
  obtain ⟨he0A, he0p⟩ := (mem_Ap A p e0).mp he0
  rw [← hw0] at hr
  obtain ⟨x, hx, x', hx', hne⟩ := Finset.one_lt_card.mp
    (lt_of_lt_of_le (by norm_num : (1 : ℕ) < 3) h3)
  obtain ⟨m3, _, hr3, hx3⟩ := (mem_LL n C _ _ (n + j) x).1 hx
  obtain ⟨m4, _, hr4, hx4⟩ := (mem_LL n C _ _ (n + j) x').1 hx'
  obtain ⟨⟨hxA, hxp⟩, hxm⟩ := (mem_labp n S A p m3 x).mp hx3
  obtain ⟨⟨hxA', hxp'⟩, hxm'⟩ := (mem_labp n S A p m4 x').mp hx4
  rw [← hxm] at hr3
  rw [← hxm'] at hr4
  exact ⟨h1, h2, ⟨e0, he0A, he0p, hr⟩, x, hxA, x', hxA', hne, hxp, hxp', hr3, hr4⟩

lemma countingB (n N M : ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : Circuit)
    (A : Finset (Fin N × Fin M)) (m S Sy : Fin N × Fin M → ℕ) (TA TO : Finset ℕ)
    (hC : PEqualNP.TopForm.IsAO2 n C)
    (hK : ∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 →
      ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5))
    (hTO : ∀ j, j < C.gates.length → (gateAt C j).op = GateOp.or → j ∈ TO)
    (hI : ∀ e ∈ A, I e.1 e.2)
    (hT : (A.image (fun e => (e.1, m e))).card ≤ 2 * TA.card)
    (hSand : ∀ e ∈ A, S e < C.gates.length ∧ (gateAt C (S e)).op = GateOp.and)
    (hSy : ∀ e ∈ A, Sy e = (gateAt C (S e)).inputs.getD 0 0 ∨
      Sy e = (gateAt C (S e)).inputs.getD 1 0)
    (hl : ∀ e ∈ A, {y2 : Fin M | RR n C (lw y2) (Sy e)} = {e.2})
    (hpath : ∀ e ∈ A, RR n C (n + S e) (m e))
    (hstar : ∀ e ∈ A, ∀ e' ∈ A, RR n C (n + S e) (m e') → I e'.1 e.2) :
    A.card ≤ 2 * (2 * TA.card + TO.card) := by
  classical
  have hper : ∀ p : Fin N, (Ap A p).card ≤
      2 * (((Ap A p).image m).card + (Bp n C m S A p).card) := by
    intro p
    unfold Bp
    refine big_fin n C _ _ _ _ hC ?_ ?_
    · intro w hw
      obtain ⟨e, he, hwe⟩ := Finset.mem_image.mp hw
      have heA : e ∈ A := ((mem_Ap A p e).mp he).1
      refine ⟨Or.inr ⟨S e, hwe.symm, (hSand e heA).1, (hSand e heA).2⟩, ?_⟩
      refine lab_card n N M lw C (labp n S A p w) S Sy p w ?_ ?_ ?_ ?_
      · intro e2 he2
        exact ((mem_labp n S A p w e2).mp he2).1.2
      · intro e2 he2
        exact ((mem_labp n S A p w e2).mp he2).2
      · intro e2 he2
        exact hSy e2 ((mem_labp n S A p w e2).mp he2).1.1
      · intro e2 he2
        exact hl e2 ((mem_labp n S A p w e2).mp he2).1.1
    · intro a ha
      have haA : a ∈ A := ((mem_Ap A p a).mp ha).1
      exact ⟨m a, Finset.mem_image_of_mem m ha, n + S a,
        Finset.mem_image_of_mem (fun e => n + S e) ha, hpath a haA,
        (mem_labp n S A p (n + S a) a).mpr ⟨(mem_Ap A p a).mp ha, rfl⟩⟩
  have hsumA : A.card = ∑ p : Fin N, (Ap A p).card :=
    Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (s := A) (t := Finset.univ)
      (fun x _ => Finset.mem_coe.mpr (Finset.mem_univ _))
  have hroots : ∑ p : Fin N, ((Ap A p).image m).card ≤
      (A.image (fun e => (e.1, m e))).card := by
    have hT2 : (A.image (fun e => (e.1, m e))).card = ∑ p : Fin N,
        ((A.image (fun e => (e.1, m e))).filter (fun t => t.1 = p)).card :=
      Finset.card_eq_sum_card_fiberwise (f := Prod.fst)
        (s := A.image (fun e => (e.1, m e))) (t := Finset.univ)
        (fun x _ => Finset.mem_coe.mpr (Finset.mem_univ _))
    rw [hT2]
    refine Finset.sum_le_sum (fun p _ => ?_)
    have hsub : (Ap A p).image m ⊆
        ((A.image (fun e => (e.1, m e))).filter (fun t => t.1 = p)).image Prod.snd := by
      intro r hr
      obtain ⟨e, he, hre⟩ := Finset.mem_image.mp hr
      obtain ⟨heA, hep⟩ := (mem_Ap A p e).mp he
      exact Finset.mem_image.mpr ⟨(e.1, m e),
        Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem (fun e : Fin N × Fin M => (e.1, m e)) heA, hep⟩, hre⟩
    exact le_trans (Finset.card_le_card hsub) Finset.card_image_le
  have hB : ∑ p : Fin N, (Bp n C m S A p).card ≤ TO.card := by
    have hdisj : (↑(Finset.univ : Finset (Fin N)) : Set (Fin N)).PairwiseDisjoint
        (Bp n C m S A) := by
      intro p _ p' _ hpp'
      show Disjoint (Bp n C m S A p) (Bp n C m S A p')
      rw [Finset.disjoint_left]
      intro j hj hj'
      obtain ⟨_, _, _, x, hxA, x', hxA', hne, hxp, hxp', hr, hr'⟩ := mem_Bp n C m S A p j hj
      obtain ⟨_, _, ⟨e0, he0A, he0p, hr0⟩, _⟩ := mem_Bp n C m S A p' j hj'
      have i1 : I p x.2 := by
        have := hI x hxA
        rw [hxp] at this
        exact this
      have i2 : I p' x.2 := by
        have := hstar x hxA e0 he0A (Relation.ReflTransGen.trans hr hr0)
        rw [he0p] at this
        exact this
      have i3 : I p x'.2 := by
        have := hI x' hxA'
        rw [hxp'] at this
        exact this
      have i4 : I p' x'.2 := by
        have := hstar x' hxA' e0 he0A (Relation.ReflTransGen.trans hr' hr0)
        rw [he0p] at this
        exact this
      have hl2 : x.2 ≠ x'.2 := fun h => hne (Prod.ext (hxp.trans hxp'.symm) h)
      exact hK p p' x.2 x'.2 hpp' hl2 ⟨i1, i2, i3, i4⟩
    rw [← Finset.card_biUnion hdisj]
    refine Finset.card_le_card ?_
    intro j hj
    obtain ⟨p, _, hjp⟩ := Finset.mem_biUnion.mp hj
    obtain ⟨h1, h2, _⟩ := mem_Bp n C m S A p j hjp
    exact hTO j h1 h2
  have hsum2 : ∑ p : Fin N, 2 * (((Ap A p).image m).card + (Bp n C m S A p).card) =
      2 * (∑ p : Fin N, ((Ap A p).image m).card + ∑ p : Fin N, (Bp n C m S A p).card) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
  have hle : A.card ≤ ∑ p : Fin N, 2 * (((Ap A p).image m).card + (Bp n C m S A p).card) := by
    rw [hsumA]
    exact Finset.sum_le_sum (fun p _ => hper p)
  have hroots2 := hroots.trans hT
  rw [hsum2] at hle
  omega

theorem main_aux : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit) (A : Finset (Fin N × Fin M)) (Rd G m S Sy : Fin N × Fin M → ℕ), PEqualNP.TopForm.IsAO2 n C → Function.Injective pw → Function.Injective lw → (∀ (p1 : Fin N) (l1 : Fin M), pw p1 ≠ lw l1) → (∀ p2 : Fin N, pw p2 < n) → (∀ l2 : Fin M, lw l2 < n) → (∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 → ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5)) → (∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2 → (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) → PEqualNP.MetaComplexity.circuitFun n C (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)) = false) → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → (∀ e ∈ A, I e.1 e.2 ∧ ((Rd e) < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (Rd e)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((((PEqualNP.MetaComplexity.NestedCover.gateAt C (Rd e)).inputs.getD 0 0) = (G e) ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (Rd e)).inputs.getD 1 0) = (m e)) ∨ (((PEqualNP.MetaComplexity.NestedCover.gateAt C (Rd e)).inputs.getD 0 0) = (m e) ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (Rd e)).inputs.getD 1 0) = (G e)))) ∧ {x1 : Fin N | R (pw x1) (G e)} = {e.1} ∧ (∃ o : ℕ, ((S e) < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (S e)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((((PEqualNP.MetaComplexity.NestedCover.gateAt C (S e)).inputs.getD 0 0) = (Sy e) ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (S e)).inputs.getD 1 0) = o) ∨ (((PEqualNP.MetaComplexity.NestedCover.gateAt C (S e)).inputs.getD 0 0) = o ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (S e)).inputs.getD 1 0) = (Sy e))))) ∧ {y2 : Fin M | R (lw y2) (Sy e)} = {e.2} ∧ R (n + S e) (m e) ∧ (∀ z3 : Fin n → Bool, (∃ h3 : pw e.1 < n, z3 ⟨pw e.1, h3⟩ = true) → (C.wires (List.ofFn z3)).getD ((m e)) false = true → PEqualNP.MetaComplexity.circuitFun n C z3 = true) ∧ (∀ pz6 : Fin N, ¬ I pz6 e.2 → ∃ (P6 : Finset (Fin N)) (Y6 : Finset (Fin M)), P6.card ≤ 1 ∧ Y6.card ≤ 2 ∧ (∀ a6 ∈ insert pz6 P6, ∀ m6 ∈ Y6, ¬ I a6 m6) ∧ (C.wires (List.ofFn (fun k6 : Fin n => decide (k6.val ∈ P6.image pw ∪ Y6.image lw)))).getD ((n + S e)) false = true)) → A.card ≤ 2 * (2 * {ja : ℕ | ja < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C ja).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard + {jo : ℕ | jo < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C jo).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard) := by
  classical
  intro n N M pw lw I C A Rd G m S Sy hC hpw hlw hne hpn hln hK hsound R hR hA
  subst hR
  have hTA : {ja : ℕ | ja < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C ja).op = PEqualNP.CircuitLowerBounds.GateOp.and} = (↑((Finset.range C.gates.length).filter (fun ja => (PEqualNP.MetaComplexity.NestedCover.gateAt C ja).op = PEqualNP.CircuitLowerBounds.GateOp.and)) : Set ℕ) := by
    ext ja
    simp
  have hTO : {jo : ℕ | jo < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C jo).op = PEqualNP.CircuitLowerBounds.GateOp.or} = (↑((Finset.range C.gates.length).filter (fun jo => (PEqualNP.MetaComplexity.NestedCover.gateAt C jo).op = PEqualNP.CircuitLowerBounds.GateOp.or)) : Set ℕ) := by
    ext jo
    simp
  rw [hTA, hTO, Set.ncard_coe_finset, Set.ncard_coe_finset]
  refine countingB n N M lw I C A m S Sy _ _ hC hK ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro j hj hop
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hop⟩
  · intro e he
    exact (hA e he).1
  · refine readersB n N M pw C A Rd G m _ ?_ ?_
    · intro e he
      obtain ⟨_, ⟨hj, hop, hab⟩, _⟩ := hA e he
      exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hop⟩, hab⟩
    · intro e he
      exact (hA e he).2.2.1
  · intro e he
    obtain ⟨_, _, _, ⟨o, hj, hop, _⟩, _⟩ := hA e he
    exact ⟨hj, hop⟩
  · intro e he
    obtain ⟨_, _, _, ⟨o, hj, hop, hab⟩, _⟩ := hA e he
    rcases hab with ⟨h0, _⟩ | ⟨_, h1⟩
    · exact Or.inl h0.symm
    · exact Or.inr h1.symm
  · intro e he
    exact (hA e he).2.2.2.2.1
  · intro e he
    exact (hA e he).2.2.2.2.2.1
  · intro e he e' he' hp
    exact starI n N M pw lw I C hC hpn hsound e'.1 e.2 (n + S e) (m e') hp
      (hA e' he').2.2.2.2.2.2.1 (hA e he).2.2.2.2.2.2.2

end PEqualNP.Outside.L_meta_2415

theorem PEqualNP.Outside.L_meta_2415 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit) (A : Finset (Fin N × Fin M)) (Rd G m S Sy : Fin N × Fin M → ℕ), PEqualNP.TopForm.IsAO2 n C → Function.Injective pw → Function.Injective lw → (∀ (p1 : Fin N) (l1 : Fin M), pw p1 ≠ lw l1) → (∀ p2 : Fin N, pw p2 < n) → (∀ l2 : Fin M, lw l2 < n) → (∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 → ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5)) → (∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2 → (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) → PEqualNP.MetaComplexity.circuitFun n C (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)) = false) → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → (∀ e ∈ A, I e.1 e.2 ∧ ((Rd e) < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (Rd e)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((((PEqualNP.MetaComplexity.NestedCover.gateAt C (Rd e)).inputs.getD 0 0) = (G e) ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (Rd e)).inputs.getD 1 0) = (m e)) ∨ (((PEqualNP.MetaComplexity.NestedCover.gateAt C (Rd e)).inputs.getD 0 0) = (m e) ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (Rd e)).inputs.getD 1 0) = (G e)))) ∧ {x1 : Fin N | R (pw x1) (G e)} = {e.1} ∧ (∃ o : ℕ, ((S e) < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (S e)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((((PEqualNP.MetaComplexity.NestedCover.gateAt C (S e)).inputs.getD 0 0) = (Sy e) ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (S e)).inputs.getD 1 0) = o) ∨ (((PEqualNP.MetaComplexity.NestedCover.gateAt C (S e)).inputs.getD 0 0) = o ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (S e)).inputs.getD 1 0) = (Sy e))))) ∧ {y2 : Fin M | R (lw y2) (Sy e)} = {e.2} ∧ R (n + S e) (m e) ∧ (∀ z3 : Fin n → Bool, (∃ h3 : pw e.1 < n, z3 ⟨pw e.1, h3⟩ = true) → (C.wires (List.ofFn z3)).getD ((m e)) false = true → PEqualNP.MetaComplexity.circuitFun n C z3 = true) ∧ (∀ pz6 : Fin N, ¬ I pz6 e.2 → ∃ (P6 : Finset (Fin N)) (Y6 : Finset (Fin M)), P6.card ≤ 1 ∧ Y6.card ≤ 2 ∧ (∀ a6 ∈ insert pz6 P6, ∀ m6 ∈ Y6, ¬ I a6 m6) ∧ (C.wires (List.ofFn (fun k6 : Fin n => decide (k6.val ∈ P6.image pw ∪ Y6.image lw)))).getD ((n + S e)) false = true)) → A.card ≤ 2 * (2 * {ja : ℕ | ja < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C ja).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard + {jo : ℕ | jo < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C jo).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard) :=
  PEqualNP.Outside.L_meta_2415.main_aux
