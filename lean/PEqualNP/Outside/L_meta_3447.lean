import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3447

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2

lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma mono (n : ℕ) (C : Circuit) (hAO : PEqualNP.EdgeOwnership.AndOrOnly C)
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, x i = true → y i = true) :
    ∀ w : ℕ, val C (List.ofFn x) w = true → val C (List.ofFn y) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · have e1 : val C (List.ofFn x) w = x ⟨w, hw⟩ := val_ofFn C x ⟨w, hw⟩
      have e2 : val C (List.ofFn y) w = y ⟨w, hw⟩ := val_ofFn C y ⟨w, hw⟩
      rw [e2]
      rw [e1] at hv
      exact hxy _ hv
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge (n := n) (by simp) hlen] at hv
        cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        rw [val_gate (n := n) (by simp) hk] at hv ⊢
        have h : ∀ i ∈ (gateAt C k).inputs,
            ((if i < n + k then val C (List.ofFn x) i else false) = true →
              (if i < n + k then val C (List.ofFn y) i else false) = true) := by
          intro i _
          by_cases hi : i < n + k
          · rw [if_pos hi, if_pos hi]
            exact ih i hi
          · rw [if_neg hi, if_neg hi]
            exact id
        exact opMono_imp (gateAt C k).op (hAO _ (gateAt_mem hk)) (gateAt C k).inputs
          (fun i => if i < n + k then val C (List.ofFn x) i else false)
          (fun i => if i < n + k then val C (List.ofFn y) i else false) h hv



lemma andOr_of {C : Circuit} (hM : PEqualNP.MetaComplexity.Monotone2 C) :
    PEqualNP.EdgeOwnership.AndOrOnly C := by
  intro g hg
  have h := (hM g hg).1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  exact h

lemma stepR {n : ℕ} {C : Circuit} (hM : PEqualNP.MetaComplexity.Monotone2 C)
    (hRB : ReadsBack n C) (g : Fin n → Bool) (j : ℕ)
    (hg : val C (List.ofFn g) (n + j) = false) :
    ∃ R : Finset ℕ, R.card ≤ 2 ∧ (∀ r ∈ R, r < n + j ∧ val C (List.ofFn g) r = false) ∧
      ∀ y : Fin n → Bool, val C (List.ofFn y) (n + j) = true →
        ∃ r ∈ R, val C (List.ofFn y) r = true := by
  by_cases hj : j < C.gates.length
  · have hmem := gateAt_mem hj
    have hlen : (gateAt C j).inputs.length ≤ 2 := (hM _ hmem).2
    have hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j := hRB j hj
    rcases andOr_of hM _ hmem with hop | hop
    · have hex : ∃ i ∈ (gateAt C j).inputs, val C (List.ofFn g) i = false := by
        by_contra hne
        push_neg at hne
        have h1 : val C (List.ofFn g) (n + j) = true := by
          rw [val_and (n := n) (x := List.ofFn g) (by simp) hj hop]
          intro i hi
          refine ⟨hrb i hi, ?_⟩
          have := hne i hi
          simpa using this
        rw [hg] at h1
        exact Bool.false_ne_true h1
      obtain ⟨i, hi, hgi⟩ := hex
      refine ⟨{i}, by simp, ?_, ?_⟩
      · intro r hr
        rw [Finset.mem_singleton] at hr
        subst hr
        exact ⟨hrb r hi, hgi⟩
      · intro y hy
        exact ⟨i, Finset.mem_singleton_self i,
          ((val_and (n := n) (x := List.ofFn y) (by simp) hj hop).mp hy i hi).2⟩
    · refine ⟨(gateAt C j).inputs.toFinset, le_trans (List.toFinset_card_le _) hlen, ?_, ?_⟩
      · intro r hr
        have hr2 := List.mem_toFinset.mp hr
        refine ⟨hrb r hr2, ?_⟩
        cases hv : val C (List.ofFn g) r
        · rfl
        · have h1 : val C (List.ofFn g) (n + j) = true :=
            (val_or (n := n) (x := List.ofFn g) (by simp) hj hop).mpr ⟨r, hr2, hrb r hr2, hv⟩
          rw [hg] at h1
          exact absurd h1 Bool.false_ne_true
      · intro y hy
        obtain ⟨i, hi, _, h⟩ := (val_or (n := n) (x := List.ofFn y) (by simp) hj hop).mp hy
        exact ⟨i, List.mem_toFinset.mpr hi, h⟩
  · refine ⟨∅, by simp, by simp, ?_⟩
    intro y hy
    rw [val_ge (n := n) (x := List.ofFn y) (by simp) (by omega)] at hy
    exact absurd hy Bool.false_ne_true

-- the counting lemma: sets of a family of good wires

lemma unionL {ι : Type} [DecidableEq ι] (S : ℕ → Finset ι) (good : ℕ → Prop)
    [DecidablePred good] (n : ℕ)
    (hbase : ∀ w, w < n → (S w).card ≤ 1)
    (hstep : ∀ j, good (n + j) → ∃ R : Finset ℕ, R.card ≤ 2 ∧
      (∀ r ∈ R, r < n + j ∧ good r) ∧ S (n + j) ⊆ R.biUnion S) :
    ∀ m (F : Finset ℕ), (∀ w ∈ F, w < n + m ∧ good w) →
      (F.biUnion S).card ≤ F.card +
        ((Finset.range m).filter (fun j => 2 ≤ (S (n + j)).card ∧ good (n + j))).card := by
  intro m
  induction m with
  | zero =>
    intro F hF
    have h1 : (F.biUnion S).card ≤ ∑ w ∈ F, (S w).card := Finset.card_biUnion_le
    have h2 : ∑ w ∈ F, (S w).card ≤ ∑ _w ∈ F, 1 :=
      Finset.sum_le_sum (fun w hw => hbase w (by have := (hF w hw).1; omega))
    have h3 : ∑ _w ∈ F, 1 = F.card := by simp
    omega
  | succ m ih =>
    intro F hF
    have hK : ((Finset.range m).filter (fun j => 2 ≤ (S (n + j)).card ∧ good (n + j))) ⊆
        ((Finset.range (m + 1)).filter (fun j => 2 ≤ (S (n + j)).card ∧ good (n + j))) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_range] at hj ⊢
      exact ⟨by omega, hj.2⟩
    by_cases hin : n + m ∈ F
    · have hgood : good (n + m) := (hF _ hin).2
      have hF0 : ∀ w ∈ F.erase (n + m), w < n + m ∧ good w := by
        intro w hw
        obtain ⟨hne, hw2⟩ := Finset.mem_erase.mp hw
        have := hF w hw2
        exact ⟨by omega, this.2⟩
      have hsub0 : F.biUnion S ⊆ (F.erase (n + m)).biUnion S ∪ S (n + m) := by
        intro x hx
        obtain ⟨w, hw, hxw⟩ := Finset.mem_biUnion.mp hx
        by_cases hwe : w = n + m
        · subst hwe
          exact Finset.mem_union_right _ hxw
        · exact Finset.mem_union_left _
            (Finset.mem_biUnion.mpr ⟨w, Finset.mem_erase.mpr ⟨hwe, hw⟩, hxw⟩)
      have hcardE : (F.erase (n + m)).card + 1 = F.card := Finset.card_erase_add_one hin
      by_cases hbig : 2 ≤ (S (n + m)).card
      · obtain ⟨R, hR, hRg, hRS⟩ := hstep m hgood
        have hF1 : ∀ w ∈ F.erase (n + m) ∪ R, w < n + m ∧ good w := by
          intro w hw
          rcases Finset.mem_union.mp hw with h | h
          · exact hF0 w h
          · exact hRg w h
        have ih1 := ih _ hF1
        have hsub : F.biUnion S ⊆ (F.erase (n + m) ∪ R).biUnion S := by
          intro x hx
          rcases Finset.mem_union.mp (hsub0 hx) with h | h
          · obtain ⟨w, hw, hxw⟩ := Finset.mem_biUnion.mp h
            exact Finset.mem_biUnion.mpr ⟨w, Finset.mem_union_left _ hw, hxw⟩
          · obtain ⟨r, hr, hxr⟩ := Finset.mem_biUnion.mp (hRS h)
            exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_union_right _ hr, hxr⟩
        have hc1 := Finset.card_le_card hsub
        have hc2 := Finset.card_union_le (F.erase (n + m)) R
        have hmK : m ∉ (Finset.range m).filter (fun j => 2 ≤ (S (n + j)).card ∧ good (n + j)) := by
          intro h
          rw [Finset.mem_filter, Finset.mem_range] at h
          omega
        have hK2 : insert m ((Finset.range m).filter (fun j => 2 ≤ (S (n + j)).card ∧ good (n + j)))
            ⊆ (Finset.range (m + 1)).filter (fun j => 2 ≤ (S (n + j)).card ∧ good (n + j)) := by
          intro j hj
          rcases Finset.mem_insert.mp hj with h | h
          · subst h
            rw [Finset.mem_filter, Finset.mem_range]
            exact ⟨by omega, hbig, hgood⟩
          · exact hK h
        have hc3 := Finset.card_le_card hK2
        rw [Finset.card_insert_of_notMem hmK] at hc3
        omega
      · have ih1 := ih _ hF0
        have hc1 := Finset.card_le_card hsub0
        have hc2 := Finset.card_union_le ((F.erase (n + m)).biUnion S) (S (n + m))
        have hc3 := Finset.card_le_card hK
        omega
    · have hF1 : ∀ w ∈ F, w < n + m ∧ good w := by
        intro w hw
        have := hF w hw
        have hne : w ≠ n + m := fun h => hin (h ▸ hw)
        exact ⟨by omega, this.2⟩
      have h1 := ih F hF1
      have h2 := Finset.card_le_card hK
      omega

-- single inputs and the bad inputs

def e1 {N : ℕ} (p : Fin N) : Fin (N + N) → Bool := fun k => decide (k = Fin.castAdd N p)

def e2 {N : ℕ} (l : Fin N) : Fin (N + N) → Bool := fun k => decide (k = Fin.natAdd N l)

def gL {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (p : Fin N) : Fin (N + N) → Bool :=
  fun k => decide (∃ l : Fin N, k = Fin.natAdd N l ∧ ¬ I p l)

def gP {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (l : Fin N) : Fin (N + N) → Bool :=
  fun k => decide (∃ p : Fin N, k = Fin.castAdd N p ∧ ¬ I p l)

lemma cn_ne {N : ℕ} (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have h1 := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at h1
  have := p.isLt
  omega

lemma c_inj {N : ℕ} {p p' : Fin N} : Fin.castAdd N p = Fin.castAdd N p' ↔ p = p' := by
  constructor
  · intro h
    have h1 := congrArg Fin.val h
    simp only [Fin.val_castAdd] at h1
    exact Fin.ext h1
  · intro h
    rw [h]

lemma n_inj {N : ℕ} {l l' : Fin N} : Fin.natAdd N l = Fin.natAdd N l' ↔ l = l' := by
  constructor
  · intro h
    have h1 := congrArg Fin.val h
    simp only [Fin.val_natAdd] at h1
    exact Fin.ext (by omega)
  · intro h
    rw [h]

lemma e1_c {N : ℕ} (p p0 : Fin N) : e1 p (Fin.castAdd N p0) = true ↔ p0 = p := by
  show decide (Fin.castAdd N p0 = Fin.castAdd N p) = true ↔ p0 = p
  rw [decide_eq_true_iff]
  exact c_inj

lemma e1_n {N : ℕ} (p l0 : Fin N) : e1 p (Fin.natAdd N l0) = false := by
  show decide (Fin.natAdd N l0 = Fin.castAdd N p) = false
  exact decide_eq_false (fun h => cn_ne p l0 h.symm)

lemma e2_n {N : ℕ} (l l0 : Fin N) : e2 l (Fin.natAdd N l0) = true ↔ l0 = l := by
  show decide (Fin.natAdd N l0 = Fin.natAdd N l) = true ↔ l0 = l
  rw [decide_eq_true_iff]
  exact n_inj

lemma e2_c {N : ℕ} (l p0 : Fin N) : e2 l (Fin.castAdd N p0) = false := by
  show decide (Fin.castAdd N p0 = Fin.natAdd N l) = false
  exact decide_eq_false (cn_ne p0 l)

lemma gL_c {N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] (p p0 : Fin N) :
    gL I p (Fin.castAdd N p0) = false := by
  show decide (∃ l : Fin N, Fin.castAdd N p0 = Fin.natAdd N l ∧ ¬ I p l) = false
  apply decide_eq_false
  rintro ⟨l, h, _⟩
  exact cn_ne p0 l h

lemma gL_n {N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] (p l0 : Fin N) :
    gL I p (Fin.natAdd N l0) = true ↔ ¬ I p l0 := by
  show decide (∃ l : Fin N, Fin.natAdd N l0 = Fin.natAdd N l ∧ ¬ I p l) = true ↔ ¬ I p l0
  rw [decide_eq_true_iff]
  constructor
  · rintro ⟨l, h, h2⟩
    rw [n_inj.mp h]
    exact h2
  · intro h
    exact ⟨l0, rfl, h⟩

lemma gP_n {N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] (l l0 : Fin N) :
    gP I l (Fin.natAdd N l0) = false := by
  show decide (∃ p : Fin N, Fin.natAdd N l0 = Fin.castAdd N p ∧ ¬ I p l) = false
  apply decide_eq_false
  rintro ⟨p, h, _⟩
  exact cn_ne p l0 h.symm

lemma gP_c {N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] (l p0 : Fin N) :
    gP I l (Fin.castAdd N p0) = true ↔ ¬ I p0 l := by
  show decide (∃ p : Fin N, Fin.castAdd N p0 = Fin.castAdd N p ∧ ¬ I p l) = true ↔ ¬ I p0 l
  rw [decide_eq_true_iff]
  constructor
  · rintro ⟨p, h, h2⟩
    rw [c_inj.mp h]
    exact h2
  · intro h
    exact ⟨p0, rfl, h⟩

lemma e1_inj {N : ℕ} : ∀ (i i' : Fin N) (k : Fin (N + N)), e1 i k = true → e1 i' k = true → i = i' := by
  intro i i' k h1 h2
  have h1' : k = Fin.castAdd N i := of_decide_eq_true h1
  have h2' : k = Fin.castAdd N i' := of_decide_eq_true h2
  exact c_inj.mp (h1'.symm.trans h2')

lemma e2_inj {N : ℕ} : ∀ (i i' : Fin N) (k : Fin (N + N)), e2 i k = true → e2 i' k = true → i = i' := by
  intro i i' k h1 h2
  have h1' : k = Fin.natAdd N i := of_decide_eq_true h1
  have h2' : k = Fin.natAdd N i' := of_decide_eq_true h2
  exact n_inj.mp (h1'.symm.trans h2')

-- wire sets

def wset {N : ℕ} (C : Circuit) (X : Fin N → Fin (N + N) → Bool) (w : ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun i => val C (List.ofFn (X i)) w = true)

lemma mem_wset {N : ℕ} {C : Circuit} {X : Fin N → Fin (N + N) → Bool} {w : ℕ} {i : Fin N} :
    i ∈ wset C X w ↔ val C (List.ofFn (X i)) w = true := by
  unfold wset
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

lemma sing_val {N : ℕ} {C : Circuit} {X : Fin N → Fin (N + N) → Bool} {b : ℕ} {q : Fin N}
    (hb : wset C X b = {q}) : val C (List.ofFn (X q)) b = true := by
  have h : q ∈ wset C X b := by
    rw [hb]
    exact Finset.mem_singleton_self q
  exact mem_wset.mp h

lemma two_val {N : ℕ} {C : Circuit} {X : Fin N → Fin (N + N) → Bool} {b : ℕ}
    (hb : 2 ≤ (wset C X b).card) : ∃ q : Fin N, val C (List.ofFn (X q)) b = true := by
  have h0 : 0 < (wset C X b).card := by omega
  obtain ⟨q, hq⟩ := Finset.card_pos.mp h0
  exact ⟨q, mem_wset.mp hq⟩

lemma base_le {N : ℕ} (C : Circuit) (X : Fin N → Fin (N + N) → Bool)
    (hX : ∀ (i i' : Fin N) (k : Fin (N + N)), X i k = true → X i' k = true → i = i') :
    ∀ w, w < N + N → (wset C X w).card ≤ 1 := by
  intro w hw
  apply Finset.card_le_one.mpr
  intro i hi i' hi'
  have e : ∀ t : Fin N, val C (List.ofFn (X t)) w = X t ⟨w, hw⟩ :=
    fun t => val_ofFn C (X t) ⟨w, hw⟩
  rw [mem_wset, e] at hi hi'
  exact hX i i' _ hi hi'

lemma stepS {N : ℕ} {C : Circuit} (hM : PEqualNP.MetaComplexity.Monotone2 C)
    (hRB : ReadsBack (N + N) C) (X : Fin N → Fin (N + N) → Bool) (g : Fin (N + N) → Bool) :
    ∀ j, val C (List.ofFn g) (N + N + j) = false → ∃ R : Finset ℕ, R.card ≤ 2 ∧
      (∀ r ∈ R, r < N + N + j ∧ val C (List.ofFn g) r = false) ∧
      wset C X (N + N + j) ⊆ R.biUnion (wset C X) := by
  intro j hj
  obtain ⟨R, hR, hRg, hy⟩ := stepR hM hRB g j hj
  refine ⟨R, hR, hRg, ?_⟩
  intro i hi
  rw [mem_wset] at hi
  obtain ⟨r, hr, h⟩ := hy (X i) hi
  exact Finset.mem_biUnion.mpr ⟨r, hr, mem_wset.mpr h⟩



-- the pair inputs and the witnessing gates

def pr {N : ℕ} (p l : Fin N) : Fin (N + N) → Bool :=
  fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)

lemma pr_of1 {N : ℕ} (p l : Fin N) : ∀ k : Fin (N + N), e1 p k = true → pr p l k = true := by
  intro k hk
  have hk2 : k = Fin.castAdd N p := of_decide_eq_true hk
  show decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l) = true
  exact decide_eq_true (Or.inl hk2)

lemma pr_of2 {N : ℕ} (p l : Fin N) : ∀ k : Fin (N + N), e2 l k = true → pr p l k = true := by
  intro k hk
  have hk2 : k = Fin.natAdd N l := of_decide_eq_true hk
  show decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l) = true
  exact decide_eq_true (Or.inr hk2)

def Wit (C : Circuit) (j a c : ℕ) : Prop :=
  j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
    ((gateAt C j).inputs = [a, c] ∨ (gateAt C j).inputs = [c, a])

lemma wit_mem {C : Circuit} {j a c : ℕ} (hw : Wit C j a c) :
    j < C.gates.length ∧ a ∈ (gateAt C j).inputs ∧ c ∈ (gateAt C j).inputs := by
  obtain ⟨hj, _, hin⟩ := hw
  rcases hin with h | h <;> rw [h] <;> simp [hj]

lemma two_list {L : List ℕ} {a c : ℕ} (hL : L.length ≤ 2) (ha : a ∈ L) (hc : c ∈ L)
    (hne : a ≠ c) : L = [a, c] ∨ L = [c, a] := by
  rcases L with _ | ⟨x, _ | ⟨y, _ | ⟨z, t⟩⟩⟩
  · simp at ha
  · simp only [List.mem_singleton] at ha hc
    exact absurd (ha.trans hc.symm) hne
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hc
    rcases ha with rfl | rfl <;> rcases hc with rfl | rfl <;> simp_all
  · simp only [List.length_cons] at hL
    omega

lemma other {L : List ℕ} {a c c' : ℕ} (h1 : L = [a, c] ∨ L = [c, a])
    (h2 : L = [a, c'] ∨ L = [c', a]) : c = c' := by
  rcases h1 with rfl | rfl <;> rcases h2 with h | h <;>
    simp only [List.cons.injEq, and_true, true_and, eq_self_iff_true] at h <;> omega

lemma two4 {N : ℕ} {I : Fin N → Fin N → Prop}
    (h4 : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    {p p' l l' : Fin N} (hpp : p ≠ p') (h1 : I p l) (h2 : I p' l) (h3 : I p l') (h5 : I p' l') :
    l = l' := by
  by_contra hll
  exact h4 p p' l l' hpp hll ⟨h1, h3, h2, h5⟩

-- every incident pair has a witnessing AND gate

lemma reach {N : ℕ} {C : Circuit} (hM : PEqualNP.MetaComplexity.Monotone2 C)
    (hRB : ReadsBack (N + N) C)
    (hA1 : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ p : Fin N, val C (List.ofFn (e1 p)) (N + N + j) = false)
    (hA2 : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ l : Fin N, val C (List.ofFn (e2 l)) (N + N + j) = false)
    (p l : Fin N) : ∀ w, val C (List.ofFn (pr p l)) w = true →
      (val C (List.ofFn (e1 p)) w = true ∨ val C (List.ofFn (e2 l)) w = true) ∨
      ∃ j a c, Wit C j a c ∧ val C (List.ofFn (e1 p)) a = true ∧
        val C (List.ofFn (e2 l)) c = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < N + N
    · have e0 : val C (List.ofFn (pr p l)) w = pr p l ⟨w, hw⟩ := val_ofFn C (pr p l) ⟨w, hw⟩
      rw [e0] at hv
      have hor : (⟨w, hw⟩ : Fin (N + N)) = Fin.castAdd N p ∨
          (⟨w, hw⟩ : Fin (N + N)) = Fin.natAdd N l := of_decide_eq_true hv
      left
      rcases hor with h | h
      · left
        have e3 : val C (List.ofFn (e1 p)) w = e1 p ⟨w, hw⟩ := val_ofFn C (e1 p) ⟨w, hw⟩
        rw [e3]
        exact decide_eq_true h
      · right
        have e3 : val C (List.ofFn (e2 l)) w = e2 l ⟨w, hw⟩ := val_ofFn C (e2 l) ⟨w, hw⟩
        rw [e3]
        exact decide_eq_true h
    · by_cases hlen : N + N + C.gates.length ≤ w
      · rw [val_ge (n := N + N) (by simp) hlen] at hv
        exact absurd hv Bool.false_ne_true
      · obtain ⟨k, rfl⟩ : ∃ k, w = N + N + k := ⟨w - (N + N), by omega⟩
        have hk : k < C.gates.length := by omega
        have hmem := gateAt_mem hk
        have hlen2 : (gateAt C k).inputs.length ≤ 2 := (hM _ hmem).2
        have hrb : ∀ i ∈ (gateAt C k).inputs, i < N + N + k := hRB k hk
        rcases andOr_of hM _ hmem with hop | hop
        · have hall := (val_and (n := N + N) (x := List.ofFn (pr p l)) (by simp) hk hop).mp hv
          by_cases hex : ∃ j a c, Wit C j a c ∧ val C (List.ofFn (e1 p)) a = true ∧
              val C (List.ofFn (e2 l)) c = true
          · right
            exact hex
          have hIH : ∀ i ∈ (gateAt C k).inputs,
              val C (List.ofFn (e1 p)) i = true ∨ val C (List.ofFn (e2 l)) i = true := by
            intro i hi
            rcases ih i (hall i hi).1 (hall i hi).2 with h | h
            · exact h
            · exact absurd h hex
          have hi1 : ∃ i ∈ (gateAt C k).inputs, val C (List.ofFn (e1 p)) i = false := by
            by_contra hne
            have h1 : val C (List.ofFn (e1 p)) (N + N + k) = true := by
              rw [val_and (n := N + N) (x := List.ofFn (e1 p)) (by simp) hk hop]
              intro i hi
              refine ⟨hrb i hi, ?_⟩
              cases h : val C (List.ofFn (e1 p)) i
              · exact (hne ⟨i, hi, h⟩).elim
              · rfl
            rw [hA1 k hk hop p] at h1
            exact Bool.false_ne_true h1
          have hi2 : ∃ i ∈ (gateAt C k).inputs, val C (List.ofFn (e2 l)) i = false := by
            by_contra hne
            have h1 : val C (List.ofFn (e2 l)) (N + N + k) = true := by
              rw [val_and (n := N + N) (x := List.ofFn (e2 l)) (by simp) hk hop]
              intro i hi
              refine ⟨hrb i hi, ?_⟩
              cases h : val C (List.ofFn (e2 l)) i
              · exact (hne ⟨i, hi, h⟩).elim
              · rfl
            rw [hA2 k hk hop l] at h1
            exact Bool.false_ne_true h1
          obtain ⟨i1, hi1m, hi1f⟩ := hi1
          obtain ⟨i2, hi2m, hi2f⟩ := hi2
          have h1 : val C (List.ofFn (e2 l)) i1 = true := by
            rcases hIH i1 hi1m with h | h
            · rw [hi1f] at h
              exact absurd h Bool.false_ne_true
            · exact h
          have h2 : val C (List.ofFn (e1 p)) i2 = true := by
            rcases hIH i2 hi2m with h | h
            · exact h
            · rw [hi2f] at h
              exact absurd h Bool.false_ne_true
          have hne : i2 ≠ i1 := by
            intro h
            rw [h, hi1f] at h2
            exact Bool.false_ne_true h2
          have hL := two_list hlen2 hi2m hi1m hne
          right
          exact ⟨k, i2, i1, ⟨hk, hop, hL⟩, h2, h1⟩
        · obtain ⟨i, hi, hlt, hvi⟩ :=
            (val_or (n := N + N) (x := List.ofFn (pr p l)) (by simp) hk hop).mp hv
          rcases ih i hlt hvi with (h | h) | h
          · left
            left
            exact (val_or (n := N + N) (x := List.ofFn (e1 p)) (by simp) hk hop).mpr
              ⟨i, hi, hlt, h⟩
          · left
            right
            exact (val_or (n := N + N) (x := List.ofFn (e2 l)) (by simp) hk hop).mpr
              ⟨i, hi, hlt, h⟩
          · right
            exact h

-- a witnessing gate only joins incident pairs

lemma inc {N : ℕ} {I : Fin N → Fin N → Prop} {C : Circuit} {j a c : ℕ}
    (hRB : ReadsBack (N + N) C) (hAO : PEqualNP.EdgeOwnership.AndOrOnly C)
    (hAP : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ p0 l0 : Fin N, ¬ I p0 l0 → val C (List.ofFn (pr p0 l0)) (N + N + j) = false)
    (hw : Wit C j a c) (p l : Fin N) (ha : val C (List.ofFn (e1 p)) a = true)
    (hc : val C (List.ofFn (e2 l)) c = true) : I p l := by
  by_contra hI
  obtain ⟨hj, hop, hin⟩ := hw
  have hz := hAP j hj hop p l hI
  have ha' := mono (N + N) C hAO (e1 p) (pr p l) (pr_of1 p l) a ha
  have hc' := mono (N + N) C hAO (e2 l) (pr p l) (pr_of2 p l) c hc
  have h1 : val C (List.ofFn (pr p l)) (N + N + j) = true := by
    rw [val_and (n := N + N) (x := List.ofFn (pr p l)) (by simp) hj hop]
    intro i hi
    refine ⟨hRB j hj i hi, ?_⟩
    have hi2 : i = a ∨ i = c := by
      rcases hin with h | h
      · rw [h] at hi
        simpa using hi
      · rw [h] at hi
        simp at hi
        exact hi.symm
    rcases hi2 with h | h
    · rw [h]
      exact ha'
    · rw [h]
      exact hc'
  rw [hz] at h1
  exact Bool.false_ne_true h1

-- downward closure of a bound on the wire sets

lemma stepT {N : ℕ} {C : Circuit} (hM : PEqualNP.MetaComplexity.Monotone2 C)
    (hRB : ReadsBack (N + N) C) (X : Fin N → Fin (N + N) → Bool)
    (hX : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ i : Fin N, val C (List.ofFn (X i)) (N + N + j) = false)
    (T : Finset (Fin N)) :
    ∀ j, wset C X (N + N + j) ⊆ T → ∃ R : Finset ℕ, R.card ≤ 2 ∧
      (∀ r ∈ R, r < N + N + j ∧ wset C X r ⊆ T) ∧
      wset C X (N + N + j) ⊆ R.biUnion (wset C X) := by
  intro j hj
  by_cases hjl : j < C.gates.length
  · have hmem := gateAt_mem hjl
    have hlen : (gateAt C j).inputs.length ≤ 2 := (hM _ hmem).2
    have hrb : ∀ i ∈ (gateAt C j).inputs, i < N + N + j := hRB j hjl
    rcases andOr_of hM _ hmem with hop | hop
    · refine ⟨∅, by simp, by simp, ?_⟩
      intro i hi
      rw [mem_wset, hX j hjl hop i] at hi
      exact absurd hi Bool.false_ne_true
    · refine ⟨(gateAt C j).inputs.toFinset, le_trans (List.toFinset_card_le _) hlen, ?_, ?_⟩
      · intro r hr
        have hr2 := List.mem_toFinset.mp hr
        refine ⟨hrb r hr2, ?_⟩
        intro i hi
        apply hj
        rw [mem_wset] at hi ⊢
        exact (val_or (n := N + N) (x := List.ofFn (X i)) (by simp) hjl hop).mpr
          ⟨r, hr2, hrb r hr2, hi⟩
      · intro i hi
        rw [mem_wset] at hi
        obtain ⟨r, hr, _, h⟩ := (val_or (n := N + N) (x := List.ofFn (X i)) (by simp) hjl hop).mp hi
        exact Finset.mem_biUnion.mpr ⟨r, List.mem_toFinset.mpr hr, mem_wset.mpr h⟩
  · refine ⟨∅, by simp, by simp, ?_⟩
    intro i hi
    rw [mem_wset, val_ge (n := N + N) (x := List.ofFn (X i)) (by simp) (by omega)] at hi
    exact absurd hi Bool.false_ne_true

-- the families

lemma fin_aux (M : ℕ) (P : ℕ → Prop) : Set.Finite {c : ℕ | c < M ∧ P c} :=
  (Set.finite_lt_nat M).subset (fun _ hc => hc.1)

noncomputable def finOf (M : ℕ) (P : ℕ → Prop) : Finset ℕ := (fin_aux M P).toFinset

lemma mem_finOf {M : ℕ} {P : ℕ → Prop} {c : ℕ} : c ∈ finOf M P ↔ c < M ∧ P c := by
  unfold finOf
  rw [Set.Finite.mem_toFinset]
  rfl

noncomputable def Fam (N : ℕ) (C : Circuit) (p : Fin N) : Finset ℕ :=
  finOf (N + N + C.gates.length) (fun c => ∃ j a, Wit C j a c ∧ wset (N := N) C e1 a = {p})

noncomputable def Fam2 (N : ℕ) (C : Circuit) (l : Fin N) : Finset ℕ :=
  finOf (N + N + C.gates.length) (fun a => ∃ j c, Wit C j a c ∧
    2 ≤ (wset (N := N) C e1 a).card ∧ wset (N := N) C e2 c = {l})

lemma mem_Fam {N : ℕ} {C : Circuit} {p : Fin N} {c : ℕ} :
    c ∈ Fam N C p ↔ c < N + N + C.gates.length ∧
      ∃ j a, Wit C j a c ∧ wset (N := N) C e1 a = {p} := mem_finOf

lemma mem_Fam2 {N : ℕ} {C : Circuit} {l : Fin N} {a : ℕ} :
    a ∈ Fam2 N C l ↔ a < N + N + C.gates.length ∧
      ∃ j c, Wit C j a c ∧ 2 ≤ (wset (N := N) C e1 a).card ∧ wset (N := N) C e2 c = {l} :=
  mem_finOf

def TP {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (p : Fin N) : Finset (Fin N) :=
  Finset.univ.filter (fun l => I p l)

def TL {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (l : Fin N) : Finset (Fin N) :=
  Finset.univ.filter (fun p => I p l)

lemma mem_TP {N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] {p l : Fin N} :
    l ∈ TP I p ↔ I p l := by
  unfold TP
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

lemma mem_TL {N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] {p l : Fin N} :
    p ∈ TL I l ↔ I p l := by
  unfold TL
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

def KL (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit) (p : Fin N) :
    Finset ℕ :=
  (Finset.range C.gates.length).filter (fun j => 2 ≤ (wset (N := N) C e2 (N + N + j)).card ∧
    wset (N := N) C e2 (N + N + j) ⊆ TP I p)

def KP (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit) (l : Fin N) :
    Finset ℕ :=
  (Finset.range C.gates.length).filter (fun j => 2 ≤ (wset (N := N) C e1 (N + N + j)).card ∧
    wset (N := N) C e1 (N + N + j) ⊆ TL I l)

lemma mem_KL {N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] {C : Circuit} {p : Fin N}
    {j : ℕ} : j ∈ KL N I C p ↔ j < C.gates.length ∧ (2 ≤ (wset (N := N) C e2 (N + N + j)).card ∧
      wset (N := N) C e2 (N + N + j) ⊆ TP I p) := by
  unfold KL
  rw [Finset.mem_filter, Finset.mem_range]

lemma mem_KP {N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] {C : Circuit} {l : Fin N}
    {j : ℕ} : j ∈ KP N I C l ↔ j < C.gates.length ∧ (2 ≤ (wset (N := N) C e1 (N + N + j)).card ∧
      wset (N := N) C e1 (N + N + j) ⊆ TL I l) := by
  unfold KP
  rw [Finset.mem_filter, Finset.mem_range]

lemma boundL {N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] {C : Circuit}
    (hM : PEqualNP.MetaComplexity.Monotone2 C) (hRB : ReadsBack (N + N) C)
    (hAP : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ p0 l0 : Fin N, ¬ I p0 l0 → val C (List.ofFn (pr p0 l0)) (N + N + j) = false)
    (hA2 : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ l : Fin N, val C (List.ofFn (e2 l)) (N + N + j) = false) (p : Fin N) :
    ((Fam N C p).biUnion (wset (N := N) C e2)).card ≤ (Fam N C p).card + (KL N I C p).card := by
  have hAO := andOr_of hM
  have hF : ∀ w ∈ Fam N C p, w < N + N + C.gates.length ∧ wset (N := N) C e2 w ⊆ TP I p := by
    intro w hw
    obtain ⟨hlt, j, a, hwit, hPa⟩ := mem_Fam.mp hw
    refine ⟨hlt, ?_⟩
    intro l hl
    exact mem_TP.mpr (inc hRB hAO hAP hwit p l (sing_val hPa) (mem_wset.mp hl))
  exact unionL (wset (N := N) C e2) (fun w => wset (N := N) C e2 w ⊆ TP I p) (N + N)
    (base_le C e2 e2_inj) (stepT hM hRB e2 hA2 (TP I p)) C.gates.length (Fam N C p) hF

lemma boundP {N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] {C : Circuit}
    (hM : PEqualNP.MetaComplexity.Monotone2 C) (hRB : ReadsBack (N + N) C)
    (hAP : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ p0 l0 : Fin N, ¬ I p0 l0 → val C (List.ofFn (pr p0 l0)) (N + N + j) = false)
    (hA1 : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ p : Fin N, val C (List.ofFn (e1 p)) (N + N + j) = false) (l : Fin N) :
    ((Fam2 N C l).biUnion (wset (N := N) C e1)).card ≤ (Fam2 N C l).card + (KP N I C l).card := by
  have hAO := andOr_of hM
  have hF : ∀ w ∈ Fam2 N C l, w < N + N + C.gates.length ∧ wset (N := N) C e1 w ⊆ TL I l := by
    intro w hw
    obtain ⟨hlt, j, c, hwit, _, hSc⟩ := mem_Fam2.mp hw
    refine ⟨hlt, ?_⟩
    intro p hp
    exact mem_TL.mpr (inc hRB hAO hAP hwit p l (mem_wset.mp hp) (sing_val hSc))
  exact unionL (wset (N := N) C e1) (fun w => wset (N := N) C e1 w ⊆ TL I l) (N + N)
    (base_le C e1 e1_inj) (stepT hM hRB e1 hA1 (TL I l)) C.gates.length (Fam2 N C l) hF

lemma sumKL {N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] {C : Circuit}
    (h4 : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) :
    ∑ p, (KL N I C p).card ≤ C.gates.length := by
  rw [← Finset.card_sigma]
  refine le_trans (Finset.card_le_card_of_injOn (t := Finset.range C.gates.length)
    (fun x => x.2) ?_ ?_) (by simp)
  · intro x hx
    have hx2 := (Finset.mem_sigma.mp (Finset.mem_coe.mp hx)).2
    exact Finset.mem_coe.mpr (Finset.mem_range.mpr (mem_KL.mp hx2).1)
  · intro x hx y hy hxy
    obtain ⟨p, j⟩ := x
    obtain ⟨p', j'⟩ := y
    have hjj : j = j' := hxy
    subst hjj
    have hx2 : j ∈ KL N I C p := (Finset.mem_sigma.mp (Finset.mem_coe.mp hx)).2
    have hy2 : j ∈ KL N I C p' := (Finset.mem_sigma.mp (Finset.mem_coe.mp hy)).2
    obtain ⟨_, hbig, hgx⟩ := mem_KL.mp hx2
    obtain ⟨_, _, hgy⟩ := mem_KL.mp hy2
    have h1 : 1 < (wset (N := N) C e2 (N + N + j)).card := hbig
    obtain ⟨l1, hl1, l2, hl2, hne⟩ := Finset.one_lt_card.mp h1
    have hpp : p = p' := by
      by_contra hne'
      exact h4 p p' l1 l2 hne' hne ⟨mem_TP.mp (hgx hl1), mem_TP.mp (hgx hl2),
        mem_TP.mp (hgy hl1), mem_TP.mp (hgy hl2)⟩
    subst hpp
    rfl

lemma sumKP {N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] {C : Circuit}
    (h4 : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) :
    ∑ l, (KP N I C l).card ≤ C.gates.length := by
  rw [← Finset.card_sigma]
  refine le_trans (Finset.card_le_card_of_injOn (t := Finset.range C.gates.length)
    (fun x => x.2) ?_ ?_) (by simp)
  · intro x hx
    have hx2 := (Finset.mem_sigma.mp (Finset.mem_coe.mp hx)).2
    exact Finset.mem_coe.mpr (Finset.mem_range.mpr (mem_KP.mp hx2).1)
  · intro x hx y hy hxy
    obtain ⟨l, j⟩ := x
    obtain ⟨l', j'⟩ := y
    have hjj : j = j' := hxy
    subst hjj
    have hx2 : j ∈ KP N I C l := (Finset.mem_sigma.mp (Finset.mem_coe.mp hx)).2
    have hy2 : j ∈ KP N I C l' := (Finset.mem_sigma.mp (Finset.mem_coe.mp hy)).2
    obtain ⟨_, hbig, hgx⟩ := mem_KP.mp hx2
    obtain ⟨_, _, hgy⟩ := mem_KP.mp hy2
    have h1 : 1 < (wset (N := N) C e1 (N + N + j)).card := hbig
    obtain ⟨p1, hp1, p2, hp2, hne⟩ := Finset.one_lt_card.mp h1
    have hll : l = l' := by
      by_contra hne'
      exact h4 p1 p2 l l' hne hne' ⟨mem_TL.mp (hgx hp1), mem_TL.mp (hgy hp1),
        mem_TL.mp (hgx hp2), mem_TL.mp (hgy hp2)⟩
    subst hll
    rfl

-- gate slots

def Tg (C : Circuit) : Finset (ℕ × ℕ) :=
  (Finset.range C.gates.length).biUnion
    (fun j => (gateAt C j).inputs.toFinset.image (fun a => (j, a)))

lemma mem_Tg {C : Circuit} {j a : ℕ} (hj : j < C.gates.length) (ha : a ∈ (gateAt C j).inputs) :
    (j, a) ∈ Tg C := by
  unfold Tg
  exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj,
    Finset.mem_image.mpr ⟨a, List.mem_toFinset.mpr ha, rfl⟩⟩

lemma card_Tg {C : Circuit} (hM : PEqualNP.MetaComplexity.Monotone2 C) :
    (Tg C).card ≤ 2 * C.gates.length := by
  unfold Tg
  refine le_trans Finset.card_biUnion_le ?_
  have h : ∀ j ∈ Finset.range C.gates.length,
      ((gateAt C j).inputs.toFinset.image (fun a => (j, a))).card ≤ 2 := by
    intro j hj
    exact le_trans Finset.card_image_le (le_trans (List.toFinset_card_le _)
      (hM _ (gateAt_mem (Finset.mem_range.mp hj))).2)
  refine le_trans (Finset.sum_le_sum h) ?_
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
  omega

lemma sumFam {N : ℕ} {C : Circuit} (hM : PEqualNP.MetaComplexity.Monotone2 C) :
    ∑ p, (Fam N C p).card + ∑ l, (Fam2 N C l).card ≤ 2 * C.gates.length := by
  rw [← Finset.card_sigma, ← Finset.card_sigma]
  have key1 : ∀ x ∈ Finset.univ.sigma (Fam N C), ∃ q : ℕ × ℕ,
      Wit C q.1 q.2 x.2 ∧ wset (N := N) C e1 q.2 = {x.1} := by
    intro x hx
    obtain ⟨j, a, h1, h2⟩ := (mem_Fam.mp (Finset.mem_sigma.mp hx).2).2
    exact ⟨(j, a), h1, h2⟩
  have key2 : ∀ y ∈ Finset.univ.sigma (Fam2 N C), ∃ q : ℕ × ℕ,
      Wit C q.1 y.2 q.2 ∧ 2 ≤ (wset (N := N) C e1 y.2).card ∧ wset (N := N) C e2 q.2 = {y.1} := by
    intro y hy
    obtain ⟨j, c, h1, h2, h3⟩ := (mem_Fam2.mp (Finset.mem_sigma.mp hy).2).2
    exact ⟨(j, c), h1, h2, h3⟩
  choose! g hg using key1
  choose! h hh using key2
  have i1 : Set.InjOn g ↑(Finset.univ.sigma (Fam N C)) := by
    intro x hx y hy hxy
    obtain ⟨hwx, hPx⟩ := hg x (Finset.mem_coe.mp hx)
    obtain ⟨hwy, hPy⟩ := hg y (Finset.mem_coe.mp hy)
    rw [hxy] at hwx hPx
    have h2 : x.2 = y.2 := other hwx.2.2 hwy.2.2
    rw [hPy] at hPx
    have h1 : x.1 = y.1 := (Finset.singleton_inj.mp hPx).symm
    obtain ⟨p, c⟩ := x
    obtain ⟨p', c'⟩ := y
    have e1' : p = p' := h1
    have e2' : c = c' := h2
    subst e1'
    subst e2'
    rfl
  have i2 : Set.InjOn (fun y => ((h y).1, y.2)) ↑(Finset.univ.sigma (Fam2 N C)) := by
    intro x hx y hy hxy
    obtain ⟨hwx, _, hSx⟩ := hh x (Finset.mem_coe.mp hx)
    obtain ⟨hwy, _, hSy⟩ := hh y (Finset.mem_coe.mp hy)
    have hxy' : ((h x).1, x.2) = ((h y).1, y.2) := hxy
    have hj : (h x).1 = (h y).1 := (Prod.mk.inj hxy').1
    have h2 : x.2 = y.2 := (Prod.mk.inj hxy').2
    rw [hj, h2] at hwx
    have hc : (h x).2 = (h y).2 := other hwx.2.2 hwy.2.2
    rw [hc, hSy] at hSx
    have h1 : x.1 = y.1 := (Finset.singleton_inj.mp hSx).symm
    obtain ⟨l, a⟩ := x
    obtain ⟨l', a'⟩ := y
    have e1' : l = l' := h1
    have e2' : a = a' := h2
    subst e1'
    subst e2'
    rfl
  have dj : Disjoint ((Finset.univ.sigma (Fam N C)).image g)
      ((Finset.univ.sigma (Fam2 N C)).image (fun y => ((h y).1, y.2))) := by
    rw [Finset.disjoint_left]
    intro q hq1 hq2
    obtain ⟨x, hx, hxq⟩ := Finset.mem_image.mp hq1
    obtain ⟨y, hy, hyq⟩ := Finset.mem_image.mp hq2
    obtain ⟨_, hPx⟩ := hg x hx
    obtain ⟨_, h2y, _⟩ := hh y hy
    have ha : (g x).2 = y.2 := by
      rw [hxq, ← hyq]
    rw [← ha, hPx, Finset.card_singleton] at h2y
    omega
  have c1 := Finset.card_image_of_injOn i1
  have c2 := Finset.card_image_of_injOn i2
  have c3 := Finset.card_union_of_disjoint dj
  have c4 : ((Finset.univ.sigma (Fam N C)).image g ∪
      (Finset.univ.sigma (Fam2 N C)).image (fun y => ((h y).1, y.2))).card ≤ (Tg C).card := by
    apply Finset.card_le_card
    intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · obtain ⟨x, hx, hxq⟩ := Finset.mem_image.mp hq
      obtain ⟨hwa, _⟩ := hg x hx
      obtain ⟨hj, ha, _⟩ := wit_mem hwa
      rw [← hxq]
      exact mem_Tg hj ha
    · obtain ⟨y, hy, hyq⟩ := Finset.mem_image.mp hq
      obtain ⟨hwc, _⟩ := hh y hy
      obtain ⟨hj, ha, _⟩ := wit_mem hwc
      rw [← hyq]
      exact mem_Tg hj ha
  have c5 := card_Tg hM (C := C)
  omega

noncomputable def TA (N : ℕ) (C : Circuit) : Finset (Fin N × Fin N) :=
  Finset.univ.biUnion (fun p => ((Fam N C p).biUnion (wset (N := N) C e2)).image (fun l => (p, l)))

noncomputable def TB (N : ℕ) (C : Circuit) : Finset (Fin N × Fin N) :=
  Finset.univ.biUnion (fun l => ((Fam2 N C l).biUnion (wset (N := N) C e1)).image (fun p => (p, l)))

lemma cardT {N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] {C : Circuit}
    (hM : PEqualNP.MetaComplexity.Monotone2 C) (hRB : ReadsBack (N + N) C)
    (h4 : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (hAP : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ p0 l0 : Fin N, ¬ I p0 l0 → val C (List.ofFn (pr p0 l0)) (N + N + j) = false)
    (hA1 : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ p : Fin N, val C (List.ofFn (e1 p)) (N + N + j) = false)
    (hA2 : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ l : Fin N, val C (List.ofFn (e2 l)) (N + N + j) = false) :
    (TA N C ∪ TB N C).card ≤ 4 * C.gates.length := by
  have s1 := Finset.card_union_le (TA N C) (TB N C)
  have s2 : (TA N C).card ≤ ∑ p, ((Fam N C p).biUnion (wset (N := N) C e2)).card := by
    unfold TA
    exact le_trans Finset.card_biUnion_le (Finset.sum_le_sum (fun p _ => Finset.card_image_le))
  have s3 : (TB N C).card ≤ ∑ l, ((Fam2 N C l).biUnion (wset (N := N) C e1)).card := by
    unfold TB
    exact le_trans Finset.card_biUnion_le (Finset.sum_le_sum (fun l _ => Finset.card_image_le))
  have s4 : ∑ p, ((Fam N C p).biUnion (wset (N := N) C e2)).card ≤
      ∑ p, ((Fam N C p).card + (KL N I C p).card) :=
    Finset.sum_le_sum (fun p _ => boundL hM hRB hAP hA2 p)
  have s5 : ∑ l, ((Fam2 N C l).biUnion (wset (N := N) C e1)).card ≤
      ∑ l, ((Fam2 N C l).card + (KP N I C l).card) :=
    Finset.sum_le_sum (fun l _ => boundP hM hRB hAP hA1 l)
  rw [Finset.sum_add_distrib] at s4 s5
  have s6 := sumKL (I := I) (C := C) h4
  have s7 := sumKP (I := I) (C := C) h4
  have s8 := sumFam (N := N) (C := C) hM
  omega

theorem main_aux : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ p1 l1 : Fin N, I p1 l1 → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k1 : Fin (N + N) => decide (k1 = Fin.castAdd N p1 ∨ k1 = Fin.natAdd N l1)) = true) → (∀ k2 : Fin (N + N), PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k3 : Fin (N + N) => decide (k3 = k2)) = false) → (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ p0 l0 : Fin N, ¬ I p0 l0 → (C.wires (List.ofFn (fun ke : Fin (N + N) => decide (ke = Fin.castAdd N p0 ∨ ke = Fin.natAdd N l0)))).getD (N + N + j) false = false) → (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ p : Fin N, (C.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (C.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false) → (Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)).card ≤ 5 * C.size + 1 := by
  intro N I _ C h4 hM hRB hcomp hone hAP0 hAO0
  have hAO := andOr_of hM
  have hAP : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ p0 l0 : Fin N, ¬ I p0 l0 → val C (List.ofFn (pr p0 l0)) (N + N + j) = false := hAP0
  have hA1 : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ p : Fin N, val C (List.ofFn (e1 p)) (N + N + j) = false :=
    fun j hj hop => (hAO0 j hj hop).1
  have hA2 : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ l : Fin N, val C (List.ofFn (e2 l)) (N + N + j) = false :=
    fun j hj hop => (hAO0 j hj hop).2
  refine le_trans (Finset.card_le_card (t := TA N C ∪ TB N C) ?_) ?_
  · intro e he
    have hI : I e.1 e.2 := (Finset.mem_filter.mp he).2
    have hv : val C (List.ofFn (pr e.1 e.2)) C.output = true := hcomp e.1 e.2 hI
    rcases reach hM hRB hA1 hA2 e.1 e.2 C.output hv with (h | h) | ⟨j, a, c, hw, ha', hc'⟩
    · have h0 : val C (List.ofFn (e1 e.1)) C.output = false := hone (Fin.castAdd N e.1)
      rw [h0] at h
      exact absurd h Bool.false_ne_true
    · have h0 : val C (List.ofFn (e2 e.2)) C.output = false := hone (Fin.natAdd N e.2)
      rw [h0] at h
      exact absurd h Bool.false_ne_true
    have hj := hw.1
    have hin := hw.2.2
    have hrb := hRB j hj
    have hal : a < N + N + j := by
      rcases hin with h | h <;> rw [h] at hrb <;> exact hrb a (by simp)
    have hcl : c < N + N + j := by
      rcases hin with h | h <;> rw [h] at hrb <;> exact hrb c (by simp)
    have hpa : e.1 ∈ wset (N := N) C e1 a := mem_wset.mpr ha'
    have hlc : e.2 ∈ wset (N := N) C e2 c := mem_wset.mpr hc'
    rw [Finset.mem_union]
    by_cases hP : (wset (N := N) C e1 a).card ≤ 1
    · left
      have hPe : wset (N := N) C e1 a = {e.1} := Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hpa, fun x hx => Finset.card_le_one.mp hP x hx e.1 hpa⟩
      unfold TA
      rw [Finset.mem_biUnion]
      refine ⟨e.1, Finset.mem_univ _, Finset.mem_image.mpr ⟨e.2, ?_, rfl⟩⟩
      exact Finset.mem_biUnion.mpr ⟨c, mem_Fam.mpr ⟨by omega, j, a, hw, hPe⟩, hlc⟩
    · right
      have hP2 : 1 < (wset (N := N) C e1 a).card := by omega
      obtain ⟨p1, hp1, p2, hp2, hne⟩ := Finset.one_lt_card.mp hP2
      have hSe : wset (N := N) C e2 c = {e.2} := by
        refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hlc, fun l hl => ?_⟩
        have hl' := mem_wset.mp hl
        exact two4 h4 hne (inc hRB hAO hAP hw p1 l (mem_wset.mp hp1) hl')
          (inc hRB hAO hAP hw p2 l (mem_wset.mp hp2) hl')
          (inc hRB hAO hAP hw p1 e.2 (mem_wset.mp hp1) hc')
          (inc hRB hAO hAP hw p2 e.2 (mem_wset.mp hp2) hc')
      unfold TB
      rw [Finset.mem_biUnion]
      refine ⟨e.2, Finset.mem_univ _, Finset.mem_image.mpr ⟨e.1, ?_, rfl⟩⟩
      exact Finset.mem_biUnion.mpr ⟨a, mem_Fam2.mpr ⟨by omega, j, c, hw, by omega, hSe⟩, hpa⟩
  · have h1 := cardT hM hRB h4 hAP hA1 hA2
    have h2 : C.size = C.gates.length := rfl
    omega

end PEqualNP.Outside.L_meta_3447

theorem PEqualNP.Outside.L_meta_3447 : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ p1 l1 : Fin N, I p1 l1 → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k1 : Fin (N + N) => decide (k1 = Fin.castAdd N p1 ∨ k1 = Fin.natAdd N l1)) = true) → (∀ k2 : Fin (N + N), PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k3 : Fin (N + N) => decide (k3 = k2)) = false) → (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ p0 l0 : Fin N, ¬ I p0 l0 → (C.wires (List.ofFn (fun ke : Fin (N + N) => decide (ke = Fin.castAdd N p0 ∨ ke = Fin.natAdd N l0)))).getD (N + N + j) false = false) → (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ p : Fin N, (C.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (C.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false) → (Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)).card ≤ 5 * C.size + 1 :=
  PEqualNP.Outside.L_meta_3447.main_aux
