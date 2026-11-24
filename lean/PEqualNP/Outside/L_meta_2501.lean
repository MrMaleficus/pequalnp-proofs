import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2501

open PEqualNP.CircuitLowerBounds PEqualNP.BicliqueBlockCost PEqualNP.SharedBlockCost

-- wire values as a fold over the gate list

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp [step, List.getD, List.getElem?_append_left hi]

lemma step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp [step, List.getD]

def W {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl step (List.ofFn x)

lemma fold_len (gs : List Gate) :
    ∀ w : List Bool, (gs.foldl step w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih, step_len, List.length_cons]
    omega

lemma fold_lt (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (gs.foldl step w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [List.foldl_cons, ih _ i (by rw [step_len]; omega)]
    exact step_lt w g i hi

lemma W_len {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    (W gs x).length = n + gs.length := by
  rw [W, fold_len]
  simp

lemma W_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    W (gs ++ [g]) x = step (W gs x) g := by
  simp [W, List.foldl_append]

def wv {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (W gs x).getD w false

lemma wv_input {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : Fin n) :
    wv gs x i.val = x i := by
  unfold wv
  rw [W, fold_lt gs _ _ (by simp)]
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

lemma wv_append_lt {n : ℕ} (gs ext : List Gate) (x : Fin n → Bool) (w : ℕ)
    (hw : w < n + gs.length) : wv (gs ++ ext) x w = wv gs x w := by
  unfold wv W
  rw [List.foldl_append]
  exact fold_lt ext _ w (by rw [fold_len]; simpa using hw)

lemma wv_snoc_last {n : ℕ} (gs : List Gate) (a b : ℕ) (x : Fin n → Bool) (op : GateOp)
    (hop : isOrOp op = true) :
    wv (gs ++ [(⟨op, [a, b]⟩ : Gate)]) x (n + gs.length) = (wv gs x a || wv gs x b) := by
  have hor : op = GateOp.or := by
    cases op <;> simp_all [isOrOp]
  subst hor
  unfold wv
  rw [W_snoc, step_last _ _ _ (by rw [W_len])]
  simp [GateOp.eval]

-- the set of a wire: the inputs whose indicator vector switches it on

def ind {n : ℕ} (i : Fin n) : Fin n → Bool := fun j => decide (j = i)

def T {n : ℕ} (gs : List Gate) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => wv gs (ind i) w = true)

lemma mem_T {n : ℕ} (gs : List Gate) (w : ℕ) (i : Fin n) :
    i ∈ (T gs w : Finset (Fin n)) ↔ wv gs (ind i) w = true := by
  unfold T
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

lemma T_input {n : ℕ} (gs : List Gate) (i : Fin n) :
    (T gs i.val : Finset (Fin n)) = {i} := by
  ext j
  rw [mem_T, wv_input, Finset.mem_singleton]
  show decide (i = j) = true ↔ j = i
  rw [decide_eq_true_eq]
  exact eq_comm

lemma T_input2 {n : ℕ} (gs : List Gate) (w : ℕ) (hw : w < n) :
    (T gs w : Finset (Fin n)) = {(⟨w, hw⟩ : Fin n)} :=
  T_input gs (⟨w, hw⟩ : Fin n)

lemma T_append_lt {n : ℕ} (gs ext : List Gate) (w : ℕ) (hw : w < n + gs.length) :
    (T (gs ++ ext) w : Finset (Fin n)) = T gs w := by
  ext i
  rw [mem_T, mem_T, wv_append_lt gs ext _ w hw]

lemma T_snoc_last {n : ℕ} (gs : List Gate) (a b : ℕ) (op : GateOp) (hop : isOrOp op = true) :
    (T (gs ++ [(⟨op, [a, b]⟩ : Gate)]) (n + gs.length) : Finset (Fin n)) = T gs a ∪ T gs b := by
  ext i
  rw [mem_T, Finset.mem_union, mem_T, mem_T, wv_snoc_last gs a b _ op hop, Bool.or_eq_true]

-- OR circuits as gate lists

def OrC (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j (h : j < gs.length), isOrOp (gs[j]'h).op = true ∧
    (gs[j]'h).inputs.length = 2 ∧ ∀ i ∈ (gs[j]'h).inputs, i < n + j

lemma orC_nil (n : ℕ) : OrC n [] := by
  intro j h
  simp at h

lemma orC_snoc {n : ℕ} {gs : List Gate} (h : OrC n gs) (a b : ℕ) (ha : a < n + gs.length)
    (hb : b < n + gs.length) : OrC n (gs ++ [(⟨GateOp.or, [a, b]⟩ : Gate)]) := by
  intro j hj
  by_cases hlt : j < gs.length
  · have e : (gs ++ [(⟨GateOp.or, [a, b]⟩ : Gate)])[j]'hj = gs[j]'hlt :=
      List.getElem_append_left hlt
    rw [e]
    exact h j hlt
  · have hj2 : j = gs.length := by
      rw [List.length_append, List.length_singleton] at hj
      omega
    subst hj2
    have e : (gs ++ [(⟨GateOp.or, [a, b]⟩ : Gate)])[gs.length]'hj = ⟨GateOp.or, [a, b]⟩ := by
      simp
    rw [e]
    refine ⟨rfl, rfl, ?_⟩
    intro i hi
    have hi2 : i = a ∨ i = b := by simpa using hi
    rcases hi2 with h1 | h1
    · rw [h1]; exact ha
    · rw [h1]; exact hb

lemma orC_init {n : ℕ} {gs : List Gate} {g : Gate} (h : OrC n (gs ++ [g])) :
    OrC n gs ∧ ∃ (op : GateOp) (a b : ℕ), g = ⟨op, [a, b]⟩ ∧ isOrOp op = true ∧
      a < n + gs.length ∧ b < n + gs.length := by
  constructor
  · intro j hj
    have hj2 : j < (gs ++ [g]).length := by
      rw [List.length_append]; omega
    have h1 := h j hj2
    have e : (gs ++ [g])[j]'hj2 = gs[j]'hj := List.getElem_append_left hj
    rw [e] at h1
    exact h1
  · have hj2 : gs.length < (gs ++ [g]).length := by simp
    have h1 := h gs.length hj2
    have e : (gs ++ [g])[gs.length]'hj2 = g := by simp
    rw [e] at h1
    obtain ⟨op, inp⟩ := g
    obtain ⟨h2, h3, h4⟩ := h1
    have h3b : inp.length = 2 := h3
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp h3b
    subst hab
    exact ⟨op, a, b, rfl, h2, h4 a (by simp), h4 b (by simp)⟩

lemma T_nonempty {n : ℕ} : ∀ gs : List Gate, OrC n gs → ∀ w, w < n + gs.length →
    (T gs w : Finset (Fin n)).Nonempty := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ w hw
    have hw2 : w < n := by simpa using hw
    rw [T_input2 _ w hw2]
    exact Finset.singleton_nonempty _
  | append_singleton gs g ih =>
    intro hor w hw
    obtain ⟨hgs, op, a, b, rfl, hop, ha, hb⟩ := orC_init hor
    by_cases hlt : w < n + gs.length
    · rw [T_append_lt gs _ w hlt]
      exact ih hgs w hlt
    · have hw2 : w = n + gs.length := by
        rw [List.length_append, List.length_singleton] at hw
        omega
      subst hw2
      rw [T_snoc_last gs a b op hop]
      exact (ih hgs a ha).mono Finset.subset_union_left

-- the counted gates: sets of size at least two inside a member of the family

def cntSet {n : ℕ} (gs : List Gate) (LL : Finset (Finset (Fin n))) : Finset ℕ :=
  (Finset.range gs.length).filter (fun j =>
    2 ≤ (T gs (n + j) : Finset (Fin n)).card ∧ ∃ L ∈ LL, (T gs (n + j) : Finset (Fin n)) ⊆ L)

lemma mem_cntSet {n : ℕ} (gs : List Gate) (LL : Finset (Finset (Fin n))) (j : ℕ) :
    j ∈ cntSet gs LL ↔ j < gs.length ∧
      2 ≤ (T gs (n + j) : Finset (Fin n)).card ∧
        ∃ L ∈ LL, (T gs (n + j) : Finset (Fin n)) ⊆ L := by
  unfold cntSet
  rw [Finset.mem_filter, Finset.mem_range]

lemma core {n : ℕ} : ∀ gs : List Gate, OrC n gs → ∀ LL : Finset (Finset (Fin n)),
    (∀ L ∈ LL, ∃ w, w < n + gs.length ∧ (T gs w : Finset (Fin n)) = L) →
    (LL.biUnion id).card ≤ (cntSet gs LL).card + LL.card := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ LL hLL
    have h1 : (LL.biUnion id).card ≤ ∑ L ∈ LL, (id L).card := Finset.card_biUnion_le
    have h2 : ∑ L ∈ LL, (id L).card ≤ ∑ _L ∈ LL, 1 := by
      apply Finset.sum_le_sum
      intro L hL
      obtain ⟨w, hw, hwL⟩ := hLL L hL
      have hw2 : w < n := by simpa using hw
      rw [T_input2 _ w hw2] at hwL
      rw [← hwL]
      simp
    have h3 : ∑ _L ∈ LL, 1 = LL.card := by simp
    omega
  | append_singleton gs g ih =>
    intro hor LL hLL
    obtain ⟨hgs, op, a, b, rfl, hop, ha, hb⟩ := orC_init hor
    have hlen : (gs ++ [(⟨op, [a, b]⟩ : Gate)]).length = gs.length + 1 := by simp
    have hTold : ∀ w, w < n + gs.length →
        (T (gs ++ [(⟨op, [a, b]⟩ : Gate)]) w : Finset (Fin n)) = T gs w :=
      fun w hw => T_append_lt gs _ w hw
    have hTnew : (T (gs ++ [(⟨op, [a, b]⟩ : Gate)]) (n + gs.length) : Finset (Fin n))
        = T gs a ∪ T gs b := T_snoc_last gs a b op hop
    by_cases hcase : (T gs a ∪ T gs b : Finset (Fin n)) ∈ LL ∧
        ¬ ∃ w, w < n + gs.length ∧ (T gs w : Finset (Fin n)) = T gs a ∪ T gs b
    · obtain ⟨hmem, hno⟩ := hcase
      obtain ⟨LL2, hLL2⟩ : ∃ LL2 : Finset (Finset (Fin n)),
          LL2 = insert (T gs a) (insert (T gs b) (LL.erase (T gs a ∪ T gs b))) := ⟨_, rfl⟩
      have hm2 : ∀ L : Finset (Fin n), L ∈ LL2 ↔
          (L = T gs a ∨ L = T gs b ∨ (L ≠ T gs a ∪ T gs b ∧ L ∈ LL)) := by
        intro L
        rw [hLL2, Finset.mem_insert, Finset.mem_insert, Finset.mem_erase]
      have hval : ∀ L ∈ LL2, ∃ w, w < n + gs.length ∧ (T gs w : Finset (Fin n)) = L := by
        intro L hL
        rcases (hm2 L).mp hL with h | h | ⟨hne, hL1⟩
        · exact ⟨a, ha, h.symm⟩
        · exact ⟨b, hb, h.symm⟩
        · obtain ⟨w, hw, hwL⟩ := hLL L hL1
          rw [hlen] at hw
          by_cases hlt : w < n + gs.length
          · exact ⟨w, hlt, by rw [← hTold w hlt]; exact hwL⟩
          · have hw2 : w = n + gs.length := by omega
            subst hw2
            exact absurd (hwL.symm.trans hTnew) hne
      have h1 := ih hgs LL2 hval
      have hsub : LL.biUnion id ⊆ LL2.biUnion id := by
        intro x hx
        obtain ⟨L, hL, hxL⟩ := Finset.mem_biUnion.mp hx
        have hxL2 : x ∈ L := hxL
        by_cases hLe : L = T gs a ∪ T gs b
        · rw [hLe] at hxL2
          rcases Finset.mem_union.mp hxL2 with h | h
          · exact Finset.mem_biUnion.mpr ⟨T gs a, (hm2 _).mpr (Or.inl rfl), h⟩
          · exact Finset.mem_biUnion.mpr ⟨T gs b, (hm2 _).mpr (Or.inr (Or.inl rfl)), h⟩
        · exact Finset.mem_biUnion.mpr ⟨L, (hm2 _).mpr (Or.inr (Or.inr ⟨hLe, hL⟩)), hxL2⟩
      have hcard : LL2.card ≤ LL.card + 1 := by
        have e1 : (LL.erase (T gs a ∪ T gs b)).card = LL.card - 1 :=
          Finset.card_erase_of_mem hmem
        have e2 : 0 < LL.card := Finset.card_pos.mpr ⟨_, hmem⟩
        have e3 := Finset.card_insert_le (T gs a) (insert (T gs b) (LL.erase (T gs a ∪ T gs b)))
        have e4 := Finset.card_insert_le (T gs b) (LL.erase (T gs a ∪ T gs b))
        rw [hLL2]
        omega
      have hbig : 2 ≤ (T gs a ∪ T gs b : Finset (Fin n)).card := by
        by_contra hlt
        have hle : (T gs a ∪ T gs b : Finset (Fin n)).card ≤ 1 := by omega
        obtain ⟨x, hx⟩ := T_nonempty gs hgs a ha
        have hxu : x ∈ (T gs a ∪ T gs b : Finset (Fin n)) := Finset.mem_union_left _ hx
        have heq : (T gs a ∪ T gs b : Finset (Fin n)) = {x} := by
          ext y
          rw [Finset.mem_singleton]
          constructor
          · intro hy
            exact Finset.card_le_one.mp hle y hy x hxu
          · intro hy
            rw [hy]; exact hxu
        exact hno ⟨x.val, by have := x.isLt; omega, by rw [T_input gs x, heq]⟩
      have hcnt : (cntSet gs LL2).card + 1 ≤
          (cntSet (gs ++ [(⟨op, [a, b]⟩ : Gate)]) LL).card := by
        have hnot : gs.length ∉ cntSet gs LL2 := by
          intro h
          have := ((mem_cntSet gs LL2 gs.length).mp h).1
          omega
        rw [← Finset.card_insert_of_notMem hnot]
        apply Finset.card_le_card
        intro j hj
        rw [mem_cntSet, hlen]
        rcases Finset.mem_insert.mp hj with hj1 | hj1
        · rw [hj1, hTnew]
          exact ⟨by omega, hbig, _, hmem, Finset.Subset.refl _⟩
        · obtain ⟨hjlt, hj2, L2, hL2, hjL2⟩ := (mem_cntSet gs LL2 j).mp hj1
          have hT := hTold (n + j) (by omega)
          rw [hT]
          refine ⟨by omega, hj2, ?_⟩
          rcases (hm2 L2).mp hL2 with h | h | ⟨_, hL1⟩
          · exact ⟨_, hmem, by rw [h] at hjL2; exact hjL2.trans Finset.subset_union_left⟩
          · exact ⟨_, hmem, by rw [h] at hjL2; exact hjL2.trans Finset.subset_union_right⟩
          · exact ⟨L2, hL1, hjL2⟩
      have h5 := Finset.card_le_card hsub
      omega
    · have hval : ∀ L ∈ LL, ∃ w, w < n + gs.length ∧ (T gs w : Finset (Fin n)) = L := by
        intro L hL
        obtain ⟨w, hw, hwL⟩ := hLL L hL
        rw [hlen] at hw
        by_cases hlt : w < n + gs.length
        · exact ⟨w, hlt, by rw [← hTold w hlt]; exact hwL⟩
        · have hw2 : w = n + gs.length := by omega
          subst hw2
          have hLe : L = T gs a ∪ T gs b := hwL.symm.trans hTnew
          have hB : ∃ w, w < n + gs.length ∧ (T gs w : Finset (Fin n)) = T gs a ∪ T gs b := by
            by_contra hB
            exact hcase ⟨by rw [← hLe]; exact hL, hB⟩
          obtain ⟨w2, hw2, e⟩ := hB
          exact ⟨w2, hw2, e.trans hLe.symm⟩
      have h1 := ih hgs LL hval
      have hcnt : (cntSet gs LL).card ≤ (cntSet (gs ++ [(⟨op, [a, b]⟩ : Gate)]) LL).card := by
        apply Finset.card_le_card
        intro j hj
        obtain ⟨hjlt, hj2, hjL⟩ := (mem_cntSet gs LL j).mp hj
        have hT := hTold (n + j) (by omega)
        rw [mem_cntSet, hlen, hT]
        exact ⟨by omega, hj2, hjL⟩
      omega

-- stars

lemma cn {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : PEqualNP.TopForm.NoFourCycle G) {a b x y : Fin n} (hab : a ≠ b)
    (hax : G.Adj a x) (hbx : G.Adj b x) (hay : G.Adj a y) (hby : G.Adj b y) : x = y := by
  have h := h4 a b hab
  exact Finset.card_le_one.mp h x (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hax, hbx⟩)
    y (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hay, hby⟩)

def sm {n : ℕ} (p : Block n) : Finset (Fin n) :=
  if p.1.card ≤ 1 then p.1 else p.2

def lf {n : ℕ} (p : Block n) : Finset (Fin n) :=
  if p.1.card ≤ 1 then p.2 else p.1

lemma star {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : PEqualNP.TopForm.NoFourCycle G) (p : Block n) (hb : IsBlock G p) :
    p.1.card ≤ 1 ∨ p.2.card ≤ 1 := by
  by_contra h
  push_neg at h
  obtain ⟨a, ha, c, hc, hac⟩ := Finset.one_lt_card.mp h.1
  obtain ⟨b, hb2, d, hd, hbd⟩ := Finset.one_lt_card.mp h.2
  obtain ⟨_, _, _, hadj⟩ := hb
  exact hbd (cn G h4 hac (hadj a ha b hb2) (hadj c hc b hb2) (hadj a ha d hd) (hadj c hc d hd))

lemma sm_lf {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : PEqualNP.TopForm.NoFourCycle G) (p : Block n) (hb : IsBlock G p) :
    (sm p).card = 1 ∧ (∀ a ∈ sm p, ∀ b ∈ lf p, G.Adj a b) ∧
    (∀ u v, BlockCovers p u v → (u ∈ sm p ∧ v ∈ lf p) ∨ (v ∈ sm p ∧ u ∈ lf p)) := by
  have hs := star G h4 p hb
  obtain ⟨_, h1, h2, hadj⟩ := hb
  have c1 : 0 < p.1.card := Finset.card_pos.mpr h1
  have c2 : 0 < p.2.card := Finset.card_pos.mpr h2
  by_cases h : p.1.card ≤ 1
  · have e1 : sm p = p.1 := if_pos h
    have e2 : lf p = p.2 := if_pos h
    rw [e1, e2]
    refine ⟨by omega, hadj, ?_⟩
    intro u v huv
    exact huv
  · have e1 : sm p = p.2 := if_neg h
    have e2 : lf p = p.1 := if_neg h
    rw [e1, e2]
    refine ⟨by omega, fun a ha b hb2 => (hadj b hb2 a ha).symm, ?_⟩
    intro u v huv
    have huv2 : (u ∈ p.1 ∧ v ∈ p.2) ∨ (v ∈ p.1 ∧ u ∈ p.2) := huv
    rcases huv2 with ⟨hu, hv⟩ | ⟨hv, hu⟩
    · exact Or.inr ⟨hv, hu⟩
    · exact Or.inl ⟨hu, hv⟩

lemma sm_mem_sides {n : ℕ} (F : Finset (Block n)) (p : Block n) (hp : p ∈ F) :
    sm p ∈ sides F ∧ lf p ∈ sides F := by
  have h1 : p.1 ∈ sides F := by
    unfold sides
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem Prod.fst hp)
  have h2 : p.2 ∈ sides F := by
    unfold sides
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem Prod.snd hp)
  by_cases h : p.1.card ≤ 1
  · have e1 : sm p = p.1 := if_pos h
    have e2 : lf p = p.2 := if_pos h
    rw [e1, e2]
    exact ⟨h1, h2⟩
  · have e1 : sm p = p.2 := if_neg h
    have e2 : lf p = p.1 := if_neg h
    rw [e1, e2]
    exact ⟨h2, h1⟩

def LLc {n : ℕ} (F : Finset (Block n)) (cs : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  (F.filter (fun p => sm p = cs)).image lf

def Uc {n : ℕ} (F : Finset (Block n)) (cs : Finset (Fin n)) : Finset (Fin n) :=
  (LLc F cs).biUnion id

lemma mem_LLc {n : ℕ} (F : Finset (Block n)) (cs L : Finset (Fin n)) :
    L ∈ LLc F cs ↔ ∃ p ∈ F, sm p = cs ∧ lf p = L := by
  unfold LLc
  rw [Finset.mem_image]
  constructor
  · rintro ⟨p, hp, h⟩
    exact ⟨p, (Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2, h⟩
  · rintro ⟨p, hp, h1, h2⟩
    exact ⟨p, Finset.mem_filter.mpr ⟨hp, h1⟩, h2⟩

lemma lower {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : PEqualNP.TopForm.NoFourCycle G) (F : Finset (Block n)) (hF : IsBlockCover G F)
    (gs : List Gate) (hor : OrC n gs)
    (hw : ∀ s ∈ sides F, ∃ w, w < n + gs.length ∧ (T gs w : Finset (Fin n)) = s) :
    G.edgeFinset.card ≤ gs.length + F.card ∧
    ∃ X : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G X ∧
      X.card ≤ F.card := by
  obtain ⟨hblk, hcov⟩ := hF
  have hsl := fun (p : Block n) (hp : p ∈ F) => sm_lf G h4 p (hblk p hp)
  constructor
  · have hE : G.edgeFinset ⊆ (F.image sm).biUnion
        (fun cs => (cs ×ˢ Uc F cs).image (fun ab => s(ab.1, ab.2))) := by
      intro e
      refine Sym2.ind (fun u v => ?_) e
      intro he
      have huv : G.Adj u v := by simpa using he
      obtain ⟨p, hp, hc⟩ := hcov u v huv
      have key : ∀ a b : Fin n, a ∈ sm p → b ∈ lf p → s(a, b) ∈ (F.image sm).biUnion
          (fun cs => (cs ×ˢ Uc F cs).image (fun ab => s(ab.1, ab.2))) := by
        intro a b ha hb
        refine Finset.mem_biUnion.mpr ⟨sm p, Finset.mem_image_of_mem _ hp, ?_⟩
        refine Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, ?_⟩, rfl⟩
        exact Finset.mem_biUnion.mpr ⟨lf p, (mem_LLc F _ _).mpr ⟨p, hp, rfl, rfl⟩, hb⟩
      rcases (hsl p hp).2.2 u v hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact key u v h1 h2
      · rw [Sym2.eq_swap]
        exact key v u h1 h2
    have hdisj : ((F.image sm : Finset (Finset (Fin n))) : Set (Finset (Fin n))).PairwiseDisjoint
        (fun cs => cntSet gs (LLc F cs)) := by
      intro cs _ cs2 _ hne
      show Disjoint (cntSet gs (LLc F cs)) (cntSet gs (LLc F cs2))
      rw [Finset.disjoint_left]
      intro j hj hj2
      apply hne
      obtain ⟨_, hc2, L, hL, hTL⟩ := (mem_cntSet gs _ j).mp hj
      obtain ⟨_, _, L2, hL2, hTL2⟩ := (mem_cntSet gs _ j).mp hj2
      obtain ⟨p, hp, hpc, hpL⟩ := (mem_LLc F _ _).mp hL
      obtain ⟨q, hq, hqc, hqL⟩ := (mem_LLc F _ _).mp hL2
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (Nat.lt_of_lt_of_le one_lt_two hc2)
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp (hsl p hp).1
      obtain ⟨y, hy⟩ := Finset.card_eq_one.mp (hsl q hq).1
      have hxm : x ∈ sm p := by rw [hx]; exact Finset.mem_singleton_self x
      have hym : y ∈ sm q := by rw [hy]; exact Finset.mem_singleton_self y
      have hap : a ∈ lf p := by rw [hpL]; exact hTL ha
      have hbp : b ∈ lf p := by rw [hpL]; exact hTL hb
      have haq : a ∈ lf q := by rw [hqL]; exact hTL2 ha
      have hbq : b ∈ lf q := by rw [hqL]; exact hTL2 hb
      have hxy : x = y := cn G h4 hab
        ((hsl p hp).2.1 x hxm a hap).symm ((hsl p hp).2.1 x hxm b hbp).symm
        ((hsl q hq).2.1 y hym a haq).symm ((hsl q hq).2.1 y hym b hbq).symm
      rw [← hpc, ← hqc, hx, hy, hxy]
    have hA : ∑ cs ∈ F.image sm, (cntSet gs (LLc F cs)).card ≤ gs.length := by
      rw [← Finset.card_biUnion hdisj]
      have hsub : (F.image sm).biUnion (fun cs => cntSet gs (LLc F cs)) ⊆
          Finset.range gs.length := by
        intro j hj
        obtain ⟨cs, _, hj2⟩ := Finset.mem_biUnion.mp hj
        exact Finset.mem_range.mpr ((mem_cntSet gs _ j).mp hj2).1
      have h5 := Finset.card_le_card hsub
      rw [Finset.card_range] at h5
      exact h5
    have hB : ∑ cs ∈ F.image sm, (F.filter (fun p => sm p = cs)).card = F.card :=
      (Finset.card_eq_sum_card_image sm F).symm
    have hC : ∀ cs ∈ F.image sm,
        ((cs ×ˢ Uc F cs).image (fun ab : Fin n × Fin n => s(ab.1, ab.2))).card ≤
          (cntSet gs (LLc F cs)).card + (F.filter (fun p => sm p = cs)).card := by
      intro cs hcs
      obtain ⟨p, hp, hpc⟩ := Finset.mem_image.mp hcs
      have hcs1 : cs.card = 1 := by rw [← hpc]; exact (hsl p hp).1
      have h6 : ((cs ×ˢ Uc F cs).image (fun ab : Fin n × Fin n => s(ab.1, ab.2))).card ≤
          (cs ×ˢ Uc F cs).card := Finset.card_image_le
      have h7 : (cs ×ˢ Uc F cs).card = cs.card * (Uc F cs).card := Finset.card_product _ _
      have h8 : (Uc F cs).card ≤ (cntSet gs (LLc F cs)).card + (LLc F cs).card := by
        apply core gs hor (LLc F cs)
        intro L hL
        obtain ⟨q, hq, _, hqL⟩ := (mem_LLc F _ _).mp hL
        rw [← hqL]
        exact hw _ (sm_mem_sides F q hq).2
      have h9 : (LLc F cs).card ≤ (F.filter (fun p => sm p = cs)).card := Finset.card_image_le
      rw [hcs1, Nat.one_mul] at h7
      omega
    calc G.edgeFinset.card
        ≤ ((F.image sm).biUnion
            (fun cs => (cs ×ˢ Uc F cs).image (fun ab => s(ab.1, ab.2)))).card :=
          Finset.card_le_card hE
      _ ≤ ∑ cs ∈ F.image sm,
            ((cs ×ˢ Uc F cs).image (fun ab : Fin n × Fin n => s(ab.1, ab.2))).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ cs ∈ F.image sm,
            ((cntSet gs (LLc F cs)).card + (F.filter (fun p => sm p = cs)).card) :=
          Finset.sum_le_sum hC
      _ = (∑ cs ∈ F.image sm, (cntSet gs (LLc F cs)).card) +
            ∑ cs ∈ F.image sm, (F.filter (fun p => sm p = cs)).card :=
          Finset.sum_add_distrib
      _ ≤ gs.length + F.card := by rw [hB]; exact Nat.add_le_add_right hA _
  · refine ⟨F.biUnion sm, ?_, ?_⟩
    · intro u v huv
      obtain ⟨p, hp, hc⟩ := hcov u v huv
      rcases (hsl p hp).2.2 u v hc with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact Or.inl (Finset.mem_biUnion.mpr ⟨p, hp, h1⟩)
      · exact Or.inr (Finset.mem_biUnion.mpr ⟨p, hp, h1⟩)
    · have h1 : (F.biUnion sm).card ≤ ∑ p ∈ F, (sm p).card := Finset.card_biUnion_le
      have h2 : ∑ p ∈ F, (sm p).card = ∑ _p ∈ F, 1 :=
        Finset.sum_congr rfl (fun p hp => (hsl p hp).1)
      have h3 : ∑ _p ∈ F, 1 = F.card := by simp
      omega

-- the upper bound: chains

def Cmp (n : ℕ) (gs : List Gate) (w : ℕ) (s : Finset (Fin n)) : Prop :=
  w < n + gs.length ∧ ∀ x : Fin n → Bool, (wv gs x w = true ↔ ∃ i ∈ s, x i = true)

lemma cmp_input {n : ℕ} (gs : List Gate) (i : Fin n) : Cmp n gs i.val {i} := by
  refine ⟨by have := i.isLt; omega, fun x => ?_⟩
  rw [wv_input]
  simp

lemma cmp_append {n : ℕ} {gs : List Gate} {w : ℕ} {s : Finset (Fin n)} (h : Cmp n gs w s)
    (ext : List Gate) : Cmp n (gs ++ ext) w s := by
  refine ⟨by rw [List.length_append]; have := h.1; omega, fun x => ?_⟩
  rw [wv_append_lt gs ext x w h.1]
  exact h.2 x

lemma cmp_or {n : ℕ} {gs : List Gate} {a b : ℕ} {sa sb : Finset (Fin n)}
    (ha : Cmp n gs a sa) (hb : Cmp n gs b sb) :
    Cmp n (gs ++ [(⟨GateOp.or, [a, b]⟩ : Gate)]) (n + gs.length) (sa ∪ sb) := by
  refine ⟨by simp, fun x => ?_⟩
  rw [wv_snoc_last gs a b x GateOp.or rfl, Bool.or_eq_true, ha.2 x, hb.2 x]
  constructor
  · rintro (⟨i, hi, hx⟩ | ⟨i, hi, hx⟩)
    · exact ⟨i, Finset.mem_union_left _ hi, hx⟩
    · exact ⟨i, Finset.mem_union_right _ hi, hx⟩
  · rintro ⟨i, hi, hx⟩
    rcases Finset.mem_union.mp hi with h | h
    · exact Or.inl ⟨i, h, hx⟩
    · exact Or.inr ⟨i, h, hx⟩

lemma chain {n : ℕ} (s : Finset (Fin n)) : s.Nonempty → ∀ gs : List Gate, OrC n gs →
    ∃ ext : List Gate, OrC n (gs ++ ext) ∧ ext.length + 1 = s.card ∧
      ∃ w, Cmp n (gs ++ ext) w s := by
  induction s using Finset.induction_on with
  | empty =>
    intro h
    exact absurd h (by simp)
  | insert a s ha ih =>
    intro _ gs hgs
    by_cases hs : s.Nonempty
    · obtain ⟨ext, hor, hlen, w, hw⟩ := ih hs gs hgs
      refine ⟨ext ++ [(⟨GateOp.or, [w, a.val]⟩ : Gate)], ?_, ?_, n + (gs ++ ext).length, ?_⟩
      · rw [← List.append_assoc]
        exact orC_snoc hor w a.val hw.1 (by have := a.isLt; omega)
      · rw [Finset.card_insert_of_notMem ha, List.length_append, List.length_singleton]
        omega
      · rw [← List.append_assoc]
        have h1 := cmp_or hw (cmp_input (gs ++ ext) a)
        rw [Finset.union_comm, ← Finset.insert_eq] at h1
        exact h1
    · rw [Finset.not_nonempty_iff_eq_empty] at hs
      subst hs
      refine ⟨[], ?_, ?_, a.val, ?_⟩
      · rw [List.append_nil]; exact hgs
      · simp
      · rw [List.append_nil]
        have h1 := cmp_input gs a
        simpa using h1

lemma family {n : ℕ} (L : Fin n → Finset (Fin n)) (I : Finset (Fin n)) :
    (∀ c ∈ I, (L c).Nonempty) →
    ∃ gs : List Gate, OrC n gs ∧ (∀ c ∈ I, ∃ w, Cmp n gs w (L c)) ∧
      gs.length + I.card = ∑ c ∈ I, (L c).card := by
  induction I using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨[], orC_nil n, by simp, by simp⟩
  | insert c I hc ih =>
    intro hne
    obtain ⟨gs, hor, hall, hlen⟩ := ih (fun c2 hc2 => hne c2 (Finset.mem_insert_of_mem hc2))
    obtain ⟨ext, hor2, hlen2, w, hw⟩ :=
      chain (L c) (hne c (Finset.mem_insert_self _ _)) gs hor
    refine ⟨gs ++ ext, hor2, ?_, ?_⟩
    · intro c2 hc2
      rcases Finset.mem_insert.mp hc2 with h | h
      · rw [h]; exact ⟨w, hw⟩
      · obtain ⟨w2, hw2⟩ := hall c2 h
        exact ⟨w2, cmp_append hw2 ext⟩
    · rw [Finset.sum_insert hc, Finset.card_insert_of_notMem hc, List.length_append]
      omega

lemma upper {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S : Finset (Fin n))
    (hS : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S) :
    HasSharedBlockCost G (G.edgeFinset.card + S.card - 1) := by
  classical
  obtain ⟨L, hL⟩ : ∃ L : Fin n → Finset (Fin n),
      ∀ c v, v ∈ L c ↔ (G.Adj c v ∧ (v ∉ S ∨ c < v)) :=
    ⟨fun c => Finset.univ.filter (fun v => G.Adj c v ∧ (v ∉ S ∨ c < v)), fun c v => by simp⟩
  obtain ⟨S2, hS2⟩ : ∃ S2 : Finset (Fin n), ∀ c, c ∈ S2 ↔ (c ∈ S ∧ (L c).Nonempty) :=
    ⟨S.filter (fun c => (L c).Nonempty), fun c => by simp⟩
  obtain ⟨gs, hor, hall, hlen⟩ := family L S2 (fun c hc => ((hS2 c).mp hc).2)
  have hsub : S2 ⊆ S := fun c hc => ((hS2 c).mp hc).1
  have hcardS : S2.card ≤ S.card := Finset.card_le_card hsub
  have hsum : ∑ c ∈ S2, (L c).card ≤ G.edgeFinset.card := by
    have e : ∑ c ∈ S2, (L c).card = (S2.sigma L).card := (Finset.card_sigma _ _).symm
    rw [e]
    apply Finset.card_le_card_of_injOn (fun cv => s(cv.1, cv.2))
    · intro cv hcv
      have h : cv.1 ∈ S2 ∧ cv.2 ∈ L cv.1 := by simpa using hcv
      have h2 : G.Adj cv.1 cv.2 := ((hL cv.1 cv.2).mp h.2).1
      simpa using h2
    · intro cv hcv cv2 hcv2 heq
      obtain ⟨c, v⟩ := cv
      obtain ⟨c2, v2⟩ := cv2
      have h1 : c ∈ S2 ∧ v ∈ L c := by simpa using hcv
      have h2 : c2 ∈ S2 ∧ v2 ∈ L c2 := by simpa using hcv2
      have heq2 : s(c, v) = s(c2, v2) := heq
      rcases Sym2.eq_iff.mp heq2 with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · subst e1
        subst e2
        rfl
      · exfalso
        have a1 := (hL c v).mp h1.2
        have a2 := (hL c2 v2).mp h2.2
        have hcS : c ∈ S := hsub h1.1
        have hc2S : c2 ∈ S := hsub h2.1
        rcases a1.2 with h | h
        · exact h (by rw [e2]; exact hc2S)
        · rcases a2.2 with h3 | h3
          · exact h3 (by rw [← e1]; exact hcS)
          · rw [← e1, ← e2] at h3
            exact lt_asymm h h3
  obtain ⟨F, hFm, hFc⟩ : ∃ F : Finset (Block n),
      (∀ p : Block n, p ∈ F ↔ ∃ c ∈ S2, (({c}, L c) : Block n) = p) ∧ F.card ≤ S2.card :=
    ⟨S2.image (fun c => (({c}, L c) : Block n)), fun p => Finset.mem_image, Finset.card_image_le⟩
  refine ⟨F, ⟨?_, ?_⟩, gs.length, ⟨⟨gs, 0⟩, ⟨hor, ?_⟩, le_rfl⟩, ?_⟩
  · intro p hp
    obtain ⟨c, hc, hcp⟩ := (hFm p).mp hp
    rw [← hcp]
    refine ⟨?_, Finset.singleton_nonempty c, ((hS2 c).mp hc).2, ?_⟩
    · show Disjoint ({c} : Finset (Fin n)) (L c)
      exact Finset.disjoint_singleton_left.mpr (fun h => G.irrefl ((hL c c).mp h).1)
    · intro a ha b hb
      have ha2 : a = c := Finset.mem_singleton.mp ha
      rw [ha2]
      exact ((hL c b).mp hb).1
  · intro u v huv
    have hne : u ≠ v := G.ne_of_adj huv
    have key : ∀ a b : Fin n, G.Adj a b → a ∈ S → (b ∉ S ∨ a < b) →
        ∃ p ∈ F, a ∈ p.1 ∧ b ∈ p.2 := by
      intro a b hab ha hb
      have hbL : b ∈ L a := (hL a b).mpr ⟨hab, hb⟩
      exact ⟨({a}, L a), (hFm _).mpr ⟨a, (hS2 a).mpr ⟨ha, ⟨b, hbL⟩⟩, rfl⟩,
        Finset.mem_singleton_self a, hbL⟩
    by_cases hu : u ∈ S
    · by_cases hv : v ∈ S
      · rcases lt_or_gt_of_ne hne with h | h
        · obtain ⟨p, hp, h1, h2⟩ := key u v huv hu (Or.inr h)
          exact ⟨p, hp, Or.inl ⟨h1, h2⟩⟩
        · obtain ⟨p, hp, h1, h2⟩ := key v u huv.symm hv (Or.inr h)
          exact ⟨p, hp, Or.inr ⟨h1, h2⟩⟩
      · obtain ⟨p, hp, h1, h2⟩ := key u v huv hu (Or.inl hv)
        exact ⟨p, hp, Or.inl ⟨h1, h2⟩⟩
    · have hv : v ∈ S := (hS u v huv).resolve_left hu
      obtain ⟨p, hp, h1, h2⟩ := key v u huv.symm hv (Or.inl hu)
      exact ⟨p, hp, Or.inr ⟨h1, h2⟩⟩
  · intro s hs
    have hs2 : s ∈ F.image Prod.fst ∪ F.image Prod.snd := hs
    rcases Finset.mem_union.mp hs2 with h | h
    · obtain ⟨p, hp, hps⟩ := Finset.mem_image.mp h
      obtain ⟨c, hc, hcp⟩ := (hFm p).mp hp
      rw [← hps, ← hcp]
      exact ⟨c.val, (cmp_input gs c).1, cmp_input gs c⟩
    · obtain ⟨p, hp, hps⟩ := Finset.mem_image.mp h
      obtain ⟨c, hc, hcp⟩ := (hFm p).mp hp
      rw [← hps, ← hcp]
      obtain ⟨w, hw⟩ := hall c hc
      exact ⟨w, hw.1, hw⟩
  · have h0 : S2.card = 0 → ∑ c ∈ S2, (L c).card = 0 := by
      intro h
      rw [Finset.card_eq_zero.mp h]
      simp
    omega

theorem main_aux : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (t : ℕ), 0 < n → PEqualNP.TopForm.NoFourCycle G → (∀ v : Fin n, ∃ u : Fin n, G.Adj v u) → (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) → (∀ S2 : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S2 → t ≤ S2.card) → PEqualNP.SharedBlockCost.sbc G + 1 = G.edgeFinset.card + t := by
  intro n G _ t hn h4 hiso hex hmin
  obtain ⟨S, hS, hSt⟩ := hex
  obtain ⟨u0, hu0⟩ := hiso ⟨0, hn⟩
  have hEpos : 0 < G.edgeFinset.card :=
    Finset.card_pos.mpr ⟨s((⟨0, hn⟩ : Fin n), u0), by simpa using hu0⟩
  have hup : HasSharedBlockCost G (G.edgeFinset.card + t - 1) := by
    rw [← hSt]
    exact upper G S hS
  have hle : sbc G ≤ G.edgeFinset.card + t - 1 := Nat.sInf_le hup
  have hmem : HasSharedBlockCost G (sbc G) :=
    Nat.sInf_mem (⟨_, hup⟩ : {c : ℕ | HasSharedBlockCost G c}.Nonempty)
  obtain ⟨F, hF, k, ⟨C, ⟨hor, hfor⟩, hlenC⟩, hcost⟩ := hmem
  have hw : ∀ s ∈ sides F, ∃ w, w < n + C.gates.length ∧ (T C.gates w : Finset (Fin n)) = s := by
    intro s hs
    obtain ⟨w, hw, hc⟩ := hfor s hs
    refine ⟨w, hw, ?_⟩
    ext i
    rw [mem_T]
    have h1 : wv C.gates (ind i) w = true ↔ ∃ i2 ∈ s, ind i i2 = true := hc.2 (ind i)
    constructor
    · intro h
      obtain ⟨i2, hi2, hx⟩ := h1.mp h
      have h2 : i2 = i := by simpa [ind] using hx
      rw [← h2]
      exact hi2
    · intro h
      exact h1.mpr ⟨i, h, by simp [ind]⟩
  obtain ⟨hE, X, hX, hXc⟩ := lower G h4 F hF C.gates hor hw
  have hFpos : 0 < F.card := by
    obtain ⟨p, hp, _⟩ := hF.2 _ _ hu0
    exact Finset.card_pos.mpr ⟨p, hp⟩
  have ht := hmin X hX
  omega

end PEqualNP.Outside.L_meta_2501

theorem PEqualNP.Outside.L_meta_2501 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (t : ℕ), 0 < n → PEqualNP.TopForm.NoFourCycle G → (∀ v : Fin n, ∃ u : Fin n, G.Adj v u) → (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) → (∀ S2 : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S2 → t ≤ S2.card) → PEqualNP.SharedBlockCost.sbc G + 1 = G.edgeFinset.card + t :=
  PEqualNP.Outside.L_meta_2501.main_aux
