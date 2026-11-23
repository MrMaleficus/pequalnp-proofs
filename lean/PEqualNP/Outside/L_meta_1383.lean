import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1383

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

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

lemma W_append_lt {n : ℕ} (gs ext : List Gate) (x : Fin n → Bool) (t : ℕ)
    (ht : t < n + gs.length) : (W (gs ++ ext) x).getD t false = (W gs x).getD t false := by
  have h : W (gs ++ ext) x = ext.foldl step (W gs x) := by simp [W, List.foldl_append]
  rw [h]
  exact fold_lt ext _ t (by rw [W_len]; exact ht)

def dstep (d : List ℕ) (g : Gate) : List ℕ := d ++ [g.lineDegree d]

lemma dstep_len (d : List ℕ) (g : Gate) : (dstep d g).length = d.length + 1 := by
  simp [dstep]

lemma dstep_lt (d : List ℕ) (g : Gate) (i : ℕ) (hi : i < d.length) :
    (dstep d g).getD i 0 = d.getD i 0 := by
  simp [dstep, List.getD, List.getElem?_append_left hi]

lemma dstep_last (d : List ℕ) (g : Gate) (k : ℕ) (hk : k = d.length) :
    (dstep d g).getD k 0 = g.lineDegree d := by
  subst hk
  simp [dstep, List.getD]

def Dg (n : ℕ) (marked : Finset ℕ) (gs : List Gate) : List ℕ :=
  gs.foldl dstep ((List.range n).map fun i => if i ∈ marked then 1 else 0)

lemma dfold_len (gs : List Gate) :
    ∀ d : List ℕ, (gs.foldl dstep d).length = d.length + gs.length := by
  induction gs with
  | nil => intro d; simp
  | cons g gs ih =>
    intro d
    rw [List.foldl_cons, ih, dstep_len, List.length_cons]
    omega

lemma dfold_lt (gs : List Gate) :
    ∀ (d : List ℕ) (i : ℕ), i < d.length → (gs.foldl dstep d).getD i 0 = d.getD i 0 := by
  induction gs with
  | nil => intro d i _; rfl
  | cons g gs ih =>
    intro d i hi
    rw [List.foldl_cons, ih _ i (by rw [dstep_len]; omega)]
    exact dstep_lt d g i hi

lemma Dg_len (n : ℕ) (marked : Finset ℕ) (gs : List Gate) :
    (Dg n marked gs).length = n + gs.length := by
  rw [Dg, dfold_len]
  simp

lemma Dg_snoc (n : ℕ) (marked : Finset ℕ) (gs : List Gate) (g : Gate) :
    Dg n marked (gs ++ [g]) = dstep (Dg n marked gs) g := by
  simp [Dg, List.foldl_append]

lemma Dg_append_lt (n : ℕ) (marked : Finset ℕ) (gs ext : List Gate) (t : ℕ)
    (ht : t < n + gs.length) :
    (Dg n marked (gs ++ ext)).getD t 0 = (Dg n marked gs).getD t 0 := by
  have h : Dg n marked (gs ++ ext) = ext.foldl dstep (Dg n marked gs) := by
    simp [Dg, List.foldl_append]
  rw [h]
  exact dfold_lt ext _ t (by rw [Dg_len]; exact ht)

def vl {n : ℕ} (P : List Gate) (t : ℕ) (z : Fin n → Bool) : Bool := (W P z).getD t false

def dg (n : ℕ) (M : Finset ℕ) (P : List Gate) (t : ℕ) : ℕ := (Dg n M P).getD t 0

lemma vl_ext {n : ℕ} (P ext : List Gate) (t : ℕ) (z : Fin n → Bool) (ht : t < n + P.length) :
    vl (P ++ ext) t z = vl P t z :=
  W_append_lt P ext z t ht

lemma dg_ext (n : ℕ) (M : Finset ℕ) (P ext : List Gate) (t : ℕ) (ht : t < n + P.length) :
    dg n M (P ++ ext) t = dg n M P t :=
  Dg_append_lt n M P ext t ht

lemma vl_oob {n : ℕ} (P : List Gate) (t : ℕ) (z : Fin n → Bool) (ht : n + P.length ≤ t) :
    vl P t z = false :=
  List.getD_eq_default _ _ (by rw [W_len]; exact ht)

lemma dg_oob (n : ℕ) (M : Finset ℕ) (P : List Gate) (t : ℕ) (ht : n + P.length ≤ t) :
    dg n M P t = 0 :=
  List.getD_eq_default _ _ (by rw [Dg_len]; exact ht)

lemma vl_new {n : ℕ} (P : List Gate) (g : Gate) (z : Fin n → Bool) :
    vl (P ++ [g]) (n + P.length) z = g.op.eval (g.inputs.map fun i => vl P i z) := by
  show (W (P ++ [g]) z).getD (n + P.length) false = _
  rw [W_snoc, step_last _ _ _ (by rw [W_len])]
  rfl

lemma dg_new (n : ℕ) (M : Finset ℕ) (P : List Gate) (g : Gate) :
    dg n M (P ++ [g]) (n + P.length) = g.lineDegree (Dg n M P) := by
  show (Dg n M (P ++ [g])).getD (n + P.length) 0 = _
  rw [Dg_snoc, dstep_last _ _ _ (by rw [Dg_len])]

lemma vl_and {n : ℕ} (P : List Gate) (a b : ℕ) (z : Fin n → Bool) :
    vl (P ++ [⟨GateOp.and, [a, b]⟩]) (n + P.length) z = (vl P a z && vl P b z) := by
  rw [vl_new]
  simp [GateOp.eval]

lemma vl_or {n : ℕ} (P : List Gate) (a b : ℕ) (z : Fin n → Bool) :
    vl (P ++ [⟨GateOp.or, [a, b]⟩]) (n + P.length) z = (vl P a z || vl P b z) := by
  rw [vl_new]
  simp [GateOp.eval]

lemma dg_and (n : ℕ) (M : Finset ℕ) (P : List Gate) (a b : ℕ) :
    dg n M (P ++ [⟨GateOp.and, [a, b]⟩]) (n + P.length) = dg n M P a + dg n M P b := by
  rw [dg_new]
  unfold Gate.lineDegree
  rw [if_pos rfl]
  show (Dg n M P).getD a 0 + ((Dg n M P).getD b 0 + 0) = _
  rfl

lemma dg_or (n : ℕ) (M : Finset ℕ) (P : List Gate) (a b : ℕ) :
    dg n M (P ++ [⟨GateOp.or, [a, b]⟩]) (n + P.length) = max (dg n M P a) (dg n M P b) := by
  rw [dg_new]
  unfold Gate.lineDegree
  rw [if_neg (fun e => GateOp.noConfusion e)]
  show max ((Dg n M P).getD a 0) (max ((Dg n M P).getD b 0) 0) = _
  rw [Nat.max_zero]
  rfl

lemma dg_input (n : ℕ) (M : Finset ℕ) (gs : List Gate) (t : ℕ) (ht : t < n) :
    dg n M gs t ≤ 1 := by
  have e : dg n M ([] ++ gs) t = dg n M [] t := dg_ext n M [] gs t (by simpa using ht)
  rw [List.nil_append] at e
  rw [e]
  show ((List.range n).map fun i => if i ∈ M then 1 else 0).getD t 0 ≤ 1
  rw [List.getD_eq_getElem _ _ (by simpa using ht)]
  simp only [List.getElem_map, List.getElem_range]
  split_ifs <;> omega

lemma any_true (l : List ℕ) (f : ℕ → Bool) :
    (l.map f).any id = true ↔ ∃ i ∈ l, f i = true := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

lemma le_foldr_max (l : List ℕ) (f : ℕ → ℕ) (i : ℕ) (hi : i ∈ l) :
    f i ≤ (l.map f).foldr max 0 := by
  induction l with
  | nil => simp at hi
  | cons a l ih =>
    rw [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.mp hi with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

lemma gate_val {n : ℕ} (pre post : List Gate) (g : Gate) (z : Fin n → Bool) :
    vl (pre ++ g :: post) (n + pre.length) z = g.op.eval (g.inputs.map fun i => vl pre i z) := by
  have e : pre ++ g :: post = (pre ++ [g]) ++ post := by simp
  rw [e, vl_ext (pre ++ [g]) post (n + pre.length) z
    (by rw [List.length_append, List.length_singleton]; omega), vl_new]

lemma gate_deg (n : ℕ) (M : Finset ℕ) (pre post : List Gate) (g : Gate) :
    dg n M (pre ++ g :: post) (n + pre.length) = g.lineDegree (Dg n M pre) := by
  have e : pre ++ g :: post = (pre ++ [g]) ++ post := by simp
  rw [e, dg_ext n M (pre ++ [g]) post (n + pre.length)
    (by rw [List.length_append, List.length_singleton]; omega), dg_new]

lemma pre_val {n : ℕ} (pre rest : List Gate) (i : ℕ) (z : Fin n → Bool) :
    vl pre i z = true ↔ (i < n + pre.length ∧ vl (pre ++ rest) i z = true) := by
  by_cases hi : i < n + pre.length
  · rw [vl_ext pre rest i z hi]
    exact ⟨fun h => ⟨hi, h⟩, fun h => h.2⟩
  · rw [vl_oob pre i z (by omega)]
    exact ⟨fun h => (Bool.false_ne_true h).elim, fun h => absurd h.1 hi⟩

lemma or_sh1 (A B C D : Prop) : ((A ∨ B ∨ C) ∨ D) ↔ ((A ∨ D) ∨ B ∨ C) := by tauto

lemma or_sh2 (A B C D : Prop) : ((A ∨ B ∨ C) ∨ D) ↔ (A ∨ (B ∨ D) ∨ C) := by tauto

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

lemma ok_and (a b : ℕ) : Ok ⟨GateOp.and, [a, b]⟩ := ⟨Or.inl rfl, by simp⟩

lemma ok_or (a b : ℕ) : Ok ⟨GateOp.or, [a, b]⟩ := ⟨Or.inr rfl, by simp⟩

def Good (n : ℕ) (M : Finset ℕ) (gs : List Gate) (k : ℕ) (P : List Gate)
    (obs prs : List (ℕ × ℕ)) (R U : ℕ) (φ : (Fin n → Bool) → Prop) : Prop :=
  (∃ ext, P = gs ++ ext) ∧
  (∀ g ∈ P, Ok g) ∧
  (∀ o ∈ obs, o.1 < n + P.length ∧ dg n M P o.1 ≤ 1 ∧ dg n M P o.1 + dg n M gs o.2 ≤ 4 ∧
    3 ≤ dg n M gs o.2 ∧ o.2 < n + k) ∧
  (∀ p ∈ prs, p.1 < n + P.length ∧ p.2 < n + P.length ∧ dg n M P p.1 ≤ 2 ∧ dg n M P p.2 ≤ 2) ∧
  prs.length ≤ P.length ∧
  (R < n + P.length ∧ dg n M P R ≤ 3) ∧
  (U < n + P.length ∧ dg n M P U ≤ 4 ∧
    ∀ z : Fin n → Bool, vl P U z = true ↔ ∃ p ∈ prs, vl P p.1 z = true ∧ vl P p.2 z = true) ∧
  ∀ z : Fin n → Bool, φ z ↔ (vl P R z = true ∨ vl P U z = true ∨
    ∃ o ∈ obs, vl P o.1 z = true ∧ vl gs o.2 z = true)

lemma good_congr {n : ℕ} {M : Finset ℕ} {gs P : List Gate} {obs prs : List (ℕ × ℕ)} {k R U : ℕ}
    {φ φ' : (Fin n → Bool) → Prop} (h : Good n M gs k P obs prs R U φ)
    (he : ∀ z, φ' z ↔ φ z) : Good n M gs k P obs prs R U φ' := by
  unfold Good at h ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, fun z => (he z).trans (h8 z)⟩

lemma good_base {n : ℕ} {M : Finset ℕ} {gs P : List Gate} {obs prs : List (ℕ × ℕ)} {k R U : ℕ}
    {φ : (Fin n → Bool) → Prop} (h : Good n M gs k P obs prs R U φ) (t : ℕ)
    (ht : t < n + gs.length) :
    t < n + P.length ∧ dg n M P t = dg n M gs t ∧ ∀ z : Fin n → Bool, vl P t z = vl gs t z := by
  unfold Good at h
  obtain ⟨⟨e0, rfl⟩, -⟩ := h
  exact ⟨by rw [List.length_append]; omega, dg_ext n M gs e0 t ht, fun z => vl_ext gs e0 t z ht⟩

lemma good_ext {n : ℕ} {M : Finset ℕ} {gs P : List Gate} {obs prs : List (ℕ × ℕ)} {k R U : ℕ}
    {φ : (Fin n → Bool) → Prop} (h : Good n M gs k P obs prs R U φ) (ext : List Gate)
    (hok : ∀ g ∈ ext, Ok g) : Good n M gs k (P ++ ext) obs prs R U φ := by
  unfold Good at h ⊢
  obtain ⟨⟨e0, he0⟩, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have hl : (P ++ ext).length = P.length + ext.length := List.length_append
  have V : ∀ t, t < n + P.length → ∀ z : Fin n → Bool, vl (P ++ ext) t z = vl P t z :=
    fun t ht z => vl_ext P ext t z ht
  have Dd : ∀ t, t < n + P.length → dg n M (P ++ ext) t = dg n M P t :=
    fun t ht => dg_ext n M P ext t ht
  refine ⟨⟨e0 ++ ext, by rw [he0, List.append_assoc]⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact h2 g hg
    · exact hok g hg
  · intro o ho
    obtain ⟨a1, a2, a3, a4, a5⟩ := h3 o ho
    rw [Dd _ a1]
    exact ⟨by omega, a2, a3, a4, a5⟩
  · intro p hp
    obtain ⟨a1, a2, a3, a4⟩ := h4 p hp
    rw [Dd _ a1, Dd _ a2]
    exact ⟨by omega, by omega, a3, a4⟩
  · omega
  · rw [Dd _ h6.1]
    exact ⟨by omega, h6.2⟩
  · obtain ⟨a1, a2, a3⟩ := h7
    rw [Dd _ a1]
    refine ⟨by omega, a2, fun z => ?_⟩
    rw [V _ a1, a3 z]
    constructor
    · rintro ⟨p, hp, b1, b2⟩
      exact ⟨p, hp, by rw [V _ (h4 p hp).1]; exact b1, by rw [V _ (h4 p hp).2.1]; exact b2⟩
    · rintro ⟨p, hp, b1, b2⟩
      rw [V _ (h4 p hp).1] at b1
      rw [V _ (h4 p hp).2.1] at b2
      exact ⟨p, hp, b1, b2⟩
  · intro z
    rw [h8 z, V _ h6.1, V _ h7.1]
    constructor
    · rintro (a | a | ⟨o, ho, b1, b2⟩)
      · exact Or.inl a
      · exact Or.inr (Or.inl a)
      · exact Or.inr (Or.inr ⟨o, ho, by rw [V _ (h3 o ho).1]; exact b1, b2⟩)
    · rintro (a | a | ⟨o, ho, b1, b2⟩)
      · exact Or.inl a
      · exact Or.inr (Or.inl a)
      · rw [V _ (h3 o ho).1] at b1
        exact Or.inr (Or.inr ⟨o, ho, b1, b2⟩)

lemma good_setR {n : ℕ} {M : Finset ℕ} {gs P : List Gate} {obs prs : List (ℕ × ℕ)} {k R U : ℕ}
    {φ : (Fin n → Bool) → Prop} (h : Good n M gs k P obs prs R U φ) (R' : ℕ)
    (ψ : (Fin n → Bool) → Bool) (hR : R' < n + P.length) (hd : dg n M P R' ≤ 3)
    (hv : ∀ z, vl P R' z = (vl P R z || ψ z)) :
    Good n M gs k P obs prs R' U (fun z => φ z ∨ ψ z = true) := by
  unfold Good at h ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨h1, h2, h3, h4, h5, ⟨hR, hd⟩, h7, fun z => ?_⟩
  show (φ z ∨ ψ z = true) ↔ _
  rw [h8 z, hv z, Bool.or_eq_true]
  exact or_sh1 _ _ _ _

lemma good_addpair {n : ℕ} {M : Finset ℕ} {gs P : List Gate} {obs prs : List (ℕ × ℕ)}
    {k R U : ℕ} {φ : (Fin n → Bool) → Prop} (h : Good n M gs k P obs prs R U φ) (U' a b : ℕ)
    (hU : U' < n + P.length) (hd : dg n M P U' ≤ 4) (ha : a < n + P.length)
    (hb : b < n + P.length) (hda : dg n M P a ≤ 2) (hdb : dg n M P b ≤ 2)
    (hlen : prs.length + 1 ≤ P.length)
    (hv : ∀ z : Fin n → Bool, vl P U' z = (vl P U z || (vl P a z && vl P b z))) :
    Good n M gs k P obs ((a, b) :: prs) R U'
      (fun z => φ z ∨ (vl P a z = true ∧ vl P b z = true)) := by
  unfold Good at h ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨h1, h2, h3, ?_, by rw [List.length_cons]; exact hlen, h6, ⟨hU, hd, fun z => ?_⟩,
    fun z => ?_⟩
  · intro p hp
    rcases List.mem_cons.mp hp with hp | hp
    · rw [hp]
      exact ⟨ha, hb, hda, hdb⟩
    · exact h4 p hp
  · rw [hv z, Bool.or_eq_true, Bool.and_eq_true, h7.2.2 z]
    constructor
    · rintro (⟨p, hp, c⟩ | c)
      · exact ⟨p, List.mem_cons_of_mem _ hp, c⟩
      · exact ⟨(a, b), List.mem_cons.mpr (Or.inl rfl), c⟩
    · rintro ⟨p, hp, c⟩
      rcases List.mem_cons.mp hp with hp | hp
      · rw [hp] at c
        exact Or.inr c
      · exact Or.inl ⟨p, hp, c⟩
  · show (φ z ∨ (vl P a z = true ∧ vl P b z = true)) ↔ _
    rw [h8 z, hv z, Bool.or_eq_true, Bool.and_eq_true]
    exact or_sh2 _ _ _ _

lemma good_addob {n : ℕ} {M : Finset ℕ} {gs P : List Gate} {obs prs : List (ℕ × ℕ)}
    {k R U : ℕ} {φ : (Fin n → Bool) → Prop} (h : Good n M gs k P obs prs R U φ) (c w : ℕ)
    (hc : c < n + P.length) (hd1 : dg n M P c ≤ 1) (hd4 : dg n M P c + dg n M gs w ≤ 4)
    (h3w : 3 ≤ dg n M gs w) (hw : w < n + k) :
    Good n M gs k P ((c, w) :: obs) prs R U
      (fun z => φ z ∨ (vl P c z = true ∧ vl gs w z = true)) := by
  unfold Good at h ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨h1, h2, ?_, h4, h5, h6, h7, fun z => ?_⟩
  · intro o ho
    rcases List.mem_cons.mp ho with ho | ho
    · rw [ho]
      exact ⟨hc, hd1, hd4, h3w, hw⟩
    · exact h3 o ho
  · show (φ z ∨ (vl P c z = true ∧ vl gs w z = true)) ↔ _
    rw [h8 z]
    constructor
    · rintro ((a | a | ⟨o, ho, b⟩) | b)
      · exact Or.inl a
      · exact Or.inr (Or.inl a)
      · exact Or.inr (Or.inr ⟨o, List.mem_cons_of_mem _ ho, b⟩)
      · exact Or.inr (Or.inr ⟨(c, w), List.mem_cons.mpr (Or.inl rfl), b⟩)
    · rintro (a | a | ⟨o, ho, b⟩)
      · exact Or.inl (Or.inl a)
      · exact Or.inl (Or.inr (Or.inl a))
      · rcases List.mem_cons.mp ho with ho | ho
        · rw [ho] at b
          exact Or.inr b
        · exact Or.inl (Or.inr (Or.inr ⟨o, ho, b⟩))

lemma good_restrict {n : ℕ} {M : Finset ℕ} {gs P : List Gate} {obs prs : List (ℕ × ℕ)}
    {k R U : ℕ} {φ : (Fin n → Bool) → Prop} (h : Good n M gs (k + 1) P obs prs R U φ)
    (obs0 : List (ℕ × ℕ)) (hmem : ∀ o, o ∈ obs0 ↔ (o ∈ obs ∧ o.2 ≠ n + k)) :
    ∃ φ0 : (Fin n → Bool) → Prop, Good n M gs k P obs0 prs R U φ0 ∧
      ∀ z, φ z ↔ (φ0 z ∨ ((∃ o ∈ obs, o.2 = n + k ∧ vl P o.1 z = true) ∧
        vl gs (n + k) z = true)) := by
  unfold Good at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨fun z => vl P R z = true ∨ vl P U z = true ∨
    ∃ o ∈ obs0, vl P o.1 z = true ∧ vl gs o.2 z = true, ?_, fun z => ?_⟩
  · unfold Good
    refine ⟨h1, h2, ?_, h4, h5, h6, h7, fun z => Iff.rfl⟩
    intro o ho
    obtain ⟨ho1, ho2⟩ := (hmem o).mp ho
    obtain ⟨a1, a2, a3, a4, a5⟩ := h3 o ho1
    exact ⟨a1, a2, a3, a4, by omega⟩
  · show φ z ↔ ((vl P R z = true ∨ vl P U z = true ∨
      ∃ o ∈ obs0, vl P o.1 z = true ∧ vl gs o.2 z = true) ∨ _)
    rw [h8 z]
    constructor
    · rintro (a | a | ⟨o, ho, b1, b2⟩)
      · exact Or.inl (Or.inl a)
      · exact Or.inl (Or.inr (Or.inl a))
      · by_cases e : o.2 = n + k
        · rw [e] at b2
          exact Or.inr ⟨⟨o, ho, e, b1⟩, b2⟩
        · exact Or.inl (Or.inr (Or.inr ⟨o, (hmem o).mpr ⟨ho, e⟩, b1, b2⟩))
    · rintro ((a | a | ⟨o, ho, b1, b2⟩) | ⟨⟨o, ho, e, b1⟩, b2⟩)
      · exact Or.inl a
      · exact Or.inr (Or.inl a)
      · exact Or.inr (Or.inr ⟨o, ((hmem o).mp ho).1, b1, b2⟩)
      · rw [← e] at b2
        exact Or.inr (Or.inr ⟨o, ho, b1, b2⟩)

lemma acc2 {n : ℕ} (M : Finset ℕ) (P : List Gate) (a b t : ℕ) (ht : t < n + P.length) :
    ∃ P' : List Gate, (∃ ext, P' = P ++ ext ∧ ∀ g ∈ ext, Ok g) ∧ P'.length = P.length + 2 ∧
      dg n M P' (n + P.length + 1) = max (dg n M P t) (dg n M P a + dg n M P b) ∧
      ∀ z : Fin n → Bool, vl P' (n + P.length + 1) z = (vl P t z || (vl P a z && vl P b z)) := by
  have l1 : (P ++ [(⟨GateOp.and, [a, b]⟩ : Gate)]).length = P.length + 1 := by
    rw [List.length_append, List.length_singleton]
  have e1 : n + P.length + 1 = n + (P ++ [(⟨GateOp.and, [a, b]⟩ : Gate)]).length := by
    rw [l1]
    omega
  refine ⟨(P ++ [⟨GateOp.and, [a, b]⟩]) ++ [⟨GateOp.or, [t, n + P.length]⟩],
    ⟨[⟨GateOp.and, [a, b]⟩] ++ [⟨GateOp.or, [t, n + P.length]⟩], List.append_assoc _ _ _, ?_⟩,
    ?_, ?_, fun z => ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · rw [List.mem_singleton.mp hg]
      exact ok_and a b
    · rw [List.mem_singleton.mp hg]
      exact ok_or _ _
  · rw [List.length_append, List.length_singleton, l1]
  · rw [e1, dg_or, dg_ext n M P _ t ht, dg_and]
  · rw [e1, vl_or, vl_ext P _ t z ht, vl_and]

lemma term {n : ℕ} {M : Finset ℕ} {gs P : List Gate} {obs prs : List (ℕ × ℕ)} {k R U : ℕ}
    {φ : (Fin n → Bool) → Prop} (h : Good n M gs k P obs prs R U φ) (a b : ℕ)
    (hd : dg n M P a + dg n M P b ≤ 3) :
    ∃ (P' : List Gate) (R' : ℕ),
      Good n M gs k P' obs prs R' U (fun z => φ z ∨ (vl P a z = true ∧ vl P b z = true)) ∧
      (∃ ext, P' = P ++ ext) ∧ P'.length = P.length + 2 := by
  have hR : R < n + P.length ∧ dg n M P R ≤ 3 := by
    unfold Good at h
    exact h.2.2.2.2.2.1
  obtain ⟨P', ⟨ext, rfl, hok⟩, hl, hdn, hvn⟩ := acc2 M P a b R hR.1
  have g1 := good_ext h ext hok
  have g2 := good_setR g1 (n + P.length + 1) (fun z => vl P a z && vl P b z) (by omega)
    (by rw [hdn]; exact max_le hR.2 hd) (fun z => by rw [hvn z, vl_ext P ext R z hR.1])
  exact ⟨P ++ ext, n + P.length + 1,
    good_congr g2 (fun z => by rw [Bool.and_eq_true]), ⟨ext, rfl⟩, hl⟩

lemma pair {n : ℕ} {M : Finset ℕ} {gs P : List Gate} {obs prs : List (ℕ × ℕ)} {k R U : ℕ}
    {φ : (Fin n → Bool) → Prop} (h : Good n M gs k P obs prs R U φ) (a b : ℕ)
    (ha : a < n + P.length) (hb : b < n + P.length) (hda : dg n M P a ≤ 2)
    (hdb : dg n M P b ≤ 2) :
    ∃ (P' : List Gate) (U' : ℕ),
      Good n M gs k P' obs ((a, b) :: prs) R U'
        (fun z => φ z ∨ (vl P a z = true ∧ vl P b z = true)) ∧ P'.length = P.length + 2 := by
  have hU : U < n + P.length ∧ dg n M P U ≤ 4 := by
    unfold Good at h
    exact ⟨h.2.2.2.2.2.2.1.1, h.2.2.2.2.2.2.1.2.1⟩
  have hlen : prs.length ≤ P.length := by
    unfold Good at h
    exact h.2.2.2.2.1
  obtain ⟨P', ⟨ext, rfl, hok⟩, hl, hdn, hvn⟩ := acc2 M P a b U hU.1
  have g1 := good_ext h ext hok
  have g2 := good_addpair g1 (n + P.length + 1) a b (by omega)
    (by rw [hdn]; exact max_le hU.2 (by omega)) (by omega) (by omega)
    (by rw [dg_ext n M P ext a ha]; exact hda) (by rw [dg_ext n M P ext b hb]; exact hdb)
    (by omega)
    (fun z => by rw [hvn z, vl_ext P ext U z hU.1, vl_ext P ext a z ha, vl_ext P ext b z hb])
  exact ⟨P ++ ext, n + P.length + 1,
    good_congr g2 (fun z => by rw [vl_ext P ext a z ha, vl_ext P ext b z hb]), hl⟩

lemma child {n : ℕ} {M : Finset ℕ} {gs P : List Gate} {obs prs : List (ℕ × ℕ)} {k R U : ℕ}
    {φ : (Fin n → Bool) → Prop} (hks : k ≤ gs.length) (h : Good n M gs k P obs prs R U φ)
    (c p : ℕ) (hc : c < n + P.length) (hd1 : dg n M P c ≤ 1)
    (hd4 : p < n + k → dg n M P c + dg n M gs p ≤ 4) :
    ∃ (P' : List Gate) (obs' : List (ℕ × ℕ)) (R' : ℕ),
      Good n M gs k P' obs' prs R' U
        (fun z => φ z ∨ (vl P c z = true ∧ (p < n + k ∧ vl gs p z = true))) ∧
      (∃ ext, P' = P ++ ext) ∧ P'.length + obs'.length ≤ P.length + obs.length + 2 := by
  by_cases hp : p < n + k
  · obtain ⟨bp1, bp2, bp3⟩ := good_base h p (by omega)
    by_cases h3 : dg n M P c + dg n M gs p ≤ 3
    · obtain ⟨P', R', g1, hext, hl⟩ := term h c p (by rw [bp2]; exact h3)
      refine ⟨P', obs, R', good_congr g1 (fun z => ?_), hext, by omega⟩
      rw [bp3 z]
      tauto
    · have g1 := good_addob h c p hc hd1 (hd4 hp) (by have := hd4 hp; omega) hp
      refine ⟨P, (c, p) :: obs, R, good_congr g1 (fun z => ?_),
        ⟨[], (List.append_nil P).symm⟩, by rw [List.length_cons]; omega⟩
      tauto
  · exact ⟨P, obs, R, good_congr h (fun z => by tauto), ⟨[], (List.append_nil P).symm⟩,
      by omega⟩

lemma or_list {n : ℕ} {M : Finset ℕ} {gs : List Gate} {prs : List (ℕ × ℕ)} {k U : ℕ}
    (hks : k ≤ gs.length) (l : List ℕ) :
    ∀ (P : List Gate) (obs : List (ℕ × ℕ)) (R : ℕ) (φ : (Fin n → Bool) → Prop) (c : ℕ),
      Good n M gs k P obs prs R U φ → c < n + P.length → dg n M P c ≤ 1 →
      (∀ p ∈ l, p < n + k → dg n M P c + dg n M gs p ≤ 4) →
      ∃ (P' : List Gate) (obs' : List (ℕ × ℕ)) (R' : ℕ),
        Good n M gs k P' obs' prs R' U
          (fun z => φ z ∨ (vl P c z = true ∧ ∃ p ∈ l, p < n + k ∧ vl gs p z = true)) ∧
        P'.length + obs'.length ≤ P.length + obs.length + 2 * l.length := by
  induction l with
  | nil =>
    intro P obs R φ c h _ _ _
    exact ⟨P, obs, R, good_congr h (fun z => by simp), by simp⟩
  | cons p l ih =>
    intro P obs R φ c h hc hd1 hd4
    obtain ⟨P1, obs1, R1, g1, ⟨e, he⟩, c1⟩ :=
      child hks h c p hc hd1 (hd4 p (List.mem_cons.mpr (Or.inl rfl)))
    have hlen1 : P1.length = P.length + e.length := by rw [he, List.length_append]
    have hdc : dg n M P1 c = dg n M P c := by rw [he]; exact dg_ext n M P e c hc
    obtain ⟨P2, obs2, R2, g2, c2⟩ := ih P1 obs1 R1 _ c g1 (by omega) (by omega)
      (fun q hq hlt => by rw [hdc]; exact hd4 q (List.mem_cons_of_mem _ hq) hlt)
    refine ⟨P2, obs2, R2, good_congr g2 (fun z => ?_), by rw [List.length_cons]; omega⟩
    have hv : vl P1 c z = vl P c z := by rw [he]; exact vl_ext P e c z hc
    rw [hv]
    constructor
    · rintro (a | ⟨hc', q, hq, hQ⟩)
      · exact Or.inl (Or.inl a)
      · rcases List.mem_cons.mp hq with hq | hq
        · rw [hq] at hQ
          exact Or.inl (Or.inr ⟨hc', hQ⟩)
        · exact Or.inr ⟨hc', q, hq, hQ⟩
    · rintro ((a | ⟨hc', hQ⟩) | ⟨hc', q, hq, hQ⟩)
      · exact Or.inl a
      · exact Or.inr ⟨hc', p, List.mem_cons.mpr (Or.inl rfl), hQ⟩
      · exact Or.inr ⟨hc', q, List.mem_cons_of_mem _ hq, hQ⟩

lemma and2 {n : ℕ} {M : Finset ℕ} {gs P : List Gate} {obs prs : List (ℕ × ℕ)} {k R U : ℕ}
    {φ : (Fin n → Bool) → Prop} (hks : k ≤ gs.length) (h : Good n M gs k P obs prs R U φ)
    (c p q : ℕ) (hc : c < n + P.length) (hd1 : dg n M P c ≤ 1) (hp : p < n + k)
    (hq : q < n + k)
    (hA : (dg n M P c + dg n M gs q ≤ 1 ∧ dg n M P c + dg n M gs q + dg n M gs p ≤ 4) ∨
      (dg n M gs p ≤ 2 ∧ dg n M P c + dg n M gs q ≤ 2)) :
    ∃ (P' : List Gate) (obs' prs' : List (ℕ × ℕ)) (R' U' : ℕ),
      Good n M gs k P' obs' prs' R' U'
        (fun z => φ z ∨ (vl P c z = true ∧ vl gs p z = true ∧ vl gs q z = true)) ∧
      P'.length + obs'.length ≤ P.length + obs.length + 3 := by
  obtain ⟨bp1, bp2, bp3⟩ := good_base h p (by omega)
  obtain ⟨bq1, bq2, bq3⟩ := good_base h q (by omega)
  have g1 := good_ext h [⟨GateOp.and, [c, q]⟩]
    (fun g hg => by rw [List.mem_singleton.mp hg]; exact ok_and c q)
  have l1 : (P ++ [(⟨GateOp.and, [c, q]⟩ : Gate)]).length = P.length + 1 := by
    rw [List.length_append, List.length_singleton]
  have dc1 : dg n M (P ++ [⟨GateOp.and, [c, q]⟩]) (n + P.length) =
      dg n M P c + dg n M gs q := by
    rw [dg_and, bq2]
  have vc1 : ∀ z : Fin n → Bool, vl (P ++ [⟨GateOp.and, [c, q]⟩]) (n + P.length) z =
      (vl P c z && vl gs q z) := by
    intro z
    rw [vl_and, bq3 z]
  rcases hA with ⟨A1, A2⟩ | ⟨A1, A2⟩
  · obtain ⟨P', obs', R', g2, -, cost⟩ := child hks g1 (n + P.length) p (by omega) (by omega)
      (fun _ => by omega)
    refine ⟨P', obs', prs, R', U, good_congr g2 (fun z => ?_), by omega⟩
    rw [vc1 z, Bool.and_eq_true]
    tauto
  · obtain ⟨P', U', g2, hl⟩ := pair g1 p (n + P.length) (by omega) (by omega)
      (by rw [dg_ext n M P _ p bp1, bp2]; exact A1) (by omega)
    refine ⟨P', obs, _, R, U', good_congr g2 (fun z => ?_), by omega⟩
    rw [vc1 z, vl_ext P _ p z bp1, bp3 z, Bool.and_eq_true]
    tauto

lemma merge {n : ℕ} (M : Finset ℕ) (w D : ℕ) :
    ∀ (obs : List (ℕ × ℕ)) (P : List Gate) (c : ℕ),
      c < n + P.length → dg n M P c ≤ D →
      (∀ o ∈ obs, o.2 = w → o.1 < n + P.length ∧ dg n M P o.1 ≤ D) →
      ∃ (ext : List Gate) (c' : ℕ) (obs0 : List (ℕ × ℕ)),
        (∀ g ∈ ext, Ok g) ∧ c' < n + (P ++ ext).length ∧ dg n M (P ++ ext) c' ≤ D ∧
        (∀ o, o ∈ obs0 ↔ (o ∈ obs ∧ o.2 ≠ w)) ∧ ext.length + obs0.length ≤ obs.length ∧
        ∀ z : Fin n → Bool, vl (P ++ ext) c' z = true ↔
          (vl P c z = true ∨ ∃ o ∈ obs, o.2 = w ∧ vl P o.1 z = true) := by
  intro obs
  induction obs with
  | nil =>
    intro P c hc hd _
    refine ⟨[], c, [], by simp, by simpa using hc, by simpa using hd, by simp, by simp,
      fun z => by simp⟩
  | cons o rest ih =>
    intro P c hc hd hobs
    by_cases ho : o.2 = w
    · obtain ⟨ho1, ho2⟩ := hobs o (List.mem_cons.mpr (Or.inl rfl)) ho
      have l1 : (P ++ [(⟨GateOp.or, [c, o.1]⟩ : Gate)]).length = P.length + 1 := by
        rw [List.length_append, List.length_singleton]
      obtain ⟨ext, c', obs0, k1, k2, k3, k4, k5, k6⟩ :=
        ih (P ++ [⟨GateOp.or, [c, o.1]⟩]) (n + P.length) (by omega)
          (by rw [dg_or]; exact max_le hd ho2)
          (fun o' ho' e => by
            obtain ⟨a1, a2⟩ := hobs o' (List.mem_cons_of_mem _ ho') e
            exact ⟨by omega, by rw [dg_ext n M P _ o'.1 a1]; exact a2⟩)
      refine ⟨[⟨GateOp.or, [c, o.1]⟩] ++ ext, c', obs0, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro g hg
        rcases List.mem_append.mp hg with hg | hg
        · rw [List.mem_singleton.mp hg]
          exact ok_or _ _
        · exact k1 g hg
      · rw [← List.append_assoc]
        exact k2
      · rw [← List.append_assoc]
        exact k3
      · intro o'
        rw [k4 o']
        constructor
        · rintro ⟨a, b⟩
          exact ⟨List.mem_cons_of_mem _ a, b⟩
        · rintro ⟨a, b⟩
          rcases List.mem_cons.mp a with a | a
          · rw [a] at b
            exact absurd ho b
          · exact ⟨a, b⟩
      · rw [List.length_append, List.length_singleton, List.length_cons]
        omega
      · intro z
        rw [← List.append_assoc, k6 z, vl_or, Bool.or_eq_true]
        constructor
        · rintro ((a | a) | ⟨o', ho', e, b⟩)
          · exact Or.inl a
          · exact Or.inr ⟨o, List.mem_cons.mpr (Or.inl rfl), ho, a⟩
          · rw [vl_ext P _ o'.1 z (hobs o' (List.mem_cons_of_mem _ ho') e).1] at b
            exact Or.inr ⟨o', List.mem_cons_of_mem _ ho', e, b⟩
        · rintro (a | ⟨o', ho', e, b⟩)
          · exact Or.inl (Or.inl a)
          · rcases List.mem_cons.mp ho' with ho' | ho'
            · rw [ho'] at b
              exact Or.inl (Or.inr b)
            · refine Or.inr ⟨o', ho', e, ?_⟩
              rw [vl_ext P _ o'.1 z (hobs o' (List.mem_cons_of_mem _ ho') e).1]
              exact b
    · obtain ⟨ext, c', obs0, k1, k2, k3, k4, k5, k6⟩ :=
        ih P c hc hd (fun o' ho' e => hobs o' (List.mem_cons_of_mem _ ho') e)
      refine ⟨ext, c', o :: obs0, k1, k2, k3, ?_, ?_, ?_⟩
      · intro o'
        rw [List.mem_cons, List.mem_cons, k4 o']
        constructor
        · rintro (a | ⟨a, b⟩)
          · rw [a]
            exact ⟨Or.inl rfl, ho⟩
          · exact ⟨Or.inr a, b⟩
        · rintro ⟨a | a, b⟩
          · exact Or.inl a
          · exact Or.inr ⟨a, b⟩
      · rw [List.length_cons, List.length_cons]
        omega
      · intro z
        rw [k6 z]
        constructor
        · rintro (a | ⟨o', ho', e, b⟩)
          · exact Or.inl a
          · exact Or.inr ⟨o', List.mem_cons_of_mem _ ho', e, b⟩
        · rintro (a | ⟨o', ho', e, b⟩)
          · exact Or.inl a
          · rcases List.mem_cons.mp ho' with ho' | ho'
            · rw [ho'] at e
              exact absurd e ho
            · exact Or.inr ⟨o', ho', e, b⟩

lemma gate_step {n : ℕ} {M : Finset ℕ} {gs P : List Gate} {obs prs : List (ℕ × ℕ)} {R U : ℕ}
    {φ : (Fin n → Bool) → Prop} (pre post : List Gate) (g : Gate)
    (hgs : gs = pre ++ g :: post) (hg : Ok g)
    (h : Good n M gs pre.length P obs prs R U φ) (c : ℕ) (hc : c < n + P.length)
    (hd1 : dg n M P c ≤ 1) (hd4 : dg n M P c + dg n M gs (n + pre.length) ≤ 4)
    (h3 : 3 ≤ dg n M gs (n + pre.length)) :
    ∃ (P' : List Gate) (obs' prs' : List (ℕ × ℕ)) (R' U' : ℕ),
      Good n M gs pre.length P' obs' prs' R' U'
        (fun z => φ z ∨ (vl P c z = true ∧ vl gs (n + pre.length) z = true)) ∧
      P'.length + obs'.length ≤ P.length + obs.length + 4 := by
  have hks : pre.length ≤ gs.length := by
    rw [hgs, List.length_append]
    omega
  have hval : ∀ z : Fin n → Bool, vl gs (n + pre.length) z =
      g.op.eval (g.inputs.map fun i => vl pre i z) := by
    intro z
    rw [hgs]
    exact gate_val pre post g z
  have hdeg : dg n M gs (n + pre.length) = g.lineDegree (Dg n M pre) := by
    rw [hgs]
    exact gate_deg n M pre post g
  have hpv : ∀ (i : ℕ) (z : Fin n → Bool),
      vl pre i z = true ↔ (i < n + pre.length ∧ vl gs i z = true) := by
    intro i z
    rw [hgs]
    exact pre_val pre (g :: post) i z
  have hpd1 : ∀ i, i < n + pre.length → (Dg n M pre).getD i 0 = dg n M gs i := by
    intro i hi
    rw [hgs]
    exact (dg_ext n M pre (g :: post) i hi).symm
  obtain ⟨op, l⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  have hop' : op = GateOp.and ∨ op = GateOp.or := hop
  have hlen' : l.length ≤ 2 := hlen
  rcases hop' with rfl | rfl
  · have hdeg' : dg n M gs (n + pre.length) =
        (l.map fun i => (Dg n M pre).getD i 0).sum := by
      rw [hdeg]
      unfold Gate.lineDegree
      exact if_pos rfl
    have hval' : ∀ z : Fin n → Bool, vl gs (n + pre.length) z =
        (l.map fun i => vl pre i z).all id := hval
    rcases l with _ | ⟨p, _ | ⟨q, _ | ⟨r, l⟩⟩⟩
    · exfalso
      have h0 : dg n M gs (n + pre.length) = 0 := hdeg'
      omega
    · have hd : dg n M gs (n + pre.length) = (Dg n M pre).getD p 0 := by
        rw [hdeg']
        simp
      obtain ⟨P', obs', R', g', cost⟩ := or_list hks [p] P obs R φ c h hc hd1
        (fun p' hp' hlt => by
          rw [List.mem_singleton.mp hp'] at hlt ⊢
          rw [← hpd1 p hlt, ← hd]
          exact hd4)
      refine ⟨P', obs', prs, R', U, good_congr g' (fun z => ?_), by
        rw [List.length_singleton] at cost; omega⟩
      have key : vl gs (n + pre.length) z = true ↔
          ∃ p' ∈ [p], p' < n + pre.length ∧ vl gs p' z = true := by
        rw [hval' z]
        simp [hpv]
      rw [key]
    · have hd : dg n M gs (n + pre.length) =
          (Dg n M pre).getD p 0 + (Dg n M pre).getD q 0 := by
        rw [hdeg']
        simp
      have key : ∀ z : Fin n → Bool, vl gs (n + pre.length) z = true ↔
          ((p < n + pre.length ∧ vl gs p z = true) ∧
            (q < n + pre.length ∧ vl gs q z = true)) := by
        intro z
        rw [hval' z]
        show ((vl pre p z && (vl pre q z && true)) = true) ↔ _
        rw [Bool.and_true, Bool.and_eq_true, hpv, hpv]
      by_cases hp : p < n + pre.length
      · by_cases hq : q < n + pre.length
        · rw [hpd1 p hp, hpd1 q hq] at hd
          have hA : ((dg n M P c + dg n M gs q ≤ 1 ∧
                dg n M P c + dg n M gs q + dg n M gs p ≤ 4) ∨
              (dg n M gs p ≤ 2 ∧ dg n M P c + dg n M gs q ≤ 2)) ∨
              ((dg n M P c + dg n M gs p ≤ 1 ∧
                dg n M P c + dg n M gs p + dg n M gs q ≤ 4) ∨
              (dg n M gs q ≤ 2 ∧ dg n M P c + dg n M gs p ≤ 2)) := by
            omega
          rcases hA with hA | hA
          · obtain ⟨P', obs', prs', R', U', g', cost⟩ := and2 hks h c p q hc hd1 hp hq hA
            refine ⟨P', obs', prs', R', U', good_congr g' (fun z => ?_), by omega⟩
            rw [key z]
            tauto
          · obtain ⟨P', obs', prs', R', U', g', cost⟩ := and2 hks h c q p hc hd1 hq hp hA
            refine ⟨P', obs', prs', R', U', good_congr g' (fun z => ?_), by omega⟩
            rw [key z]
            tauto
        · refine ⟨P, obs, prs, R, U, good_congr h (fun z => ?_), by omega⟩
          rw [key z]
          tauto
      · refine ⟨P, obs, prs, R, U, good_congr h (fun z => ?_), by omega⟩
        rw [key z]
        tauto
    · exfalso
      simp only [List.length_cons] at hlen'
      omega
  · have hdeg' : dg n M gs (n + pre.length) =
        (l.map fun i => (Dg n M pre).getD i 0).foldr max 0 := by
      rw [hdeg]
      unfold Gate.lineDegree
      exact if_neg (fun e => GateOp.noConfusion e)
    obtain ⟨P', obs', R', g', cost⟩ := or_list hks l P obs R φ c h hc hd1
      (fun p hp hlt => by
        have hle : (Dg n M pre).getD p 0 ≤ (l.map fun i => (Dg n M pre).getD i 0).foldr max 0 :=
          le_foldr_max l (fun i => (Dg n M pre).getD i 0) p hp
        rw [hpd1 p hlt, ← hdeg'] at hle
        omega)
    refine ⟨P', obs', prs, R', U, good_congr g' (fun z => ?_), by omega⟩
    have key : vl gs (n + pre.length) z = true ↔
        ∃ p ∈ l, p < n + pre.length ∧ vl gs p z = true := by
      rw [hval z]
      show (l.map fun i => vl pre i z).any id = true ↔ _
      rw [any_true]
      constructor
      · rintro ⟨i, hi, b⟩
        exact ⟨i, hi, (hpv i z).mp b⟩
      · rintro ⟨i, hi, b⟩
        exact ⟨i, hi, (hpv i z).mpr b⟩
    rw [key]

lemma proc {n : ℕ} {M : Finset ℕ} {gs P : List Gate} {obs prs : List (ℕ × ℕ)} {R U : ℕ}
    {φ : (Fin n → Bool) → Prop} (pre post : List Gate) (g : Gate)
    (hgs : gs = pre ++ g :: post) (hg : Ok g)
    (h : Good n M gs (pre.length + 1) P obs prs R U φ) :
    ∃ (P' : List Gate) (obs' prs' : List (ℕ × ℕ)) (R' U' : ℕ),
      Good n M gs pre.length P' obs' prs' R' U' φ ∧
      P'.length + obs'.length ≤ P.length + obs.length + 3 := by
  by_cases hex : ∃ o ∈ obs, o.2 = n + pre.length
  · obtain ⟨o1, ho1, e1⟩ := hex
    obtain ⟨l1, l2, hl⟩ := List.append_of_mem ho1
    have hobs : ∀ o ∈ obs, o.1 < n + P.length ∧ dg n M P o.1 ≤ 1 ∧
        dg n M P o.1 + dg n M gs o.2 ≤ 4 ∧ 3 ≤ dg n M gs o.2 ∧
        o.2 < n + (pre.length + 1) := by
      have h' := h
      unfold Good at h'
      exact h'.2.2.1
    obtain ⟨a1, a2, a3, a4, a5⟩ := hobs o1 ho1
    rw [e1] at a3 a4
    have hsub : ∀ o, o ∈ l1 ++ l2 → o ∈ obs := by
      intro o ho
      rw [hl]
      rcases List.mem_append.mp ho with ho | ho
      · exact List.mem_append.mpr (Or.inl ho)
      · exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ ho))
    obtain ⟨ext, c', obs0, k1, k2, k3, k4, k5, k6⟩ :=
      merge M (n + pre.length) (4 - dg n M gs (n + pre.length)) (l1 ++ l2) P o1.1 a1
        (by omega)
        (fun o ho e => by
          obtain ⟨b1, b2, b3, b4, b5⟩ := hobs o (hsub o ho)
          rw [e] at b3
          exact ⟨b1, by omega⟩)
    have g1 := good_ext h ext k1
    obtain ⟨φ0, g2, hφ⟩ := good_restrict g1 obs0 (fun o => by
      rw [k4 o]
      constructor
      · rintro ⟨a, b⟩
        exact ⟨hsub o a, b⟩
      · rintro ⟨a, b⟩
        refine ⟨?_, b⟩
        rw [hl] at a
        rcases List.mem_append.mp a with a | a
        · exact List.mem_append.mpr (Or.inl a)
        · rcases List.mem_cons.mp a with a | a
          · rw [a] at b
            exact absurd e1 b
          · exact List.mem_append.mpr (Or.inr a))
    obtain ⟨P', obs', prs', R', U', g3, cost⟩ :=
      gate_step pre post g hgs hg g2 c' k2 (by omega) (by omega) a4
    have el1 : (P ++ ext).length = P.length + ext.length := List.length_append
    have el2 : (l1 ++ l2).length + 1 = obs.length := by
      rw [hl, List.length_append, List.length_append, List.length_cons]
      omega
    refine ⟨P', obs', prs', R', U', good_congr g3 (fun z => ?_), by omega⟩
    rw [hφ z, k6 z]
    have key : (∃ o ∈ obs, o.2 = n + pre.length ∧ vl (P ++ ext) o.1 z = true) ↔
        (vl P o1.1 z = true ∨
          ∃ o ∈ l1 ++ l2, o.2 = n + pre.length ∧ vl P o.1 z = true) := by
      constructor
      · rintro ⟨o, ho, e, b⟩
        rw [vl_ext P ext o.1 z (hobs o ho).1] at b
        rw [hl] at ho
        rcases List.mem_append.mp ho with ho | ho
        · exact Or.inr ⟨o, List.mem_append.mpr (Or.inl ho), e, b⟩
        · rcases List.mem_cons.mp ho with ho | ho
          · rw [ho] at b
            exact Or.inl b
          · exact Or.inr ⟨o, List.mem_append.mpr (Or.inr ho), e, b⟩
      · rintro (b | ⟨o, ho, e, b⟩)
        · exact ⟨o1, ho1, e1, by rw [vl_ext P ext o1.1 z a1]; exact b⟩
        · exact ⟨o, hsub o ho, e, by rw [vl_ext P ext o.1 z (hobs o (hsub o ho)).1]; exact b⟩
    rw [key]
  · obtain ⟨φ0, g2, hφ⟩ := good_restrict h obs
      (fun o => ⟨fun ho => ⟨ho, fun e => hex ⟨o, ho, e⟩⟩, fun ho => ho.1⟩)
    refine ⟨P, obs, prs, R, U, good_congr g2 (fun z => ?_), by omega⟩
    rw [hφ z]
    constructor
    · rintro (a | ⟨⟨o, ho, e, -⟩, -⟩)
      · exact a
      · exact absurd ⟨o, ho, e⟩ hex
    · exact Or.inl

lemma loop {n : ℕ} {M : Finset ℕ} {gs : List Gate} {φ : (Fin n → Bool) → Prop}
    (hmono : ∀ g ∈ gs, Ok g) :
    ∀ (k : ℕ), k ≤ gs.length → ∀ (P : List Gate) (obs prs : List (ℕ × ℕ)) (R U : ℕ),
      Good n M gs k P obs prs R U φ →
      ∃ (P' : List Gate) (obs' prs' : List (ℕ × ℕ)) (R' U' : ℕ),
        Good n M gs 0 P' obs' prs' R' U' φ ∧
        P'.length + obs'.length ≤ P.length + obs.length + 3 * k := by
  intro k
  induction k with
  | zero =>
    intro _ P obs prs R U h
    exact ⟨P, obs, prs, R, U, h, by omega⟩
  | succ k ih =>
    intro hk P obs prs R U h
    have hlt : k < gs.length := by omega
    have hgs : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
      rw [← List.drop_eq_getElem_cons hlt]
      exact (List.take_append_drop k gs).symm
    have hpl : (gs.take k).length = k := by
      rw [List.length_take]
      omega
    have h' : Good n M gs ((gs.take k).length + 1) P obs prs R U φ := by
      rw [hpl]
      exact h
    obtain ⟨P1, obs1, prs1, R1, U1, g1, c1⟩ :=
      proc (gs.take k) (gs.drop (k + 1)) gs[k] hgs (hmono _ (List.getElem_mem hlt)) h'
    rw [hpl] at g1
    obtain ⟨P2, obs2, prs2, R2, U2, g2, c2⟩ := ih (by omega) P1 obs1 prs1 R1 U1 g1
    exact ⟨P2, obs2, prs2, R2, U2, g2, by omega⟩

lemma core (n : ℕ) (M : Finset ℕ) (gs : List Gate) (out : ℕ) (hmono : ∀ g ∈ gs, Ok g)
    (hdeg : dg n M gs out ≤ 4) :
    ∃ (P : List Gate) (prs : List (ℕ × ℕ)) (U R : ℕ),
      (∀ g ∈ P, Ok g) ∧ P.length ≤ 7 * gs.length ∧ prs.length ≤ P.length ∧
      (∀ p ∈ prs, dg n M (P ++ [⟨GateOp.or, [U, R]⟩]) p.1 ≤ 2 ∧
        dg n M (P ++ [⟨GateOp.or, [U, R]⟩]) p.2 ≤ 2) ∧
      dg n M (P ++ [⟨GateOp.or, [U, R]⟩]) R ≤ 3 ∧
      dg n M (P ++ [⟨GateOp.or, [U, R]⟩]) (n + P.length) ≤ 4 ∧
      ∀ z : Fin n → Bool, vl (P ++ [⟨GateOp.or, [U, R]⟩]) (n + P.length) z = vl gs out z ∧
        (vl (P ++ [⟨GateOp.or, [U, R]⟩]) U z = true ↔ ∃ p ∈ prs,
          vl (P ++ [⟨GateOp.or, [U, R]⟩]) p.1 z = true ∧
          vl (P ++ [⟨GateOp.or, [U, R]⟩]) p.2 z = true) := by
  by_cases hlow : dg n M gs out ≤ 3
  · obtain ⟨R, hR1, hR2, hR3⟩ : ∃ R, (R < n + gs.length ∨ n + gs.length + 1 ≤ R) ∧
        dg n M gs R ≤ 3 ∧ ∀ z : Fin n → Bool, vl gs R z = vl gs out z := by
      by_cases ho : out < n + gs.length
      · exact ⟨out, Or.inl ho, hlow, fun z => rfl⟩
      · refine ⟨n + gs.length + 1, Or.inr le_rfl, ?_, fun z => ?_⟩
        · rw [dg_oob n M gs (n + gs.length + 1) (by omega)]
          omega
        · rw [vl_oob gs (n + gs.length + 1) z (by omega), vl_oob gs out z (by omega)]
    have lD : (gs ++ [(⟨GateOp.or, [n + gs.length + 1, R]⟩ : Gate)]).length = gs.length + 1 := by
      rw [List.length_append, List.length_singleton]
    have S : ∀ t, (t < n + gs.length ∨ n + gs.length + 1 ≤ t) →
        dg n M (gs ++ [⟨GateOp.or, [n + gs.length + 1, R]⟩]) t = dg n M gs t ∧
        ∀ z : Fin n → Bool,
          vl (gs ++ [⟨GateOp.or, [n + gs.length + 1, R]⟩]) t z = vl gs t z := by
      intro t ht
      rcases ht with ht | ht
      · exact ⟨dg_ext n M gs _ t ht, fun z => vl_ext gs _ t z ht⟩
      · refine ⟨?_, fun z => ?_⟩
        · rw [dg_oob n M (gs ++ [(⟨GateOp.or, [n + gs.length + 1, R]⟩ : Gate)]) t (by omega),
            dg_oob n M gs t (by omega)]
        · rw [vl_oob (gs ++ [(⟨GateOp.or, [n + gs.length + 1, R]⟩ : Gate)]) t z (by omega),
            vl_oob gs t z (by omega)]
    refine ⟨gs, [], n + gs.length + 1, R, hmono, by omega, by simp, by simp, ?_, ?_,
      fun z => ⟨?_, ?_⟩⟩
    · rw [(S R hR1).1]
      exact hR2
    · rw [dg_or, dg_oob n M gs (n + gs.length + 1) (by omega)]
      exact max_le (by omega) (by omega)
    · rw [vl_or, vl_oob gs (n + gs.length + 1) z (by omega), hR3 z]
      rfl
    · rw [(S (n + gs.length + 1) (Or.inr le_rfl)).2 z, vl_oob gs (n + gs.length + 1) z (by omega)]
      simp
  · have h4 : dg n M gs out = 4 := by omega
    have hout : out < n + gs.length := by
      by_contra hc
      rw [dg_oob n M gs out (by omega)] at h4
      omega
    have hnout : n ≤ out := by
      by_contra hc
      have := dg_input n M gs out (by omega)
      omega
    have hs : 1 ≤ gs.length := by omega
    obtain ⟨B0, hB0⟩ : ∃ B0 : List Gate, B0 = gs ++ [⟨GateOp.or, []⟩] := ⟨_, rfl⟩
    obtain ⟨B1, hB1⟩ : ∃ B1 : List Gate, B1 = B0 ++ [⟨GateOp.and, []⟩] := ⟨_, rfl⟩
    have lB0 : B0.length = gs.length + 1 := by
      rw [hB0, List.length_append, List.length_singleton]
    have lB1 : B1.length = gs.length + 2 := by
      rw [hB1, List.length_append, List.length_singleton, lB0]
    have vF : ∀ z : Fin n → Bool, vl B1 (n + gs.length) z = false := by
      intro z
      rw [hB1, vl_ext B0 _ (n + gs.length) z (by omega), hB0, vl_new]
      rfl
    have dF : dg n M B1 (n + gs.length) = 0 := by
      rw [hB1, dg_ext n M B0 _ (n + gs.length) (by omega), hB0, dg_new]
      unfold Gate.lineDegree
      rw [if_neg (fun e => GateOp.noConfusion e)]
      rfl
    have eT : n + gs.length + 1 = n + B0.length := by omega
    have vT : ∀ z : Fin n → Bool, vl B1 (n + gs.length + 1) z = true := by
      intro z
      rw [eT, hB1, vl_new]
      rfl
    have dT : dg n M B1 (n + gs.length + 1) = 0 := by
      rw [eT, hB1, dg_new]
      unfold Gate.lineDegree
      rw [if_pos rfl]
      rfl
    have g0 : Good n M gs gs.length B1 [(n + gs.length + 1, out)] [] (n + gs.length)
        (n + gs.length) (fun z => vl gs out z = true) := by
      unfold Good
      refine ⟨⟨[⟨GateOp.or, []⟩] ++ [⟨GateOp.and, []⟩], by
        rw [hB1, hB0, List.append_assoc]⟩, ?_, ?_, ?_, ?_, ⟨by omega, by omega⟩,
        ⟨by omega, by omega, fun z => ?_⟩, fun z => ?_⟩
      · intro g hg
        rw [hB1, hB0] at hg
        rcases List.mem_append.mp hg with hg | hg
        · rcases List.mem_append.mp hg with hg | hg
          · exact hmono g hg
          · rw [List.mem_singleton.mp hg]
            exact ⟨Or.inr rfl, by simp⟩
        · rw [List.mem_singleton.mp hg]
          exact ⟨Or.inl rfl, by simp⟩
      · intro o ho
        rw [List.mem_singleton.mp ho]
        refine ⟨?_, ?_, ?_, ?_, hout⟩
        · show n + gs.length + 1 < n + B1.length
          omega
        · show dg n M B1 (n + gs.length + 1) ≤ 1
          omega
        · show dg n M B1 (n + gs.length + 1) + dg n M gs out ≤ 4
          omega
        · show 3 ≤ dg n M gs out
          omega
      · intro p hp
        simp at hp
      · simp
      · rw [vF z]
        simp
      · show vl gs out z = true ↔ _
        constructor
        · intro hv
          exact Or.inr (Or.inr ⟨(n + gs.length + 1, out), List.mem_singleton.mpr rfl, vT z, hv⟩)
        · rintro (a | a | ⟨o, ho, -, b⟩)
          · rw [vF z] at a
            exact (Bool.false_ne_true a).elim
          · rw [vF z] at a
            exact (Bool.false_ne_true a).elim
          · rw [List.mem_singleton.mp ho] at b
            exact b
    obtain ⟨P', obs', prs', R', U', gF, cost⟩ := loop hmono gs.length le_rfl B1 _ _ _ _ g0
    unfold Good at gF
    obtain ⟨-, f2, f3, f4, f5, f6, f7, f8⟩ := gF
    have noobs : ∀ o ∈ obs', False := by
      intro o ho
      obtain ⟨-, -, -, a4, a5⟩ := f3 o ho
      have := dg_input n M gs o.2 (by omega)
      omega
    have E : ∀ t, t < n + P'.length →
        dg n M (P' ++ [⟨GateOp.or, [U', R']⟩]) t = dg n M P' t ∧
        ∀ z : Fin n → Bool, vl (P' ++ [⟨GateOp.or, [U', R']⟩]) t z = vl P' t z :=
      fun t ht => ⟨dg_ext n M P' _ t ht, fun z => vl_ext P' _ t z ht⟩
    refine ⟨P', prs', U', R', f2, ?_, f5, ?_, ?_, ?_, fun z => ⟨?_, ?_⟩⟩
    · rw [List.length_singleton] at cost
      omega
    · intro p hp
      obtain ⟨a1, a2, a3, a4⟩ := f4 p hp
      rw [(E p.1 a1).1, (E p.2 a2).1]
      exact ⟨a3, a4⟩
    · rw [(E R' f6.1).1]
      exact f6.2
    · rw [dg_or]
      exact max_le f7.2.1 (by omega)
    · have f8z : vl gs out z = true ↔ (vl P' R' z = true ∨ vl P' U' z = true ∨
          ∃ o ∈ obs', vl P' o.1 z = true ∧ vl gs o.2 z = true) := f8 z
      rw [vl_or, Bool.eq_iff_iff, Bool.or_eq_true, f8z]
      constructor
      · rintro (a | a)
        · exact Or.inr (Or.inl a)
        · exact Or.inl a
      · rintro (a | a | ⟨o, ho, -⟩)
        · exact Or.inr a
        · exact Or.inl a
        · exact (noobs o ho).elim
    · rw [(E U' f7.1).2 z, f7.2.2 z]
      constructor
      · rintro ⟨p, hp, b1, b2⟩
        exact ⟨p, hp, by rw [(E p.1 (f4 p hp).1).2 z]; exact b1,
          by rw [(E p.2 (f4 p hp).2.1).2 z]; exact b2⟩
      · rintro ⟨p, hp, b1, b2⟩
        rw [(E p.1 (f4 p hp).1).2 z] at b1
        rw [(E p.2 (f4 p hp).2.1).2 z] at b2
        exact ⟨p, hp, b1, b2⟩

theorem main_aux : ∀ (Np Nl : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.CircuitLowerBounds.HasLineDegree (Np + Nl) (Finset.Ico Np (Np + Nl)) C 4 → ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (J : ℕ) (a b : Fin J → ℕ) (u r : ℕ), PEqualNP.MetaComplexity.Monotone2 D ∧ D.size ≤ 7 * C.size + 1 ∧ J ≤ D.size ∧ PEqualNP.CircuitLowerBounds.HasLineDegree (Np + Nl) (Finset.Ico Np (Np + Nl)) D 4 ∧ D.gates.getLast? = some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [u, r] } ∧ D.output + 1 = Np + Nl + D.gates.length ∧ (∀ j : Fin J, (D.lineDegrees (Np + Nl) (Finset.Ico Np (Np + Nl))).getD (a j) 0 ≤ 2 ∧ (D.lineDegrees (Np + Nl) (Finset.Ico Np (Np + Nl))).getD (b j) 0 ≤ 2) ∧ (D.lineDegrees (Np + Nl) (Finset.Ico Np (Np + Nl))).getD (r) 0 ≤ 3 ∧ ∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) D z = PEqualNP.MetaComplexity.circuitFun (Np + Nl) C z ∧ ((D.wires (List.ofFn z)).getD u false = true ↔ ∃ i : Fin J, (D.wires (List.ofFn z)).getD (a i) false = true ∧ (D.wires (List.ofFn z)).getD (b i) false = true) := by
  intro Np Nl C hmono hdeg
  obtain ⟨P, prs, U, R, h1, h2, h3, h4, h5, h6, h7⟩ :=
    core (Np + Nl) (Finset.Ico Np (Np + Nl)) C.gates C.output hmono hdeg
  have hlen : (P ++ [(⟨GateOp.or, [U, R]⟩ : Gate)]).length = P.length + 1 := by
    rw [List.length_append, List.length_singleton]
  refine ⟨⟨P ++ [⟨GateOp.or, [U, R]⟩], Np + Nl + P.length⟩, prs.length,
    fun j => (prs.get j).1, fun j => (prs.get j).2, U, R, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact h1 g hg
    · rw [List.mem_singleton.mp hg]
      exact ok_or U R
  · show (P ++ [(⟨GateOp.or, [U, R]⟩ : Gate)]).length ≤ 7 * C.gates.length + 1
    omega
  · show prs.length ≤ (P ++ [(⟨GateOp.or, [U, R]⟩ : Gate)]).length
    omega
  · exact h6
  · show (P ++ [(⟨GateOp.or, [U, R]⟩ : Gate)]).getLast? = _
    simp
  · show Np + Nl + P.length + 1 = Np + Nl + (P ++ [(⟨GateOp.or, [U, R]⟩ : Gate)]).length
    omega
  · intro j
    exact h4 (prs.get j) (List.get_mem prs j)
  · exact h5
  · intro z
    refine ⟨(h7 z).1, (h7 z).2.trans ⟨?_, ?_⟩⟩
    · rintro ⟨p, hp, b⟩
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hp
      rw [← hi] at b
      exact ⟨i, b⟩
    · rintro ⟨i, b⟩
      exact ⟨prs.get i, List.get_mem prs i, b⟩

end PEqualNP.Outside.L_meta_1383

theorem PEqualNP.Outside.L_meta_1383 : ∀ (Np Nl : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.CircuitLowerBounds.HasLineDegree (Np + Nl) (Finset.Ico Np (Np + Nl)) C 4 → ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (J : ℕ) (a b : Fin J → ℕ) (u r : ℕ), PEqualNP.MetaComplexity.Monotone2 D ∧ D.size ≤ 7 * C.size + 1 ∧ J ≤ D.size ∧ PEqualNP.CircuitLowerBounds.HasLineDegree (Np + Nl) (Finset.Ico Np (Np + Nl)) D 4 ∧ D.gates.getLast? = some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [u, r] } ∧ D.output + 1 = Np + Nl + D.gates.length ∧ (∀ j : Fin J, (D.lineDegrees (Np + Nl) (Finset.Ico Np (Np + Nl))).getD (a j) 0 ≤ 2 ∧ (D.lineDegrees (Np + Nl) (Finset.Ico Np (Np + Nl))).getD (b j) 0 ≤ 2) ∧ (D.lineDegrees (Np + Nl) (Finset.Ico Np (Np + Nl))).getD (r) 0 ≤ 3 ∧ ∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) D z = PEqualNP.MetaComplexity.circuitFun (Np + Nl) C z ∧ ((D.wires (List.ofFn z)).getD u false = true ↔ ∃ i : Fin J, (D.wires (List.ofFn z)).getD (a i) false = true ∧ (D.wires (List.ofFn z)).getD (b i) false = true) :=
  PEqualNP.Outside.L_meta_1383.main_aux
