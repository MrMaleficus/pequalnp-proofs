import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19120

open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem getD_ofFn {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    (List.ofFn f).getD (i : ℕ) false = f i := by
  simp

def pw (N B i : ℕ) : ℕ := if i < N then i else B + 2 * (i - N)

def nw (N B : ℕ) (ν : ℕ → ℕ) (i : ℕ) : ℕ := if i < N then ν i else B + 2 * (i - N) + 1

def posG (N B : ℕ) (ν : ℕ → ℕ) (L : ℕ) (g : Gate) : Gate :=
  match g.op with
  | GateOp.and => if g.inputs.all (fun i => decide (i < L)) = true then ⟨GateOp.and, g.inputs.map (pw N B)⟩ else ⟨GateOp.or, []⟩
  | GateOp.or => ⟨GateOp.or, (g.inputs.filter (fun i => decide (i < L))).map (pw N B)⟩
  | _ => match g.inputs with
    | [] => ⟨GateOp.and, []⟩
    | a :: _ => if a < L then ⟨GateOp.and, [nw N B ν a]⟩ else ⟨GateOp.and, []⟩

def negG (N B : ℕ) (ν : ℕ → ℕ) (L : ℕ) (g : Gate) : Gate :=
  match g.op with
  | GateOp.and => if g.inputs.all (fun i => decide (i < L)) = true then ⟨GateOp.or, g.inputs.map (nw N B ν)⟩ else ⟨GateOp.and, []⟩
  | GateOp.or => ⟨GateOp.and, (g.inputs.filter (fun i => decide (i < L))).map (nw N B ν)⟩
  | _ => match g.inputs with
    | [] => ⟨GateOp.or, []⟩
    | a :: _ => if a < L then ⟨GateOp.or, [pw N B a]⟩ else ⟨GateOp.or, []⟩

def Rel (N B : ℕ) (ν : ℕ → ℕ) (U U' : List Bool) : Prop :=
  ∀ i, i < U.length → U'.getD (pw N B i) false = U.getD i false ∧ U'.getD (nw N B ν i) false = !U.getD i false

theorem dm1 : ∀ l : List Bool, (l.map fun b => !b).any id = !(l.all id) := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih => simp only [List.map_cons, List.any_cons, List.all_cons, ih, id, Bool.not_and]

theorem dm2 : ∀ l : List Bool, (l.map fun b => !b).all id = !(l.any id) := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih => simp only [List.map_cons, List.any_cons, List.all_cons, ih, id, Bool.not_or]

theorem any_filter (p : ℕ → Bool) (f : ℕ → Bool) : ∀ ins : List ℕ, (∀ i ∈ ins, p i = false → f i = false) →
    ((ins.filter p).map f).any id = (ins.map f).any id := by
  intro ins
  induction ins with
  | nil => intro _; rfl
  | cons a t ih =>
    intro h
    have iht := ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
    by_cases hp : p a = true
    · simp only [List.filter_cons, hp, if_true, List.map_cons, List.any_cons, iht]
    · have hp' : p a = false := by simpa using hp
      have hf := h a (List.mem_cons_self ..) hp'
      simp only [List.filter_cons, hp', Bool.false_eq_true, if_false, List.map_cons, List.any_cons, iht, hf, id,
        Bool.false_or]

theorem gate_dual (N B : ℕ) (ν : ℕ → ℕ) (L : ℕ) (U U' : List Bool) (hL : U.length = L) (hR : Rel N B ν U U') (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) :
    (posG N B ν L g).op.eval ((posG N B ν L g).inputs.map fun i => U'.getD i false)
      = g.op.eval (g.inputs.map fun i => U.getD i false) ∧
    (negG N B ν L g).op.eval ((negG N B ν L g).inputs.map fun i => U'.getD i false)
      = !(g.op.eval (g.inputs.map fun i => U.getD i false)) := by
  obtain ⟨op, ins⟩ := g
  simp only at hop
  have hinv : ∀ i, ¬ i < L → U.getD i false = false := fun i hi =>
    List.getD_eq_default _ _ (by omega)
  have hmp : ∀ l : List ℕ, (∀ i ∈ l, i < L) → (l.map (pw N B)).map (fun i => U'.getD i false) = l.map fun i => U.getD i false := by
    intro l hl
    rw [List.map_map]
    apply List.map_congr_left
    intro i hi
    exact (hR i (by rw [hL]; exact hl i hi)).1
  have hmn : ∀ l : List ℕ, (∀ i ∈ l, i < L) → (l.map (nw N B ν)).map (fun i => U'.getD i false)
      = (l.map fun i => U.getD i false).map fun b => !b := by
    intro l hl
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro i hi
    exact (hR i (by rw [hL]; exact hl i hi)).2
  rcases hop with rfl | rfl | rfl
  · by_cases hall : ins.all (fun i => decide (i < L)) = true
    · have hl : ∀ i ∈ ins, i < L := fun i hi => by simpa using List.all_eq_true.1 hall i hi
      simp only [posG, negG, hall, if_true]
      constructor
      · show ((ins.map (pw N B)).map fun i => U'.getD i false).all id = (ins.map fun i => U.getD i false).all id
        rw [hmp ins hl]
      · show ((ins.map (nw N B ν)).map fun i => U'.getD i false).any id = !((ins.map fun i => U.getD i false).all id)
        rw [hmn ins hl, dm1]
    · simp only [posG, negG, hall, if_false]
      have hf : (ins.map fun i => U.getD i false).all id = false := by
        rw [Bool.eq_false_iff]
        intro hc
        apply hall
        rw [List.all_eq_true] at hc ⊢
        intro i hi
        by_contra hlt
        have h1 := hc (U.getD i false) (List.mem_map.2 ⟨i, hi, rfl⟩)
        rw [hinv i (by simpa using hlt)] at h1
        exact absurd h1 (by simp)
      constructor
      · show ([] : List Bool).any id = (ins.map fun i => U.getD i false).all id
        rw [hf]; rfl
      · show ([] : List Bool).all id = !((ins.map fun i => U.getD i false).all id)
        rw [hf]; rfl
  · have hl : ∀ i ∈ ins.filter (fun i => decide (i < L)), i < L := fun i hi => by
      simpa using (List.mem_filter.1 hi).2
    have hfa := any_filter (fun i => decide (i < L)) (fun i => U.getD i false) ins
      (fun i _ hp => hinv i (by simpa using hp))
    simp only [posG, negG]
    constructor
    · show (((ins.filter fun i => decide (i < L)).map (pw N B)).map fun i => U'.getD i false).any id
        = (ins.map fun i => U.getD i false).any id
      rw [hmp _ hl, hfa]
    · show (((ins.filter fun i => decide (i < L)).map (nw N B ν)).map fun i => U'.getD i false).all id
        = !((ins.map fun i => U.getD i false).any id)
      rw [hmn _ hl, dm2, hfa]
  · cases ins with
    | nil =>
      simp only [posG, negG]
      exact ⟨rfl, rfl⟩
    | cons a t =>
      by_cases ha : a < L
      · simp only [posG, negG, ha, if_true]
        have h1 := hR a (by rw [hL]; exact ha)
        constructor
        · show (U'.getD (nw N B ν a) false && true) = !(U.getD a false)
          rw [h1.2, Bool.and_true]
        · show (U'.getD (pw N B a) false || false) = !!(U.getD a false)
          rw [h1.1, Bool.or_false, Bool.not_not]
      · simp only [posG, negG, ha, if_false]
        have h0 := hinv a ha
        constructor
        · show true = !(U.getD a false)
          rw [h0]; rfl
        · show false = !!(U.getD a false)
          rw [h0]; rfl

def dual (N B : ℕ) (ν : ℕ → ℕ) : ℕ → List Gate → List Gate
  | _, [] => []
  | L, g :: t => posG N B ν L g :: negG N B ν L g :: dual N B ν (L + 1) t

theorem dual_len (N B : ℕ) (ν : ℕ → ℕ) : ∀ (gs : List Gate) (L : ℕ), (dual N B ν L gs).length = 2 * gs.length := by
  intro gs
  induction gs with
  | nil => intro L; rfl
  | cons g t ih => intro L; simp only [dual, List.length_cons, ih]; omega

theorem pn_ok (N B : ℕ) (ν : ℕ → ℕ) (L : ℕ) (g : Gate) (hlen : g.inputs.length ≤ 2) :
    ((posG N B ν L g).op = GateOp.and ∨ (posG N B ν L g).op = GateOp.or) ∧ (posG N B ν L g).inputs.length ≤ 2 ∧
    ((negG N B ν L g).op = GateOp.and ∨ (negG N B ν L g).op = GateOp.or) ∧ (negG N B ν L g).inputs.length ≤ 2 := by
  obtain ⟨op, ins⟩ := g
  simp only at hlen
  have hfl := List.length_filter_le (fun i => decide (i < L)) ins
  cases op with
  | and => simp only [posG, negG]; split_ifs <;> simp <;> omega
  | or => simp only [posG, negG]; simp; omega
  | not =>
    cases ins with
    | nil => simp [posG, negG]
    | cons a t => simp only [posG, negG]; split_ifs <;> simp
  | mod m =>
    cases ins with
    | nil => simp [posG, negG]
    | cons a t => simp only [posG, negG]; split_ifs <;> simp
  | maj =>
    cases ins with
    | nil => simp [posG, negG]
    | cons a t => simp only [posG, negG]; split_ifs <;> simp

theorem dual_ok (N B : ℕ) (ν : ℕ → ℕ) : ∀ (gs : List Gate) (L : ℕ), (∀ g ∈ gs, g.inputs.length ≤ 2) →
    ∀ g ∈ dual N B ν L gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro gs
  induction gs with
  | nil => intro L _ g hg; simp [dual] at hg
  | cons g0 t ih =>
    intro L h g hg
    simp only [dual, List.mem_cons] at hg
    have hp := pn_ok N B ν L g0 (h g0 (List.mem_cons_self ..))
    rcases hg with rfl | rfl | hg
    · exact ⟨hp.1, hp.2.1⟩
    · exact ⟨hp.2.2.1, hp.2.2.2⟩
    · exact ih (L + 1) (fun g' hg' => h g' (List.mem_cons_of_mem _ hg')) g hg


theorem getD_snoc_ne (L : List Bool) (a : Bool) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [a]).getD j false = L.getD j false := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · exact getD_snoc_lt L a j h
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem dual_sim (N B : ℕ) (ν : ℕ → ℕ) (hNB : N ≤ B) : ∀ (gs : List Gate) (L : ℕ) (U U' : List Bool),
    U.length = L → N ≤ L → U'.length = B + 2 * (L - N) →
    (∀ i, i < N → ν i < B ∨ B + 2 * (L - N) + 2 * gs.length ≤ ν i) → Rel N B ν U U' →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) →
    Rel N B ν (wf gs U) (wf (dual N B ν L gs) U') := by
  intro gs
  induction gs with
  | nil => intro L U U' _ _ _ _ hR _; exact hR
  | cons g t ih =>
    intro L U U' hL hn hL' hν hR hop
    have hpl : ∀ i, i < L → (pw N B i ≠ U'.length ∧ pw N B i ≠ U'.length + 1) ∧
        (nw N B ν i ≠ U'.length ∧ nw N B ν i ≠ U'.length + 1) := by
      intro i hi
      by_cases hiN : i < N
      · simp only [pw, nw, if_pos hiN]
        rcases hν i hiN with h1 | h1
        · omega
        · simp only [List.length_cons] at h1
          omega
      · simp only [pw, nw, if_neg hiN]
        omega
    have hg := gate_dual N B ν L U U' hL hR g (hop g (List.mem_cons_self ..))
    generalize hv : g.op.eval (g.inputs.map fun i => U.getD i false) = v at hg
    have hR1 : Rel N B ν U (U' ++ [v]) := by
      intro i hi
      have := hpl i (by omega)
      rw [getD_snoc_ne U' _ _ this.1.1, getD_snoc_ne U' _ _ this.2.1]
      exact hR i hi
    have hg2 := gate_dual N B ν L U _ hL hR1 g (hop g (List.mem_cons_self ..))
    rw [hv] at hg2
    show Rel N B ν (wf (g :: t) U) (wf (posG N B ν L g :: negG N B ν L g :: dual N B ν (L + 1) t) U')
    rw [wf_cons, wf_cons, wf_cons, hv, hg.1, hg2.2]
    refine ih (L + 1) _ _ (by simp [hL]) (by omega) (by simp [hL']; omega) ?_ ?_
      (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg'))
    · intro i hi
      rcases hν i hi with h1 | h1
      · exact Or.inl h1
      · right
        simp only [List.length_cons] at h1
        omega
    intro i hi
    have hi' : i < L + 1 := by simpa [hL] using hi
    by_cases hil : i < L
    · have h12 := hpl i hil
      have hlv : (U' ++ [v]).length = U'.length + 1 := by simp
      constructor
      · rw [getD_snoc_ne (U' ++ [v]) _ _ (by rw [hlv]; exact h12.1.2), getD_snoc_ne U' _ _ h12.1.1,
          getD_snoc_lt U _ _ (by omega)]
        exact (hR i (by omega)).1
      · rw [getD_snoc_ne (U' ++ [v]) _ _ (by rw [hlv]; exact h12.2.2), getD_snoc_ne U' _ _ h12.2.1,
          getD_snoc_lt U _ _ (by omega)]
        exact (hR i (by omega)).2
    · have hie : i = L := by omega
      subst hie
      have e1 : pw N B i = U'.length := by unfold pw; rw [if_neg (by omega)]; omega
      have e2 : nw N B ν i = (U' ++ [v]).length := by
        unfold nw; rw [if_neg (by omega), List.length_append]; simp; omega
      constructor
      · rw [e1, getD_snoc_lt (U' ++ [v]) _ _ (by rw [List.length_append]; simp), getD_snoc_eq, ← hL, getD_snoc_eq]
      · rw [e2, getD_snoc_eq, ← hL, getD_snoc_eq]

theorem wf_append (a b : List Gate) (w : List Bool) : wf (a ++ b) w = wf b (wf a w) := by
  unfold wf
  rw [List.foldl_append]

theorem wf_prefix : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  intro gs
  induction gs with
  | nil => intro w i _; rfl
  | cons g t ih =>
    intro w i hi
    rw [wf_cons, ih _ i (by simp; omega), getD_snoc_lt _ _ _ hi]

theorem blk_val (G : ℕ → Gate) (V : ℕ → Bool) (w : List Bool) : ∀ r : ℕ,
    (∀ i, i < w.length → w.getD i false = V i) →
    (∀ j, j < r → (∀ i ∈ (G j).inputs, i < w.length + j) ∧
      (G j).op.eval ((G j).inputs.map V) = V (w.length + j)) →
    ∀ i, i < w.length + r → (wf ((List.range r).map G) w).getD i false = V i := by
  intro r
  induction r with
  | zero =>
    intro hw _ i hi
    rw [List.range_zero, List.map_nil]
    exact hw i (by omega)
  | succ r ih =>
    intro hw hG i hi
    have ih' := ih hw (fun j hj => hG j (by omega))
    rw [List.range_succ, List.map_append, List.map_singleton, wf_append]
    have hlenA : (wf ((List.range r).map G) w).length = w.length + r := by rw [wf_len]; simp
    show (wf ((List.range r).map G) w ++ [(G r).op.eval ((G r).inputs.map fun i =>
      (wf ((List.range r).map G) w).getD i false)]).getD i false = V i
    by_cases hir : i < w.length + r
    · rw [getD_snoc_lt _ _ _ (by omega)]
      exact ih' i hir
    · obtain ⟨hin, hv⟩ := hG r (by omega)
      rw [show i = (wf ((List.range r).map G) w).length by omega, getD_snoc_eq, hlenA, ← hv]
      congr 1
      exact List.map_congr_left (fun i hi => ih' i (hin i hi))

theorem dd {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) : decide p = decide q := by
  simp only [h]

theorem dd2 {p q r : Prop} [Decidable p] [Decidable q] [Decidable r] (h : (p ∨ q) ↔ r) :
    (decide p || decide q) = decide r := by
  rw [← Bool.decide_or]
  exact dd h

def pre (o b t : ℕ) : ℕ := if t = 0 then o else b + (t - 1)

def suf (o k b t : ℕ) : ℕ := if t = 0 then o + (k - 1) else b + (k - 2 + t - 1)

def sg (o k b j : ℕ) : Gate :=
  if j < k - 2 then ⟨GateOp.or, [pre o b j, o + (j + 1)]⟩
  else if j < 2 * (k - 2) then ⟨GateOp.or, [o + (k - 2 - (j - (k - 2))), suf o k b (j - (k - 2))]⟩
  else ⟨GateOp.or, [pre o b (j - 2 * (k - 2)), suf o k b (k - 2 - 1 - (j - 2 * (k - 2)))]⟩

def blk (o k b : ℕ) : List Gate := (List.range (3 * (k - 2))).map (sg o k b)

def nus (o k b i : ℕ) : ℕ :=
  if i = 0 then suf o k b (k - 2) else if i = k - 1 then pre o b (k - 2) else b + (2 * (k - 2) + (i - 1))

def SEj (k u j : ℕ) : Bool :=
  if j < k - 2 then decide (u ≤ j + 1)
  else if j < 2 * (k - 2) then decide (k - 2 - (j - (k - 2)) ≤ u)
  else decide (u ≠ j - 2 * (k - 2) + 1)

theorem blk_len (o k b : ℕ) : (blk o k b).length = 3 * (k - 2) := by simp [blk]

theorem blk_ok (o k b : ℕ) : ∀ g ∈ blk o k b, g.op = GateOp.or ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [blk, List.mem_map, List.mem_range] at hg
  obtain ⟨j, _, rfl⟩ := hg
  unfold sg
  split_ifs <;> simp

theorem nus_lt (o k b i : ℕ) (hk : 2 ≤ k) (hi : i < k) (hob : o + k ≤ b) : nus o k b i < b + 3 * (k - 2) := by
  unfold nus pre suf
  split_ifs <;> omega

theorem side_ok (o k b u : ℕ) (w : List Bool) (hb : w.length = b) (hu : u < k) (hk : 2 ≤ k) (hob : o + k ≤ b)
    (hx : ∀ i, i < k → w.getD (o + i) false = decide (i = u)) :
    ∀ i, i < k → (wf (blk o k b) w).getD (nus o k b i) false = !decide (i = u) := by
  let V : ℕ → Bool := fun x => if x < b then w.getD x false else SEj k u (x - b)
  have hVi : ∀ i, i < k → V (o + i) = decide (i = u) := by
    intro i hi
    simp only [V, if_pos (show o + i < b by omega)]
    exact hx i hi
  have hVg : ∀ j, V (b + j) = SEj k u j := by
    intro j
    simp only [V, if_neg (show ¬ (b + j < b) by omega), Nat.add_sub_cancel_left]
  have hVp : ∀ t, t ≤ k - 2 → V (pre o b t) = decide (u ≤ t) := by
    intro t ht
    unfold pre
    split_ifs with h
    · have := hVi 0 (by omega)
      rw [Nat.add_zero] at this
      rw [this]
      exact dd (by omega)
    · rw [hVg]
      unfold SEj
      split_ifs <;> exact dd (by omega)
  have hVs : ∀ t, t ≤ k - 2 → V (suf o k b t) = decide (k - 1 - t ≤ u) := by
    intro t ht
    unfold suf
    split_ifs with h
    · rw [hVi (k - 1) (by omega)]
      exact dd (by omega)
    · rw [hVg]
      unfold SEj
      split_ifs <;> exact dd (by omega)
  have hv := blk_val (sg o k b) V w (3 * (k - 2))
    (fun i hi => by simp only [V, if_pos (show i < b by omega)])
    (by
      intro j hj
      rw [hb]
      unfold sg
      split_ifs with h1 h2
      · constructor
        · intro i hi
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
          rcases hi with rfl | rfl
          · unfold pre
            split_ifs <;> omega
          · omega
        · simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
            Bool.or_false, id_eq]
          rw [hVp j (by omega), hVi (j + 1) (by omega), hVg j]
          unfold SEj
          rw [if_pos h1]
          exact dd2 (by omega)
      · constructor
        · intro i hi
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
          rcases hi with rfl | rfl
          · omega
          · unfold suf
            split_ifs <;> omega
        · simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
            Bool.or_false, id_eq]
          rw [hVi (k - 2 - (j - (k - 2))) (by omega), hVs (j - (k - 2)) (by omega), hVg j]
          unfold SEj
          rw [if_neg h1, if_pos h2]
          exact dd2 (by omega)
      · constructor
        · intro i hi
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
          rcases hi with rfl | rfl
          · unfold pre
            split_ifs <;> omega
          · unfold suf
            split_ifs <;> omega
        · simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
            Bool.or_false, id_eq]
          rw [hVp (j - 2 * (k - 2)) (by omega), hVs (k - 2 - 1 - (j - 2 * (k - 2))) (by omega), hVg j]
          unfold SEj
          rw [if_neg h1, if_neg h2]
          exact dd2 (by omega))
  intro i hi
  show (wf ((List.range (3 * (k - 2))).map (sg o k b)) w).getD (nus o k b i) false = !decide (i = u)
  rw [hv _ (by rw [hb]; exact nus_lt o k b i hk hi hob), ← decide_not]
  unfold nus
  split_ifs with h1 h2
  · rw [hVs (k - 2) le_rfl]
    exact dd (by omega)
  · rw [hVp (k - 2) le_rfl]
    exact dd (by omega)
  · rw [hVg]
    unfold SEj
    split_ifs <;> exact dd (by omega)

open PEqualNP.MetaComplexity PEqualNP.Represents

theorem oe_len {n m : ℕ} (u : Fin n) (v : Fin m) : (oneEach u v).length = n + m := by
  simp [oneEach]

theorem oe_left {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) (h : i < n) :
    (oneEach u v).getD i false = decide (i = u.val) := by
  unfold oneEach
  rw [List.getD_append _ _ _ _ (by simp [h])]
  have e := getD_ofFn (fun j : Fin n => decide (j = u)) ⟨i, h⟩
  simp only at e
  rw [e]
  exact dd Fin.ext_iff

theorem oe_right {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) (h : i < m) :
    (oneEach u v).getD (n + i) false = decide (i = v.val) := by
  unfold oneEach
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_ofFn, Nat.add_sub_cancel_left]
  have e := getD_ofFn (fun j : Fin m => decide (j = v)) ⟨i, h⟩
  simp only at e
  rw [e]
  exact dd Fin.ext_iff

def BB (n m : ℕ) : ℕ := n + m + 3 * (n - 2) + 3 * (m - 2)

def nuF (n m G i : ℕ) : ℕ :=
  if i < n then (if n = 1 then BB n m + 2 * G else nus 0 n (n + m) i)
  else (if m = 1 then BB n m + 2 * G else nus n m (n + m + 3 * (n - 2)) (i - n))

def newC (n m : ℕ) (C : Circuit) : Circuit :=
  ⟨blk 0 n (n + m) ++ blk n m (n + m + 3 * (n - 2)) ++
      dual (n + m) (BB n m) (nuF n m C.gates.length) (n + m) C.gates,
    if C.output < n + m + C.gates.length then pw (n + m) (BB n m) C.output else BB n m + 2 * C.gates.length⟩

theorem conv_main : ∀ (n m s : ℕ) (A : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ s → PEqualNP.Represents.Represents A C →
  PEqualNP.Represents.RepSizeAtMost A (2 * s + ((3 * n - 6) + (3 * m - 6))) := by
  intro n m s A C hF hs hR
  have hop : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := fun g hg => by
    simpa using (hF g hg).1
  refine ⟨newC n m C, ?_, ?_, ?_⟩
  · intro g hg
    simp only [newC, List.mem_append] at hg
    rcases hg with (h | h) | h
    · have := blk_ok _ _ _ g h
      exact ⟨by simp [this.1], this.2⟩
    · have := blk_ok _ _ _ g h
      exact ⟨by simp [this.1], this.2⟩
    · have := dual_ok _ _ _ C.gates (n + m) (fun g' hg' => (hF g' hg').2) g h
      exact ⟨by rcases this.1 with h | h <;> simp [h], this.2⟩
  · show (blk 0 n (n + m) ++ blk n m (n + m + 3 * (n - 2)) ++
      dual (n + m) (BB n m) (nuF n m C.gates.length) (n + m) C.gates).length ≤ _
    rw [List.length_append, List.length_append, blk_len, blk_len, dual_len]
    have : C.gates.length ≤ s := hs
    omega
  · intro u v
    rw [← hR u v]
    show (wf (blk 0 n (n + m) ++ blk n m (n + m + 3 * (n - 2)) ++
      dual (n + m) (BB n m) (nuF n m C.gates.length) (n + m) C.gates) (oneEach u v)).getD
      (if C.output < n + m + C.gates.length then pw (n + m) (BB n m) C.output else BB n m + 2 * C.gates.length)
      false = (wf C.gates (oneEach u v)).getD C.output false
    rw [wf_append, wf_append]
    have hxl : (oneEach u v).length = n + m := oe_len u v
    have hU1l : (wf (blk 0 n (n + m)) (oneEach u v)).length = n + m + 3 * (n - 2) := by
      rw [wf_len, hxl, blk_len]
    have hU2l : (wf (blk n m (n + m + 3 * (n - 2))) (wf (blk 0 n (n + m)) (oneEach u v))).length = BB n m := by
      rw [wf_len, hU1l, blk_len]
      unfold BB
      omega
    set U1 := wf (blk 0 n (n + m)) (oneEach u v) with hU1
    set U2 := wf (blk n m (n + m + 3 * (n - 2))) U1 with hU2
    have hun := u.isLt
    have hvm := v.isLt
    have hR0 : Rel (n + m) (BB n m) (nuF n m C.gates.length) (oneEach u v) U2 := by
      intro i hi
      rw [hxl] at hi
      have hpre : ∀ j, j < n + m → U2.getD j false = (oneEach u v).getD j false := fun j hj => by
        rw [hU2, wf_prefix _ _ _ (by rw [hU1l]; omega), hU1, wf_prefix _ _ _ (by rw [hxl]; exact hj)]
      constructor
      · simp only [pw, if_pos hi]
        exact hpre i hi
      · simp only [nw, if_pos hi, nuF]
        by_cases hin : i < n
        · rw [if_pos hin, oe_left u v i hin]
          by_cases hn1 : n = 1
          · rw [if_pos hn1, List.getD_eq_default _ _ (by rw [hU2l]; omega)]
            rw [show i = u.val by omega]
            simp
          · rw [if_neg hn1]
            have hk : 2 ≤ n := by omega
            have hs1 := side_ok 0 n (n + m) u.val (oneEach u v) hxl u.isLt hk (by omega)
              (fun j hj => by rw [Nat.zero_add]; exact oe_left u v j hj) i hin
            have hlt := nus_lt 0 n (n + m) i hk hin (by omega)
            rw [hU2, wf_prefix _ _ _ (by rw [hU1l]; omega), hU1, hs1]
        · have ho := oe_right u v (i - n) (by omega)
          rw [show n + (i - n) = i by omega] at ho
          rw [if_neg hin, ho]
          by_cases hm1 : m = 1
          · rw [if_pos hm1, List.getD_eq_default _ _ (by rw [hU2l]; omega)]
            rw [show i - n = v.val by omega]
            simp
          · rw [if_neg hm1]
            have hk : 2 ≤ m := by omega
            have hs1 := side_ok n m (n + m + 3 * (n - 2)) v.val U1 hU1l v.isLt hk (by omega)
              (fun j hj => by rw [hU1, wf_prefix _ _ _ (by rw [hxl]; omega)]; exact oe_right u v j hj)
              (i - n) (by omega)
            rw [hU2, hs1]
    have hν : ∀ i, i < n + m → nuF n m C.gates.length i < BB n m ∨
        BB n m + 2 * (n + m - (n + m)) + 2 * C.gates.length ≤ nuF n m C.gates.length i := by
      intro i hi
      unfold nuF
      split_ifs with h1 h2 h3
      · right
        omega
      · left
        have := nus_lt 0 n (n + m) i (by omega) h1 (by omega)
        unfold BB
        omega
      · right
        omega
      · left
        have := nus_lt n m (n + m + 3 * (n - 2)) (i - n) (by omega) (by omega) (by omega)
        unfold BB
        omega
    have hD := dual_sim (n + m) (BB n m) (nuF n m C.gates.length) (by unfold BB; omega) C.gates (n + m)
      (oneEach u v) U2 hxl le_rfl (by rw [hU2l]; omega) hν hR0 hop
    by_cases ho : C.output < n + m + C.gates.length
    · rw [if_pos ho]
      exact (hD C.output (by rw [wf_len, hxl]; exact ho)).1
    · rw [if_neg ho, List.getD_eq_default _ _ (le_of_eq (by rw [wf_len, dual_len, hU2l])),
        List.getD_eq_default _ _ (by rw [wf_len, hxl]; omega)]

theorem main_aux : ∀ (n m c : ℕ) (A : Fin n → Fin m → Bool), ¬ PEqualNP.Represents.RepSizeAtMost A c →
  ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
    PEqualNP.Represents.Represents A C → c < 2 * C.size + ((3 * n - 6) + (3 * m - 6)) := by
  intro n m c A hA C hC hR
  by_contra h
  have h' : 2 * C.size + ((3 * n - 6) + (3 * m - 6)) ≤ c := Nat.le_of_not_lt h
  obtain ⟨D, hD1, hD2, hD3⟩ := conv_main n m C.size A C hC le_rfl hR
  exact hA ⟨D, hD1, le_trans hD2 h', hD3⟩

end PEqualNP.Outside.L_meta_19120

theorem PEqualNP.Outside.L_meta_19120 : ∀ (n m c : ℕ) (A : Fin n → Fin m → Bool), ¬ PEqualNP.Represents.RepSizeAtMost A c →
  ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
    PEqualNP.Represents.Represents A C → c < 2 * C.size + ((3 * n - 6) + (3 * m - 6)) :=
  PEqualNP.Outside.L_meta_19120.main_aux
