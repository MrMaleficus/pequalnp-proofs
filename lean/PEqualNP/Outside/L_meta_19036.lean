import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19036

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

theorem getD_snoc_ne (L : List Bool) (a : Bool) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [a]).getD j false = L.getD j false := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · exact getD_snoc_lt L a j h
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

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

def fm (N B i : ℕ) : ℕ := if i < N then i else B + (i - N)

def cm (N B Z L i : ℕ) : ℕ := if i < L then fm N B i else Z

def cpG (N B Z : ℕ) (ν : ℕ → ℕ) (L : ℕ) (g : Gate) : Gate :=
  match g.op with
  | GateOp.and => ⟨GateOp.and, g.inputs.map (cm N B Z L)⟩
  | GateOp.or => ⟨GateOp.or, g.inputs.map (cm N B Z L)⟩
  | GateOp.not => match g.inputs with
    | [] => ⟨GateOp.or, []⟩
    | a :: _ => ⟨GateOp.or, [ν a]⟩
  | _ => ⟨GateOp.or, []⟩

def cp (N B Z : ℕ) (ν : ℕ → ℕ) : ℕ → List Gate → List Gate
  | _, [] => []
  | L, g :: t => cpG N B Z ν L g :: cp N B Z ν (L + 1) t

theorem cp_len (N B Z : ℕ) (ν : ℕ → ℕ) : ∀ (gs : List Gate) (L : ℕ), (cp N B Z ν L gs).length = gs.length := by
  intro gs
  induction gs with
  | nil => intro L; rfl
  | cons g t ih => intro L; simp only [cp, List.length_cons, ih]

theorem cpG_ok (N B Z : ℕ) (ν : ℕ → ℕ) (L : ℕ) (g : Gate) (hlen : g.inputs.length ≤ 2) :
    ((cpG N B Z ν L g).op = GateOp.and ∨ (cpG N B Z ν L g).op = GateOp.or) ∧
      (cpG N B Z ν L g).inputs.length ≤ 2 := by
  obtain ⟨op, ins⟩ := g
  simp only at hlen
  cases op with
  | and => simp only [cpG]; simp; omega
  | or => simp only [cpG]; simp; omega
  | not =>
    cases ins with
    | nil => simp [cpG]
    | cons a t => simp [cpG]
  | mod m => simp [cpG]
  | maj => simp [cpG]

theorem cp_ok (N B Z : ℕ) (ν : ℕ → ℕ) : ∀ (gs : List Gate) (L : ℕ), (∀ g ∈ gs, g.inputs.length ≤ 2) →
    ∀ g ∈ cp N B Z ν L gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro gs
  induction gs with
  | nil => intro L _ g hg; simp [cp] at hg
  | cons g0 t ih =>
    intro L h g hg
    simp only [cp, List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact cpG_ok N B Z ν L _ (h _ (List.mem_cons_self ..))
    · exact ih (L + 1) (fun g' hg' => h g' (List.mem_cons_of_mem _ hg')) g hg

theorem cp_gate (N B Z : ℕ) (ν : ℕ → ℕ) (L : ℕ) (U U' : List Bool) (hL : U.length = L)
    (hU' : U'.length ≤ Z) (hR : ∀ i, i < L → U'.getD (fm N B i) false = U.getD i false)
    (hneg : ∀ i, i < N → U'.getD (ν i) false = !U.getD i false) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨
      (g.op = GateOp.not ∧ ∃ i, i < N ∧ g.inputs.head? = some i)) :
    (cpG N B Z ν L g).op.eval ((cpG N B Z ν L g).inputs.map fun i => U'.getD i false)
      = g.op.eval (g.inputs.map fun i => U.getD i false) := by
  have hm : ∀ l : List ℕ, (l.map (cm N B Z L)).map (fun i => U'.getD i false) = l.map fun i => U.getD i false := by
    intro l
    rw [List.map_map]
    apply List.map_congr_left
    intro i _
    simp only [Function.comp, cm]
    split_ifs with h
    · exact hR i h
    · rw [List.getD_eq_default _ _ hU', List.getD_eq_default _ _ (by omega)]
  obtain ⟨op, ins⟩ := g
  rcases hop with h | h | ⟨h, i, hi, hh⟩ <;> simp only at h <;> subst h
  · simp only [cpG]
    rw [hm]
  · simp only [cpG]
    rw [hm]
  · cases ins with
    | nil => simp at hh
    | cons a t =>
      simp only [List.head?_cons, Option.some.injEq] at hh
      subst hh
      simp only [cpG, List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false,
        List.headD_cons, id_eq]
      exact hneg a hi

theorem cp_sim (N B Z : ℕ) (ν : ℕ → ℕ) (hNB : N ≤ B) (hν : ∀ i, i < N → ν i < B ∨ Z ≤ ν i) :
    ∀ (gs : List Gate) (L : ℕ) (U U' : List Bool),
    U.length = L → N ≤ L → U'.length = B + (L - N) → B + (L - N) + gs.length ≤ Z →
    (∀ i, i < L → U'.getD (fm N B i) false = U.getD i false) →
    (∀ i, i < N → U'.getD (ν i) false = !U.getD i false) →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨
      (g.op = GateOp.not ∧ ∃ i, i < N ∧ g.inputs.head? = some i)) →
    ∀ i, i < L + gs.length → (wf (cp N B Z ν L gs) U').getD (fm N B i) false = (wf gs U).getD i false := by
  intro gs
  induction gs with
  | nil => intro L U U' _ _ _ _ hR _ _ i hi; exact hR i (by simpa using hi)
  | cons g t ih =>
    intro L U U' hL hn hL' hZ hR hneg hop
    simp only [List.length_cons] at hZ
    have hval := cp_gate N B Z ν L U U' hL (by omega) hR hneg g (hop g (List.mem_cons_self ..))
    show ∀ i, i < L + (t.length + 1) → (wf (cpG N B Z ν L g :: cp N B Z ν (L + 1) t) U').getD (fm N B i) false
      = (wf (g :: t) U).getD i false
    rw [wf_cons, wf_cons, hval]
    have h2 := ih (L + 1) (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (U' ++ [g.op.eval (g.inputs.map fun i => U.getD i false)]) (by simp [hL]) (by omega)
      (by simp [hL']; omega) (by omega) ?_ ?_ (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg'))
    · intro i hi
      exact h2 i (by omega)
    · intro i hi
      by_cases hil : i < L
      · have hfl : fm N B i < U'.length := by unfold fm; split_ifs <;> omega
        rw [getD_snoc_lt _ _ _ hfl, getD_snoc_lt _ _ _ (by omega)]
        exact hR i hil
      · have hie : i = L := by omega
        subst hie
        have e1 : fm N B i = U'.length := by unfold fm; rw [if_neg (by omega)]; omega
        rw [e1, getD_snoc_eq, ← hL, getD_snoc_eq]
    · intro i hi
      have hne : ν i ≠ U'.length := by rcases hν i hi with h | h <;> omega
      rw [getD_snoc_ne _ _ _ hne, getD_snoc_lt _ _ _ (by omega)]
      exact hneg i hi

def BB (n m : ℕ) : ℕ := n + m + 3 * (n - 2) + 3 * (m - 2)

def nuF (n m Z i : ℕ) : ℕ :=
  if i < n then (if n = 1 then Z else nus 0 n (n + m) i)
  else (if m = 1 then Z else nus n m (n + m + 3 * (n - 2)) (i - n))

def newC (n m : ℕ) (C : Circuit) : Circuit :=
  ⟨blk 0 n (n + m) ++ blk n m (n + m + 3 * (n - 2)) ++
      cp (n + m) (BB n m) (BB n m + C.gates.length) (nuF n m (BB n m + C.gates.length)) (n + m) C.gates,
    if C.output < n + m + C.gates.length then fm (n + m) (BB n m) C.output else BB n m + C.gates.length⟩

theorem main_aux : ∀ (n m s : ℕ) (A : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ s → (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ i, i < n + m ∧ g.inputs.head? = some i) → PEqualNP.Represents.Represents A C → PEqualNP.Represents.RepSizeAtMost A (s + ((3 * n - 6) + (3 * m - 6))) := by
  intro n m s A C hF hs hnot hR
  have hop : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨
      (g.op = GateOp.not ∧ ∃ i, i < n + m ∧ g.inputs.head? = some i) := fun g hg => by
    have h1 : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by simpa using (hF g hg).1
    rcases h1 with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨h, hnot g hg h⟩)
  refine ⟨newC n m C, ?_, ?_, ?_⟩
  · intro g hg
    simp only [newC, List.mem_append] at hg
    rcases hg with (h | h) | h
    · have := blk_ok _ _ _ g h
      exact ⟨by simp [this.1], this.2⟩
    · have := blk_ok _ _ _ g h
      exact ⟨by simp [this.1], this.2⟩
    · have := cp_ok _ _ _ _ C.gates (n + m) (fun g' hg' => (hF g' hg').2) g h
      exact ⟨by rcases this.1 with h | h <;> simp [h], this.2⟩
  · show (blk 0 n (n + m) ++ blk n m (n + m + 3 * (n - 2)) ++
      cp (n + m) (BB n m) (BB n m + C.gates.length) (nuF n m (BB n m + C.gates.length)) (n + m) C.gates).length ≤ _
    rw [List.length_append, List.length_append, blk_len, blk_len, cp_len]
    have : C.gates.length ≤ s := hs
    omega
  · intro u v
    rw [← hR u v]
    show (wf (blk 0 n (n + m) ++ blk n m (n + m + 3 * (n - 2)) ++
      cp (n + m) (BB n m) (BB n m + C.gates.length) (nuF n m (BB n m + C.gates.length)) (n + m) C.gates)
      (oneEach u v)).getD
      (if C.output < n + m + C.gates.length then fm (n + m) (BB n m) C.output else BB n m + C.gates.length)
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
    have hpre : ∀ j, j < n + m → U2.getD j false = (oneEach u v).getD j false := fun j hj => by
      rw [hU2, wf_prefix _ _ _ (by rw [hU1l]; omega), hU1, wf_prefix _ _ _ (by rw [hxl]; exact hj)]
    have hR0 : ∀ i, i < n + m → U2.getD (fm (n + m) (BB n m) i) false = (oneEach u v).getD i false := by
      intro i hi
      simp only [fm, if_pos hi]
      exact hpre i hi
    have hN0 : ∀ i, i < n + m → U2.getD (nuF n m (BB n m + C.gates.length) i) false = !(oneEach u v).getD i false := by
      intro i hi
      simp only [nuF]
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
    have hν : ∀ i, i < n + m → nuF n m (BB n m + C.gates.length) i < BB n m ∨
        BB n m + C.gates.length ≤ nuF n m (BB n m + C.gates.length) i := by
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
    have hD := cp_sim (n + m) (BB n m) (BB n m + C.gates.length) (nuF n m (BB n m + C.gates.length))
      (by unfold BB; omega) hν C.gates (n + m) (oneEach u v) U2 hxl le_rfl (by rw [hU2l]; omega)
      (by omega) hR0 hN0 hop
    by_cases ho : C.output < n + m + C.gates.length
    · rw [if_pos ho]
      exact hD C.output ho
    · rw [if_neg ho, List.getD_eq_default _ _ (le_of_eq (by rw [wf_len, cp_len, hU2l])),
        List.getD_eq_default _ _ (by rw [wf_len, hxl]; omega)]

end PEqualNP.Outside.L_meta_19036

theorem PEqualNP.Outside.L_meta_19036 : ∀ (n m s : ℕ) (A : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ s → (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ i, i < n + m ∧ g.inputs.head? = some i) → PEqualNP.Represents.Represents A C → PEqualNP.Represents.RepSizeAtMost A (s + ((3 * n - 6) + (3 * m - 6))) :=
  PEqualNP.Outside.L_meta_19036.main_aux
