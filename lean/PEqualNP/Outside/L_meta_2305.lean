import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2305

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

abbrev Stat := Bool ⊕ ℕ

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Sum.inl b ∈ ins) : ∃ c, (simplify op m ins).2 = Sum.inl c := by
  rcases hop with rfl | rfl | rfl
  · have := hand rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpAnd]
  · have := hor rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Sum.inl false) = Sum.inl c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
  rw [hnone]; simp

def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Sum.inl false) = Sum.inl (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Sum.inl false) = Sum.inl c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Sum.inl false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩

def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate), gs[p]? = some g → CleanGate (m + p) g

theorem CleanGate.nok {m : ℕ} {g : Gate} (h : CleanGate m g) : NOk g := by
  rcases h with ⟨h1, j, _, h2⟩ | ⟨h1 | h1, j, k, _, _, h2⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inr rfl)
    · rw [h2]; simp
    · intro _; rw [h2]; simp
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inl rfl
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inl rfl)
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h

theorem CleanGate.lt {m : ℕ} {g : Gate} (h : CleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  intro a ha
  rcases h with ⟨_, j, hj, h2⟩ | ⟨_, j, k, hj, hk, h2⟩
  · rw [h2] at ha
    simp at ha
    subst ha; exact hj
  · rw [h2] at ha
    simp at ha
    rcases ha with rfl | rfl
    · exact hj
    · exact hk

theorem clean_nok (m : ℕ) (gs : List Gate) (h : CleanL m gs) : ∀ g ∈ gs, NOk g := by
  intro g hg
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hg
  exact (h p g hp).nok

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins, s.Valid m) :
    ∀ g ∈ (simplify op m ins).1, CleanGate m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    refine Or.inr ⟨Or.inl rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    refine Or.inr ⟨Or.inr rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    refine Or.inl ⟨rfl, _, ?_, rfl⟩
    exact hv _ List.mem_cons_self
  · simp at hg
  · simp at hg

theorem toList_getElem? {α : Type} (o : Option α) (k : ℕ) (a : α)
    (h : o.toList[k]? = some a) : k = 0 ∧ a ∈ o := by
  cases o with
  | none => simp at h
  | some b =>
    cases k with
    | zero => simp at h; simp [h]
    | succ k => simp at h

theorem clean_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro w acc _ _ h; exact h
  | cons g gs ih =>
    intro w acc hok hinv hcl
    have hinv' : Inv n y (wiresFrom [g] w) (elimStep n acc g) :=
      inv_elim n y hy [g] w acc (fun g' hg' => hok g' (by simp at hg'; simp [hg'])) hinv
    refine ih _ (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hinv' ?_
    intro p g' hp
    have hp' : (acc.2 ++ (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)[p]? = some g' := hp
    by_cases hlt : p < acc.2.length
    · rw [List.getElem?_append_left hlt] at hp'
      exact hcl p g' hp'
    · rw [List.getElem?_append_right (by omega)] at hp'
      obtain ⟨h0, hmem⟩ := toList_getElem? _ _ _ hp'
      have hpl : p = acc.2.length := by omega
      rw [hpl]
      exact simplify_clean _ _ _ (fun s hs => by
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        exact (hinv.2 a).1) g' hmem

theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩

theorem elim_split_getD (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a ≤ acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elimStep n (elim n pre acc) g).1.getD a d := by
  rw [elim_append, elim_cons, elim_getD n a d post _ (by
    show a < ((elim n pre acc).1 ++ [_]).length
    rw [List.length_append, elim_fst_len, List.length_singleton]; omega)]

theorem elim_split_getD_lt (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a < acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elim n pre acc).1.getD a d := by
  rw [elim_split_getD n pre g post acc a d (le_of_lt h)]
  show ((elim n pre acc).1 ++ [_]).getD a d = _
  exact getD_snoc_ne _ _ _ _ (by rw [elim_fst_len]; omega)

theorem const_of_read (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) (p : ℕ) (g : Gate)
    (hp : gs[p]? = some g) (hg : NOk g) (a : ℕ) (ha : a ∈ g.inputs)
    (hlt : a < acc.1.length + p)
    (hc : (elim n gs acc).1.getD a (Sum.inl false) = Sum.inl (fixBit g)) :
    ∃ c, (elim n gs acc).1.getD (acc.1.length + p) (Sum.inl false) = Sum.inl c := by
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  rw [elim_split_getD_lt n pre g post acc a _ hlt] at hc
  obtain ⟨c, hc'⟩ := elimStep_const n (elim n pre acc) g hg a ha hc
  refine ⟨c, ?_⟩
  rw [elim_split_getD n pre g post acc _ _ (le_refl _)]
  rw [elim_fst_len] at hc'
  exact hc'

def trim (g : Gate) : Gate :=
  { op := g.op, inputs := if g.op.eval [Bool.false] = Bool.true then List.take (1 : ℕ) g.inputs else g.inputs }

def rd (g : Gate) : Bool := [(0 : ℕ), (9 : ℕ)].any fun (i : ℕ) => g.inputs.contains i

def X5 (gs : List Gate) : Prop :=
  ∃ (pre : List Gate) (g : Gate) (post : List Gate), gs = pre ++ g :: post ∧
    (g.op = GateOp.and ∧ (0 : ℕ) ∈ g.inputs ∨ g.op = GateOp.or ∧ (9 : ℕ) ∈ g.inputs) ∧
    ∃ h ∈ post, rd h = Bool.false ∧ (10 : ℕ) + pre.length ∈ h.inputs

theorem rd_iff (g : Gate) : rd g = true ↔ ((0 : ℕ) ∈ g.inputs ∨ (9 : ℕ) ∈ g.inputs) := by
  simp [rd]

theorem trim_eval (g : Gate) (hg : Ok g) (f : ℕ → Bool) :
    (trim g).op.eval ((trim g).inputs.map f) = g.op.eval (g.inputs.map f) := by
  obtain ⟨op, ins⟩ := g
  have h1 : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not := hg.1
  rcases h1 with rfl | rfl | rfl
  · simp [trim, GateOp.eval]
  · simp [trim, GateOp.eval]
  · cases ins <;> simp [trim, GateOp.eval]

theorem trim_nok (g : Gate) (hg : Ok g) : NOk (trim g) := by
  obtain ⟨op, ins⟩ := g
  have h1 : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not := hg.1
  have h2 : ins.length ≤ 2 := hg.2
  refine ⟨⟨h1, ?_⟩, ?_⟩
  · show (if op.eval [Bool.false] = Bool.true then List.take (1 : ℕ) ins else ins).length ≤ 2
    split_ifs
    · exact (List.length_take_le 1 ins).trans (by norm_num)
    · exact h2
  · intro h
    have h3 : op = GateOp.not := h
    subst h3
    show (if GateOp.not.eval [Bool.false] = Bool.true then List.take (1 : ℕ) ins else ins).length ≤ 1
    have e : GateOp.not.eval [Bool.false] = Bool.true := rfl
    rw [if_pos e]
    exact List.length_take_le 1 ins

theorem trim_wires (gs : List Gate) : (∀ g ∈ gs, Ok g) → ∀ w : List Bool,
    wiresFrom (gs.map trim) w = wiresFrom gs w := by
  induction gs with
  | nil => intro _ w; rfl
  | cons g gs ih =>
    intro hok w
    have e1 : wiresFrom ((g :: gs).map trim) w = wiresFrom (gs.map trim)
        (w ++ [(trim g).op.eval ((trim g).inputs.map fun i => w.getD i false)]) := rfl
    have e2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [e1, e2, trim_eval g (hok g List.mem_cons_self),
      ih (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))]

def Pst (acc : List Stat × List Gate) : Prop :=
  9 < acc.1.length ∧ acc.1.getD 0 (Sum.inl false) = Sum.inl false ∧
    acc.1.getD 9 (Sum.inl false) = Sum.inl true

theorem Pst_elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) (h : Pst acc) :
    Pst (elim n gs acc) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [elim_fst_len]; omega
  · rw [elim_getD n 0 _ gs acc (by omega)]; exact h2
  · rw [elim_getD n 9 _ gs acc (by omega)]; exact h3

theorem cnt (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate, (∀ g ∈ gs, NOk g) →
    Pst acc → (elim n gs acc).2.length + (gs.filter rd).length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _; simp [elim]
  | cons g gs ih =>
    intro acc hok hP
    have hP' : Pst (elimStep n acc g) := Pst_elim n [g] acc hP
    have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hP'
    rw [elim_cons]
    by_cases hr : rd g = true
    · have h2 : (elimStep n acc g).2.length = acc.2.length := by
        rcases (rd_iff g).1 hr with h0 | h9
        · exact elimStep_none n acc g (hok g List.mem_cons_self) 0 h0 false hP.2.1
        · exact elimStep_none n acc g (hok g List.mem_cons_self) 9 h9 true hP.2.2
      rw [List.filter_cons_of_pos hr, List.length_cons, List.length_cons]
      omega
    · have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      rw [List.filter_cons_of_neg hr, List.length_cons]
      omega

theorem count_bound (n : ℕ) (gs : List Gate) (a0 : List Stat × List Gate)
    (hok : ∀ g ∈ gs, NOk g) (hP : Pst a0) (hl : a0.1.length = 10)
    (hc : 3 ≤ (gs.filter rd).length ∨ (2 ≤ (gs.filter rd).length ∧ X5 gs)) :
    (elim n gs a0).2.length + 3 ≤ a0.2.length + gs.length := by
  rcases hc with hc | ⟨hc, pre, g, post, rfl, hg, h, hh, hrd, hin⟩
  · have := cnt n gs a0 hok hP
    omega
  · obtain ⟨p1, p2, rfl⟩ := List.append_of_mem hh
    obtain ⟨L1, hL1⟩ : ∃ L1 : List Gate, L1 = pre ++ g :: p1 := ⟨_, rfl⟩
    have e : pre ++ g :: (p1 ++ h :: p2) = L1 ++ h :: p2 := by rw [hL1]; simp
    rw [e] at hok hc ⊢
    have hokL : ∀ g' ∈ L1, NOk g' := fun g' hg' => hok g' (List.mem_append_left _ hg')
    have hokh : NOk h := hok h (by simp)
    have hokg : NOk g := hok g (by simp [hL1])
    have hok2 : ∀ g' ∈ p2, NOk g' := fun g' hg' => hok g' (by simp [hg'])
    have c1 := cnt n L1 a0 hokL hP
    have hP3 : Pst (elim n L1 a0) := Pst_elim n L1 a0 hP
    have hgp : L1[pre.length]? = some g := by
      rw [hL1, List.getElem?_append_right (le_refl _)]; simp
    have hcst : ∃ c, (elim n L1 a0).1.getD (a0.1.length + pre.length) (Sum.inl false)
        = Sum.inl c := by
      rcases hg with ⟨hop, h0⟩ | ⟨hop, h9⟩
      · have hb : fixBit g = false := by simp [fixBit, hop]
        exact const_of_read n L1 a0 pre.length g hgp hokg 0 h0 (by omega)
          (by rw [hb]; exact hP3.2.1)
      · have hb : fixBit g = true := by simp [fixBit, hop]
        exact const_of_read n L1 a0 pre.length g hgp hokg 9 h9 (by omega)
          (by rw [hb]; exact hP3.2.2)
    obtain ⟨c, hcst⟩ := hcst
    rw [hl] at hcst
    have h4 : (elimStep n (elim n L1 a0) h).2.length = (elim n L1 a0).2.length :=
      elimStep_none n _ h hokh (10 + pre.length) hin c hcst
    have hP4 : Pst (elimStep n (elim n L1 a0) h) := Pst_elim n [h] _ hP3
    have c2 := cnt n p2 _ hok2 hP4
    have hrd' : ¬ (rd h = true) := by rw [hrd]; simp
    rw [elim_append, elim_cons]
    rw [List.filter_append, List.filter_cons_of_neg hrd', List.length_append] at hc
    rw [List.length_append, List.length_cons]
    omega

def acc0 (n : ℕ) : List Stat × List Gate :=
  ((Sum.inl false : Stat) ::
    ((List.ofFn fun k : Fin n => (Sum.inr (k : ℕ) : Stat)) ++ [(Sum.inl true : Stat)]), [])

theorem inv0 (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (false :: (List.ofFn y ++ [true])) (acc0 n) := by
  refine ⟨by simp [acc0], ?_⟩
  intro i
  show Stat.Valid (n + 0) (((Sum.inl false : Stat) ::
      ((List.ofFn fun k : Fin n => (Sum.inr (k : ℕ) : Stat)) ++ [(Sum.inl true : Stat)])).getD i
        (Sum.inl false)) ∧
    Stat.val (List.ofFn y) (((Sum.inl false : Stat) ::
      ((List.ofFn fun k : Fin n => (Sum.inr (k : ℕ) : Stat)) ++ [(Sum.inl true : Stat)])).getD i
        (Sum.inl false)) = (false :: (List.ofFn y ++ [true])).getD i false
  rcases i with _ | i
  · simp only [List.getD_cons_zero]
    exact ⟨trivial, rfl⟩
  · simp only [List.getD_cons_succ]
    rcases lt_trichotomy i n with h | h | h
    · have hl1 : i < (List.ofFn fun k : Fin n => (Sum.inr (k : ℕ) : Stat)).length := by
        simpa using h
      have hl2 : i < (List.ofFn y).length := by simpa using h
      rw [List.getD_append _ _ _ _ hl1, List.getD_append _ _ _ _ hl2]
      have e1 : (List.ofFn fun k : Fin n => (Sum.inr (k : ℕ) : Stat)).getD i (Sum.inl false)
          = Sum.inr i := by
        simp [h]
      rw [e1]
      exact ⟨by show i < n + 0; omega, rfl⟩
    · have hl1 : (List.ofFn fun k : Fin n => (Sum.inr (k : ℕ) : Stat)).length = i := by
        simp [h]
      have hl2 : (List.ofFn y).length = i := by simp [h]
      rw [getD_snoc_len _ _ _ i hl1, getD_snoc_len _ _ _ i hl2]
      exact ⟨trivial, rfl⟩
    · have hl1 : ((List.ofFn fun k : Fin n => (Sum.inr (k : ℕ) : Stat))
          ++ [(Sum.inl true : Stat)]).length ≤ i := by
        simp; omega
      have hl2 : (List.ofFn y ++ [true]).length ≤ i := by simp; omega
      rw [List.getD_eq_default _ _ hl1, List.getD_eq_default _ _ hl2]
      exact ⟨trivial, rfl⟩

theorem Pst0 : Pst (acc0 8) := by
  refine ⟨by simp [acc0], by simp [acc0], ?_⟩
  show ((Sum.inl false : Stat) ::
      ((List.ofFn fun k : Fin 8 => (Sum.inr (k : ℕ) : Stat)) ++ [(Sum.inl true : Stat)])).getD
        (8 + 1) (Sum.inl false) = Sum.inl true
  rw [List.getD_cons_succ]
  exact getD_snoc_len _ _ _ 8 (by simp)

theorem core (C : Circuit) (hF : FanInTwo C)
    (h9 : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 Bool.false = !x 0)
    (hs : C.size ≤ 15)
    (hc : 3 ≤ ((List.map trim (List.drop 1 C.gates)).filter rd).length ∨
      (2 ≤ ((List.map trim (List.drop 1 C.gates)).filter rd).length ∧
        X5 (List.map trim (List.drop 1 C.gates))))
    (hnc : ∃ (a b : Fin 8 → Bool), circuitFun 9 C (Fin.cons Bool.false a) ≠
      circuitFun 9 C (Fin.cons Bool.false b)) :
    HasCircuitSize 8 (fun y : Fin 8 → Bool => circuitFun 9 C (Fin.cons Bool.false y)) 11 := by
  obtain ⟨gates, out⟩ := C
  have hok : ∀ g ∈ gates, Ok g := hF
  rcases gates with _ | ⟨g0, rest⟩
  · exfalso
    have h := h9 (fun _ => false)
    have e : (Circuit.wires ⟨[], out⟩ (List.ofFn fun _ : Fin 9 => false))
        = List.ofFn fun _ : Fin 9 => false := rfl
    rw [e, List.getD_eq_default _ _ (by simp)] at h
    simp at h
  · have hsz : rest.length ≤ 14 := by
      have h : (g0 :: rest).length ≤ 15 := hs
      rw [List.length_cons] at h
      omega
    have hc' : 3 ≤ ((rest.map trim).filter rd).length ∨
        (2 ≤ ((rest.map trim).filter rd).length ∧ X5 (rest.map trim)) := hc
    have hokr : ∀ g ∈ rest, Ok g := fun g hg => hok g (List.mem_cons_of_mem _ hg)
    have hok2 : ∀ g ∈ rest.map trim, NOk g := by
      intro g hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
      exact trim_nok g' (hokr g' hg')
    have hok2' : ∀ g ∈ rest.map trim, Ok g := fun g hg => (hok2 g hg).1
    have hw : ∀ y : Fin 8 → Bool,
        wiresFrom (rest.map trim) (false :: (List.ofFn y ++ [true]))
          = Circuit.wires ⟨g0 :: rest, out⟩ (List.ofFn (Fin.cons false y : Fin 9 → Bool)) := by
      intro y
      have e1 : Circuit.wires ⟨g0 :: rest, out⟩ (List.ofFn (Fin.cons false y : Fin 9 → Bool))
          = wiresFrom rest (List.ofFn (Fin.cons false y : Fin 9 → Bool) ++
            [g0.op.eval (g0.inputs.map fun i =>
              (List.ofFn (Fin.cons false y : Fin 9 → Bool)).getD i false)]) := rfl
      have hv : g0.op.eval (g0.inputs.map fun i =>
          (List.ofFn (Fin.cons false y : Fin 9 → Bool)).getD i false) = true := by
        have h := h9 (Fin.cons false y)
        rw [e1, getD_wiresFrom _ _ 9 (by simp), getD_snoc_len _ _ _ 9 (by simp)] at h
        exact h.trans rfl
      rw [trim_wires rest hokr, e1, hv]
      exact congrArg (fun l : List Bool => wiresFrom rest (l ++ [true]))
        (List.ofFn_cons false y).symm
    obtain ⟨A, hA⟩ : ∃ A : List Stat × List Gate, A = elim 8 (rest.map trim) (acc0 8) :=
      ⟨_, rfl⟩
    have hinv : ∀ y : Fin 8 → Bool, Inv 8 (List.ofFn y)
        (Circuit.wires ⟨g0 :: rest, out⟩ (List.ofFn (Fin.cons false y : Fin 9 → Bool))) A := by
      intro y
      rw [← hw y, hA]
      exact inv_elim 8 (List.ofFn y) (by simp) (rest.map trim) _ _ hok2' (inv0 8 y)
    have hval : ∀ y : Fin 8 → Bool,
        (A.1.getD out (Sum.inl false)).val (wiresFrom A.2 (List.ofFn y))
          = circuitFun 9 ⟨g0 :: rest, out⟩ (Fin.cons false y) :=
      fun y => ((hinv y).2 out).2
    have hlen : A.2.length ≤ 11 := by
      have h1 := count_bound 8 (rest.map trim) (acc0 8) hok2 Pst0 (by simp [acc0]) hc'
      rw [← hA, List.length_map] at h1
      have h2 : (acc0 8).2.length = 0 := rfl
      omega
    cases hst : A.1.getD out (Sum.inl false) with
    | inl c =>
      exfalso
      obtain ⟨a, b, hne⟩ := hnc
      apply hne
      have ha := hval a
      have hb := hval b
      rw [hst] at ha hb
      exact ha.symm.trans hb
    | inr j =>
      refine ⟨⟨A.2, j⟩, ?_, hlen, ?_⟩
      · have hcl : CleanL 8 A.2 := by
          rw [hA]
          exact clean_elim 8 (List.ofFn fun _ : Fin 8 => false) (by simp) (rest.map trim) _ _
            hok2' (inv0 8 _) (by intro p g hp; simp [acc0] at hp)
        show ∀ g ∈ A.2, Ok g
        exact fun g hg => (clean_nok 8 A.2 hcl g hg).1
      · intro y
        have h := hval y
        rw [hst] at h
        exact h

theorem main_aux : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   have x2 : List PEqualNP.CircuitLowerBounds.Gate := List.map (fun (x2 : PEqualNP.CircuitLowerBounds.Gate) => { op := x2.op, inputs := if x2.op.eval [Bool.false] = Bool.true then List.take (1 : ℕ) x2.inputs else x2.inputs : PEqualNP.CircuitLowerBounds.Gate }) (List.drop (1 : ℕ) x1.gates);   have x3 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Gate) => [(0 : ℕ), (9 : ℕ)].any fun (x4 : ℕ) => x3.inputs.contains x4;   have x4 : ℕ := (List.filter x3 x2).length;   have x5 : Prop := ∃ (x5 : List PEqualNP.CircuitLowerBounds.Gate) (x6 : PEqualNP.CircuitLowerBounds.Gate) (x7 : List PEqualNP.CircuitLowerBounds.Gate), x2 = x5 ++ x6 :: x7 ∧ (x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (0 : ℕ) ∈ x6.inputs ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (9 : ℕ) ∈ x6.inputs) ∧ ∃ x8 ∈ x7, x3 x8 = Bool.false ∧ (10 : ℕ) + x5.length ∈ x8.inputs;   PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x7 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x7)).getD (9 : ℕ) Bool.false = !x7 (0 : Fin (9 : ℕ))) → x1.size ≤ (15 : ℕ) → (3 : ℕ) ≤ x4 ∨ (2 : ℕ) ≤ x4 ∧ x5 → (∃ (x10 : Fin (8 : ℕ) → Bool) (x11 : Fin (8 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 (Fin.cons Bool.false x10) ≠ PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 (Fin.cons Bool.false x11)) → PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) (fun (x11 : Fin (8 : ℕ) → Bool) => PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 (Fin.cons Bool.false x11)) (11 : ℕ) := by
  intro x1
  exact core x1

end PEqualNP.Outside.L_meta_2305

theorem PEqualNP.Outside.L_meta_2305 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   have x2 : List PEqualNP.CircuitLowerBounds.Gate := List.map (fun (x2 : PEqualNP.CircuitLowerBounds.Gate) => { op := x2.op, inputs := if x2.op.eval [Bool.false] = Bool.true then List.take (1 : ℕ) x2.inputs else x2.inputs : PEqualNP.CircuitLowerBounds.Gate }) (List.drop (1 : ℕ) x1.gates);   have x3 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Gate) => [(0 : ℕ), (9 : ℕ)].any fun (x4 : ℕ) => x3.inputs.contains x4;   have x4 : ℕ := (List.filter x3 x2).length;   have x5 : Prop := ∃ (x5 : List PEqualNP.CircuitLowerBounds.Gate) (x6 : PEqualNP.CircuitLowerBounds.Gate) (x7 : List PEqualNP.CircuitLowerBounds.Gate), x2 = x5 ++ x6 :: x7 ∧ (x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (0 : ℕ) ∈ x6.inputs ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (9 : ℕ) ∈ x6.inputs) ∧ ∃ x8 ∈ x7, x3 x8 = Bool.false ∧ (10 : ℕ) + x5.length ∈ x8.inputs;   PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x7 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x7)).getD (9 : ℕ) Bool.false = !x7 (0 : Fin (9 : ℕ))) → x1.size ≤ (15 : ℕ) → (3 : ℕ) ≤ x4 ∨ (2 : ℕ) ≤ x4 ∧ x5 → (∃ (x10 : Fin (8 : ℕ) → Bool) (x11 : Fin (8 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 (Fin.cons Bool.false x10) ≠ PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 (Fin.cons Bool.false x11)) → PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) (fun (x11 : Fin (8 : ℕ) → Bool) => PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 (Fin.cons Bool.false x11)) (11 : ℕ) :=
  PEqualNP.Outside.L_meta_2305.main_aux
