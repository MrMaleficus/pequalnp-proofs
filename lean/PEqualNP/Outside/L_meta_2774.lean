import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2774

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- Part 1: wire values, the value of an OR tree, the size of an OR tree.

private def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

private lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

private lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

private lemma wiresFrom_append (gs1 gs2 : List Gate) (w : List Bool) :
    wiresFrom (gs1 ++ gs2) w = wiresFrom gs2 (wiresFrom gs1 w) := by
  induction gs1 generalizing w with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, wiresFrom_cons, ih]

private lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih => rw [wiresFrom_cons, ih]; simp; omega

private lemma wiresFrom_prefix (gs : List Gate) (w : List Bool) :
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp [wiresFrom]⟩
  | cons g gs ih =>
    obtain ⟨t, ht, hlen⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, ?_, by simp [hlen]⟩
    rw [wiresFrom_cons, ht, List.append_assoc]

private lemma getD_snoc_lt {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

private lemma getD_snoc_eq {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
    (l ++ [x]).getD i d = x := by
  subst hi; simp [List.getD]

private lemma getD_snoc_ne {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i ≠ l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  by_cases hlt : i < l.length
  · exact getD_snoc_lt l x d i hlt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ hi]

private def wval {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

private lemma wval_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    wval C x w = x ⟨w, hw⟩ := by
  unfold wval
  rw [wires_eq, wiresFrom_getD_lt _ _ _ (by simp; exact hw)]
  simp [List.getD, hw]

private lemma wval_gate {n : ℕ} (C : Circuit) (hRB : ReadsBack n C) (x : Fin n → Bool)
    (j : ℕ) (hj : j < C.gates.length) :
    wval C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (wval C x)) := by
  have hsplit : C.gates = C.gates.take j ++ gateAt C j :: C.gates.drop (j + 1) := by
    have htake : C.gates.take j ++ C.gates.drop j = C.gates := List.take_append_drop j C.gates
    have hdrop : C.gates.drop j = gateAt C j :: C.gates.drop (j + 1) := by
      rw [List.drop_eq_getElem_cons hj]
      exact congrArg (· :: _) (List.getD_eq_getElem _ _ hj).symm
    rw [← hdrop, htake]
  have hlen : (wiresFrom (C.gates.take j) (List.ofFn x)).length = n + j := by
    rw [wiresFrom_length, List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  change (wiresFrom C.gates (List.ofFn x)).getD (n + j) false = _
  rw [hsplit, wiresFrom_append, wiresFrom_cons]
  rw [wiresFrom_getD_lt _ _ _ (by simp [hlen])]
  rw [getD_snoc_eq _ _ _ _ hlen.symm]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hilt : i < n + j := hRB j hj i hi
  symm
  change (wiresFrom C.gates (List.ofFn x)).getD i false = _
  conv_lhs => rw [hsplit, wiresFrom_append, wiresFrom_cons]
  rw [wiresFrom_getD_lt _ _ _ (by simp [hlen]; omega), getD_snoc_lt _ _ _ _ (by omega)]


private lemma orTree_eval_up {n : ℕ} {C : Circuit} {G L : Finset ℕ} {ρ : ℕ}
    (hRB : ReadsBack n C) (hGlt : ∀ j ∈ G, j < C.gates.length)
    (htree : IsOrTree n C G L ρ) (x : Fin n → Bool) :
    ∀ u, (u ∈ L ∨ (n ≤ u ∧ u - n ∈ G)) → wval C x u = true → wval C x ρ = true := by
  intro u hu hwu
  by_cases huρ0 : u = ρ
  · exact huρ0 ▸ hwu
  have hub : u ≤ n + C.gates.length := by
    rcases hu with huL | ⟨h1, h2⟩
    · have hr := (htree.2.1 u huL).2
      rw [if_neg huρ0] at hr
      have hex : ∃ j ∈ G, 0 < (gateAt C j).inputs.count u := by
        by_contra hno; push Not at hno
        have h0 : readsIn C G u = 0 :=
          Finset.sum_eq_zero (fun j hj => Nat.eq_zero_of_le_zero (hno j hj))
        omega
      obtain ⟨j, hj, hcnt⟩ := hex
      have hmem : u ∈ (gateAt C j).inputs := List.count_pos_iff.mp hcnt
      have := hRB j (hGlt j hj) u hmem
      have := hGlt j hj
      omega
    · have := hGlt (u - n) h2; omega
  clear huρ0
  generalize hk : n + C.gates.length - u = k
  induction k using Nat.strong_induction_on generalizing u with
  | _ k ih =>
    by_cases huρ : u = ρ
    · exact huρ ▸ hwu
    · have hrc : readsIn C G u = 1 := by
        rcases hu with huL | ⟨h1, h2⟩
        · have := (htree.2.1 u huL).2; rw [if_neg huρ] at this; exact this
        · have hsub : n + (u - n) = u := by omega
          have := htree.2.2.1 (u - n) h2
          rw [hsub, if_neg huρ] at this; exact this
      have hex : ∃ j ∈ G, u ∈ (gateAt C j).inputs := by
        by_contra hno; push Not at hno
        have h0 : readsIn C G u = 0 :=
          Finset.sum_eq_zero (fun j hj => List.count_eq_zero.mpr (hno j hj))
        omega
      obtain ⟨j, hj, hmem⟩ := hex
      have hjlt := hGlt j hj
      have hult : u < n + j := hRB j hjlt u hmem
      have hop := (htree.1 j hj).1
      have hval : wval C x (n + j) = true := by
        rw [wval_gate C hRB x j hjlt, hop]
        simp [GateOp.eval]
        exact ⟨u, hmem, hwu⟩
      exact ih (n + C.gates.length - (n + j)) (by omega) (n + j)
        (Or.inr ⟨Nat.le_add_right _ _, by simpa using hj⟩) hval (by omega) rfl

private lemma orTree_eval_down {n : ℕ} {C : Circuit} {G L : Finset ℕ} {ρ : ℕ}
    (hRB : ReadsBack n C) (hGlt : ∀ j ∈ G, j < C.gates.length)
    (htree : IsOrTree n C G L ρ) (x : Fin n → Bool) :
    ∀ u, (u ∈ L ∨ (n ≤ u ∧ u - n ∈ G)) → wval C x u = true → ∃ w ∈ L, wval C x w = true := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu hwu
    rcases hu with huL | ⟨h1, h2⟩
    · exact ⟨u, huL, hwu⟩
    · set j := u - n with hjdef
      have hu_eq : u = n + j := by omega
      rw [hu_eq, wval_gate C hRB x j (hGlt j h2), (htree.1 j h2).1] at hwu
      simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply] at hwu
      obtain ⟨i, hi, hwi⟩ := hwu
      have hilt : i < u := by rw [hu_eq]; exact hRB j (hGlt j h2) i hi
      exact ih i hilt ((htree.1 j h2).2.2 i hi) hwi

private lemma orTree_top_mem {n : ℕ} {C : Circuit} {G L : Finset ℕ} {ρ : ℕ}
    (htree : IsOrTree n C G L ρ) : ρ ∈ L ∨ (n ≤ ρ ∧ ρ - n ∈ G) := by
  have hr := htree.2.2.2
  by_cases hG : G = ∅
  · rw [if_pos hG] at hr
    exact Or.inl (by rw [hr]; simp)
  · rw [if_neg hG] at hr
    obtain ⟨j, hj, rfl⟩ := hr
    exact Or.inr ⟨Nat.le_add_right _ _, by simpa using hj⟩

private lemma orTree_eval_iff {n : ℕ} {C : Circuit} {G L : Finset ℕ} {ρ : ℕ}
    (hRB : ReadsBack n C) (hGlt : ∀ j ∈ G, j < C.gates.length)
    (htree : IsOrTree n C G L ρ) (x : Fin n → Bool) :
    wval C x ρ = true ↔ ∃ w ∈ L, wval C x w = true :=
  ⟨orTree_eval_down hRB hGlt htree x ρ (orTree_top_mem htree),
   fun ⟨w, hw, hww⟩ => orTree_eval_up hRB hGlt htree x w (Or.inl hw) hww⟩


-- The length of a list is the sum of the multiplicities of its entries over any set holding them.
theorem length_eq_sum_count (l : List ℕ) (S : Finset ℕ) (h : ∀ i ∈ l, i ∈ S) :
    l.length = ∑ w ∈ S, l.count w := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha : a ∈ S := h a (by simp)
    have ih' := ih (fun i hi => h i (by simp [hi]))
    simp only [List.length_cons, List.count_cons, Finset.sum_add_distrib]
    rw [← ih']
    simp [ha]

-- A binary OR tree has one gate less than leaves.
theorem tree_card (n : ℕ) (C : Circuit) (G L : Finset ℕ) (ρ : ℕ) (h : IsOrTree n C G L ρ) :
    L.card = G.card + 1 := by
  obtain ⟨hg, hl, hgg, hroot⟩ := h
  by_cases hG : G = ∅
  · rw [if_pos hG] at hroot
    rw [hroot, hG]
    simp
  · rw [if_neg hG] at hroot
    obtain ⟨j0, hj0, hρ⟩ := hroot
    have hρL : ρ ∉ L := by
      intro hin
      apply (hl ρ hin).1
      rw [hρ]
      exact ⟨Nat.le_add_right _ _, by simpa using hj0⟩
    have hdisj : Disjoint L (G.image (fun k => n + k)) := by
      rw [Finset.disjoint_left]
      intro w hw hw'
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw'
      apply (hl _ hw).1
      exact ⟨Nat.le_add_right _ _, by simpa using hk⟩
    have hsum : ∑ j ∈ G, (gateAt C j).inputs.length = 2 * G.card := by
      rw [Finset.sum_congr rfl (fun j hj => (hg j hj).2.1)]
      simp [Nat.mul_comm]
    have hlen : ∀ j ∈ G, (gateAt C j).inputs.length
        = ∑ w ∈ L ∪ G.image (fun k => n + k), (gateAt C j).inputs.count w := by
      intro j hj
      apply length_eq_sum_count
      intro i hi
      rcases (hg j hj).2.2 i hi with h1 | ⟨h1, h2⟩
      · exact Finset.mem_union_left _ h1
      · apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨i - n, h2, by omega⟩
    have h1 : ∑ j ∈ G, (gateAt C j).inputs.length
        = ∑ w ∈ L ∪ G.image (fun k => n + k), readsIn C G w := by
      rw [Finset.sum_congr rfl hlen, Finset.sum_comm]
      rfl
    have h2 : ∑ w ∈ L, readsIn C G w = L.card := by
      rw [Finset.sum_congr rfl (fun w hw => (hl w hw).2)]
      rw [Finset.sum_congr rfl (fun w hw => if_neg (fun (e : w = ρ) => hρL (e ▸ hw)))]
      simp
    have h3 : ∑ w ∈ G.image (fun k => n + k), readsIn C G w + 1 = G.card := by
      rw [Finset.sum_image (fun a _ b _ hab => by omega)]
      rw [Finset.sum_congr rfl (fun k hk => hgg k hk)]
      have e : ∀ k ∈ G, (if n + k = ρ then 0 else 1) = (if k = j0 then 0 else 1) := by
        intro k _
        by_cases hk : k = j0
        · simp [hk, hρ]
        · have : n + k ≠ ρ := by omega
          simp [hk, this]
      rw [Finset.sum_congr rfl e]
      rw [← Finset.add_sum_erase G _ hj0]
      rw [Finset.sum_congr rfl (fun k hk => if_neg (Finset.ne_of_mem_erase hk))]
      simp only [if_true, Finset.sum_const, smul_eq_mul, Nat.mul_one, Nat.zero_add]
      have := Finset.card_erase_add_one hj0
      omega
    rw [h1, Finset.sum_union hdisj, h2] at hsum
    omega


-- Part 2: reading back, as a property of a gate list with an offset.

def RBo (b : ℕ) (gs : List Gate) : Prop :=
  ∀ p < gs.length, ∀ i ∈ (gs.getD p ⟨GateOp.or, []⟩).inputs, i < b + p

theorem RBo_nil (b : ℕ) : RBo b [] := by
  intro p hp
  simp at hp

theorem RBo_cons (b : ℕ) (g : Gate) (gs : List Gate) (hg : ∀ i ∈ g.inputs, i < b)
    (h : RBo (b + 1) gs) : RBo b (g :: gs) := by
  intro p hp i hi
  cases p with
  | zero =>
    have hi' : i ∈ g.inputs := hi
    have := hg i hi'
    omega
  | succ q =>
    have hq : q < gs.length := by
      rw [List.length_cons] at hp
      omega
    have hi' : i ∈ (gs.getD q ⟨GateOp.or, []⟩).inputs := hi
    have := h q hq i hi'
    omega

theorem RBo_append (b : ℕ) (g1 g2 : List Gate) (h1 : RBo b g1)
    (h2 : RBo (b + g1.length) g2) : RBo b (g1 ++ g2) := by
  intro p hp i hi
  by_cases hlt : p < g1.length
  · rw [List.getD_append _ _ _ _ hlt] at hi
    exact h1 p hlt i hi
  · have hge : g1.length ≤ p := by omega
    rw [List.getD_append_right _ _ _ _ hge] at hi
    have hp2 : p - g1.length < g2.length := by
      rw [List.length_append] at hp
      omega
    have := h2 (p - g1.length) hp2 i hi
    omega

-- Part 3: restriction to a set of gates closed under reading.

def keepL (S : Finset ℕ) (m : ℕ) : List ℕ := (List.range m).filter (fun j => !decide (j ∈ S))

def rk (S : Finset ℕ) (m : ℕ) : ℕ := (keepL S m).length

def rn (n : ℕ) (S : Finset ℕ) (w : ℕ) : ℕ := if w < n then w else n + rk S (w - n)

def mkG (n : ℕ) (C : Circuit) (S : Finset ℕ) (j : ℕ) : Gate :=
  ⟨(gateAt C j).op, (gateAt C j).inputs.map (rn n S)⟩

def Dg (n : ℕ) (C : Circuit) (S : Finset ℕ) (m : ℕ) : List Gate := (keepL S m).map (mkG n C S)

theorem keepL_succ_in (S : Finset ℕ) (m : ℕ) (h : m ∈ S) : keepL S (m + 1) = keepL S m := by
  simp [keepL, List.range_succ, List.filter_append, h]

theorem keepL_succ_out (S : Finset ℕ) (m : ℕ) (h : m ∉ S) :
    keepL S (m + 1) = keepL S m ++ [m] := by
  simp [keepL, List.range_succ, List.filter_append, h]

theorem rk_mono (S : Finset ℕ) (a b : ℕ) (h : a ≤ b) : rk S a ≤ rk S b := by
  unfold rk keepL
  exact ((List.range_sublist.mpr h).filter _).length_le

theorem rk_lt (S : Finset ℕ) (j m : ℕ) (hj : j < m) (hS : j ∉ S) : rk S j < rk S m := by
  have h1 : rk S (j + 1) = rk S j + 1 := by
    unfold rk
    rw [keepL_succ_out S j hS, List.length_append, List.length_singleton]
  have h2 := rk_mono S (j + 1) m hj
  omega

theorem rn_lt (n : ℕ) (S : Finset ℕ) (i m : ℕ) (hi : i < n + m) (hS : i < n ∨ i - n ∉ S) :
    rn n S i < n + rk S m := by
  unfold rn
  by_cases h : i < n
  · rw [if_pos h]
    omega
  · rw [if_neg h]
    have hS2 : i - n ∉ S := by
      rcases hS with h1 | h1
      · exact absurd h1 h
      · exact h1
    have := rk_lt S (i - n) m (by omega) hS2
    omega

theorem Dg_succ_in (n : ℕ) (C : Circuit) (S : Finset ℕ) (m : ℕ) (h : m ∈ S) :
    Dg n C S (m + 1) = Dg n C S m := by
  unfold Dg
  rw [keepL_succ_in S m h]

theorem Dg_succ_out (n : ℕ) (C : Circuit) (S : Finset ℕ) (m : ℕ) (h : m ∉ S) :
    Dg n C S (m + 1) = Dg n C S m ++ [mkG n C S m] := by
  unfold Dg
  rw [keepL_succ_out S m h, List.map_append, List.map_singleton]

theorem Dg_len (n : ℕ) (C : Circuit) (S : Finset ℕ) (m : ℕ) : (Dg n C S m).length = rk S m := by
  unfold Dg rk
  rw [List.length_map]

theorem restrict_val (n : ℕ) (C : Circuit) (S : Finset ℕ) (hRB : ReadsBack n C)
    (hcl : ∀ k < C.gates.length, k ∉ S → ∀ i ∈ (gateAt C k).inputs, i < n ∨ i - n ∉ S)
    (x : Fin n → Bool) :
    ∀ m, m ≤ C.gates.length →
      (wiresFrom (Dg n C S m) (List.ofFn x)).length = n + rk S m ∧
      ∀ w, w < n + m → (w < n ∨ w - n ∉ S) →
        (wiresFrom (Dg n C S m) (List.ofFn x)).getD (rn n S w) false = wval C x w := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨?_, ?_⟩
    · rw [wiresFrom_length, Dg_len, List.length_ofFn]
    · intro w hw _
      have hw' : w < n := by omega
      have hl : w < (List.ofFn x).length := by rw [List.length_ofFn]; exact hw'
      have e : rn n S w = w := by unfold rn; rw [if_pos hw']
      rw [e]
      unfold wval
      rw [wires_eq, wiresFrom_getD_lt _ _ _ hl, wiresFrom_getD_lt _ _ _ hl]
  | succ m ih =>
    intro hm
    obtain ⟨hlen, hval⟩ := ih (by omega)
    by_cases hS : m ∈ S
    · have e2 : rk S (m + 1) = rk S m := by unfold rk; rw [keepL_succ_in S m hS]
      rw [Dg_succ_in n C S m hS, e2]
      refine ⟨hlen, ?_⟩
      intro w hw hk
      have hne : w ≠ n + m := by
        intro hwe
        rcases hk with h1 | h1
        · omega
        · apply h1
          have : w - n = m := by omega
          rw [this]
          exact hS
      exact hval w (by omega) hk
    · have e2 : rk S (m + 1) = rk S m + 1 := by
        unfold rk
        rw [keepL_succ_out S m hS, List.length_append, List.length_singleton]
      rw [Dg_succ_out n C S m hS, e2, wiresFrom_append]
      have hsingle : ∀ v : List Bool, wiresFrom [mkG n C S m] v =
          v ++ [(gateAt C m).op.eval (((gateAt C m).inputs.map (rn n S)).map
            fun i => v.getD i false)] :=
        fun v => rfl
      rw [hsingle]
      refine ⟨?_, ?_⟩
      · rw [List.length_append, List.length_singleton, hlen] <;> omega
      · intro w hw hk
        by_cases hwm : w = n + m
        · subst hwm
          have e3 : rn n S (n + m) = n + rk S m := by
            unfold rn
            rw [if_neg (by omega), Nat.add_sub_cancel_left]
          rw [e3, getD_snoc_eq _ _ _ _ hlen.symm, wval_gate C hRB x m (by omega), List.map_map]
          congr 1
          apply List.map_congr_left
          intro i hi
          exact hval i (hRB m (by omega) i hi) (hcl m (by omega) hS i hi)
        · have hw2 : w < n + m := by omega
          rw [getD_snoc_lt _ _ _ _ (by rw [hlen]; exact rn_lt n S w m hw2 hk)]
          exact hval w hw2 hk

theorem restrict_rb (n : ℕ) (C : Circuit) (S : Finset ℕ) (hRB : ReadsBack n C)
    (hcl : ∀ k < C.gates.length, k ∉ S → ∀ i ∈ (gateAt C k).inputs, i < n ∨ i - n ∉ S) :
    ∀ m, m ≤ C.gates.length → RBo n (Dg n C S m) := by
  intro m
  induction m with
  | zero =>
    intro _
    exact RBo_nil n
  | succ m ih =>
    intro hm
    by_cases hS : m ∈ S
    · rw [Dg_succ_in n C S m hS]
      exact ih (by omega)
    · rw [Dg_succ_out n C S m hS]
      apply RBo_append _ _ _ (ih (by omega))
      apply RBo_cons _ _ _ _ (RBo_nil _)
      intro i hi
      have hi' : i ∈ (gateAt C m).inputs.map (rn n S) := hi
      obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hi'
      rw [Dg_len]
      exact rn_lt n S i0 m (hRB m (by omega) i0 hi0) (hcl m (by omega) hS i0 hi0)

theorem keep_gate (C : Circuit) (S : Finset ℕ) (j : ℕ) (hj : j ∈ keepL S C.gates.length) :
    gateAt C j ∈ C.gates := by
  have hjl : j < C.gates.length := by
    have := (List.mem_filter.mp hj).1
    exact List.mem_range.mp this
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hjl]
  exact List.getElem_mem hjl

theorem restrict (n : ℕ) (C : Circuit) (S : Finset ℕ) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hcl : ∀ k < C.gates.length, k ∉ S → ∀ i ∈ (gateAt C k).inputs, i < n ∨ i - n ∉ S)
    (hS : ∀ j ∈ S, j < C.gates.length)
    (o : ℕ) (ho : o < C.gates.length) (hoS : o ∉ S) (hout : C.output = n + o) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ circuitFun n D = circuitFun n C ∧
      D.size + S.card ≤ C.size := by
  obtain ⟨hao, hRB, h2⟩ := hAO
  refine ⟨⟨Dg n C S C.gates.length, n + rk S o⟩, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g hg
    have hg' : g ∈ (keepL S C.gates.length).map (mkG n C S) := hg
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg'
    exact hao (gateAt C j) (keep_gate C S j hj)
  · exact restrict_rb n C S hRB hcl _ le_rfl
  · intro g hg
    have hg' : g ∈ (keepL S C.gates.length).map (mkG n C S) := hg
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg'
    have := h2 _ (keep_gate C S j hj)
    show ((gateAt C j).inputs.map (rn n S)).length = 2
    rw [List.length_map]
    exact this
  · funext x
    have h := (restrict_val n C S hRB hcl x C.gates.length le_rfl).2 (n + o) (by omega)
      (Or.inr (by rw [Nat.add_sub_cancel_left]; exact hoS))
    have e3 : rn n S (n + o) = n + rk S o := by
      unfold rn
      rw [if_neg (by omega), Nat.add_sub_cancel_left]
    rw [e3] at h
    show (wiresFrom (Dg n C S C.gates.length) (List.ofFn x)).getD (n + rk S o) false =
      (C.wires (List.ofFn x)).getD C.output false
    rw [hout]
    exact h
  · show (Dg n C S C.gates.length).length + S.card ≤ C.gates.length
    have h3 : (List.range C.gates.length).length =
        ((List.range C.gates.length).filter (fun j => decide (j ∈ S))).length +
        ((List.range C.gates.length).filter (fun j => !decide (j ∈ S))).length :=
      List.length_eq_length_filter_add _
    have h4 : S.card ≤ ((List.range C.gates.length).filter (fun j => decide (j ∈ S))).length := by
      refine le_trans (Finset.card_le_card ?_)
        (List.toFinset_card_le (l := (List.range C.gates.length).filter (fun j => decide (j ∈ S))))
      intro j hj
      rw [List.mem_toFinset, List.mem_filter]
      exact ⟨List.mem_range.mpr (hS j hj), by simpa using hj⟩
    have h5 : (Dg n C S C.gates.length).length =
        ((List.range C.gates.length).filter (fun j => !decide (j ∈ S))).length := Dg_len n C S _
    rw [List.length_range] at h3
    omega

-- Part 4: the new gates.

theorem or2v (p q : Bool) : GateOp.or.eval [p, q] = (p || q) := by
  cases p <;> cases q <;> rfl

theorem and2v (p q : Bool) : GateOp.and.eval [p, q] = (p && q) := by
  cases p <;> cases q <;> rfl

theorem or2 (V : List Bool) (p q : ℕ) :
    GateOp.or.eval ([p, q].map fun i => V.getD i false) = (V.getD p false || V.getD q false) :=
  or2v _ _

theorem and2 (V : List Bool) (p q : ℕ) :
    GateOp.and.eval ([p, q].map fun i => V.getD i false) = (V.getD p false && V.getD q false) :=
  and2v _ _

def chain : ℕ → List ℕ → List Gate
  | _, [] => []
  | acc, w :: ws => ⟨GateOp.or, [acc, w]⟩ :: chain (acc + 1) ws

theorem chain_len (ws : List ℕ) : ∀ acc, (chain acc ws).length = ws.length := by
  induction ws with
  | nil => intro acc; rfl
  | cons w ws ih =>
    intro acc
    show (chain (acc + 1) ws).length + 1 = ws.length + 1
    rw [ih]

theorem chain_mem (ws : List ℕ) : ∀ acc g, g ∈ chain acc ws →
    ∃ a w, acc ≤ a ∧ w ∈ ws ∧ g = ⟨GateOp.or, [a, w]⟩ := by
  induction ws with
  | nil =>
    intro acc g hg
    simp [chain] at hg
  | cons w ws ih =>
    intro acc g hg
    have hg' : g ∈ (⟨GateOp.or, [acc, w]⟩ : Gate) :: chain (acc + 1) ws := hg
    rcases List.mem_cons.mp hg' with h1 | h1
    · exact ⟨acc, w, le_rfl, List.mem_cons_self, h1⟩
    · obtain ⟨a, w2, ha, hw2, e⟩ := ih (acc + 1) g h1
      exact ⟨a, w2, by omega, List.mem_cons_of_mem _ hw2, e⟩

theorem chain_rb (ws : List ℕ) : ∀ acc, (∀ w ∈ ws, w ≤ acc) → RBo (acc + 1) (chain acc ws) := by
  induction ws with
  | nil =>
    intro acc _
    exact RBo_nil _
  | cons w ws ih =>
    intro acc h
    show RBo (acc + 1) (⟨GateOp.or, [acc, w]⟩ :: chain (acc + 1) ws)
    apply RBo_cons
    · intro i hi
      have hw := h w List.mem_cons_self
      have hi' : i ∈ [acc, w] := hi
      simp at hi'
      rcases hi' with e | e <;> omega
    · exact ih (acc + 1) (fun w2 hw2 => by
        have := h w2 (List.mem_cons_of_mem _ hw2)
        omega)

theorem chain_val (ws : List ℕ) : ∀ (acc : ℕ) (V : List Bool), V.length = acc + 1 →
    (∀ w ∈ ws, w < V.length) →
    ((wiresFrom (chain acc ws) V).getD (acc + ws.length) false = true ↔
      (V.getD acc false = true ∨ ∃ w ∈ ws, V.getD w false = true)) := by
  induction ws with
  | nil =>
    intro acc V _ _
    show V.getD (acc + 0) false = true ↔ _
    simp
  | cons w ws ih =>
    intro acc V hV h
    show (wiresFrom (chain (acc + 1) ws)
      (V ++ [GateOp.or.eval ([acc, w].map fun i => V.getD i false)])).getD
        (acc + (ws.length + 1)) false = true ↔ _
    rw [or2]
    have hlen : (V ++ [(V.getD acc false || V.getD w false)]).length = acc + 1 + 1 := by
      rw [List.length_append, List.length_singleton, hV]
    have e := ih (acc + 1) _ hlen (fun w2 hw2 => by
      rw [hlen]
      have := h w2 (List.mem_cons_of_mem _ hw2)
      omega)
    have e1 : acc + (ws.length + 1) = acc + 1 + ws.length := by omega
    have hsn : ∀ w2 ∈ ws, (V ++ [(V.getD acc false || V.getD w false)]).getD w2 false =
        V.getD w2 false :=
      fun w2 hw2 => getD_snoc_lt _ _ _ _ (h w2 (List.mem_cons_of_mem _ hw2))
    rw [e1, e, getD_snoc_eq V _ false (acc + 1) (by omega), Bool.or_eq_true]
    constructor
    · rintro (h1 | ⟨w2, hw2, h2⟩)
      · rcases h1 with h1 | h1
        · exact Or.inl h1
        · exact Or.inr ⟨w, List.mem_cons_self, h1⟩
      · exact Or.inr ⟨w2, List.mem_cons_of_mem _ hw2, (hsn w2 hw2).symm.trans h2⟩
    · rintro (h1 | ⟨w2, hw2, h2⟩)
      · exact Or.inl (Or.inl h1)
      · rcases List.mem_cons.mp hw2 with e2 | hw3
        · subst e2
          exact Or.inl (Or.inr h2)
        · exact Or.inr ⟨w2, hw3, (hsn w2 hw3).trans h2⟩

def newG (n len a b c : ℕ) (Lo : List ℕ) : List Gate :=
  ⟨GateOp.or, [b, c]⟩ :: ⟨GateOp.and, [a, n + len]⟩ :: chain (n + len + 1) Lo

theorem newG_len (n len a b c : ℕ) (Lo : List ℕ) : (newG n len a b c Lo).length = Lo.length + 1 + 1 := by
  show (chain (n + len + 1) Lo).length + 1 + 1 = Lo.length + 1 + 1
  rw [chain_len]

theorem newG_mem (n len a b c : ℕ) (Lo : List ℕ) (g : Gate) (hg : g ∈ newG n len a b c Lo) :
    g = ⟨GateOp.or, [b, c]⟩ ∨ g = ⟨GateOp.and, [a, n + len]⟩ ∨
      ∃ a2 w, n + len + 1 ≤ a2 ∧ w ∈ Lo ∧ g = ⟨GateOp.or, [a2, w]⟩ := by
  have hg' : g ∈ (⟨GateOp.or, [b, c]⟩ : Gate) :: (⟨GateOp.and, [a, n + len]⟩ : Gate) ::
      chain (n + len + 1) Lo := hg
  rcases List.mem_cons.mp hg' with h | h
  · exact Or.inl h
  · rcases List.mem_cons.mp h with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (chain_mem Lo _ g h))

theorem newG_rb (n len a b c : ℕ) (Lo : List ℕ) (ha : a < n + len) (hb : b < n + len)
    (hc : c < n + len) (hLo : ∀ w ∈ Lo, w < n + len) : RBo (n + len) (newG n len a b c Lo) := by
  unfold newG
  apply RBo_cons
  · intro i hi
    have hi' : i ∈ [b, c] := hi
    simp at hi'
    rcases hi' with e | e <;> omega
  · apply RBo_cons
    · intro i hi
      have hi' : i ∈ [a, n + len] := hi
      simp at hi'
      rcases hi' with e | e <;> omega
    · exact chain_rb Lo (n + len + 1) (fun w hw => by
        have := hLo w hw
        omega)

theorem two_step (V0 : List Bool) (N a b c : ℕ) (hN : V0.length = N) (ha : a < N)
    (gs : List Gate) :
    wiresFrom (⟨GateOp.or, [b, c]⟩ :: ⟨GateOp.and, [a, N]⟩ :: gs) V0 =
      wiresFrom gs ((V0 ++ [(V0.getD b false || V0.getD c false)]) ++
        [(V0.getD a false && (V0.getD b false || V0.getD c false))]) := by
  have e1 : (V0 ++ [(V0.getD b false || V0.getD c false)]).getD a false = V0.getD a false :=
    getD_snoc_lt _ _ _ _ (by omega)
  have e2 : (V0 ++ [(V0.getD b false || V0.getD c false)]).getD N false =
      (V0.getD b false || V0.getD c false) :=
    getD_snoc_eq _ _ _ _ hN.symm
  show wiresFrom gs ((V0 ++ [GateOp.or.eval ([b, c].map fun i => V0.getD i false)]) ++
    [GateOp.and.eval ([a, N].map fun i =>
      (V0 ++ [GateOp.or.eval ([b, c].map fun i => V0.getD i false)]).getD i false)]) = _
  rw [or2, and2, e1, e2]

theorem tail_val (V0 : List Bool) (N : ℕ) (hN : V0.length = N) (vx vy : Bool) (Lo : List ℕ)
    (hLo : ∀ w ∈ Lo, w < N) :
    ((wiresFrom (chain (N + 1) Lo) ((V0 ++ [vx]) ++ [vy])).getD (N + 1 + Lo.length) false = true ↔
      (vy = true ∨ ∃ w ∈ Lo, V0.getD w false = true)) := by
  have hl1 : (V0 ++ [vx]).length = N + 1 := by
    rw [List.length_append, List.length_singleton, hN]
  have hl2 : ((V0 ++ [vx]) ++ [vy]).length = N + 1 + 1 := by
    rw [List.length_append, List.length_singleton, hl1]
  refine (chain_val Lo (N + 1) _ hl2 (fun w hw => by
    rw [hl2]
    have := hLo w hw
    omega)).trans ?_
  have e3 : ((V0 ++ [vx]) ++ [vy]).getD (N + 1) false = vy := getD_snoc_eq _ _ _ _ hl1.symm
  have e4 : ∀ w ∈ Lo, ((V0 ++ [vx]) ++ [vy]).getD w false = V0.getD w false := fun w hw => by
    have := hLo w hw
    rw [getD_snoc_lt (V0 ++ [vx]) vy false w (by rw [hl1]; omega), getD_snoc_lt V0 vx false w (by omega)]
  rw [e3]
  constructor
  · rintro (h1 | ⟨w, hw, h2⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨w, hw, by rw [← e4 w hw]; exact h2⟩
  · rintro (h1 | ⟨w, hw, h2⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨w, hw, by rw [e4 w hw]; exact h2⟩

theorem newG_val (n : ℕ) (C : Circuit) (a b c : ℕ) (Lo : List ℕ) (x : Fin n → Bool)
    (ha : a < n + C.gates.length) (hLo : ∀ w ∈ Lo, w < n + C.gates.length) :
    ((wiresFrom (C.gates ++ newG n C.gates.length a b c Lo) (List.ofFn x)).getD
        (n + C.gates.length + 1 + Lo.length) false = true ↔
      ((wval C x a = true ∧ (wval C x b = true ∨ wval C x c = true)) ∨
        ∃ w ∈ Lo, wval C x w = true)) := by
  have hV0 : (wiresFrom C.gates (List.ofFn x)).length = n + C.gates.length := by
    rw [wiresFrom_length, List.length_ofFn]
  have hw : ∀ w, wval C x w = (wiresFrom C.gates (List.ofFn x)).getD w false := fun w => rfl
  simp only [hw]
  rw [wiresFrom_append]
  generalize wiresFrom C.gates (List.ofFn x) = V0 at hV0 ⊢
  unfold newG
  rw [two_step V0 (n + C.gates.length) a b c hV0 ha,
    tail_val V0 (n + C.gates.length) hV0 _ _ Lo hLo]
  simp only [Bool.and_eq_true, Bool.or_eq_true]

def bigC (C : Circuit) (NG : List Gate) (o : ℕ) : Circuit := ⟨C.gates ++ NG, o⟩

theorem main_aux : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (T L : Finset ℕ) (i₁ i₂ a b c : ℕ),
  (PEqualNP.TopForm.IsAO2 n C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧ PEqualNP.MetaComplexity.NestedCover.IsOrTree n C T L C.output ∧
  n + i₁ ∈ L ∧ n + i₂ ∈ L ∧ i₁ ≠ i₂ ∧
  (PEqualNP.MetaComplexity.NestedCover.gateAt C i₁).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C i₁).inputs = [a, b] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C i₁).inputs = [b, a]) ∧
  (PEqualNP.MetaComplexity.NestedCover.gateAt C i₂).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C i₂).inputs = [a, c] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C i₂).inputs = [c, a]) ∧
  (∀ k < C.gates.length, k ∉ T → n + i₁ ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs ∧ n + i₂ ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs ∧
    ∀ j ∈ T, n + j ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs)) →
  ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n D ∧
  PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.circuitFun n C ∧ D.size + 1 ≤ C.size := by
  intro n C T L i₁ i₂ a b c h
  obtain ⟨hAO, hRB, htree, hi1L, hi2L, hne, hop1, hin1, hop2, hin2, hout⟩ := h
  have hao := hAO.1
  have hlen2 := hAO.2.2
  have hTlt : ∀ j ∈ T, j < C.gates.length := by
    intro j hj
    by_contra hge
    have h2 := (htree.1 j hj).2.1
    have e : gateAt C j = ⟨GateOp.or, []⟩ := by
      unfold gateAt
      exact List.getD_eq_default _ _ (by omega)
    rw [e] at h2
    have h2' : (0 : ℕ) = 2 := h2
    omega
  have hi1lt : i₁ < C.gates.length := by
    by_contra hge
    have e : gateAt C i₁ = ⟨GateOp.or, []⟩ := by
      unfold gateAt
      exact List.getD_eq_default _ _ (by omega)
    rw [e] at hop1
    have hop1' : GateOp.or = GateOp.and := hop1
    cases hop1'
  have hi2lt : i₂ < C.gates.length := by
    by_contra hge
    have e : gateAt C i₂ = ⟨GateOp.or, []⟩ := by
      unfold gateAt
      exact List.getD_eq_default _ _ (by omega)
    rw [e] at hop2
    have hop2' : GateOp.or = GateOp.and := hop2
    cases hop2'
  have hi1T : i₁ ∉ T := by
    intro hin
    exact (htree.2.1 _ hi1L).1 ⟨Nat.le_add_right _ _, by rw [Nat.add_sub_cancel_left]; exact hin⟩
  have hi2T : i₂ ∉ T := by
    intro hin
    exact (htree.2.1 _ hi2L).1 ⟨Nat.le_add_right _ _, by rw [Nat.add_sub_cancel_left]; exact hin⟩
  have hTne : T ≠ ∅ := by
    intro hT
    have hr := htree.2.2.2
    rw [if_pos hT] at hr
    have h1 : n + i₁ = C.output := by
      rw [hr] at hi1L
      exact Finset.mem_singleton.mp hi1L
    have h2 : n + i₂ = C.output := by
      rw [hr] at hi2L
      exact Finset.mem_singleton.mp hi2L
    omega
  have hroot : ∃ j ∈ T, C.output = n + j := by
    have hr := htree.2.2.2
    rw [if_neg hTne] at hr
    exact hr
  obtain ⟨j0, hj0, hρ⟩ := hroot
  have hLlt : ∀ w ∈ L, w < n + C.gates.length := by
    intro w hw
    have hwρ : w ≠ C.output := by
      intro e
      apply (htree.2.1 w hw).1
      rw [e, hρ]
      exact ⟨Nat.le_add_right _ _, by rw [Nat.add_sub_cancel_left]; exact hj0⟩
    have hr := (htree.2.1 w hw).2
    rw [if_neg hwρ] at hr
    have hex : ∃ j ∈ T, w ∈ (gateAt C j).inputs := by
      by_contra hno
      have h0 : readsIn C T w = 0 :=
        Finset.sum_eq_zero (fun j hj => List.count_eq_zero.mpr (fun hm => hno ⟨j, hj, hm⟩))
      omega
    obtain ⟨j, hj, hmem⟩ := hex
    have := hRB j (hTlt j hj) w hmem
    have := hTlt j hj
    omega
  have ha1 : a ∈ (gateAt C i₁).inputs ∧ b ∈ (gateAt C i₁).inputs := by
    rcases hin1 with e | e <;> rw [e] <;> simp
  have ha2 : a ∈ (gateAt C i₂).inputs ∧ c ∈ (gateAt C i₂).inputs := by
    rcases hin2 with e | e <;> rw [e] <;> simp
  have halt : a < n + i₁ := hRB i₁ hi1lt a ha1.1
  have hblt : b < n + i₁ := hRB i₁ hi1lt b ha1.2
  have hclt : c < n + i₂ := hRB i₂ hi2lt c ha2.2
  obtain ⟨S, hSdef⟩ : ∃ S : Finset ℕ, S = insert i₁ (insert i₂ T) := ⟨_, rfl⟩
  have hSmem : ∀ j, j ∈ S ↔ (j = i₁ ∨ j = i₂ ∨ j ∈ T) := by
    intro j
    rw [hSdef, Finset.mem_insert, Finset.mem_insert]
  have hnm : i₁ ∉ insert i₂ T := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact hne h
    · exact hi1T h
  have hScard : S.card = T.card + 1 + 1 := by
    rw [hSdef, Finset.card_insert_of_notMem hnm, Finset.card_insert_of_notMem hi2T]
  have hSlt : ∀ j ∈ S, j < C.gates.length := by
    intro j hj
    rcases (hSmem j).mp hj with e | e | e
    · rw [e]; exact hi1lt
    · rw [e]; exact hi2lt
    · exact hTlt j e
  have good_of : ∀ k < C.gates.length, k ∉ T →
      ∀ i ∈ (gateAt C k).inputs, i < n ∨ i - n ∉ S := by
    intro k hk hkT i hi
    obtain ⟨h1, h2, h3⟩ := hout k hk hkT
    by_cases hin : i < n
    · exact Or.inl hin
    · right
      intro hS
      rcases (hSmem _).mp hS with e | e | e
      · apply h1
        have e' : n + i₁ = i := by omega
        rw [e']
        exact hi
      · apply h2
        have e' : n + i₂ = i := by omega
        rw [e']
        exact hi
      · apply h3 (i - n) e
        have e' : n + (i - n) = i := by omega
        rw [e']
        exact hi
  have ga : a < n ∨ a - n ∉ S := good_of i₁ hi1lt hi1T a ha1.1
  have gb : b < n ∨ b - n ∉ S := good_of i₁ hi1lt hi1T b ha1.2
  have gc : c < n ∨ c - n ∉ S := good_of i₂ hi2lt hi2T c ha2.2
  obtain ⟨Lo, hLo⟩ : ∃ Lo : List ℕ, Lo = ((L.erase (n + i₁)).erase (n + i₂)).toList := ⟨_, rfl⟩
  have hLomem : ∀ w, w ∈ Lo ↔ (w ≠ n + i₂ ∧ w ≠ n + i₁ ∧ w ∈ L) := by
    intro w
    rw [hLo, Finset.mem_toList, Finset.mem_erase, Finset.mem_erase]
  have hcard := tree_card n C T L C.output htree
  have hTpos : 0 < T.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hTne)
  have hLolen : Lo.length + 1 + 1 = L.card := by
    have h2 : n + i₂ ∈ L.erase (n + i₁) := Finset.mem_erase.mpr ⟨by omega, hi2L⟩
    rw [hLo, Finset.length_toList, Finset.card_erase_of_mem h2, Finset.card_erase_of_mem hi1L]
    omega
  have hLoL : ∀ w ∈ Lo, w < n + C.gates.length :=
    fun w hw => hLlt w ((hLomem w).mp hw).2.2
  obtain ⟨NG, hNG⟩ : ∃ NG : List Gate, NG = newG n C.gates.length a b c Lo := ⟨_, rfl⟩
  have hNGlen : NG.length = Lo.length + 1 + 1 := by
    rw [hNG]
    exact newG_len _ _ _ _ _ _
  have hNGmem : ∀ g ∈ NG, g = ⟨GateOp.or, [b, c]⟩ ∨ g = ⟨GateOp.and, [a, n + C.gates.length]⟩ ∨
      ∃ a2 w, n + C.gates.length + 1 ≤ a2 ∧ w ∈ Lo ∧ g = ⟨GateOp.or, [a2, w]⟩ := by
    intro g hg
    rw [hNG] at hg
    exact newG_mem _ _ _ _ _ _ g hg
  have hRB' : RBo n C.gates := hRB
  have hbig : PEqualNP.TopForm.IsAO2 n (bigC C NG (n + C.gates.length + 1 + Lo.length)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      have hg' : g ∈ C.gates ++ NG := hg
      rcases List.mem_append.mp hg' with h | h
      · exact hao g h
      · rcases hNGmem g h with e | e | ⟨a2, w, _, _, e⟩
        · subst e
          exact Or.inr rfl
        · subst e
          exact Or.inl rfl
        · subst e
          exact Or.inr rfl
    · have hrb : RBo n (C.gates ++ NG) := by
        refine RBo_append n C.gates NG hRB' ?_
        rw [hNG]
        exact newG_rb n C.gates.length a b c Lo (by omega) (by omega) (by omega) hLoL
      exact hrb
    · intro g hg
      have hg' : g ∈ C.gates ++ NG := hg
      rcases List.mem_append.mp hg' with h | h
      · exact hlen2 g h
      · rcases hNGmem g h with e | e | ⟨a2, w, _, _, e⟩
        · subst e
          rfl
        · subst e
          rfl
        · subst e
          rfl
  have hcl : ∀ k < (bigC C NG (n + C.gates.length + 1 + Lo.length)).gates.length, k ∉ S →
      ∀ i ∈ (gateAt (bigC C NG (n + C.gates.length + 1 + Lo.length)) k).inputs,
        i < n ∨ i - n ∉ S := by
    intro k hk hkS i hi
    have hk' : k < (C.gates ++ NG).length := hk
    have hi' : i ∈ ((C.gates ++ NG).getD k ⟨GateOp.or, []⟩).inputs := hi
    by_cases hkl : k < C.gates.length
    · rw [List.getD_append _ _ _ _ hkl] at hi'
      exact good_of k hkl (fun h => hkS ((hSmem k).mpr (Or.inr (Or.inr h)))) i hi'
    · have hbigw : ∀ v, n + C.gates.length ≤ v → (v < n ∨ v - n ∉ S) := by
        intro v hv
        right
        intro hS2
        have := hSlt _ hS2
        omega
      rw [List.length_append] at hk'
      have hge : C.gates.length ≤ k := by omega
      have hlt2 : k - C.gates.length < NG.length := by omega
      rw [List.getD_append_right _ _ _ _ hge, List.getD_eq_getElem _ _ hlt2] at hi'
      obtain ⟨g, hgm, hgi⟩ : ∃ g ∈ NG, i ∈ g.inputs := ⟨_, List.getElem_mem hlt2, hi'⟩
      rcases hNGmem g hgm with e | e | ⟨a2, w, ha2, hw, e⟩
      · subst e
        have hgi' : i = b ∨ i = c := by simpa using hgi
        rcases hgi' with e1 | e1
        · rw [e1]; exact gb
        · rw [e1]; exact gc
      · subst e
        have hgi' : i = a ∨ i = n + C.gates.length := by simpa using hgi
        rcases hgi' with e1 | e1
        · rw [e1]; exact ga
        · rw [e1]; exact hbigw _ le_rfl
      · subst e
        have hgi' : i = a2 ∨ i = w := by simpa using hgi
        rcases hgi' with e1 | e1
        · rw [e1]; exact hbigw _ (by omega)
        · rw [e1]
          obtain ⟨hw2, hw1, hwL⟩ := (hLomem w).mp hw
          by_cases hwn : w < n
          · exact Or.inl hwn
          · right
            intro hS2
            rcases (hSmem _).mp hS2 with e2 | e2 | e2
            · exact hw1 (by omega)
            · exact hw2 (by omega)
            · exact (htree.2.1 w hwL).1 ⟨by omega, e2⟩
  have hfun : circuitFun n (bigC C NG (n + C.gates.length + 1 + Lo.length)) = circuitFun n C := by
    funext x
    have h1 := newG_val n C a b c Lo x (by omega) hLoL
    have h2 := orTree_eval_iff hRB hTlt htree x
    have hg1 : wval C x (n + i₁) = (wval C x a && wval C x b) := by
      have hw := wval_gate C hRB x i₁ hi1lt
      rw [hop1] at hw
      rcases hin1 with e | e
      · rw [e] at hw
        exact hw.trans (and2v _ _)
      · rw [e] at hw
        exact hw.trans ((and2v _ _).trans (Bool.and_comm _ _))
    have hg2 : wval C x (n + i₂) = (wval C x a && wval C x c) := by
      have hw := wval_gate C hRB x i₂ hi2lt
      rw [hop2] at hw
      rcases hin2 with e | e
      · rw [e] at hw
        exact hw.trans (and2v _ _)
      · rw [e] at hw
        exact hw.trans ((and2v _ _).trans (Bool.and_comm _ _))
    show (wiresFrom (C.gates ++ NG) (List.ofFn x)).getD
      (n + C.gates.length + 1 + Lo.length) false = wval C x C.output
    rw [hNG, Bool.eq_iff_iff, h1, h2]
    constructor
    · rintro (⟨ha', hb' | hc'⟩ | ⟨w, hw, hwv⟩)
      · exact ⟨n + i₁, hi1L, by rw [hg1, Bool.and_eq_true]; exact ⟨ha', hb'⟩⟩
      · exact ⟨n + i₂, hi2L, by rw [hg2, Bool.and_eq_true]; exact ⟨ha', hc'⟩⟩
      · exact ⟨w, ((hLomem w).mp hw).2.2, hwv⟩
    · rintro ⟨w, hw, hwv⟩
      by_cases e1 : w = n + i₁
      · rw [e1, hg1, Bool.and_eq_true] at hwv
        exact Or.inl ⟨hwv.1, Or.inl hwv.2⟩
      · by_cases e2 : w = n + i₂
        · rw [e2, hg2, Bool.and_eq_true] at hwv
          exact Or.inl ⟨hwv.1, Or.inr hwv.2⟩
        · exact Or.inr ⟨w, (hLomem w).mpr ⟨e2, e1, hw⟩, hwv⟩
  have hSlt' : ∀ j ∈ S, j < (bigC C NG (n + C.gates.length + 1 + Lo.length)).gates.length := by
    intro j hj
    have := hSlt j hj
    show j < (C.gates ++ NG).length
    rw [List.length_append]
    omega
  have ho : C.gates.length + 1 + Lo.length <
      (bigC C NG (n + C.gates.length + 1 + Lo.length)).gates.length := by
    show _ < (C.gates ++ NG).length
    rw [List.length_append, hNGlen]
    omega
  have hoS : C.gates.length + 1 + Lo.length ∉ S := by
    intro h
    have := hSlt _ h
    omega
  have hout' : (bigC C NG (n + C.gates.length + 1 + Lo.length)).output =
      n + (C.gates.length + 1 + Lo.length) := by
    show n + C.gates.length + 1 + Lo.length = n + (C.gates.length + 1 + Lo.length)
    omega
  obtain ⟨D, hD, hDf, hDs⟩ := restrict n _ S hbig hcl hSlt' _ ho hoS hout'
  refine ⟨D, hD, hDf.trans hfun, ?_⟩
  have hsz : (bigC C NG (n + C.gates.length + 1 + Lo.length)).size =
      C.gates.length + (Lo.length + 1 + 1) := by
    show (C.gates ++ NG).length = _
    rw [List.length_append, hNGlen]
  rw [hsz] at hDs
  show D.size + 1 ≤ C.gates.length
  omega

end PEqualNP.Outside.L_meta_2774

theorem PEqualNP.Outside.L_meta_2774 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (T L : Finset ℕ) (i₁ i₂ a b c : ℕ),
  (PEqualNP.TopForm.IsAO2 n C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧ PEqualNP.MetaComplexity.NestedCover.IsOrTree n C T L C.output ∧
  n + i₁ ∈ L ∧ n + i₂ ∈ L ∧ i₁ ≠ i₂ ∧
  (PEqualNP.MetaComplexity.NestedCover.gateAt C i₁).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C i₁).inputs = [a, b] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C i₁).inputs = [b, a]) ∧
  (PEqualNP.MetaComplexity.NestedCover.gateAt C i₂).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C i₂).inputs = [a, c] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C i₂).inputs = [c, a]) ∧
  (∀ k < C.gates.length, k ∉ T → n + i₁ ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs ∧ n + i₂ ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs ∧
    ∀ j ∈ T, n + j ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs)) →
  ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n D ∧
  PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.circuitFun n C ∧ D.size + 1 ≤ C.size :=
  PEqualNP.Outside.L_meta_2774.main_aux
