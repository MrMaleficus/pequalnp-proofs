import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2908

open PEqualNP.MetaComplexity

theorem cc {P L : ℕ} {q p : Fin P} (h : Fin.castAdd L q = Fin.castAdd L p) : q = p := by
  have := congrArg Fin.val h
  exact Fin.ext (by simpa using this)

theorem nn {P L : ℕ} {l' l : Fin L} (h : Fin.natAdd P l' = Fin.natAdd P l) : l' = l := by
  have := congrArg Fin.val h
  exact Fin.ext (by simpa using this)

theorem cn {P L : ℕ} (q : Fin P) (l : Fin L) : Fin.castAdd L q ≠ Fin.natAdd P l := by
  intro h
  have := congrArg Fin.val h
  simp at this
  have := q.isLt
  omega

theorem memL {α : Type*} [DecidableEq α] {x : α} {S1 S2 D1 D2 : Finset α} (h : x ∉ D1) :
    x ∈ S1 → x ∈ (S1 \ D1) ∪ (S2 \ D2) :=
  fun hx => Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, h⟩)

theorem memR {α : Type*} [DecidableEq α] {x : α} {S1 S2 D1 D2 : Finset α} (h : x ∉ D2) :
    x ∈ S2 → x ∈ (S1 \ D1) ∪ (S2 \ D2) :=
  fun hx => Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx, h⟩)

theorem nf {α : Type*} {S : Finset α} {q : α → Prop} [DecidablePred q] {x : α} (h : ¬ q x) :
    x ∉ S.filter q :=
  fun hx => h (Finset.mem_filter.mp hx).2

theorem ne0 {α : Type*} {x : α} : x ∉ (∅ : Finset α) := fun hx => by simp at hx

theorem or_count {α β γ : Type*} [DecidableEq β] [DecidableEq γ] (G A : Finset α)
    (c d : α → Prop) [DecidablePred c] [DecidablePred d] (fst : α → β) (snd : α → γ)
    (TP1 TP2 : Finset β) (TL1 TL2 : Finset γ) (a1 a2 s1 s2 : ℕ)
    (hA : A ⊆ (G.filter c).filter d) (hG : G.card ≤ a1 + a2)
    (b1 : a1 + TP1.card + TL1.card ≤ s1) (b2 : a2 + TP2.card + TL2.card ≤ s2) :
    A.card + (TP1 ∪ TP2 ∪ (G.filter (fun x => ¬ c x)).image fst).card +
      (TL1 ∪ TL2 ∪ ((G.filter c).filter (fun x => ¬ d x)).image snd).card ≤ s1 + s2 := by
  have h1 := Finset.card_filter_add_card_filter_not (s := G) c
  have h2 := Finset.card_filter_add_card_filter_not (s := G.filter c) d
  have h3 := Finset.card_le_card hA
  have h4 := Finset.card_image_le (s := G.filter (fun x => ¬ c x)) (f := fst)
  have h5 := Finset.card_image_le (s := (G.filter c).filter (fun x => ¬ d x)) (f := snd)
  have h6 := Finset.card_union_le (TP1 ∪ TP2) ((G.filter (fun x => ¬ c x)).image fst)
  have h7 := Finset.card_union_le TP1 TP2
  have h8 := Finset.card_union_le (TL1 ∪ TL2) (((G.filter c).filter (fun x => ¬ d x)).image snd)
  have h9 := Finset.card_union_le TL1 TL2
  omega

theorem and_count {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (A A1 A2 C12 C21 : Finset α) (TP1 TP2 DP1 DP2 : Finset β) (TL1 TL2 DL1 DL2 : Finset γ)
    (s1 s2 : ℕ) (hsub : A ⊆ A1 ∪ A2 ∪ C12 ∪ C21)
    (b1 : A1.card + TP1.card + TL1.card ≤ s1) (b2 : A2.card + TP2.card + TL2.card ≤ s2)
    (hP1 : DP1 ⊆ TP1) (hP2 : DP2 ⊆ TP2) (hL1 : DL1 ⊆ TL1) (hL2 : DL2 ⊆ TL2)
    (h12 : C12.card ≤ DL2.card + DP1.card) (h21 : C21.card ≤ DL1.card + DP2.card) :
    A.card + ((TP1 \ DP1) ∪ (TP2 \ DP2)).card + ((TL1 \ DL1) ∪ (TL2 \ DL2)).card ≤ s1 + s2 := by
  have e1 := Finset.card_sdiff_add_card_eq_card hP1
  have e2 := Finset.card_sdiff_add_card_eq_card hP2
  have e3 := Finset.card_sdiff_add_card_eq_card hL1
  have e4 := Finset.card_sdiff_add_card_eq_card hL2
  have u1 := Finset.card_union_le (TP1 \ DP1) (TP2 \ DP2)
  have u2 := Finset.card_union_le (TL1 \ DL1) (TL2 \ DL2)
  have c := Finset.card_le_card hsub
  have v1 := Finset.card_union_le (A1 ∪ A2 ∪ C12) C21
  have v2 := Finset.card_union_le (A1 ∪ A2) C12
  have v3 := Finset.card_union_le A1 A2
  omega

variable {P L : ℕ} (I : Fin P → Fin L → Prop) [DecidableRel I]

def bp (z : Fin L → Bool) (p : Fin P) : Bool := decide (∃ m, ¬ I p m ∧ z m = false)

theorem bp_iff (z : Fin L → Bool) (p : Fin P) :
    bp I z p = true ↔ ∃ m, ¬ I p m ∧ z m = false := by
  unfold bp
  exact decide_eq_true_iff

theorem bp_mono {z1 z : Fin L → Bool} (hz : ∀ m, z1 m = false → z m = false) {p : Fin P}
    (h : bp I z1 p = true) : bp I z p = true := by
  obtain ⟨m, hm, hzm⟩ := (bp_iff I z1 p).mp h
  exact (bp_iff I z p).mpr ⟨m, hm, hz m hzm⟩

theorem of_not_bp {z : Fin L → Bool} {p : Fin P} (h : ¬ bp I z p = true) (m : Fin L)
    (hm : z m = false) : I p m := by
  by_contra hc
  exact h ((bp_iff I z p).mpr ⟨m, hc, hm⟩)

def Cov (t : Fin P × Fin L → Bool) (z : Fin L → Bool) (TP : Finset (Fin P))
    (TL : Finset (Fin L)) : Prop :=
  ∀ p l, I p l → t (p, l) = true →
    (z l = false → p ∈ TP ∨ (bp I z p = true ∧ l ∈ TL)) ∧
    (bp I z p = true → l ∈ TL ∨ (z l = false ∧ p ∈ TP))

def AB (t : Fin P × Fin L → Bool) (z : Fin L → Bool) : Finset (Fin P × Fin L) :=
  Finset.univ.filter (fun f => I f.1 f.2 ∧ t f = true ∧ z f.2 = false ∧ bp I z f.1 = true)

def Good (t : Fin P × Fin L → Bool) (z : Fin L → Bool) (s : ℕ) : Prop :=
  ∃ TP : Finset (Fin P), ∃ TL : Finset (Fin L),
    Cov I t z TP TL ∧ (AB I t z).card + TP.card + TL.card ≤ s

def Gor (t1 t2 : Fin P × Fin L → Bool) (z1 z2 : Fin L → Bool) : Finset (Fin P × Fin L) :=
  Finset.univ.filter (fun f => I f.1 f.2 ∧
    ((t1 f = true ∧ z1 f.2 = false ∧ bp I z1 f.1 = true) ∨
     (t1 f = false ∧ t2 f = true ∧ z2 f.2 = false ∧ bp I z2 f.1 = true)))

def Cx (ta tb : Fin P × Fin L → Bool) (za zb : Fin L → Bool) : Finset (Fin P × Fin L) :=
  Finset.univ.filter (fun f => I f.1 f.2 ∧ ta f = true ∧ tb f = true ∧ za f.2 = false ∧
    ¬ bp I za f.1 = true ∧ bp I zb f.1 = true ∧ zb f.2 = true)

theorem good_pt (t : Fin P × Fin L → Bool) (z : Fin L → Bool) (q : Fin P)
    (ht : ∀ p l, t (p, l) = true → p = q) (hz : ∀ m, z m = false → I q m) : Good I t z 1 := by
  have nb : ∀ p l, t (p, l) = true → ¬ bp I z p = true := by
    intro p l h hb
    obtain ⟨m, hm, hzm⟩ := (bp_iff I z p).mp hb
    rw [ht p l h] at hm
    exact hm (hz m hzm)
  refine ⟨{q}, ∅, ?_, ?_⟩
  · intro p l _ h
    refine ⟨fun _ => Or.inl ?_, fun hb => absurd hb (nb p l h)⟩
    rw [ht p l h]
    exact Finset.mem_singleton_self q
  · have e : AB I t z = ∅ := by
      ext f
      simp only [AB, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨_, h1, _, h3⟩
        exact absurd h3 (nb f.1 f.2 h1)
      · intro h
        simp at h
    rw [e]
    simp

theorem good_ln (t : Fin P × Fin L → Bool) (z : Fin L → Bool) (l0 : Fin L)
    (ht : ∀ p l, t (p, l) = true → l = l0) (hz : z l0 = true) : Good I t z 1 := by
  refine ⟨∅, {l0}, ?_, ?_⟩
  · intro p l _ h
    have e := ht p l h
    refine ⟨fun h2 => ?_, fun _ => Or.inl ?_⟩
    · rw [e, hz] at h2
      simp at h2
    · rw [e]
      exact Finset.mem_singleton_self _
  · have e : AB I t z = ∅ := by
      ext f
      simp only [AB, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨_, h1, h2, _⟩
        rw [ht f.1 f.2 h1, hz] at h2
        simp at h2
      · intro h
        simp at h
    rw [e]
    simp

theorem gor_card (t1 t2 : Fin P × Fin L → Bool) (z1 z2 : Fin L → Bool) :
    (Gor I t1 t2 z1 z2).card ≤ (AB I t1 z1).card + (AB I t2 z2).card := by
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro f hf
  simp only [Gor, AB, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hf ⊢
  rcases hf with ⟨hI, ⟨a, b, c⟩ | ⟨_, a, b, c⟩⟩
  · exact Or.inl ⟨hI, a, b, c⟩
  · exact Or.inr ⟨hI, a, b, c⟩

theorem good_or (t1 t2 : Fin P × Fin L → Bool) (z1 z2 : Fin L → Bool) (s1 s2 : ℕ)
    (g1 : Good I t1 z1 s1) (g2 : Good I t2 z2 s2) :
    Good I (fun f => t1 f || t2 f) (fun m => z1 m || z2 m) (s1 + s2) := by
  obtain ⟨TP1, TL1, c1, b1⟩ := g1
  obtain ⟨TP2, TL2, c2, b2⟩ := g2
  have m1 : ∀ {p : Fin P}, bp I (fun m => z1 m || z2 m) p = true → bp I z1 p = true :=
    fun h => bp_mono I (z1 := fun m => z1 m || z2 m) (z := z1)
      (fun m h' => (Bool.or_eq_false_iff.mp h').1) h
  have m2 : ∀ {p : Fin P}, bp I (fun m => z1 m || z2 m) p = true → bp I z2 p = true :=
    fun h => bp_mono I (z1 := fun m => z1 m || z2 m) (z := z2)
      (fun m h' => (Bool.or_eq_false_iff.mp h').2) h
  refine ⟨TP1 ∪ TP2 ∪ ((Gor I t1 t2 z1 z2).filter
      (fun f => ¬ bp I (fun m => z1 m || z2 m) f.1 = true)).image Prod.fst,
    TL1 ∪ TL2 ∪ (((Gor I t1 t2 z1 z2).filter
      (fun f => bp I (fun m => z1 m || z2 m) f.1 = true)).filter
      (fun f => ¬ (z1 f.2 || z2 f.2) = false)).image Prod.snd, ?_, ?_⟩
  · intro p l hI ht
    have ht' : (t1 (p, l) || t2 (p, l)) = true := ht
    by_cases h1 : t1 (p, l) = true
    · obtain ⟨ca, cb⟩ := c1 p l hI h1
      constructor
      · intro hz
        have hz' : (z1 l || z2 l) = false := hz
        have hz1 : z1 l = false := (Bool.or_eq_false_iff.mp hz').1
        rcases ca hz1 with hp | ⟨hb, hl⟩
        · exact Or.inl (Finset.mem_union_left _ (Finset.mem_union_left _ hp))
        · by_cases hbz : bp I (fun m => z1 m || z2 m) p = true
          · exact Or.inr ⟨hbz, Finset.mem_union_left _ (Finset.mem_union_left _ hl)⟩
          · refine Or.inl (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(p, l), ?_, rfl⟩))
            simp only [Gor, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨⟨hI, Or.inl ⟨h1, hz1, hb⟩⟩, hbz⟩
      · intro hbz
        have hb1 := m1 hbz
        rcases cb hb1 with hl | ⟨hz1, hp⟩
        · exact Or.inl (Finset.mem_union_left _ (Finset.mem_union_left _ hl))
        · by_cases hzz : (z1 l || z2 l) = false
          · exact Or.inr ⟨hzz, Finset.mem_union_left _ (Finset.mem_union_left _ hp)⟩
          · refine Or.inl (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(p, l), ?_, rfl⟩))
            simp only [Gor, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨⟨⟨hI, Or.inl ⟨h1, hz1, hb1⟩⟩, hbz⟩, hzz⟩
    · have h1f : t1 (p, l) = false := by simpa using h1
      have h2 : t2 (p, l) = true := by
        rw [h1f] at ht'
        simpa using ht'
      obtain ⟨ca, cb⟩ := c2 p l hI h2
      constructor
      · intro hz
        have hz' : (z1 l || z2 l) = false := hz
        have hz2 : z2 l = false := (Bool.or_eq_false_iff.mp hz').2
        rcases ca hz2 with hp | ⟨hb, hl⟩
        · exact Or.inl (Finset.mem_union_left _ (Finset.mem_union_right _ hp))
        · by_cases hbz : bp I (fun m => z1 m || z2 m) p = true
          · exact Or.inr ⟨hbz, Finset.mem_union_left _ (Finset.mem_union_right _ hl)⟩
          · refine Or.inl (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(p, l), ?_, rfl⟩))
            simp only [Gor, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨⟨hI, Or.inr ⟨h1f, h2, hz2, hb⟩⟩, hbz⟩
      · intro hbz
        have hb2 := m2 hbz
        rcases cb hb2 with hl | ⟨hz2, hp⟩
        · exact Or.inl (Finset.mem_union_left _ (Finset.mem_union_right _ hl))
        · by_cases hzz : (z1 l || z2 l) = false
          · exact Or.inr ⟨hzz, Finset.mem_union_left _ (Finset.mem_union_right _ hp)⟩
          · refine Or.inl (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(p, l), ?_, rfl⟩))
            simp only [Gor, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨⟨⟨hI, Or.inr ⟨h1f, h2, hz2, hb2⟩⟩, hbz⟩, hzz⟩
  · have hAB : AB I (fun f => t1 f || t2 f) (fun m => z1 m || z2 m) ⊆
        ((Gor I t1 t2 z1 z2).filter (fun f => bp I (fun m => z1 m || z2 m) f.1 = true)).filter
          (fun f => (z1 f.2 || z2 f.2) = false) := by
      intro f hf
      simp only [AB, Gor, Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
      obtain ⟨hI, ht, hz, hb⟩ := hf
      have hz' : (z1 f.2 || z2 f.2) = false := hz
      refine ⟨⟨⟨hI, ?_⟩, hb⟩, hz'⟩
      have hz1 := (Bool.or_eq_false_iff.mp hz').1
      have hz2 := (Bool.or_eq_false_iff.mp hz').2
      by_cases h1 : t1 f = true
      · exact Or.inl ⟨h1, hz1, m1 hb⟩
      · have h1f : t1 f = false := by simpa using h1
        have ht' : (t1 f || t2 f) = true := ht
        have h2 : t2 f = true := by
          rw [h1f] at ht'
          simpa using ht'
        exact Or.inr ⟨h1f, h2, hz2, m2 hb⟩
    exact or_count (Gor I t1 t2 z1 z2) _ (fun f => bp I (fun m => z1 m || z2 m) f.1 = true)
      (fun f => (z1 f.2 || z2 f.2) = false) Prod.fst Prod.snd TP1 TP2 TL1 TL2 _ _ s1 s2 hAB
      (gor_card I t1 t2 z1 z2) b1 b2

theorem handled (t1 : Fin P × Fin L → Bool) (z1 z : Fin L → Bool) (TP1 TP : Finset (Fin P))
    (TL1 TL : Finset (Fin L)) (c1 : Cov I t1 z1 TP1 TL1) (hz : ∀ m, z1 m = false → z m = false)
    (p : Fin P) (l : Fin L) (hI : I p l) (ht : t1 (p, l) = true)
    (hs : z1 l = false ∨ bp I z1 p = true) (hP : p ∈ TP1 → p ∈ TP) (hL : l ∈ TL1 → l ∈ TL) :
    (z l = false → p ∈ TP ∨ (bp I z p = true ∧ l ∈ TL)) ∧
    (bp I z p = true → l ∈ TL ∨ (z l = false ∧ p ∈ TP)) := by
  obtain ⟨ca, cb⟩ := c1 p l hI ht
  have mono : bp I z1 p = true → bp I z p = true := fun h => bp_mono I hz h
  constructor
  · intro _
    by_cases e : z1 l = false
    · rcases ca e with h | ⟨hb, hl⟩
      · exact Or.inl (hP h)
      · exact Or.inr ⟨mono hb, hL hl⟩
    · have hb : bp I z1 p = true := by
        rcases hs with h | h
        · exact absurd h e
        · exact h
      rcases cb hb with hl | ⟨h, _⟩
      · exact Or.inr ⟨mono hb, hL hl⟩
      · exact absurd h e
  · intro _
    by_cases hb : bp I z1 p = true
    · rcases cb hb with hl | ⟨h, hp⟩
      · exact Or.inl (hL hl)
      · exact Or.inr ⟨hz l h, hP hp⟩
    · have e : z1 l = false := by
        rcases hs with h | h
        · exact h
        · exact absurd h hb
      rcases ca e with hp | ⟨h, _⟩
      · exact Or.inr ⟨hz l e, hP hp⟩
      · exact absurd h hb

theorem cov_sides (t1 t2 : Fin P × Fin L → Bool) (z1 z2 : Fin L → Bool)
    (TP1 : Finset (Fin P)) (TL1 : Finset (Fin L)) (TP2 : Finset (Fin P)) (TL2 : Finset (Fin L))
    (TP : Finset (Fin P)) (TL : Finset (Fin L))
    (c1 : Cov I t1 z1 TP1 TL1) (c2 : Cov I t2 z2 TP2 TL2)
    (hside : ∀ p l, I p l → t1 (p, l) = true → t2 (p, l) = true →
      ((z1 l = false ∨ bp I z1 p = true) ∨ (z2 l = false ∨ bp I z2 p = true)) →
      ((z1 l = false ∨ bp I z1 p = true) ∧ (p ∈ TP1 → p ∈ TP) ∧ (l ∈ TL1 → l ∈ TL)) ∨
      ((z2 l = false ∨ bp I z2 p = true) ∧ (p ∈ TP2 → p ∈ TP) ∧ (l ∈ TL2 → l ∈ TL))) :
    Cov I (fun f => t1 f && t2 f) (fun m => z1 m && z2 m) TP TL := by
  intro p l hI ht
  have ht' : (t1 (p, l) && t2 (p, l)) = true := ht
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp ht'
  have hS : ((z1 l && z2 l) = false ∨ bp I (fun m => z1 m && z2 m) p = true) →
      ((z1 l = false ∨ bp I z1 p = true) ∨ (z2 l = false ∨ bp I z2 p = true)) := by
    rintro (h | h)
    · rcases Bool.and_eq_false_iff.mp h with e | e
      · exact Or.inl (Or.inl e)
      · exact Or.inr (Or.inl e)
    · obtain ⟨m, hm, hzm⟩ := (bp_iff I _ _).mp h
      have hzm' : (z1 m && z2 m) = false := hzm
      rcases Bool.and_eq_false_iff.mp hzm' with e | e
      · exact Or.inl (Or.inr ((bp_iff I _ _).mpr ⟨m, hm, e⟩))
      · exact Or.inr (Or.inr ((bp_iff I _ _).mpr ⟨m, hm, e⟩))
  have k1 : ∀ m, z1 m = false → (fun m => z1 m && z2 m) m = false := by
    intro m h
    simp [h]
  have k2 : ∀ m, z2 m = false → (fun m => z1 m && z2 m) m = false := by
    intro m h
    simp [h]
  constructor
  · intro hz
    have hz' : (z1 l && z2 l) = false := hz
    rcases hside p l hI h1 h2 (hS (Or.inl hz')) with ⟨s, hP, hL⟩ | ⟨s, hP, hL⟩
    · exact (handled I t1 z1 _ TP1 TP TL1 TL c1 k1 p l hI h1 s hP hL).1 hz
    · exact (handled I t2 z2 _ TP2 TP TL2 TL c2 k2 p l hI h2 s hP hL).1 hz
  · intro hb
    rcases hside p l hI h1 h2 (hS (Or.inr hb)) with ⟨s, hP, hL⟩ | ⟨s, hP, hL⟩
    · exact (handled I t1 z1 _ TP1 TP TL1 TL c1 k1 p l hI h1 s hP hL).2 hb
    · exact (handled I t2 z2 _ TP2 TP TL2 TL c2 k2 p l hI h2 s hP hL).2 hb

theorem count_lines
    (hlin : ∀ l l' : Fin L, l ≠ l' → ∀ p p' : Fin P, I p l → I p l' → I p' l → I p' l' → p = p')
    (ta tb : Fin P × Fin L → Bool) (za zb : Fin L → Bool) (TPb : Finset (Fin P))
    (TLb : Finset (Fin L)) (cb : Cov I tb zb TPb TLb)
    (h : ∃ a b, a ≠ b ∧ za a = false ∧ za b = false) :
    (Cx I ta tb za zb).card ≤ (TLb.filter (fun l => za l = false ∧ zb l = true)).card := by
  obtain ⟨a, b, hab, ha, hb⟩ := h
  apply Finset.card_le_card_of_injOn Prod.snd
  · intro f hf
    simp only [Finset.mem_coe, Cx, Finset.mem_filter, Finset.mem_univ, true_and] at hf
    obtain ⟨hI, _, htb, hza, _, hbb, hzb⟩ := hf
    simp only [Finset.mem_coe, Finset.mem_filter]
    refine ⟨?_, hza, hzb⟩
    rcases (cb f.1 f.2 hI htb).2 hbb with hl | ⟨h, _⟩
    · exact hl
    · rw [hzb] at h
      simp at h
  · intro f hf g hg hfg
    simp only [Finset.mem_coe, Cx, Finset.mem_filter, Finset.mem_univ, true_and] at hf hg
    obtain ⟨_, _, _, _, hnf, _, _⟩ := hf
    obtain ⟨_, _, _, _, hng, _, _⟩ := hg
    have e2 : f.2 = g.2 := hfg
    have e1 : f.1 = g.1 := hlin a b hab f.1 g.1 (of_not_bp I hnf a ha) (of_not_bp I hnf b hb)
      (of_not_bp I hng a ha) (of_not_bp I hng b hb)
    exact Prod.ext e1 e2

theorem count_points (ta tb : Fin P × Fin L → Bool) (za zb : Fin L → Bool)
    (TPa : Finset (Fin P)) (TLa : Finset (Fin L)) (ca : Cov I ta za TPa TLa)
    (h : ¬ ∃ a b, a ≠ b ∧ za a = false ∧ za b = false) :
    (Cx I ta tb za zb).card ≤
      (TPa.filter (fun p => ¬ bp I za p = true ∧ bp I zb p = true)).card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro f hf
    simp only [Finset.mem_coe, Cx, Finset.mem_filter, Finset.mem_univ, true_and] at hf
    obtain ⟨hI, hta, _, hza, hnb, hbb, _⟩ := hf
    simp only [Finset.mem_coe, Finset.mem_filter]
    refine ⟨?_, hnb, hbb⟩
    rcases (ca f.1 f.2 hI hta).1 hza with hp | ⟨hb, _⟩
    · exact hp
    · exact absurd hb hnb
  · intro f hf g hg hfg
    simp only [Finset.mem_coe, Cx, Finset.mem_filter, Finset.mem_univ, true_and] at hf hg
    obtain ⟨_, _, _, hzf, _, _, _⟩ := hf
    obtain ⟨_, _, _, hzg, _, _, _⟩ := hg
    have e1 : f.1 = g.1 := hfg
    have e2 : f.2 = g.2 := by
      by_contra hne
      exact h ⟨f.2, g.2, hne, hzf, hzg⟩
    exact Prod.ext e1 e2

theorem and_assemble (t1 t2 : Fin P × Fin L → Bool) (z1 z2 : Fin L → Bool)
    (TP1 : Finset (Fin P)) (TL1 : Finset (Fin L)) (TP2 : Finset (Fin P)) (TL2 : Finset (Fin L))
    (DP1 DP2 : Finset (Fin P)) (DL1 DL2 : Finset (Fin L)) (s1 s2 : ℕ)
    (b1 : (AB I t1 z1).card + TP1.card + TL1.card ≤ s1)
    (b2 : (AB I t2 z2).card + TP2.card + TL2.card ≤ s2)
    (hP1 : DP1 ⊆ TP1) (hP2 : DP2 ⊆ TP2) (hL1 : DL1 ⊆ TL1) (hL2 : DL2 ⊆ TL2)
    (hcov : Cov I (fun f => t1 f && t2 f) (fun m => z1 m && z2 m)
      ((TP1 \ DP1) ∪ (TP2 \ DP2)) ((TL1 \ DL1) ∪ (TL2 \ DL2)))
    (h12 : (Cx I t1 t2 z1 z2).card ≤ DL2.card + DP1.card)
    (h21 : (Cx I t2 t1 z2 z1).card ≤ DL1.card + DP2.card) :
    Good I (fun f => t1 f && t2 f) (fun m => z1 m && z2 m) (s1 + s2) := by
  have hsub : AB I (fun f => t1 f && t2 f) (fun m => z1 m && z2 m) ⊆
      AB I t1 z1 ∪ AB I t2 z2 ∪ Cx I t1 t2 z1 z2 ∪ Cx I t2 t1 z2 z1 := by
    intro f hf
    simp only [AB, Cx, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hf ⊢
    obtain ⟨hI, ht, hz, hb⟩ := hf
    have ht' : (t1 f && t2 f) = true := ht
    have hz' : (z1 f.2 && z2 f.2) = false := hz
    obtain ⟨ht1, ht2⟩ := Bool.and_eq_true_iff.mp ht'
    have hbz : bp I z1 f.1 = true ∨ bp I z2 f.1 = true := by
      obtain ⟨m, hm, hzm⟩ := (bp_iff I _ _).mp hb
      have hzm' : (z1 m && z2 m) = false := hzm
      rcases Bool.and_eq_false_iff.mp hzm' with e | e
      · exact Or.inl ((bp_iff I _ _).mpr ⟨m, hm, e⟩)
      · exact Or.inr ((bp_iff I _ _).mpr ⟨m, hm, e⟩)
    by_cases a1 : z1 f.2 = false ∧ bp I z1 f.1 = true
    · exact Or.inl (Or.inl (Or.inl ⟨hI, ht1, a1.1, a1.2⟩))
    by_cases a2 : z2 f.2 = false ∧ bp I z2 f.1 = true
    · exact Or.inl (Or.inl (Or.inr ⟨hI, ht2, a2.1, a2.2⟩))
    rcases Bool.and_eq_false_iff.mp hz' with e | e
    · have nb1 : ¬ bp I z1 f.1 = true := fun h => a1 ⟨e, h⟩
      have b2' : bp I z2 f.1 = true := hbz.resolve_left nb1
      have z2t : z2 f.2 = true := by
        cases hh : z2 f.2
        · exact absurd ⟨hh, b2'⟩ a2
        · rfl
      exact Or.inl (Or.inr ⟨hI, ht1, ht2, e, nb1, b2', z2t⟩)
    · have nb2 : ¬ bp I z2 f.1 = true := fun h => a2 ⟨e, h⟩
      have b1' : bp I z1 f.1 = true := hbz.resolve_right nb2
      have z1t : z1 f.2 = true := by
        cases hh : z1 f.2
        · exact absurd ⟨hh, b1'⟩ a1
        · rfl
      exact Or.inr ⟨hI, ht2, ht1, e, nb2, b1', z1t⟩
  exact ⟨_, _, hcov, and_count _ _ _ _ _ TP1 TP2 DP1 DP2 TL1 TL2 DL1 DL2 s1 s2 hsub b1 b2
    hP1 hP2 hL1 hL2 h12 h21⟩

theorem good_and
    (hlin : ∀ l l' : Fin L, l ≠ l' → ∀ p p' : Fin P, I p l → I p l' → I p' l → I p' l' → p = p')
    (t1 t2 : Fin P × Fin L → Bool) (z1 z2 : Fin L → Bool) (s1 s2 : ℕ)
    (g1 : Good I t1 z1 s1) (g2 : Good I t2 z2 s2) :
    Good I (fun f => t1 f && t2 f) (fun m => z1 m && z2 m) (s1 + s2) := by
  obtain ⟨TP1, TL1, c1, b1⟩ := g1
  obtain ⟨TP2, TL2, c2, b2⟩ := g2
  by_cases h1 : ∃ a b, a ≠ b ∧ z1 a = false ∧ z1 b = false <;>
    by_cases h2 : ∃ a b, a ≠ b ∧ z2 a = false ∧ z2 b = false
  · refine and_assemble I t1 t2 z1 z2 TP1 TL1 TP2 TL2 ∅ ∅
      (TL1.filter (fun l => z2 l = false ∧ z1 l = true))
      (TL2.filter (fun l => z1 l = false ∧ z2 l = true)) s1 s2 b1 b2
      (Finset.empty_subset _) (Finset.empty_subset _) (Finset.filter_subset _ _)
      (Finset.filter_subset _ _) ?_ ?_ ?_
    · apply cov_sides I t1 t2 z1 z2 TP1 TL1 TP2 TL2 _ _ c1 c2
      intro p l _ _ _ hs
      by_cases e1 : z1 l = false ∧ z2 l = true
      · exact Or.inl ⟨Or.inl e1.1, memL ne0, memL (nf (fun h => by simp [e1.2] at h))⟩
      by_cases e2 : z2 l = false ∧ z1 l = true
      · exact Or.inr ⟨Or.inl e2.1, memR ne0, memR (nf (fun h => by simp [e2.2] at h))⟩
      rcases hs with s | s
      · exact Or.inl ⟨s, memL ne0, memL (nf e2)⟩
      · exact Or.inr ⟨s, memR ne0, memR (nf e1)⟩
    · have := count_lines I hlin t1 t2 z1 z2 TP2 TL2 c2 h1
      rw [Finset.card_empty, Nat.add_zero]
      exact this
    · have := count_lines I hlin t2 t1 z2 z1 TP1 TL1 c1 h2
      rw [Finset.card_empty, Nat.add_zero]
      exact this
  · refine and_assemble I t1 t2 z1 z2 TP1 TL1 TP2 TL2 ∅
      (TP2.filter (fun p => ¬ bp I z2 p = true ∧ bp I z1 p = true)) ∅
      (TL2.filter (fun l => z1 l = false ∧ z2 l = true)) s1 s2 b1 b2
      (Finset.empty_subset _) (Finset.filter_subset _ _) (Finset.empty_subset _)
      (Finset.filter_subset _ _) ?_ ?_ ?_
    · apply cov_sides I t1 t2 z1 z2 TP1 TL1 TP2 TL2 _ _ c1 c2
      intro p l _ _ _ hs
      by_cases s1' : z1 l = false ∨ bp I z1 p = true
      · exact Or.inl ⟨s1', memL ne0, memL ne0⟩
      · exact Or.inr ⟨hs.resolve_left s1', memR (nf (fun h => s1' (Or.inr h.2))),
          memR (nf (fun h => s1' (Or.inl h.1)))⟩
    · have := count_lines I hlin t1 t2 z1 z2 TP2 TL2 c2 h1
      rw [Finset.card_empty, Nat.add_zero]
      exact this
    · have := count_points I t2 t1 z2 z1 TP2 TL2 c2 h2
      rw [Finset.card_empty, Nat.zero_add]
      exact this
  · refine and_assemble I t1 t2 z1 z2 TP1 TL1 TP2 TL2
      (TP1.filter (fun p => ¬ bp I z1 p = true ∧ bp I z2 p = true)) ∅
      (TL1.filter (fun l => z2 l = false ∧ z1 l = true)) ∅ s1 s2 b1 b2
      (Finset.filter_subset _ _) (Finset.empty_subset _) (Finset.filter_subset _ _)
      (Finset.empty_subset _) ?_ ?_ ?_
    · apply cov_sides I t1 t2 z1 z2 TP1 TL1 TP2 TL2 _ _ c1 c2
      intro p l _ _ _ hs
      by_cases s2' : z2 l = false ∨ bp I z2 p = true
      · exact Or.inr ⟨s2', memR ne0, memR ne0⟩
      · exact Or.inl ⟨hs.resolve_right s2', memL (nf (fun h => s2' (Or.inr h.2))),
          memL (nf (fun h => s2' (Or.inl h.1)))⟩
    · have := count_points I t1 t2 z1 z2 TP1 TL1 c1 h1
      rw [Finset.card_empty, Nat.zero_add]
      exact this
    · have := count_lines I hlin t2 t1 z2 z1 TP1 TL1 c1 h2
      rw [Finset.card_empty, Nat.add_zero]
      exact this
  · refine and_assemble I t1 t2 z1 z2 TP1 TL1 TP2 TL2
      (TP1.filter (fun p => ¬ bp I z1 p = true ∧ bp I z2 p = true))
      (TP2.filter (fun p => ¬ bp I z2 p = true ∧ bp I z1 p = true)) ∅ ∅ s1 s2 b1 b2
      (Finset.filter_subset _ _) (Finset.filter_subset _ _) (Finset.empty_subset _)
      (Finset.empty_subset _) ?_ ?_ ?_
    · apply cov_sides I t1 t2 z1 z2 TP1 TL1 TP2 TL2 _ _ c1 c2
      intro p l _ _ _ hs
      by_cases bb2 : bp I z2 p = true
      · exact Or.inr ⟨Or.inr bb2, memR (nf (fun h => h.1 bb2)), memR ne0⟩
      by_cases bb1 : bp I z1 p = true
      · exact Or.inl ⟨Or.inr bb1, memL (nf (fun h => bb2 h.2)), memL ne0⟩
      rcases hs with s | s
      · exact Or.inl ⟨s, memL (nf (fun h => bb2 h.2)), memL ne0⟩
      · exact Or.inr ⟨s, memR (nf (fun h => bb1 h.2)), memR ne0⟩
    · have := count_points I t1 t2 z1 z2 TP1 TL1 c1 h1
      rw [Finset.card_empty, Nat.zero_add]
      exact this
    · have := count_points I t2 t1 z2 z1 TP2 TL2 c2 h2
      rw [Finset.card_empty, Nat.zero_add]
      exact this

theorem good_formula
    (hlin : ∀ l l' : Fin L, l ≠ l' → ∀ p p' : Fin P, I p l → I p l' → I p' l → I p' l' → p = p')
    (xf : Fin P → Fin L → Fin (P + L) → Bool) (xz : Fin L → Fin (P + L) → Bool)
    (hf1 : ∀ p l q, xf p l (Fin.castAdd L q) = true ↔ q = p)
    (hf2 : ∀ p l l', xf p l (Fin.natAdd P l') = true ↔ l' = l)
    (hz1 : ∀ m q, xz m (Fin.castAdd L q) = true ↔ ¬ I q m)
    (hz2 : ∀ m l', xz m (Fin.natAdd P l') = true ↔ l' = m)
    (φ : DMFormula (P + L)) :
    DMFormula.rec (motive := fun _ : DMFormula (P + L) => Prop)
      (fun (_ : Fin (P + L)) (c : Bool) => c = true) (fun _ _ a b => a ∧ b)
      (fun _ _ a b => a ∧ b) φ →
    Good I (fun f => φ.eval (xf f.1 f.2)) (fun m => φ.eval (xz m)) φ.leaves := by
  induction φ with
  | lit k c =>
    intro hc
    have hc' : c = true := hc
    subst hc'
    have hl : (DMFormula.lit k true : DMFormula (P + L)).leaves = 1 := rfl
    rw [hl]
    rcases Fin.addCases (motive := fun k => (∃ q, k = Fin.castAdd L q) ∨ (∃ l, k = Fin.natAdd P l))
      (fun q => Or.inl ⟨q, rfl⟩) (fun l => Or.inr ⟨l, rfl⟩) k with ⟨q, rfl⟩ | ⟨l0, rfl⟩
    · apply good_pt I _ _ q
      · intro p l h
        have h' : xf p l (Fin.castAdd L q) = true := h
        exact ((hf1 p l q).mp h').symm
      · intro m h
        have h' : xz m (Fin.castAdd L q) = false := h
        by_contra hc
        have := (hz1 m q).mpr hc
        rw [h'] at this
        simp at this
    · apply good_ln I _ _ l0
      · intro p l h
        have h' : xf p l (Fin.natAdd P l0) = true := h
        exact ((hf2 p l l0).mp h').symm
      · exact (hz2 l0 l0).mpr rfl
  | and a b iha ihb =>
    intro h
    exact good_and I hlin (fun f => a.eval (xf f.1 f.2)) (fun f => b.eval (xf f.1 f.2))
      (fun m => a.eval (xz m)) (fun m => b.eval (xz m)) a.leaves b.leaves (iha h.1) (ihb h.2)
  | or a b iha ihb =>
    intro h
    exact good_or I (fun f => a.eval (xf f.1 f.2)) (fun f => b.eval (xf f.1 f.2))
      (fun m => a.eval (xz m)) (fun m => b.eval (xz m)) a.leaves b.leaves (iha h.1) (ihb h.2)

theorem exists_off
    (hlin : ∀ l l' : Fin L, l ≠ l' → ∀ p p' : Fin P, I p l → I p l' → I p' l → I p' l' → p = p')
    (hlp : ∀ l : Fin L, 2 ≤ (Finset.univ.filter (fun p : Fin P => I p l)).card)
    (hpl : ∀ p : Fin P, 2 ≤ (Finset.univ.filter (fun l : Fin L => I p l)).card)
    (p : Fin P) : ∃ m, ¬ I p m := by
  obtain ⟨l, hl⟩ := Finset.card_pos.mp
    (by have := hpl p; omega : 0 < (Finset.univ.filter (fun l : Fin L => I p l)).card)
  have hIl : I p l := (Finset.mem_filter.mp hl).2
  obtain ⟨q, hq, hqp⟩ := Finset.exists_mem_ne
    (by have := hlp l; omega : 1 < (Finset.univ.filter (fun p : Fin P => I p l)).card) p
  have hIq : I q l := (Finset.mem_filter.mp hq).2
  obtain ⟨m, hm, hml⟩ := Finset.exists_mem_ne
    (by have := hpl q; omega : 1 < (Finset.univ.filter (fun l : Fin L => I q l)).card) l
  have hIqm : I q m := (Finset.mem_filter.mp hm).2
  refine ⟨m, fun hpm => hqp ?_⟩
  exact (hlin l m (Ne.symm hml) p q hIl hpm hIq hIqm).symm

theorem main_aux : ∀ (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I] (φ : PEqualNP.MetaComplexity.DMFormula (P + L)),
  (∀ l l' : Fin L, l ≠ l' → ∀ p p' : Fin P, I p l → I p l' → I p' l → I p' l' → p = p') →
  (∀ l : Fin L, 2 ≤ (Finset.univ.filter (fun p : Fin P => I p l)).card) →
  (∀ p : Fin P, 2 ≤ (Finset.univ.filter (fun l : Fin L => I p l)).card) →
  PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ : PEqualNP.MetaComplexity.DMFormula (P + L) => Prop)
    (fun (_ : Fin (P + L)) (c : Bool) => c = true) (fun _ _ a b => a ∧ b) (fun _ _ a b => a ∧ b) φ →
  (∀ (p : Fin P) (l : Fin L), I p l →
    φ.eval (fun k => decide (k = Fin.castAdd L p ∨ k = Fin.natAdd P l)) = true) →
  (∀ m : Fin L,
    φ.eval (fun k => decide ((∃ p : Fin P, k = Fin.castAdd L p ∧ ¬ I p m) ∨ k = Fin.natAdd P m)) = false) →
  ∃ (TP : Finset (Fin P)) (TL : Finset (Fin L)),
    (∀ (p : Fin P) (l : Fin L), I p l → p ∈ TP ∨ l ∈ TL) ∧
    (Finset.univ.filter (fun f : Fin P × Fin L => I f.1 f.2)).card + TP.card + TL.card ≤ φ.leaves := by
  intro P L I inst φ hlin hlp hpl hpos hflag hzero
  have hf1 : ∀ (p : Fin P) (l : Fin L) (q : Fin P),
      decide (Fin.castAdd L q = Fin.castAdd L p ∨ Fin.castAdd L q = Fin.natAdd P l) = true ↔
        q = p := by
    intro p l q
    rw [decide_eq_true_iff]
    constructor
    · rintro (h | h)
      · exact cc h
      · exact absurd h (cn q l)
    · intro h
      exact Or.inl (by rw [h])
  have hf2 : ∀ (p : Fin P) (l l' : Fin L),
      decide (Fin.natAdd P l' = Fin.castAdd L p ∨ Fin.natAdd P l' = Fin.natAdd P l) = true ↔
        l' = l := by
    intro p l l'
    rw [decide_eq_true_iff]
    constructor
    · rintro (h | h)
      · exact absurd h.symm (cn p l')
      · exact nn h
    · intro h
      exact Or.inr (by rw [h])
  have hz1 : ∀ (m : Fin L) (q : Fin P),
      decide ((∃ p : Fin P, Fin.castAdd L q = Fin.castAdd L p ∧ ¬ I p m) ∨
        Fin.castAdd L q = Fin.natAdd P m) = true ↔ ¬ I q m := by
    intro m q
    rw [decide_eq_true_iff]
    constructor
    · rintro (⟨p, h, h'⟩ | h)
      · rw [cc h]
        exact h'
      · exact absurd h (cn q m)
    · intro h
      exact Or.inl ⟨q, rfl, h⟩
  have hz2 : ∀ (m l' : Fin L),
      decide ((∃ p : Fin P, Fin.natAdd P l' = Fin.castAdd L p ∧ ¬ I p m) ∨
        Fin.natAdd P l' = Fin.natAdd P m) = true ↔ l' = m := by
    intro m l'
    rw [decide_eq_true_iff]
    constructor
    · rintro (⟨p, h, _⟩ | h)
      · exact absurd h.symm (cn p l')
      · exact nn h
    · intro h
      exact Or.inr (by rw [h])
  obtain ⟨TP, TL, cov, bd⟩ := good_formula I hlin
    (fun p l => fun k => decide (k = Fin.castAdd L p ∨ k = Fin.natAdd P l))
    (fun m => fun k => decide ((∃ p : Fin P, k = Fin.castAdd L p ∧ ¬ I p m) ∨ k = Fin.natAdd P m))
    hf1 hf2 hz1 hz2 φ hpos
  refine ⟨TP, TL, ?_, ?_⟩
  · intro p l hI
    rcases (cov p l hI (hflag p l hI)).1 (hzero l) with h | ⟨_, h⟩
    · exact Or.inl h
    · exact Or.inr h
  · refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_le_card ?_) _) _) bd
    intro f hf
    have hI : I f.1 f.2 := (Finset.mem_filter.mp hf).2
    obtain ⟨m, hm⟩ := exists_off I hlin hlp hpl f.1
    simp only [AB, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hI, hflag f.1 f.2 hI, hzero f.2, (bp_iff I _ _).mpr ⟨m, hm, hzero m⟩⟩

end PEqualNP.Outside.L_meta_2908

theorem PEqualNP.Outside.L_meta_2908 : ∀ (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I] (φ : PEqualNP.MetaComplexity.DMFormula (P + L)),
  (∀ l l' : Fin L, l ≠ l' → ∀ p p' : Fin P, I p l → I p l' → I p' l → I p' l' → p = p') →
  (∀ l : Fin L, 2 ≤ (Finset.univ.filter (fun p : Fin P => I p l)).card) →
  (∀ p : Fin P, 2 ≤ (Finset.univ.filter (fun l : Fin L => I p l)).card) →
  PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ : PEqualNP.MetaComplexity.DMFormula (P + L) => Prop)
    (fun (_ : Fin (P + L)) (c : Bool) => c = true) (fun _ _ a b => a ∧ b) (fun _ _ a b => a ∧ b) φ →
  (∀ (p : Fin P) (l : Fin L), I p l →
    φ.eval (fun k => decide (k = Fin.castAdd L p ∨ k = Fin.natAdd P l)) = true) →
  (∀ m : Fin L,
    φ.eval (fun k => decide ((∃ p : Fin P, k = Fin.castAdd L p ∧ ¬ I p m) ∨ k = Fin.natAdd P m)) = false) →
  ∃ (TP : Finset (Fin P)) (TL : Finset (Fin L)),
    (∀ (p : Fin P) (l : Fin L), I p l → p ∈ TP ∨ l ∈ TL) ∧
    (Finset.univ.filter (fun f : Fin P × Fin L => I f.1 f.2)).card + TP.card + TL.card ≤ φ.leaves :=
  PEqualNP.Outside.L_meta_2908.main_aux
