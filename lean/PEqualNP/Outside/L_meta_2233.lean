import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2233

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge

lemma flatMap_congr' {α β : Type} (l : List α) (f g : α → List β) (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]

lemma step_len (n : ℕ) (gs : List Gate) : ∀ cs : List (List ℕ),
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs with
  | nil => intro cs; simp
  | cons g gs ih => intro cs; simp only [List.foldl_cons, ih, orStep]; simp; omega

lemma step_prefix (n : ℕ) (gs : List Gate) : ∀ (cs : List (List ℕ)) (i : ℕ), i < cs.length →
    (gs.foldl (orStep n) cs).getD i [] = cs.getD i [] := by
  induction gs with
  | nil => intros; rfl
  | cons g gs ih =>
    intro cs i h
    rw [List.foldl_cons, ih _ i (by simp [orStep]; omega)]
    simp only [orStep]
    exact List.getD_append _ _ _ _ h

lemma step_entry (n : ℕ) (gs : List Gate) : ∀ (cs : List (List ℕ)) (k : ℕ) (hk : k < gs.length) (g : ℕ),
    g ∈ (gs.foldl (orStep n) cs).getD (cs.length + k) [] ↔
      (g = cs.length + k ∨ (gs[k].op = GateOp.or ∧ ∃ w ∈ gs[k].inputs,
        n ≤ w ∧ w < n + (cs.length + k) ∧ g ∈ (gs.foldl (orStep n) cs).getD (w - n) [])) := by
  induction gs with
  | nil => intro cs k hk; simp at hk
  | cons g0 gs ih =>
    intro cs k hk g
    cases k with
    | zero =>
      simp only [List.foldl_cons, List.getElem_cons_zero, Nat.add_zero]
      rw [step_prefix n gs (orStep n cs g0) cs.length (by simp [orStep])]
      have hin : ∀ w, n ≤ w → w < n + cs.length →
          (gs.foldl (orStep n) (orStep n cs g0)).getD (w - n) [] = cs.getD (w - n) [] := by
        intro w h1 h2
        rw [step_prefix n gs _ (w - n) (by simp [orStep]; omega)]
        exact List.getD_append _ _ _ _ (by omega)
      generalize List.foldl (orStep n) (orStep n cs g0) gs = X at hin ⊢
      simp only [orStep]
      rw [List.getD_append_right _ _ _ _ (le_refl _)]
      simp only [Nat.sub_self, List.getD_cons_zero, List.mem_cons]
      split_ifs with hor
      · simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, hor, true_and]
        constructor
        · rintro (h | ⟨w, ⟨hw, h1, h2⟩, hg⟩)
          · exact Or.inl h
          · exact Or.inr ⟨w, hw, h1, h2, by rw [hin w h1 h2]; exact hg⟩
        · rintro (h | ⟨w, hw, h1, h2, hg⟩)
          · exact Or.inl h
          · exact Or.inr ⟨w, ⟨hw, h1, h2⟩, by rw [← hin w h1 h2]; exact hg⟩
      · simp [hor]
    | succ k =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      have h1 := ih (orStep n cs g0) k (by simpa using hk) g
      have hl : (orStep n cs g0).length = cs.length + 1 := by simp [orStep]
      rw [hl] at h1
      rw [show cs.length + (k + 1) = cs.length + 1 + k by omega, h1]

def S (n : ℕ) (C : Circuit) (k : ℕ) : List ℕ := (orSets n C).getD k []

lemma memS (n : ℕ) (C : Circuit) (k g : ℕ) : g ∈ S n C k ↔ k < C.gates.length ∧
    (g = k ∨ ((gateAt C k).op = GateOp.or ∧ ∃ w ∈ (gateAt C k).inputs,
      n ≤ w ∧ w < n + k ∧ g ∈ S n C (w - n))) := by
  by_cases hk : k < C.gates.length
  · have he := step_entry n C.gates [] k hk g
    simp only [List.length_nil, Nat.zero_add] at he
    have hg : gateAt C k = C.gates[k] := by
      unfold gateAt; rw [List.getD_eq_getElem _ _ hk]
    unfold S orSets
    rw [he, hg]
    simp [hk]
  · have : S n C k = [] := by
      unfold S orSets
      apply List.getD_eq_default
      rw [step_len]; simp; omega
    rw [this]
    simp [hk]

lemma parent (n : ℕ) (C : Circuit) : ∀ o x, x ∈ S n C o → x ≠ o →
    ∃ h, h ∈ S n C o ∧ h < C.gates.length ∧ (gateAt C h).op = GateOp.or ∧
      n + x ∈ (gateAt C h).inputs := by
  intro o
  induction o using Nat.strong_induction_on with
  | _ o ih =>
  intro x hx hne
  rw [memS] at hx
  obtain ⟨ho, hx⟩ := hx
  rcases hx with h | ⟨hor, w, hw, hn, hlt, hxw⟩
  · exact absurd h hne
  · by_cases hxk : x = w - n
    · refine ⟨o, (memS n C o o).mpr ⟨ho, Or.inl rfl⟩, ho, hor, ?_⟩
      rw [show n + x = w by omega]; exact hw
    · obtain ⟨h, hh, hhl, hhor, hhin⟩ := ih (w - n) (by omega) x hxw hxk
      exact ⟨h, (memS n C o h).mpr ⟨ho, Or.inr ⟨hor, w, hw, hn, hlt, hh⟩⟩, hhl, hhor, hhin⟩

end PEqualNP.Outside.L_meta_2233

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge

theorem PEqualNP.Outside.L_meta_2233 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ), PEqualNP.TopForm.IsAO2 n C → (∀ j ∈ F, j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output j) → F.card ≤ Set.ncard {i : ℕ | i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output i} + 1 := by
  intro n C F hC hF
  classical
  by_cases hno : n ≤ C.output
  swap
  · have : F = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro j hj
      exact hno (hF j hj).2.2.1
    rw [this]; simp
  have hOR : ∀ i, OrReaches n C C.output i ↔ i ∈ PEqualNP.Outside.L_meta_2233.S n C (C.output - n) :=
    fun i => ⟨fun h => h.2, fun h => ⟨hno, h⟩⟩
  set o := C.output - n with ho
  let D : Finset ℕ := (Finset.range C.gates.length).filter
    (fun i => (gateAt C i).op = GateOp.or ∧ i ∈ PEqualNP.Outside.L_meta_2233.S n C o)
  have hset : {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧ OrReaches n C C.output i} =
      (D : Set ℕ) := by
    ext i
    simp only [Set.mem_setOf_eq, Finset.coe_filter, Finset.mem_range, hOR, D]
  rw [hset, Set.ncard_coe_finset]
  have hdisj : Disjoint F D := by
    rw [Finset.disjoint_left]
    intro j hjF hjD
    have h1 := (hF j hjF).2.1
    have h2 := (Finset.mem_filter.mp hjD).2.1
    rw [h1] at h2
    cases h2
  let Y := (F ∪ D).erase o
  have hpar : ∀ y ∈ Y, ∃ h ∈ D, n + y ∈ (gateAt C h).inputs := by
    intro y hy
    obtain ⟨hne, hyU⟩ := Finset.mem_erase.mp hy
    have hyS : y ∈ PEqualNP.Outside.L_meta_2233.S n C o := by
      rcases Finset.mem_union.mp hyU with h | h
      · exact (hOR y).mp (hF y h).2.2
      · exact (Finset.mem_filter.mp h).2.2
    obtain ⟨h, hh, hhl, hhor, hin⟩ := PEqualNP.Outside.L_meta_2233.parent n C o y hyS hne
    exact ⟨h, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hhl, hhor, hh⟩, hin⟩
  let f : ℕ → ℕ := fun y => if hy : y ∈ Y then Classical.choose (hpar y hy) else 0
  have hf : ∀ y ∈ Y, f y ∈ D ∧ n + y ∈ (gateAt C (f y)).inputs := by
    intro y hy
    have := Classical.choose_spec (hpar y hy)
    simp only [f, dif_pos hy]
    exact this
  have hfib : ∀ b ∈ D, (Y.filter (fun y => f y = b)).card ≤ 2 := by
    intro b hb
    have hbl : b < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
    have hmem : gateAt C b ∈ C.gates := by
      unfold gateAt; rw [List.getD_eq_getElem _ _ hbl]; exact List.getElem_mem hbl
    have hlen : (gateAt C b).inputs.length = 2 := hC.2.2 _ hmem
    calc (Y.filter (fun y => f y = b)).card
        = ((Y.filter (fun y => f y = b)).image (fun y => n + y)).card :=
          (Finset.card_image_of_injective _ (add_right_injective n)).symm
      _ ≤ (gateAt C b).inputs.toFinset.card := by
          apply Finset.card_le_card
          intro z hz
          obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
          obtain ⟨hyY, hfy⟩ := Finset.mem_filter.mp hy
          rw [List.mem_toFinset, ← hfy]
          exact (hf y hyY).2
      _ ≤ (gateAt C b).inputs.length := List.toFinset_card_le _
      _ = 2 := hlen
  have hcard : Y.card ≤ 2 * D.card :=
    Finset.card_le_mul_card_image_of_maps_to (fun y hy => (hf y hy).1) 2 hfib
  have hY : (F ∪ D).card - 1 ≤ Y.card := Finset.pred_card_le_card_erase
  have hU : (F ∪ D).card = F.card + D.card := Finset.card_union_of_disjoint hdisj
  omega
