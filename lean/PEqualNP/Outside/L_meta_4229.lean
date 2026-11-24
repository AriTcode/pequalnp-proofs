import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4229

open PEqualNP.CircuitLowerBounds

def F (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl F x := rfl

def rho (n : ℕ) (i : ℕ) : ℕ := if i < n then i else i + 2

def remap (n : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (rho n)⟩

lemma foldl_remap (n : ℕ) :
    ∀ (gs : List Gate) (A S : List Bool), n ≤ A.length → S.length = A.length + 2 →
      (∀ i, S.getD (rho n i) false = A.getD i false) →
      ∀ i, ((gs.map (remap n)).foldl F S).getD (rho n i) false = (gs.foldl F A).getD i false := by
  intro gs
  induction gs with
  | nil => intro A S _ _ h i; exact h i
  | cons g gs ih =>
    intro A S hA hS h
    simp only [List.map_cons, List.foldl_cons]
    apply ih
    · simp [F]; omega
    · simp [F]; omega
    · have hv : (remap n g).op.eval ((remap n g).inputs.map fun i => S.getD i false) =
          g.op.eval (g.inputs.map fun i => A.getD i false) := by
        simp only [remap, List.map_map]
        congr 1
        apply List.map_congr_left
        intro i _
        exact h i
      intro i
      simp only [F]
      rw [hv]
      rcases lt_trichotomy i A.length with hi | hi | hi
      · have h1 : rho n i < S.length := by unfold rho; split <;> omega
        rw [List.getD_append _ _ _ _ h1, List.getD_append _ _ _ _ hi, h i]
      · have h1 : rho n i = S.length := by unfold rho; split <;> omega
        rw [h1, hi]
        simp
      · have h1 : S.length + 1 ≤ rho n i := by unfold rho; split <;> omega
        rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

end PEqualNP.Outside.L_meta_4229

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_4229 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x2 → x2.output < x1 + x2.size → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (x1 + (2 : ℕ)) x6 ∧ x6.size = x2.size ∧ x6.output < x1 + (2 : ℕ) + x6.size ∧ (∀ (x7 : List Bool), x7.length = x1 → ∀ (x9 x10 : Bool), x6.eval (x7 ++ [x9, x10]) = x2.eval x7) ∧ ∀ x7 < x1, (∃ x9 ∈ x2.gates, x7 ∈ x9.inputs) → ∃ x10 ∈ x6.gates, x7 ∈ x10.inputs := by
  intro n C hm hrb hout
  refine ⟨⟨C.gates.map (PEqualNP.Outside.L_meta_4229.remap n),
    PEqualNP.Outside.L_meta_4229.rho n C.output⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    simpa [PEqualNP.Outside.L_meta_4229.remap] using hm g' hg'
  · intro j hj i hi
    have hj' : j < C.gates.length := by simpa using hj
    have hg : PEqualNP.MetaComplexity.NestedCover.gateAt
        ⟨C.gates.map (PEqualNP.Outside.L_meta_4229.remap n), PEqualNP.Outside.L_meta_4229.rho n C.output⟩ j =
        PEqualNP.Outside.L_meta_4229.remap n (PEqualNP.MetaComplexity.NestedCover.gateAt C j) := by
      simp only [PEqualNP.MetaComplexity.NestedCover.gateAt]
      rw [List.getD_eq_getElem _ _ (by simpa using hj'), List.getD_eq_getElem _ _ hj']
      simp
    rw [hg] at hi
    simp only [PEqualNP.Outside.L_meta_4229.remap, List.mem_map] at hi
    obtain ⟨i', hi', rfl⟩ := hi
    have := hrb j hj' i' hi'
    unfold PEqualNP.Outside.L_meta_4229.rho
    split <;> omega
  · simp [Circuit.size]
  · have hs : (⟨C.gates.map (PEqualNP.Outside.L_meta_4229.remap n),
        PEqualNP.Outside.L_meta_4229.rho n C.output⟩ : Circuit).size = C.size := by
      simp [Circuit.size]
    rw [hs]
    show PEqualNP.Outside.L_meta_4229.rho n C.output < n + 2 + C.size
    unfold PEqualNP.Outside.L_meta_4229.rho
    split <;> omega
  · intro x7 hx7 x9 x10
    simp only [Circuit.eval, PEqualNP.Outside.L_meta_4229.wires_eq]
    apply PEqualNP.Outside.L_meta_4229.foldl_remap n C.gates x7 (x7 ++ [x9, x10]) (by omega)
      (by simp)
    intro i
    unfold PEqualNP.Outside.L_meta_4229.rho
    split
    · exact List.getD_append _ _ _ _ (by omega)
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
  · rintro i hi ⟨g, hg, hig⟩
    refine ⟨PEqualNP.Outside.L_meta_4229.remap n g, List.mem_map_of_mem hg, ?_⟩
    simp only [PEqualNP.Outside.L_meta_4229.remap, List.mem_map]
    exact ⟨i, hig, by simp [PEqualNP.Outside.L_meta_4229.rho, hi]⟩
