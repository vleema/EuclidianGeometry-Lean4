import Mathlib.Logic.ExistsUnique

class PlaneGeometry where
  Point : Type
  Line : Type
  -- Incidence relation (when a point lies on a line)
  incident : Point → Line → Prop

def isIncident {P : PlaneGeometry} (p : P.Point) (l : P.Line) : Prop :=
  P.incident p l

infix:50 " ∈ " => isIncident

-- Axioms of Incidence
class IncidenceAxioms (P : PlaneGeometry) where
  -- Axiom I₁: Every line has at least one point on it and at least one point not on it
  axiom_I₁ : ∀ l : P.Line, 
    (∃ p : P.Point, p ∈ l) ∧ 
    (∃ p : P.Point, ¬(p ∈ l))
  
  -- Axiom I₂: For any two distinct points, there exists a unique line containing them
  axiom_I₂ : ∀ (p q : P.Point), p ≠ q → 
    ∃! l : P.Line, p ∈ l ∧ q ∈ l

def intersect {P : PlaneGeometry} (l m : P.Line) : Prop :=
  ∃ p : P.Point, p ∈ l ∧ p ∈ m

-- Proposition 1.1: Two distinct lines either don't intersect or intersect at exactly one point
theorem prop_1_1 {P : PlaneGeometry} [IncidenceAxioms P] 
    (l m : P.Line) (h : l ≠ m) : 
    (¬intersect l m) ∨ (∃! p : P.Point, p ∈ l ∧ p ∈ m) := by
    by_cases h_int : intersect l m
    case neg =>
        left
        exact h_int
    case pos =>
        right
        obtain ⟨p, h_int_p⟩ := h_int
        apply ExistsUnique.intro p
        exact h_int_p
        intro q h_int_q
        apply Classical.byContradiction
        intro h_contra
        have hneq := Ne.symm h_contra
        obtain ⟨u, h_l_exists, h_l_unique⟩ := IncidenceAxioms.axiom_I₂ p q hneq
        have h_l_eq_u := h_l_unique l ⟨h_int_p.1, h_int_q.1⟩
        have h_m_eq_u := h_l_unique m ⟨h_int_p.2, h_int_q.2⟩
        have h_eq : l = m := by rw [h_l_eq_u, h_m_eq_u]
        contradiction
