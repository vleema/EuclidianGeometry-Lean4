import EuclideanGeometry.Basic
import Mathlib.Data.Real.Basic

namespace EuclideanGeometry

class MetricPlane (α : Type) extends OrderedPlane α where
  distance : Point → Point → ℝ

  -- Properties that define a valid distance function
  distance_positive  : ∀ (p q : Point), p ≠ q → distance p q > 0
  distance_symmetric : ∀ (p q : Point), distance p q = distance q p
  distance_zero_iff  : ∀ (p q : Point), distance p q = 0 ↔ p = q

instance {α : Type} : Coe (MetricPlane α) (Plane α) where
  coe mp := mp.toOrderedPlane.toPlane

def segmentLength {α : Type} {P : MetricPlane α} (s : Segment (P : Plane α)) : ℝ := 
  let (a, b) := endpoints s
  P.distance a b

class SegmentMeasureAxioms (α : Type) (P : MetricPlane α) where
  -- For those that read "Lucas, João - Geometria Euclidiana Plana", note that the first Segment Measure
  -- (Axiom III₁) is now part of the distance function required properties.
  --
  -- Axiom III₁ : For any segment, there is a unique real number that represents its length
  axiom_III₁ : ∀ (s : Segment (P : Plane α)), ∃! (r : ℝ), r = segmentLength s

  -- Axiom III₂ : Segment addition postulate
  axiom_III₂ : ∀ (a b c : P.Point),
    isBetween a b c → P.distance a b = P.distance a c + P.distance c b

end EuclideanGeometry
