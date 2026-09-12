/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.MeasureTheory.Measure.UniqueProd

/-!
# Product measures

`Measure.prod` requires evidence that the measurable rectangle formula determines a unique
measure. Both factors being sigma-finite supplies this evidence automatically.

For arbitrary measures, `Measure.primitiveProd` is the greatest product measure, constructed
by rectangle covers.
`Measure.productBySections` is the ordered section-integral construction, defined under
`HasAEMeasurableSectionMeasures`. Its s-finite Tonelli theory is exported from
`Measure.ProductBySections`.
The predicates `IsProductMeasure` and `HasUniqueProduct` distinguish a chosen product measure
from a uniquely determined one.
-/
