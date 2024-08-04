/-
Copyright (c) 2024 Shujian Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shujian Yan
-/

import Mathlib.Algebra.Field.Defs
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Algebra.Ring.Defs
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
Translated from https://stacks.math.columbia.edu/tag/01T0
-/

namespace AlgebraicGeometry

variable {X S: Scheme}
variable (f: X ⟶ S)

open CategoryTheory

universe u

/-!
## References
* https://stacks.math.columbia.edu/tag/01T1
-/
class IsFiniteType extends LocallyOfFiniteType f, QuasiCompact f: Prop

end AlgebraicGeometry
