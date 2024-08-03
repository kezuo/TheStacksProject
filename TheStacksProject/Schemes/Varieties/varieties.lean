/-
Copyright (c) 2024 Shujian Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shujian Yan
-/

import Mathlib.Algebra.Field.Defs
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Properties
import TheStacksProject.Schemes.Schemes.base_change

/-!
Translated from https://stacks.math.columbia.edu/tag/020C
-/

namespace AlgebraicGeometry

variable {κ: Type} [Field κ]
variable {X S: Scheme}
variable (f: X ⟶ S)

class OfFiniteType extends LocallyOfFiniteType f, QuasiCompact f: Prop

/-!
## References
* https://stacks.math.columbia.edu/tag/020D
-/
class Variety (_: SchemeOver f) [OfFiniteType f] [IsIntegral X] [IsSeparated f]: Prop


end AlgebraicGeometry
