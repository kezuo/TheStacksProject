/-
Copyright (c) 2024 Shujian Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shujian Yan
-/

import Mathlib.Algebra.Field.Defs
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Algebra.Ring.Defs

/-!
Translated from https://stacks.math.columbia.edu/tag/01JW
-/

namespace AlgebraicGeometry

open CategoryTheory

universe u

structure SchemeOver {X S: Scheme} (f: X ⟶ S)

structure SchemeOverRing {X: Scheme} {R: CommRingCat} (f: X ⟶ Spec R)

def SchemeOverRing.toSchemeOver (_: SchemeOverRing f) : SchemeOver f :=
SchemeOver.mk

instance : Coe (SchemeOverRing f) (SchemeOver f) := ⟨SchemeOverRing.toSchemeOver⟩

instance : CoeSort (SchemeOver (f: (X: Scheme.{u}) ⟶ Y)) (Type u) where
  coe _:= X.carrier

end AlgebraicGeometry
