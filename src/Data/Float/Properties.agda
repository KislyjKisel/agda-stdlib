------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of operations on floats
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Float.Properties where

open import Data.Bool.Base as Bool using (Bool)
open import Data.Float.Base
import Data.Word.Base as Word
import Data.Word.Properties as Wₚ
open import Relation.Nullary.Decidable as RN using (map′)
open import Relation.Binary
import Relation.Binary.Construct.On as On
open import Relation.Binary.PropositionalEquality
open import Data.Maybe.Relation.Binary.Pointwise as Mb using ()
open import Function.Bundles using (Equivalence)

------------------------------------------------------------------------
-- Primitive properties

open import Agda.Builtin.Float.Properties
  renaming (primFloatToWord64Injective to toWord-injective)
  public

------------------------------------------------------------------------
-- Properties of _≈_

≈⇒≡ : _≈_ ⇒ _≡_
≈⇒≡ {x} {y} eq = toWord-injective x y (Mb.[R⇒≡]⇒≡ Wₚ.≈⇒≡ eq)

≈-reflexive : _≡_ ⇒ _≈_
≈-reflexive eq = Mb.reflexive Wₚ.≈-reflexive (cong toWord eq)

≈-refl : Reflexive _≈_
≈-refl = Mb.refl refl

≈-sym : Symmetric _≈_
≈-sym = Mb.sym sym

≈-trans : Transitive _≈_
≈-trans = Mb.trans trans

≈-subst : ∀ {ℓ} → Substitutive _≈_ ℓ
≈-subst P x≈y p = subst P (≈⇒≡ x≈y) p

infix 4 _≈?_
_≈?_ : Decidable _≈_
_≈?_ = On.decidable toWord (Mb.Pointwise Word._≈_) (Mb.dec Wₚ._≈?_)

≈-isEquivalence : IsEquivalence _≈_
≈-isEquivalence = record
  { refl  = λ {i} → ≈-refl {i}
  ; sym   = λ {i j} → ≈-sym {i} {j}
  ; trans = λ {i j k} → ≈-trans {i} {j} {k}
  }

≈-setoid : Setoid _ _
≈-setoid = record
  { isEquivalence = ≈-isEquivalence
  }

≈-isDecEquivalence : IsDecEquivalence _≈_
≈-isDecEquivalence = record
  { isEquivalence = ≈-isEquivalence
  ; _≟_           = _≈?_
  }

≈-decSetoid : DecSetoid _ _
≈-decSetoid = record
  { isDecEquivalence = ≈-isDecEquivalence
  }
------------------------------------------------------------------------
-- Properties of _≡_

infix 4 _≟_
_≟_ : DecidableEquality Float
x ≟ y = map′ ≈⇒≡ ≈-reflexive (x ≈? y)

≡-setoid : Setoid _ _
≡-setoid = setoid Float

≡-decSetoid : DecSetoid _ _
≡-decSetoid = decSetoid _≟_
