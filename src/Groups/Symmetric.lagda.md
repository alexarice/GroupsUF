In this file we show that given a set X, we can form a group, using the special definition of permutation from `Groups.Function.Inverse` which is strictly associative and unital.

<details>
<summary>Module header</summary>

```agda
{-# OPTIONS --safe --cubical #-}

module Groups.Symmetric where

open import Cubical.Foundations.Prelude
open import Cubical.Structures.Group
open import Groups.Function.Inverse

private
  variable
    ℓ ℓ′ : Level
```

</details>

```agda
Symmetric-Group : (X : Type ℓ) → isSet X → Group
Symmetric-Group X isSetX =
  -- Carrier
  Inverse X X ,
  -- Operation
  _∘_ ,
  -- Semigroup axioms
  (isSetInv isSetX isSetX , inv-comp-assoc) ,
  -- Unit
  id-inv , (λ f → (id-unit-left f) , (id-unit-right f)) ,
  -- Inverses
  (λ f → (inv-inv f) , ((inv-inv-right isSetX f) , inv-inv-left isSetX f))
```
