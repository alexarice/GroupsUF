In this file we show that given a set X, we can form a group, using the special definition of permutation from `Groups.Function.Inverse` which is strictly associative and unital.

<details>
<summary>Module header</summary>

```agda
{-# OPTIONS --safe --cubical #-}

module Groups.Symmetric where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Group
open import Groups.Function.Inverse

private
  variable
    ℓ ℓ′ : Level
```

</details>

```agda
Symmetric-Group : (X : Type ℓ) → isSet X → Group
Symmetric-Group X isSetX = makeGroup
  -- Id
  id-inv
  -- Operation
  _∘_
  -- Inverse
  inv-inv
  -- Group Axioms
  (isSetInv isSetX isSetX)
  inv-comp-assoc
  id-unit-left
  id-unit-left
  (inv-inv-right isSetX)
  (inv-inv-left isSetX)
```
