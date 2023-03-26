This file demonstrates how to use the equality between `𝓖` and `RSymGroup 𝓖` to make proofs simpler.

<details>
<summary>Module header</summary>

```agda
{-# OPTIONS --safe --cubical #-}

module Groups.Properties.Test where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Group
open import Groups.Symmetric.Representable

private
  variable
    ℓ ℓ′ : Level
```

</details>

The best way I have found to structure the proofs is to first list the properties we want to prove.

```agda
module _ {ℓ} (𝓖 : Group ℓ) where

  open GroupStr (𝓖 .snd)

  Cancellativeᵣ : Type ℓ
  Cancellativeᵣ = ∀ g h z → g · z ≡ h · z → g ≡ h

  Cancellativeₗ : Type ℓ
  Cancellativeₗ = ∀ g h z → z · g ≡ z · h → g ≡ h

  InvOfComp : Type ℓ
  InvOfComp = ∀ g h → inv (g · h) ≡ inv h · inv g

  InvInvolution : Type ℓ
  InvInvolution = ∀ g → inv (inv g) ≡ g

  InvUniqueRight : Type ℓ
  InvUniqueRight = ∀ g h → g · h ≡ 1g → h ≡ inv g

  InvUniqueLeft : Type ℓ
  InvUniqueLeft = ∀ g h → h · g ≡ 1g → h ≡ inv g
```

We can then we can easily prove these using `strictify`.

```agda
module _ {ℓ} (𝓖 : Group ℓ) where
  open import Groups.Reasoning 𝓖

  cancelᵣ : Cancellativeᵣ 𝓖
  cancelᵣ = strictify Cancellativeᵣ
    λ g h z p → begin
      g ∘⌊⌋            ≈˘⌊ ·InvR′ z ⌋
      ⌊ g ∘ z ⌋∘ (z ⁻¹) ≈⌊  p      ⌋
      h ∘⌊ z ∘ z ⁻¹ ⌋ ≈⌊  ·InvR′ z ⌋
      h                ∎′

  cancelₗ : Cancellativeₗ 𝓖
  cancelₗ = strictify Cancellativeₗ
   λ g h z p → begin
     ⌊⌋∘ g            ≈˘⌊ ·InvL′ z ⌋
     z ⁻¹ ∘⌊ z ∘ g ⌋ ≈⌊  p      ⌋
     ⌊ z ⁻¹ ∘ z ⌋∘ h ≈⌊  ·InvL′ z ⌋
     h                ∎′

  inv-of-comp : InvOfComp 𝓖
  inv-of-comp = strictify InvOfComp
    λ g h → refl

  inv-involution : InvInvolution 𝓖
  inv-involution = strictify InvInvolution
    λ g → refl

  inv-unique-right : InvUniqueRight 𝓖
  inv-unique-right = strictify InvUniqueRight
    λ g h p → begin
      ⌊⌋∘ h            ≈˘⌊ ·InvL′ g ⌋
      g ⁻¹ ∘⌊ g ∘ h ⌋ ≈⌊  p      ⌋
      g ⁻¹            ∎′

  inv-unique-left : InvUniqueLeft 𝓖
  inv-unique-left = strictify InvUniqueLeft
    λ g h p → begin
      h ∘⌊⌋            ≈˘⌊ ·InvR′ g ⌋
      ⌊ h ∘ g ⌋∘ g ⁻¹ ≈⌊  p      ⌋
      g ⁻¹            ∎′
```
