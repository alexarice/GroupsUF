This file demonstrates how to use the equality between `𝓖` and `RSymGroup 𝓖` to make proofs simpler.

<details>
<summary>Module header</summary>

```agda
{-# OPTIONS --safe --cubical #-}

module Groups.Properties.Test where

open import Cubical.Foundations.Prelude
open import Cubical.Structures.Group
open import Groups.Symmetric.Representable

private
  variable
    ℓ ℓ′ : Level
```

</details>

We first define a function that allows us to prove a property for a group `𝓖` by instead proving it for the strictly associative and unital group `RSymGroup 𝓖`.

```agda
strictify : (𝓖 : Group) → (P : Group {ℓ} → Type ℓ′) → P (RSymGroup 𝓖) → P 𝓖
strictify 𝓖 P p = transport (sym (cong P (inc≡ 𝓖))) p
```

The best way I have found to structure the proofs is to first list the properties we want to prove.

```agda
module _ {ℓ} (𝓖 : Group {ℓ}) where

  open group-·syntax 𝓖

  Cancellativeᵣ : Type ℓ
  Cancellativeᵣ = ∀ g h z → g · z ≡ h · z → g ≡ h

  Cancellativeₗ : Type ℓ
  Cancellativeₗ = ∀ g h z → z · g ≡ z · h → g ≡ h

  InvOfComp : Type ℓ
  InvOfComp = ∀ g h → (g · h) ⁻¹ ≡ h ⁻¹ · g ⁻¹

  InvInvolution : Type ℓ
  InvInvolution = ∀ g → g ⁻¹ ⁻¹ ≡ g

  InvUniqueRight : Type ℓ
  InvUniqueRight = ∀ g h → g · h ≡ ₁ → h ≡ g ⁻¹

  InvUniqueLeft : Type ℓ
  InvUniqueLeft = ∀ g h → h · g ≡ ₁ → h ≡ g ⁻¹
```

We can then we can easily prove these using `strictify`.

```agda
module _ {ℓ} (𝓖 : Group {ℓ}) where

  open group-·syntax 𝓖
  open group-operation-syntax
  open import Groups.Reasoning 𝓖

  cancelᵣ : Cancellativeᵣ 𝓖
  cancelᵣ = strictify 𝓖 Cancellativeᵣ
    λ g h z p → begin
      g ∘⌊⌋            ≈˘⌊ rinv z ⌋
      ⌊ g ∘ z ⌋∘ inv z ≈⌊  p      ⌋
      h ∘⌊ z ∘ inv z ⌋ ≈⌊  rinv z ⌋
      h                ∎′

  cancelₗ : Cancellativeₗ 𝓖
  cancelₗ = strictify 𝓖 Cancellativeₗ
   λ g h z p → begin
     ⌊⌋∘ g            ≈˘⌊ linv z ⌋
     inv z ∘⌊ z ∘ g ⌋ ≈⌊  p      ⌋
     ⌊ inv z ∘ z ⌋∘ h ≈⌊  linv z ⌋
     h                ∎′

  inv-of-comp : InvOfComp 𝓖
  inv-of-comp = strictify 𝓖 InvOfComp
    λ g h → begin
      inv (g ∘ h) ∘⌊⌋                        ≈˘⌊ rinv g       ⌋
      inv (g ∘ h) ∘ g ∘⌊⌋∘ inv g             ≈˘⌊ rinv h       ⌋
      ⌊ inv (g ∘ h) ∘ g ∘ h ⌋∘ inv h ∘ inv g ≈⌊  linv (g ∘ h) ⌋
      inv h ∘ inv g                          ∎′

  inv-involution : InvInvolution 𝓖
  inv-involution = strictify 𝓖 InvInvolution
    λ g → begin
      inv (inv g) ∘⌊⌋            ≈˘⌊ linv g       ⌋
      ⌊ inv (inv g) ∘ inv g ⌋∘ g ≈⌊  linv (inv g) ⌋
      g                          ∎′

  inv-unique-right : InvUniqueRight 𝓖
  inv-unique-right = strictify 𝓖 InvUniqueRight
    λ g h p → begin
      ⌊⌋∘ h            ≈˘⌊ linv g ⌋
      inv g ∘⌊ g ∘ h ⌋ ≈⌊  p      ⌋
      inv g            ∎′

  inv-unique-left : InvUniqueLeft 𝓖
  inv-unique-left = strictify 𝓖 InvUniqueLeft
    λ g h p → begin
      h ∘⌊⌋            ≈˘⌊ rinv g ⌋
      ⌊ h ∘ g ⌋∘ inv g ≈⌊  p      ⌋
      inv g            ∎′
```
