{-# OPTIONS --safe --cubical #-}

module Groups.Properties.Test where

open import Cubical.Foundations.Prelude
open import Cubical.Structures.Group
open import Groups.Symmetric.Representable

private
  variable
    ℓ ℓ′ : Level

strictify : (𝓖 : Group) → (P : Group {ℓ} → Type ℓ′) → P (RSymGroup 𝓖) → P 𝓖
strictify 𝓖 P p = transport (sym (cong P (inc≡ 𝓖))) p

Cancellativeᵣ : {A : Type ℓ} → (op : A → A → A) → Type ℓ
Cancellativeᵣ op = ∀ g h z → op g z ≡ op h z → g ≡ h

module _ {ℓ} (𝓖 : Group {ℓ}) where

  open group-·syntax 𝓖
  open group-operation-syntax
  open group-·syntax (RSymGroup 𝓖) renaming (_·_ to _∘_; ₁ to e; _⁻¹ to inv)

  cancelᵣ : Cancellativeᵣ _·_
  cancelᵣ = strictify 𝓖 (λ 𝓗 → Cancellativeᵣ (group-operation 𝓗))
    λ g h z g·z≡h·z →
      g             ≡⟨ cong (g ∘_) (sym (group-rinv (RSymGroup 𝓖) z)) ⟩
      g ∘ z ∘ inv z ≡⟨ cong (_∘ inv z) g·z≡h·z ⟩
      h ∘ z ∘ inv z ≡⟨ cong (h ∘_) (group-rinv (RSymGroup 𝓖) z) ⟩
      h             ∎
