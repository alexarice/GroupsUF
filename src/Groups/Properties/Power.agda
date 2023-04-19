{-# OPTIONS --safe --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Group
open import Groups.Symmetric.Representable

module Groups.Properties.Power where

open import Cubical.Data.Nat using (ℕ; suc; zero; _+_)

module Power {ℓ} (𝓖 : Group ℓ) where
  open GroupStr (𝓖 .snd)
  _^_ : 𝓖 .fst → ℕ → 𝓖 .fst
  g ^ zero = 1g
  g ^ suc n = g · g ^ n

module _ {ℓ} (𝓖 : Group ℓ) where
  open GroupStr (𝓖 .snd)
  open Power 𝓖

  Power-comm : Type ℓ
  Power-comm = ∀ n g → g · g ^ n ≡ g ^ n · g

  Power-prop : Type ℓ
  Power-prop = ∀ n m g → g ^ n · g ^ m ≡ g ^ (n + m)

  Power-inv : Type ℓ
  Power-inv = ∀ n g → inv g ^ n ≡ inv (g ^ n)

module _ {ℓ} (𝓖 : Group ℓ) where
  open GroupStr (RSymGroup 𝓖 .snd)
  open import Groups.Reasoning 𝓖 using (strictify)
  open Power (RSymGroup 𝓖)

  Power-comm-proof : Power-comm 𝓖
  Power-comm-proof = strictify Power-comm γ
    where
      γ : Power-comm (RSymGroup 𝓖)
      γ zero g = refl
      γ (suc n) g = cong (g ·_) (γ n g)

module _ {ℓ} (𝓖 : Group ℓ) where
  open GroupStr (RSymGroup 𝓖 .snd)
  open import Groups.Reasoning 𝓖 using (strictify)
  open Power (RSymGroup 𝓖)

  Power-prop-proof : Power-prop 𝓖
  Power-prop-proof = strictify Power-prop γ
    where
      γ : Power-prop (RSymGroup 𝓖)
      γ zero m g = refl
      γ (suc n) m g = cong (g ·_) (γ n m g)

  Power-inv-proof : Power-inv 𝓖
  Power-inv-proof = strictify Power-inv γ
    where
      γ : Power-inv (RSymGroup 𝓖)
      γ zero g = refl
      γ (suc n) g =
        inv g · (inv g ^ n)
          ≡⟨ Power-comm-proof (RSymGroup 𝓖) n (inv g) ⟩
        (inv g ^ n) · inv g
          ≡⟨ cong (_· inv g) (γ n g) ⟩
        inv (g ^ n) · inv g ∎
