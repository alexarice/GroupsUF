{-# OPTIONS --safe --cubical #-}

open import Cubical.Structures.Group

module Groups.Symmetric.Inclusion {ℓ} (𝓖 : Group {ℓ}) where

open import Groups.Symmetric
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Functions.FunExtEquiv

open group-·syntax 𝓖

SymGroup : Group
SymGroup = Symmetric-Group ⟨ 𝓖 ⟩ (group-is-set 𝓖)

inc : ⟨ 𝓖 ⟩ → ⟨ SymGroup ⟩
inc g = (λ x → g · x) , (λ x → g ⁻¹ · x) , i , ii
  where
    i : (b x : ⟨ 𝓖 ⟩) → x ≡ g ⁻¹ · b → g · x ≡ b
    i b x p =
      g · x          ≡⟨ cong (g ·_) p ⟩
      g · (g ⁻¹ · b) ≡⟨ group-assoc 𝓖 g (g ⁻¹) b ⟩
      (g · g ⁻¹) · b ≡⟨ cong (_· b) (group-rinv 𝓖 g) ⟩
      ₁ · b          ≡⟨ group-lid 𝓖 b ⟩
      b ∎

    ii : (a y : ⟨ 𝓖 ⟩) → y ≡ g · a → g ⁻¹ · y ≡ a
    ii a y p =
      g ⁻¹ · y       ≡⟨ cong (g ⁻¹ ·_) p ⟩
      g ⁻¹ · (g · a) ≡⟨ group-assoc 𝓖 (g ⁻¹) g a ⟩
      (g ⁻¹ · g) · a ≡⟨ cong (_· a) (group-linv 𝓖 g) ⟩
      ₁ · a          ≡⟨ group-lid 𝓖 a ⟩
      a ∎

inc-injective : (x y : ⟨ 𝓖 ⟩) → inc x ≡ inc y → x ≡ y
inc-injective x y p =
  x ≡⟨ sym (group-rid 𝓖 x) ⟩
  x · ₁ ≡⟨ cong (λ a → fst a ₁) p ⟩
  y · ₁ ≡⟨ group-rid 𝓖 y ⟩
  y ∎

inv-involution : ∀ (g h : ⟨ 𝓖 ⟩) → (g · h) ⁻¹ ≡ h ⁻¹ · g ⁻¹
inv-involution g h =
  (g · h) ⁻¹ ≡⟨ sym (group-rid 𝓖 ((g · h) ⁻¹)) ⟩
  (g · h) ⁻¹ · ₁ ≡⟨ cong ((g · h) ⁻¹ ·_) i ⟩
  (g · h) ⁻¹ · ((g · h) · (h ⁻¹ · g ⁻¹)) ≡⟨ group-assoc 𝓖 ((g · h) ⁻¹) (g · h) (h ⁻¹ · g ⁻¹) ⟩
  ((g · h) ⁻¹ · (g · h)) · (h ⁻¹ · g ⁻¹) ≡⟨ cong (_· (h ⁻¹ · g ⁻¹)) (group-linv 𝓖 (g · h)) ⟩
  ₁ · (h ⁻¹ · g ⁻¹) ≡⟨ group-lid 𝓖 (h ⁻¹ · g ⁻¹) ⟩
  h ⁻¹ · g ⁻¹ ∎
    where
      i : ₁ ≡ (g · h) · h ⁻¹ · g ⁻¹
      i =
        ₁ ≡⟨ sym (group-rinv 𝓖 g) ⟩
        g · g ⁻¹ ≡⟨ cong (_· g ⁻¹) (sym (group-rid 𝓖 g)) ⟩
        (g · ₁) · g ⁻¹ ≡⟨ cong (λ a → (g · a) · g ⁻¹) (sym (group-rinv 𝓖 h)) ⟩
        (g · (h · h ⁻¹)) · g ⁻¹ ≡⟨ cong (_· g ⁻¹) (group-assoc 𝓖 g h (h ⁻¹)) ⟩
        ((g · h) · h ⁻¹) · g ⁻¹ ≡⟨ sym (group-assoc 𝓖 (g · h) (h ⁻¹) (g ⁻¹)) ⟩
        (g · h) · h ⁻¹ · g ⁻¹ ∎

inc-homo : (x y : ⟨ 𝓖 ⟩) → inc (x · y) ≡ group-operation (SymGroup) (inc x) (inc y)
inc-homo x y = sigmaPath→pathSigma _ _ (i , sigmaPath→pathSigma _ _ (ii , (sigmaPath→pathSigma _ _ (iii , iv))))
  where
    i : (λ g → (x · y) · g) ≡ λ g → x · (y · g)
    i = funExt (λ g → sym (group-assoc 𝓖 x y g))

    ii : _
    ii = funExt (λ g → (transportRefl _) ∙ cong₂ _·_ (inv-involution x y) (transportRefl _) ∙ sym (group-assoc 𝓖 (y ⁻¹) (x ⁻¹) g))

    iii : _
    iii = funExt₃ (λ a b c → group-is-set 𝓖 _ _ _ _)

    iv : _
    iv = funExt₃ (λ a b c → group-is-set 𝓖 _ _ _ _ )
