{-# OPTIONS --safe --cubical --postfix-projections #-}

open import Cubical.Algebra.Group

module Groups.Reasoning {ℓ} (𝓖 : Group {ℓ}) where

open import Cubical.Foundations.Prelude
open import Groups.Symmetric.Representable
open import Cubical.Foundations.Structure

private
  variable
    ℓ′ : Level

open GroupStr (RSymGroup 𝓖 .snd) using () renaming (_+_ to _∘_; 0g to e; -_ to inv; invr to rinv; invl to linv)  public

record Expr : Type ℓ where
  field
    before : ⟨ RSymGroup 𝓖 ⟩
    focus : ⟨ RSymGroup 𝓖 ⟩
    after : ⟨ RSymGroup 𝓖 ⟩

  eval : ⟨ RSymGroup 𝓖 ⟩
  eval = before ∘ focus ∘ after

open Expr

_∼_ : (x : ⟨ RSymGroup 𝓖 ⟩) → (y : Expr) → Type ℓ
x ∼ y = x ≡ eval y

infix 6 _∘⌊_⌋∘_ ⌊_⌋ _∘⌊_⌋ ⌊_⌋∘_ _∘⌊⌋∘_ ⌊⌋ _∘⌊⌋ ⌊⌋∘_
infix 3 _∎′

_∘⌊_⌋∘_ : ⟨ RSymGroup 𝓖 ⟩ → ⟨ RSymGroup 𝓖 ⟩ → ⟨ RSymGroup 𝓖 ⟩ → Expr
(g ∘⌊ f ⌋∘ h) .before = g
(g ∘⌊ f ⌋∘ h) .focus = f
(g ∘⌊ f ⌋∘ h) .after = h

⌊_⌋ : ⟨ RSymGroup 𝓖 ⟩ → Expr
⌊ f ⌋ = e ∘⌊ f ⌋∘ e

_∘⌊_⌋ : ⟨ RSymGroup 𝓖 ⟩ → ⟨ RSymGroup 𝓖 ⟩ → Expr
g ∘⌊ f ⌋ = g ∘⌊ f ⌋∘ e

⌊_⌋∘_ : ⟨ RSymGroup 𝓖 ⟩ → ⟨ RSymGroup 𝓖 ⟩ → Expr
⌊ f ⌋∘ g = e ∘⌊ f ⌋∘ g

⌊⌋ : Expr
⌊⌋ = ⌊ e ⌋

_∘⌊⌋ : ⟨ RSymGroup 𝓖 ⟩ → Expr
g ∘⌊⌋ = g ∘⌊ e ⌋

⌊⌋∘_ : ⟨ RSymGroup 𝓖 ⟩ → Expr
⌊⌋∘ g = ⌊ e ⌋∘ g

_∘⌊⌋∘_ : ⟨ RSymGroup 𝓖 ⟩ → ⟨ RSymGroup 𝓖 ⟩ → Expr
g ∘⌊⌋∘ h = g ∘⌊ e ⌋∘ h

data _IsRelatedTo_ (x : ⟨ RSymGroup 𝓖 ⟩) (y : Expr) : Type ℓ where
  relTo : x ∼ y → x IsRelatedTo y

infix 1 begin_
begin_ : ∀ {x y} → x IsRelatedTo y → x ≡ eval y
begin relTo p = p

step-≈ : ∀ x {y z} → y IsRelatedTo z → x ≡ y → x IsRelatedTo z
step-≈ _ (relTo y∼z) x∼y = relTo (x∼y ∙ y∼z)

step-≈˘ : ∀ x {y z} → y IsRelatedTo z → y ≡ x → x IsRelatedTo z
step-≈˘ _ p q = step-≈ _ p (sym q)

_∎′ : ∀ x → x IsRelatedTo ⌊ x ⌋
x ∎′ = relTo refl

replaceFocus : (x : Expr) → (y : ⟨ RSymGroup 𝓖 ⟩) → Expr
replaceFocus x y .before = x .before
replaceFocus x y .focus = y
replaceFocus x y .after = x .after

congExpr : (x : Expr) → {y : ⟨ RSymGroup 𝓖 ⟩} → focus x ≡ y → eval x ∼ (replaceFocus x y)
congExpr x p = cong (λ a → before x ∘ a ∘ after x) p

step-cong-≈ : ∀ x {y z} → (eval (replaceFocus x y)) IsRelatedTo z → focus x ≡ y → eval x IsRelatedTo z
step-cong-≈ x (relTo p) q = relTo (congExpr x q ∙ p)

step-cong-≈˘ : ∀ x {y z} → (eval (replaceFocus x y)) IsRelatedTo z → y ≡ focus x → eval x IsRelatedTo z
step-cong-≈˘ x (relTo p) q = relTo (congExpr x (sym q) ∙ p)

infixr 2 step-≈
syntax step-≈ x rest p = x ≈⟨ p ⟩ rest

infixr 2 step-≈˘
syntax step-≈˘ x rest p = x ≈⟨ p ⟩ rest

infixr 2 step-cong-≈
syntax step-cong-≈ x rest p = x ≈⌊ p ⌋ rest

infixr 2 step-cong-≈˘
syntax step-cong-≈˘ x rest p = x ≈˘⌊ p ⌋ rest
