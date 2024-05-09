open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc)

module types where

{- Types -}

data Type : Set where
  bool : Type
  _⇒_ : Type → Type → Type
  _*_ : Type → Type → Type

infixr 7 _⇒_
infixr 9 _*_

{- Typing contexts -}

Ctx : ℕ → Set
Ctx n = Fin n → Type

_∷_ : ∀ {n : ℕ} → Ctx n → Type → Ctx (suc n)
(_ ∷ T) zero    = T
(Γ ∷ _) (suc m) = Γ m

infixl 5 _∷_
