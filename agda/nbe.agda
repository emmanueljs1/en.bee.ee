import Relation.Binary.PropositionalEquality as Eq
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_) renaming (_∸_ to _-_)
open import Data.Product using (∃-syntax; _×_; _,_)
open Eq using (refl; _≡_)

module nbe where

variable i j k l n : ℕ

infix 5 ƛ_ ⟨λ_⟩_ ⟨_,_⟩
infix 7 _[_]
infix 10 `_
infix 9 ↑[_]_ ↓[_]_
infixl 8 _·_
infixl 5 _∘_
infixl 6 _•_
infixr 7 _⇒_ _⇒ᴰ_
infix 4 _⊢_ _∷_ _⊢_≣_ _⊢_≣_∷_ ⊢_ _⊢_∷_ _[_]=_ _⊢_⦂_ _⊢_≤_ _·_↘_ ⦅_⦆_↘_ Rⁿᶠ_⦂_↘_ Rⁿᵉ_⦂_↘_ ↑_↘_

{- Syntax -}

-- constants
data Cst : Set where
  𝟙 : Cst
  one : Cst
  Fun : Cst
  𝒰 : ℕ → Cst

variable c : Cst

mutual
  -- expressions
  data Exp : Set where
    `_ : Cst → Exp
    var : ℕ → Exp
    ƛ_ : Exp → Exp
    _·_ : Exp → Exp → Exp
    _[_] : Exp → Subst → Exp

  -- substitutions
  data Subst : Set where
    ↑ : Subst
    id : Subst
    _∘_ : Subst → Subst → Subst
    _•_ : Subst → Exp → Subst

variable r s t R S T T′ : Exp
variable σ τ : Subst

-- normal terms and neutral terms
mutual
  data Nf : Set where
    `_ : Ne → Nf
    Fun : Nf → Nf → Nf
    ƛ_ : Nf → Nf
    𝟙 : Nf
    one : Nf
    𝒰 : ℕ → Nf

  data Ne : Set where
    var : ℕ → Ne
    _·_ : Ne → Nf → Ne

variable v w V W : Nf
variable u U : Ne

-- non-dependent function space
_⇒_ : Exp → Exp → Exp
S ⇒ T = ` Fun · S · (ƛ T [ ↑ ])

{- Typing -}

-- typing of constant expressions
data _∷_ : Cst → Exp → Set where
  ∷one : one ∷ ` 𝟙

  ∷𝟙 : 𝟙 ∷ ` 𝒰 k

  ∷Fun : ∀ {i j k} → i ≤ k → j ≤ k
       → Fun ∷ ` Fun · ` 𝒰 i · (ƛ (var zero ⇒ ` 𝒰 j) ⇒ ` 𝒰 k)

  ∷𝒰 : ∀ {i j} → i < j → 𝒰 i ∷ ` 𝒰 k

-- contexts
data Ctx : Set where
  ε : Ctx
  _•_ : Ctx → Exp → Ctx

variable Γ Δ Γ₁ Γ₂ Γ₃ : Ctx

-- context lookup
data _[_]=_ : Ctx → ℕ → Exp → Set where
  here : Γ • S [ zero ]= S [ ↑ ]

  there : Γ [ i ]= S → Γ • T [ suc i ]= S [ ↑ ]

mutual
  -- typing of contexts
  data ⊢_ : Ctx → Set where
    ⊢ε : ⊢ ε

    ⊢• : ⊢ Γ → Γ ⊢ T → ⊢ Γ • T

  -- typing of "types" (expressions with type 𝒰ₖ)
  _⊢_ : Ctx → Exp → Set
  Γ ⊢ T = ∀ {k} → Γ ⊢ T ∷ ` 𝒰 k

  -- expression typing
  data _⊢_∷_ : Ctx → Exp → Exp → Set where
    ⊢cst : ⊢ Γ → c ∷ T → Γ ⊢ ` c ∷ T

    ⊢subst : Γ ⊢ σ ⦂ Δ → Δ ⊢ t ∷ T → Γ ⊢ t [ σ ] ∷ T [ σ ]

    ⊢var : ⊢ Γ → Γ [ i ]= S → Γ ⊢ var i ∷ S

    ⊢abs : Γ • S ⊢ t ∷ T → Γ ⊢ ƛ t ∷ ` Fun · S · (ƛ T)

    ⊢app : Γ ⊢ r ∷ ` Fun · S · R → Γ ⊢ s ∷ S → Γ ⊢ r · s ∷ R · s

    ⊢sub : Γ ⊢ t ∷ T → Γ ⊢ T ≤ T′ → Γ ⊢ t ∷ T′

  -- subsumption
  data _⊢_≤_ : Ctx → Exp → Exp → Set where
    ≤𝒰 : k ≤ l → Γ ⊢ ` 𝒰 k ≤ ` 𝒰 l

    ≤≣ : Γ ⊢ T ≣ T′ → Γ ⊢ T ≤ T′

  -- equality of types
  _⊢_≣_ : Ctx → Exp → Exp → Set
  Γ ⊢ T ≣ T′ = ∀ {k} → Γ ⊢ T ≣ T′ ∷ ` 𝒰 k

  -- equality of expressions
  data _⊢_≣_∷_ : Ctx → Exp → Exp → Exp → Set where

  -- typing of substitutions
  data _⊢_⦂_ : Ctx → Subst → Ctx → Set where
    ⊢↑ : Γ • S ⊢ ↑ ⦂ Γ

    ⊢id : Γ ⊢ id ⦂ Γ

    ⊢∘ : Γ₁ ⊢ τ ⦂ Γ₂ → Γ₂ ⊢ σ ⦂ Γ₃ → Γ₁ ⊢ σ ∘ τ ⦂ Γ₃

    ⊢• : Γ ⊢ σ ⦂ Δ → Γ ⊢ s ∷ S → Γ ⊢ σ • s ⦂ Δ • S

{- Semantics -}

mutual
  -- environments
  Env = ℕ → Domain

  -- domain of evaluation
  data Domain : Set where
    ⟨λ_⟩_ : Exp → Env → Domain
    ↑[_]_ : Domain → Domainⁿᵉ → Domain
    `_ : Cst → Domain
    Fun1 : Domain → Domain
    Fun2 : Domain → Domain → Domain

  -- neutral forms of domain (target of Rⁿᵉ)
  data Domainⁿᵉ : Set where
    lvl : ℕ → Domainⁿᵉ
    _·_ : Domainⁿᵉ → Domainⁿᶠ → Domainⁿᵉ
    rec : Domainⁿᶠ → Domainⁿᶠ → Domainⁿᶠ → Domainⁿᵉ → Domainⁿᵉ

  -- normal forms of domain (target of Rⁿᶠ)
  data Domainⁿᶠ : Set where
    ↓[_]_ : Domain → Domain → Domainⁿᶠ

variable a b f A A′ F B B′ : Domain
variable ρ : Env
variable e E : Domainⁿᵉ
variable d D : Domainⁿᶠ

-- base "types" in domain
data Base : Domain → Set where
  unit : Base (` 𝟙)
  univ : (k : ℕ) → Base (` 𝒰 k)
  reflect : (k : ℕ) → (E : Domainⁿᵉ) → Base (↑[ ` 𝒰 k ] E)

-- "empty" environment (absurd environment)
∅ : Env
∅ = λ z → ` 𝟙

-- environment extension
⟨_,_⟩ : Env → Domain → Env
⟨ ρ , a ⟩ zero = a
⟨ ρ , a ⟩ (suc x) = ρ x

-- non-dependent function space in domain
_⇒ᴰ_ : Domain → Domain → Domain
A₁ ⇒ᴰ A₂ = Fun2 A₁ (⟨λ var (suc zero)⟩ ⟨ ∅ , A₂ ⟩)

-- evaluating expressions into domain
mutual
  data _·_↘_ : Domain → Domain → Domain → Set where
    clos· : ⦅ t ⦆ ⟨ ρ , a ⟩ ↘ b → ⟨λ t ⟩ ρ · a ↘ b

    ↑Fun· : F · a ↘ A′ → ↑[ Fun2 A F ] e · a ↘ ↑[ A′ ] (e · ↓[ A ] a)

    Fun· : ` Fun · A ↘ Fun1 A

    Fun1· : Fun1 A · F ↘ Fun2 A F

  data ⦅_⦆_↘_ : Exp → Env → Domain → Set where
    ⦅cst⦆ : ⦅ ` c ⦆ ρ ↘ ` c

    ⦅var⦆ : ρ i ≡ a → ⦅ var i ⦆ ρ ↘ a

    ⦅abs⦆ : ⦅ ƛ t ⦆ ρ ↘ ⟨λ t ⟩ ρ

    ⦅app⦆ : ⦅ r ⦆ ρ ↘ f → ⦅ s ⦆ ρ ↘ a → f · a ↘ b → ⦅ r · s ⦆ ρ ↘ b

-- reading back a normal/neutral form from domain
mutual
  data Rⁿᶠ_⦂_↘_ : ℕ → Domainⁿᶠ → Nf → Set where
    RⁿᶠFun : F · ↑[ A ] lvl n ↘ A′
           → f · ↑[ A ] lvl n ↘ b
           → Rⁿᶠ suc n ⦂ ↓[ A′ ] b ↘ v
           → Rⁿᶠ n ⦂ ↓[ Fun2 A F ] f ↘ ƛ v

    Rⁿᶠone : Rⁿᶠ n ⦂ ↓[ ` 𝟙 ] ` one ↘ one

    Rⁿᶠ𝒰-𝟙 : Rⁿᶠ n ⦂ ↓[ ` 𝒰 k ] ` 𝟙 ↘ 𝟙

    Rⁿᶠ𝒰-𝒰 : Rⁿᶠ n ⦂ ↓[ ` 𝒰 k ] ` 𝒰 i ↘ 𝒰 i

    Rⁿᶠ𝒰-Fun : Rⁿᶠ n ⦂ ↓[ ` 𝒰 k ] A ↘ V
             → Rⁿᶠ n ⦂ ↓[ A ⇒ᴰ ` 𝒰 k ] F ↘ W
             → Rⁿᶠ n ⦂ ↓[ ` 𝒰 k ] Fun2 A F ↘ Fun V W

    Rⁿᶠ↑↓ : Base B → Base B′ → Rⁿᵉ n ⦂ e ↘ u → Rⁿᶠ n ⦂ ↓[ B ] ↑[ B′ ] e ↘ ` u

  data Rⁿᵉ_⦂_↘_ : ℕ → Domainⁿᵉ → Ne → Set where
    Rⁿᵉvar : Rⁿᵉ n ⦂ lvl k ↘ var (n - (suc k))

    Rⁿᵉapp : Rⁿᵉ n ⦂ e ↘ u
           → Rⁿᶠ n ⦂ d ↘ v
           → Rⁿᵉ n ⦂ e · d ↘ u · v

-- length of context
∣_∣ : Ctx → ℕ
∣ ε ∣ = zero
∣ Γ • _ ∣ = suc ∣ Γ ∣

-- reflection of contexts
data ↑_↘_ : Ctx → Env → Set where
  ↑ε : ↑ ε ↘ ∅

  ↑• : ↑ Γ ↘ ρ
     → ⦅ S ⦆ ρ ↘ A
     → ↑ Γ • S ↘ ⟨ ρ , ↑[ A ] lvl ∣ Γ ∣ ⟩

{- Normalization by Evaluation -}

{-
- normal form of a term t of type T in context Γ is:
-   + reflect Γ into environment ρ
-   + evaluate T in ρ to domain "type" A
-   + evaluate t in ρ to domain "value" a
-   + readback from a reified at A to value "v"
-}

nf : Exp → Ctx → Exp → Set
nf T Γ t =
  ∃[ ρ ] ∃[ A ] ∃[ a ] ∃[ v ]
    ↑ Γ ↘ ρ
  × ⦅ T ⦆ ρ ↘ A
  × ⦅ t ⦆ ρ ↘ a
  × Rⁿᶠ ∣ Γ ∣ ⦂ ↓[ A ] a ↘ v
