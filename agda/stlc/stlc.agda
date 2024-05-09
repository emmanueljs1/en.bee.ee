import Relation.Binary.PropositionalEquality as Eq
open import Data.Nat using (ℕ; suc; zero) renaming (_∸_ to _-_)
open import Data.Product using (∃-syntax; _×_)
open Eq using (_≡_)

module stlc where

variable x i j k n : ℕ

infix 5 ƛ_ ⟨ƛ_⟩_
infix 9 _[_] ↑[_]_ ↓[_]_
infixl 8 _·_
infixl 5 _∘_
infixl 6 _•_
infixr 7 _⇒_
infix 4 _∷_∈_ _⊢_∷_ _⊢_⦂_ _⊢_≣_∷_ _⊢_≣_⦂_ _·_↘_ ⟦_⟧_↘_ Rⁿᶠ_⦂_↘_ Rⁿᵉ_⦂_↘_ ↑_↘_

mutual
  -- terms
  data Exp : Set where
    var : ℕ → Exp
    one : Exp
    ƛ_ : Exp → Exp
    _·_ : Exp → Exp → Exp
    _[_] : Exp → Subst → Exp

  -- substitutions
  data Subst : Set where
    ↑ : Subst
    id : Subst
    _∘_ : Subst → Subst → Subst
    _•_ : Subst → Exp → Subst

variable r s t r′ s′ t′ t₁ t₂ t₃ : Exp
variable σ τ σ′ τ′ σ₃ σ₂ σ₁ : Subst

-- types
data Type : Set where
  𝟙 : Type
  _⇒_ : Type → Type → Type

variable S T : Type

-- contexts
data Ctx : Set where
  ε : Ctx
  _•_ : Ctx → Type → Ctx

variable Γ Δ Γ′ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx

-- variable lookup
data _∷_∈_ : ℕ → Type → Ctx → Set where
  here : zero ∷ T ∈ Γ • T

  there : x ∷ T ∈ Γ → suc x ∷ T ∈ Γ • S

mutual
  -- syntactic typing of terms
  data _⊢_∷_ : Ctx → Exp → Type → Set where
    ⊢one : Γ ⊢ one ∷ 𝟙
    ⊢var : x ∷ T ∈ Γ → Γ ⊢ var x ∷ T
    ⊢abs : Γ • S ⊢ t ∷ T → Γ ⊢ ƛ t ∷ S ⇒ T
    ⊢app : Γ ⊢ r ∷ S ⇒ T → Γ ⊢ s ∷ S → Γ ⊢ r · s ∷ T
    ⊢sub : Γ ⊢ σ ⦂ Δ → Δ ⊢ t ∷ T → Γ ⊢ t [ σ ] ∷ T

  -- syntactic typing of substitutions
  data _⊢_⦂_ : Ctx → Subst → Ctx → Set where
    ⊢up : Γ • S ⊢ ↑ ⦂ Γ
    ⊢id : Γ ⊢ id ⦂ Γ
    ⊢comp : Γ₁ ⊢ τ ⦂ Γ₂ → Γ₂ ⊢ σ ⦂ Γ₃ → Γ₁ ⊢ σ ∘ τ ⦂ Γ₃
    ⊢ext : Γ ⊢ σ ⦂ Δ → Γ ⊢ s ∷ S → Γ ⊢ σ • s ⦂ Δ • S

mutual
  -- syntactic term equality
  data _⊢_≣_∷_ : Ctx → Exp → Exp → Type → Set where
    β : Γ • S ⊢ t ∷ T
      → Γ ⊢ s ∷ S
      → Γ ⊢ (ƛ t) · s ≣ t [ id • s ] ∷ T

    η : Γ ⊢ t ∷ S ⇒ T
      → Γ ⊢ t ≣ ƛ t [ ↑ ] · var zero ∷ S ⇒ T

    var-↑ : x ∷ T ∈ Γ
          → Γ • S ⊢ var x [ ↑ ] ≣ var (suc x) ∷ T

    [id] : Γ ⊢ t ∷ T
         → Γ ⊢ t [ id ] ≣ t ∷ T

    zero-• : Γ ⊢ σ ⦂ Δ
           → Γ ⊢ s ∷ S
           → Γ ⊢ var zero [ σ • s ] ≣ s ∷ S

    suc-• : Γ ⊢ σ ⦂ Δ
          → Γ ⊢ s ∷ S
          → x ∷ T ∈ Δ
          → Γ ⊢ var (suc x) [ σ • s ] ≣ var x [ σ ] ∷ T

    one-sub : Γ ⊢ σ ⦂ Δ
             → Γ ⊢ one [ σ ] ≣ one ∷ 𝟙

    abs-sub : Γ ⊢ σ ⦂ Δ
            → Δ • S ⊢ t ∷ T
            → Γ ⊢ (ƛ t) [ σ ] ≣ ƛ t [ (σ ∘ ↑) • var zero ] ∷ S ⇒ T

    app-sub : Γ ⊢ σ ⦂ Δ
            → Δ ⊢ r ∷ S ⇒ T
            → Δ ⊢ s ∷ S
            → Γ ⊢ (r · s) [ σ ] ≣ r [ σ ] · s [ σ ] ∷ T

    sub-comp : Γ₁ ⊢ τ ⦂ Γ₂
             → Γ₂ ⊢ σ ⦂ Γ₃
             → Γ₃ ⊢ t ∷ T
             → Γ ⊢ t [ σ ] [ τ ] ≣ t [ σ ∘ τ ] ∷ T

    app-compatible : Γ ⊢ r ≣ r′ ∷ S ⇒ T
                   → Γ ⊢ s ≣ s′ ∷ S
                   → Γ ⊢ r · s ≣ r′ · s′ ∷ T

    ξ : Γ • S ⊢ t ≣ t′ ∷ T
      → Γ ⊢ ƛ t ≣ ƛ t′ ∷ T

    refl : Γ ⊢ t ∷ T
         → Γ ⊢ t ≣ t ∷ T

    sym : Γ ⊢ t ≣ t′ ∷ T
        → Γ ⊢ t′ ≣ t ∷ T

    trans : Γ ⊢ t₁ ≣ t₂ ∷ T
          → Γ ⊢ t₂ ≣ t₃ ∷ T
          → Γ ⊢ t₁ ≣ t₃ ∷ T

  -- syntactic substitution equality
  data _⊢_≣_⦂_ : Ctx → Subst → Subst → Ctx → Set where
    up-ext : Γ ⊢ σ ⦂ Δ
           → Γ ⊢ s ∷ S
           → Γ ⊢ ↑ ∘ (σ • s) ≣ σ ⦂ Δ

    comp-identityˡ : Γ ⊢ σ ⦂ Δ
                   → Γ ⊢ id ∘ σ ≣ σ ⦂ Δ

    comp-identityʳ : Γ ⊢ σ ⦂ Δ
                   → Γ ⊢ σ ∘ id ≣ σ ⦂ Δ

    comp-assoc : Γ₄ ⊢ σ₃ ⦂ Γ₃
               → Γ₃ ⊢ σ₂ ⦂ Γ₂
               → Γ₂ ⊢ σ₁ ⦂ Γ₁
               → Γ₄ ⊢ σ₁ ∘ σ₂ ∘ σ₃ ≣ σ₁ ∘ (σ₂ ∘ σ₃) ⦂ Γ₁

    η-id : Γ • S ⊢ id ≣ (↑ • var zero) ⦂ Γ • S

    up-comp : Γ ⊢ τ ⦂ Γ′
            → Γ′ ⊢ σ ⦂ Δ
            → Γ′ ⊢ s ∷ S
            → Γ ⊢ (σ • s) ∘ τ ≣ (σ ∘ τ) • s [ τ ] ⦂ Δ • S

    ext-compatible : Γ ⊢ σ ≣ σ′ ⦂ Δ
                   → Γ ⊢ s ≣ s′ ∷ S
                   → Γ ⊢ σ • s ≣ σ′ • s′ ⦂ Δ • S

    comp-compatible : Γ₁ ⊢ σ ≣ σ′ ⦂ Γ₂
                    → Γ₂ ⊢ τ ≣ τ′ ⦂ Γ₃
                    → Γ₁ ⊢ σ ∘ τ ≣ σ′ ∘ τ′ ⦂ Γ₃

    refl : Γ ⊢ σ ⦂ Δ
         → Γ ⊢ σ ≣ σ ⦂ Δ

    sym : Γ ⊢ σ ≣ σ′ ⦂ Δ
        → Γ ⊢ σ′ ≣ σ ⦂ Δ

    trans : Γ ⊢ σ₁ ≣ σ₂ ⦂ Δ
          → Γ ⊢ σ₂ ≣ σ₃ ⦂ Δ
          → Γ ⊢ σ₁ ≣ σ₃ ⦂ Δ

mutual
  -- domain of evaluation
  data D : Set where
    ⟨ƛ_⟩_ : Exp → Env → D
    ↑[_]_ : Type → Dⁿᵉ → D
    one : D

  -- target of readback for neutrals
  data Dⁿᵉ : Set where
    lvl : ℕ → Dⁿᵉ
    _·_ : Dⁿᵉ → Dⁿᶠ → Dⁿᵉ

  -- target of readback for normals
  data Dⁿᶠ : Set where
    ↓[_]_ : Type → D → Dⁿᶠ

  -- environment
  Env = ℕ → D

variable ρ ρ′ ρ″ : Env
variable a b f : D
variable e : Dⁿᵉ
variable d : Dⁿᶠ

-- environment extension
⟨_,_⟩ : Env → D → Env
⟨ ρ , a ⟩ zero = a
⟨ ρ , a ⟩ (suc x) = ρ x

mutual
  -- partial application in domain
  data _·_↘_ : D → D → D → Set where
    clos· : ⟦ t ⟧ ⟨ ρ , a ⟩ ↘ b
          → ⟨ƛ t ⟩ ρ · a ↘ b

    ↑fun· : ↑[ S ⇒ T ] e · a ↘ ↑[ T ] (e · ↓[ S ] a)

  -- evaluation of terms to domain
  data ⟦_⟧_↘_ : Exp → Env → D → Set where
    ⟦one⟧ : ⟦ one ⟧ ρ ↘ one

    ⟦var⟧ : ρ i ≡ a → ⟦ var i ⟧ ρ ↘ a

    ⟦abs⟧ : ⟦ ƛ t ⟧ ρ ↘ ⟨ƛ t ⟩ ρ

    ⟦app⟧ : ⟦ r ⟧ ρ ↘ f
          → ⟦ s ⟧ ρ ↘ a
          → f · a ↘ b
          → ⟦ r · s ⟧ ρ ↘ b

    ⟦sub⟧ : ⦅ σ ⦆ ρ ↘ ρ′
          → ⟦ t ⟧ ρ′ ↘ a
          → ⟦ t [ σ ] ⟧ ρ ↘ a

  -- evaluation fo substitutions to environments
  data ⦅_⦆_↘_ : Subst → Env → Env → Set where
    ⦅up⦆ : ⦅ ↑ ⦆ ⟨ ρ , a ⟩ ↘ ρ

    ⦅id⦆ : ⦅ id ⦆ ρ ↘ ρ

    ⦅comp⦆ : ⦅ τ ⦆ ρ ↘ ρ′
           → ⦅ σ ⦆ ρ′ ↘ ρ″
           → ⦅ σ ∘ τ ⦆ ρ ↘ ρ″

    ⦅ext⦆ : ⦅ σ ⦆ ρ ↘ ρ′
          → ⟦ s ⟧ ρ ↘ a
          → ⦅ σ • s ⦆ ρ ↘ ⟨ ρ′ , a ⟩

mutual
  -- normal terms
  data Nf : Set where
    one : Nf
    ƛ_ : Nf → Nf
    `_ : Ne → Nf

  -- neutral terms
  data Ne : Set where
    var : ℕ → Ne
    _·_ : Ne → Nf → Ne

variable v : Nf
variable u : Ne

mutual
  -- readback of normal term from domain
  data Rⁿᶠ_⦂_↘_ : ℕ → Dⁿᶠ → Nf → Set where
    Rⁿᶠone : Rⁿᶠ n ⦂ ↓[ 𝟙 ] one ↘ one

    Rⁿᶠfun : f · ↑[ S ] lvl n ↘ b
           → Rⁿᶠ suc n ⦂ ↓[ T ] b ↘ v
           → Rⁿᶠ n ⦂ ↓[ S ⇒ T ] f ↘ ƛ v

    Rⁿᶠ↓↑ : Rⁿᵉ n ⦂ e ↘ u
          → Rⁿᶠ n ⦂ ↓[ 𝟙 ] ↑[ 𝟙 ] e ↘ ` u

  -- readback of neutral term from domain
  data Rⁿᵉ_⦂_↘_ : ℕ → Dⁿᵉ → Ne → Set where
    Rⁿᵉvar : Rⁿᵉ n ⦂ lvl k ↘ var (n - (suc k))

    Rⁿᵉapp : Rⁿᵉ n ⦂ e ↘ u
           → Rⁿᶠ n ⦂ d ↘ v
           → Rⁿᵉ n ⦂ e · d ↘ u · v

-- absurd ("empty") environment
∅ : Env
∅ = λ _ → one

-- length of context
∣_∣ : Ctx → ℕ
∣ ε ∣ = zero
∣ Γ • _ ∣ = suc ∣ Γ ∣

-- reflection of context to an environment
data ↑_↘_ : Ctx → Env → Set where
  ↑empty : ↑ ε ↘ ∅

  ↑ext : ↑ Γ ↘ ρ
       → ↑ Γ • S ↘ ⟨ ρ , ↑[ S ] lvl ∣ Γ ∣ ⟩

-- normalization by evaluation:
--   + reflect context into environment
--   + evaluate term in environment
--   + readback normal term from evaluation
--
-- (formulated relationally)
nf : Type → Ctx → Exp → Set
nf T Γ t =
  ∃[ ρ ] ∃[ a ] ∃[ v ]
    ↑ Γ ↘ ρ
  × ⟦ t ⟧ ρ ↘ a
  × Rⁿᶠ ∣ Γ ∣ ⦂ ↓[ T ] a ↘ v
