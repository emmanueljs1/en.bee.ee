import Relation.Binary.PropositionalEquality as Eq
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_) renaming (_∸_ to _-_)
open import Data.Product using (∃-syntax; _×_)
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

data Cst : Set where
  Nat : Cst
  zero : Cst
  suc : Cst
  rec : Cst
  Fun : Cst
  𝒰 : ℕ → Cst

variable c : Cst

mutual
  data Exp : Set where
    `_ : Cst → Exp
    var : ℕ → Exp
    ƛ_ : Exp → Exp
    _·_ : Exp → Exp → Exp
    _[_] : Exp → Subst → Exp

  data Subst : Set where
    ↑ : Subst
    id : Subst
    _∘_ : Subst → Subst → Subst
    _•_ : Subst → Exp → Subst

variable r s t R S T T′ : Exp
variable σ τ : Subst

mutual
  data Nf : Set where
    `_ : Ne → Nf
    Fun : Nf → Nf → Nf
    ƛ_ : Nf → Nf
    Nat : Nf
    zero : Nf
    suc : Nf → Nf
    𝒰 : ℕ → Nf

  data Ne : Set where
    var : ℕ → Ne
    _·_ : Ne → Nf → Ne
    rec : Nf → Nf → Nf → Ne

variable v w V W : Nf
variable u U : Ne

data Ctx : Set where
  ε : Ctx
  _•_ : Ctx → Exp → Ctx

variable Γ Δ Γ₁ Γ₂ Γ₃ : Ctx

∣_∣ : Ctx → ℕ
∣ ε ∣ = zero
∣ Γ • _ ∣ = suc ∣ Γ ∣

data _[_]=_ : Ctx → ℕ → Exp → Set where
  here : Γ • S [ zero ]= S [ ↑ ]

  there : Γ [ i ]= S → Γ • T [ suc i ]= S [ ↑ ]

_⇒_ : Exp → Exp → Exp
S ⇒ T = ` Fun · S · (ƛ T [ ↑ ])

Rec : ℕ → Exp
Rec k =
  (` Nat ⇒ ` 𝒰 k) ⇒ -- (P : N → Set k)
  var zero · ` zero ⇒ -- P zero
  (` Nat ⇒ var (suc zero) · var zero ⇒ var (suc zero) · (` suc · var zero)) ⇒ -- (x : N) → P x → P (suc x)
  ` Nat ⇒ -- (y : N)
  var (suc zero) · var zero -- P x

data _∷_ : Cst → Exp → Set where
  ∷zero : zero ∷ ` Nat

  ∷suc : suc ∷ ` Nat ⇒ ` Nat

  ∷rec : rec ∷ Rec k

  ∷Nat : Nat ∷ ` 𝒰 k

  ∷Fun : ∀ {i j k} → i ≤ k → j ≤ k
       → Fun ∷ ` Fun · ` 𝒰 i · (ƛ (var zero ⇒ ` 𝒰 j) ⇒ ` 𝒰 k)

  ∷𝒰 : ∀ {i j} → i < j → 𝒰 i ∷ ` 𝒰 k

mutual
  data ⊢_ : Ctx → Set where
    ⊢ε : ⊢ ε

    ⊢• : ⊢ Γ → Γ ⊢ T → ⊢ Γ • T

  _⊢_ : Ctx → Exp → Set
  Γ ⊢ T = ∀ {k} → Γ ⊢ T ∷ ` 𝒰 k

  data _⊢_∷_ : Ctx → Exp → Exp → Set where
    ⊢cst : ⊢ Γ → c ∷ T → Γ ⊢ ` c ∷ T

    ⊢subst : Γ ⊢ σ ⦂ Δ → Δ ⊢ t ∷ T → Γ ⊢ t [ σ ] ∷ T [ σ ]

    ⊢var : ⊢ Γ → Γ [ i ]= S → Γ ⊢ var i ∷ S

    ⊢abs : Γ • S ⊢ t ∷ T → Γ ⊢ ƛ t ∷ ` Fun · S · (ƛ T)

    ⊢app : Γ ⊢ r ∷ ` Fun · S · R → Γ ⊢ s ∷ S → Γ ⊢ r · s ∷ R · s

    ⊢sub : Γ ⊢ t ∷ T → Γ ⊢ T ≤ T′ → Γ ⊢ t ∷ T′

  data _⊢_≤_ : Ctx → Exp → Exp → Set where
    ≤𝒰 : k ≤ l → Γ ⊢ ` 𝒰 k ≤ ` 𝒰 l

    ≤≣ : Γ ⊢ T ≣ T′ → Γ ⊢ T ≤ T′

  _⊢_≣_ : Ctx → Exp → Exp → Set
  Γ ⊢ T ≣ T′ = ∀ {k} → Γ ⊢ T ≣ T′ ∷ ` 𝒰 k

  data _⊢_≣_∷_ : Ctx → Exp → Exp → Exp → Set where

  data _⊢_⦂_ : Ctx → Subst → Ctx → Set where
    ⊢↑ : Γ • S ⊢ ↑ ⦂ Γ

    ⊢id : Γ ⊢ id ⦂ Γ

    ⊢∘ : Γ₁ ⊢ τ ⦂ Γ₂ → Γ₂ ⊢ σ ⦂ Γ₃ → Γ₁ ⊢ σ ∘ τ ⦂ Γ₃

    ⊢• : Γ ⊢ σ ⦂ Δ → Γ ⊢ s ∷ S → Γ ⊢ σ • s ⦂ Δ • S

mutual
  Env = ℕ → Domain

  data Domain : Set where
    ⟨λ_⟩_ : Exp → Env → Domain
    ↑[_]_ : Domain → Domainⁿᵉ → Domain
    `_ : Cst → Domain
    suc1 : Domain → Domain
    rec1 : Domain → Domain
    rec2 : Domain → Domain → Domain
    rec3 : Domain → Domain → Domain → Domain
    Fun1 : Domain → Domain
    Fun2 : Domain → Domain → Domain
    ``_ : Base → Domain

  data Base : Set where
    Nat : Base
    𝒰 : ℕ → Base
    ↑[_]_ : ℕ → Domainⁿᵉ → Base

  data Domainⁿᵉ : Set where
    lvl : ℕ → Domainⁿᵉ
    _·_ : Domainⁿᵉ → Domainⁿᶠ → Domainⁿᵉ
    rec : Domainⁿᶠ → Domainⁿᶠ → Domainⁿᶠ → Domainⁿᵉ → Domainⁿᵉ

  data Domainⁿᶠ : Set where
    ↓[_]_ : Domain → Domain → Domainⁿᶠ

variable a b f A A′ F : Domain
variable B B′ : Base
variable ρ : Env
variable e E : Domainⁿᵉ
variable d D : Domainⁿᶠ

-- absurd ("empty") environment
∅ : Env
∅ = λ z → ` Nat

⟨_,_⟩ : Env → Domain → Env
⟨ ρ , a ⟩ zero = a
⟨ ρ , a ⟩ (suc x) = ρ x

_⇒ᴰ_ : Domain → Domain → Domain
A₁ ⇒ᴰ A₂ = Fun2 A₁ (⟨λ var (suc zero)⟩ ⟨ ∅ , A₂ ⟩)

mutual
  data _·_↘_ : Domain → Domain → Domain → Set where
    ·abs : ⦅ t ⦆ ⟨ ρ , a ⟩ ↘ b → ⟨λ t ⟩ ρ · a ↘ b

    ·app : F · a ↘ A′ → ↑[ Fun2 A F ] e · a ↘ ↑[ A′ ] (e · ↓[ A ] a)

  data ⦅_⦆_↘_ : Exp → Env → Domain → Set where
    ⦅var⦆ : ρ i ≡ a → ⦅ var i ⦆ ρ ↘ a

    ⦅abs⦆ : ⦅ ƛ t ⦆ ρ ↘ ⟨λ t ⟩ ρ

    ⦅app⦆ : ⦅ r ⦆ ρ ↘ f → ⦅ s ⦆ ρ ↘ a → f · a ↘ b → ⦅ r · s ⦆ ρ ↘ b

mutual
  data Rⁿᶠ_⦂_↘_ : ℕ → Domainⁿᶠ → Nf → Set where
    RⁿᶠFun : F · ↑[ A ] lvl n ↘ A′
           → f · ↑[ A ] lvl n ↘ b
           → Rⁿᶠ suc n ⦂ ↓[ A′ ] b ↘ v
           → Rⁿᶠ n ⦂ ↓[ Fun2 A F ] f ↘ ƛ v

    Rⁿᶠzero : Rⁿᶠ n ⦂ ↓[ `` Nat ] ` zero ↘ zero

    Rⁿᶠsuc : Rⁿᶠ n ⦂ ↓[ `` Nat ] a ↘ v
           → Rⁿᶠ n ⦂ ↓[ `` Nat ] suc1 a ↘ suc v

    Rⁿᶠ𝒰-Nat : Rⁿᶠ n ⦂ ↓[ `` 𝒰 k ] ` Nat ↘ Nat

    Rⁿᶠ𝒰-𝒰 : Rⁿᶠ n ⦂ ↓[ `` 𝒰 k ] ` 𝒰 i ↘ 𝒰 i

    Rⁿᶠ𝒰-Fun : Rⁿᶠ n ⦂ ↓[ `` 𝒰 k ] A ↘ V
             → Rⁿᶠ n ⦂ ↓[ A ⇒ᴰ `` 𝒰 k ] F ↘ W
             → Rⁿᶠ n ⦂ ↓[ `` 𝒰 k ] Fun2 A F ↘ Fun V W

    Rⁿᶠ↑↓ : Rⁿᵉ n ⦂ e ↘ u → Rⁿᶠ n ⦂ ↓[ `` B ] ↑[ `` B′ ] e ↘ ` u

  data Rⁿᵉ_⦂_↘_ : ℕ → Domainⁿᵉ → Ne → Set where
    Rⁿᵉvar : Rⁿᵉ n ⦂ lvl k ↘ var (n - (suc k))

    Rⁿᵉapp : Rⁿᵉ n ⦂ e ↘ u
           → Rⁿᶠ n ⦂ d ↘ v
           → Rⁿᵉ n ⦂ e · d ↘ u · v

data ↑_↘_ : Ctx → Env → Set where
  ↑ε : ↑ ε ↘ ∅

  ↑• : ↑ Γ ↘ ρ
     → ⦅ S ⦆ ρ ↘ A
     → ↑ Γ • S ↘ ⟨ ρ , ↑[ A ] lvl ∣ Γ ∣ ⟩

nf : Exp → Ctx → Exp → Set
nf T Γ t =
  ∃[ ρ ] ∃[ A ] ∃[ a ] ∃[ v ]
    ↑ Γ ↘ ρ
  × ⦅ T ⦆ ρ ↘ A
  × ⦅ t ⦆ ρ ↘ a
  × Rⁿᶠ ∣ Γ ∣ ⦂ ↓[ A ] a ↘ v
