import Relation.Binary.PropositionalEquality as Eq
open import Data.Empty using () renaming (⊥ to Empty)
open import Data.Nat using (ℕ; suc; zero) renaming (_∸_ to _-_)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Unit using (tt) renaming (⊤ to Unit)
open import Relation.Binary using (IsEquivalence)
open import Relation.Unary using (_∈_)
open Eq using (_≡_; refl)

module stlc where

variable x i j k n : ℕ

infix 5 ƛ_ ⟨ƛ_⟩_
infix 9 _[_] ↑[_]_ ↓[_]_
infixl 8 _·_
infixl 5 _∘_
infixl 6 _•_
infixr 7 _⇒_ _⟶_
infix 4 _∷_∈_ _⊢_∷_ _⊢_⦂_ _⊢_==_∷_ _⊢_==_⦂_
infix 4 _↦_∈_ _·_↘_ ⟦_⟧_↘_ ⦅_⦆_↘_ Rⁿᶠ_⦂_↘_ Rⁿᵉ_⦂_↘_
infix 4 _==_∈_ _⊨_==_∷_ _⊨_==_⦂_

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

variable Γ Δ Γ′ Γ₁ Γ₂ Γ₃ Γ₄ Ψ : Ctx

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
  data _⊢_==_∷_ : Ctx → Exp → Exp → Type → Set where
    β : Γ • S ⊢ t ∷ T
      → Γ ⊢ s ∷ S
      → Γ ⊢ (ƛ t) · s == t [ id • s ] ∷ T

    η : Γ ⊢ t ∷ S ⇒ T
      → Γ ⊢ t == ƛ t [ ↑ ] · var zero ∷ S ⇒ T

    var-↑ : x ∷ T ∈ Γ
          → Γ • S ⊢ var x [ ↑ ] == var (suc x) ∷ T

    [id] : Γ ⊢ t ∷ T
         → Γ ⊢ t [ id ] == t ∷ T

    zero-• : Γ ⊢ σ ⦂ Δ
           → Γ ⊢ s ∷ S
           → Γ ⊢ var zero [ σ • s ] == s ∷ S

    suc-• : Γ ⊢ σ ⦂ Δ
          → Γ ⊢ s ∷ S
          → x ∷ T ∈ Δ
          → Γ ⊢ var (suc x) [ σ • s ] == var x [ σ ] ∷ T

    one-sub : Γ ⊢ σ ⦂ Δ
             → Γ ⊢ one [ σ ] == one ∷ 𝟙

    abs-sub : Γ ⊢ σ ⦂ Δ
            → Δ • S ⊢ t ∷ T
            → Γ ⊢ (ƛ t) [ σ ] == ƛ t [ (σ ∘ ↑) • var zero ] ∷ S ⇒ T

    app-sub : Γ ⊢ σ ⦂ Δ
            → Δ ⊢ r ∷ S ⇒ T
            → Δ ⊢ s ∷ S
            → Γ ⊢ (r · s) [ σ ] == r [ σ ] · s [ σ ] ∷ T

    sub-comp : Γ₁ ⊢ τ ⦂ Γ₂
             → Γ₂ ⊢ σ ⦂ Γ₃
             → Γ₃ ⊢ t ∷ T
             → Γ₁ ⊢ t [ σ ] [ τ ] == t [ σ ∘ τ ] ∷ T

    app-compatible : Γ ⊢ r == r′ ∷ S ⇒ T
                   → Γ ⊢ s == s′ ∷ S
                   → Γ ⊢ r · s == r′ · s′ ∷ T

    ξ : Γ • S ⊢ t == t′ ∷ T
      → Γ ⊢ ƛ t == ƛ t′ ∷ S ⇒ T

    refl : Γ ⊢ t ∷ T
         → Γ ⊢ t == t ∷ T

    sym : Γ ⊢ t == t′ ∷ T
        → Γ ⊢ t′ == t ∷ T

    trans : Γ ⊢ t₁ == t₂ ∷ T
          → Γ ⊢ t₂ == t₃ ∷ T
          → Γ ⊢ t₁ == t₃ ∷ T

  -- syntactic substitution equality
  data _⊢_==_⦂_ : Ctx → Subst → Subst → Ctx → Set where
    up-ext : Γ ⊢ σ ⦂ Δ
           → Γ ⊢ s ∷ S
           → Γ ⊢ ↑ ∘ (σ • s) == σ ⦂ Δ

    comp-identityˡ : Γ ⊢ σ ⦂ Δ
                   → Γ ⊢ id ∘ σ == σ ⦂ Δ

    comp-identityʳ : Γ ⊢ σ ⦂ Δ
                   → Γ ⊢ σ ∘ id == σ ⦂ Δ

    comp-assoc : Γ₄ ⊢ σ₃ ⦂ Γ₃
               → Γ₃ ⊢ σ₂ ⦂ Γ₂
               → Γ₂ ⊢ σ₁ ⦂ Γ₁
               → Γ₄ ⊢ σ₁ ∘ σ₂ ∘ σ₃ == σ₁ ∘ (σ₂ ∘ σ₃) ⦂ Γ₁

    η-id : Γ • S ⊢ id == (↑ • var zero) ⦂ Γ • S

    up-comp : Γ ⊢ τ ⦂ Γ′
            → Γ′ ⊢ σ ⦂ Δ
            → Γ′ ⊢ s ∷ S
            → Γ ⊢ (σ • s) ∘ τ == (σ ∘ τ) • s [ τ ] ⦂ Δ • S

    ext-compatible : Γ ⊢ σ == σ′ ⦂ Δ
                   → Γ ⊢ s == s′ ∷ S
                   → Γ ⊢ σ • s == σ′ • s′ ⦂ Δ • S

    comp-compatible : Γ₁ ⊢ τ == τ′ ⦂ Γ₂
                    → Γ₂ ⊢ σ == σ′ ⦂ Γ₃
                    → Γ₁ ⊢ σ ∘ τ == σ′ ∘ τ′ ⦂ Γ₃

    refl : Γ ⊢ σ ⦂ Δ
         → Γ ⊢ σ == σ ⦂ Δ

    sym : Γ ⊢ σ == σ′ ⦂ Δ
        → Γ ⊢ σ′ == σ ⦂ Δ

    trans : Γ ⊢ σ₁ == σ₂ ⦂ Δ
          → Γ ⊢ σ₂ == σ₃ ⦂ Δ
          → Γ ⊢ σ₁ == σ₃ ⦂ Δ

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
  data Env : Set where
    ε : Env
    _•_ : Env → D → Env

variable γ γ′ γ″ δ δ′ δ″ ψ : Env
variable a a′ a″ b b′ f f′ : D
variable e e′ : Dⁿᵉ
variable d d′ : Dⁿᶠ

data _↦_∈_ : ℕ → D → Env → Set where
  here : zero ↦ a ∈ γ • a

  there : x ↦ a ∈ γ → suc x ↦ a ∈ γ • b

mutual
  -- partial application in domain
  data _·_↘_ : D → D → D → Set where
    clos· : ⟦ t ⟧ (δ • a) ↘ b
          → ⟨ƛ t ⟩ δ · a ↘ b

    ↑fun· : ↑[ S ⇒ T ] e · a ↘ ↑[ T ] (e · ↓[ S ] a)

  -- evaluation of terms to domain
  data ⟦_⟧_↘_ : Exp → Env → D → Set where
    ⟦one⟧ : ⟦ one ⟧ γ ↘ one

    ⟦var⟧ : x ↦ a ∈ γ → ⟦ var x ⟧ γ ↘ a

    ⟦abs⟧ : ⟦ ƛ t ⟧ γ ↘ ⟨ƛ t ⟩ γ

    ⟦app⟧ : ⟦ r ⟧ γ ↘ f
          → ⟦ s ⟧ γ ↘ a
          → f · a ↘ b
          → ⟦ r · s ⟧ γ ↘ b

    ⟦sub⟧ : ⦅ σ ⦆ γ ↘ δ
          → ⟦ t ⟧ δ ↘ a
          → ⟦ t [ σ ] ⟧ γ ↘ a

  -- evaluation for substitutions to environments
  data ⦅_⦆_↘_ : Subst → Env → Env → Set where
    ⦅up⦆ : ⦅ ↑ ⦆ (γ • a) ↘ γ

    ⦅id⦆ : ⦅ id ⦆ γ ↘ γ

    ⦅comp⦆ : ⦅ τ ⦆ γ ↘ δ
           → ⦅ σ ⦆ δ ↘ ψ
           → ⦅ σ ∘ τ ⦆ γ ↘ ψ

    ⦅ext⦆ : ⦅ σ ⦆ γ ↘ δ
          → ⟦ s ⟧ γ ↘ a
          → ⦅ σ • s ⦆ γ ↘ δ • a

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

variable v v′ : Nf
variable u u′ : Ne

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

-- length of context
∣_∣ : Ctx → ℕ
∣ ε ∣ = zero
∣ Γ • _ ∣ = suc ∣ Γ ∣

-- reflection of context to an environment
env : Ctx → Env
env ε = ε
env (Γ • S) = env Γ • ↑[ S ] lvl ∣ Γ ∣

-- normalization by evaluation:
--   + reflect context into environment
--   + evaluate term in environment
--   + readback normal term from evaluation
--
-- (formulated relationally)
nf : Type → Ctx → Exp → Set
nf T Γ t = ∃[ a ] ∃[ v ] ⟦ t ⟧ (env Γ) ↘ a × Rⁿᶠ ∣ Γ ∣ ⦂ ↓[ T ] a ↘ v

~_ : nf T Γ t → Nf
~ (_ , v , _) = v

SemType = D × D → Set

variable 𝒜 ℬ : SemType

_==_∈_ : ∀ {A : Set} → A → A → (A × A → Set) → Set
a == a′ ∈ 𝒜 = 𝒜 (a , a′)

_⟶_ : SemType → SemType → SemType
(𝒜 ⟶ ℬ) (f , f′) =
  ∀ {a a′}
  → a == a′ ∈ 𝒜
  → ∃[ b ] ∃[ b′ ]
      f · a ↘ b
    × f′ · a′ ↘ b′
    × b == b′ ∈ ℬ

⊥ : Dⁿᵉ × Dⁿᵉ → Set
⊥ (e , e′) =
  ∀ n → ∃[ u ] Rⁿᵉ n ⦂ e ↘ u × Rⁿᵉ n ⦂ e′ ↘ u

⊤ : Dⁿᶠ × Dⁿᶠ → Set
⊤ (d , d′) =
  ∀ n → ∃[ v ] Rⁿᶠ n ⦂ d ↘ v × Rⁿᶠ n ⦂ d′ ↘ v

⟦_⟧ : Type → SemType
⟦ 𝟙 ⟧ (one , one) = Unit
⟦ 𝟙 ⟧ (↑[ 𝟙 ] e , ↑[ 𝟙 ] e′) = e == e′ ∈ ⊥
⟦ S ⇒ T ⟧ = ⟦ S ⟧ ⟶ ⟦ T ⟧
⟦ _ ⟧ _ = Empty

semtype-sym : a == a′ ∈ ⟦ T ⟧ → a′ == a ∈ ⟦ T ⟧
semtype-sym {one} {one} {𝟙} _ = tt
semtype-sym {↑[ 𝟙 ] e} {↑[ 𝟙 ] e′} {𝟙} e==e′ n
  with e==e′ n
... | u , e↘ , e′↘ = u , e′↘ , e↘
semtype-sym {f} {f′} {S ⇒ T} f==f′ {a} {a′} a==a′
  with f==f′ (semtype-sym {a} {a′} {S} a==a′)
... | b , b′ , ↘b , ↘b′ , b==b′ =
  b′ , b , ↘b′ , ↘b , semtype-sym {b} {b′} {T} b==b′

mutual
  lookup-unique : x ↦ a ∈ γ → x ↦ a′ ∈ γ → a ≡ a′
  lookup-unique here here = refl
  lookup-unique (there a∈ρ) (there a′∈ρ) = lookup-unique a∈ρ a′∈ρ

  eval-unique : ⟦ t ⟧ γ ↘ a → ⟦ t ⟧ γ ↘ a′ → a ≡ a′
  eval-unique ⟦one⟧ ⟦one⟧ = refl
  eval-unique (⟦var⟧ a∈ρ) (⟦var⟧ a′∈ρ) = lookup-unique a∈ρ a′∈ρ
  eval-unique ⟦abs⟧ ⟦abs⟧ = refl
  eval-unique (⟦app⟧ ↘f ↘a ↘b) (⟦app⟧ ↘f′ ↘a′ ↘b′)
    rewrite eval-unique ↘f ↘f′ | eval-unique ↘a ↘a′ | app-unique ↘b ↘b′ = refl
  eval-unique (⟦sub⟧ ↘δ ↘a) (⟦sub⟧ ↘δ′ ↘a′)
    rewrite eval-sub-unique ↘δ ↘δ′ | eval-unique ↘a ↘a′ = refl

  app-unique : f · a ↘ b → f · a ↘ b′ → b ≡ b′
  app-unique (clos· ↘b) (clos· ↘b′) rewrite eval-unique ↘b ↘b′ = refl
  app-unique ↑fun· ↑fun· = refl

  eval-sub-unique : ⦅ σ ⦆ γ ↘ δ → ⦅ σ ⦆ γ ↘ δ′ → δ ≡ δ′
  eval-sub-unique ⦅up⦆ ⦅up⦆ = refl
  eval-sub-unique ⦅id⦆ ⦅id⦆ = refl
  eval-sub-unique (⦅comp⦆ ↘δ₀ ↘δ₁) (⦅comp⦆ ↘δ₀′ ↘δ₁′)
    rewrite eval-sub-unique ↘δ₀ ↘δ₀′ | eval-sub-unique ↘δ₁ ↘δ₁′ = refl
  eval-sub-unique (⦅ext⦆ ↘δ ↘a) (⦅ext⦆ ↘δ′ ↘a′)
    rewrite eval-sub-unique ↘δ ↘δ′ | eval-unique ↘a ↘a′ = refl

mutual
  readback-ne-unique : Rⁿᵉ n ⦂ e ↘ u → Rⁿᵉ n ⦂ e ↘ u′ → u ≡ u′
  readback-ne-unique Rⁿᵉvar Rⁿᵉvar = refl
  readback-ne-unique (Rⁿᵉapp ↘u ↘v) (Rⁿᵉapp ↘u′ ↘v′)
    rewrite readback-ne-unique ↘u ↘u′ | readback-unique ↘v ↘v′ = refl

  readback-unique : Rⁿᶠ n ⦂ d ↘ v → Rⁿᶠ n ⦂ d ↘ v′ → v ≡ v′
  readback-unique Rⁿᶠone Rⁿᶠone = refl
  readback-unique (Rⁿᶠfun ↘b ↘v) (Rⁿᶠfun ↘b′ ↘v′)
    rewrite app-unique ↘b ↘b′ | readback-unique ↘v ↘v′ = refl
  readback-unique (Rⁿᶠ↓↑ ↘u) (Rⁿᶠ↓↑ ↘u′)
    rewrite readback-ne-unique ↘u ↘u′ = refl

semtype-trans : a == a′ ∈ ⟦ T ⟧ → a′ == a″ ∈ ⟦ T ⟧ → a == a″ ∈ ⟦ T ⟧
semtype-trans {one} {one} {𝟙} {one} _ _ = tt
semtype-trans {↑[ 𝟙 ] e} {↑[ 𝟙 ] e′} {𝟙} {↑[ 𝟙 ] e″} e==e′ e′==e″ n
  with e==e′ n
... | _ , e↘ , e′↘
  with e′==e″ n
... | u , e′↘₀ , e″↘
  rewrite readback-ne-unique e′↘ e′↘₀ =
  u , e↘ , e″↘
semtype-trans {f} {f′} {S ⇒ T} {f″} f==f′ f′==f″ {a} {a′} a==a′
  with f==f′ a==a′
...  | b , _ , ↘b , ↘b′ , b==b′
  with f′==f″ (semtype-trans {a′} {a} {S} {a′} (semtype-sym {a} {a′} {S} a==a′) a==a′)
...  | b′ , b″ , ↘b′₀ , ↘b″ , b′==b″
  rewrite app-unique ↘b′ ↘b′₀ =
  b , b″ , ↘b , ↘b″ ,
  semtype-trans {b} {b′} {T} {b″} b==b′ b′==b″

split-semtype : a == a′ ∈ ⟦ T ⟧ → a == a ∈ ⟦ T ⟧ × a′ == a′ ∈ ⟦ T ⟧
split-semtype {a} {a′} {T} a==a′ =
  semtype-trans {a} {a′} {T} {a} a==a′ a′==a ,
  semtype-trans {a′} {a} {T} {a′} a′==a a==a′
  where
    a′==a = semtype-sym {a} {a′} {T} a==a′

SemCtx = Env × Env → Set

⦅_⦆ : Ctx → SemCtx
⦅ ε ⦆ (ε , ε) = Unit
⦅ Γ • T ⦆ (γ • a , γ′ • a′) =
  γ == γ′ ∈ ⦅ Γ ⦆ × a == a′ ∈ ⟦ T ⟧
⦅ _ ⦆ _ = Empty

_??_ : γ == γ′ ∈ ⦅ Γ ⦆ → x ∷ T ∈ Γ
      → ∃[ a ] ∃[ a′ ] x ↦ a ∈ γ × x ↦ a′ ∈ γ′ × a == a′ ∈ ⟦ T ⟧
_??_ {_ • a} {_ • a′} (_ , a==a′) here = a , a′ , here , here , a==a′
_??_ {_ • _} {_ • _} (γ==γ′ , _) (there x∷T∈Γ) =
  let (a , a′ , x↦a∈γ , x↦a′∈γ′ , a==a′) = γ==γ′ ?? x∷T∈Γ in
  a , a′ , there x↦a∈γ , there x↦a′∈γ′ , a==a′

semctx-sym : γ == γ′ ∈ ⦅ Γ ⦆ → γ′ == γ ∈ ⦅ Γ ⦆
semctx-sym {ε} {ε} {ε} tt = tt
semctx-sym {γ • a} {γ′ • a′} {Γ • S} (γ==γ′ , a==a′) =
  semctx-sym γ==γ′ , semtype-sym {a} {a′} {S} a==a′

semctx-trans : γ == γ′ ∈ ⦅ Γ ⦆ → γ′ == γ″ ∈ ⦅ Γ ⦆ → γ == γ″ ∈ ⦅ Γ ⦆
semctx-trans {ε} {ε} {ε} {ε} tt tt = tt
semctx-trans {γ • a} {γ′ • a′} {Γ • S} {γ″ • a″} (γ==γ′ , a==a′) (γ′==γ″ , a′==a″) =
  semctx-trans γ==γ′ γ′==γ″ , semtype-trans {a} {a′} {S} {a″} a==a′ a′==a″

split-semctx : γ == γ′ ∈ ⦅ Γ ⦆ → γ == γ ∈ ⦅ Γ ⦆ × γ′ == γ′ ∈ ⦅ Γ ⦆
split-semctx γ==γ′ = semctx-trans γ==γ′ γ′==γ , semctx-trans γ′==γ γ==γ′
  where
    γ′==γ = semctx-sym γ==γ′

_⊨_==_∷_ : Ctx → Exp → Exp → Type → Set
Γ ⊨ t == t′ ∷ T =
  ∀ {γ γ′}
  → γ == γ′ ∈ ⦅ Γ ⦆
  → ∃[ a ] ∃[ a′ ]
      ⟦ t ⟧ γ ↘ a
    × ⟦ t′ ⟧ γ′ ↘ a′
    × a == a′ ∈ ⟦ T ⟧

_⊨_==_⦂_ : Ctx → Subst → Subst → Ctx → Set
Γ ⊨ σ == σ′ ⦂ Δ =
  ∀ {γ γ′}
  → γ == γ′ ∈ ⦅ Γ ⦆
  → ∃[ δ ] ∃[ δ′ ]
      ⦅ σ ⦆ γ ↘ δ
    × ⦅ σ′ ⦆ γ′ ↘ δ′
    × δ == δ′ ∈ ⦅ Δ ⦆

mutual
  fundamental-lemma-sub : Γ ⊢ σ ⦂ Δ → Γ ⊨ σ == σ ⦂ Δ
  fundamental-lemma-sub ⊢up {γ • _} {γ′ • _} (γ==γ′ , _) =
    γ , γ′ , ⦅up⦆ , ⦅up⦆ , γ==γ′
  fundamental-lemma-sub ⊢id {γ} {γ′} γ==γ′ = γ , γ′ , ⦅id⦆ , ⦅id⦆ , γ==γ′
  fundamental-lemma-sub (⊢comp ⊢σ ⊢τ) γ==γ′
    with fundamental-lemma-sub ⊢σ γ==γ′
  ... | δ , δ′ , ↘δ , ↘δ′ , δ==δ′
    with fundamental-lemma-sub ⊢τ δ==δ′
  ... | ψ , ψ′ , ↘ψ , ↘ψ′ , ψ==ψ′ =
    ψ , ψ′ , ⦅comp⦆ ↘δ ↘ψ , ⦅comp⦆ ↘δ′ ↘ψ′ , ψ==ψ′
  fundamental-lemma-sub (⊢ext ⊢σ ⊢s) γ==γ′
    with fundamental-lemma-sub ⊢σ γ==γ′
  ... | δ , δ′ , ↘δ , ↘δ′ , δ==δ′
    with fundamental-lemma ⊢s γ==γ′
  ... | a , a′ , ↘a , ↘a′ , a==a′ =
    δ • a , δ′ • a′ , ⦅ext⦆ ↘δ ↘a , ⦅ext⦆ ↘δ′ ↘a′ , δ==δ′ , a==a′

  fundamental-lemma : Γ ⊢ t ∷ T → Γ ⊨ t == t ∷ T
  fundamental-lemma ⊢one γ==γ′ =
    one , one , ⟦one⟧ , ⟦one⟧ , tt
  fundamental-lemma (⊢var x∷T∈Γ) γ==γ′ =
    let (a , a′ , x↦a∈γ , x↦a′∈γ′ , a==a′) = γ==γ′ ?? x∷T∈Γ in
    a , a′ , ⟦var⟧ x↦a∈γ , ⟦var⟧ x↦a′∈γ′ , a==a′
  fundamental-lemma (⊢abs {t = t} ⊢t) {γ} {γ′} γ==γ′ =
    ⟨ƛ t ⟩ γ , ⟨ƛ t ⟩ γ′ , ⟦abs⟧ , ⟦abs⟧ ,
    λ a==a′ →
      let (b , b′ , ↘b , ↘b′ , b==b′) = fundamental-lemma
                                          ⊢t (γ==γ′ , a==a′)
      in
      b , b′ , clos· ↘b , clos· ↘b′ , b==b′
  fundamental-lemma (⊢app ⊢r ⊢s) γ==γ′
    with fundamental-lemma ⊢r γ==γ′
  ... | f , f′ , ↘f , ↘f′ , f==f′
    with fundamental-lemma ⊢s γ==γ′
  ... | a , a′ , ↘a , ↘a′ , a==a′
    with f==f′ a==a′
  ... | b , b′ , ↘b , ↘b′ , b==b′ =
    b , b′ , ⟦app⟧ ↘f ↘a ↘b , ⟦app⟧ ↘f′ ↘a′ ↘b′ , b==b′
  fundamental-lemma (⊢sub ⊢σ ⊢t) γ==γ′
    with fundamental-lemma-sub ⊢σ γ==γ′
  ... | δ , δ′ , ↘δ , ↘δ′ , δ==δ′
    with fundamental-lemma ⊢t δ==δ′
  ... | a , a′ , ↘a , ↘a′ , a==a′ =
    a , a′ , ⟦sub⟧ ↘δ ↘a , ⟦sub⟧ ↘δ′ ↘a′ , a==a′

mutual
  fundamental-lemma-sub₂ : Γ ⊢ σ == σ′ ⦂ Δ → Γ ⊨ σ == σ′ ⦂ Δ
  fundamental-lemma-sub₂ (up-ext ⊢σ ⊢s) γ==γ′
    with fundamental-lemma-sub ⊢σ γ==γ′
  ... | δ , δ′ , ↘δ , ↘δ′ , δ==δ′
    with fundamental-lemma ⊢s γ==γ′
  ... | _ , _ , ↘a , _ , _ =
    δ , δ′ , ⦅comp⦆ (⦅ext⦆ ↘δ ↘a) ⦅up⦆ , ↘δ′ , δ==δ′
  fundamental-lemma-sub₂ (comp-identityˡ ⊢σ) γ==γ′
    with fundamental-lemma-sub ⊢σ γ==γ′
  ... | δ , δ′ , ↘δ , ↘δ′ , δ==δ′ =
    δ , δ′ , ⦅comp⦆ ↘δ ⦅id⦆ , ↘δ′ , δ==δ′
  fundamental-lemma-sub₂ (comp-identityʳ ⊢σ) γ==γ′
    with fundamental-lemma-sub ⊢σ γ==γ′
  ... | δ , δ′ , ↘δ , ↘δ′ , δ==δ′ =
    δ , δ′ , ⦅comp⦆ ⦅id⦆ ↘δ , ↘δ′ , δ==δ′
  fundamental-lemma-sub₂ (comp-assoc ⊢σ₁ ⊢σ₂ ⊢σ₃) γ==γ′
    with fundamental-lemma-sub ⊢σ₁ γ==γ′
  ... | δ , δ′ , ↘δ , ↘δ′ , δ==δ′
    with fundamental-lemma-sub ⊢σ₂ δ==δ′
  ... | ψ , ψ′ , ↘ψ , ↘ψ′ , ψ==ψ′
    with fundamental-lemma-sub ⊢σ₃ ψ==ψ′
  ... | ω , ω′ , ↘ω , ↘ω′ , ω==ω′ =
    ω , ω′ , ⦅comp⦆ ↘δ (⦅comp⦆ ↘ψ ↘ω) , ⦅comp⦆ (⦅comp⦆ ↘δ′ ↘ψ′) ↘ω′ , ω==ω′
  fundamental-lemma-sub₂ η-id {γ • a} {γ′ • a′} (γ==γ′ , a==a′) =
    γ • a , γ′ • a′ , ⦅id⦆ , ⦅ext⦆ ⦅up⦆ (⟦var⟧ here) , γ==γ′ , a==a′
  fundamental-lemma-sub₂ (up-comp ⊢σ ⊢τ ⊢s) γ==γ′
    with fundamental-lemma-sub ⊢σ γ==γ′
  ... | δ , δ′ , ↘δ , ↘δ′ , δ==δ′
    with fundamental-lemma-sub ⊢τ δ==δ′
  ... | ψ , ψ′ , ↘ψ , ↘ψ′ , ψ==ψ′
    with fundamental-lemma ⊢s δ==δ′
  ... | a , a′ , ↘a , ↘a′ , a==a′ =
    ψ • a , ψ′ • a′ , ⦅comp⦆ ↘δ (⦅ext⦆ ↘ψ ↘a) ,
      ⦅ext⦆ (⦅comp⦆ ↘δ′ ↘ψ′) (⟦sub⟧ ↘δ′ ↘a′) , ψ==ψ′ , a==a′
  fundamental-lemma-sub₂ (ext-compatible σ==σ′ s==s′) γ==γ′
    with fundamental-lemma-sub₂ σ==σ′ γ==γ′
  ... | δ , δ′ , ↘δ , ↘δ′ , δ==δ′
    with fundamental-lemma² s==s′ γ==γ′
  ... | a , a′ , ↘a , ↘a′ , a==a′ =
    δ • a , δ′ • a′ , ⦅ext⦆ ↘δ ↘a , ⦅ext⦆ ↘δ′ ↘a′ , δ==δ′ , a==a′
  fundamental-lemma-sub₂ (comp-compatible σ==σ′ τ==τ′) γ==γ′
    with fundamental-lemma-sub₂ σ==σ′ γ==γ′
  ... | δ , δ′ , ↘δ , ↘δ′ , δ==δ′
    with fundamental-lemma-sub₂ τ==τ′ δ==δ′
  ... | ψ , ψ′ , ↘ψ , ↘ψ′ , ψ==ψ′ =
    ψ , ψ′ , ⦅comp⦆ ↘δ ↘ψ , ⦅comp⦆ ↘δ′ ↘ψ′ , ψ==ψ′
  fundamental-lemma-sub₂ (refl ⊢σ) γ==γ′ =
    fundamental-lemma-sub ⊢σ γ==γ′
  fundamental-lemma-sub₂ (sym σ′==σ) γ==γ′
    with fundamental-lemma-sub₂ σ′==σ (semctx-sym γ==γ′)
  ... | δ′ , δ , ↘δ′ , ↘δ , δ′==δ =
    δ , δ′ , ↘δ , ↘δ′ , semctx-sym δ′==δ
  fundamental-lemma-sub₂ (trans σ==σ′ σ′==σ″) γ==γ′
    with fundamental-lemma-sub₂ σ==σ′ γ==γ′
  ... | δ , _ , ↘δ , ↘δ′ , δ==δ′
    with split-semctx γ==γ′
  ... | _ , γ′==γ′
    with fundamental-lemma-sub₂ σ′==σ″ γ′==γ′
  ... | δ′ , δ″ , ↘δ′₀ , ↘δ″ , δ′==δ″
    rewrite eval-sub-unique ↘δ′ ↘δ′₀ =
    δ , δ″ , ↘δ , ↘δ″ , semctx-trans δ==δ′ δ′==δ″

  fundamental-lemma² : Γ ⊢ t == t′ ∷ T → Γ ⊨ t == t′ ∷ T
  fundamental-lemma² (β {S = S} ⊢t ⊢s) γ==γ′
    with fundamental-lemma ⊢s γ==γ′
  ... | a , a′ , ↘a , ↘a′ , a==a′
    with fundamental-lemma ⊢t (γ==γ′ , a==a′)
  ... | b , b′ , ↘b , ↘b′ , b==b′ =
    b , b′ , ⟦app⟧ ⟦abs⟧ ↘a (clos· ↘b) , ⟦sub⟧ (⦅ext⦆ ⦅id⦆ ↘a′) ↘b′ , b==b′
  fundamental-lemma² (η {t = t} ⊢t) {_} {γ′} γ==γ′
    with fundamental-lemma ⊢t γ==γ′
  ... | f , f′ , ↘f , ↘f′ , f==f′ =
    f , ⟨ƛ t [ ↑ ] · var zero ⟩ γ′ , ↘f , ⟦abs⟧ ,
      λ a==a′ →
    let (b , b′ , ↘b , ↘b′ , b==b′) = f==f′ a==a′ in
    b , b′ , ↘b , clos· (⟦app⟧ (⟦sub⟧ ⦅up⦆ ↘f′) (⟦var⟧ here) ↘b′) , b==b′
  fundamental-lemma² (var-↑ x∷T∈Γ) γ==γ′
    with γ==γ′ ?? there x∷T∈Γ
  ... | a , a′ , there x↦a∈γ , x↦a′∈γ′ , a==a′ =
    a , a′ , ⟦sub⟧ ⦅up⦆ (⟦var⟧ x↦a∈γ) , ⟦var⟧ x↦a′∈γ′ , a==a′
  fundamental-lemma² ([id] ⊢t) γ==γ′
    with fundamental-lemma ⊢t γ==γ′
  ... | a , a′ , ↘a , ↘a′ , a==a′ =
    a , a′ , ⟦sub⟧ ⦅id⦆ ↘a , ↘a′ , a==a′
  fundamental-lemma² (zero-• ⊢σ ⊢s) γ==γ′
    with fundamental-lemma-sub ⊢σ γ==γ′
  ... | δ , δ′ , ↘δ , ↘δ′ , δ==δ′
    with fundamental-lemma ⊢s γ==γ′
  ... | a , a′ , ↘a , ↘a′ , a==a′ =
    a , a′ , ⟦sub⟧ (⦅ext⦆ ↘δ ↘a) (⟦var⟧ here) , ↘a′ , a==a′
  fundamental-lemma² (suc-• ⊢σ ⊢s x∷T∈Δ) γ==γ′
    with fundamental-lemma-sub ⊢σ γ==γ′
  ... | δ , δ′ , ↘δ , ↘δ′ , δ==δ′
    with fundamental-lemma ⊢s γ==γ′
  ... | a , a′ , ↘a , ↘a′ , a==a
    with δ==δ′ ?? x∷T∈Δ
  ... | b , b′ , ↘b , ↘b′ , b==b′ =
    b , b′ , ⟦sub⟧ (⦅ext⦆ ↘δ ↘a) (⟦var⟧ (there ↘b)) ,
      ⟦sub⟧ ↘δ′ (⟦var⟧ ↘b′) , b==b′
  fundamental-lemma² (one-sub ⊢σ) γ==γ′
    with fundamental-lemma-sub ⊢σ γ==γ′
  ... | δ , δ′ , ↘δ , ↘δ′ , δ==δ′ =
    one , one , ⟦sub⟧ ↘δ ⟦one⟧ , ⟦one⟧ , tt
  fundamental-lemma² (abs-sub {σ = σ} {t = t} ⊢σ ⊢t) {_} {γ′} γ==γ′
    with fundamental-lemma-sub ⊢σ γ==γ′
  ... | δ , δ′ , ↘δ , ↘δ′ , δ==δ′ =
    ⟨ƛ t ⟩ δ , ⟨ƛ t [ (σ ∘ ↑) • var zero ] ⟩ γ′ , ⟦sub⟧ ↘δ ⟦abs⟧ , ⟦abs⟧ ,
      λ a==a′ →
    let (b , b′ , ↘b , ↘b′ , b==b′) = fundamental-lemma ⊢t (δ==δ′ , a==a′) in
    b , b′ , clos· ↘b ,
      clos· (⟦sub⟧ (⦅ext⦆ (⦅comp⦆ ⦅up⦆ ↘δ′) (⟦var⟧ here)) ↘b′) , b==b′
  fundamental-lemma² (app-sub ⊢σ ⊢r ⊢s) γ==γ′
    with fundamental-lemma-sub ⊢σ γ==γ′
  ... | δ , δ′ , ↘δ , ↘δ′ , δ==δ′
    with fundamental-lemma ⊢r δ==δ′
  ... | f , f′ , ↘f , ↘f′ , f==f′
    with fundamental-lemma ⊢s δ==δ′
  ... | a , a′ , ↘a , ↘a′ , a==a′
    with f==f′ a==a′
  ... | b , b′ , ↘b , ↘b′ , b==b′ =
    b , b′ , ⟦sub⟧ ↘δ (⟦app⟧ ↘f ↘a ↘b) ,
      ⟦app⟧ (⟦sub⟧ ↘δ′ ↘f′) (⟦sub⟧ ↘δ′ ↘a′) ↘b′ , b==b′
  fundamental-lemma² (sub-comp ⊢τ ⊢σ ⊢t) γ==γ′
    with fundamental-lemma-sub ⊢τ γ==γ′
  ... | δ , δ′ , ↘δ , ↘δ′ , δ==δ′
    with fundamental-lemma-sub ⊢σ δ==δ′
  ... | ψ , ψ′ , ↘ψ , ↘ψ′ , ψ==ψ′
    with fundamental-lemma ⊢t ψ==ψ′
  ... | a , a′ , ↘a , ↘a′ , a==a′ =
    a , a′ , ⟦sub⟧ ↘δ (⟦sub⟧ ↘ψ ↘a) , ⟦sub⟧ (⦅comp⦆ ↘δ′ ↘ψ′) ↘a′ , a==a′
  fundamental-lemma² (app-compatible r==r′ s==s′) γ==γ′
    with fundamental-lemma² r==r′ γ==γ′
  ... | f , f′ , ↘f , ↘f′ , f==f′
    with fundamental-lemma² s==s′ γ==γ′
  ... | a , a′ , ↘a , ↘a′ , a==a′
    with f==f′ a==a′
  ... | b , b′ , ↘b , ↘b′ , b==b′ =
    b , b′ , ⟦app⟧ ↘f ↘a ↘b , ⟦app⟧ ↘f′ ↘a′ ↘b′ , b==b′
  fundamental-lemma² (ξ {t = t} {t′ = t′} t==t′) {γ} {γ′} γ==γ′ =
    ⟨ƛ t ⟩ γ , ⟨ƛ t′ ⟩ γ′ , ⟦abs⟧ , ⟦abs⟧ ,
      λ a==a′ → let (b , b′ , ↘b , ↘b′ , b==b′) = fundamental-lemma²
                                                    t==t′ (γ==γ′ , a==a′)
      in b , b′ , clos· ↘b , clos· ↘b′ , b==b′
  fundamental-lemma² (refl ⊢t) γ==γ′ =
    fundamental-lemma ⊢t γ==γ′
  fundamental-lemma² {T = T} (sym t′==t) γ==γ′
    with fundamental-lemma² t′==t (semctx-sym γ==γ′)
  ... | a′ , a , ↘a′ , ↘a , a′==a =
    a , a′ , ↘a , ↘a′ , semtype-sym {a′} {a} {T} a′==a
  fundamental-lemma² {T = T} (trans t==t′ t′==t″) γ==γ′
    with fundamental-lemma² t==t′ γ==γ′
  ... | a , _ , ↘a , ↘a′ , a==a′
    with split-semctx γ==γ′
  ... | _ , γ′==γ′
    with fundamental-lemma² t′==t″ γ′==γ′
  ... | a′ , a″ , ↘a′₀ , ↘a″ , a′==a″
    rewrite eval-unique ↘a′ ↘a′₀ =
    a , a″ , ↘a , ↘a″ , semtype-trans {a} {a′} {T} {a″} a==a′ a′==a″

lvl_∈⊥ : ∀ k → lvl k == lvl k ∈ ⊥
lvl k ∈⊥ n = var (n - suc k) , Rⁿᵉvar , Rⁿᵉvar

⊥·⊤∈⊥ : e == e′ ∈ ⊥ → d == d′ ∈ ⊤ → e · d == e′ · d′ ∈ ⊥
⊥·⊤∈⊥ e==e′ d==d′ n =
  let (u , e↘ , e′↘) = e==e′ n in
  let (v , d↘ , d′↘) = d==d′ n in
  u · v , Rⁿᵉapp e↘ d↘ , Rⁿᵉapp e′↘ d′↘

↓↑⊥∈⊤ : e == e′ ∈ ⊥ → ↓[ 𝟙 ] ↑[ 𝟙 ] e == ↓[ 𝟙 ] ↑[ 𝟙 ] e′ ∈ ⊤
↓↑⊥∈⊤ e==e′ n =
  let (u , e↘ , e′↘) = e==e′ n in
  ` u , Rⁿᶠ↓↑ e↘ , Rⁿᶠ↓↑ e′↘


⊤[_] : Type → SemType
⊤[ T ] (a , a′) = ↓[ T ] a == ↓[ T ] a′ ∈ ⊤

⊥[_] : Type → SemType
⊥[ T ] (↑[ T′ ] e , ↑[ T″ ] e′) = T ≡ T′ × T ≡ T″ × e == e′ ∈ ⊥
⊥[ _ ] _ = Empty

⊥[_]⟶⊤[_]⊆⊤ : ∀ S T
               → f == f′ ∈ ⊥[ S ] ⟶ ⊤[ T ]
               → f == f′ ∈ ⊤[ S ⇒ T ]
⊥[ S ]⟶⊤[ T ]⊆⊤ f==f′ n
  with f==f′ (refl  , refl , lvl n ∈⊥)
... | b , b′ , ↘b , ↘b′ , b==b′
  with b==b′ (suc n)
... | v , b↘ , b′↘ =
  ƛ v , Rⁿᶠfun ↘b b↘ , Rⁿᶠfun ↘b′ b′↘

⊥[_⇒_]⊆⊤⟶⊥ : ∀ S T
              → f == f′ ∈ ⊥[ S ⇒ T ]
              → f == f′ ∈ ⊤[ S ] ⟶ ⊥[ T ]
⊥[_⇒_]⊆⊤⟶⊥ {↑[ _ ] e} {↑[ _ ] e′} S T (refl , refl , e==e′) {a} {a′} a==a′ =
  ↑[ T ] (e · ↓[ S ] a) , ↑[ T ] (e′ · ↓[ S ] a′) , ↑fun· , ↑fun· , refl ,
    refl , ⊥·⊤∈⊥ e==e′ a==a′

mutual
  ⊤⟶⊥⊆⟦_⇒_⟧ : ∀ S T → f == f′ ∈ ⊤[ S ] ⟶ ⊥[ T ] → f == f′ ∈ ⟦ S ⇒ T ⟧
  ⊤⟶⊥⊆⟦ S ⇒ T ⟧ f==f′ a==a′
    with ⟦ S ⟧⊆⊤ a==a′
  ... | a==a′
    with f==f′ a==a′
  ... | ↑[ T ] e , ↑[ _ ] e′ , ↘e , ↘e′ , refl , refl , e==e′ =
    ↑[ T ] e , ↑[ T ] e′ , ↘e , ↘e′ , ⊥⊆⟦ T ⟧ (refl , refl , e==e′)

  ⟦_⇒_⟧⊆⊥⟶⊤ : ∀ S T → f == f′ ∈ ⟦ S ⇒ T ⟧ → f == f′ ∈ ⊥[ S ] ⟶ ⊤[ T ]
  ⟦ S ⇒ T ⟧⊆⊥⟶⊤ f==f′ a==a′
    with f==f′ (⊥⊆⟦ S ⟧ a==a′)
  ... | d , d′ , ↘d , ↘d′ , d==d′ =
    d , d′ , ↘d , ↘d′ , ⟦ T ⟧⊆⊤ d==d′

  ⊥⊆⟦_⟧ : ∀ S → a == a′ ∈ ⊥[ S ] → a == a′ ∈ ⟦ S ⟧
  ⊥⊆⟦_⟧ {↑[ _ ] _} {↑[ _ ] _} 𝟙 (refl , refl , e==e′) = e==e′
  ⊥⊆⟦ S ⇒ T ⟧ f==f′ = ⊤⟶⊥⊆⟦ S ⇒ T ⟧ (⊥[ S ⇒ T ]⊆⊤⟶⊥ f==f′)

  ⟦_⟧⊆⊤ : ∀ S → a == a′ ∈ ⟦ S ⟧ → a == a′ ∈ ⊤[ S ]
  ⟦_⟧⊆⊤ {↑[ 𝟙 ] _} {↑[ 𝟙 ] _} 𝟙 e==e′ n
    with e==e′ n
  ... | var _ , Rⁿᵉvar , lvl↘ =
    ` var (n - suc _) , Rⁿᶠ↓↑ Rⁿᵉvar , Rⁿᶠ↓↑ lvl↘
  ... | u · v , Rⁿᵉapp e↘ d↘ , Rⁿᵉapp e′↘ d′↘ =
    ` (u · v) , Rⁿᶠ↓↑ (Rⁿᵉapp e↘ d↘) , Rⁿᶠ↓↑ (Rⁿᵉapp e′↘ d′↘)
  ⟦_⟧⊆⊤ {one} {one} 𝟙 tt _ = one , Rⁿᶠone , Rⁿᶠone
  ⟦ S ⇒ T ⟧⊆⊤ f==f′ = ⊥[ S ]⟶⊤[ T ]⊆⊤ (⟦ S ⇒ T ⟧⊆⊥⟶⊤ f==f′)

env==env∈⦅_⦆ : ∀ Γ → env Γ == env Γ ∈ ⦅ Γ ⦆
env==env∈⦅ ε ⦆ = tt
env==env∈⦅ Γ • S ⦆ =
  env==env∈⦅ Γ ⦆ ,
  ⊥⊆⟦ S ⟧ (refl , refl , (λ n → var (n - suc ∣ Γ ∣) , Rⁿᵉvar , Rⁿᵉvar))

complete : Γ ⊢ t == t′ ∷ T
         → (nf-t : nf T Γ t)
         → (nf-t′ : nf T Γ t′)
         → ~ nf-t ≡ ~ nf-t′
complete {Γ} {T = T} t==t′ (_ , _ , ↘a₀ , a↘₀) (_ , _ , ↘a′₀ , a′↘₀)
  with fundamental-lemma² t==t′ env==env∈⦅ Γ ⦆
... | a , a′ , ↘a , ↘a′ , a==a′
  with ⟦ T ⟧⊆⊤ a==a′ ∣ Γ ∣
... | v , a↘ , a′↘
  rewrite eval-unique ↘a ↘a₀ | readback-unique a↘ a↘₀
        | eval-unique ↘a′ ↘a′₀ | readback-unique a′↘ a′↘₀ =
  refl
