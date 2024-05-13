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
infixr 7 _⇒_ _⟶²_
infix 4 _∷_∈_ _⊢_∷_ _⊢_⦂_ _⊢_==_∷_ _⊢_==_⦂_
infix 4 _↦_∈_ _·_↘_ ⟦_⟧_↘_ ⦅_⦆_↘_ Rⁿᶠ_⦂_↘_ Rⁿᵉ_⦂_↘_
infix 4 _⊨_⦂_ _⊨_∷_
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
             → Γ ⊢ t [ σ ] [ τ ] == t [ σ ∘ τ ] ∷ T

    app-compatible : Γ ⊢ r == r′ ∷ S ⇒ T
                   → Γ ⊢ s == s′ ∷ S
                   → Γ ⊢ r · s == r′ · s′ ∷ T

    ξ : Γ • S ⊢ t == t′ ∷ T
      → Γ ⊢ ƛ t == ƛ t′ ∷ T

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

    comp-compatible : Γ₁ ⊢ σ == σ′ ⦂ Γ₂
                    → Γ₂ ⊢ τ == τ′ ⦂ Γ₃
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

  -- evaluation fo substitutions to environments
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
nf T Γ t =
  ∃[ a ] ∃[ v ]
    ⟦ t ⟧ (env Γ) ↘ a
  × Rⁿᶠ ∣ Γ ∣ ⦂ ↓[ T ] a ↘ v

SemType = D → Set

variable 𝒜 ℬ : SemType

_⟶_ : SemType → SemType → SemType
(𝒜 ⟶ ℬ) f = ∀ {a} → a ∈ 𝒜 → ∃[ b ] f · a ↘ b × b ∈ ℬ

⊥ : Dⁿᵉ → Set
⊥ e = ∀ n → ∃[ u ] Rⁿᵉ n ⦂ e ↘ u

⊤ : Dⁿᶠ → Set
⊤ d = ∀ n → ∃[ v ] Rⁿᶠ n ⦂ d ↘ v

lvl_∈⊥ : ∀ k → lvl k ∈ ⊥
(lvl k ∈⊥) n = var (n - suc k) , Rⁿᵉvar

⊥·⊤∈⊥ : e ∈ ⊥ → d ∈ ⊤ → e · d ∈ ⊥
⊥·⊤∈⊥ e∈⊥ d∈⊤ n =
  let (u , ↘u) = e∈⊥ n in
  let (v , ↘v) = d∈⊤ n in
  u · v , Rⁿᵉapp ↘u ↘v

⟦𝟙⟧ : SemType
⟦𝟙⟧ (↑[ 𝟙 ] e) = e ∈ ⊥
⟦𝟙⟧ one = Unit
⟦𝟙⟧ _ = Empty

⟦_⟧ : Type → SemType
⟦ 𝟙 ⟧ = ⟦𝟙⟧
⟦ S ⇒ T ⟧ = ⟦ S ⟧ ⟶ ⟦ T ⟧

SemCtx = Env → Set

⦅_⦆ : Ctx → SemCtx
⦅ ε ⦆ ε = Unit
⦅ Γ • S ⦆ (γ • a)  = γ ∈ ⦅ Γ ⦆ × a ∈ ⟦ S ⟧
⦅ _ ⦆ _ = Empty

-- Typed candidate spaces
⊤[_] : Type → SemType
⊤[ T ] a = ↓[ T ] a ∈ ⊤

⊥[_] : Type → SemType
⊥[ T ] (↑[ T′ ] e) = T ≡ T′ × e ∈ ⊥
⊥[ _ ] _ = Empty

⊥[_⇒_]⊆⊤⟶⊥ : ∀ S T
           → a ∈ ⊥[ S ⇒ T ]
           → a ∈ ⊤[ S ] ⟶ ⊥[ T ]
⊥[_⇒_]⊆⊤⟶⊥ {↑[ _ ] e} S T (refl , e∈⊥) {d} d∈⊤ =
  ↑[ T ] (e · ↓[ S ] d) , ↑fun· , refl , ⊥·⊤∈⊥ e∈⊥ d∈⊤

⊥[_]⟶⊤[_]⊆⊤ : ∀ S T
             → f ∈ ⊥[ S ] ⟶ ⊤[ T ]
             → f ∈ ⊤[ S ⇒ T ]
⊥[ S ]⟶⊤[ T ]⊆⊤ f∈⊥⟶⊤ n
  with f∈⊥⟶⊤ (refl , lvl n ∈⊥)
... | b , ↘b , b∈⊤
  with b∈⊤ (suc n)
... | v , ↘v = ƛ v , Rⁿᶠfun ↘b ↘v

mutual
  ⊤⟶⊥⊆⟦_⇒_⟧ : ∀ S T → f ∈ ⊤[ S ] ⟶ ⊥[ T ] → f ∈ ⟦ S ⇒ T ⟧
  ⊤⟶⊥⊆⟦ S ⇒ T ⟧ f∈⊤⟶⊥ {a} a∈⟦S⟧
    with ⟦ S ⟧⊆⊤ a∈⟦S⟧
  ... | a∈⊤
    with f∈⊤⟶⊥ a∈⊤
  ... | ↑[ T ] e , ↘e , refl , e∈⊥ =
    ↑[ T ] e , ↘e , ⊥⊆⟦ T ⟧ (refl , e∈⊥)

  ⊥⊆⟦_⟧ : ∀ T → a ∈ ⊥[ T ] → a ∈ ⟦ T ⟧
  ⊥⊆⟦_⟧ {↑[ 𝟙 ] e} 𝟙 (_ , e∈⊥) = e∈⊥
  ⊥⊆⟦ S ⇒ T ⟧ a∈⊥ =
    ⊤⟶⊥⊆⟦ S ⇒ T ⟧ (⊥[ S ⇒ T ]⊆⊤⟶⊥ a∈⊥)

  ⟦_⇒_⟧⊆⊥⟶⊤ : ∀ S T
            → f ∈ ⟦ S ⇒ T ⟧
            → f ∈ ⊥[ S ] ⟶ ⊤[ T ]
  ⟦ S ⇒ T ⟧⊆⊥⟶⊤ f∈⟦S⇒T⟧ a∈⊥
    with f∈⟦S⇒T⟧ (⊥⊆⟦ S ⟧ a∈⊥)
  ... | d , ↘f , d∈⟦T⟧ =
    d , ↘f , ⟦ T ⟧⊆⊤ d∈⟦T⟧

  ⟦_⟧⊆⊤ : ∀ T → a ∈ ⟦ T ⟧ → a ∈ ⊤[ T ]
  ⟦_⟧⊆⊤ {↑[ 𝟙 ] e} 𝟙 e∈⟦𝟙⟧ n
    with e∈⟦𝟙⟧ n
  ... | _ , Rⁿᵉvar {k = k} =
    ` var (n - suc k) , Rⁿᶠ↓↑ Rⁿᵉvar
  ... | u · v , Rⁿᵉapp e↘ d↘ =
    ` (u · v) , Rⁿᶠ↓↑ (Rⁿᵉapp e↘ d↘)
  ⟦_⟧⊆⊤ {one} 𝟙 _ _ = one , Rⁿᶠone
  ⟦ S ⇒ T ⟧⊆⊤ f∈⟦S⇒T⟧ =
    ⊥[ S ]⟶⊤[ T ]⊆⊤ (⟦ S ⇒ T ⟧⊆⊥⟶⊤ f∈⟦S⇒T⟧)

_⊨_⦂_ : Ctx → Subst → Ctx → Set
Γ ⊨ σ ⦂ Δ =
  ∀ {γ} → γ ∈ ⦅ Γ ⦆ → ∃[ δ ] ⦅ σ ⦆ γ ↘ δ × δ ∈ ⦅ Δ ⦆

_⊨_∷_ : Ctx → Exp → Type → Set
Γ ⊨ t ∷ T =
  ∀ {γ} → γ ∈ ⦅ Γ ⦆ → ∃[ a ] ⟦ t ⟧ γ ↘ a × a ∈ ⟦ T ⟧

_??_ : γ ∈ ⦅ Γ ⦆ → x ∷ T ∈ Γ → ∃[ a ] (x ↦ a ∈ γ) × a ∈ ⟦ T ⟧
_??_ {_ • a} (_ , a∈⟦T⟧) here = a , here , a∈⟦T⟧
_??_ {γ • _} (γ∈⟦T⟧ , _) (there x∷T∈Γ) =
  let (a , x↦a∈γ , a∈⟦T⟧) = γ∈⟦T⟧ ?? x∷T∈Γ in
  a , there x↦a∈γ , a∈⟦T⟧

mutual
  fundamental-lemma₁-sub₁ : Γ ⊢ σ ⦂ Δ → Γ ⊨ σ ⦂ Δ
  fundamental-lemma₁-sub₁ ⊢up {γ • _} (γ∈⦅Γ⦆ , _) = γ , ⦅up⦆ , γ∈⦅Γ⦆
  fundamental-lemma₁-sub₁ ⊢id {γ} γ∈⦅Γ⦆ = γ , ⦅id⦆ , γ∈⦅Γ⦆
  fundamental-lemma₁-sub₁ (⊢comp ⊢σ₁ ⊢σ₂) γ∈⦅Γ⦆
    with fundamental-lemma₁-sub₁ ⊢σ₁ γ∈⦅Γ⦆
  ... | δ , ↘δ , δ∈⦅Δ⦆
    with fundamental-lemma₁-sub₁ ⊢σ₂ δ∈⦅Δ⦆
  ... | ψ , ↘ψ , ψ∈⦅Ψ⦆ =
    ψ , ⦅comp⦆ ↘δ ↘ψ , ψ∈⦅Ψ⦆
  fundamental-lemma₁-sub₁ (⊢ext ⊢σ ⊢s) γ∈⦅Γ⦆
    with fundamental-lemma₁-sub₁ ⊢σ γ∈⦅Γ⦆
  ... | δ , ↘δ , δ∈⦅Δ⦆
    with fundamental-lemma₁ ⊢s γ∈⦅Γ⦆
  ... | a , ↘a , a∈⦅S⦆ =
    δ • a , ⦅ext⦆ ↘δ ↘a , δ∈⦅Δ⦆ , a∈⦅S⦆

  fundamental-lemma₁ : Γ ⊢ t ∷ T → Γ ⊨ t ∷ T
  fundamental-lemma₁ ⊢one γ∈⦅Γ⦆ = one , ⟦one⟧ , tt
  fundamental-lemma₁ (⊢var x∷T∈Γ) γ∈⦅Γ⦆ =
    let (a , x↦a∈γ , a∈⟦T⟧) = γ∈⦅Γ⦆ ?? x∷T∈Γ in
    a , ⟦var⟧ x↦a∈γ , a∈⟦T⟧
  fundamental-lemma₁ (⊢abs {t = t} ⊢t) {γ} γ∈⦅Γ⦆ =
    ⟨ƛ t ⟩ γ , ⟦abs⟧ ,
    λ a∈⟦S⟧ →
      let (b , ↘b , b∈⟦T⟧) = fundamental-lemma₁ ⊢t (γ∈⦅Γ⦆ , a∈⟦S⟧) in
      b , clos· ↘b , b∈⟦T⟧
  fundamental-lemma₁ (⊢app ⊢r ⊢s) γ∈⦅Γ⦆
    with fundamental-lemma₁ ⊢r γ∈⦅Γ⦆
  ... | _ , ↘f , f∈⟦S⇒T⟧
    with fundamental-lemma₁ ⊢s γ∈⦅Γ⦆
  ... | _ , ↘a , a∈⟦S⟧
    with f∈⟦S⇒T⟧ a∈⟦S⟧
  ... | b , ↘b , b∈⟦T⟧ =
    b , ⟦app⟧ ↘f ↘a ↘b , b∈⟦T⟧
  fundamental-lemma₁ (⊢sub ⊢σ ⊢t) γ∈⦅Γ⦆
    with fundamental-lemma₁-sub₁ ⊢σ γ∈⦅Γ⦆
  ... | δ , ↘δ , δ∈⦅Δ⦆
    with fundamental-lemma₁ ⊢t δ∈⦅Δ⦆
  ... | b , ↘b , b∈⦅T⦆ =
    b , ⟦sub⟧ ↘δ ↘b , b∈⦅T⦆

SemType² = D × D → Set

variable 𝒜² ℬ² : SemType²

_==_∈_ : ∀ {A : Set} → A → A → (A × A → Set) → Set
a == a′ ∈ 𝒜² = 𝒜² (a , a′)

_⟶²_ : SemType² → SemType² → SemType²
(𝒜² ⟶² ℬ) (f , f′) =
  ∀ {a a′}
  → a == a′ ∈ 𝒜²
  → ∃[ b ] ∃[ b′ ]
      f · a ↘ b
    × f′ · a′ ↘ b′
    × b == b′ ∈ ℬ

⊥² : Dⁿᵉ × Dⁿᵉ → Set
⊥² (e , e′) =
  ∀ n → ∃[ u ] Rⁿᵉ n ⦂ e ↘ u × Rⁿᵉ n ⦂ e′ ↘ u

⊤² : Dⁿᶠ × Dⁿᶠ → Set
⊤² (d , d′) =
  ∀ n → ∃[ v ] Rⁿᶠ n ⦂ d ↘ v × Rⁿᶠ n ⦂ d′ ↘ v

lvl_∈⊥² : ∀ k → lvl k == lvl k ∈ ⊥²
lvl k ∈⊥² n = var (n - suc k) , Rⁿᵉvar , Rⁿᵉvar

⊥²·⊤²∈⊥² : e == e′ ∈ ⊥² → d == d′ ∈ ⊤² → e · d == e′ · d′ ∈ ⊥²
⊥²·⊤²∈⊥² e==e′ d==d′ n =
  let (u , e↘ , e′↘) = e==e′ n in
  let (v , d↘ , d′↘) = d==d′ n in
  u · v , Rⁿᵉapp e↘ d↘ , Rⁿᵉapp e′↘ d′↘

↓↑⊥²∈⊤² : e == e′ ∈ ⊥² → ↓[ 𝟙 ] ↑[ 𝟙 ] e == ↓[ 𝟙 ] ↑[ 𝟙 ] e′ ∈ ⊤²
↓↑⊥²∈⊤² e==e′ n =
  let (u , e↘ , e′↘) = e==e′ n in
  ` u , Rⁿᶠ↓↑ e↘ , Rⁿᶠ↓↑ e′↘

⟦_⟧² : Type → SemType²
⟦ 𝟙 ⟧² (one , one) = Unit
⟦ 𝟙 ⟧² (↑[ 𝟙 ] e , ↑[ 𝟙 ] e′) = e == e′ ∈ ⊥²
⟦ S ⇒ T ⟧² = ⟦ S ⟧² ⟶² ⟦ T ⟧²
⟦ _ ⟧² _ = Empty

⊤²[_] : Type → SemType²
⊤²[ T ] (a , a′) = ↓[ T ] a == ↓[ T ] a′ ∈ ⊤²

⊥²[_] : Type → SemType²
⊥²[ T ] (↑[ T′ ] e , ↑[ T″ ] e′) = T ≡ T′ × T ≡ T″ × e == e′ ∈ ⊥²
⊥²[ _ ] _ = Empty

⊥²[_]⟶⊤²[_]⊆⊤² : ∀ S T
               → f == f′ ∈ ⊥²[ S ] ⟶² ⊤²[ T ]
               → f == f′ ∈ ⊤²[ S ⇒ T ]
⊥²[ S ]⟶⊤²[ T ]⊆⊤² f==f′ n
  with f==f′ (refl  , refl , lvl n ∈⊥²)
... | b , b′ , ↘b , ↘b′ , b==b′
  with b==b′ (suc n)
... | v , b↘ , b′↘ =
  ƛ v , Rⁿᶠfun ↘b b↘ , Rⁿᶠfun ↘b′ b′↘

⊥²[_⇒_]⊆⊤²⟶⊥² : ∀ S T
              → f == f′ ∈ ⊥²[ S ⇒ T ]
              → f == f′ ∈ ⊤²[ S ] ⟶² ⊥²[ T ]
⊥²[_⇒_]⊆⊤²⟶⊥² {↑[ _ ] e} {↑[ _ ] e′} S T (refl , refl , e==e′) {a} {a′} a==a′ =
  ↑[ T ] (e · ↓[ S ] a) , ↑[ T ] (e′ · ↓[ S ] a′) , ↑fun· , ↑fun· , refl ,
    refl , ⊥²·⊤²∈⊥² e==e′ a==a′

semtype²-sym : a == a′ ∈ ⟦ T ⟧² → a′ == a ∈ ⟦ T ⟧²
semtype²-sym {one} {one} {𝟙} _ = tt
semtype²-sym {↑[ 𝟙 ] e} {↑[ 𝟙 ] e′} {𝟙} e==e′ n
  with e==e′ n
... | u , e↘ , e′↘ = u , e′↘ , e↘
semtype²-sym {f} {f′} {S ⇒ T} f==f′ {a} {a′} a==a′
  with f==f′ (semtype²-sym {a} {a′} {S} a==a′)
... | b , b′ , ↘b , ↘b′ , b==b′ =
  b′ , b , ↘b′ , ↘b , semtype²-sym {b} {b′} {T} b==b′

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

semtype²-trans : a == a′ ∈ ⟦ T ⟧² → a′ == a″ ∈ ⟦ T ⟧² → a == a″ ∈ ⟦ T ⟧²
semtype²-trans {one} {one} {𝟙} {one} _ _ = tt
semtype²-trans {↑[ 𝟙 ] e} {↑[ 𝟙 ] e′} {𝟙} {↑[ 𝟙 ] e″} e==e′ e′==e″ n
  with e==e′ n
... | _ , e↘ , e′↘
  with e′==e″ n
... | u , e′↘₀ , e″↘
  rewrite readback-ne-unique e′↘ e′↘₀ =
  u , e↘ , e″↘
semtype²-trans {f} {f′} {S ⇒ T} {f″} f==f′ f′==f″ {a} {a′} a==a′
  with f==f′ a==a′
...  | b , _ , ↘b , ↘b′ , b==b′
  with f′==f″ (semtype²-trans {a′} {a} {S} {a′} (semtype²-sym {a} {a′} {S} a==a′) a==a′)
...  | b′ , b″ , ↘b′₀ , ↘b″ , b′==b″
  rewrite app-unique ↘b′ ↘b′₀ =
  b , b″ , ↘b , ↘b″ ,
  semtype²-trans {b} {b′} {T} {b″} b==b′ b′==b″

split-semtype² : a == a′ ∈ ⟦ T ⟧² → a == a ∈ ⟦ T ⟧² × a′ == a′ ∈ ⟦ T ⟧²
split-semtype² {a} {a′} {T} a==a′ =
  semtype²-trans {a} {a′} {T} {a} a==a′ a′==a ,
  semtype²-trans {a′} {a} {T} {a′} a′==a a==a′
  where
    a′==a = semtype²-sym {a} {a′} {T} a==a′

semtype→semtype² : a ∈ ⟦ T ⟧ → a == a ∈ ⟦ T ⟧²
semtype→semtype² {↑[ x₁ ] x₂} {𝟙} x = {!!}
semtype→semtype² {one} {𝟙} _ = tt
semtype→semtype² {T = S ⇒ T} f∈⟦S⇒T⟧ a==a′ = {!!}

semtype²-refl→semtype : a == a ∈ ⟦ T ⟧² → a ∈ ⟦ T ⟧
semtype²-refl→semtype {↑[ 𝟙 ] e} {𝟙} e==e n
  with e==e n
... | u , ↘u , _ = u , ↘u
semtype²-refl→semtype {one} {𝟙} _ = tt
semtype²-refl→semtype {T = S ⇒ T} f==f x = {!!}

SemCtx² = Env × Env → Set

⦅_⦆² : Ctx → SemCtx²
⦅ ε ⦆² (ε , ε) = Unit
⦅ Γ • T ⦆² (γ • a , γ′ • a′) =
  γ == γ′ ∈ ⦅ Γ ⦆² × a == a′ ∈ ⟦ T ⟧²
⦅ _ ⦆² _ = Empty

semctx²-sym : γ == γ′ ∈ ⦅ Γ ⦆² → γ′ == γ ∈ ⦅ Γ ⦆²
semctx²-sym {ε} {ε} {ε} tt = tt
semctx²-sym {γ • a} {γ′ • a′} {Γ • S} (γ==γ′ , a==a′) =
  semctx²-sym γ==γ′ , semtype²-sym {a} {a′} {S} a==a′

semctx²-trans : γ == γ′ ∈ ⦅ Γ ⦆² → γ′ == γ″ ∈ ⦅ Γ ⦆² → γ == γ″ ∈ ⦅ Γ ⦆²
semctx²-trans {ε} {ε} {ε} {ε} tt tt = tt
semctx²-trans {γ • a} {γ′ • a′} {Γ • S} {γ″ • a″} (γ==γ′ , a==a′) (γ′==γ″ , a′==a″) =
  semctx²-trans γ==γ′ γ′==γ″ , semtype²-trans {a} {a′} {S} {a″} a==a′ a′==a″

split-semctx² : γ == γ′ ∈ ⦅ Γ ⦆² → γ == γ ∈ ⦅ Γ ⦆² × γ′ == γ′ ∈ ⦅ Γ ⦆²
split-semctx² γ==γ′ = semctx²-trans γ==γ′ γ′==γ , semctx²-trans γ′==γ γ==γ′
  where
    γ′==γ = semctx²-sym γ==γ′

_⊨_==_∷_ : Ctx → Exp → Exp → Type → Set
Γ ⊨ t == t′ ∷ T =
  ∀ {γ γ′}
  → γ == γ′ ∈ ⦅ Γ ⦆²
  → ∃[ a ] ∃[ a′ ]
      ⟦ t ⟧ γ ↘ a
    × ⟦ t′ ⟧ γ′ ↘ a′
    × a == a′ ∈ ⟦ T ⟧²

_⊨_==_⦂_ : Ctx → Subst → Subst → Ctx → Set
Γ ⊨ σ == σ′ ⦂ Δ =
  ∀ {γ γ′}
  → γ == γ′ ∈ ⦅ Γ ⦆²
  → ∃[ δ ] ∃[ δ′ ]
      ⦅ σ ⦆ γ ↘ δ
    × ⦅ σ′ ⦆ γ′ ↘ δ′
    × δ == δ′ ∈ ⦅ Δ ⦆²

mutual
  fundamental-lemma-sub₂ : Γ ⊢ σ == σ′ ⦂ Δ → Γ ⊨ σ == σ′ ⦂ Δ
  fundamental-lemma-sub₂ = {!!}

  fundamental-lemma₂ : Γ ⊢ t == t′ ∷ T → Γ ⊨ t == t′ ∷ T
  fundamental-lemma₂ (β ⊢t ⊢σ) γ==γ′ = {!!}
  fundamental-lemma₂ (η x) γ==γ′ = {!!}
  fundamental-lemma₂ (var-↑ x) γ==γ′ = {!!}
  fundamental-lemma₂ ([id] x) γ==γ′ = {!!}
  fundamental-lemma₂ (zero-• x x₁) γ==γ′ = {!!}
  fundamental-lemma₂ (suc-• x x₁ x₂) γ==γ′ = {!!}
  fundamental-lemma₂ (one-sub x) γ==γ′ = {!!}
  fundamental-lemma₂ (abs-sub x x₁) γ==γ′ = {!!}
  fundamental-lemma₂ (app-sub x x₁ x₂) γ==γ′ = {!!}
  fundamental-lemma₂ (sub-comp x x₁ x₂) γ==γ′ = {!!}
  fundamental-lemma₂ (app-compatible t==t′ t==t′₁) γ==γ′ = {!!}
  fundamental-lemma₂ (ξ t==t′) γ==γ′ = {!!}
  fundamental-lemma₂ (refl ⊢t) γ==γ′ = {!!}
  fundamental-lemma₂ (sym t==t′) γ==γ′ = {!!}
  fundamental-lemma₂ (trans t==t′ t==t′₁) γ==γ′ = {!!}
