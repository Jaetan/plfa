module part1.Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_)
open import part1.Isomorphism using (_≃_; extensionality)

¬_ : Set → Set
¬ A = A → ⊥

¬-elim : ∀ {A : Set} → ¬ A → A → ⊥
¬-elim ¬x x = ¬x x

infix 3 ¬_

¬¬-intro : ∀ {A : Set} → A → ¬ ¬ A
¬¬-intro x = λ{¬x → ¬x x}

¬¬-intro′ : ∀ {A : Set} → A → ¬ ¬ A
¬¬-intro′ x ¬x = ¬x x

¬¬¬-elim : ∀ {A : Set} → ¬ ¬ ¬ A → ¬ A
¬¬¬-elim ¬¬¬x  =  λ x → ¬¬¬x (¬¬-intro x)

contraposition : ∀ {A B : Set} → (A → B) → (¬ B → ¬ A)
contraposition f ¬y x = ¬y (f x)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y  =  ¬ (x ≡ y)

_ : 1 ≢ 2
_ = λ()

peano : ∀ {m : ℕ} → zero ≢ suc m
peano = λ()

id : ⊥ → ⊥
id x = x

id′ : ⊥ → ⊥
id′ ()

id≡id′ : id ≡ id′
id≡id′ = extensionality (λ())

assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation ¬x ¬x′ = extensionality (λ x → ⊥-elim (¬x x))

infix 4 _<_

data _<_ : ℕ → ℕ → Set where
  z<s : ∀ {n : ℕ} → zero < suc n
  s<s : ∀ {m n : ℕ} → m < n → suc m < suc n

<-irreflexive : ∀ {n : ℕ} → ¬ (n < n)
<-irreflexive (s<s p) = <-irreflexive p

open import Relation.Binary.PropositionalEquality using (cong)
open import Data.Product

<-strict : ∀ {m n : ℕ} → m < n → ¬ m ≡ n
<-strict z<s = λ ()
<-strict (s<s p<) refl = <-irreflexive p<

<-nonsymmetical : ∀ {m n : ℕ} → m < n → ¬ n < m
<-nonsymmetical (s<s p) (s<s q) = <-nonsymmetical p q

<-trichotomy₀ : ∀ {m n : ℕ} → m < n ⊎ m ≡ n ⊎ n < m
<-trichotomy₀ {zero} {zero} = inj₂ (inj₁ refl)
<-trichotomy₀ {zero} {(suc n)} = inj₁ z<s
<-trichotomy₀ {(suc m)} {zero} = inj₂ (inj₂ z<s)
<-trichotomy₀ {(suc m)} {(suc n)} with <-trichotomy₀ {m} {n}
... | inj₁ p< = inj₁ (s<s p<)
... | inj₂ (inj₁ p≡) = inj₂ (inj₁ (cong suc p≡))
... | inj₂ (inj₂ p>) = inj₂ (inj₂ (s<s p>))

<-trichotomy-≡ : ∀ {m n : ℕ} → m ≡ n → ¬ m < n × ¬ n < m
<-trichotomy-≡ refl = <-irreflexive , <-irreflexive

<-trichotomy-< : ∀ {m n : ℕ} → m < n → ¬ m ≡ n × ¬ n < m
<-trichotomy-< z<s = (λ ()) , λ ()
<-trichotomy-< (s<s p<) = <-strict (s<s p<) , λ { (s<s p>) → <-nonsymmetical p< p> }

<-trichotomy-> : ∀ {m n : ℕ} → n < m → ¬ n ≡ m × ¬ m < n
<-trichotomy-> = <-trichotomy-<

<-trichotomy : ∀ {m n : ℕ} → (m < n ⊎ m ≡ n ⊎ n < m) × (m ≡ n → ¬ m < n × ¬ n < m) × (m < n → ¬ m ≡ n × ¬ n < m) × (n < m → ¬ n ≡ m × ¬ m < n)
<-trichotomy = <-trichotomy₀ , <-trichotomy-≡ , <-trichotomy-< , <-trichotomy->

open import part1.Isomorphism using (_∘_)
open import part1.Connectives using (η-⊎ ; uniq-⊎ ; case-⊎)

⊎-dual-× : ∀ {A B : Set} → ¬ (A ⊎ B) ≃ ¬ A × ¬ B
⊎-dual-× = record
  { to = λ ¬a⊎b → ¬a⊎b ∘ inj₁ , ¬a⊎b ∘ inj₂
  ; from = λ ¬a×¬b → λ { (inj₁ a) → proj₁ ¬a×¬b a
                       ; (inj₂ b) → proj₂ ¬a×¬b b }
  ; from∘to = λ ¬a⊎b → {!!}
  ; to∘from = {!!} }
