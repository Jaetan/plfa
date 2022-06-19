module part1.Connectives where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import part1.Isomorphism using (_≃_; _≲_; extensionality)
open part1.Isomorphism.≃-Reasoning

data _×_ (A B : Set) : Set where
  ⟨_,_⟩ : A → B → A × B

proj₁ : ∀ {A B : Set} → A × B → A
proj₁ ⟨ x , y ⟩ = x

proj₂ : ∀ {A B : Set} → A × B → B
proj₂ ⟨ x , y ⟩ = y

η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ x , y ⟩ = refl

infixr 2 _×_

record _×′_ (A B : Set) : Set where
  constructor ⟨_,_⟩′
  field
    proj₁′ : A
    proj₂′ : B
open _×′_

η-×′ : ∀ {A B : Set} (w : A ×′ B) → ⟨ proj₁′ w , proj₂′ w ⟩′ ≡ w
η-×′ w = refl

data Bool : Set where
  true  : Bool
  false : Bool

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

×-count : Bool × Tri → ℕ
×-count ⟨ true  , aa ⟩   =  1
×-count ⟨ true  , bb ⟩   =  2
×-count ⟨ true  , cc ⟩   =  3
×-count ⟨ false  , aa ⟩  =  4
×-count ⟨ false  , bb ⟩  =  5
×-count ⟨ false  , cc ⟩  =  6

×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm =
  record
    { to      =  λ{ ⟨ x , y ⟩ → ⟨ y , x ⟩ }
    ; from    =  λ{ ⟨ y , x ⟩ → ⟨ x , y ⟩ }
    ; from∘to =  λ{ ⟨ x , y ⟩ → refl }
    ; to∘from =  λ{ ⟨ y , x ⟩ → refl }
    }

×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc =
  record
    { to      = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → ⟨ x , ⟨ y , z ⟩ ⟩ }
    ; from    = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ x , y ⟩ , z ⟩ }
    ; from∘to = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → refl }
    ; to∘from = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → refl }
    }

record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
open _⇔_

⇔≃× : ∀ {A B : Set} → A ⇔ B ≃ (A → B) × (B → A)
⇔≃× =
  record
    { to      = λ p → ⟨ to p , from p ⟩
    ; from    = λ f → record { to = proj₁ f ; from = proj₂ f }
    ; from∘to = λ p → refl
    ; to∘from = λ f → η-× f
    }

data ⊤ : Set where
  tt : ⊤

η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl

record ⊤′ : Set where
  constructor tt′

η-⊤′ : ∀ (w : ⊤′) → tt′ ≡ w
η-⊤′ w = refl

truth′ : ⊤′
truth′ = _

⊤-count : ⊤ → ℕ
⊤-count tt = 1

⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identityˡ =
  record
    { to      = λ{ ⟨ tt , x ⟩ → x }
    ; from    = λ{ x → ⟨ tt , x ⟩ }
    ; from∘to = λ{ ⟨ tt , x ⟩ → refl }
    ; to∘from = λ{ x → refl }
    }

⊤-identityʳ : ∀ {A : Set} → (A × ⊤) ≃ A
⊤-identityʳ {A} =
  ≃-begin
  (A × ⊤) ≃⟨ ×-comm ⟩
  (⊤ × A) ≃⟨ ⊤-identityˡ ⟩
  A ≃-∎

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

case-⊎ : ∀ {A B C : Set} → (A → C) → (B → C) → A ⊎ B → C
case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ y) = g y

η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ y) = refl

uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) → case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ x) = refl
uniq-⊎ h (inj₂ y) = refl

infixr 1 _⊎_

⊎-count : Bool ⊎ Tri → ℕ
⊎-count (inj₁ true)   =  1
⊎-count (inj₁ false)  =  2
⊎-count (inj₂ aa)     =  3
⊎-count (inj₂ bb)     =  4
⊎-count (inj₂ cc)     =  5

⊎-comm : ∀ {A B : Set} → A ⊎ B ≃ B ⊎ A
⊎-comm = record
  { to = case-⊎ inj₂ inj₁
  ; from = case-⊎ inj₂ inj₁
  ; from∘to = λ{ (inj₁ x) → refl ; (inj₂ y) → refl } 
  ; to∘from = λ{ (inj₁ x) → refl ; (inj₂ y) → refl }
  }

⊎-assoc : ∀ {A B C : Set} → (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-assoc = record
  { to = λ{ (inj₁ a⊎b) → case-⊎ inj₁ (inj₂ ∘ inj₁) a⊎b
          ; (inj₂ c) → inj₂ (inj₂ c) }
  ; from = λ{ (inj₁ a) → inj₁ (inj₁ a)
            ; (inj₂ b⊎c) → case-⊎ (inj₁ ∘ inj₂) inj₂ b⊎c }
  ; from∘to = λ{ (inj₁ (inj₁ a)) → refl
               ; (inj₁ (inj₂ b)) → refl
               ; (inj₂ c) → refl}
  ; to∘from = λ{ (inj₁ a) → refl
                ; (inj₂ (inj₁ b)) → refl
                ; (inj₂ (inj₂ c)) → refl}
  }

data ⊥ : Set where

⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()

uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h ()

⊥-count : ⊥ → ℕ
⊥-count ()

⊥-identityˡ : ∀ {A : Set} → ⊥ ⊎ A ≃ A
⊥-identityˡ = record
  { to = λ{ (inj₁ ()) ; (inj₂ a) → a }
  ; from = λ a → inj₂ a
  ; from∘to = λ{ (inj₁ ()) ; (inj₂ a) → refl }
  ; to∘from = λ a → refl }

⊥-identityʳ : ∀ {A : Set} → A ⊎ ⊥ ≃ A
⊥-identityʳ = record
  { to = λ{ (inj₁ a) → a ; (inj₂ ()) }
  ; from = λ a → inj₁ a
  ; from∘to = λ{ (inj₁ a) → refl ; (inj₂ ()) }
  ; to∘from = λ{ a → refl }
  }

→-elim : ∀ {A B : Set} → (A → B) → A → B
→-elim L M = L M

η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl

→-count : (Bool → Tri) → ℕ
→-count f with f true | f false
...          | aa     | aa      =   1
...          | aa     | bb      =   2
...          | aa     | cc      =   3
...          | bb     | aa      =   4
...          | bb     | bb      =   5
...          | bb     | cc      =   6
...          | cc     | aa      =   7
...          | cc     | bb      =   8
...          | cc     | cc      =   9

currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
currying = record
  { to      =  λ{ f → λ{ ⟨ x , y ⟩ → f x y }}
  ; from    =  λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ }}}
  ; from∘to =  λ{ f → refl }
  ; to∘from =  λ{ g → extensionality λ{ ⟨ x , y ⟩ → refl }}
  }

→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ = record
  { to      = λ{ f → ⟨ f ∘ inj₁ , f ∘ inj₂ ⟩ }
  ; from    = λ{ ⟨ g , h ⟩ → λ{ (inj₁ x) → g x ; (inj₂ y) → h y } }
  ; from∘to = λ{ f → extensionality λ{ (inj₁ x) → refl ; (inj₂ y) → refl } }
  ; to∘from = λ{ ⟨ g , h ⟩ → refl }
  }

→-distrib-× : ∀ {A B C : Set} → (A → B × C) ≃ (A → B) × (A → C)
→-distrib-× = record
  { to      = λ{ f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩ }
  ; from    = λ{ ⟨ g , h ⟩ → λ x → ⟨ g x , h x ⟩ }
  ; from∘to = λ{ f → extensionality λ{ x → η-× (f x) } }
  ; to∘from = λ{ ⟨ g , h ⟩ → refl }
  }

×-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
×-distrib-⊎ = record
  { to      = λ{ ⟨ inj₁ x , z ⟩ → (inj₁ ⟨ x , z ⟩)
               ; ⟨ inj₂ y , z ⟩ → (inj₂ ⟨ y , z ⟩)
               }
  ; from    = λ{ (inj₁ ⟨ x , z ⟩) → ⟨ inj₁ x , z ⟩
               ; (inj₂ ⟨ y , z ⟩) → ⟨ inj₂ y , z ⟩
               }
  ; from∘to = λ{ ⟨ inj₁ x , z ⟩ → refl
               ; ⟨ inj₂ y , z ⟩ → refl
               }
  ; to∘from = λ{ (inj₁ ⟨ x , z ⟩) → refl
               ; (inj₂ ⟨ y , z ⟩) → refl
               }
  }

⊎-distrib-× : ∀ {A B C : Set} → (A × B) ⊎ C ≲ (A ⊎ C) × (B ⊎ C)
⊎-distrib-× = record
  { to      = λ{ (inj₁ ⟨ x , y ⟩) → ⟨ inj₁ x , inj₁ y ⟩
               ; (inj₂ z)         → ⟨ inj₂ z , inj₂ z ⟩
               }
  ; from    = λ{ ⟨ inj₁ x , inj₁ y ⟩ → (inj₁ ⟨ x , y ⟩)
               ; ⟨ inj₁ x , inj₂ z ⟩ → (inj₂ z)
               ; ⟨ inj₂ z , _      ⟩ → (inj₂ z)
               }
  ; from∘to = λ{ (inj₁ ⟨ x , y ⟩) → refl
               ; (inj₂ z)         → refl
               }
  }

⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
⊎-weak-× ⟨ inj₁ x , y ⟩ = inj₁ x
⊎-weak-× ⟨ inj₂ x , y ⟩ = inj₂ ⟨ x , y ⟩

-- In the hole below must come a term of type (A ⊎ B) × C, but we only
-- have x : A and no term of type C to complete the product. So this
-- implication is not true.
--
-- f : ∀ {A B C : Set} → A ⊎ (B × C) → (A ⊎ B) × C
-- f (inj₁ x) = {!!}
-- f (inj₂ x) = ⟨ inj₂ (proj₁ x) , proj₂ x ⟩
--
-- In particular, this means that there is no embedding:
--
--  ∀ {A B C : Set} → (A ⊎ B) × C ≲ A ⊎ (B × C)
--
-- because f would be the function "from", which can therefore not be
-- defined

⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
⊎×-implies-×⊎ (inj₁ ⟨ x , y ⟩) = ⟨ inj₁ x , inj₁ y ⟩
⊎×-implies-×⊎ (inj₂ ⟨ x , y ⟩) = ⟨ inj₂ x , inj₂ y ⟩

-- In the first hole below, there are no terms of types B (resp. C) to
-- build a term of type A × B (resp. C × D). Similarly, in the second
-- hole, there are no terms of types A (resp. D) to build a term of
-- type A × B (resp. C × D). So this implication does not hold.
-- 
-- f : ∀ {A B C D : Set} → (A ⊎ C) × (B ⊎ D) → (A × B) ⊎ (C × D)
-- f ⟨ inj₁ x , inj₁ y ⟩ = inj₁ ⟨ x , y ⟩
-- f ⟨ inj₁ x , inj₂ y ⟩ = {!!}
-- f ⟨ inj₂ x , inj₁ y ⟩ = {!!}
-- f ⟨ inj₂ x , inj₂ y ⟩ = inj₂ ⟨ x , y ⟩

-- import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
-- import Data.Unit using (⊤; tt)
-- import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
-- import Data.Empty using (⊥; ⊥-elim)
-- import Function.Equivalence using (_⇔_)
