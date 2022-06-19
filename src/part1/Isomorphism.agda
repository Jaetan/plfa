module part1.Isomorphism where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm; +-identityʳ; +-assoc)

_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
(g ∘ f) x  = g (f x)

_∘′_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
g ∘′ f  =  λ x → g (f x)

postulate
  extensionality : ∀ {A B : Set} {f g : A → B} → (∀ (x : A) → f x ≡ g x) → f ≡ g

_+′_ : ℕ → ℕ → ℕ
m +′ zero  = m
m +′ suc n = suc (m +′ n)

same-app : ∀ (m n : ℕ) → m +′ n ≡ m + n
same-app m n rewrite +-comm m n = helper m n
  where
    helper : ∀ (m n : ℕ) → m +′ n ≡ n + m
    helper m zero    = refl
    helper m (suc n) = cong suc (helper m n)

same : _+′_ ≡ _+_
same = extensionality (λ m → extensionality (λ n → same-app m n))

postulate
  ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : ∀(x : A) → B x} → (∀ (x : A) → f x ≡ g x) → f ≡ g

infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≃_

data _≃′_ (A B : Set): Set where
  mk-≃′ : ∀ (to : A → B) →
          ∀ (from : B → A) →
          ∀ (from∘to : (∀ (x : A) → from (to x) ≡ x)) →
          ∀ (to∘from : (∀ (y : B) → to (from y) ≡ y)) →
          A ≃′ B

to′ : ∀ {A B : Set} → (A ≃′ B) → (A → B)
to′ (mk-≃′ f g g∘f f∘g) = f

from′ : ∀ {A B : Set} → (A ≃′ B) → (B → A)
from′ (mk-≃′ f g g∘f f∘g) = g

from∘to′ : ∀ {A B : Set} → (A≃B : A ≃′ B) → (∀ (x : A) → from′ A≃B (to′ A≃B x) ≡ x)
from∘to′ (mk-≃′ f g g∘f f∘g) = g∘f

to∘from′ : ∀ {A B : Set} → (A≃B : A ≃′ B) → (∀ (y : B) → to′ A≃B (from′ A≃B y) ≡ y)
to∘from′ (mk-≃′ f g g∘f f∘g) = f∘g

≃-refl : ∀ {A : Set} → A ≃ A
≃-refl = record
           { to      = λ{x → x}
           ; from    = λ{y → y}
           ; from∘to = λ{x → refl}
           ; to∘from = λ{y → refl}
           }

≃-sym : ∀ {A B : Set} → A ≃ B → B ≃ A
≃-sym A≃B = record
              { to      = from A≃B
              ; from    = to   A≃B
              ; from∘to = to∘from A≃B
              ; to∘from = from∘to A≃B
              }

≃-trans : ∀ {A B C : Set} → A ≃ B → B ≃ C → A ≃ C
≃-trans A≃B B≃C = record
                    { to      = to B≃C ∘ to A≃B
                    ; from    = from A≃B ∘ from B≃C
                    ; from∘to = λ{x → begin
                        (from A≃B ∘ from B≃C) ((to B≃C ∘ to A≃B) x) ≡⟨⟩
                        from A≃B (from B≃C (to B≃C (to A≃B x)))     ≡⟨ cong (from A≃B) (from∘to B≃C (to A≃B x)) ⟩
                        from A≃B (to A≃B x)                         ≡⟨ from∘to A≃B x ⟩
                        x ∎}
                    ; to∘from = λ x → begin
                        to B≃C (to A≃B ((from A≃B ∘ from B≃C) x)) ≡⟨ cong (to B≃C) (to∘from A≃B (from B≃C x)) ⟩
                        to B≃C (from B≃C x)                       ≡⟨ to∘from B≃C x ⟩
                        x ∎
                    }

module ≃-Reasoning where

  infix  1 ≃-begin_
  infixr 2 _≃⟨_⟩_
  infix  3 _≃-∎

  ≃-begin_ : ∀ {A B : Set} → A ≃ B → A ≃ B
  ≃-begin A≃B = A≃B

  _≃⟨_⟩_ : ∀ (A : Set) {B C : Set} → A ≃ B → B ≃ C → A ≃ C
  A ≃⟨ A≃B ⟩ B≃C = ≃-trans A≃B B≃C

  _≃-∎ : ∀ (A : Set) → A ≃ A
  A ≃-∎ = ≃-refl

open ≃-Reasoning

infix 0 _≲_

record _≲_ (A B : Set) : Set where
  field
    to      : A → B
    from    : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x

open _≲_

≲-refl : ∀ {A : Set} → A ≲ A
≲-refl =
  record
    { to      = λ{x → x}
    ; from    = λ{y → y}
    ; from∘to = λ{x → refl}
    }

≲-trans : ∀ {A B C : Set} → A ≲ B → B ≲ C → A ≲ C
≲-trans A≲B B≲C =
  record
    { to      = λ{x → to   B≲C (to   A≲B x)}
    ; from    = λ{y → from A≲B (from B≲C y)}
    ; from∘to = λ{x →
        begin from A≲B (from B≲C (to B≲C (to A≲B x)))
        ≡⟨ cong (from A≲B) (from∘to B≲C (to A≲B x)) ⟩ from A≲B (to A≲B x)
        ≡⟨ from∘to A≲B x ⟩ x ∎}
    }

≲-antisym : ∀ {A B : Set} → (A≲B : A ≲ B) → (B≲A : B ≲ A) → (to A≲B ≡ from B≲A) → (from A≲B ≡ to B≲A) → A ≃ B
≲-antisym A≲B B≲A to≡from from≡to =
  record
    { to      = to A≲B
    ; from    = from A≲B
    ; from∘to = from∘to A≲B
    ; to∘from = λ{y →
        begin to A≲B (from A≲B y)
        ≡⟨ cong (to A≲B) (cong-app from≡to y) ⟩ to A≲B (to B≲A y)
        ≡⟨ cong-app to≡from (to B≲A y) ⟩ from B≲A (to B≲A y)
        ≡⟨ from∘to B≲A y ⟩ y ∎}
    }

module ≲-Reasoning where

  infix  1 ≲-begin_
  infixr 2 _≲⟨_⟩_
  infix  3 _≲-∎

  ≲-begin_ : ∀ {A B : Set} → A ≲ B → A ≲ B
  ≲-begin A≲B = A≲B

  _≲⟨_⟩_ : ∀ (A : Set) {B C : Set} → A ≲ B → B ≲ C → A ≲ C
  A ≲⟨ A≲B ⟩ B≲C = ≲-trans A≲B B≲C

  _≲-∎ : ∀ (A : Set) → A ≲ A
  A ≲-∎ = ≲-refl

open ≲-Reasoning

≃-implies-≲ : ∀ {A B : Set} → A ≃ B → A ≲ B
≃-implies-≲ A≃B =
  record
    { to = to A≃B
    ; from = from A≃B
    ; from∘to = from∘to A≃B
    }

record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A

open _⇔_

⇔-refl : ∀ {A : Set} → A ⇔ A
⇔-refl = record
           { to = λ x → x
           ; from = λ x → x
           }

⇔-sym : ∀ {A B : Set} → A ⇔ B → B ⇔ A
⇔-sym A⇔B = record
              { to = from A⇔B
              ; from = to A⇔B
              }

⇔-trans : ∀ {A B C : Set} → A ⇔ B → B ⇔ C → A ⇔ C
⇔-trans A⇔B B⇔C = record
                    { to = to B⇔C ∘ to A⇔B
                    ; from = from A⇔B ∘ from B⇔C
                    }

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)

module Binary where

  data Bin : Set where
    ⟨⟩ : Bin
    _O : Bin → Bin
    _I : Bin → Bin

  Bin-inc : Bin → Bin
  Bin-inc ⟨⟩ = ⟨⟩ I
  Bin-inc (b O) = b I
  Bin-inc (b I) = Bin-inc b O

  Bin-to : ℕ → Bin
  Bin-to zero = ⟨⟩ O
  Bin-to (suc n) = Bin-inc (Bin-to n)

open Binary

Bin-from : Bin → ℕ
Bin-from ⟨⟩ = 0
Bin-from (b O) = 2 * Bin-from b
Bin-from (b I) = 2 * Bin-from b + 1

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

-- See Induction.agda for this proof and a compatible version of inc
Bin-from-to : ∀ n → Bin-from (Bin-to n) ≡ n
Bin-from-to zero = refl
Bin-from-to (suc n) = begin
  Bin-from (Bin-to (suc n))     ≡⟨⟩
  Bin-from (Bin-inc (Bin-to n)) ≡⟨ from-inc-suc (Bin-to n) ⟩
  suc (Bin-from (Bin-to n))     ≡⟨ cong suc (Bin-from-to n) ⟩
  suc n                         ∎
  where
    n+1 : ∀ (n : ℕ) → n + 1 ≡ suc n
    n+1 zero = refl
    n+1 (suc n) rewrite n+1 n = refl

    from-inc-suc : ∀ b → Bin-from (Bin-inc b) ≡ suc (Bin-from b)
    from-inc-suc ⟨⟩ = refl
    from-inc-suc (b O) rewrite +-identityʳ (Bin-from b) | n+1 (Bin-from b + Bin-from b) = refl
    from-inc-suc (b I) rewrite +-identityʳ (Bin-from (Bin-inc b))
                       | from-inc-suc b
                       | +-identityʳ (Bin-from b)
                       | sym (n+1 (Bin-from b))
                       | +-assoc (Bin-from b) (Bin-from b) 1 = refl

Bin-embedding : ℕ ≲ Bin
Bin-embedding = record
    { to = Bin-to
    ; from = Bin-from
    ; from∘to = Bin-from-to
    }

-- import Function using (_∘_)
-- import Function.Inverse using (_↔_)
-- import Function.LeftInverse using (_↞_)
