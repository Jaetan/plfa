module part1.Equality where

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : ∀ {A B C : Set} (f : A → B → C) {u x : A} {v y : B} → u ≡ x → v ≡ y → f u v ≡ f x y
cong₂ f refl refl = refl

cong-app : ∀ {A B : Set} {f g : A → B} → f ≡ g → ∀ (x : A) → f x ≡ g x
cong-app refl x = refl

subst : ∀ {A : Set} {x y : A} (P : A → Set) → x ≡ y → P x → P y
subst P refl px = px

module ≡-Reasoning {A : Set} where

  infix  1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {x y : A} → x ≡ y → x ≡ y
  begin x≡y = x≡y

  _≡⟨⟩_ : ∀ (x : A) {y : A} → x ≡ y → x ≡ y
  x ≡⟨⟩ x≡y = x≡y

  _≡⟨_⟩_ : ∀ (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
  x ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

  _∎ : ∀ (x : A) → x ≡ x
  x ∎  =  refl

open ≡-Reasoning

trans' : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans' {A} {x} {y} {z} x≡y y≡z = begin x ≡⟨ x≡y ⟩ y ≡⟨ y≡z ⟩ z ∎

-- _≡⟨_⟩_ requires trans in its definition. If we replace trans with
-- trans', we end up with trans' requiring _≡⟨_⟩_, which in turn requires
-- trans'. None of these two definitions reduces to anything before
-- calling the other: _≡⟨_⟩_ is the head call of trans' (as begin_ is
-- simply a placeholder), and trans' is the head call of _≡⟨_⟩_.

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero    + n  =  n
(suc m) + n  =  suc (m + n)

postulate
  +-identity : ∀ (m : ℕ) → m + zero ≡ m
  +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
  +-zeroʳ : ∀ n → n + zero ≡ n

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero = begin m + zero ≡⟨ +-identity m ⟩ zero + m ∎
+-comm m (suc n) = begin m + suc n ≡⟨ +-suc m n ⟩ suc (m + n)
                                   ≡⟨ cong suc (+-comm m n) ⟩ suc (n + m)
                                   ≡⟨⟩ suc n + m ∎

data _≤_ : (x y : ℕ) → Set where
  z≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n

infix 4 _≤_

refl-≤ : ∀ {x : ℕ} → x ≤ x
refl-≤ {zero} = z≤n
refl-≤ {suc x} = s≤s refl-≤

-- ≤-inv : ∀ {x y : ℕ} → suc x ≤ suc y → x ≤ y
-- ≤-inv (s≤s x≤y) = x≤y

trans-≤ : ∀ {x y z : ℕ} → x ≤ y → y ≤ z → x ≤ z
trans-≤ z≤n _ = z≤n
trans-≤ (s≤s x≤y) (s≤s y≤z) = s≤s (trans-≤ x≤y y≤z)

module ≤-Reasoning where

  infix  1 begin-≤_
  infixr 2 _≤⟨⟩_ _≤⟨_⟩_
  infix  3 _∎-≤

  begin-≤_ : ∀ {x y : ℕ} → x ≤ y → x ≤ y
  begin-≤ x≤y = x≤y

  _≤⟨⟩_ : ∀ (x : ℕ) {y : ℕ} → x ≤ y → x ≤ y
  x ≤⟨⟩ x≤y = x≤y

  _≤⟨_⟩_ : ∀ (x : ℕ) {y z : ℕ} → x ≤ y → y ≤ z → x ≤ z
  x ≤⟨ x≤y ⟩ y≤z = trans-≤ x≤y y≤z

  _∎-≤ : ∀ (x : ℕ) → x ≤ x
  x ∎-≤  =  refl-≤

open ≤-Reasoning

{-# BUILTIN EQUALITY _≡_ #-}

-- +-zeroʳ : ∀ n → n + zero ≡ n
-- +-zeroʳ zero = refl
-- +-zeroʳ (suc n) rewrite +-zeroʳ n = refl

+-monoʳ-≤ : ∀ {n p q} → p ≤ q → n + p ≤ n + q
+-monoʳ-≤ {zero} p≤q = p≤q
+-monoʳ-≤ {suc n} {p} {q} p≤q = begin-≤ suc (n + p) ≤⟨ s≤s (+-monoʳ-≤ p≤q) ⟩ suc (n + q) ∎-≤
-- +-monoʳ-≤ {suc n} p≤q = s≤s (+-monoʳ-≤ p≤q)

+-monoˡ-≤ : ∀ {m n p} → m ≤ n → m + p ≤ n + p
+-monoˡ-≤ {m} {n} {zero} m≤n rewrite +-zeroʳ m | +-zeroʳ n = m≤n
+-monoˡ-≤ {m} {n} {suc p} m≤n rewrite +-suc m p | +-suc n p = begin-≤ suc (m + p) ≤⟨ s≤s (+-monoˡ-≤ m≤n) ⟩ suc (n + p) ∎-≤
-- +-monoˡ-≤ {m} {n} {suc p} m≤n rewrite +-suc m p | +-suc n p = s≤s (+-monoˡ-≤ m≤n)

+-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q = begin-≤ m + p ≤⟨ +-monoˡ-≤ m≤n ⟩ n + p
                                         ≤⟨ +-monoʳ-≤ p≤q ⟩ n + q ∎-≤

data even : ℕ → Set
data odd : ℕ → Set

data even where
  even-zero : even zero
  even-suc : ∀ {n} → odd n → even (suc n)

data odd where
  odd-suc : ∀ {n} → even n → odd (suc n)

even-comm : ∀ m n → even (m + n) → even (n + m)
even-comm m n p rewrite +-comm m n = p

+-comm' : ∀ m n → m + n ≡ n + m
+-comm' zero n rewrite +-zeroʳ n = refl
+-comm' (suc m) n rewrite +-suc n m | +-comm' n m = refl

even-comm' : ∀ m n → even (m + n) → even (n + m)
even-comm' m n p with   m + n  | +-comm m n
...                 | .(n + m) | refl       = p

even-comm'' : ∀ m n → even (m + n) → even (n + m)
even-comm'' m n = subst even (+-comm m n)

_≐_ : ∀ {A : Set} (x y : A) → Set₁
_≐_ {A} x y = ∀ (P : A → Set) → P x → P y

refl-≐ : ∀ {A : Set} {x : A} → x ≐ x
refl-≐ P Px = Px

trans-≐ : ∀ {A : Set} {x y z : A} → x ≐ y → y ≐ z → x ≐ z
trans-≐ x≐y y≐z P Px = y≐z P (x≐y P Px)

sym-≐ : ∀ {A : Set} {x y : A} → x ≐ y → y ≐ x
sym-≐ {A} {x} {y} x≐y P = Qy
  where
    Q : A → Set
    Q z = P z → P x

    Qx : Q x
    Qx = refl-≐ P

    Qy : Q y
    Qy = x≐y Q Qx

≡-implies-≐ : ∀ {A : Set} {x y : A} → x ≡ y → x ≐ y
≡-implies-≐ x≡y P = subst P x≡y

≐-implies-≡ : ∀ {A : Set} {x y : A} → x ≐ y → x ≡ y
≐-implies-≡ {A} {x} {y} x≐y = Qy
  where
    Q : A → Set
    Q z = x ≡ z

    Qx : Q x
    Qx = refl

    Qy : Q y
    Qy = x≐y Q Qx

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)

data _≡′_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl′ : x ≡′ x

sym′ : ∀ {ℓ : Level} {A : Set ℓ} {x y : A} → x ≡′ y → y ≡′ x
sym′ refl′ = refl′

_≐′_ : ∀ {ℓ : Level} {A : Set ℓ} (x y : A) → Set (lsuc ℓ)
_≐′_ {ℓ} {A} x y = ∀ (P : A → Set ℓ) → P x → P y

_∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} → (B → C) → (A → B) → A → C
(g ∘ f) x  =  g (f x)

-- import Relation.Binary.PropositionalEquality as Eq
-- open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
-- open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
