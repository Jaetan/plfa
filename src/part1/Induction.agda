module part1.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

-- Associative and commutative, with distributivity: locigal ∨ and ∧
-- Associtaive but not commutative: function composition ∘

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p = begin (zero + n) + p ≡⟨⟩ n + p ≡⟨⟩ zero + (n + p) ∎
+-assoc (suc m) n p = begin
                      (suc m + n) + p ≡⟨⟩ suc (m + n) + p
                                      ≡⟨⟩ suc ((m + n) + p)
                                      ≡⟨ cong suc (+-assoc m n p) ⟩ suc (m + (n + p))
                                      ≡⟨⟩ suc m + (n + p) ∎

+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero = begin zero + zero ≡⟨⟩ zero ∎
+-identityʳ (suc m) = begin (suc m) + zero ≡⟨⟩ suc (m + zero)
                                           ≡⟨ cong suc (+-identityʳ m) ⟩ suc m ∎

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n = begin zero + suc n ≡⟨⟩ suc n
                                  ≡⟨⟩ suc (zero + n) ∎
+-suc (suc m) n =  begin suc m + suc n ≡⟨⟩ suc (m + suc n)
                                       ≡⟨  cong suc (+-suc m n) ⟩ suc (suc (m + n)) ∎

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero = begin m + zero ≡⟨ +-identityʳ m ⟩ m
                               ≡⟨⟩ zero + m ∎
+-comm m (suc n) = begin m + suc n ≡⟨ +-suc m n ⟩ suc (m + n)
                                   ≡⟨ cong suc (+-comm m n) ⟩ suc n + m ∎

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q = begin (m + n) + (p + q) ≡⟨ +-assoc m n (p + q) ⟩ m + (n + (p + q))
                                              ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩ m + ((n + p) + q)
                                              ≡⟨ sym (+-assoc m (n + p) q) ⟩ (m + (n + p) + q) ∎

{-
  step 0: nothing is known but the rules for integers and those for associativity
  
  step 1: 0 is known (base case for integers), nothing is known from associativity

  step 2: 0, 1 are known
          (0 + 0) + 0 ≡ 0 + (0 + 0) is known (base case for associativity)

  step 3: 0, 1, 2 are known

          known from associativity (base case):
          (0 + 0) + 0 ≡ 0 + (0 + 0)
          (0 + 0) + 1 ≡ 0 + (0 + 1)
          (0 + 1) + 1 ≡ 0 + (1 + 1)
          (0 + 1) + 0 ≡ 0 + (1 + 0)

          known from associativity (inductive case):
          (1 + 0) + 0 ≡ 1 + (0 + 0)
          (1 + 0) + 1 ≡ 1 + (0 + 1)
          (1 + 1) + 0 ≡ 1 + (1 + 0)
          (1 + 1) + 1 ≡ 1 + (1 + 1)

  step 4: 0, 1, 2, 3 are known

          known from associativity (base case):
          (0 + 0) + 0 ≡ 0 + (0 + 0)
          (0 + 0) + 1 ≡ 0 + (0 + 1)
          (0 + 0) + 2 ≡ 0 + (0 + 2)
          (0 + 1) + 0 ≡ 0 + (1 + 0)
          (0 + 1) + 1 ≡ 0 + (1 + 1)
          (0 + 1) + 2 ≡ 0 + (1 + 2)
          (0 + 2) + 0 ≡ 0 + (2 + 0)
          (0 + 2) + 1 ≡ 0 + (2 + 1)
          (0 + 2) + 2 ≡ 0 + (2 + 2)

          known from associativity (inductive case):
          (1 + 0) + 0 ≡ 1 + (0 + 0)
          (1 + 0) + 1 ≡ 1 + (0 + 1)
          (1 + 0) + 2 ≡ 1 + (0 + 2)
          (1 + 1) + 0 ≡ 1 + (1 + 0)
          (1 + 1) + 1 ≡ 1 + (1 + 1)
          (1 + 1) + 2 ≡ 1 + (1 + 2)
          (1 + 2) + 0 ≡ 1 + (2 + 0)
          (1 + 2) + 1 ≡ 1 + (2 + 1)
          (1 + 2) + 2 ≡ 1 + (2 + 2)
          (2 + 0) + 0 ≡ 2 + (0 + 0)
          (2 + 0) + 1 ≡ 2 + (0 + 1)
          (2 + 0) + 2 ≡ 2 + (0 + 2)
          (2 + 1) + 0 ≡ 2 + (1 + 0)
          (2 + 1) + 1 ≡ 2 + (1 + 1)
          (2 + 1) + 2 ≡ 2 + (1 + 2)
          (2 + 2) + 0 ≡ 2 + (2 + 0)
          (2 + 2) + 1 ≡ 2 + (2 + 1)
          (2 + 2) + 2 ≡ 2 + (2 + 2)
-}

+-assoc' : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc' zero n p = refl
+-assoc' (suc m) n p rewrite +-assoc' m n p = refl

+-identity' : ∀ (n : ℕ) → n + zero ≡ n
+-identity' zero = refl
+-identity' (suc n) rewrite +-identity' n = refl

+-suc' : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc' zero n = refl
+-suc' (suc m) n rewrite +-suc' m n = refl

+-comm' : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm' m zero rewrite +-identity' m = refl
+-comm' m (suc n) rewrite +-suc' m n | +-comm' m n = refl

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p rewrite +-comm' m (n + p) | +-comm' m p | +-assoc' n p m = refl

*-distrib : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib zero n p = refl
*-distrib (suc m) n p rewrite *-distrib m n p | +-assoc' p (m * p) (n * p) = refl

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p rewrite *-distrib n (m * n) p | *-assoc m n p = refl

*-absorption' : ∀ (n : ℕ) → n * zero ≡ zero
*-absorption' zero = refl
*-absorption' (suc n) rewrite *-absorption' n = refl

*-identity' : ∀ (n : ℕ) → n * 1 ≡ n
*-identity' zero = refl
*-identity' (suc n) rewrite *-identity' n = refl

*-comm' : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm' zero n rewrite *-absorption' n = refl
*-comm' (suc m) zero rewrite *-absorption' m = refl
*-comm' (suc m) (suc n) rewrite *-comm' m (suc n) | *-comm' n (suc m)
                        | sym (+-assoc' n m (n * m)) | sym (+-assoc' m n (m * n))
                        | +-comm' n m | *-comm' n m = refl

0∸n≡0 : ∀ (n : ℕ) → zero ∸ n ≡ zero
0∸n≡0 zero = refl
0∸n≡0 (suc n) = refl

∸-|-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-|-assoc m       n       zero rewrite +-identity' n = refl
∸-|-assoc m       zero    (suc p) = refl
∸-|-assoc zero    (suc n) (suc p) = refl
∸-|-assoc (suc m) (suc n) (suc p) rewrite ∸-|-assoc m n (suc p) = refl

_^_ : ℕ → ℕ → ℕ
m ^ zero = 1
m ^ suc n = m * m ^ n

^-distribˡ-|-* : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distribˡ-|-* m zero p rewrite +-identity' (m ^ p) = refl
^-distribˡ-|-* m (suc n) p rewrite ^-distribˡ-|-* m n p | *-assoc m (m ^ n) (m ^ p) = refl

--------------------------------------------------------------------------------

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

data Carry : Set where
  NC : Carry
  CY : Carry

carry : Bin → Carry → Bin
carry n NC = n
carry ⟨⟩ CY = ⟨⟩ I
carry (n O) CY = n I
carry (n I) CY = (carry n CY) O

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = inc b O

-- The version below does not satisfy from (inc n) ≡ suc (from n)
-- inc : Bin → Bin
-- inc ⟨⟩ = ⟨⟩ O
-- inc b = inc-helper b where
--   inc-helper : Bin → Bin
--   inc-helper ⟨⟩ = ⟨⟩ I
--   inc-helper (b O) = b I
--   inc-helper (b I) = inc-helper b O

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc n) = inc (to n)

from : Bin → ℕ
from ⟨⟩ = zero
from (n O) = 2 * (from n)
from (n I) = 2 * (from n) + 1

n+1 : ∀ (n : ℕ) → n + 1 ≡ suc n
n+1 zero = refl
n+1 (suc n) rewrite n+1 n = refl

from-inc-suc : ∀ b → from (inc b) ≡ suc (from b)
from-inc-suc ⟨⟩ = refl
from-inc-suc (b O) rewrite +-identityʳ (from b)
                   | n+1 (from b + from b) = refl
from-inc-suc (b I) rewrite +-identityʳ (from (inc b))
                   | from-inc-suc b
                   | +-identityʳ (from b)
                   | sym (n+1 (from b))
                   | +-assoc (from b) (from b) 1 = refl

-- ∀ (b : bin) →  to (from b) ≡ b
-- Not true: for b = ⟨⟩, to (from b) ≡ to zero ≡ ⟨⟩ O instead of b

from-to : ∀ n → from (to n) ≡ n
from-to zero = refl
from-to (suc n) = begin
  from (to (suc n)) ≡⟨⟩
  from (inc (to n)) ≡⟨ from-inc-suc (to n) ⟩
  suc (from (to n)) ≡⟨ cong suc (from-to n) ⟩
  suc n ∎

-- import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc; +-comm)
