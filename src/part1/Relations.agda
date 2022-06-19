module part1.Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; +-identityʳ; *-zeroʳ; *-zeroˡ; *-identityˡ; +-suc; +-assoc; *-suc)

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ} → zero ≤ n
  s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n

_ : 2 ≤ 4
_ = s≤s (s≤s z≤n)

_ : 2 ≤ 4
_ = s≤s {1} {3} (s≤s {0} {2} (z≤n {2}))

_ : 2 ≤ 4
_ = s≤s {m = 1} {n = 3} (s≤s {m = 0} {n = 2} (z≤n {n = 2}))

_ : 2 ≤ 4
_ = s≤s {n = 3} (s≤s {n = 2} z≤n)

+-identityʳ' : ∀ {m : ℕ} → m + zero ≡ m
+-identityʳ' = +-identityʳ _

infix 4 _≤_

inv-s≤s : ∀ {m n : ℕ} → suc m ≤ suc n → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n

inv-z≤n : ∀ {n : ℕ} → n ≤ zero → n ≡ zero
inv-z≤n z≤n = refl

≡-suc : ∀ {m n : ℕ} → m ≡ n → suc m ≡ suc n
≡-suc p = cong suc p

≡-inv : ∀ {m n : ℕ} → suc m ≡ suc n → m ≡ n
≡-inv refl = refl

≤-sym : ∀ {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
≤-sym z≤n z≤n = refl
≤-sym (s≤s p) (s≤s q) = ≡-suc (≤-sym p q)

-- Give an example of a preorder that is not a partial order.

-- Let R be defined on ℕ × ℕ by xRy iff either x = y or x < y. R is
-- reflexive by definition. From the properties of <, we deduce that R
-- is transitive but not antisymmetric.

-- Give an example of a partial order that is not a total order.

-- Let | be defined on ℕ × ℕ by x|y iff x divides y. This relation is
-- reflexive, antisymmetric and transitive, but not all elements are
-- comparable: for example, neither 2|3 nor 3|2 hold.

≤-refl : ∀ {n : ℕ} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
≤-trans z≤n _ = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

≤-antisym : ∀ {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)

-- The case ≤-antisym z≤n (s≤s n≤m) requires the arguments to be of
-- types zero ≤ n and s≤s (n ≤ zero). n ≤ zero implies that n ≡ zero
-- (with witness refl), and then that the first argument is of type
-- zero ≤ zero (and is thus also equal to refl). This gives us a
-- pattern ≤-antisym refl (s≤s refl), with arguments of type 0 ≤ 0 and
-- 1 ≤ 1, both indexed at the same value of n, so that n must be both
-- equal to 0 and 1. This is impossible.
--
-- The case ≤-antisym (s≤s n≤m) z≤n, with arguments of types suc m ≤
-- suc n and suc n ≤ zero, requires suc m ≤ zero, so that suc m ≡
-- zero, which is impossible.

data Total (m n : ℕ) : Set where
  forward : m ≤ n → Total m n
  flipped : n ≤ m → Total m n

≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero n = forward z≤n
≤-total (suc m) zero = flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
... | forward m≤n = forward (s≤s m≤n)
... | flipped n≤m = flipped (s≤s n≤m)

+-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q → n + p ≤ n + q
+-monoʳ-≤ zero p q p≤q = p≤q
+-monoʳ-≤ (suc n) p q p≤q = s≤s (+-monoʳ-≤ n p q p≤q)

+-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n rewrite +-comm m p | +-comm n p = +-monoʳ-≤ p m n m≤n

+-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monoʳ-≤ m p q p≤q) (+-monoˡ-≤ m n q m≤n)

*-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m * p ≤ n * p
*-monoˡ-≤ m n zero m≤n rewrite *-zeroʳ m = z≤n
*-monoˡ-≤ m n (suc p) m≤n rewrite *-suc m p | *-suc n p = +-mono-≤ m n (m * p) (n * p) m≤n (*-monoˡ-≤ m n p m≤n)

*-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q → n * p ≤ n * q
*-monoʳ-≤ zero p q p≤q = z≤n
*-monoʳ-≤ (suc n) p q p≤q = +-mono-≤ p q (n * p) (n * q) p≤q (*-monoʳ-≤ n p q p≤q)

*-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m * p ≤ n * q
*-mono-≤ m n p q m≤n p≤q = ≤-trans (*-monoˡ-≤ m n p m≤n) (*-monoʳ-≤ n p q p≤q)

infix 4 _<_

data _<_ : ℕ → ℕ → Set where
  z<s : ∀ {n : ℕ} → zero < suc n
  s<s : ∀ {m n : ℕ} → m < n → suc m < suc n

<-trans : ∀ {m n p : ℕ} → m < n → n < p → m < p
<-trans z<s (s<s n<p) = z<s
<-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)

data Weak-Trichotomy (m n : ℕ) : Set where
  forward : m < n → Weak-Trichotomy m n
  flipped : n < m → Weak-Trichotomy m n
  equiv : m ≡ n → Weak-Trichotomy m n

<-total : ∀ (m n : ℕ) → Weak-Trichotomy m n
<-total zero zero = equiv refl
<-total zero (suc n) = forward z<s
<-total (suc m) zero = flipped z<s
<-total (suc m) (suc n) with <-total m n
... | forward m<n = forward (s<s m<n)
... | equiv m≡n = equiv (cong suc m≡n)
... | flipped n<m = flipped (s<s n<m)

<-inv : ∀ {m n : ℕ} → suc m < suc n → m < n
<-inv (s<s m<n) = m<n

+-mono-<ˡ : ∀ {m n p : ℕ} → m < n → m + p < n + p
+-mono-<ˡ {m = m} {n = n} {p = zero} m<n rewrite +-identityʳ m | +-identityʳ n = m<n
+-mono-<ˡ {m = m} {n = n} {p = suc p} m<n rewrite +-suc m p | +-suc n p = s<s (+-mono-<ˡ m<n)

+-mono-<ʳ : ∀ {n p q : ℕ} → p < q → n + p < n + q
+-mono-<ʳ {zero} p<q = p<q
+-mono-<ʳ {suc n} p<q = s<s (+-mono-<ʳ p<q)

+-mono-< : ∀ {m n p q : ℕ} → m < n → p < q → m + p < n + q
+-mono-< m<n p<q = <-trans (+-mono-<ˡ m<n) (+-mono-<ʳ p<q)

≤-implies-< : ∀ {m n : ℕ} → suc m ≤ n → m < n
≤-implies-< {zero} (s≤s sm≤n) = z<s
≤-implies-< {suc m} (s≤s sm≤n) = s<s (≤-implies-< sm≤n)

<-implies-≤ : ∀ {m n : ℕ} → m < n → m ≤ n
<-implies-≤ z<s = z≤n
<-implies-≤ (s<s m<n) = s≤s (<-implies-≤ m<n)

<-implies-s≤ : ∀ {m n : ℕ} → m < n → suc m ≤ n
<-implies-s≤ z<s = s≤s z≤n
<-implies-s≤ (s<s m<n) = s≤s (<-implies-s≤ m<n)

<-trans-revisited : ∀ {m n p : ℕ} → m < n → n < p → m < p
<-trans-revisited m<n n<p = ≤-implies-< (≤-trans (<-implies-s≤ m<n) (<-implies-≤ n<p))

data even : ℕ → Set
data odd : ℕ → Set

data even where
  zero : even zero
  suc : ∀ {n} → odd n → even (suc n)

data odd where
  suc : ∀ {n} → even n → odd (suc n)

e+e≡e : ∀ {m n : ℕ} → even m → even n → even (m + n)
o+e≡o : ∀ {m n : ℕ} → odd m → even n → odd (m + n)

e+e≡e zero en = en
e+e≡e (suc em) en = suc (o+e≡o em en)

o+e≡o (suc om) en = suc (e+e≡e om en)

o+o≡e : ∀ {m n : ℕ} → odd m → odd n → even (m + n)
o+o≡e {m} {suc n} om (suc en) rewrite +-suc m n = suc (o+e≡o om en)

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

-- A first attempt at defining One b was:
--
-- append : Bin → Bin → Bin
-- append b ⟨⟩ = b
-- append b (c O) = append b c O
-- append b (c I) = append b c I

-- data One' : Bin → Set where
--   one' : One' (⟨⟩ I)
--   app' : ∀ b c → One' b → One' (append b c)
--
-- However this definition is cumbersome to use in proofs, because
-- function types are not inductive and therefore do not support
-- pattern matching.

-- A definition of inc that verifies inc ⟨⟩ ≡ ⟨⟩
-- data Carry : Set where
--   NC : Carry
--   CY : Carry
--
-- adc : Bin → Carry → Bin
-- adc b NC = b
-- adc ⟨⟩ CY = ⟨⟩ I
-- adc (b O) CY = b I
-- adc (b I) CY = adc b CY O
--
-- inc : Bin → Bin
-- inc ⟨⟩ = ⟨⟩
-- inc (b O) = b I
-- inc (b I) = adc (b I) CY

-- A definition of inc that satisfies inc ⟨⟩ ≡ inc (⟨⟩ O). More
-- properties using to and from can be satisifed when using this
-- definition.
inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = inc b O

data One : Bin → Set where
  one : One (⟨⟩ I)
  ztail : ∀ {b} → One b → One (b O)
  otail : ∀ {b} → One b → One (b I)

data Can : Bin → Set where
  zero : Can (⟨⟩ O)
  leading : ∀ {b} → One b → Can b

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc n) = inc (to n)

from : Bin → ℕ
from ⟨⟩ = 0
from (b O) = 2 * from b
from (b I) = 2 * from b + 1

to-inc : ∀ n → to (n + 1) ≡ inc (to n)
to-inc zero = refl
to-inc (suc n) rewrite to-inc n = refl

to-inc' : ∀ n → to (suc n) ≡ inc (to n)
to-inc' n = refl

suc-n+1 : ∀ n → suc n ≡ n + 1
suc-n+1 zero = refl
suc-n+1 (suc n) rewrite +-suc n 1 = cong suc (suc-n+1 n)

from-inc : ∀ b → from (inc b) ≡ from b + 1
from-inc ⟨⟩ = refl
from-inc (b O) = refl
from-inc (b I) rewrite +-identityʳ (from (inc b)) | +-identityʳ (from b) = begin
  from (inc b) + from (inc b) ≡⟨ cong (λ x → x + x) (from-inc b) ⟩
  from b + 1 + (from b + 1)   ≡⟨ h (from b) ⟩
  from b + from b + 1 + 1     ∎
  where
    h : ∀ n → n + 1 + (n + 1) ≡ n + n + 1 + 1
    h n rewrite sym (+-assoc (n + 1) n 1)
        |       cong (λ x → x + 1) (+-assoc n 1 n)
        |       cong (λ x → n + x + 1) (+-comm 1 n)
        |       cong (λ x → x + 1) (sym (+-assoc n n 1)) = refl

from-to : ∀ n → from (to n) ≡ n
from-to zero = refl
from-to (suc n) = begin
  from (to (suc n)) ≡⟨ cong (λ x → from (to x)) (suc-n+1 n) ⟩
  from (to (n + 1)) ≡⟨ cong from (to-inc n) ⟩
  from (inc (to n)) ≡⟨ from-inc (to n) ⟩
  from (to n) + 1   ≡⟨ cong (λ x → x + 1) (from-to n) ⟩
  n + 1             ≡⟨ sym (suc-n+1 n) ⟩
  suc n             ∎

one-inc : ∀ {b} → One b → One (inc b)
one-inc one = ztail one
one-inc (ztail p) = otail p
one-inc {b} (otail p) = ztail (one-inc p)

can-inc : ∀ {b} → Can b → Can (inc b)
can-inc zero = leading one
can-inc (leading one) = leading (ztail one)
can-inc (leading (ztail p)) = leading (otail p)
can-inc (leading (otail one)) = leading (ztail (ztail one))
can-inc (leading (otail (ztail p))) = leading (ztail (otail p))
can-inc (leading (otail (otail p))) = leading (ztail (ztail (one-inc p)))

can-to : ∀ n → Can (to n)
can-to zero = zero
can-to (suc n) = can-inc (can-to n)

can-to-from : ∀ {b} → Can b → Can (to (from b))
can-to-from zero = zero
can-to-from {b} (leading p) = can-to (from b)

one→can : ∀ {b} → One b → Can b
one→can one = leading one
one→can p = leading p

can→one : ∀ {b} → Can b → 1 ≤ from b → One b
can→one (leading p) _ = p

-- Part of the lemmas suggested in the lesson, but unused here
one→1≤from : ∀ {b} → One b → 1 ≤ from b
one→1≤from one = ≤-refl
one→1≤from {b O} (ztail p) rewrite +-identityʳ (from b) = +-mono-≤ _ _ _ _ z≤n (one→1≤from p)
one→1≤from {b I} (otail p) rewrite +-identityʳ (from b) = +-monoˡ-≤ _ _ _ z≤n

-- During a first attempt at proving Can b → to (from b) ≡ b, I
-- thought splitting out the last digit of a binary number, or
-- implementing an addition of binary numbers, could be useful. In the
-- end, using l-shift proved to be simpler.
--
-- but-last : Bin → Bin
-- but-last ⟨⟩ = ⟨⟩
-- but-last (b O) = b
-- but-last (b I) = b

-- last : Bin → Bin
-- last ⟨⟩ = ⟨⟩
-- last (b O) = ⟨⟩ O
-- last (b I) = ⟨⟩ I

-- b-add : Bin → Bin → Bin
-- b-add ⟨⟩ c = c
-- b-add b ⟨⟩ = b
-- b-add (b O) (c O) = b-add b c O
-- b-add (b O) (c I) = b-add b c I
-- b-add (b I) (c O) = b-add b c I
-- b-add (b I) (c I) = inc (b-add b c I)

l-shift : Bin → Bin
l-shift ⟨⟩ = ⟨⟩
l-shift (b O) = collapse (b O O) where
  collapse : Bin → Bin
  collapse (⟨⟩ O O) = ⟨⟩ O
  collapse b = b
l-shift (b I) = b I O

l-shift-inc : ∀ b → l-shift (inc b) ≡ inc (inc (l-shift b))
l-shift-inc ⟨⟩ = refl
l-shift-inc (⟨⟩ O) = refl
l-shift-inc (b O O) = begin
  l-shift (inc (b O O))       ≡⟨⟩
  l-shift (b O I)             ≡⟨⟩
  b O I O                     ≡⟨⟩
  inc (inc (b O O O))         ≡⟨⟩
  inc (inc (l-shift (b O O))) ∎
l-shift-inc (b I O) = begin
   l-shift (inc (b I O))       ≡⟨⟩
   l-shift (b I I)             ≡⟨⟩
   b I I O                     ≡⟨⟩
   inc (inc (b I O O))         ≡⟨⟩
   inc (inc (l-shift (b I O))) ∎
l-shift-inc (⟨⟩ I) = refl
l-shift-inc ((b O) I) = refl
l-shift-inc ((b I) I) = refl

to-l-shift : ∀ n → to (2 * n) ≡ l-shift (to n)
to-l-shift zero = refl
to-l-shift (suc n) = begin
  to (2 * suc n)             ≡⟨ cong to (double-suc n) ⟩
  to (suc (suc (2 * n)))     ≡⟨⟩
  inc (to (suc (2 * n)))     ≡⟨⟩
  inc (inc (to (2 * n)))     ≡⟨ cong (λ b → inc (inc b)) (to-l-shift n) ⟩
  inc (inc (l-shift (to n))) ≡⟨ sym (l-shift-inc (to n)) ⟩
  l-shift (to (suc n))       ∎
  where
    double-suc : ∀ n → 2 * (suc n) ≡ suc (suc (2 * n))
    double-suc zero = refl
    double-suc (suc n) rewrite +-identityʳ n | +-suc n (suc n) = refl

l-shift-O : ∀ b → One b → l-shift b ≡ b O
l-shift-O ((b O) O) (ztail p) = refl
l-shift-O ((b I) O) (ztail p) = refl
l-shift-O (b I) p = refl

n+n≡2*n : ∀ n → n + n ≡ 2 * n
n+n≡2*n zero = refl
n+n≡2*n (suc n) rewrite *-suc 2 n | +-identityʳ n | +-suc n n = refl

n+n+1≡2*n+1 : ∀ n → n + n + 1 ≡ 2 * n + 1
n+n+1≡2*n+1 zero = refl
n+n+1≡2*n+1 (suc n) rewrite +-identityʳ n = refl

can-to-from-≡ : ∀ {b} → Can b → to (from b) ≡ b
can-to-from-≡ zero = refl
can-to-from-≡ {b O} (leading (ztail p)) rewrite +-identityʳ (from b) = begin
  to (from b + from b)  ≡⟨ cong to (n+n≡2*n (from b)) ⟩
  to (2 * from b)       ≡⟨ to-l-shift (from b) ⟩
  l-shift (to (from b)) ≡⟨ cong l-shift (can-to-from-≡ (one→can p)) ⟩
  l-shift b             ≡⟨ l-shift-O b p ⟩
  b O                   ∎
can-to-from-≡ (leading one) = refl
can-to-from-≡ {b I} (leading (otail p)) rewrite *-zeroʳ (from b) | +-identityʳ (from b) = begin
  to (from b + from b + 1)    ≡⟨ cong to (n+n+1≡2*n+1 (from b)) ⟩
  to (2 * from b + 1)         ≡⟨ to-inc (2 * from b) ⟩
  inc (to (2 * from b))       ≡⟨ cong inc (to-l-shift (from b)) ⟩
  inc (l-shift (to (from b))) ≡⟨ cong (λ b → inc (l-shift b)) (can-to-from-≡ (one→can p)) ⟩
  inc (l-shift b)             ≡⟨ cong inc (l-shift-O b p) ⟩
  inc (b O)                   ≡⟨⟩
  b I                         ∎

-- import Data.Nat using (_≤_; z≤n; s≤s)
-- import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-antisym; ≤-total; +-monoʳ-≤; +-monoˡ-≤; +-mono-≤)
